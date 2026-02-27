(******************************************************************************)
(* void_neural_theory.v - EXTENDED NEURAL CAPABILITIES                      *)
(*                                                                          *)
(* Three mechanisms that any VOID network builder can use:                  *)
(*                                                                          *)
(* 1. REFUND - budget flows back to cells that predicted correctly.         *)
(*    Without this, every network is disposable.                            *)
(*                                                                          *)
(* 2. INTERFERENCE - two Bool3 signals meeting produce a third.             *)
(*    Constructive (both agree), destructive (disagree), or unknown.        *)
(*    This is what makes nonlinearity possible without faking it.           *)
(*                                                                          *)
(* 3. VERDICT - a layer's output (list Bool3) becomes a collective          *)
(*    decision with honest confidence: how many agreed, how many silent.    *)
(*                                                                          *)
(* Uses types from: void_learning_cell, void_network                        *)
(* Draws ideas from: void_credit_propagation, void_interference_routing     *)
(*                                                                          *)
(* ALL THEOREMS FULLY PROVEN. ZERO Admitted.                                *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Prelude.

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_learning_cell.
Require Import void_network.

Import Void_Probability_Minimal.

(******************************************************************************)
(*                                                                          *)
(*                     PART 1: REFUND                                       *)
(*                                                                          *)
(******************************************************************************)

(* refund_cell : give budget back to a cell that predicted correctly.        *)
(*                                                                          *)
(* amount is Fin (budget domain). Threshold and heat unchanged.             *)
(* Budget increases by amount. That is the entire operation.                *)
(*                                                                          *)
(* Who decides how much to refund? The builder. This just adds ticks.       *)
(* Credit_propagation has prediction_accuracy, calculate_refund, etc.       *)
(* The builder can use those, or invent a different policy.                 *)

Definition refund_cell (c : LearningCell) (amount : Fin) : LearningCell :=
  mkCell (cell_threshold c)
         (add_heat (cell_budget c) amount)   (* add_heat is just fs^n *)
         (cell_heat c).

(* Refund a specific cell in a layer *)
Fixpoint refund_nth (layer : Layer) (n : Fin) (amount : Fin) : Layer :=
  match layer, n with
  | [], _ => []
  | wc :: rest, fz =>
      mkWeighted (refund_cell (cell wc) amount) (weights wc) :: rest
  | wc :: rest, fs n' =>
      wc :: refund_nth rest n' amount
  end.

(* Refund every cell in a layer that gave a specific answer *)
Fixpoint refund_matching (layer : Layer) (output : Signal) (target : Bool3)
  (amount : Fin) : Layer :=
  match layer, output with
  | [], _ => []
  | _, [] => layer
  | wc :: rest, sig :: sigs =>
      let wc' := match sig, target with
        | BTrue, BTrue => mkWeighted (refund_cell (cell wc) amount) (weights wc)
        | BFalse, BFalse => mkWeighted (refund_cell (cell wc) amount) (weights wc)
        | BUnknown, BUnknown => mkWeighted (refund_cell (cell wc) amount) (weights wc)
        | _, _ => wc
        end
      in wc' :: refund_matching rest sigs target amount
  end.

(******************************************************************************)
(* REFUND THEOREMS                                                          *)
(******************************************************************************)

Theorem refund_increases_budget : forall c amount,
  leF (cell_budget c) (cell_budget (refund_cell c amount)).
Proof.
  intros c amount. unfold refund_cell. simpl. apply add_heat_geq.
Qed.

Theorem refund_preserves_threshold : forall c amount,
  cell_threshold (refund_cell c amount) = cell_threshold c.
Proof.
  intros. unfold refund_cell. simpl. reflexivity.
Qed.

Theorem refund_preserves_heat : forall c amount,
  cell_heat (refund_cell c amount) = cell_heat c.
Proof.
  intros. unfold refund_cell. simpl. reflexivity.
Qed.

Theorem refund_zero_identity : forall c,
  refund_cell c fz = c.
Proof.
  intro c. unfold refund_cell.
  destruct c. simpl. reflexivity.
Qed.

Theorem refund_nth_preserves_length : forall layer n amount,
  length (refund_nth layer n amount) = length layer.
Proof.
  induction layer as [|wc rest IH]; intros n amount.
  - simpl. reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

Theorem refund_matching_preserves_length : forall layer output target amount,
  length (refund_matching layer output target amount) = length layer.
Proof.
  induction layer as [|wc rest IH]; intros output target amount.
  - simpl. reflexivity.
  - destruct output as [|sig sigs].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(* A refunded cell can now do work it couldn't do before *)
Theorem refund_revives_frozen : forall thr h amount,
  amount <> fz ->
  cell_budget (refund_cell (mkCell thr fz h) amount) <> fz.
Proof.
  intros thr h amount Hnz. unfold refund_cell. simpl.
  destruct amount as [|a'].
  - exfalso. apply Hnz. reflexivity.
  - discriminate.
Qed.

(******************************************************************************)
(*                                                                          *)
(*                     PART 2: INTERFERENCE                                 *)
(*                                                                          *)
(******************************************************************************)

(* Two Bool3 signals meeting. The result depends on agreement.              *)
(*                                                                          *)
(* BUnknown is infectious: unknown + anything = unknown.                    *)
(* Agreement is constructive: same + same = same.                           *)
(* Disagreement is destructive: true + false = unknown.                     *)
(*   (Not false! Disagreement means we DON'T KNOW, not "no".)              *)
(*                                                                          *)
(* This is the foundation for multi-path architectures.                     *)
(* Two paths see the same input differently, their interference tells       *)
(* whether the signal is real (constructive) or ambiguous (destructive).    *)

Definition interfere (a b : Bool3) : Bool3 :=
  match a, b with
  | BUnknown, _ => BUnknown
  | _, BUnknown => BUnknown
  | BTrue, BTrue => BTrue
  | BFalse, BFalse => BFalse
  | BTrue, BFalse => BUnknown     (* disagreement = uncertainty *)
  | BFalse, BTrue => BUnknown     (* disagreement = uncertainty *)
  end.

(* Interfere two signals element-wise *)
Fixpoint interfere_signals (s1 s2 : Signal) : Signal :=
  match s1, s2 with
  | [], _ => []
  | _, [] => []
  | a :: s1', b :: s2' => interfere a b :: interfere_signals s1' s2'
  end.

(******************************************************************************)
(* INTERFERENCE THEOREMS                                                    *)
(******************************************************************************)

(* Commutative *)
Theorem interfere_comm : forall a b, interfere a b = interfere b a.
Proof.
  intros [] []; reflexivity.
Qed.

(* BUnknown absorbs everything *)
Theorem interfere_unknown_left : forall b, interfere BUnknown b = BUnknown.
Proof.
  intros []; reflexivity.
Qed.

Theorem interfere_unknown_right : forall a, interfere a BUnknown = BUnknown.
Proof.
  intros []; reflexivity.
Qed.

(* Agreement is idempotent *)
Theorem interfere_self : forall a, interfere a a = a.
Proof.
  intros []; reflexivity.
Qed.

(* Disagreement always produces uncertainty *)
Theorem interfere_disagree : interfere BTrue BFalse = BUnknown.
Proof. reflexivity. Qed.

(* Interference never fabricates information *)
(* If both inputs lack info, output lacks info *)
Theorem interfere_honest : forall a b,
  a = BUnknown \/ b = BUnknown ->
  interfere a b = BUnknown.
Proof.
  intros a b [Ha | Hb].
  - subst a. apply interfere_unknown_left.
  - subst b. apply interfere_unknown_right.
Qed.

(* Constructive interference: both agree -> result matches *)
Theorem interfere_constructive_true :
  interfere BTrue BTrue = BTrue.
Proof. reflexivity. Qed.

Theorem interfere_constructive_false :
  interfere BFalse BFalse = BFalse.
Proof. reflexivity. Qed.

(* Signal interference preserves minimum length *)
Theorem interfere_signals_length : forall s1 s2,
  length (interfere_signals s1 s2) = min (length s1) (length s2).
Proof.
  induction s1 as [|a s1' IH]; intros s2.
  - simpl. reflexivity.
  - destruct s2 as [|b s2'].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(******************************************************************************)
(*                                                                          *)
(*                     PART 3: VERDICT                                      *)
(*                                                                          *)
(******************************************************************************)

(* A layer produces list Bool3. We need collective decisions.               *)
(*                                                                          *)
(* Verdict = (decision, count_for, count_against, count_unknown)            *)
(*                                                                          *)
(* Rules:                                                                   *)
(*   - If count_unknown > count_known: verdict = BUnknown                  *)
(*     (majority doesn't know -> we don't know)                            *)
(*   - If count_true > count_false: verdict = BTrue                        *)
(*   - If count_false > count_true: verdict = BFalse                       *)
(*   - If count_true = count_false: verdict = BUnknown                     *)
(*     (tie = no information, not "pick one")                              *)
(*                                                                          *)
(* The tie->BUnknown rule is critical. No coin flips. No defaults.         *)

Record Verdict := mkVerdict {
  decision : Bool3;
  votes_true : Fin;
  votes_false : Fin;
  votes_unknown : Fin
}.

Definition tally (signals : Signal) (b : Budget) : Verdict :=
  let t := count_result signals BTrue in
  let f := count_result signals BFalse in
  let u := count_result signals BUnknown in
  let known := add_heat t f in
  match le_fin_b3 known u b with
  | (BTrue, b1, _) => mkVerdict BUnknown t f u    (* unknown >= known *)
  | (BUnknown, b1, _) => mkVerdict BUnknown t f u (* can't compare *)
  | (BFalse, b1, _) =>
      (* More known than unknown. Strict comparison: is t < f? *)
      match le_fin_b3 (fs t) f b1 with
      | (BTrue, _, _) => mkVerdict BFalse t f u     (* t < f: false wins *)
      | (_, b2, _) =>
          match le_fin_b3 (fs f) t b2 with
          | (BTrue, _, _) => mkVerdict BTrue t f u   (* f < t: true wins *)
          | (_, _, _) => mkVerdict BUnknown t f u    (* tie or exhausted *)
          end
      end
  end.

(* Confidence = votes_for / total_votes. As FinProb. *)
(* Only meaningful when decision is not BUnknown.     *)
Definition verdict_confidence (v : Verdict) : FinProb :=
  match decision v with
  | BUnknown => (fz, fs fz)    (* 0/1: no confidence *)
  | BTrue =>
      let total := add_heat (votes_true v) (add_heat (votes_false v) (votes_unknown v)) in
      (votes_true v, total)
  | BFalse =>
      let total := add_heat (votes_true v) (add_heat (votes_false v) (votes_unknown v)) in
      (votes_false v, total)
  end.

(******************************************************************************)
(* VERDICT THEOREMS                                                         *)
(******************************************************************************)

(* We use a generous budget for theorem proofs: fs^10 fz *)
Definition big_budget : Budget :=
  fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).

Theorem tally_empty : decision (tally [] big_budget) = BUnknown.
Proof. simpl. reflexivity. Qed.

Theorem tally_single_true : decision (tally [BTrue] big_budget) = BTrue.
Proof. simpl. reflexivity. Qed.

Theorem tally_single_false : decision (tally [BFalse] big_budget) = BFalse.
Proof. simpl. reflexivity. Qed.

Theorem tally_single_unknown : decision (tally [BUnknown] big_budget) = BUnknown.
Proof. simpl. reflexivity. Qed.

(* Unanimous true -> true *)
Theorem tally_unanimous_true : decision (tally [BTrue; BTrue] big_budget) = BTrue.
Proof. simpl. reflexivity. Qed.

(* Unanimous false -> false *)
Theorem tally_unanimous_false : decision (tally [BFalse; BFalse] big_budget) = BFalse.
Proof. simpl. reflexivity. Qed.

(* Tie -> unknown, not a coin flip *)
Theorem tally_tie_unknown : decision (tally [BTrue; BFalse] big_budget) = BUnknown.
Proof. simpl. reflexivity. Qed.

(* Unknown majority dominates *)
Theorem tally_unknown_majority :
  decision (tally [BTrue; BUnknown; BUnknown] big_budget) = BUnknown.
Proof. simpl. reflexivity. Qed.

(* Confidence of BUnknown verdict is always 0 *)
Theorem unknown_verdict_zero_confidence : forall v,
  decision v = BUnknown ->
  verdict_confidence v = (fz, fs fz).
Proof.
  intros v Hu. unfold verdict_confidence. rewrite Hu. reflexivity.
Qed.

(******************************************************************************)
(*                                                                          *)
(*                COMBINED: LEARN-FROM-VERDICT                              *)
(*                                                                          *)
(******************************************************************************)

(* After a verdict, we know which cells agreed with the verdict             *)
(* and which didn't. This drives learning:                                  *)
(*                                                                          *)
(* Cell agreed with correct verdict   -> REFUND (survived, gets budget)     *)
(* Cell disagreed with correct verdict -> ERODE or CONSTRICT (was wrong)    *)
(* Cell said BUnknown                 -> nothing (honest, no punishment)    *)
(*                                                                          *)
(* "correct verdict" = external ground truth. The builder provides it.     *)
(* We just provide the operation that applies the policy across a layer.   *)

Inductive Correction :=
  | DoRefund (amount : Fin)
  | DoErode
  | DoConstrict
  | DoNothing.

(* Decide what to do with a cell based on its output vs ground truth *)
Definition cell_correction (output : Bool3) (truth : Bool3) : Correction :=
  match output, truth with
  | BUnknown, _ => DoNothing          (* honest ignorance, no punishment *)
  | BTrue, BTrue => DoRefund (fs fz)  (* correct! default refund: 1 tick *)
  | BFalse, BFalse => DoRefund (fs fz)
  | BTrue, BFalse => DoConstrict      (* fired when shouldn't -> raise threshold *)
  | BFalse, BTrue => DoErode          (* silent when should fire -> lower threshold *)
  | _, BUnknown => DoNothing          (* truth is unknown -> can't judge *)
  end.

(* Apply correction to a single weighted cell *)
Definition apply_correction (wc : WeightedCell) (corr : Correction) : WeightedCell :=
  match corr with
  | DoRefund amount => mkWeighted (refund_cell (cell wc) amount) (weights wc)
  | DoErode => mkWeighted (erode_threshold (cell wc)) (weights wc)
  | DoConstrict => mkWeighted (constrict_threshold (cell wc)) (weights wc)
  | DoNothing => wc
  end.

(* Apply corrections across a layer, given output and ground truth *)
Fixpoint learn_from_truth (layer : Layer) (output : Signal) (truth : Bool3)
  : Layer :=
  match layer, output with
  | [], _ => []
  | _, [] => layer
  | wc :: rest, sig :: sigs =>
      apply_correction wc (cell_correction sig truth) :: learn_from_truth rest sigs truth
  end.

(******************************************************************************)
(* LEARN-FROM-VERDICT THEOREMS                                              *)
(******************************************************************************)

Theorem learn_preserves_length : forall layer output truth,
  length (learn_from_truth layer output truth) = length layer.
Proof.
  induction layer as [|wc rest IH]; intros output truth.
  - simpl. reflexivity.
  - destruct output as [|sig sigs].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(* BUnknown cells are never modified *)
Theorem unknown_never_punished : forall wc truth,
  apply_correction wc (cell_correction BUnknown truth) = wc.
Proof.
  intros wc truth. destruct truth; simpl; reflexivity.
Qed.

(* Correct predictions get refunded *)
Theorem correct_true_refunded : forall wc,
  apply_correction wc (cell_correction BTrue BTrue) =
  mkWeighted (refund_cell (cell wc) (fs fz)) (weights wc).
Proof. intros. simpl. reflexivity. Qed.

Theorem correct_false_refunded : forall wc,
  apply_correction wc (cell_correction BFalse BFalse) =
  mkWeighted (refund_cell (cell wc) (fs fz)) (weights wc).
Proof. intros. simpl. reflexivity. Qed.

(* False positive -> constrict *)
Theorem false_positive_constricts : forall wc,
  apply_correction wc (cell_correction BTrue BFalse) =
  mkWeighted (constrict_threshold (cell wc)) (weights wc).
Proof. intros. simpl. reflexivity. Qed.

(* False negative -> erode *)
Theorem false_negative_erodes : forall wc,
  apply_correction wc (cell_correction BFalse BTrue) =
  mkWeighted (erode_threshold (cell wc)) (weights wc).
Proof. intros. simpl. reflexivity. Qed.

(* Unknown truth -> nothing happens to anyone *)
Theorem unknown_truth_no_learning : forall sig,
  cell_correction sig BUnknown = DoNothing.
Proof.
  intros []; simpl; reflexivity.
Qed.

(* Weights never change through learning *)
Theorem learn_preserves_weights : forall wc corr,
  weights (apply_correction wc corr) = weights wc.
Proof.
  intros wc []; simpl; reflexivity.
Qed.
