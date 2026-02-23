(******************************************************************************)
(* void_network.v - ABSTRACT NETWORK PROPERTIES                             *)
(*                                                                          *)
(* Inter-layer signal is list Bool3, NOT VoidVector.                        *)
(* BUnknown never silently becomes a FinProb value.                         *)
(*                                                                          *)
(* A weighted cell receiving Bool3 inputs must handle unknown explicitly:   *)
(*   - BTrue/BFalse inputs contribute to signal via weights                *)
(*   - BUnknown inputs are HOLES - they contribute nothing                 *)
(*   - If ALL inputs are unknown -> cell outputs BUnknown                  *)
(*   - If SOME inputs are known -> cell computes on partial information    *)
(*     but with honest accounting of how much it actually saw              *)
(*                                                                          *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal,               *)
(*             void_geometry, void_learning_cell                            *)
(* ALL THEOREMS FULLY PROVEN. ZERO Admitted.                                *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Prelude.

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import void_geometry.
Require Import void_learning_cell.

Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Geometry.

(******************************************************************************)
(* SIGNAL TYPE - Bool3 between layers, always                                *)
(******************************************************************************)

Definition Signal := list Bool3.

(******************************************************************************)
(* COUNTING KNOWN vs UNKNOWN in a signal                                     *)
(******************************************************************************)

Fixpoint count_known (s : Signal) : Fin :=
  match s with
  | [] => fz
  | BUnknown :: rest => count_known rest
  | _ :: rest => fs (count_known rest)
  end.

Fixpoint all_unknown (s : Signal) : bool :=
  match s with
  | [] => true
  | BUnknown :: rest => all_unknown rest
  | _ :: rest => false
  end.

(******************************************************************************)
(* WEIGHTED CELL                                                             *)
(******************************************************************************)

Record WeightedCell := mkWeighted {
  cell : LearningCell;
  weights : VoidVector          (* one FinProb weight per input dimension *)
}.

(******************************************************************************)
(* PARTIAL INNER PRODUCT                                                     *)
(*                                                                          *)
(* The honest weighted sum. Pairs (Bool3, FinProb weight).                  *)
(* BTrue   -> add weight to accumulator                                    *)
(* BFalse  -> skip (signal is off, contributes nothing)                    *)
(* BUnknown -> skip (no information, contributes nothing)                  *)
(*                                                                          *)
(* Note: BFalse and BUnknown both skip, but for DIFFERENT REASONS.         *)
(* BFalse = "I know the signal is off" -> honest zero contribution         *)
(* BUnknown = "I don't know" -> cannot contribute anything                 *)
(*                                                                          *)
(* The accumulator starts at (fz, fs fz) = 0/1.                           *)
(* Only BTrue inputs contribute their weight.                              *)
(* Result: sum of weights where input fired.                               *)
(******************************************************************************)

Definition zero_prob : FinProb := (fz, fs fz).   (* 0/1 *)

Fixpoint partial_weighted_sum (inputs : Signal) (ws : VoidVector) (b : Budget)
  : (FinProb * Budget) :=
  match inputs, ws with
  | [], _ => (zero_prob, b)
  | _, [] => (zero_prob, b)
  | BTrue :: ins', w :: ws' =>
      match partial_weighted_sum ins' ws' b with
      | (acc, b') => add_prob_b acc w b'
      end
  | _ :: ins', _ :: ws' =>
      (* BFalse or BUnknown: skip this weight, no budget spent *)
      partial_weighted_sum ins' ws' b
  end.

(******************************************************************************)
(* FIRE_WEIGHTED - the fundamental network operation                         *)
(*                                                                          *)
(* 1. If ALL inputs are BUnknown -> BUnknown (no information, no compute)  *)
(* 2. Otherwise: partial_weighted_sum -> FinProb -> activate -> Bool3       *)
(*                                                                          *)
(* Budget consumed ONLY for known inputs. Unknown inputs are free to skip.  *)
(******************************************************************************)

Definition fire_weighted (wc : WeightedCell) (input : Signal)
  : (Bool3 * WeightedCell) :=
  if all_unknown input then
    (* No information at all -> honest Unknown, no budget spent *)
    (BUnknown, wc)
  else
    let b := cell_budget (cell wc) in
    let h := cell_heat (cell wc) in
    let thr := cell_threshold (cell wc) in
    match partial_weighted_sum input (weights wc) b with
    | (signal, b') =>
        let cell_after := mkCell thr b' h in
        match activate cell_after signal with
        | (result, cell_final) =>
            (result, mkWeighted cell_final (weights wc))
        end
    end.

(******************************************************************************)
(* LAYER = list of weighted cells                                            *)
(******************************************************************************)

Definition Layer := list WeightedCell.

(******************************************************************************)
(* PROPAGATE_LAYER                                                           *)
(* Each cell reads the SAME Signal through its OWN weights.                 *)
(* Output: Signal (list Bool3) + updated layer.                             *)
(******************************************************************************)

Fixpoint propagate_layer (layer : Layer) (input : Signal)
  : (Signal * Layer) :=
  match layer with
  | [] => ([], [])
  | wc :: rest =>
      match fire_weighted wc input with
      | (result, wc') =>
          match propagate_layer rest input with
          | (results, rest') =>
              (result :: results, wc' :: rest')
          end
      end
  end.

(******************************************************************************)
(* LEARNING PRIMITIVES                                                       *)
(******************************************************************************)

Fixpoint erode_nth (layer : Layer) (n : Fin) : Layer :=
  match layer, n with
  | [], _ => []
  | wc :: rest, fz =>
      mkWeighted (erode_threshold (cell wc)) (weights wc) :: rest
  | wc :: rest, fs n' =>
      wc :: erode_nth rest n'
  end.

Fixpoint constrict_nth (layer : Layer) (n : Fin) : Layer :=
  match layer, n with
  | [], _ => []
  | wc :: rest, fz =>
      mkWeighted (constrict_threshold (cell wc)) (weights wc) :: rest
  | wc :: rest, fs n' =>
      wc :: constrict_nth rest n'
  end.

(******************************************************************************)
(* COUNTING                                                                  *)
(******************************************************************************)

Fixpoint count_result (signals : Signal) (target : Bool3) : Fin :=
  match signals with
  | [] => fz
  | s :: rest =>
      let c := count_result rest target in
      match s, target with
      | BTrue, BTrue => fs c
      | BFalse, BFalse => fs c
      | BUnknown, BUnknown => fs c
      | _, _ => c
      end
  end.

(******************************************************************************)
(*                          THEOREMS                                         *)
(******************************************************************************)

(******************************************************************************)
(* THEOREM 1: ALL-UNKNOWN INPUT -> BUnknown OUTPUT                           *)
(* The fundamental honesty property. No information in, no answer out.      *)
(******************************************************************************)

Theorem fire_all_unknown : forall wc input,
  all_unknown input = true ->
  fst (fire_weighted wc input) = BUnknown.
Proof.
  intros wc input Hu. unfold fire_weighted.
  rewrite Hu. simpl. reflexivity.
Qed.

(* Corollary: all-unknown input costs zero budget *)
Theorem fire_all_unknown_free : forall wc input,
  all_unknown input = true ->
  snd (fire_weighted wc input) = wc.
Proof.
  intros wc input Hu. unfold fire_weighted.
  rewrite Hu. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 2: EMPTY SIGNAL -> BUnknown                                       *)
(******************************************************************************)

Theorem fire_empty_unknown : forall wc,
  fst (fire_weighted wc []) = BUnknown.
Proof.
  intro wc. apply fire_all_unknown. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 3: PROPAGATION PRESERVES LENGTH                                   *)
(******************************************************************************)

Theorem propagate_preserves_length : forall layer input,
  length (snd (propagate_layer layer input)) = length layer.
Proof.
  induction layer as [|wc rest IH]; intro input.
  - simpl. reflexivity.
  - simpl.
    destruct (fire_weighted wc input) as [r wc'].
    destruct (propagate_layer rest input) as [rs rest'] eqn:E.
    simpl. f_equal.
    assert (H := IH input). rewrite E in H. simpl in H. exact H.
Qed.

Theorem propagate_output_length : forall layer input,
  length (fst (propagate_layer layer input)) = length layer.
Proof.
  induction layer as [|wc rest IH]; intro input.
  - simpl. reflexivity.
  - simpl.
    destruct (fire_weighted wc input) as [r wc'].
    destruct (propagate_layer rest input) as [rs rest'] eqn:E.
    simpl. f_equal.
    assert (H := IH input). rewrite E in H. simpl in H. exact H.
Qed.

(******************************************************************************)
(* THEOREM 4: WEIGHTS UNCHANGED BY PROPAGATION                              *)
(******************************************************************************)

Theorem fire_preserves_weights : forall wc input,
  weights (snd (fire_weighted wc input)) = weights wc.
Proof.
  intros wc input. unfold fire_weighted.
  destruct (all_unknown input).
  - simpl. reflexivity.
  - destruct (partial_weighted_sum input (weights wc) (cell_budget (cell wc)))
      as [signal b'].
    destruct (activate (mkCell (cell_threshold (cell wc)) b' (cell_heat (cell wc))) signal)
      as [r cell_final].
    simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 5: EMPTY LAYER IS INERT                                          *)
(******************************************************************************)

Theorem empty_layer_propagate : forall input,
  propagate_layer [] input = ([], []).
Proof. reflexivity. Qed.

(******************************************************************************)
(* THEOREM 6: SINGLE CELL LAYER                                             *)
(******************************************************************************)

Theorem single_cell_propagate : forall wc input,
  propagate_layer [wc] input =
  let (r, wc') := fire_weighted wc input in ([r], [wc']).
Proof.
  intros wc input. simpl.
  destruct (fire_weighted wc input) as [r wc'].
  reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 7: ERODE/CONSTRICT PRESERVES LAYER LENGTH                        *)
(******************************************************************************)

Theorem erode_nth_preserves_length : forall layer n,
  length (erode_nth layer n) = length layer.
Proof.
  induction layer as [|wc rest IH]; intros n.
  - simpl. reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

Theorem constrict_nth_preserves_length : forall layer n,
  length (constrict_nth layer n) = length layer.
Proof.
  induction layer as [|wc rest IH]; intros n.
  - simpl. reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(******************************************************************************)
(* THEOREM 8: ERODE/CONSTRICT ONLY AFFECTS TARGET CELL                      *)
(******************************************************************************)

Theorem erode_nth_other_unchanged : forall wc rest n',
  erode_nth (wc :: rest) (fs n') = wc :: erode_nth rest n'.
Proof. intros. simpl. reflexivity. Qed.

Theorem constrict_nth_other_unchanged : forall wc rest n',
  constrict_nth (wc :: rest) (fs n') = wc :: constrict_nth rest n'.
Proof. intros. simpl. reflexivity. Qed.

(******************************************************************************)
(* THEOREM 9: ALL-UNKNOWN LAYER PRODUCES ALL-UNKNOWN OUTPUT                  *)
(* If entire input signal is unknown, every cell says unknown.              *)
(******************************************************************************)

Lemma all_unknown_propagate_helper : forall layer input,
  all_unknown input = true ->
  fst (propagate_layer layer input) = map (fun _ => BUnknown) layer.
Proof.
  induction layer as [|wc rest IH]; intros input Hu.
  - simpl. reflexivity.
  - simpl.
    assert (Hf : fire_weighted wc input = (BUnknown, wc)).
    { unfold fire_weighted. rewrite Hu. reflexivity. }
    rewrite Hf.
    destruct (propagate_layer rest input) as [rs rest'] eqn:E.
    simpl. f_equal.
    assert (H := IH input Hu). rewrite E in H. simpl in H. exact H.
Qed.

(******************************************************************************)
(* THEOREM 10: count_known reflects actual information                       *)
(******************************************************************************)

Theorem count_known_nil : count_known [] = fz.
Proof. reflexivity. Qed.

Theorem count_known_all_unknown : forall s,
  all_unknown s = true -> count_known s = fz.
Proof.
  induction s as [|b rest IH].
  - intros _. reflexivity.
  - intro Hu. destruct b; simpl in Hu; try discriminate.
    simpl. apply IH. exact Hu.
Qed.

(******************************************************************************)
(* THEOREM 11: partial_weighted_sum with no known inputs returns zero       *)
(******************************************************************************)

Theorem partial_sum_all_unknown : forall input ws b,
  all_unknown input = true ->
  partial_weighted_sum input ws b = (zero_prob, b).
Proof.
  induction input as [|i rest IH]; intros ws b Hu.
  - simpl. reflexivity.
  - destruct i; simpl in Hu; try discriminate.
    (* i = BUnknown *)
    destruct ws as [|w ws'].
    + simpl. reflexivity.
    + simpl. apply IH. exact Hu.
Qed.

(* Corollary: all-unknown input spends zero budget on weighted sum *)
Theorem partial_sum_all_unknown_free : forall input ws b,
  all_unknown input = true ->
  snd (partial_weighted_sum input ws b) = b.
Proof.
  intros. rewrite partial_sum_all_unknown; [reflexivity | exact H].
Qed.
