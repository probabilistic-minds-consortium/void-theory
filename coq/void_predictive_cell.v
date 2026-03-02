(******************************************************************************)
(* void_predictive_cell.v                                                     *)
(*                                                                            *)
(* Dual-accumulator predictive cell with budget-flow learning.               *)
(* Replaces void_perceptron.v (deleted).                                     *)
(* Definitions derived from void_error_audit.v — PROVED, not axiomatized.    *)
(*                                                                            *)
(* Imports: void_finite_minimal only.                                        *)
(* No FinProb in cell operations. No nat. No Admitted.                       *)
(*                                                                            *)
(* Errors addressed:                                                         *)
(*   #2  BFalse is active (dual accumulator)                                 *)
(*   #3  No threshold (compare acc_for vs acc_against)                       *)
(*   #4  No erode/constrict (weights frozen, budget flow only)               *)
(*   #5  No subtraction (except spend_aux for budget transfer)               *)
(*   #6  No multiplication (comparison = le_fin_b3 on Fin)                   *)
(*   #7  Predictive processing (selection, not adjustment)                   *)
(*   #8  Conservation with environment (refund from external pool)           *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.

Module Void_Predictive_Cell.

(******************************************************************************)
(* BOOL3 EQUALITY — costs 1 tick, returns Bool3                              *)
(******************************************************************************)

Definition bool3_eq_b3 (a b : Bool3) (budget : Budget)
  : (Bool3 * Budget * Heat) :=
  match budget with
  | fz => (BUnknown, fz, fz)
  | fs budget' =>
    match a, b with
    | BTrue, BTrue       => (BTrue, budget', fs fz)
    | BFalse, BFalse     => (BTrue, budget', fs fz)
    | BUnknown, BUnknown => (BTrue, budget', fs fz)
    | _, _               => (BFalse, budget', fs fz)
    end
  end.

(******************************************************************************)
(* PREDICTIVE CELL                                                           *)
(*                                                                            *)
(* No threshold field. No FinProb. Weights are list Fin.                     *)
(* Decision = compare acc_for vs acc_against via le_fin_b3.                  *)
(******************************************************************************)

Record PredictiveCell := mkPredCell {
  weights_for     : list Fin;
  weights_against : list Fin;
  cell_budget     : Budget;
  cell_heat       : Heat
}.

(******************************************************************************)
(* DUAL ACCUMULATOR                                                          *)
(*                                                                            *)
(* BTrue inputs activate weights_for. BFalse activates weights_against.      *)
(* BUnknown activates neither — honest silence.                              *)
(* Non-matching inputs are READ (free). Matching = WRITE (costs budget).     *)
(******************************************************************************)

Fixpoint accumulate_for (inputs : list Bool3) (ws : list Fin)
                         (acc : Fin) (b : Budget)
  : (Fin * Budget * Heat) :=
  match inputs, ws with
  | [], _    => (acc, b, fz)
  | _, []    => (acc, b, fz)
  | BTrue :: ins, w :: ws' =>
      match add_fin_b_heat acc w b with
      | (acc', b', h) =>
          match accumulate_for ins ws' acc' b' with
          | (r, b_final, h2) => (r, b_final, add_heat h h2)
          end
      end
  | _ :: ins, _ :: ws' =>
      accumulate_for ins ws' acc b
  end.

Fixpoint accumulate_against (inputs : list Bool3) (ws : list Fin)
                             (acc : Fin) (b : Budget)
  : (Fin * Budget * Heat) :=
  match inputs, ws with
  | [], _    => (acc, b, fz)
  | _, []    => (acc, b, fz)
  | BFalse :: ins, w :: ws' =>
      match add_fin_b_heat acc w b with
      | (acc', b', h) =>
          match accumulate_against ins ws' acc' b' with
          | (r, b_final, h2) => (r, b_final, add_heat h h2)
          end
      end
  | _ :: ins, _ :: ws' =>
      accumulate_against ins ws' acc b
  end.

(******************************************************************************)
(* PREDICT                                                                   *)
(*                                                                            *)
(* Fire both accumulators. Compare in both directions.                       *)
(* Tie → BUnknown (honest). Budget exhaustion → BUnknown (honest).          *)
(******************************************************************************)

Definition predict (cell : PredictiveCell) (inputs : list Bool3)
  : (Bool3 * Budget * Heat) :=
  match accumulate_for inputs (weights_for cell) fz (cell_budget cell) with
  | (acc_f, b1, h1) =>
    match accumulate_against inputs (weights_against cell) fz b1 with
    | (acc_a, b2, h2) =>
      match le_fin_b3 acc_a acc_f b2 with
      | (BTrue, b3, h3) =>
        (* against <= for. Now check reverse. *)
        match le_fin_b3 acc_f acc_a b3 with
        | (BTrue, b4, h4) =>
            (* for <= against AND against <= for: TIE *)
            (BUnknown, b4, add_heat h1 (add_heat h2 (add_heat h3 h4)))
        | (BFalse, b4, h4) =>
            (* against <= for BUT NOT for <= against: FOR WINS *)
            (BTrue, b4, add_heat h1 (add_heat h2 (add_heat h3 h4)))
        | (BUnknown, b4, h4) =>
            (* Budget exhausted *)
            (BUnknown, b4, add_heat h1 (add_heat h2 (add_heat h3 h4)))
        end
      | (BFalse, b3, h3) =>
          (* NOT against <= for: AGAINST WINS *)
          (BFalse, b3, add_heat h1 (add_heat h2 h3))
      | (BUnknown, b3, h3) =>
          (* Budget exhausted *)
          (BUnknown, b3, add_heat h1 (add_heat h2 h3))
      end
    end
  end.

(******************************************************************************)
(* LEARNING PARAMETERS                                                       *)
(******************************************************************************)

Parameter precision_gain : Fin.
Parameter surprise_cost  : Fin.

(******************************************************************************)
(* UPDATE — budget flow only                                                 *)
(*                                                                            *)
(* Correct → refund (budget from environment pool).                          *)
(* Wrong → penalty (budget to heat).                                         *)
(* Unknown → comparison cost only.                                           *)
(* Weights NEVER change. This is selection, not adjustment.                  *)
(******************************************************************************)

Definition update_cell (cell : PredictiveCell) (prediction truth : Bool3)
  : PredictiveCell :=
  match bool3_eq_b3 prediction truth (cell_budget cell) with
  | (BTrue, b', h) =>
      (* CORRECT — low surprise — refund from environment *)
      match add_fin_b_heat b' precision_gain b' with
      | (new_b, _, h2) =>
          mkPredCell (weights_for cell) (weights_against cell)
                     new_b (add_heat (cell_heat cell) (add_heat h h2))
      end
  | (BFalse, b', h) =>
      (* WRONG — high surprise — penalty to heat *)
      match spend_aux b' surprise_cost with
      | (new_b, h2) =>
          mkPredCell (weights_for cell) (weights_against cell)
                     new_b (add_heat (cell_heat cell) (add_heat h h2))
      end
  | (BUnknown, b', h) =>
      (* BUDGET EXHAUSTED — can't even compare — no change *)
      mkPredCell (weights_for cell) (weights_against cell)
                 b' (add_heat (cell_heat cell) h)
  end.

(******************************************************************************)
(* CELL ALIVE                                                                *)
(******************************************************************************)

Definition cell_alive (cell : PredictiveCell) : Bool3 :=
  match cell_budget cell with
  | fz => BFalse
  | fs _ => BTrue
  end.

(******************************************************************************)
(* THEOREM 1: WEIGHTS NEVER CHANGE                                          *)
(*                                                                            *)
(* Was: Axiom weights_immutable in error audit.                              *)
(* Now: Lemma. update_cell builds mkPredCell with same weights in all        *)
(* three branches. QED by case analysis on bool3_eq_b3 result.               *)
(******************************************************************************)

Lemma weights_immutable : forall cell pred truth,
  weights_for (update_cell cell pred truth) = weights_for cell /\
  weights_against (update_cell cell pred truth) = weights_against cell.
Proof.
  intros cell pred truth.
  unfold update_cell.
  destruct (bool3_eq_b3 pred truth (cell_budget cell)) as [[r b'] h] eqn:Heq.
  destruct r.
  - (* BTrue: correct prediction *)
    destruct (add_fin_b_heat b' precision_gain b') as [[new_b ?] h2].
    simpl. auto.
  - (* BFalse: wrong prediction *)
    destruct (spend_aux b' surprise_cost) as [new_b h2].
    simpl. auto.
  - (* BUnknown: budget exhausted *)
    simpl. auto.
Qed.

(******************************************************************************)
(* THEOREM 2: DEAD CELLS STAY DEAD                                          *)
(*                                                                            *)
(* Was: Axiom dead_stays_dead in error audit.                                *)
(* Now: Lemma. When budget = fz, bool3_eq_b3 returns (BUnknown, fz, fz).    *)
(* The BUnknown branch preserves budget = fz.                                *)
(******************************************************************************)

Lemma dead_stays_dead : forall cell pred truth,
  cell_budget cell = fz ->
  cell_budget (update_cell cell pred truth) = fz.
Proof.
  intros cell pred truth Hdead.
  unfold update_cell.
  rewrite Hdead.
  simpl.
  reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 3: EMPTY EVIDENCE → UNKNOWN                                      *)
(*                                                                            *)
(* With no inputs both accumulators return fz.                               *)
(* le_fin_b3 fz fz in both directions gives BTrue (tie).                    *)
(* Tie → BUnknown. Requires budget >= 2 ticks for both comparisons.         *)
(******************************************************************************)

Lemma accumulate_for_nil : forall ws acc b,
  accumulate_for [] ws acc b = (acc, b, fz).
Proof. intros. simpl. reflexivity. Qed.

Lemma accumulate_against_nil : forall ws acc b,
  accumulate_against [] ws acc b = (acc, b, fz).
Proof. intros. simpl. reflexivity. Qed.

Lemma le_fin_b3_fz_fz : forall b,
  le_fin_b3 fz fz (fs b) = (BTrue, b, fs fz).
Proof. intros. simpl. reflexivity. Qed.

Theorem no_evidence_is_unknown : forall cell,
  (exists n, cell_budget cell = fs (fs n)) ->
  fst (fst (predict cell [])) = BUnknown.
Proof.
  intros cell [n Hbudget].
  unfold predict.
  rewrite accumulate_for_nil.
  rewrite accumulate_against_nil.
  rewrite Hbudget.
  rewrite le_fin_b3_fz_fz.
  rewrite le_fin_b3_fz_fz.
  simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 4: BFalse IS ACTIVE (not silence)                                 *)
(*                                                                            *)
(* Was: Axiom bfalse_is_active in error audit.                               *)
(* Now: Lemma. BFalse adds weight to acc_against. BUnknown does not.         *)
(* Therefore the two results differ.                                         *)
(******************************************************************************)

Lemma accumulate_against_bfalse : forall w ws acc b,
  accumulate_against [BFalse] (w :: ws) acc b =
  match add_fin_b_heat acc w b with
  | (acc', b', h) => (acc', b', h)
  end.
Proof.
  intros. simpl.
  destruct (add_fin_b_heat acc w b) as [[acc' b'] h].
  reflexivity.
Qed.

Lemma accumulate_against_bunknown : forall w ws acc b,
  accumulate_against [BUnknown] (w :: ws) acc b = (acc, b, fz).
Proof. intros. simpl. reflexivity. Qed.

Theorem bfalse_is_active : forall w acc b,
  w = fs fz ->
  accumulate_against [BFalse] [w] acc (fs b) <>
  accumulate_against [BUnknown] [w] acc (fs b).
Proof.
  intros w acc b Hw. subst w.
  (* Reduce both sides: BFalse adds weight, BUnknown skips *)
  simpl.
  (* Goal: (fs acc, b, fs fz) <> (acc, fs b, fz) *)
  intro Heq.
  (* Extract heat component: fs fz = fz — contradiction *)
  apply (f_equal snd) in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(******************************************************************************)
(* THEOREM 5: ALIVE ↔ BUDGET                                                *)
(******************************************************************************)

Lemma dead_is_bfalse : forall cell,
  cell_budget cell = fz ->
  cell_alive cell = BFalse.
Proof.
  intros cell H. unfold cell_alive. rewrite H. reflexivity.
Qed.

Lemma alive_has_budget : forall cell,
  cell_alive cell = BTrue ->
  exists n, cell_budget cell = fs n.
Proof.
  intros cell H. unfold cell_alive in H.
  destruct (cell_budget cell) as [| n] eqn:Hb.
  - discriminate.
  - exists n. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 6: SPEND_AUX PROPERTIES                                          *)
(*                                                                            *)
(* Was: Axiom budget_transfer_conserves in error audit (incorrect as stated  *)
(* — fails when cost > budget because spend_aux returns full cost as heat).  *)
(*                                                                            *)
(* Now: Two correct lemmas about spend_aux behavior.                         *)
(******************************************************************************)

(* Dead cells can't spend — but spend_aux records the cost as heat. *)
Lemma spend_aux_dead : forall cost,
  spend_aux fz cost = (fz, cost).
Proof.
  destruct cost; simpl; reflexivity.
Qed.

(* Zero cost does nothing. *)
Lemma spend_aux_zero_cost : forall b,
  spend_aux b fz = (b, fz).
Proof.
  destruct b; simpl; reflexivity.
Qed.

(******************************************************************************)
(* STRUCTURAL SUMMARY                                                        *)
(*                                                                            *)
(* DEFINES:                                                                  *)
(*   bool3_eq_b3          — 3-valued Bool3 equality, 1 tick                  *)
(*   PredictiveCell       — dual weights, budget, heat, NO threshold         *)
(*   accumulate_for       — BTrue inputs add to evidence-for                 *)
(*   accumulate_against   — BFalse inputs add to evidence-against            *)
(*   predict              — dual comparison, tie = BUnknown                  *)
(*   update_cell          — budget flow, weights frozen                      *)
(*   cell_alive           — structural check on budget                       *)
(*                                                                            *)
(* PROVES (7 lemmas/theorems, 0 axioms, 0 Admitted):                        *)
(*   weights_immutable        — weights never change under update            *)
(*   dead_stays_dead          — budget fz is absorbing state                 *)
(*   no_evidence_is_unknown   — empty inputs → BUnknown (budget >= 2)       *)
(*   bfalse_is_active         — BFalse ≠ BUnknown in accumulation           *)
(*   dead_is_bfalse           — dead cell reports BFalse                     *)
(*   alive_has_budget         — alive cell has fs n budget                   *)
(*   spend_aux_dead            — dead cell spend records cost as heat        *)
(*   spend_aux_zero_cost      — zero cost is identity                       *)
(*                                                                            *)
(* DOES NOT USE:                                                             *)
(*   FinProb          (no fractions in cell operations)                      *)
(*   mult_fin_heat    (no multiplication)                                    *)
(*   sub_saturate_b_heat directly (only via spend_aux)                       *)
(*   erode / constrict (deleted with void_perceptron.v)                      *)
(*   threshold : Fin  (no threshold field)                                   *)
(*   nat              (forbidden in VOID computation)                        *)
(*   Admitted          (zero)                                                *)
(******************************************************************************)

End Void_Predictive_Cell.
