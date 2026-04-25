(******************************************************************************)
(* void_predictive_learning.v — PREDICTIVE CODING WITH WEIGHT UPDATES        *)
(*                                                                            *)
(* The existing PredictiveCell in void_predictive_cell.v has dual             *)
(* accumulators but weights are immutable; update_cell only moves budget.    *)
(* This file introduces a new cell type whose weights DO change, driven by   *)
(* surprise (mismatch between prediction and truth), with full VOID           *)
(* bookkeeping.                                                               *)
(*                                                                            *)
(* Philosophy: Predictive coding, finite and mortal.                          *)
(*   Classical: delta_w = eta * (truth - prediction) * input — requires       *)
(*              reals, continuous error, implicit infinite precision.         *)
(*   VOID    : surprise is categorical (For/Against/None/Unknown), weight     *)
(*              adjustment is add/subtract on Fin, every adjustment costs     *)
(*              budget.  Cells that learn too aggressively burn out.  Cells   *)
(*              that learn too slowly survive but never adapt.                *)
(*                                                                            *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal                  *)
(* Accumulator logic is re-defined locally with _lpc suffix to avoid clash    *)
(* with Void_Predictive_Cell module.                                          *)
(* ZERO Admitted.  ZERO new Axioms.                                           *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.

Import Void_Probability_Minimal.

(******************************************************************************)
(* PART 1: THE TYPE                                                           *)
(*                                                                            *)
(* LearningPredCell extends PredictiveCell's shape with:                      *)
(*   - lpc_learning_rate: how aggressively surprise changes weights           *)
(*   - lpc_weight_max:    saturation cap so repeated strengthening cannot     *)
(*                        grow weights without bound                          *)
(******************************************************************************)

Record LearningPredCell := mkLPC {
  lpc_weights_for     : list Fin;
  lpc_weights_against : list Fin;
  lpc_budget          : Budget;
  lpc_spur            : Spuren;
  lpc_learning_rate   : FinProb;   (* eta — numerator is the Fin adjustment *)
  lpc_weight_max      : Fin        (* saturation cap on each weight *)
}.

(******************************************************************************)
(* PART 2: LOCAL DUAL ACCUMULATOR + predict                                   *)
(*                                                                            *)
(* Semantics identical to void_predictive_cell.v but redefined locally to     *)
(* avoid a module import.                                                     *)
(******************************************************************************)

Fixpoint accumulate_for_lpc (inputs : list Bool3) (ws : list Fin)
                            (acc : Fin) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match inputs, ws with
  | [], _    => (acc, b, fz)
  | _, []    => (acc, b, fz)
  | BTrue :: ins, w :: ws' =>
      match add_fin_b_spur acc w b with
      | (acc', b', h) =>
          match accumulate_for_lpc ins ws' acc' b' with
          | (r, b_final, h2) => (r, b_final, add_spur h h2)
          end
      end
  | _ :: ins, _ :: ws' =>
      accumulate_for_lpc ins ws' acc b
  end.

Fixpoint accumulate_against_lpc (inputs : list Bool3) (ws : list Fin)
                                (acc : Fin) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match inputs, ws with
  | [], _    => (acc, b, fz)
  | _, []    => (acc, b, fz)
  | BFalse :: ins, w :: ws' =>
      match add_fin_b_spur acc w b with
      | (acc', b', h) =>
          match accumulate_against_lpc ins ws' acc' b' with
          | (r, b_final, h2) => (r, b_final, add_spur h h2)
          end
      end
  | _ :: ins, _ :: ws' =>
      accumulate_against_lpc ins ws' acc b
  end.

Definition lpc_predict (cell : LearningPredCell) (inputs : list Bool3)
  : (Bool3 * Budget * Spuren) :=
  match accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell) with
  | (acc_f, b1, h1) =>
    match accumulate_against_lpc inputs (lpc_weights_against cell) fz b1 with
    | (acc_a, b2, h2) =>
      match le_fin_b3 acc_a acc_f b2 with
      | (BTrue, b3, h3) =>
        match le_fin_b3 acc_f acc_a b3 with
        | (BTrue, b4, h4) =>
            (BUnknown, b4, add_spur h1 (add_spur h2 (add_spur h3 h4)))
        | (BFalse, b4, h4) =>
            (BTrue, b4, add_spur h1 (add_spur h2 (add_spur h3 h4)))
        | (BUnknown, b4, h4) =>
            (BUnknown, b4, add_spur h1 (add_spur h2 (add_spur h3 h4)))
        end
      | (BFalse, b3, h3) =>
          (BFalse, b3, add_spur h1 (add_spur h2 h3))
      | (BUnknown, b3, h3) =>
          (BUnknown, b3, add_spur h1 (add_spur h2 h3))
      end
    end
  end.

(******************************************************************************)
(* PART 3: SURPRISE                                                           *)
(*                                                                            *)
(* Categorical mismatch signal.  The cost of computing surprise is one tick   *)
(* of budget and one Spuren, matching bool3_eq_b3 in the older cell model.    *)
(******************************************************************************)

Inductive Surprise :=
  | NoSurprise        (* prediction matched truth *)
  | SurpriseFor       (* predicted against, truth was for — strengthen for *)
  | SurpriseAgainst   (* predicted for, truth was against — strengthen against *)
  | SurpriseUnknown.  (* budget/information ran out — no learning *)

Definition compute_surprise (prediction truth : Bool3) (b : Budget)
  : (Surprise * Budget * Spuren) :=
  match b with
  | fz => (SurpriseUnknown, fz, fz)
  | fs b' =>
    match prediction, truth with
    | BTrue,    BTrue    => (NoSurprise,      b', fs fz)
    | BFalse,   BFalse   => (NoSurprise,      b', fs fz)
    | BFalse,   BTrue    => (SurpriseFor,     b', fs fz)
    | BTrue,    BFalse   => (SurpriseAgainst, b', fs fz)
    | BUnknown, _        => (SurpriseUnknown, b', fs fz)
    | _,        BUnknown => (SurpriseUnknown, b', fs fz)
    end
  end.

(******************************************************************************)
(* PART 4: WEIGHT UPDATE                                                      *)
(*                                                                            *)
(* Strengthen = saturating add of learning-rate numerator, capped at          *)
(*              lpc_weight_max.                                               *)
(* Weaken     = saturating sub of learning-rate numerator, floored at fz     *)
(*              (free via sub_saturate_b_spur semantics).                    *)
(* Every adjusted weight costs budget — no free lunch for learning.          *)
(******************************************************************************)

(* Saturating add of bonus to w, capped at max. *)
Definition sat_add (w bonus max : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match add_fin_b_spur w bonus b with
  | (sum, b', h) =>
      match le_fin_b3 sum max b' with
      | (BTrue,    b'', h2) => (sum, b'', add_spur h h2)
      | (BFalse,   b'', h2) => (max, b'', add_spur h h2)
      | (BUnknown, b'', h2) => (sum, b'', add_spur h h2)
      end
  end.

(* Saturating sub of penalty from w.  sub_saturate_b_spur already floors. *)
Definition sat_sub (w penalty : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  sub_saturate_b_spur w penalty b.

(* For each BTrue input, adjust the corresponding weight.
   direction = true  → strengthen via sat_add
   direction = false → weaken via sat_sub
   Non-BTrue inputs do not touch their weight and cost nothing. *)
Fixpoint update_weights_rec (inputs : list Bool3) (ws : list Fin)
                            (direction : bool) (lr_num : Fin) (max : Fin)
                            (b : Budget)
  : (list Fin * Budget * Spuren) :=
  match inputs, ws with
  | [], _ => ([], b, fz)
  | _, [] => ([], b, fz)
  | BTrue :: ins, w :: ws' =>
      match
        (if direction
         then sat_add w lr_num max b
         else sat_sub w lr_num b)
      with
      | (w', b', h) =>
          match update_weights_rec ins ws' direction lr_num max b' with
          | (rest_ws, b'', h2) => (w' :: rest_ws, b'', add_spur h h2)
          end
      end
  | _ :: ins, w :: ws' =>
      match update_weights_rec ins ws' direction lr_num max b with
      | (rest_ws, b', h) => (w :: rest_ws, b', h)
      end
  end.

(* Apply the update rule dictated by the Surprise value. *)
Definition update_weights (cell : LearningPredCell)
                          (inputs : list Bool3)
                          (surprise : Surprise)
  : LearningPredCell :=
  let lr_num := fst (lpc_learning_rate cell) in
  let max    := lpc_weight_max cell in
  match surprise with
  | NoSurprise =>
      cell
  | SurpriseFor =>
      (* Strengthen weights_for, weaken weights_against on active inputs. *)
      match update_weights_rec inputs (lpc_weights_for cell)
                               true  lr_num max (lpc_budget cell) with
      | (new_for, b1, h1) =>
          match update_weights_rec inputs (lpc_weights_against cell)
                                   false lr_num max b1 with
          | (new_against, b2, h2) =>
              mkLPC new_for new_against b2
                    (add_spur (lpc_spur cell) (add_spur h1 h2))
                    (lpc_learning_rate cell) max
          end
      end
  | SurpriseAgainst =>
      (* Strengthen weights_against, weaken weights_for on active inputs. *)
      match update_weights_rec inputs (lpc_weights_for cell)
                               false lr_num max (lpc_budget cell) with
      | (new_for, b1, h1) =>
          match update_weights_rec inputs (lpc_weights_against cell)
                                   true  lr_num max b1 with
          | (new_against, b2, h2) =>
              mkLPC new_for new_against b2
                    (add_spur (lpc_spur cell) (add_spur h1 h2))
                    (lpc_learning_rate cell) max
          end
      end
  | SurpriseUnknown =>
      cell
  end.

(******************************************************************************)
(* PART 5: FULL LEARNING STEP                                                 *)
(*                                                                            *)
(* One cycle: predict → compare → adjust weights.                             *)
(* Every sub-step threads budget and Spuren.                                  *)
(******************************************************************************)

Definition learn_step (cell : LearningPredCell) (inputs : list Bool3)
                      (truth : Bool3)
  : LearningPredCell :=
  match lpc_predict cell inputs with
  | (prediction, b1, h1) =>
      match compute_surprise prediction truth b1 with
      | (surp, b2, h2) =>
          let cell' :=
            mkLPC (lpc_weights_for cell)
                  (lpc_weights_against cell)
                  b2
                  (add_spur (lpc_spur cell) (add_spur h1 h2))
                  (lpc_learning_rate cell)
                  (lpc_weight_max cell) in
          update_weights cell' inputs surp
      end
  end.

(******************************************************************************)
(* PART 6: THEOREMS                                                           *)
(******************************************************************************)

(* Helper: update_weights with NoSurprise or SurpriseUnknown returns cell
   unchanged (no new record constructed). *)
Lemma update_weights_nosurprise : forall cell inputs,
  update_weights cell inputs NoSurprise = cell.
Proof. intros. unfold update_weights. reflexivity. Qed.

Lemma update_weights_unknown : forall cell inputs,
  update_weights cell inputs SurpriseUnknown = cell.
Proof. intros. unfold update_weights. reflexivity. Qed.

(* THEOREM 1: no surprise → weights unchanged.
   If the prediction equals the truth (including the BUnknown=BUnknown case
   which routes through SurpriseUnknown), neither weight vector changes. *)
Theorem no_surprise_preserves_weights :
  forall cell inputs truth prediction b_pred h_pred,
    lpc_predict cell inputs = (prediction, b_pred, h_pred) ->
    prediction = truth ->
    lpc_weights_for     (learn_step cell inputs truth) = lpc_weights_for     cell
    /\
    lpc_weights_against (learn_step cell inputs truth) = lpc_weights_against cell.
Proof.
  intros cell inputs truth prediction b_pred h_pred Hpred Heq.
  unfold learn_step.
  rewrite Hpred.
  subst truth.
  (* Case on prediction.  In every matched case compute_surprise yields
     NoSurprise or SurpriseUnknown, and update_weights then returns the
     intermediate cell' unchanged — whose weights are cell's weights. *)
  destruct prediction; destruct b_pred as [| b_pred'];
    simpl; split; reflexivity.
Qed.

(* Helper: add_fin_b_spur at budget fz is a no-op returning (n, fz, fz). *)
Lemma add_fin_b_spur_zero_budget : forall n m,
  add_fin_b_spur n m fz = (n, fz, fz).
Proof. intros n m. destruct m; reflexivity. Qed.

(* Helper: le_fin_b3 at budget fz always returns BUnknown, fz, fz.
   le_fin_b3 is Coq-detected to recurse on n, so we destruct n to unlock. *)
Lemma le_fin_b3_zero_budget : forall n m,
  le_fin_b3 n m fz = (BUnknown, fz, fz).
Proof. intros n m. destruct n; reflexivity. Qed.

(* Helper: accumulate_for_lpc at budget fz always returns budget fz.
   We destruct i BEFORE ws so simpl can fully reduce the match. *)
Lemma accumulate_for_lpc_zero_budget : forall inputs ws acc r b h,
  accumulate_for_lpc inputs ws acc fz = (r, b, h) -> b = fz.
Proof.
  induction inputs as [| i ins IH]; intros ws acc r b h Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - destruct i; destruct ws as [| w ws']; simpl in Heq.
    + (* BTrue, [] *) inversion Heq. reflexivity.
    + (* BTrue, w :: ws' *)
      rewrite add_fin_b_spur_zero_budget in Heq.
      destruct (accumulate_for_lpc ins ws' acc fz) as [[r' b'] h'] eqn:Erec.
      inversion Heq; subst.
      eapply IH. eassumption.
    + (* BFalse, [] *) inversion Heq. reflexivity.
    + (* BFalse, w :: ws' *) eapply IH; eassumption.
    + (* BUnknown, [] *) inversion Heq. reflexivity.
    + (* BUnknown, w :: ws' *) eapply IH; eassumption.
Qed.

(* Helper: accumulate_against_lpc at budget fz always returns budget fz. *)
Lemma accumulate_against_lpc_zero_budget : forall inputs ws acc r b h,
  accumulate_against_lpc inputs ws acc fz = (r, b, h) -> b = fz.
Proof.
  induction inputs as [| i ins IH]; intros ws acc r b h Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - destruct i; destruct ws as [| w ws']; simpl in Heq.
    + (* BTrue, [] *) inversion Heq. reflexivity.
    + (* BTrue, w :: ws' *) eapply IH; eassumption.
    + (* BFalse, [] *) inversion Heq. reflexivity.
    + (* BFalse, w :: ws' *)
      rewrite add_fin_b_spur_zero_budget in Heq.
      destruct (accumulate_against_lpc ins ws' acc fz) as [[r' b'] h'] eqn:Erec.
      inversion Heq; subst.
      eapply IH. eassumption.
    + (* BUnknown, [] *) inversion Heq. reflexivity.
    + (* BUnknown, w :: ws' *) eapply IH; eassumption.
Qed.

(* THEOREM 2: dead cell does not learn.
   Budget exhausted → learn_step preserves weights and keeps budget at fz. *)
Theorem dead_cell_no_learning : forall cell inputs truth,
  lpc_budget cell = fz ->
  lpc_budget           (learn_step cell inputs truth) = fz
  /\
  lpc_weights_for      (learn_step cell inputs truth) = lpc_weights_for     cell
  /\
  lpc_weights_against  (learn_step cell inputs truth) = lpc_weights_against cell.
Proof.
  intros cell inputs truth Hdead.
  unfold learn_step.
  destruct (lpc_predict cell inputs) as [[prediction b_pred] h_pred] eqn:Epred.
  (* Show b_pred = fz via the two accumulator helpers. *)
  assert (Hb : b_pred = fz).
  { unfold lpc_predict in Epred.
    rewrite Hdead in Epred.
    destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz fz)
      as [[acc_f b1] h1] eqn:E1.
    pose proof (accumulate_for_lpc_zero_budget _ _ _ _ _ _ E1) as Hb1.
    subst b1.
    destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz fz)
      as [[acc_a b2] h2] eqn:E2.
    pose proof (accumulate_against_lpc_zero_budget _ _ _ _ _ _ E2) as Hb2.
    subst b2.
    (* At this point Epred: match le_fin_b3 acc_a acc_f fz with ... = ...
       Use the le_fin_b3_zero_budget rewrite to collapse the first compare. *)
    rewrite le_fin_b3_zero_budget in Epred.
    simpl in Epred. inversion Epred. reflexivity. }
  subst b_pred.
  (* compute_surprise prediction truth fz = (SurpriseUnknown, fz, fz), so
     learn_step reduces to the cell' placed into update_weights with
     SurpriseUnknown, which returns cell' itself. *)
  simpl.
  split; [| split]; reflexivity.
Qed.

(* Helper: update_weights_rec preserves list length. *)
Lemma update_weights_rec_preserves_length :
  forall inputs ws direction lr_num max b ws' b' h,
    update_weights_rec inputs ws direction lr_num max b = (ws', b', h) ->
    length ws' = length (firstn (length inputs) ws).
Proof.
  induction inputs as [| i ins IH]; intros ws direction lr_num max b ws' b' h Heq.
  - simpl in Heq. inversion Heq. simpl. reflexivity.
  - destruct i; destruct ws as [| w ws_rest]; simpl in Heq.
    + (* BTrue, [] *) inversion Heq. reflexivity.
    + (* BTrue, w :: ws_rest *)
      destruct (if direction
                then sat_add w lr_num max b
                else sat_sub w lr_num b)
        as [[w_new b_new] h_new] eqn:Estep.
      destruct (update_weights_rec ins ws_rest direction lr_num max b_new)
        as [[ws_tail b_tail] h_tail] eqn:Erec.
      inversion Heq; subst.
      simpl. f_equal. eapply IH; eauto.
    + (* BFalse, [] *) inversion Heq. reflexivity.
    + (* BFalse, w :: ws_rest *)
      destruct (update_weights_rec ins ws_rest direction lr_num max b)
        as [[ws_tail b_tail] h_tail] eqn:Erec.
      inversion Heq; subst.
      simpl. f_equal. eapply IH; eauto.
    + (* BUnknown, [] *) inversion Heq. reflexivity.
    + (* BUnknown, w :: ws_rest *)
      destruct (update_weights_rec ins ws_rest direction lr_num max b)
        as [[ws_tail b_tail] h_tail] eqn:Erec.
      inversion Heq; subst.
      simpl. f_equal. eapply IH; eauto.
Qed.

(* THEOREM 3: learn_step preserves the length of both weight vectors,
   provided the input list is at least as long as each weight vector.
   This is the dimensional-consistency guarantee: learning cannot drop
   or duplicate weight slots. *)
Theorem learning_preserves_weight_length :
  forall cell inputs truth,
    length (lpc_weights_for cell)     <= length inputs ->
    length (lpc_weights_against cell) <= length inputs ->
    length (lpc_weights_for     (learn_step cell inputs truth)) =
    length (lpc_weights_for     cell) /\
    length (lpc_weights_against (learn_step cell inputs truth)) =
    length (lpc_weights_against cell).
Proof.
  intros cell inputs truth Hfor Hag.
  unfold learn_step.
  destruct (lpc_predict cell inputs) as [[prediction b_pred] h_pred] eqn:Epred.
  destruct (compute_surprise prediction truth b_pred)
    as [[surp b_s] h_s] eqn:Esurp.
  (* update_weights: case on surp. *)
  destruct surp; simpl; try (split; reflexivity).
  - (* SurpriseFor *)
    destruct (update_weights_rec inputs (lpc_weights_for cell)
                                 true  (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b_s)
      as [[new_for b1'] h1'] eqn:Eu1.
    destruct (update_weights_rec inputs (lpc_weights_against cell)
                                 false (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b1')
      as [[new_ag b2'] h2'] eqn:Eu2.
    simpl. split.
    + rewrite (update_weights_rec_preserves_length _ _ _ _ _ _ _ _ _ Eu1).
      rewrite List.firstn_all2; [reflexivity | exact Hfor].
    + rewrite (update_weights_rec_preserves_length _ _ _ _ _ _ _ _ _ Eu2).
      rewrite List.firstn_all2; [reflexivity | exact Hag].
  - (* SurpriseAgainst *)
    destruct (update_weights_rec inputs (lpc_weights_for cell)
                                 false (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b_s)
      as [[new_for b1'] h1'] eqn:Eu1.
    destruct (update_weights_rec inputs (lpc_weights_against cell)
                                 true  (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b1')
      as [[new_ag b2'] h2'] eqn:Eu2.
    simpl. split.
    + rewrite (update_weights_rec_preserves_length _ _ _ _ _ _ _ _ _ Eu1).
      rewrite List.firstn_all2; [reflexivity | exact Hfor].
    + rewrite (update_weights_rec_preserves_length _ _ _ _ _ _ _ _ _ Eu2).
      rewrite List.firstn_all2; [reflexivity | exact Hag].
Qed.

(* THEOREM 4: learn_step preserves the learning rate and weight cap.
   These scalars describe the cell's identity and cannot drift under
   normal operation. *)
Theorem learning_preserves_hyperparameters : forall cell inputs truth,
  lpc_learning_rate (learn_step cell inputs truth) = lpc_learning_rate cell /\
  lpc_weight_max    (learn_step cell inputs truth) = lpc_weight_max    cell.
Proof.
  intros cell inputs truth.
  unfold learn_step.
  destruct (lpc_predict cell inputs) as [[prediction b_pred] h_pred] eqn:Epred.
  destruct (compute_surprise prediction truth b_pred)
    as [[surp b_s] h_s] eqn:Esurp.
  destruct surp; simpl.
  - (* NoSurprise: update_weights returns cell' unchanged. *)
    split; reflexivity.
  - (* SurpriseFor *)
    destruct (update_weights_rec inputs (lpc_weights_for cell)
                                 true  (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b_s)
      as [[new_for b1'] h1'] eqn:Eu1.
    destruct (update_weights_rec inputs (lpc_weights_against cell)
                                 false (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b1')
      as [[new_ag b2'] h2'] eqn:Eu2.
    simpl. split; reflexivity.
  - (* SurpriseAgainst *)
    destruct (update_weights_rec inputs (lpc_weights_for cell)
                                 false (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b_s)
      as [[new_for b1'] h1'] eqn:Eu1.
    destruct (update_weights_rec inputs (lpc_weights_against cell)
                                 true  (fst (lpc_learning_rate cell))
                                 (lpc_weight_max cell) b1')
      as [[new_ag b2'] h2'] eqn:Eu2.
    simpl. split; reflexivity.
  - (* SurpriseUnknown *)
    split; reflexivity.
Qed.

(******************************************************************************)
(* PREDICTIVE CODING IN VOID                                                  *)
(*                                                                            *)
(* Classical predictive coding: delta_w = eta * (truth - prediction) * input  *)
(* requires subtraction on reals, a continuous error signal, and implicitly   *)
(* infinite precision.                                                        *)
(*                                                                            *)
(* VOID predictive coding: surprise is categorical (For / Against / None /    *)
(* Unknown), weight adjustment is finite (add or subtract eta on Fin),        *)
(* every adjustment costs budget.  The cell that learns too aggressively      *)
(* (high eta) burns through budget and dies.  The cell that learns too        *)
(* slowly (low eta) survives but never adapts.  The optimal learning rate     *)
(* is the one that balances adaptation against survival.                      *)
(*                                                                            *)
(* This is not an approximation of backprop.  It is a different theory of     *)
(* learning: local, finite, mortal.                                           *)
(******************************************************************************)
