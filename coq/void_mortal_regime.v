(******************************************************************************)
(* void_mortal_regime.v — FIGHT / FLIGHT / FREEZE AS THEOREMS                *)
(*                                                                            *)
(* Three regimes of a LearningPredCell — defined STRUCTURALLY on the result  *)
(* of learn_step, not on arbitrary numerical thresholds.                      *)
(*                                                                            *)
(*   Freeze  : lpc_predict returns BUnknown.  The cell does not see.          *)
(*   Flight  : predict returns BTrue/BFalse, but compute_surprise returns     *)
(*             SurpriseUnknown.  The cell sees but cannot judge.              *)
(*   Fight   : predict returns BTrue/BFalse and compute_surprise returns one  *)
(*             of NoSurprise / SurpriseFor / SurpriseAgainst.  The cell      *)
(*             sees and judges (and may or may not learn — learning is the    *)
(*             next step, not part of the regime).                            *)
(*                                                                            *)
(* This is the "fear is a theorem" claim from the Mortal Predictor pitch:    *)
(* the freeze/flight/fight triad is not programmed.  It falls out of the      *)
(* arithmetic of finite budget.                                               *)
(*                                                                            *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal,                 *)
(*             void_predictive_learning, void_probability_geometry            *)
(* ZERO Admitted.  ZERO new Axioms.                                           *)
(******************************************************************************)
Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_predictive_learning.
Require Import void_probability_geometry.
Import Void_Probability_Minimal.
Import Void_Probability_Geometry.
(******************************************************************************)
(* PART 1: THE THREE REGIMES AS PROPOSITIONS                                 *)
(*                                                                            *)
(* Each regime is a Prop on (cell, inputs[, truth]).  Definition is observa- *)
(* tional: we do not classify budget into intervals.  We look at what the    *)
(* cell actually did and report the regime.                                   *)
(******************************************************************************)
(* Helper: project the prediction out of lpc_predict. *)
Definition predict_value (cell : LearningPredCell) (inputs : list Bool3) : Bool3 :=
  match lpc_predict cell inputs with
  | (pred, _, _) => pred
  end.
(* Helper: project the budget remaining after lpc_predict. *)
Definition predict_budget (cell : LearningPredCell) (inputs : list Bool3) : Budget :=
  match lpc_predict cell inputs with
  | (_, b, _) => b
  end.
(* Helper: the surprise computed inside learn_step for given truth. *)
Definition surprise_value (cell : LearningPredCell) (inputs : list Bool3)
                          (truth : Bool3) : Surprise :=
  match lpc_predict cell inputs with
  | (pred, b_pred, _) =>
      match compute_surprise pred truth b_pred with
      | (s, _, _) => s
      end
  end.
(* Freeze: the cell does not see.  Independent of truth. *)
Definition InFreeze (cell : LearningPredCell) (inputs : list Bool3) : Prop :=
  predict_value cell inputs = BUnknown.
(* Flight: the cell sees but cannot judge. *)
Definition InFlight (cell : LearningPredCell) (inputs : list Bool3)
                    (truth : Bool3) : Prop :=
  (predict_value cell inputs = BTrue \/ predict_value cell inputs = BFalse)
  /\ surprise_value cell inputs truth = SurpriseUnknown.
(* Fight: the cell sees and judges. *)
Definition InFight (cell : LearningPredCell) (inputs : list Bool3)
                   (truth : Bool3) : Prop :=
  (predict_value cell inputs = BTrue \/ predict_value cell inputs = BFalse)
  /\ surprise_value cell inputs truth <> SurpriseUnknown.
(******************************************************************************)
(* PART 2: LEMMA A — TOTALITY AND MUTUAL EXCLUSION                           *)
(*                                                                            *)
(* Every (cell, inputs, truth) lies in exactly one regime.                    *)
(******************************************************************************)
(* Totality: at least one regime holds. *)
Theorem regime_total : forall cell inputs truth,
  InFreeze cell inputs
  \/ InFlight cell inputs truth
  \/ InFight  cell inputs truth.
Proof.
  intros cell inputs truth.
  unfold InFreeze, InFlight, InFight.
  destruct (predict_value cell inputs) eqn:Epred.
  - (* prediction = BTrue *)
    destruct (surprise_value cell inputs truth) eqn:Esurp.
    + (* NoSurprise *) right. right. split.
      * left. reflexivity.
      * discriminate.
    + (* SurpriseFor *) right. right. split.
      * left. reflexivity.
      * discriminate.
    + (* SurpriseAgainst *) right. right. split.
      * left. reflexivity.
      * discriminate.
    + (* SurpriseUnknown *) right. left. split.
      * left. reflexivity.
      * reflexivity.
  - (* prediction = BFalse *)
    destruct (surprise_value cell inputs truth) eqn:Esurp.
    + right. right. split.
      * right. reflexivity.
      * discriminate.
    + right. right. split.
      * right. reflexivity.
      * discriminate.
    + right. right. split.
      * right. reflexivity.
      * discriminate.
    + right. left. split.
      * right. reflexivity.
      * reflexivity.
  - (* prediction = BUnknown — Freeze *)
    left. reflexivity.
Qed.
(* Mutual exclusion: Freeze and Flight cannot coexist. *)
Theorem freeze_flight_exclusive : forall cell inputs truth,
  InFreeze cell inputs ->
  ~ InFlight cell inputs truth.
Proof.
  intros cell inputs truth Hfreeze Hflight.
  unfold InFreeze in Hfreeze.
  unfold InFlight in Hflight.
  destruct Hflight as [Hpred _].
  destruct Hpred as [H | H]; rewrite Hfreeze in H; discriminate.
Qed.
(* Mutual exclusion: Freeze and Fight cannot coexist. *)
Theorem freeze_fight_exclusive : forall cell inputs truth,
  InFreeze cell inputs ->
  ~ InFight cell inputs truth.
Proof.
  intros cell inputs truth Hfreeze Hfight.
  unfold InFreeze in Hfreeze.
  unfold InFight in Hfight.
  destruct Hfight as [Hpred _].
  destruct Hpred as [H | H]; rewrite Hfreeze in H; discriminate.
Qed.
(* Mutual exclusion: Flight and Fight cannot coexist. *)
Theorem flight_fight_exclusive : forall cell inputs truth,
  InFlight cell inputs truth ->
  ~ InFight cell inputs truth.
Proof.
  intros cell inputs truth Hflight Hfight.
  unfold InFlight in Hflight.
  unfold InFight in Hfight.
  destruct Hflight as [_ Hsurp_unk].
  destruct Hfight  as [_ Hsurp_def].
  apply Hsurp_def. exact Hsurp_unk.
Qed.
(******************************************************************************)
(* PART 3: LEMMA C — SURPRISE COST IS STRICT                                 *)
(*                                                                            *)
(* compute_surprise only returns NoSurprise / SurpriseFor / SurpriseAgainst   *)
(* when it was given budget of the form (fs b'), and in that case it returns *)
(* exactly b'.  The cell pays ONE unit of budget for every act of judgment. *)
(* If it pays nothing (budget was fz), the result is SurpriseUnknown.         *)
(*                                                                            *)
(* Corollary: in Fight regime, every step strictly decreases the budget fed  *)
(* into compute_surprise.  Finite budget + strict decrease = Fight cannot    *)
(* be sustained forever.                                                      *)
(******************************************************************************)
Theorem surprise_cost_strict : forall pred truth b s b_out h,
  compute_surprise pred truth b = (s, b_out, h) ->
  s <> SurpriseUnknown ->
  b = fs b_out.
Proof.
  intros pred truth b s b_out h Hcs Hneq.
  unfold compute_surprise in Hcs.
  destruct b as [| b'].
  - (* b = fz : compute_surprise returns (SurpriseUnknown, fz, fz)       *)
    (*          so s = SurpriseUnknown — contradicts Hneq.                *)
    inversion Hcs. subst s. exfalso. apply Hneq. reflexivity.
  - (* b = fs b' : every concrete match returns (_, b', _).               *)
    (* We must eliminate the cases that return SurpriseUnknown (pred or   *)
    (* truth = BUnknown), which Hneq rules out.                           *)
    destruct pred; destruct truth; inversion Hcs; subst;
      try reflexivity;
      try (exfalso; apply Hneq; reflexivity).
Qed.
(* Corollary: compute_surprise never INCREASES the budget (weaker but      *)
(* sometimes more convenient than the strict version above).                *)
Corollary surprise_budget_le : forall pred truth b s b_out h,
  compute_surprise pred truth b = (s, b_out, h) ->
  leF b_out b.
Proof.
  intros pred truth b s b_out h Hcs.
  unfold compute_surprise in Hcs.
  destruct b as [| b'].
  - inversion Hcs. subst. apply leF_refl.
  - destruct pred; destruct truth; inversion Hcs; subst;
      apply leF_step.
Qed.
(******************************************************************************)
(* PART 4: BUDGET MONOTONICITY — HELPER LEMMAS FOR LEMMA B                   *)
(*                                                                            *)
(* Per Tomasz: the library has fin_eq_b3_budget_le but NOT the following     *)
(* chain.  We prove them here, inside void_mortal_regime.v, so existing      *)
(* files stay untouched.                                                      *)
(*                                                                            *)
(*   4.1  add_fin_b_spur_budget_le        : atomic                            *)
(*   4.2  accumulate_for_lpc_budget_le    : depends on 4.1                    *)
(*   4.3  accumulate_against_lpc_budget_le: symmetric to 4.2                  *)
(*   4.4  le_fin_b3_budget_le             : atomic                            *)
(*   4.5  lpc_predict_budget_le           : combines 4.2, 4.3, 4.4            *)
(******************************************************************************)
(* 4.1 -------------------------------------------------------------------- *)
Lemma add_fin_b_spur_budget_le : forall n m b r b_out h,
  add_fin_b_spur n m b = (r, b_out, h) ->
  leF b_out b.
Proof.
  intros n m. induction m as [| m' IH]; intros b r b_out h Hadd.
  - (* m = fz : add_fin_b_spur returns (n, b, fz) *)
    simpl in Hadd. inversion Hadd. subst. apply leF_refl.
  - (* m = fs m' *)
    destruct b as [| b'].
    + (* b = fz : returns (n, fz, fz) *)
      simpl in Hadd. inversion Hadd. subst. apply leF_refl.
    + (* b = fs b' : recurse with b' *)
      simpl in Hadd.
      destruct (add_fin_b_spur n m' b') as [[r' b''] h''] eqn:Erec.
      specialize (IH b' r' b'' h'' Erec).
      inversion Hadd. subst.
      apply leF_trans with b'.
      * exact IH.
      * apply leF_step.
Qed.
(* 4.2 -------------------------------------------------------------------- *)
Lemma accumulate_for_lpc_budget_le : forall inputs ws acc b r b_out h,
  accumulate_for_lpc inputs ws acc b = (r, b_out, h) ->
  leF b_out b.
Proof.
  induction inputs as [| i ins IH]; intros ws acc b r b_out h Hacc.
  - (* inputs = [] : returns (acc, b, fz) *)
    simpl in Hacc. inversion Hacc. subst. apply leF_refl.
  - destruct ws as [| w ws'].
    + (* ws = [] : returns (acc, b, fz).  Must destruct i so simpl fires. *)
      destruct i; simpl in Hacc; inversion Hacc; subst; apply leF_refl.
    + destruct i; simpl in Hacc.
      * (* BTrue :: ins — costs add_fin_b_spur + recursion *)
        destruct (add_fin_b_spur acc w b) as [[acc' b1] h1] eqn:Eadd.
        destruct (accumulate_for_lpc ins ws' acc' b1) as [[r' b''] h''] eqn:Erec.
        assert (Hrec : leF b'' b1)
          by (apply (IH ws' acc' b1 r' b'' h''); exact Erec).
        assert (Hadd : leF b1 b)
          by (apply (add_fin_b_spur_budget_le acc w b acc' b1 h1); exact Eadd).
        inversion Hacc. subst.
        apply leF_trans with b1; assumption.
      * (* BFalse :: ins — free recursion *)
        apply (IH ws' acc b r b_out h). exact Hacc.
      * (* BUnknown :: ins — free recursion *)
        apply (IH ws' acc b r b_out h). exact Hacc.
Qed.
(* 4.3 -------------------------------------------------------------------- *)
Lemma accumulate_against_lpc_budget_le : forall inputs ws acc b r b_out h,
  accumulate_against_lpc inputs ws acc b = (r, b_out, h) ->
  leF b_out b.
Proof.
  induction inputs as [| i ins IH]; intros ws acc b r b_out h Hacc.
  - simpl in Hacc. inversion Hacc. subst. apply leF_refl.
  - destruct ws as [| w ws'].
    + destruct i; simpl in Hacc; inversion Hacc; subst; apply leF_refl.
    + destruct i; simpl in Hacc.
      * (* BTrue :: ins — free *)
        apply (IH ws' acc b r b_out h). exact Hacc.
      * (* BFalse :: ins — costs add_fin_b_spur + recursion *)
        destruct (add_fin_b_spur acc w b) as [[acc' b1] h1] eqn:Eadd.
        destruct (accumulate_against_lpc ins ws' acc' b1) as [[r' b''] h''] eqn:Erec.
        assert (Hrec : leF b'' b1)
          by (apply (IH ws' acc' b1 r' b'' h''); exact Erec).
        assert (Hadd : leF b1 b)
          by (apply (add_fin_b_spur_budget_le acc w b acc' b1 h1); exact Eadd).
        inversion Hacc. subst.
        apply leF_trans with b1; assumption.
      * (* BUnknown :: ins — free *)
        apply (IH ws' acc b r b_out h). exact Hacc.
Qed.
(* 4.4 -------------------------------------------------------------------- *)
Lemma le_fin_b3_budget_le : forall n m b r b_out h,
  le_fin_b3 n m b = (r, b_out, h) ->
  leF b_out b.
Proof.
  intros n. induction n as [| n' IH]; intros m b r b_out h Hle.
  - (* n = fz *)
    destruct b as [| b'].
    + simpl in Hle. inversion Hle. subst. apply leF_refl.
    + simpl in Hle. inversion Hle. subst. apply leF_step.
  - (* n = fs n' *)
    destruct b as [| b'].
    + simpl in Hle. inversion Hle. subst. apply leF_refl.
    + destruct m as [| m'].
      * simpl in Hle. inversion Hle. subst. apply leF_step.
      * simpl in Hle.
        destruct (le_fin_b3 n' m' b') as [[r' b''] h''] eqn:Erec.
        assert (Hrec : leF b'' b')
          by (apply (IH m' b' r' b'' h''); exact Erec).
        inversion Hle. subst.
        apply leF_trans with b'.
        -- exact Hrec.
        -- apply leF_step.
Qed.
(* 4.5 -------------------------------------------------------------------- *)
Lemma lpc_predict_budget_le : forall cell inputs pred b_out h,
  lpc_predict cell inputs = (pred, b_out, h) ->
  leF b_out (lpc_budget cell).
Proof.
  intros cell inputs pred b_out h Hpred.
  unfold lpc_predict in Hpred.
  destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell))
    as [[acc_f b1] h1] eqn:Eacc_f.
  destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz b1)
    as [[acc_a b2] h2] eqn:Eacc_a.
  destruct (le_fin_b3 acc_a acc_f b2) as [[r3 b3] h3] eqn:Ele1.
  (* Budget chain: lpc_budget cell → b1 → b2 → b3 → possibly b4, all ≤. *)
  assert (Hb1 : leF b1 (lpc_budget cell)).
  { apply (accumulate_for_lpc_budget_le inputs (lpc_weights_for cell) fz
            (lpc_budget cell) acc_f b1 h1). exact Eacc_f. }
  assert (Hb2 : leF b2 b1).
  { apply (accumulate_against_lpc_budget_le inputs (lpc_weights_against cell) fz
            b1 acc_a b2 h2). exact Eacc_a. }
  assert (Hb3 : leF b3 b2).
  { apply (le_fin_b3_budget_le acc_a acc_f b2 r3 b3 h3). exact Ele1. }
  destruct r3.
  - (* BTrue — enter second comparison *)
    destruct (le_fin_b3 acc_f acc_a b3) as [[r4 b4] h4] eqn:Ele2.
    assert (Hb4 : leF b4 b3).
    { apply (le_fin_b3_budget_le acc_f acc_a b3 r4 b4 h4). exact Ele2. }
    destruct r4; inversion Hpred; subst;
      apply leF_trans with b3; try exact Hb4;
      apply leF_trans with b2; try exact Hb3;
      apply leF_trans with b1; assumption.
  - (* BFalse *)
    inversion Hpred. subst.
    apply leF_trans with b2. exact Hb3.
    apply leF_trans with b1; assumption.
  - (* BUnknown *)
    inversion Hpred. subst.
    apply leF_trans with b2. exact Hb3.
    apply leF_trans with b1; assumption.
Qed.
(* 4.6  BUnknown is stable under budget decrease.                             *)
(* Contrapositive of le_fin_b3_budget_true + le_fin_b3_budget_false           *)
(* (both in void_probability_geometry.v).                                     *)
Lemma le_fin_b3_budget_unknown : forall n m b1 b2,
  bool3_of (le_fin_b3 n m b1) = BUnknown ->
  leF b2 b1 ->
  bool3_of (le_fin_b3 n m b2) = BUnknown.
Proof.
  intros n m b1 b2 Hun Hle.
  destruct (bool3_of (le_fin_b3 n m b2)) eqn:Ecase.
  - exfalso.
    assert (Hrise : bool3_of (le_fin_b3 n m b1) = BTrue).
    { apply (le_fin_b3_budget_true n m b2 Ecase b1 Hle). }
    rewrite Hrise in Hun. discriminate.
  - exfalso.
    assert (Hrise : bool3_of (le_fin_b3 n m b1) = BFalse).
    { apply (le_fin_b3_budget_false n m b2 Ecase b1 Hle). }
    rewrite Hrise in Hun. discriminate.
  - reflexivity.
Qed.
(******************************************************************************)
(* PART 5: LEMMA B — FREEZE IS ABSORBING (same-inputs variant)               *)
(*                                                                            *)
(* If cell is in Freeze for given inputs, then after one learn_step with the *)
(* same inputs, the resulting cell is still in Freeze for those inputs.      *)
(*                                                                            *)
(* Proof idea.  In the freeze case, prediction is BUnknown, so               *)
(* compute_surprise returns SurpriseUnknown, so update_weights returns the   *)
(* intermediate cell' unchanged.  cell' has the SAME weights as cell, but    *)
(* strictly smaller (leF) budget.  We then need: lpc_predict at smaller      *)
(* budget (same weights) still gives BUnknown.                                *)
(*                                                                            *)
(* Caveat: partial accumulation under lower budget can change acc_f, acc_a.  *)
(* So we cannot just reuse the le_fin_b3 budget stability lemmas blindly.    *)
(* We case-split on the original freeze path and argue each case closes.     *)
(******************************************************************************)
(* Helper: unfold predict_value once so we can reason about the triple. *)
Lemma predict_value_eq_BUnknown_iff : forall cell inputs,
  predict_value cell inputs = BUnknown <->
  exists b_out h, lpc_predict cell inputs = (BUnknown, b_out, h).
Proof.
  intros cell inputs. unfold predict_value. split.
  - intros H. destruct (lpc_predict cell inputs) as [[p b] h] eqn:E.
    subst p. exists b, h. reflexivity.
  - intros [b_out [h Heq]]. rewrite Heq. reflexivity.
Qed.
(* Helper: in the freeze case, learn_step produces a cell with SAME weights,
   SAME learning_rate, SAME weight_max — only budget and spur change. *)
Lemma learn_step_freeze_preserves_shape :
  forall cell inputs truth,
    predict_value cell inputs = BUnknown ->
    lpc_weights_for      (learn_step cell inputs truth) = lpc_weights_for     cell /\
    lpc_weights_against  (learn_step cell inputs truth) = lpc_weights_against cell /\
    lpc_learning_rate    (learn_step cell inputs truth) = lpc_learning_rate   cell /\
    lpc_weight_max       (learn_step cell inputs truth) = lpc_weight_max      cell.
Proof.
  intros cell inputs truth Hfreeze.
  unfold predict_value in Hfreeze.
  destruct (lpc_predict cell inputs) as [[pred b_pred] h_pred] eqn:Epred.
  simpl in Hfreeze. subst pred.
  unfold learn_step. rewrite Epred.
  destruct (compute_surprise BUnknown truth b_pred) as [[surp b2] h2] eqn:Ecs.
  (* surp must be SurpriseUnknown because prediction = BUnknown *)
  assert (Hsurp : surp = SurpriseUnknown).
  { unfold compute_surprise in Ecs.
    destruct b_pred as [| b_pred']; inversion Ecs; reflexivity. }
  subst surp.
  rewrite update_weights_unknown.
  simpl. repeat split; reflexivity.
Qed.
(* Helper: in the freeze case, learn_step leaves budget ≤ original budget. *)
Lemma learn_step_freeze_budget_le :
  forall cell inputs truth,
    predict_value cell inputs = BUnknown ->
    leF (lpc_budget (learn_step cell inputs truth)) (lpc_budget cell).
Proof.
  intros cell inputs truth Hfreeze.
  unfold predict_value in Hfreeze.
  destruct (lpc_predict cell inputs) as [[pred b_pred] h_pred] eqn:Epred.
  simpl in Hfreeze. subst pred.
  unfold learn_step. rewrite Epred.
  destruct (compute_surprise BUnknown truth b_pred) as [[surp b2] h2] eqn:Ecs.
  assert (Hsurp : surp = SurpriseUnknown).
  { unfold compute_surprise in Ecs.
    destruct b_pred as [| b_pred']; inversion Ecs; reflexivity. }
  subst surp.
  rewrite update_weights_unknown.
  simpl.
  (* budget is b2.  b2 ≤ b_pred by surprise_budget_le, b_pred ≤ lpc_budget cell
     by lpc_predict_budget_le. *)
  apply leF_trans with b_pred.
  - apply (surprise_budget_le BUnknown truth b_pred SurpriseUnknown b2 h2).
    exact Ecs.
  - apply (lpc_predict_budget_le cell inputs BUnknown b_pred h_pred). exact Epred.
Qed.
(******************************************************************************)
(* PART 5B: DETERMINISM HELPERS FOR LEMMA B                                  *)
(*                                                                            *)
(* For lpc_predict with the SAME weights, when the LOWER-budget run leaves   *)
(* budget non-zero (i.e., did not saturate), the result value is the same as *)
(* the HIGHER-budget run and budget chains are ordered.                       *)
(******************************************************************************)
(* H1: add_fin_b_spur is deterministic (in result) under leF when lower
   budget output is non-zero.  Budget chain is ordered. *)
Lemma add_fin_b_spur_det_leF :
  forall n m b1 b2 r1 b1_out h1 r2 b2_out h2,
    add_fin_b_spur n m b1 = (r1, b1_out, h1) ->
    add_fin_b_spur n m b2 = (r2, b2_out, h2) ->
    leF b1 b2 ->
    b1_out <> fz ->
    r1 = r2 /\ leF b1_out b2_out.
Proof.
  intros n m. induction m as [| m' IH];
    intros b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne.
  - (* m = fz : returns (n, b, fz) *)
    simpl in H1, H2. inversion H1. inversion H2. subst.
    split; [reflexivity | exact Hle].
  - destruct b1 as [| b1'].
    + (* b1 = fz : H1 gives b1_out = fz, contradicting Hne *)
      simpl in H1. inversion H1. subst. exfalso. apply Hne. reflexivity.
    + destruct b2 as [| b2'].
      * (* b2 = fz, b1 = fs _ : leF (fs _) fz impossible *)
        inversion Hle.
      * simpl in H1, H2.
        destruct (add_fin_b_spur n m' b1') as [[r1' b1''] h1'] eqn:Erec1.
        destruct (add_fin_b_spur n m' b2') as [[r2' b2''] h2'] eqn:Erec2.
        assert (Hle' : leF b1' b2') by (inversion Hle; assumption).
        injection H1 as E1r E1b E1h.
        injection H2 as E2r E2b E2h.
        subst r1 b1_out h1 r2 b2_out h2.
        assert (Hrec : r1' = r2' /\ leF b1'' b2'')
          by (apply (IH b1' b2' r1' b1'' h1' r2' b2'' h2' Erec1 Erec2 Hle' Hne)).
        destruct Hrec as [Heq Hlf].
        split; [f_equal; exact Heq | exact Hlf].
Qed.
(* H2: accumulate_for_lpc is deterministic under leF when lower budget
   output is non-zero, with ordered budget chain. *)
Lemma accumulate_for_lpc_det_leF :
  forall inputs ws acc b1 b2 r1 b1_out h1 r2 b2_out h2,
    accumulate_for_lpc inputs ws acc b1 = (r1, b1_out, h1) ->
    accumulate_for_lpc inputs ws acc b2 = (r2, b2_out, h2) ->
    leF b1 b2 ->
    b1_out <> fz ->
    r1 = r2 /\ leF b1_out b2_out.
Proof.
  induction inputs as [| i ins IH];
    intros ws acc b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne.
  - (* inputs = [] : returns (acc, b, fz) *)
    simpl in H1, H2. inversion H1. inversion H2. subst.
    split; [reflexivity | exact Hle].
  - destruct ws as [| w ws'].
    + (* ws = [] : returns (acc, b, fz) regardless of i *)
      destruct i; simpl in H1, H2; inversion H1; inversion H2; subst;
        (split; [reflexivity | exact Hle]).
    + destruct i; simpl in H1, H2.
      * (* BTrue :: ins — add + recursion *)
        destruct (add_fin_b_spur acc w b1) as [[acc1' b1a] h1a] eqn:Eadd1.
        destruct (add_fin_b_spur acc w b2) as [[acc2' b2a] h2a] eqn:Eadd2.
        destruct (accumulate_for_lpc ins ws' acc1' b1a) as [[r1' b1''] h1''] eqn:Erec1.
        destruct (accumulate_for_lpc ins ws' acc2' b2a) as [[r2' b2''] h2''] eqn:Erec2.
        injection H1 as E1r E1b E1h.
        injection H2 as E2r E2b E2h.
        subst r1 b1_out h1 r2 b2_out h2.
        assert (Hb1a_ne : b1a <> fz).
        { intro Heq. subst b1a.
          assert (Hle0 : leF b1'' fz).
          { apply (accumulate_for_lpc_budget_le ins ws' acc1' fz r1' b1'' h1'').
            exact Erec1. }
          inversion Hle0; subst. apply Hne. reflexivity. }
        assert (Hadd : acc1' = acc2' /\ leF b1a b2a).
        { apply (add_fin_b_spur_det_leF acc w b1 b2 acc1' b1a h1a acc2' b2a h2a
                   Eadd1 Eadd2 Hle Hb1a_ne). }
        destruct Hadd as [Hacc_eq Hb_le].
        subst acc2'.
        assert (Hrec : r1' = r2' /\ leF b1'' b2'').
        { apply (IH ws' acc1' b1a b2a r1' b1'' h1'' r2' b2'' h2'' Erec1 Erec2 Hb_le Hne). }
        destruct Hrec as [Hr_eq Hb_le'].
        split; [f_equal; exact Hr_eq | exact Hb_le'].
      * (* BFalse :: ins — free recursion *)
        apply (IH ws' acc b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne).
      * (* BUnknown :: ins — free recursion *)
        apply (IH ws' acc b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne).
Qed.
(* H3: accumulate_against_lpc is deterministic under leF when lower budget
   output is non-zero, with ordered budget chain. *)
Lemma accumulate_against_lpc_det_leF :
  forall inputs ws acc b1 b2 r1 b1_out h1 r2 b2_out h2,
    accumulate_against_lpc inputs ws acc b1 = (r1, b1_out, h1) ->
    accumulate_against_lpc inputs ws acc b2 = (r2, b2_out, h2) ->
    leF b1 b2 ->
    b1_out <> fz ->
    r1 = r2 /\ leF b1_out b2_out.
Proof.
  induction inputs as [| i ins IH];
    intros ws acc b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne.
  - simpl in H1, H2. inversion H1. inversion H2. subst.
    split; [reflexivity | exact Hle].
  - destruct ws as [| w ws'].
    + destruct i; simpl in H1, H2; inversion H1; inversion H2; subst;
        (split; [reflexivity | exact Hle]).
    + destruct i; simpl in H1, H2.
      * (* BTrue :: ins — free recursion *)
        apply (IH ws' acc b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne).
      * (* BFalse :: ins — add + recursion *)
        destruct (add_fin_b_spur acc w b1) as [[acc1' b1a] h1a] eqn:Eadd1.
        destruct (add_fin_b_spur acc w b2) as [[acc2' b2a] h2a] eqn:Eadd2.
        destruct (accumulate_against_lpc ins ws' acc1' b1a)
          as [[r1' b1''] h1''] eqn:Erec1.
        destruct (accumulate_against_lpc ins ws' acc2' b2a)
          as [[r2' b2''] h2''] eqn:Erec2.
        injection H1 as E1r E1b E1h.
        injection H2 as E2r E2b E2h.
        subst r1 b1_out h1 r2 b2_out h2.
        assert (Hb1a_ne : b1a <> fz).
        { intro Heq. subst b1a.
          assert (Hle0 : leF b1'' fz).
          { apply (accumulate_against_lpc_budget_le ins ws' acc1' fz r1' b1'' h1'').
            exact Erec1. }
          inversion Hle0; subst. apply Hne. reflexivity. }
        assert (Hadd : acc1' = acc2' /\ leF b1a b2a).
        { apply (add_fin_b_spur_det_leF acc w b1 b2 acc1' b1a h1a acc2' b2a h2a
                   Eadd1 Eadd2 Hle Hb1a_ne). }
        destruct Hadd as [Hacc_eq Hb_le]. subst acc2'.
        assert (Hrec : r1' = r2' /\ leF b1'' b2'').
        { apply (IH ws' acc1' b1a b2a r1' b1'' h1'' r2' b2'' h2''
                   Erec1 Erec2 Hb_le Hne). }
        destruct Hrec as [Hr_eq Hb_le'].
        split; [f_equal; exact Hr_eq | exact Hb_le'].
      * (* BUnknown :: ins — free recursion *)
        apply (IH ws' acc b1 b2 r1 b1_out h1 r2 b2_out h2 H1 H2 Hle Hne).
Qed.
(* H4: when le_fin_b3 n m b produces BTrue at two budgets b1 ≤ b2, the output
   budgets satisfy b1_out ≤ b2_out (same cost is burned on the BTrue path). *)
Lemma le_fin_b3_btrue_leF_out :
  forall n m b1 b2 b1_out h1 b2_out h2,
    le_fin_b3 n m b1 = (BTrue, b1_out, h1) ->
    le_fin_b3 n m b2 = (BTrue, b2_out, h2) ->
    leF b1 b2 ->
    leF b1_out b2_out.
Proof.
  intros n. induction n as [| n' IH];
    intros m b1 b2 b1_out h1 b2_out h2 H1 H2 Hle.
  - (* n = fz : le_fin_b3 fz m b = if b=fz then BUnknown else BTrue at (pred b). *)
    destruct b1 as [| b1'].
    + (* b1 = fz : result BUnknown, contradicts BTrue *)
      simpl in H1. inversion H1.
    + destruct b2 as [| b2'].
      * inversion Hle.
      * simpl in H1, H2. inversion H1. inversion H2. subst.
        inversion Hle. assumption.
  - (* n = fs n' *)
    destruct b1 as [| b1'].
    + simpl in H1. inversion H1.
    + destruct b2 as [| b2'].
      * inversion Hle.
      * destruct m as [| m'].
        { (* m = fz : BFalse in both, contradicts BTrue *)
          simpl in H1. inversion H1. }
        simpl in H1, H2.
        destruct (le_fin_b3 n' m' b1') as [[r1' b1''] h1'] eqn:Erec1.
        destruct (le_fin_b3 n' m' b2') as [[r2' b2''] h2'] eqn:Erec2.
        injection H1 as E1r E1b E1h.
        injection H2 as E2r E2b E2h.
        subst r1' b1_out h1 r2' b2_out h2.
        assert (Hle' : leF b1' b2') by (inversion Hle; assumption).
        apply (IH m' b1' b2' b1'' h1' b2'' h2' Erec1 Erec2 Hle').
Qed.
(* Small helper: le_fin_b3 at budget fz is always (BUnknown, fz, fz).
   The recursive Fixpoint struct argument prevents direct reflexivity — need
   to destruct n (and m) to force reduction. *)
Lemma le_fin_b3_at_fz :
  forall n m, le_fin_b3 n m fz = (BUnknown, fz, fz).
Proof. intros n m. destruct n, m; reflexivity. Qed.
(******************************************************************************)
(* PART 5C: LEMMA B — FREEZE IS ABSORBING                                    *)
(*                                                                            *)
(* Main theorem: if cell is in Freeze for inputs, then learn_step cell inputs *)
(* truth is also in Freeze for inputs.  Freeze persists across one learning   *)
(* step with the SAME inputs.                                                 *)
(*                                                                            *)
(* Proof strategy: if the new cell's prediction were BTrue or BFalse, then   *)
(* by determinism (H1–H3), the accumulated values A_f, A_a are the same as   *)
(* in the original cell, and the remaining budget chain is weakly monotone.  *)
(* Then by le_fin_b3_budget_true / _budget_false (from                        *)
(* void_probability_geometry) and H4, the old cell would also return BTrue   *)
(* or BFalse — contradicting Hfreeze.                                         *)
(******************************************************************************)
Theorem freeze_is_absorbing :
  forall cell inputs truth,
    InFreeze cell inputs ->
    InFreeze (learn_step cell inputs truth) inputs.
Proof.
  intros cell inputs truth Hfreeze.
  unfold InFreeze in *.
  pose proof (learn_step_freeze_preserves_shape cell inputs truth Hfreeze) as Hshape.
  destruct Hshape as [Hw_for [Hw_against [Hlr Hmax]]].
  pose proof (learn_step_freeze_budget_le cell inputs truth Hfreeze) as Hble.
  set (cell' := learn_step cell inputs truth) in *.
  (* Reduce to showing the predicted value is BUnknown *)
  unfold predict_value.
  destruct (lpc_predict cell' inputs) as [[p_new b_new] h_new] eqn:E_new.
  simpl.
  destruct p_new as [ | | ].
  - (* Case new = BTrue : derive contradiction with old = BUnknown *)
    exfalso.
    (* Unfold both old and new lpc_predict *)
    unfold predict_value in Hfreeze.
    unfold lpc_predict in Hfreeze, E_new.
    rewrite Hw_for, Hw_against in E_new.
    destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell))
      as [[A_f B_1] h1] eqn:E_af_old.
    destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz B_1)
      as [[A_a B_2] h2] eqn:E_aa_old.
    destruct (le_fin_b3 A_a A_f B_2) as [[r3 B_3] h3] eqn:E_le1_old.
    destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell'))
      as [[A_f' B_1'] h1'] eqn:E_af_new.
    destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz B_1')
      as [[A_a' B_2'] h2'] eqn:E_aa_new.
    destruct (le_fin_b3 A_a' A_f' B_2') as [[r3' B_3'] h3'] eqn:E_le1_new.
    (* New must pass BTrue path : r3' = BTrue and second le_fin_b3 = BFalse *)
    destruct r3' as [| |].
    + (* r3' = BTrue — proceed *)
      destruct (le_fin_b3 A_f' A_a' B_3') as [[r4' B_4'] h4'] eqn:E_le2_new.
      destruct r4' as [| |].
      * (* r4' = BTrue — gives BUnknown for new; contradicts BTrue *)
        inversion E_new.
      * (* r4' = BFalse — gives BTrue for new (this is the actual case) *)
        (* Apply determinism to propagate to old *)
        (* Step 1: B_2' <> fz (since le_fin_b3 at B_2' produced BTrue) *)
        assert (HB2'ne : B_2' <> fz).
        { intro Heq. subst B_2'. rewrite le_fin_b3_at_fz in E_le1_new.
          discriminate E_le1_new. }
        (* Step 2: B_1' <> fz (since accumulate_against_budget_le B_2' <= B_1') *)
        assert (HB1'ne : B_1' <> fz).
        { intro Heq. subst B_1'.
          pose proof (accumulate_against_lpc_budget_le inputs (lpc_weights_against cell)
                        fz fz A_a' B_2' h2' E_aa_new) as Hlefz.
          inversion Hlefz; subst. apply HB2'ne. reflexivity. }
        (* Step 3: accumulate_for determinism *)
        pose proof (accumulate_for_lpc_det_leF inputs (lpc_weights_for cell) fz
                      (lpc_budget cell') (lpc_budget cell)
                      A_f' B_1' h1' A_f B_1 h1
                      E_af_new E_af_old Hble HB1'ne) as [HfEq HB1le].
        subst A_f.
        (* Step 4: accumulate_against determinism *)
        pose proof (accumulate_against_lpc_det_leF inputs (lpc_weights_against cell) fz
                      B_1' B_1
                      A_a' B_2' h2' A_a B_2 h2
                      E_aa_new E_aa_old HB1le HB2'ne) as [HaEq HB2le].
        subst A_a.
        (* Step 5: old's first le_fin_b3 at B_2 must be BTrue (from new = BTrue at B_2') *)
        assert (Hpre1 : bool3_of (le_fin_b3 A_a' A_f' B_2') = BTrue).
        { unfold bool3_of. rewrite E_le1_new. reflexivity. }
        assert (HB3true_old : bool3_of (le_fin_b3 A_a' A_f' B_2) = BTrue).
        { apply (le_fin_b3_budget_true A_a' A_f' B_2' Hpre1 B_2 HB2le). }
        unfold bool3_of in HB3true_old. rewrite E_le1_old in HB3true_old.
        simpl in HB3true_old. subst r3.
        (* Now old proceeds to second le_fin_b3 at B_3 *)
        (* Step 6: H4 — leF B_3' B_3 *)
        pose proof (le_fin_b3_btrue_leF_out A_a' A_f' B_2' B_2 B_3' h3' B_3 h3
                     E_le1_new E_le1_old HB2le) as HB3le.
        (* Step 7: new's second le_fin_b3 is BFalse → old's second is BFalse *)
        assert (Hpre2 : bool3_of (le_fin_b3 A_f' A_a' B_3') = BFalse).
        { unfold bool3_of. rewrite E_le2_new. reflexivity. }
        assert (HB4false_old : bool3_of (le_fin_b3 A_f' A_a' B_3) = BFalse).
        { apply (le_fin_b3_budget_false A_f' A_a' B_3' Hpre2 B_3 HB3le). }
        destruct (le_fin_b3 A_f' A_a' B_3) as [[r4 B_4] h4] eqn:E_le2_old.
        unfold bool3_of in HB4false_old. simpl in HB4false_old. subst r4.
        (* Old's lpc_predict thus returns (BFalse, _, _) — but Hfreeze says BUnknown *)
        simpl in Hfreeze. inversion Hfreeze.
      * (* r4' = BUnknown — gives BUnknown for new; contradicts BTrue *)
        inversion E_new.
    + (* r3' = BFalse — gives BFalse for new; contradicts BTrue *)
      inversion E_new.
    + (* r3' = BUnknown — gives BUnknown for new; contradicts BTrue *)
      inversion E_new.
  - (* Case new = BFalse : derive contradiction with old = BUnknown *)
    exfalso.
    unfold predict_value in Hfreeze.
    unfold lpc_predict in Hfreeze, E_new.
    rewrite Hw_for, Hw_against in E_new.
    destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell))
      as [[A_f B_1] h1] eqn:E_af_old.
    destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz B_1)
      as [[A_a B_2] h2] eqn:E_aa_old.
    destruct (le_fin_b3 A_a A_f B_2) as [[r3 B_3] h3] eqn:E_le1_old.
    destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell'))
      as [[A_f' B_1'] h1'] eqn:E_af_new.
    destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz B_1')
      as [[A_a' B_2'] h2'] eqn:E_aa_new.
    destruct (le_fin_b3 A_a' A_f' B_2') as [[r3' B_3'] h3'] eqn:E_le1_new.
    destruct r3' as [| |].
    + (* r3' = BTrue *)
      destruct (le_fin_b3 A_f' A_a' B_3') as [[r4' B_4'] h4'] eqn:E_le2_new.
      destruct r4'; inversion E_new.
    + (* r3' = BFalse : this is the actual case *)
      (* Step 1: B_2' <> fz *)
      assert (HB2'ne : B_2' <> fz).
      { intro Heq. subst B_2'. rewrite le_fin_b3_at_fz in E_le1_new.
        discriminate E_le1_new. }
      assert (HB1'ne : B_1' <> fz).
      { intro Heq. subst B_1'.
        pose proof (accumulate_against_lpc_budget_le inputs (lpc_weights_against cell)
                      fz fz A_a' B_2' h2' E_aa_new) as Hlefz.
        inversion Hlefz; subst. apply HB2'ne. reflexivity. }
      pose proof (accumulate_for_lpc_det_leF inputs (lpc_weights_for cell) fz
                    (lpc_budget cell') (lpc_budget cell)
                    A_f' B_1' h1' A_f B_1 h1
                    E_af_new E_af_old Hble HB1'ne) as [HfEq HB1le].
      subst A_f.
      pose proof (accumulate_against_lpc_det_leF inputs (lpc_weights_against cell) fz
                    B_1' B_1
                    A_a' B_2' h2' A_a B_2 h2
                    E_aa_new E_aa_old HB1le HB2'ne) as [HaEq HB2le].
      subst A_a.
      assert (Hpre1 : bool3_of (le_fin_b3 A_a' A_f' B_2') = BFalse).
      { unfold bool3_of. rewrite E_le1_new. reflexivity. }
      assert (HB3false_old : bool3_of (le_fin_b3 A_a' A_f' B_2) = BFalse).
      { apply (le_fin_b3_budget_false A_a' A_f' B_2' Hpre1 B_2 HB2le). }
      unfold bool3_of in HB3false_old. rewrite E_le1_old in HB3false_old.
      simpl in HB3false_old. subst r3.
      simpl in Hfreeze. inversion Hfreeze.
    + (* r3' = BUnknown *)
      inversion E_new.
  - (* Case new = BUnknown : done *)
    reflexivity.
Qed.

(******************************************************************************)
(* PART 6: STRICT BUDGET DECREMENT OF lpc_predict                             *)
(*                                                                            *)
(* lpc_predict_budget_le (4.5) said: output budget ≤ input budget.           *)
(* That is not enough to drive termination.  We need STRICT decrement:        *)
(* if the input budget is fs b', then the output budget is ≤ b' (i.e.        *)
(* the computation spent at least one tick).                                  *)
(*                                                                            *)
(* Why it's true: lpc_predict always performs at least one le_fin_b3 call.   *)
(* le_fin_b3 at budget fs b' always produces output budget ≤ b' — regardless *)
(* of whether the match hits the fz/_, fs/fz, or recursive branch.           *)
(*                                                                            *)
(* Road-map:                                                                   *)
(*   6.1  leF_fz_inv                 : leF n fz -> n = fz                     *)
(*   6.2  leF_fs_inv                 : leF (fs n)(fs m) -> leF n m            *)
(*   6.3  le_fin_b3_strict           : le_fin_b3 _ _ (fs b') has out ≤ b'     *)
(*   6.4  lpc_predict_strictly_decreases : the main lemma                    *)
(******************************************************************************)

(* 6.1 -------------------------------------------------------------------- *)
Lemma leF_fz_inv : forall n, leF n fz -> n = fz.
Proof.
  intros n H. inversion H. reflexivity.
Qed.

(* 6.2 -------------------------------------------------------------------- *)
Lemma leF_fs_inv : forall n m, leF (fs n) (fs m) -> leF n m.
Proof.
  intros n m H. inversion H. assumption.
Qed.

(* 6.3 -------------------------------------------------------------------- *)
Lemma le_fin_b3_strict : forall n m b' r b_out h,
  le_fin_b3 n m (fs b') = (r, b_out, h) ->
  leF b_out b'.
Proof.
  intros n. induction n as [| n' IH]; intros m b' r b_out h Hle.
  - (* n = fz *)
    simpl in Hle. inversion Hle. subst. apply leF_refl.
  - (* n = fs n' *)
    destruct m as [| m'].
    + simpl in Hle. inversion Hle. subst. apply leF_refl.
    + simpl in Hle.
      destruct (le_fin_b3 n' m' b') as [[r' b''] h''] eqn:Erec.
      inversion Hle; subst.
      apply (le_fin_b3_budget_le n' m' b' r b_out h''). exact Erec.
Qed.

(* 6.4 -------------------------------------------------------------------- *)
Lemma lpc_predict_strictly_decreases :
  forall cell inputs b' pred b_out h,
    lpc_budget cell = fs b' ->
    lpc_predict cell inputs = (pred, b_out, h) ->
    leF b_out b'.
Proof.
  intros cell inputs b' pred b_out h Hbud Hpred.
  unfold lpc_predict in Hpred.
  destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz (lpc_budget cell))
    as [[acc_f b1] h1] eqn:Eacc_f.
  destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz b1)
    as [[acc_a b2] h2] eqn:Eacc_a.
  assert (Hb1 : leF b1 (lpc_budget cell)).
  { apply (accumulate_for_lpc_budget_le inputs (lpc_weights_for cell) fz
            (lpc_budget cell) acc_f b1 h1). exact Eacc_f. }
  assert (Hb2b1 : leF b2 b1).
  { apply (accumulate_against_lpc_budget_le inputs (lpc_weights_against cell) fz
            b1 acc_a b2 h2). exact Eacc_a. }
  rewrite Hbud in Hb1.
  assert (Hb2 : leF b2 (fs b')) by (apply leF_trans with b1; assumption).
  destruct (le_fin_b3 acc_a acc_f b2) as [[r3 b3] h3] eqn:Ele1.
  assert (Hb3 : leF b3 b').
  { destruct b2 as [| b2'].
    - (* b2 = fz : le_fin_b3_budget_le gives b3 ≤ fz, hence b3 = fz ≤ b' *)
      assert (Hb3fz : leF b3 fz)
        by (apply (le_fin_b3_budget_le acc_a acc_f fz r3 b3 h3); exact Ele1).
      assert (b3 = fz) by (apply leF_fz_inv; exact Hb3fz).
      subst b3. apply leF_z.
    - (* b2 = fs b2' : use le_fin_b3_strict then transit via b2' ≤ b' *)
      assert (Hb2' : leF b2' b') by (apply leF_fs_inv; exact Hb2).
      assert (H3b2' : leF b3 b2')
        by (apply (le_fin_b3_strict acc_a acc_f b2' r3 b3 h3); exact Ele1).
      apply leF_trans with b2'; assumption. }
  destruct r3.
  - (* BTrue : run second le_fin_b3 at budget b3 *)
    destruct (le_fin_b3 acc_f acc_a b3) as [[r4 b4] h4] eqn:Ele2.
    assert (Hb4 : leF b4 b3).
    { apply (le_fin_b3_budget_le acc_f acc_a b3 r4 b4 h4). exact Ele2. }
    destruct r4; inversion Hpred; subst; apply leF_trans with b3; assumption.
  - (* BFalse *) inversion Hpred. subst. exact Hb3.
  - (* BUnknown *) inversion Hpred. subst. exact Hb3.
Qed.

(******************************************************************************)
(* PART 7: learn_step STRICTLY DECREASES BUDGET                               *)
(*                                                                            *)
(* From Part 6 we have: lpc_predict at fs b' yields b1 ≤ b'.                  *)
(* compute_surprise and update_weights are MONOTONE (not strict) — they do    *)
(* not inflate budget.  Combining gives: learn_step at fs b' yields final     *)
(* budget ≤ b'.                                                               *)
(*                                                                            *)
(* Helpers:                                                                   *)
(*   7.1  sub_saturate_b_spur_budget_le                                      *)
(*   7.2  sat_add_budget_le                                                   *)
(*   7.3  sat_sub_budget_le  (thin wrapper over 7.1)                         *)
(*   7.4  update_weights_rec_budget_le                                        *)
(*   7.5  update_weights_budget_le                                            *)
(*   7.6  compute_surprise_budget_le                                          *)
(*   7.7  learn_step_strict_decrement  (the goal)                            *)
(******************************************************************************)

(* 7.1 -------------------------------------------------------------------- *)
Lemma sub_saturate_b_spur_budget_le : forall n m b r b_out h,
  sub_saturate_b_spur n m b = (r, b_out, h) ->
  leF b_out b.
Proof.
  intros n. induction n as [| n' IH]; intros m b r b_out h Hsub.
  - (* n = fz *)
    destruct b as [| b'].
    + simpl in Hsub. inversion Hsub. subst. apply leF_refl.
    + destruct m as [| m'].
      * simpl in Hsub. inversion Hsub. subst. apply leF_step.
      * simpl in Hsub. inversion Hsub. subst. apply leF_step.
  - (* n = fs n' *)
    destruct b as [| b'].
    + simpl in Hsub. inversion Hsub. subst. apply leF_refl.
    + destruct m as [| m'].
      * simpl in Hsub. inversion Hsub. subst. apply leF_step.
      * simpl in Hsub.
        destruct (sub_saturate_b_spur n' m' b') as [[r' b''] h''] eqn:Erec.
        specialize (IH m' b' r' b'' h'' Erec).
        inversion Hsub; subst.
        apply leF_trans with b'. exact IH. apply leF_step.
Qed.

(* 7.2 -------------------------------------------------------------------- *)
Lemma sat_add_budget_le : forall w bonus max b r b_out h,
  sat_add w bonus max b = (r, b_out, h) ->
  leF b_out b.
Proof.
  intros w bonus max b r b_out h Hsat. unfold sat_add in Hsat.
  destruct (add_fin_b_spur w bonus b) as [[sum b'] h1] eqn:Eadd.
  assert (Hb' : leF b' b).
  { apply (add_fin_b_spur_budget_le w bonus b sum b' h1). exact Eadd. }
  destruct (le_fin_b3 sum max b') as [[r' b''] h2] eqn:Ele.
  assert (Hb'' : leF b'' b').
  { apply (le_fin_b3_budget_le sum max b' r' b'' h2). exact Ele. }
  destruct r'; inversion Hsat; subst; apply leF_trans with b'; assumption.
Qed.

(* 7.3 -------------------------------------------------------------------- *)
Lemma sat_sub_budget_le : forall w penalty b r b_out h,
  sat_sub w penalty b = (r, b_out, h) ->
  leF b_out b.
Proof.
  unfold sat_sub. intros w penalty b r b_out h Hsub.
  apply (sub_saturate_b_spur_budget_le w penalty b r b_out h). exact Hsub.
Qed.

(* 7.4 -------------------------------------------------------------------- *)
Lemma update_weights_rec_budget_le :
  forall inputs ws direction lr_num max b ws_out b_out h,
    update_weights_rec inputs ws direction lr_num max b = (ws_out, b_out, h) ->
    leF b_out b.
Proof.
  induction inputs as [| i ins IH];
  intros ws direction lr_num max b ws_out b_out h Hupd.
  - (* [] *)
    simpl in Hupd. inversion Hupd. subst. apply leF_refl.
  - destruct i.
    + (* BTrue *)
      destruct ws as [| w ws'].
      * (* ws = [] *)
        simpl in Hupd. inversion Hupd. subst. apply leF_refl.
      * (* BTrue : adjust this weight *)
        simpl in Hupd.
        destruct direction eqn:Edir.
        -- (* strengthen *)
           destruct (sat_add w lr_num max b) as [[w' b1] h1] eqn:Esat.
           assert (Hb1 : leF b1 b)
             by (apply (sat_add_budget_le w lr_num max b w' b1 h1); exact Esat).
           destruct (update_weights_rec ins ws' true lr_num max b1)
             as [[rest b2] h2] eqn:Erec.
           specialize (IH ws' true lr_num max b1 rest b2 h2 Erec).
           inversion Hupd; subst.
           apply leF_trans with b1; assumption.
        -- (* weaken *)
           destruct (sat_sub w lr_num b) as [[w' b1] h1] eqn:Esat.
           assert (Hb1 : leF b1 b)
             by (apply (sat_sub_budget_le w lr_num b w' b1 h1); exact Esat).
           destruct (update_weights_rec ins ws' false lr_num max b1)
             as [[rest b2] h2] eqn:Erec.
           specialize (IH ws' false lr_num max b1 rest b2 h2 Erec).
           inversion Hupd; subst.
           apply leF_trans with b1; assumption.
    + (* BFalse : skip, free *)
      destruct ws as [| w ws'].
      * (* ws = [] *)
        simpl in Hupd. inversion Hupd. subst. apply leF_refl.
      * (* ws = w :: ws' *)
        simpl in Hupd.
        destruct (update_weights_rec ins ws' direction lr_num max b)
          as [[rest b1] h1] eqn:Erec.
        specialize (IH ws' direction lr_num max b rest b1 h1 Erec).
        inversion Hupd; subst. exact IH.
    + (* BUnknown : skip, free *)
      destruct ws as [| w ws'].
      * (* ws = [] *)
        simpl in Hupd. inversion Hupd. subst. apply leF_refl.
      * (* ws = w :: ws' *)
        simpl in Hupd.
        destruct (update_weights_rec ins ws' direction lr_num max b)
          as [[rest b1] h1] eqn:Erec.
        specialize (IH ws' direction lr_num max b rest b1 h1 Erec).
        inversion Hupd; subst. exact IH.
Qed.

(* 7.5 -------------------------------------------------------------------- *)
Lemma update_weights_budget_le :
  forall cell inputs surp,
    leF (lpc_budget (update_weights cell inputs surp)) (lpc_budget cell).
Proof.
  intros cell inputs surp. unfold update_weights. destruct surp.
  - (* NoSurprise : cell unchanged *)
    apply leF_refl.
  - (* SurpriseFor *)
    destruct (update_weights_rec inputs (lpc_weights_for cell) true
                (fst (lpc_learning_rate cell)) (lpc_weight_max cell)
                (lpc_budget cell))
      as [[new_for b1] h1] eqn:E1.
    destruct (update_weights_rec inputs (lpc_weights_against cell) false
                (fst (lpc_learning_rate cell)) (lpc_weight_max cell) b1)
      as [[new_against b2] h2] eqn:E2.
    simpl.
    assert (H1 : leF b1 (lpc_budget cell))
      by (apply (update_weights_rec_budget_le inputs (lpc_weights_for cell)
                 true (fst (lpc_learning_rate cell)) (lpc_weight_max cell)
                 (lpc_budget cell) new_for b1 h1); exact E1).
    assert (H2 : leF b2 b1)
      by (apply (update_weights_rec_budget_le inputs (lpc_weights_against cell)
                 false (fst (lpc_learning_rate cell)) (lpc_weight_max cell)
                 b1 new_against b2 h2); exact E2).
    apply leF_trans with b1; assumption.
  - (* SurpriseAgainst : symmetric *)
    destruct (update_weights_rec inputs (lpc_weights_for cell) false
                (fst (lpc_learning_rate cell)) (lpc_weight_max cell)
                (lpc_budget cell))
      as [[new_for b1] h1] eqn:E1.
    destruct (update_weights_rec inputs (lpc_weights_against cell) true
                (fst (lpc_learning_rate cell)) (lpc_weight_max cell) b1)
      as [[new_against b2] h2] eqn:E2.
    simpl.
    assert (H1 : leF b1 (lpc_budget cell))
      by (apply (update_weights_rec_budget_le inputs (lpc_weights_for cell)
                 false (fst (lpc_learning_rate cell)) (lpc_weight_max cell)
                 (lpc_budget cell) new_for b1 h1); exact E1).
    assert (H2 : leF b2 b1)
      by (apply (update_weights_rec_budget_le inputs (lpc_weights_against cell)
                 true (fst (lpc_learning_rate cell)) (lpc_weight_max cell)
                 b1 new_against b2 h2); exact E2).
    apply leF_trans with b1; assumption.
  - (* SurpriseUnknown : cell unchanged *)
    apply leF_refl.
Qed.

(* 7.6 -------------------------------------------------------------------- *)
Lemma compute_surprise_budget_le : forall pred truth b r b_out h,
  compute_surprise pred truth b = (r, b_out, h) ->
  leF b_out b.
Proof.
  intros pred truth b r b_out h Hcs.
  destruct b as [| b']; simpl in Hcs.
  - inversion Hcs; subst. apply leF_refl.
  - destruct pred, truth; inversion Hcs; subst; apply leF_step.
Qed.

(* 7.7 -------------------------------------------------------------------- *)
Theorem learn_step_strict_decrement :
  forall cell inputs truth b',
    lpc_budget cell = fs b' ->
    leF (lpc_budget (learn_step cell inputs truth)) b'.
Proof.
  intros cell inputs truth b' Hbud.
  unfold learn_step.
  destruct (lpc_predict cell inputs) as [[pred b1] h1] eqn:Epred.
  assert (Hb1 : leF b1 b')
    by (apply (lpc_predict_strictly_decreases cell inputs b' pred b1 h1);
        assumption).
  destruct (compute_surprise pred truth b1) as [[surp b2] h2] eqn:Ecs.
  assert (Hb2 : leF b2 b1)
    by (apply (compute_surprise_budget_le pred truth b1 surp b2 h2); exact Ecs).
  (* After let-binding cell', the term reduces to update_weights applied
     to an explicit mkLPC with budget b2.                                   *)
  match goal with
  | [ |- leF (lpc_budget (update_weights ?C _ _)) _ ] =>
      assert (Hupd : leF (lpc_budget (update_weights C inputs surp))
                          (lpc_budget C))
        by (apply update_weights_budget_le)
  end.
  simpl in Hupd.
  apply leF_trans with b2. exact Hupd.
  apply leF_trans with b1; assumption.
Qed.

(******************************************************************************)
(* PART 8: ZERO BUDGET ⇒ FREEZE                                               *)
(*                                                                            *)
(* The other end of the budget axis: once budget hits fz the cell is frozen.  *)
(* This is the invariant driving the descent: strict decrement (Part 7)       *)
(* eventually drains the budget to fz, and at fz we land in Freeze.           *)
(******************************************************************************)

Theorem zero_budget_in_freeze : forall cell inputs,
  lpc_budget cell = fz -> InFreeze cell inputs.
Proof.
  intros cell inputs Hdead.
  unfold InFreeze, predict_value.
  destruct (lpc_predict cell inputs) as [[p b] h] eqn:Epred.
  (* Reproduce the b_pred = fz argument from dead_cell_no_learning, but
     here we additionally extract the prediction value and show it is
     BUnknown, not merely that the budget survived at fz.                  *)
  unfold lpc_predict in Epred.
  rewrite Hdead in Epred.
  destruct (accumulate_for_lpc inputs (lpc_weights_for cell) fz fz)
    as [[acc_f b1] h1] eqn:E1.
  pose proof (accumulate_for_lpc_zero_budget _ _ _ _ _ _ E1) as Hb1.
  subst b1.
  destruct (accumulate_against_lpc inputs (lpc_weights_against cell) fz fz)
    as [[acc_a b2] h2] eqn:E2.
  pose proof (accumulate_against_lpc_zero_budget _ _ _ _ _ _ E2) as Hb2.
  subst b2.
  rewrite le_fin_b3_zero_budget in Epred.
  simpl in Epred. inversion Epred. reflexivity.
Qed.

(******************************************************************************)
(* PART 9: ITERATED LEARNING                                                  *)
(*                                                                            *)
(* iter_learn : apply learn_step n times, consuming truths one per step.      *)
(*                                                                            *)
(* CRITICAL: the counter n is Fin, NOT nat.  VT is strictly finitist.         *)
(* A nat counter would smuggle in the Peano Platonism VT rejects.            *)
(*                                                                            *)
(* If the truths list runs out before the counter, we stop (return the        *)
(* current cell).  enough_truths captures the side condition: there are at    *)
(* least n truths available, which the termination theorems need.            *)
(******************************************************************************)

Fixpoint iter_learn (n : Fin) (cell : LearningPredCell)
                    (inputs : list Bool3) (truths : list Bool3)
  : LearningPredCell :=
  match n with
  | fz => cell
  | fs n' =>
      match truths with
      | [] => cell
      | t :: ts => iter_learn n' (learn_step cell inputs t) inputs ts
      end
  end.

(* enough_truths n truths : truths has at least n elements.                    *)
Fixpoint enough_truths (n : Fin) (truths : list Bool3) : Prop :=
  match n with
  | fz => True
  | fs n' =>
      match truths with
      | [] => False
      | _ :: ts => enough_truths n' ts
      end
  end.

(******************************************************************************)
(* PART 10: MONOTONICITY OF learn_step AND TERMINATION                        *)
(*                                                                            *)
(* learn_step never increases the budget (monotonicity, no hypothesis).       *)
(* Combined with Part 7 (strict decrement when budget is fs b') and Part 8    *)
(* (zero budget ⇒ Freeze), this drives the descent: after at most            *)
(* lpc_budget cell iterations the cell is frozen.                             *)
(******************************************************************************)

(* 10.1  learn_step is monotone in budget (no side conditions).              *)
Lemma learn_step_monotone :
  forall cell inputs truth,
    leF (lpc_budget (learn_step cell inputs truth)) (lpc_budget cell).
Proof.
  intros cell inputs truth. unfold learn_step.
  destruct (lpc_predict cell inputs) as [[pred b1] h1] eqn:Epred.
  assert (Hb1 : leF b1 (lpc_budget cell))
    by (apply (lpc_predict_budget_le cell inputs pred b1 h1); exact Epred).
  destruct (compute_surprise pred truth b1) as [[surp b2] h2] eqn:Ecs.
  assert (Hb2 : leF b2 b1)
    by (apply (compute_surprise_budget_le pred truth b1 surp b2 h2); exact Ecs).
  match goal with
  | [ |- leF (lpc_budget (update_weights ?C _ _)) _ ] =>
      assert (Hupd : leF (lpc_budget (update_weights C inputs surp))
                         (lpc_budget C))
        by apply update_weights_budget_le
  end.
  simpl in Hupd.
  apply leF_trans with b2. exact Hupd.
  apply leF_trans with b1; assumption.
Qed.

(* 10.2  If leF (lpc_budget cell) n then after n iter_learn steps the         *)
(*       cell's budget is fz — provided there are enough truths.              *)
Lemma iter_learn_exhausts :
  forall n cell inputs truths,
    leF (lpc_budget cell) n ->
    enough_truths n truths ->
    lpc_budget (iter_learn n cell inputs truths) = fz.
Proof.
  intros n. induction n as [| n' IH]; intros cell inputs truths Hb Henough.
  - (* n = fz *)
    apply leF_fz_inv in Hb. simpl. exact Hb.
  - (* n = fs n' *)
    simpl in Henough.
    destruct truths as [| t ts].
    + destruct Henough.
    + simpl. apply IH; [| exact Henough].
      (* Need: leF (lpc_budget (learn_step cell inputs t)) n'. Case split.   *)
      destruct (lpc_budget cell) as [| b'] eqn:Ecell.
      * (* dead cell *)
        pose proof (dead_cell_no_learning cell inputs t Ecell) as [Hdead _].
        rewrite Hdead. apply leF_z.
      * (* alive cell, budget = fs b'.  destruct of (lpc_budget cell) with
           eqn rewrites Hb to leF (fs b') (fs n').                         *)
        assert (Hdec : leF (lpc_budget (learn_step cell inputs t)) b')
          by (apply (learn_step_strict_decrement cell inputs t b'); exact Ecell).
        apply leF_fs_inv in Hb.
        apply leF_trans with b'; assumption.
Qed.

(* 10.3  COROLLARY: every trajectory of length lpc_budget cell ends in        *)
(*        Freeze.  Fight cannot last forever.                                 *)
Theorem all_trajectories_end_in_freeze :
  forall cell inputs truths,
    enough_truths (lpc_budget cell) truths ->
    InFreeze (iter_learn (lpc_budget cell) cell inputs truths) inputs.
Proof.
  intros cell inputs truths Henough.
  apply zero_budget_in_freeze.
  apply iter_learn_exhausts.
  - apply leF_refl.
  - exact Henough.
Qed.

(* 10.4  COROLLARY: fight_is_finite.                                          *)
(*   The Fight regime cannot persist forever: after lpc_budget cell           *)
(*   iterations the cell is in Freeze, which is mutually exclusive with      *)
(*   Fight (Part 2: freeze_fight_exclusive).                                  *)
Theorem fight_is_finite :
  forall cell inputs truths truth_next,
    enough_truths (lpc_budget cell) truths ->
    ~ InFight (iter_learn (lpc_budget cell) cell inputs truths)
              inputs truth_next.
Proof.
  intros cell inputs truths truth_next Henough.
  apply freeze_fight_exclusive.
  apply all_trajectories_end_in_freeze. exact Henough.
Qed.

(******************************************************************************)
(* PART 11: TIGHTER COST BOUND — TWO TICKS PER ITERATION                      *)
(*                                                                            *)
(* Part 7 proved learn_step spends AT LEAST 1 tick per call.  That was        *)
(* enough for qualitative termination.  For a quantitative bound we compose   *)
(* more finely:                                                               *)
(*                                                                            *)
(*   lpc_predict at fs (fs b)  strictly drops to ≤ fs b   (Part 6)           *)
(*   compute_surprise at fs b' strictly drops to b'       (by case on pred,  *)
(*                                                         truth, 1 tick)    *)
(*   update_weights              monotone                 (Part 7.5)         *)
(*                                                                            *)
(* So: lpc_budget cell = fs (fs b)  implies  output ≤ b.  Two ticks per       *)
(* learn_step — without any new apparatus.                                    *)
(*                                                                            *)
(* NOTE on cost-as-function-of-weight-size: this floor is a CONSTANT 2,       *)
(* not a function of |ws|.  The reason: if inputs are all BUnknown, the       *)
(* accumulators spend zero, and weight size never enters.  A ws-proportional  *)
(* lower bound would require a side hypothesis on inputs (at least k BTrue    *)
(* entries with nonzero adjacent weights).  What we have below is the         *)
(* unconditional floor — the cheapest-iteration baseline.                     *)
(******************************************************************************)

(* 11.1 -------------------------------------------------------------------- *)
Theorem learn_step_two_step_decrement :
  forall cell inputs truth b,
    lpc_budget cell = fs (fs b) ->
    leF (lpc_budget (learn_step cell inputs truth)) b.
Proof.
  intros cell inputs truth b Hbud.
  unfold learn_step.
  destruct (lpc_predict cell inputs) as [[pred b1] h1] eqn:Epred.
  (* Part 6: predict on fs (fs b) drops to ≤ fs b. *)
  assert (Hb1 : leF b1 (fs b))
    by (apply (lpc_predict_strictly_decreases cell inputs (fs b) pred b1 h1);
        assumption).
  destruct (compute_surprise pred truth b1) as [[surp b2] h2] eqn:Ecs.
  (* compute_surprise on fs b1' strictly drops to b1'; on fz returns fz. *)
  assert (Hb2 : leF b2 b).
  { destruct b1 as [| b1'].
    - (* b1 = fz : surprise = (SurpriseUnknown, fz, fz) *)
      simpl in Ecs. inversion Ecs; subst. apply leF_z.
    - (* b1 = fs b1' : in all 9 pred × truth combos, b2 = b1' *)
      assert (Hb1' : leF b1' b) by (apply leF_fs_inv; exact Hb1).
      unfold compute_surprise in Ecs.
      destruct pred, truth; inversion Ecs; subst; exact Hb1'. }
  (* update_weights is monotone (Part 7.5) — does not inflate the budget. *)
  match goal with
  | [ |- leF (lpc_budget (update_weights ?C _ _)) _ ] =>
      assert (Hupd : leF (lpc_budget (update_weights C inputs surp))
                         (lpc_budget C))
        by apply update_weights_budget_le
  end.
  simpl in Hupd.
  apply leF_trans with b2; assumption.
Qed.

(* 11.2 Helper: learn_step at budget ≤ fs (fs m) produces output ≤ m.        *)
(*      Unifies the dead / one-tick / two-tick cases.                        *)
Lemma learn_step_two_cap :
  forall cell inputs truth m,
    leF (lpc_budget cell) (fs (fs m)) ->
    leF (lpc_budget (learn_step cell inputs truth)) m.
Proof.
  intros cell inputs truth m H.
  destruct (lpc_budget cell) as [| b1] eqn:E.
  - (* dead cell : output stays fz *)
    pose proof (dead_cell_no_learning cell inputs truth E) as [Hdead _].
    rewrite Hdead. apply leF_z.
  - destruct b1 as [| b2].
    + (* budget = fs fz : strict decrement drops to fz *)
      assert (Hdec : leF (lpc_budget (learn_step cell inputs truth)) fz)
        by (apply (learn_step_strict_decrement cell inputs truth fz); exact E).
      apply leF_fz_inv in Hdec. rewrite Hdec. apply leF_z.
    + (* budget = fs (fs b2) : two-step decrement drops to b2 ≤ m *)
      assert (Hdec : leF (lpc_budget (learn_step cell inputs truth)) b2)
        by (apply (learn_step_two_step_decrement cell inputs truth b2);
            exact E).
      apply leF_fs_inv in H. apply leF_fs_inv in H.
      apply leF_trans with b2; assumption.
Qed.

(* 11.3 Fin arithmetic helper: add_spur is left-successor-commuting.         *)
Lemma add_spur_fs_left : forall a b, add_spur (fs a) b = fs (add_spur a b).
Proof.
  intros a b. induction b as [| b' IH].
  - simpl. reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(* 11.4 Tight iter_learn termination: budget 2n suffices for n iterations.   *)
Lemma iter_learn_exhausts_tight :
  forall n cell inputs truths,
    leF (lpc_budget cell) (add_spur n n) ->
    enough_truths n truths ->
    lpc_budget (iter_learn n cell inputs truths) = fz.
Proof.
  intros n. induction n as [| n' IH]; intros cell inputs truths Hb Henough.
  - (* n = fz : add_spur fz fz = fz ⇒ budget = fz *)
    simpl in Hb. apply leF_fz_inv in Hb. simpl. exact Hb.
  - simpl in Henough.
    destruct truths as [| t ts].
    + destruct Henough.
    + simpl. apply IH; [| exact Henough].
      (* Need: leF (lpc_budget (learn_step cell inputs t)) (add_spur n' n').
         Rewrite add_spur (fs n') (fs n') = fs (fs (add_spur n' n')), then
         apply learn_step_two_cap.                                          *)
      apply (learn_step_two_cap cell inputs t (add_spur n' n')).
      assert (Heq : add_spur (fs n') (fs n') = fs (fs (add_spur n' n'))).
      { simpl. f_equal. apply add_spur_fs_left. }
      rewrite Heq in Hb. exact Hb.
Qed.

(* 11.5 Tight all_trajectories_end_in_freeze: n iterations suffice whenever  *)
(*      the starting budget is ≤ 2n.                                         *)
Theorem all_trajectories_end_in_freeze_tight :
  forall n cell inputs truths,
    leF (lpc_budget cell) (add_spur n n) ->
    enough_truths n truths ->
    InFreeze (iter_learn n cell inputs truths) inputs.
Proof.
  intros n cell inputs truths Hb Henough.
  apply zero_budget_in_freeze.
  apply iter_learn_exhausts_tight; assumption.
Qed.
