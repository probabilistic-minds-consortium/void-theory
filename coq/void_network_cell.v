(******************************************************************************)
(* void_network_cell.v - NETWORK-READY INTERFACE EXTENSION                    *)
(*                                                                            *)
(* Extends void_predictive_learning.v with operations that wire a cell into  *)
(* a network.  The file distinguishes NETWORK-LEVEL OPERATIONS (invariants   *)
(* hold across the sender/receiver pair) from INTERNAL BUILDING BLOCKS       *)
(* (arithmetic on a single cell's budget, used to prove properties of the    *)
(* network-level ops).                                                        *)
(*                                                                            *)
(* NETWORK-LEVEL OPERATIONS (the three primitives a network step uses):      *)
(*   - learn_step_open (Part 1)                                               *)
(*       learn_step that additionally exposes prediction and surprise as      *)
(*       output signals, for wiring into another cell.                        *)
(*   - transfer_credit (Part 10)                                              *)
(*       ATOMIC budget transfer.  STRICT conservation                         *)
(*         budget sender + budget receiver is preserved exactly               *)
(*       (L1 transfer_credit_conservation).  Spur cost falls on the sender   *)
(*       (L1').  REFUSES to resurrect a dead receiver                         *)
(*       (L6 transfer_credit_freeze_absorbing): if budget receiver = fz,     *)
(*       transfer is a no-op.                                                 *)
(*   - spawn_cell (Part 11)                                                   *)
(*       GENERATIONAL SUCCESSION.  Constructs a new cell on the site of a    *)
(*       dead one, inheriting its weights (DNA / trauma) but not resurrecting*)
(*       the ancestor.  Death stays irreversible: the dead cell is still     *)
(*       the same dead cell; spawn_cell returns a DIFFERENT cell.            *)
(*                                                                            *)
(* INTERNAL BUILDING BLOCKS (not network-level; used as helpers):            *)
(*   - receive_credit  (Parts 3, 5, 6, 7, 8)                                  *)
(*       One-sided budget inflow, PAID FOR by the receiver.  Does NOT on    *)
(*       its own conserve anything - a network that used receive_credit     *)
(*       without a paired send_credit would leak budget.                     *)
(*   - send_credit  (Parts 4, 6)                                              *)
(*       One-sided budget outflow, PAID FOR by the sender.  Does NOT on its  *)
(*       own conserve anything either.                                        *)
(*   These two were initially stated as network primitives; Part 10 then     *)
(*   subsumed them with an atomic version.  They are kept because their     *)
(*   lemmas (freeze_survives_credit, receive_credit_zero_budget_noop, etc.) *)
(*   are reused as monotonicity/freeze arguments in proofs about             *)
(*   transfer_credit and are referenced by Part 8's transfer_no_free_lunch. *)
(*                                                                            *)
(* ARCHITECTURAL INVARIANTS:                                                  *)
(*   (1) No cell's lpc_budget transitions fz -> fs _.  Death is final.        *)
(*       Holds for every operation in this file.                              *)
(*   (2) Budget is QUANTUM in every CLOSED subsystem:                         *)
(*         - Isolated cell under learn_step / learn_step_open: strict         *)
(*           nonincrease (budget only goes down, never up, within one cell). *)
(*         - Pair of cells under transfer_credit: strict EQUALITY             *)
(*           (L1 transfer_credit_conservation).                               *)
(*         - Part 8's transfer_no_free_lunch pins the inequality for the     *)
(*           earlier, non-atomic receive/send pair.                           *)
(*   (3) Two operations in this file OPEN the system by referencing a budget *)
(*       source that is not yet modeled in Coq:                               *)
(*         - receive_credit (in isolation, without a paired send_credit).    *)
(*         - spawn_cell (fresh_budget argument).                              *)
(*       These are NOT exceptions to conservation.  They are PLACEHOLDERS   *)
(*       for a reservoir/environment module that will be added later and    *)
(*       will source/sink both.  When that module lands, conservation       *)
(*       closes globally - the budget that fresh_budget pulls in will be    *)
(*       exactly debited from the reservoir.  Until then: quantum within    *)
(*       the subsystems above, OPEN at the external interface.               *)
(*                                                                            *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal,                 *)
(*             void_predictive_learning, void_mortal_regime.                  *)
(* ZERO Admitted.  ZERO new Axioms.                                           *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_predictive_learning.
Require Import void_mortal_regime.

Import Void_Probability_Minimal.

(******************************************************************************)
(* PART 1: OPEN INTERFACE - learn_step_open                                   *)
(******************************************************************************)

Definition learn_step_open (cell : LearningPredCell) (inputs : list Bool3)
                           (truth : Bool3)
  : LearningPredCell * Bool3 * Surprise :=
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
          (update_weights cell' inputs surp, prediction, surp)
      end
  end.

Definition ls_cell (t : LearningPredCell * Bool3 * Surprise) : LearningPredCell :=
  fst (fst t).
Definition ls_pred (t : LearningPredCell * Bool3 * Surprise) : Bool3 :=
  snd (fst t).
Definition ls_surp (t : LearningPredCell * Bool3 * Surprise) : Surprise :=
  snd t.

(* THEOREM 1 *)
Theorem learn_step_open_consistent : forall cell inputs truth,
  ls_cell (learn_step_open cell inputs truth) = learn_step cell inputs truth.
Proof.
  intros cell inputs truth.
  unfold ls_cell, learn_step_open, learn_step.
  destruct (lpc_predict cell inputs) as [[prediction b1] h1].
  destruct (compute_surprise prediction truth b1) as [[surp b2] h2].
  reflexivity.
Qed.

(******************************************************************************)
(* PART 2: ARITHMETIC HELPERS FOR credit OPERATIONS                           *)
(*                                                                            *)
(* add_fin_b_spur_result_ge  - add never shrinks.                             *)
(* sub_saturate_result_le    - sub never grows.                               *)
(* Together these pin down the direction of budget flow under credit.         *)
(******************************************************************************)

Lemma add_fin_b_spur_result_ge : forall n m b r b_out h,
  add_fin_b_spur n m b = (r, b_out, h) ->
  leF n r.
Proof.
  intros n m. induction m as [| m' IH]; intros b r b_out h Heq.
  - (* m = fz : result = n *)
    simpl in Heq. inversion Heq. subst. apply leF_refl.
  - destruct b as [| b'].
    + (* budget exhausted : result = n *)
      simpl in Heq. inversion Heq. subst. apply leF_refl.
    + (* recurse with smaller m and b *)
      simpl in Heq.
      destruct (add_fin_b_spur n m' b') as [[r' b''] h''] eqn:Erec.
      specialize (IH b' r' b'' h'' Erec).
      inversion Heq. subst.
      apply leF_trans with r'. exact IH. apply leF_step.
Qed.

Lemma sub_saturate_result_le : forall n m b r b_out h,
  sub_saturate_b_spur n m b = (r, b_out, h) ->
  leF r n.
Proof.
  intros n. induction n as [| n' IH]; intros m b r b_out h Heq.
  - (* n = fz *)
    destruct b as [| b'].
    + simpl in Heq. inversion Heq. subst. apply leF_refl.
    + destruct m as [| m'].
      * simpl in Heq. inversion Heq. subst. apply leF_refl.
      * simpl in Heq. inversion Heq. subst. apply leF_refl.
  - (* n = fs n' *)
    destruct b as [| b'].
    + simpl in Heq. inversion Heq. subst. apply leF_z.
    + destruct m as [| m'].
      * simpl in Heq. inversion Heq. subst. apply leF_refl.
      * simpl in Heq.
        destruct (sub_saturate_b_spur n' m' b') as [[r' b''] h''] eqn:Erec.
        specialize (IH m' b' r' b'' h'' Erec).
        inversion Heq. subst.
        apply leF_trans with n'. exact IH. apply leF_step.
Qed.

(******************************************************************************)
(* PART 3: CREDIT OPERATIONS                                                  *)
(*                                                                            *)
(* Credit is not free.  The act of absorbing credit costs the receiver, the   *)
(* act of sending credit costs the sender.  Both use the cell's own budget    *)
(* as the budget of the operation: you pay with what you already have.        *)
(******************************************************************************)

Definition receive_credit (cell : LearningPredCell) (amount : Fin)
  : LearningPredCell :=
  match add_fin_b_spur (lpc_budget cell) amount (lpc_budget cell) with
  | (new_budget, _, h) =>
      mkLPC (lpc_weights_for cell)
            (lpc_weights_against cell)
            new_budget
            (add_spur (lpc_spur cell) h)
            (lpc_learning_rate cell)
            (lpc_weight_max cell)
  end.

Definition send_credit (sender : LearningPredCell) (amount : Fin)
  : LearningPredCell :=
  match sub_saturate_b_spur (lpc_budget sender) amount (lpc_budget sender) with
  | (new_budget, _, h) =>
      mkLPC (lpc_weights_for sender)
            (lpc_weights_against sender)
            new_budget
            (add_spur (lpc_spur sender) h)
            (lpc_learning_rate sender)
            (lpc_weight_max sender)
  end.

(******************************************************************************)
(* PART 4: UPDATED THEOREMS 2 - 4 FOR receive_credit                          *)
(******************************************************************************)

(* THEOREM 2: receive_credit does not touch either weight vector. *)
Theorem receive_credit_preserves_weights : forall cell amount,
  lpc_weights_for     (receive_credit cell amount) = lpc_weights_for     cell
  /\
  lpc_weights_against (receive_credit cell amount) = lpc_weights_against cell.
Proof.
  intros. unfold receive_credit.
  destruct (add_fin_b_spur (lpc_budget cell) amount (lpc_budget cell))
    as [[nb rem] h].
  simpl. split; reflexivity.
Qed.

(* THEOREM 3: the new budget is exactly the result of the saturating add,
   where the cell's own budget funds the operation.  This is the definition-
   level statement that downstream lemmas can rewrite with. *)
Theorem receive_credit_budget : forall cell amount r b_out h,
  add_fin_b_spur (lpc_budget cell) amount (lpc_budget cell) = (r, b_out, h) ->
  lpc_budget (receive_credit cell amount) = r.
Proof.
  intros cell amount r b_out h Hadd.
  unfold receive_credit.
  rewrite Hadd. simpl. reflexivity.
Qed.

(* THEOREM 4: a cell with nonzero budget that receives nonzero credit ends
   up with nonzero budget.  A zero-budget cell does NOT unfreeze via credit
   - that case is covered by receive_credit_zero_budget_noop below.  This
   theorem does NOT claim the cell exits the Freeze regime on given inputs:
   whether lpc_predict survives depends on weights and input length. *)
Theorem receive_credit_unfreezes_requires_budget :
  forall cell a b,
    lpc_budget cell = fs b ->
    exists b', lpc_budget (receive_credit cell (fs a)) = fs b'.
Proof.
  intros cell a b Hbudget.
  unfold receive_credit.
  rewrite Hbudget.
  simpl.
  destruct (add_fin_b_spur (fs b) a b) as [[r rem] h] eqn:Erec.
  simpl.
  exists r. reflexivity.
Qed.

(******************************************************************************)
(* PART 5: send_credit THEOREMS 3.1 and 3.2                                   *)
(******************************************************************************)

(* 3.1: budget after sending is no greater than budget before.               *)
Theorem send_credit_budget_le : forall sender amount,
  leF (lpc_budget (send_credit sender amount)) (lpc_budget sender).
Proof.
  intros sender amount.
  unfold send_credit.
  destruct (sub_saturate_b_spur (lpc_budget sender) amount (lpc_budget sender))
    as [[nb rem] h] eqn:Esub.
  simpl.
  apply (sub_saturate_result_le _ _ _ _ _ _ Esub).
Qed.

(* 3.2: send_credit does not touch either weight vector. *)
Theorem send_credit_preserves_weights : forall sender amount,
  lpc_weights_for     (send_credit sender amount) = lpc_weights_for     sender
  /\
  lpc_weights_against (send_credit sender amount) = lpc_weights_against sender.
Proof.
  intros. unfold send_credit.
  destruct (sub_saturate_b_spur (lpc_budget sender) amount (lpc_budget sender))
    as [[nb rem] h].
  simpl. split; reflexivity.
Qed.

(******************************************************************************)
(* PART 6: receive_credit THEOREMS 3.3, 3.4, 3.5                              *)
(******************************************************************************)

(* 3.3: absorption never shrinks the receiver's budget. *)
Theorem receive_credit_budget_le_absorb : forall cell amount,
  leF (lpc_budget cell) (lpc_budget (receive_credit cell amount)).
Proof.
  intros cell amount.
  unfold receive_credit.
  destruct (add_fin_b_spur (lpc_budget cell) amount (lpc_budget cell))
    as [[nb rem] h] eqn:Eadd.
  simpl.
  apply (add_fin_b_spur_result_ge _ _ _ _ _ _ Eadd).
Qed.

(* 3.4: a cell with zero budget absorbs nothing.
   This is the structural reason freeze_is_absorbing extends from the
   isolated cell (void_mortal_regime) to the networked cell. *)
Theorem receive_credit_zero_budget_noop : forall cell amount,
  lpc_budget cell = fz ->
  lpc_budget (receive_credit cell amount) = fz.
Proof.
  intros cell amount Hdead.
  unfold receive_credit.
  rewrite Hdead.
  (* add_fin_b_spur fz amount fz : by cases on amount, both reduce to (fz,fz,fz). *)
  destruct amount as [| a'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* 3.5: Freeze survives credit absorption.
   A dead cell that receives credit is still in Freeze for the same inputs,
   because receive_credit cannot inject budget into a zero-budget cell
   (3.4), and zero budget implies Freeze (void_mortal_regime). *)
Theorem freeze_survives_credit : forall cell inputs amount,
  lpc_budget cell = fz ->
  InFreeze (receive_credit cell amount) inputs.
Proof.
  intros cell inputs amount Hdead.
  apply zero_budget_in_freeze.
  apply receive_credit_zero_budget_noop.
  exact Hdead.
Qed.

(******************************************************************************)
(* PART 7: THEOREM 3.6 - bounded absorption                                   *)
(*                                                                            *)
(* The receiver absorbs at most what the sender sent in ideal units: the new  *)
(* budget is at most (old budget) +_spur (amount).  Equality iff the cell     *)
(* had enough budget to pay for all ticks; below that, some of the credit is  *)
(* lost to the cell's own capacity limit.                                     *)
(******************************************************************************)

(* Helper: add_spur monotonicity on the left. *)
Lemma leF_add_spur_right : forall n m, leF n (add_spur n m).
Proof.
  intros n m. induction m as [| m' IH].
  - simpl. apply leF_refl.
  - simpl. apply leF_trans with (add_spur n m'). exact IH. apply leF_step.
Qed.

(* Helper: add_fin_b_spur result is at most the spur-saturated sum. *)
Lemma add_fin_b_spur_le_add_spur : forall n m b r b_out h,
  add_fin_b_spur n m b = (r, b_out, h) ->
  leF r (add_spur n m).
Proof.
  intros n m. induction m as [| m' IH]; intros b r b_out h Heq.
  - (* m = fz : result = n, add_spur n fz = n *)
    simpl in Heq. inversion Heq. subst. simpl. apply leF_refl.
  - destruct b as [| b'].
    + (* budget exhausted : result = n, target = fs (add_spur n m') *)
      simpl in Heq.
      assert (Hr : r = n) by (inversion Heq; reflexivity).
      rewrite Hr. simpl.
      apply leF_trans with (add_spur n m').
      * apply leF_add_spur_right.
      * apply leF_step.
    + (* recurse *)
      simpl in Heq.
      destruct (add_fin_b_spur n m' b') as [[r' b''] h''] eqn:Erec.
      specialize (IH b' r' b'' h'' Erec).
      assert (Hr : r = fs r') by (inversion Heq; reflexivity).
      rewrite Hr. simpl.
      constructor. exact IH.
Qed.

Theorem receive_credit_partial : forall cell amount,
  leF (lpc_budget (receive_credit cell amount))
      (add_spur (lpc_budget cell) amount).
Proof.
  intros cell amount.
  unfold receive_credit.
  destruct (add_fin_b_spur (lpc_budget cell) amount (lpc_budget cell))
    as [[nb rem] h] eqn:Eadd.
  simpl.
  apply (add_fin_b_spur_le_add_spur _ _ _ _ _ _ Eadd).
Qed.

(******************************************************************************)
(* PART 8: THEOREM 3.7 - CONSERVATION, HONEST ACCOUNTING                      *)
(*                                                                            *)
(* The literal statement in the brief - sum(budgets + spuren) before = after  *)
(* - does NOT hold under the current definitions, and this is informative.    *)
(*                                                                            *)
(* Reason: send_credit and receive_credit are INDEPENDENT operations with     *)
(* independent budgets.  The amount argument appears in both, but what the    *)
(* sender actually spends (min(amount, B_s)) is unrelated to what the         *)
(* receiver actually absorbs (min(amount, B_r)).  Consequently:               *)
(*                                                                            *)
(*   Sender: budget drops by min(amount, B_s); spur grows by 1 + min(amount,  *)
(*           B_s).  Net (budget + spur) increases by 1 (the transmission      *)
(*           cost - the base of sub_saturate_b_spur's recursion).             *)
(*   Receiver: budget grows by min(amount, B_r); spur grows by min(amount,   *)
(*             B_r).  Net (budget + spur) increases by 2 * min(amount, B_r). *)
(*                                                                            *)
(* Sum across sender and receiver increases by 1 + 2 * min(amount, B_r) - an  *)
(* injection of "new" ticks into the system.                                  *)
(*                                                                            *)
(* The model makes this injection visible because receive_credit treats the   *)
(* amount as an EXTERNAL parameter that appears from outside the system.      *)
(* Strict conservation would require an atomic transfer_credit op pairing     *)
(* sender and receiver so the amount that leaves one is exactly the amount   *)
(* that arrives at the other, minus well-accounted operational cost.  That    *)
(* is a next-brief concern.                                                   *)
(*                                                                            *)
(* What CAN be proved here is an inequality: the system never gains more      *)
(* budget than the amount injected.  The sum of the new budgets is bounded   *)
(* by the sum of the old budgets plus amount.  This is the correct weak      *)
(* form of "no free lunch" for the pair of operations.                        *)
(******************************************************************************)

(* Helper: add_spur is monotone in the left argument (holding right fixed). *)
Lemma add_spur_mono_left : forall a b c, leF a b -> leF (add_spur a c) (add_spur b c).
Proof.
  intros a b c Hab. induction c as [| c' IH].
  - simpl. exact Hab.
  - simpl. constructor. exact IH.
Qed.

(* Helper: add_spur is monotone in the right argument. *)
Lemma add_spur_mono_right : forall b x y, leF x y -> leF (add_spur b x) (add_spur b y).
Proof.
  intros b x y Hxy. revert b. induction Hxy; intros b.
  - (* leF_z : x = fz, y = m.  Show leF b (add_spur b m). *)
    simpl. apply leF_add_spur_right.
  - (* leF_ss : x = fs n, y = fs m, with leF n m. *)
    simpl. constructor. apply IHHxy.
Qed.

Theorem transfer_no_free_lunch : forall sender receiver amount,
  leF (add_spur (lpc_budget (send_credit sender amount))
                (lpc_budget (receive_credit receiver amount)))
      (add_spur (lpc_budget sender)
                (add_spur (lpc_budget receiver) amount)).
Proof.
  intros sender receiver amount.
  apply leF_trans with
    (add_spur (lpc_budget sender) (lpc_budget (receive_credit receiver amount))).
  - (* Monotone in the left: send_credit_budget_le. *)
    apply add_spur_mono_left. apply send_credit_budget_le.
  - (* Monotone in the right: receive_credit_partial. *)
    apply add_spur_mono_right. apply receive_credit_partial.
Qed.

(******************************************************************************)
(* PART 9: THEOREM 3.8 - UNFREEZING IS CONDITIONAL                            *)
(*                                                                            *)
(* The brief s full statement - there exists a threshold such that below it  *)
(* the cell stays frozen and above it it unfreezes - is a two-sided quantity  *)
(* statement about lpc_predict whose universal form depends on the weights    *)
(* and inputs.  Below we give the simplified variant requested: an explicit   *)
(* witness of a cell + inputs configuration where                            *)
(*   - zero credit keeps the cell in Freeze,                                  *)
(*   - enough credit pushes it out.                                           *)
(*                                                                            *)
(* The witness is a minimal cell: one for-weight of value 1, no against-     *)
(* weights, and an input list [BTrue].  Predict for this cell needs three     *)
(* budget ticks (one for the for-accumulator, two for the two le_fin_b3       *)
(* comparisons) before it can distinguish BTrue from the empty against-side. *)
(* Budget 2 is insufficient (Freeze); budget 4 suffices (not Freeze).         *)
(* receive_credit amount=3 on a budget-2 cell brings it to budget 4.         *)
(******************************************************************************)

(* Example cell: budget 2, weights_for = [1], weights_against = [].  *)
Definition cell_at_threshold : LearningPredCell :=
  mkLPC [fs fz] [] (fs (fs fz)) fz (fz, fs fz) (fs fz).

(* Witness: the same cell is in Freeze because budget 2 is not enough to
   complete lpc_predict. *)
Lemma cell_at_threshold_frozen :
  InFreeze cell_at_threshold [BTrue].
Proof.
  unfold InFreeze, predict_value, cell_at_threshold. simpl. reflexivity.
Qed.

(* Witness: zero credit leaves the cell still in Freeze. *)
Lemma cell_at_threshold_zero_credit_frozen :
  InFreeze (receive_credit cell_at_threshold fz) [BTrue].
Proof.
  unfold InFreeze, predict_value, receive_credit, cell_at_threshold.
  simpl. reflexivity.
Qed.

(* Witness: credit of amount 3 unfreezes the cell (predict returns BTrue). *)
Lemma cell_at_threshold_enough_credit_unfreezes :
  ~ InFreeze (receive_credit cell_at_threshold (fs (fs (fs fz)))) [BTrue].
Proof.
  unfold InFreeze, predict_value, receive_credit, cell_at_threshold.
  simpl. discriminate.
Qed.

(* The full conditional-unfreeze statement. *)
Theorem unfreeze_is_conditional :
  exists cell inputs amount_blocks amount_wakes,
    InFreeze cell inputs /\
    InFreeze (receive_credit cell amount_blocks) inputs /\
    ~ InFreeze (receive_credit cell amount_wakes) inputs.
Proof.
  exists cell_at_threshold, [BTrue], fz, (fs (fs (fs fz))).
  split; [| split].
  - apply cell_at_threshold_frozen.
  - apply cell_at_threshold_zero_credit_frozen.
  - apply cell_at_threshold_enough_credit_unfreezes.
Qed.

(******************************************************************************)
(* PART 10: ATOMIC TRANSFER - transfer_credit                                 *)
(*                                                                            *)
(* Part 8 (transfer_no_free_lunch) was an honest inequality: the pair         *)
(*   send_credit sender amount  /\  receive_credit receiver amount            *)
(* is not a conserving operation, because `amount` enters the receive side   *)
(* from outside the system instead of being exactly what the sender lost.    *)
(*                                                                            *)
(* This part closes that hole with a single ATOMIC operation. The mechanism: *)
(* a dedicated fixpoint `transfer_budget` that walks tick-by-tick, at each   *)
(* step DECREMENTING sender and INCREMENTING receiver simultaneously. Budget *)
(* is strictly conserved: ticks are MOVED, not created or destroyed.          *)
(*                                                                            *)
(* --- FREEZE IS ABSORBING (architectural decision). ---                      *)
(* A DEAD receiver (lpc_budget receiver = fz) is NOT eligible for transfer.  *)
(* Transferring ticks into a zero-budget cell would resurrect it, which      *)
(* contradicts void_mortal_regime's zero_budget_in_freeze / InFreeze being   *)
(* terminal. We guard transfer_credit explicitly:                             *)
(*                                                                            *)
(*    lpc_budget receiver = fz  =>  transfer_credit = (sender, receiver)     *)
(*                                  (strict no-op on both sides)             *)
(*                                                                            *)
(* The network layer handles dead-cell positions via `spawn_cell` (Part 11), *)
(* which is a DIFFERENT semantic operation - birth, not transfer. The caller *)
(* (network orchestrator) decides whether a dead position is to be spawned   *)
(* anew or left dead; transfer_credit itself refuses to resurrect.           *)
(*                                                                            *)
(* --- Cost model (living-receiver branch only). ---                          *)
(* The operation has a computational cost, returned as a third Fin component *)
(* `h`. That cost is charged ENTIRELY to the sender's spur, not shared:      *)
(*                                                                            *)
(*   - Sender initiates the transfer. Sender decides, sender pays compute.   *)
(*   - Receiver is passive. "Receiver also pays" would mean receiver's       *)
(*     budget is debited for absorbing inflow, which immediately cancels     *)
(*     part of what was transferred - that is taxation, not conservation.    *)
(*                                                                            *)
(* In the NO-OP (dead-receiver) branch neither cell's spur changes either -  *)
(* the check happens at the network orchestrator layer, not in the cell's    *)
(* own accounting. That choice is arguable; recording it here openly.        *)
(******************************************************************************)

(* Raw transfer primitive on Fin values. Returns (new_bs, new_br, cost).      *)
(* Step rule: while amount > 0 and bs > 0, move one tick; else stop (base    *)
(* cost 1 for the emptiness check when amount > 0 but bs = fz).              *)
(* NOTE: `{struct amount}` is REQUIRED here. Without it Coq infers `{struct bs}`
   (the first candidate argument it finds structurally smaller in a recursive
   call), which makes `simpl`/`cbn` fail to reduce the fixpoint when `bs` is
   a variable - blocking every proof of the base case amount = fz. *)
Fixpoint transfer_budget (bs br amount : Fin) {struct amount} : Fin * Fin * Fin :=
  match amount with
  | fz => (bs, br, fz)
  | fs amount' =>
      match bs with
      | fz => (bs, br, fs fz)
      | fs bs' =>
          let '(nbs, nbr, h) := transfer_budget bs' (fs br) amount' in
          (nbs, nbr, fs h)
      end
  end.

Definition transfer_credit (sender receiver : LearningPredCell) (amount : Fin)
  : LearningPredCell * LearningPredCell :=
  match lpc_budget receiver with
  | fz => (sender, receiver)  (* DEAD RECEIVER: no transfer, freeze absorbs. *)
  | fs _ =>
      match transfer_budget (lpc_budget sender) (lpc_budget receiver) amount with
      | (new_bs, new_br, h) =>
          (mkLPC (lpc_weights_for sender)
                 (lpc_weights_against sender)
                 new_bs
                 (add_spur (lpc_spur sender) h)
                 (lpc_learning_rate sender)
                 (lpc_weight_max sender),
           mkLPC (lpc_weights_for receiver)
                 (lpc_weights_against receiver)
                 new_br
                 (lpc_spur receiver)
                 (lpc_learning_rate receiver)
                 (lpc_weight_max receiver))
      end
  end.

(* --- Raw lemma on transfer_budget: STRICT BUDGET CONSERVATION. --- *)
Lemma transfer_budget_conserves : forall amount bs br nbs nbr h,
  transfer_budget bs br amount = (nbs, nbr, h) ->
  add_spur nbs nbr = add_spur bs br.
Proof.
  induction amount as [| amount' IH]; intros bs br nbs nbr h Heq.
  - simpl in Heq. inversion Heq; subst. reflexivity.
  - simpl in Heq. destruct bs as [| bs'].
    + inversion Heq; subst. reflexivity.
    + destruct (transfer_budget bs' (fs br) amount') as [[nbs' nbr'] h'] eqn:Erec.
      specialize (IH bs' (fs br) nbs' nbr' h' Erec).
      inversion Heq; subst.
      rewrite IH. simpl. rewrite add_spur_fs_l. reflexivity.
Qed.

(* --- Raw lemma: transfer_budget never increases the sender's budget. --- *)
Lemma transfer_budget_sender_le : forall amount bs br nbs nbr h,
  transfer_budget bs br amount = (nbs, nbr, h) -> leF nbs bs.
Proof.
  induction amount as [| amount' IH]; intros bs br nbs nbr h Heq.
  - simpl in Heq. inversion Heq; subst. apply leF_refl.
  - simpl in Heq. destruct bs as [| bs'].
    + inversion Heq; subst. apply leF_refl.
    + destruct (transfer_budget bs' (fs br) amount') as [[nbs' nbr'] h'] eqn:Erec.
      specialize (IH bs' (fs br) nbs' nbr' h' Erec).
      inversion Heq; subst.
      apply leF_trans with bs'. exact IH. apply leF_step.
Qed.

(* --- Raw lemma: transfer_budget never decreases the receiver's budget. --- *)
Lemma transfer_budget_receiver_ge : forall amount bs br nbs nbr h,
  transfer_budget bs br amount = (nbs, nbr, h) -> leF br nbr.
Proof.
  induction amount as [| amount' IH]; intros bs br nbs nbr h Heq.
  - simpl in Heq. inversion Heq; subst. apply leF_refl.
  - simpl in Heq. destruct bs as [| bs'].
    + inversion Heq; subst. apply leF_refl.
    + destruct (transfer_budget bs' (fs br) amount') as [[nbs' nbr'] h'] eqn:Erec.
      specialize (IH bs' (fs br) nbs' nbr' h' Erec).
      inversion Heq; subst.
      apply leF_trans with (fs br). apply leF_step. exact IH.
Qed.

(* --- Raw lemma: zero-budget sender stays at zero; receiver unchanged. --- *)
Lemma transfer_budget_zero_sender : forall amount br nbs nbr h,
  transfer_budget fz br amount = (nbs, nbr, h) ->
  nbs = fz /\ nbr = br.
Proof.
  induction amount as [| amount' IH]; intros br nbs nbr h Heq.
  - simpl in Heq. inversion Heq; subst. split; reflexivity.
  - simpl in Heq. inversion Heq; subst. split; reflexivity.
Qed.

(******************************************************************************)
(* NAMED LEMMAS (brief L1 - L5) LIFTED TO LearningPredCell.                   *)
(******************************************************************************)

(* L1. transfer_credit_conservation - STRICT BUDGET CONSERVATION.
   Sum of budgets after transfer equals sum of budgets before, UNCONDITIONALLY.
   Both branches satisfy the equality:
     - dead receiver:   (sender, receiver) identity  =>  both sides identical.
     - alive receiver:  transfer_budget_conserves handles it. *)
Theorem transfer_credit_conservation : forall sender receiver amount,
  add_spur (lpc_budget (fst (transfer_credit sender receiver amount)))
           (lpc_budget (snd (transfer_credit sender receiver amount)))
  = add_spur (lpc_budget sender) (lpc_budget receiver).
Proof.
  intros sender receiver amount.
  unfold transfer_credit.
  destruct (lpc_budget receiver) as [| br'] eqn:Hbr.
  - (* dead receiver: no-op. *)
    simpl. rewrite Hbr. reflexivity.
  - (* alive receiver: delegate to raw lemma. *)
    destruct (transfer_budget (lpc_budget sender) (fs br') amount)
      as [[nbs nbr] h] eqn:Etrans.
    simpl.
    apply (transfer_budget_conserves _ _ _ _ _ _ Etrans).
Qed.

(* L1'. Full accounting (living-receiver branch only): sender.spur absorbs
   exactly the transfer cost h; receiver.spur is unchanged. Restricted to
   the alive-receiver branch because the no-op branch does not invoke
   transfer_budget and thus has no cost to account for. *)
Theorem transfer_credit_spur_charged_to_sender :
  forall sender receiver amount br',
    lpc_budget receiver = fs br' ->
    lpc_spur (fst (transfer_credit sender receiver amount))
      = add_spur (lpc_spur sender)
                 (snd (transfer_budget (lpc_budget sender) (fs br') amount))
    /\
    lpc_spur (snd (transfer_credit sender receiver amount))
      = lpc_spur receiver.
Proof.
  intros sender receiver amount br' Hbr.
  unfold transfer_credit.
  rewrite Hbr.
  destruct (transfer_budget (lpc_budget sender) (fs br') amount)
    as [[nbs nbr] h] eqn:Etrans.
  simpl. split; reflexivity.
Qed.

(* L2. transfer_credit_sender_le - sender's budget never grows. *)
Theorem transfer_credit_sender_le : forall sender receiver amount,
  leF (lpc_budget (fst (transfer_credit sender receiver amount)))
      (lpc_budget sender).
Proof.
  intros sender receiver amount.
  unfold transfer_credit.
  destruct (lpc_budget receiver) as [| br'] eqn:Hbr.
  - simpl. apply leF_refl.
  - destruct (transfer_budget (lpc_budget sender) (fs br') amount)
      as [[nbs nbr] h] eqn:Etrans.
    simpl.
    apply (transfer_budget_sender_le _ _ _ _ _ _ Etrans).
Qed.

(* L3. transfer_credit_receiver_ge - receiver's budget never shrinks. *)
Theorem transfer_credit_receiver_ge : forall sender receiver amount,
  leF (lpc_budget receiver)
      (lpc_budget (snd (transfer_credit sender receiver amount))).
Proof.
  intros sender receiver amount.
  unfold transfer_credit.
  destruct (lpc_budget receiver) as [| br'] eqn:Hbr.
  - simpl. rewrite Hbr. apply leF_refl.
  - destruct (transfer_budget (lpc_budget sender) (fs br') amount)
      as [[nbs nbr] h] eqn:Etrans.
    simpl.
    apply (transfer_budget_receiver_ge _ _ _ _ _ _ Etrans).
Qed.

(* L4. transfer_credit_zero_sender_noop - dead sender moves no ticks.
   Budget equality on both sides; receiver's budget is literally preserved
   in BOTH sub-branches because either we hit no-op (dead receiver, so
   both cells unchanged) or transfer_budget with a zero sender leaves
   receiver's budget intact (raw lemma transfer_budget_zero_sender). *)
Theorem transfer_credit_zero_sender_noop : forall sender receiver amount,
  lpc_budget sender = fz ->
  lpc_budget (fst (transfer_credit sender receiver amount)) = fz /\
  lpc_budget (snd (transfer_credit sender receiver amount))
    = lpc_budget receiver.
Proof.
  intros sender receiver amount Hdead.
  unfold transfer_credit.
  destruct (lpc_budget receiver) as [| br'] eqn:Hbr.
  - (* dead receiver: no-op; sender's budget is fz via Hdead, receiver's is fz via Hbr. *)
    simpl. split. exact Hdead. rewrite Hbr. reflexivity.
  - (* alive receiver, dead sender: transfer_budget fz (fs br') amount. *)
    rewrite Hdead.
    destruct (transfer_budget fz (fs br') amount)
      as [[nbs nbr] h] eqn:Etrans.
    simpl.
    destruct (transfer_budget_zero_sender _ _ _ _ _ Etrans) as [Hnbs Hnbr].
    split. exact Hnbs. exact Hnbr.
Qed.

(* L5. transfer_credit_preserves_weights - both sides keep both weight
   vectors untouched, regardless of which branch fires. *)
Theorem transfer_credit_preserves_weights : forall sender receiver amount,
  lpc_weights_for
    (fst (transfer_credit sender receiver amount)) = lpc_weights_for     sender
  /\
  lpc_weights_against
    (fst (transfer_credit sender receiver amount)) = lpc_weights_against sender
  /\
  lpc_weights_for
    (snd (transfer_credit sender receiver amount)) = lpc_weights_for     receiver
  /\
  lpc_weights_against
    (snd (transfer_credit sender receiver amount)) = lpc_weights_against receiver.
Proof.
  intros sender receiver amount.
  unfold transfer_credit.
  destruct (lpc_budget receiver) as [| br'] eqn:Hbr.
  - simpl. repeat split; reflexivity.
  - destruct (transfer_budget (lpc_budget sender) (fs br') amount)
      as [[nbs nbr] h].
    simpl. repeat split; reflexivity.
Qed.

(* L6. transfer_credit_freeze_absorbing - the CORRECTNESS STATEMENT for the
   refactor. A dead receiver stays dead after transfer_credit. This is what
   was BROKEN before adding the no-op branch, and is now provable. *)
Theorem transfer_credit_freeze_absorbing : forall sender receiver amount,
  lpc_budget receiver = fz ->
  lpc_budget (snd (transfer_credit sender receiver amount)) = fz.
Proof.
  intros sender receiver amount Hdead.
  unfold transfer_credit.
  rewrite Hdead. simpl. exact Hdead.
Qed.

(******************************************************************************)
(* PART 11: SPAWN PRIMITIVES - INHERITANCE, AND A DOCUMENTARY TABULA RASA    *)
(*                                                                            *)
(* ONLY spawn_inherited is used as a network primitive.  The other one in   *)
(* this section, spawn_random, is a DOCUMENTARY primitive whose R3 lemma   *)
(* proves why tabula rasa cannot function as an exploration mode in this   *)
(* stack: zero weights fold accumulators to fz on every input, lpc_predict *)
(* returns BUnknown, compute_surprise returns SurpriseUnknown, and         *)
(* update_weights with SurpriseUnknown is a no-op.  A spawn_random cell    *)
(* is therefore ineducable - it starts at zero and stays at zero forever.  *)
(*                                                                            *)
(* The architectural reading of that lemma: in a finitist, mortal, trauma- *)
(* indexed framework, there is no neutral starting point.  Every new cell  *)
(* must inherit from something.  void_mortal_network.v enforces this by   *)
(* replacing every dead cell via spawn_inherited from either the dead     *)
(* cell itself, a living sibling, or the layer's head cell - never from   *)
(* nothing.  spawn_random stays in this file as a proof obligation against *)
(* a competing design, not as a network operation.                          *)
(*                                                                            *)
(* spawn_inherited - INHERITANCE.  New cell on the site of a dead one;     *)
(*   weights are copied from a TEMPLATE (not necessarily the dead cell    *)
(*   itself - void_mortal_network may pass a living sibling's weights    *)
(*   when the dead cell's weights were the ones that failed).  Budget     *)
(*   comes from a parent reservoir (explicit argument, OPEN see header). *)
(*   Spuren reset to fz.                                                    *)
(*                                                                            *)
(* spawn_random - ZERO-WEIGHT WITNESS.  Documentary only.  Kept so R3     *)
(*   stands as a proof against using it.                                   *)
(*                                                                            *)
(* ARCHITECTURAL INVARIANTS (both primitives):                                *)
(*   - Neither operation MODIFIES the dead cell.  Both construct new       *)
(*     cells.  Death stays irreversible.                                    *)
(*   - Both are OPEN (see header): budget comes from outside the file.   *)
(*                                                                            *)
(* HELPER: zeros_fin (n : Fin) : list Fin                                   *)
(*   Strictly-finitist replicate fz.  Used by spawn_random only.          *)
(*                                                                            *)
(* I1 spawn_inherited_weights - weights are passed through.                 *)
(* I2 spawn_inherited_budget  - budget = parent_budget.                     *)
(* I3 spawn_inherited_trauma_witness - inherited weights cause confident    *)
(*    wrong prediction where clean weights give BUnknown.                   *)
(* R1 spawn_random_zero_weights - both weight vectors are zeros_fin n.     *)
(* R2 spawn_random_budget       - budget = supplied budget.                *)
(* R3 spawn_random_no_trauma_witness - a zero-weight cell produces        *)
(*    SurpriseUnknown (never SurpriseFor/Against) on any given input.     *)
(*    This is the proof that tabula rasa is ineducable: SurpriseUnknown   *)
(*    triggers update_weights no-op (void_predictive_learning), so the    *)
(*    cell's zero weights are a fixed point.                               *)
(******************************************************************************)

(* Fin-indexed zeros list.  This is the strictly-finitist analogue of      *)
(* List.repeat fz n for nat n.  Defined here rather than in              *)
(* void_finite_minimal so the coupling to list Fin stays local.          *)
Fixpoint zeros_fin (n : Fin) : list Fin :=
  match n with
  | fz    => []
  | fs n' => fz :: zeros_fin n'
  end.

(* SPAWN VARIANT 1: inherited weights, parent-supplied budget.             *)
Definition spawn_inherited (dead : LearningPredCell) (parent_budget : Fin)
  : LearningPredCell :=
  mkLPC (lpc_weights_for dead)
        (lpc_weights_against dead)
        parent_budget
        fz
        (lpc_learning_rate dead)
        (lpc_weight_max dead).

(* SPAWN VARIANT 2: zero weights, fully specified new cell parameters.     *)
Definition spawn_random (n_inputs : Fin) (budget : Fin)
                        (lr : FinProb) (wmax : Fin)
  : LearningPredCell :=
  mkLPC (zeros_fin n_inputs)
        (zeros_fin n_inputs)
        budget
        fz
        lr
        wmax.

(* I1. Inherited weights - DNA / trauma passes through.                    *)
Theorem spawn_inherited_weights :
  forall dead parent_budget,
    lpc_budget dead = fz ->
    lpc_weights_for     (spawn_inherited dead parent_budget)
      = lpc_weights_for     dead /\
    lpc_weights_against (spawn_inherited dead parent_budget)
      = lpc_weights_against dead.
Proof.
  intros dead parent_budget _.
  unfold spawn_inherited. simpl.
  split; reflexivity.
Qed.

(* I2. Budget is exactly parent_budget.                                     *)
Theorem spawn_inherited_budget :
  forall dead parent_budget,
    lpc_budget dead = fz ->
    lpc_budget (spawn_inherited dead parent_budget) = parent_budget.
Proof.
  intros dead parent_budget _.
  unfold spawn_inherited. simpl. reflexivity.
Qed.

(* I3 witness configurations - two dead cells, identical except for        *)
(* inherited for-weights.  Reused from old S4.                             *)
Definition dead_traumatic : LearningPredCell :=
  mkLPC [fs fz] [] fz fz (fz, fs fz) (fs fz).

Definition dead_clean : LearningPredCell :=
  mkLPC [] [] fz fz (fz, fs fz) (fs fz).

Lemma dead_traumatic_is_dead : lpc_budget dead_traumatic = fz.
Proof. reflexivity. Qed.

Lemma dead_clean_is_dead : lpc_budget dead_clean = fz.
Proof. reflexivity. Qed.

(* I3. Inherited weights can HURT. Same parent_budget, same inputs, same    *)
(* truth; different inherited weights produce distinct Surprise classes.   *)
Theorem spawn_inherited_trauma_witness :
  ls_surp (learn_step_open (spawn_inherited dead_traumatic
                                            (fs (fs (fs (fs fz)))))
                           [BTrue] BFalse)
  = SurpriseAgainst
  /\
  ls_surp (learn_step_open (spawn_inherited dead_clean
                                            (fs (fs (fs (fs fz)))))
                           [BTrue] BFalse)
  = SurpriseUnknown.
Proof.
  split; reflexivity.
Qed.

(* Bundled existential carried over from old intergenerational_trauma_exists. *)
Theorem intergenerational_trauma_exists :
  exists dead1 dead2 parent_budget inputs truth,
    lpc_budget dead1 = fz /\
    lpc_budget dead2 = fz /\
    ls_surp (learn_step_open (spawn_inherited dead1 parent_budget) inputs truth)
    <> ls_surp (learn_step_open (spawn_inherited dead2 parent_budget) inputs truth).
Proof.
  exists dead_traumatic, dead_clean,
         (fs (fs (fs (fs fz)))), [BTrue], BFalse.
  split; [reflexivity |].
  split; [reflexivity |].
  destruct spawn_inherited_trauma_witness as [Htrau Hclean].
  rewrite Htrau, Hclean. discriminate.
Qed.

(* R1. spawn_random gives zero weights in both vectors.                     *)
Theorem spawn_random_zero_weights :
  forall n b lr wm,
    lpc_weights_for     (spawn_random n b lr wm) = zeros_fin n /\
    lpc_weights_against (spawn_random n b lr wm) = zeros_fin n.
Proof.
  intros n b lr wm.
  unfold spawn_random. simpl.
  split; reflexivity.
Qed.

(* R2. Budget is exactly b.                                                 *)
Theorem spawn_random_budget :
  forall n b lr wm,
    lpc_budget (spawn_random n b lr wm) = b.
Proof.
  intros n b lr wm.
  unfold spawn_random. simpl. reflexivity.
Qed.

(* R3 witness: a tabula-rasa cell with n_inputs=2, budget=8, on any input  *)
(* list, produces SurpriseUnknown.  Intuition: both accumulators stay at  *)
(* fz (adding fz weight to acc leaves acc unchanged), so acc_for=acc_against*)
(* =fz, so le_fin_b3 fz fz is BTrue twice, so lpc_predict = BUnknown,     *)
(* so compute_surprise = SurpriseUnknown.                                  *)
(*                                                                            *)
(* Witness, not universal: proving this for ALL inputs would require       *)
(* induction on list Bool3 + invariants about accumulate_for_lpc.  The     *)
(* brief explicitly allows the witness form.                               *)
Theorem spawn_random_no_trauma_witness :
  ls_surp (learn_step_open
             (spawn_random (fs (fs fz))
                           (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))
                           (fz, fs fz) (fs fz))
             [BTrue; BFalse] BTrue)
  = SurpriseUnknown.
Proof.
  reflexivity.
Qed.
