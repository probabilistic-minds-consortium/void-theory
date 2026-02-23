(******************************************************************************)
(* void_learning_cell.v - THEORY OF THRESHOLD LEARNING                      *)
(*                                                                          *)
(* A cell with a FinProb threshold that fires when input >= threshold.      *)
(* Learning = adjusting threshold via erode (decrease) / constrict (increase)*)
(*                                                                          *)
(* DEPENDS ON: void_finite_minimal.v, void_probability_minimal.v            *)
(* USES: FinProb for threshold and input (computational domain)             *)
(*        Budget/Heat for resource tracking (budget domain)                 *)
(*        prob_le_b3 for three-valued comparison                            *)
(*                                                                          *)
(* ALL THEOREMS FULLY PROVEN. ZERO Admitted.                                *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import void_finite_minimal.
Require Import void_probability_minimal.

Import Void_Probability_Minimal.

(******************************************************************************)
(* LEARNING CELL - threshold is FinProb, not Fin                             *)
(******************************************************************************)

Record LearningCell := mkCell {
  cell_threshold : FinProb;    (* FinProb: computational domain *)
  cell_budget : Budget;        (* Fin: budget domain *)
  cell_heat : Heat             (* Fin: budget domain *)
}.

(******************************************************************************)
(* ACTIVATE - Compare FinProb input to FinProb threshold                     *)
(* Uses prob_le_b3: cross-multiplication then le_fin_b3                      *)
(* Returns Bool3: BTrue (fires), BFalse (silent), BUnknown (exhausted)      *)
(******************************************************************************)

Definition activate (cell : LearningCell) (input : FinProb)
  : (Bool3 * LearningCell) :=
  match prob_le_b3 (cell_threshold cell) input (cell_budget cell) with
  | (result, b', h) =>
      (result, mkCell (cell_threshold cell) b' (add_heat (cell_heat cell) h))
  end.

(******************************************************************************)
(* ERODE - Decrease threshold numerator by one step                          *)
(* Denominator stays: fraction gets smaller = easier to fire                 *)
(* (fs n, d) -> (n, d)                                                      *)
(* Cost: one tick of budget                                                  *)
(******************************************************************************)

Definition erode_threshold (cell : LearningCell) : LearningCell :=
  match cell_budget cell with
  | fz => cell
  | fs b' =>
      let (num, den) := cell_threshold cell in
      match num with
      | fz => mkCell (fz, den) b' (add_heat (cell_heat cell) (fs fz))
      | fs n' => mkCell (n', den) b' (add_heat (cell_heat cell) (fs fz))
      end
  end.

(******************************************************************************)
(* CONSTRICT - Increase threshold numerator by one step                      *)
(* Denominator stays: fraction gets larger = harder to fire                  *)
(* (n, d) -> (fs n, d)                                                      *)
(* Cost: one tick of budget                                                  *)
(******************************************************************************)

Definition constrict_threshold (cell : LearningCell) : LearningCell :=
  match cell_budget cell with
  | fz => cell
  | fs b' =>
      let (num, den) := cell_threshold cell in
      mkCell (fs num, den) b' (add_heat (cell_heat cell) (fs fz))
  end.

(******************************************************************************)
(* ORDERING ON FinProb (same denominator)                                    *)
(*                                                                          *)
(* erode/constrict preserve denominator, only change numerator.              *)
(* So the natural ordering is: same den, compare numerators via leF.         *)
(******************************************************************************)

Definition leFinProb_num (p1 p2 : FinProb) : Prop :=
  snd p1 = snd p2 /\ leF (fst p1) (fst p2).

(******************************************************************************)
(* HELPER: mult_fin_heat with zero budget always returns (fz, fz, fz)       *)
(******************************************************************************)

Lemma mult_fin_heat_no_budget : forall n m,
  mult_fin_heat n m fz = (fz, fz, fz).
Proof.
  intros n m. destruct m as [|m']; simpl; reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 1: HONESTY UNDER EXHAUSTION                                       *)
(* prob_le_b3 with zero budget -> BUnknown                                   *)
(* Therefore: no budget -> cell cannot even compare -> Unknown               *)
(******************************************************************************)

Lemma prob_le_b3_no_budget : forall p1 p2,
  fst (fst (prob_le_b3 p1 p2 fz)) = BUnknown.
Proof.
  intros [n1 d1] [n2 d2].
  unfold prob_le_b3.
  assert (H1 : mult_fin_heat n1 d2 fz = (fz, fz, fz))
    by apply mult_fin_heat_no_budget.
  rewrite H1.
  assert (H2 : mult_fin_heat n2 d1 fz = (fz, fz, fz))
    by apply mult_fin_heat_no_budget.
  rewrite H2.
  simpl. reflexivity.
Qed.

Theorem activate_no_budget_unknown : forall cell input,
  cell_budget cell = fz ->
  fst (activate cell input) = BUnknown.
Proof.
  intros cell input Hb.
  unfold activate.
  rewrite Hb.
  destruct (prob_le_b3 (cell_threshold cell) input fz)
    as [[r b'] h'] eqn:E.
  simpl.
  assert (Hu : fst (fst (prob_le_b3 (cell_threshold cell) input fz)) = BUnknown)
    by apply prob_le_b3_no_budget.
  rewrite E in Hu. simpl in Hu. exact Hu.
Qed.

(******************************************************************************)
(* THEOREM 2: ERODE DECREASES THRESHOLD                                      *)
(* Numerator decreases, denominator unchanged -> fraction smaller            *)
(******************************************************************************)

Theorem erode_decreases : forall cell,
  leFinProb_num (cell_threshold (erode_threshold cell)) (cell_threshold cell).
Proof.
  intro cell. unfold erode_threshold.
  destruct (cell_budget cell) as [|b'].
  - (* No budget: unchanged *)
    unfold leFinProb_num. split.
    + reflexivity.
    + apply leF_refl.
  - (* Budget available *)
    destruct (cell_threshold cell) as [num den].
    destruct num as [|n'].
    + (* Numerator already fz: stays fz *)
      unfold leFinProb_num. simpl. split.
      * reflexivity.
      * apply leF_refl.
    + (* Numerator = fs n': decreases to n' *)
      unfold leFinProb_num. simpl. split.
      * reflexivity.
      * apply leF_step.
Qed.

Theorem erode_preserves_denominator : forall n d b' h,
  snd (cell_threshold (erode_threshold (mkCell (n, d) (fs b') h))) = d.
Proof.
  intros n d b' h. simpl. destruct n; reflexivity.
Qed.

Theorem erode_strictly_decreases_num : forall n' d b' h,
  fst (cell_threshold (erode_threshold (mkCell (fs n', d) (fs b') h))) = n'.
Proof.
  intros. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 3: CONSTRICT INCREASES THRESHOLD                                  *)
(* Numerator increases, denominator unchanged -> fraction larger             *)
(******************************************************************************)

Theorem constrict_increases : forall cell,
  leFinProb_num (cell_threshold cell) (cell_threshold (constrict_threshold cell)).
Proof.
  intro cell. unfold constrict_threshold.
  destruct (cell_budget cell) as [|b'].
  - unfold leFinProb_num. split.
    + reflexivity.
    + apply leF_refl.
  - destruct (cell_threshold cell) as [num den].
    unfold leFinProb_num. simpl. split.
    + reflexivity.
    + apply leF_step.
Qed.

Theorem constrict_preserves_denominator : forall n d b' h,
  snd (cell_threshold (constrict_threshold (mkCell (n, d) (fs b') h))) = d.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem constrict_strictly_increases_num : forall n d b' h,
  fst (cell_threshold (constrict_threshold (mkCell (n, d) (fs b') h))) = fs n.
Proof.
  intros. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 4: EACH OPERATION COSTS EXACTLY ONE TICK                          *)
(******************************************************************************)

Theorem erode_consumes_one_tick : forall n d b' h,
  cell_budget (erode_threshold (mkCell (n, d) (fs b') h)) = b'.
Proof.
  intros n d b' h. simpl. destruct n; reflexivity.
Qed.

Theorem constrict_consumes_one_tick : forall n d b' h,
  cell_budget (constrict_threshold (mkCell (n, d) (fs b') h)) = b'.
Proof.
  intros. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 5: FROZEN WHEN EXHAUSTED                                          *)
(******************************************************************************)

Theorem erode_frozen : forall p h,
  erode_threshold (mkCell p fz h) = mkCell p fz h.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem constrict_frozen : forall p h,
  constrict_threshold (mkCell p fz h) = mkCell p fz h.
Proof.
  intros. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 6: ERODE + CONSTRICT = IDENTITY ON THRESHOLD (costs 2 ticks)      *)
(******************************************************************************)

Theorem erode_constrict_inverse : forall n d b h,
  cell_threshold
    (erode_threshold (constrict_threshold (mkCell (n, d) (fs (fs b)) h)))
  = (n, d).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem erode_constrict_costs_two : forall n d b h,
  cell_budget
    (erode_threshold (constrict_threshold (mkCell (n, d) (fs (fs b)) h)))
  = b.
Proof.
  intros. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 7: HEAT MONOTONICITY (second law)                                 *)
(******************************************************************************)

Lemma add_heat_geq : forall h1 h2, leF h1 (add_heat h1 h2).
Proof.
  intros h1 h2. induction h2 as [|h2' IH].
  - simpl. apply leF_refl.
  - simpl. apply leF_trans with (y := add_heat h1 h2').
    + exact IH.
    + apply leF_step.
Qed.

Theorem erode_heat_increases : forall cell,
  leF (cell_heat cell) (cell_heat (erode_threshold cell)).
Proof.
  intro cell. unfold erode_threshold.
  destruct (cell_budget cell) as [|b'].
  - apply leF_refl.
  - destruct (cell_threshold cell) as [num den].
    destruct num; simpl; apply leF_step.
Qed.

Theorem constrict_heat_increases : forall cell,
  leF (cell_heat cell) (cell_heat (constrict_threshold cell)).
Proof.
  intro cell. unfold constrict_threshold.
  destruct (cell_budget cell) as [|b'].
  - apply leF_refl.
  - destruct (cell_threshold cell) as [num den].
    simpl. apply leF_step.
Qed.

(******************************************************************************)
(* THEOREM 8: BOUNDED LEARNING - terminates in at most B steps               *)
(******************************************************************************)

Fixpoint repeat_erode (cell : LearningCell) (fuel : Fin) : LearningCell :=
  match fuel with
  | fz => cell
  | fs fuel' => repeat_erode (erode_threshold cell) fuel'
  end.

Theorem repeat_erode_exhausts : forall b n d h,
  cell_budget (repeat_erode (mkCell (n, d) (fs b) h) (fs b)) = fz.
Proof.
  induction b; intros n d h.
  - simpl. destruct n; reflexivity.
  - simpl. destruct n as [|n']; simpl; apply IHb.
Qed.

Theorem exhausted_stays_frozen : forall p h fuel,
  repeat_erode (mkCell p fz h) fuel = mkCell p fz h.
Proof.
  intros p h fuel. induction fuel as [|fuel' IH].
  - simpl. reflexivity.
  - simpl. destruct p as [n d]. destruct n; simpl; exact IH.
Qed.

(******************************************************************************)
(* INTERFACE TO void_arithmetic.v                                            *)
(*                                                                          *)
(* The cell takes FinProb input. In a network, this input comes from:       *)
(* - mult_prob_heat : signal * weight -> weighted signal                    *)
(* - add_prob_heat  : accumulate signals from multiple sources              *)
(* - mult_fin_heat  : used internally by prob_le_b3 for comparison          *)
(*                                                                          *)
(* Activation cost depends on the size of threshold and input numerators    *)
(* because prob_le_b3 does cross-multiplication then comparison.            *)
(******************************************************************************)

(* How much budget does activation consume?                                  *)
(* prob_le_b3 does: mult(n1,d2) + mult(n2,d1) + le_fin_b3(v1,v2)          *)
(* Each multiplication costs O(min(n,m)) ticks                              *)
(* Comparison costs O(min(v1,v2)) ticks                                     *)
(* Total: bounded by initial budget (conservation)                          *)

(******************************************************************************)
(* INTERFACE TO void_geometry.v                                              *)
(*                                                                          *)
(* VoidVector = list FinProb.                                               *)
(* inner_product_b : VoidVector -> VoidVector -> Budget -> FinProb * Budget  *)
(*                                                                          *)
(* Network activation pattern:                                              *)
(*   1. Receive input as VoidVector                                         *)
(*   2. Compute inner_product_b(weights, input) -> FinProb signal           *)
(*   3. Pass FinProb signal to activate(cell, signal) -> Bool3              *)
(*   4. Bool3 verdict: fire, silent, or unknown                             *)
(*                                                                          *)
(* This is how geometry (vector space) connects to learning (threshold):    *)
(* Geometry computes the signal, the cell makes the decision.               *)
(******************************************************************************)

(* Type alias showing the connection *)
Definition CellInput := FinProb.  (* = fst (inner_product_b weights input b) *)

(* A cell with weights would compose geometry + decision *)
(* This composition is for void_network.v, not here.     *)
(* Here we prove properties of the decision unit alone.  *)
