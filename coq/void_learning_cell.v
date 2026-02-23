(******************************************************************************)
(* void_learning_cell.v - THEORY OF THRESHOLD LEARNING                      *)
(*                                                                          *)
(* A cell with a FinProb threshold that fires when input >= threshold.      *)
(* Learning = adjusting threshold via erode (decrease) / constrict (increase)*)
(*                                                                          *)
(* BOUNDARY INVARIANT: 0 < numerator < denominator. ALWAYS.                 *)
(* Probability 0 and probability 1 are unreachable boundaries.              *)
(* erode cannot go below 1/d. constrict cannot reach d/d.                   *)
(*                                                                          *)
(* DEPENDS ON: void_finite_minimal.v, void_probability_minimal.v            *)
(* ALL THEOREMS FULLY PROVEN. ZERO Admitted.                                *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import void_finite_minimal.
Require Import void_probability_minimal.

Import Void_Probability_Minimal.

(******************************************************************************)
(* VALID PROBABILITY - the fundamental invariant                             *)
(*                                                                          *)
(* A valid FinProb (n, d) satisfies:                                        *)
(*   1. n > 0           (never probability 0)                               *)
(*   2. n < d           (never probability 1)                               *)
(*   3. d >= 2          (implied: room must exist between 0 and 1)          *)
(******************************************************************************)

Definition valid_prob (p : FinProb) : Prop :=
  match p with
  | (num, den) =>
      match num with
      | fz => False                 (* numerator must be > 0 *)
      | fs _ => leF (fs num) den    (* fs num <= den means num < den *)
      end
  end.

Lemma valid_half : valid_prob half.
Proof. unfold valid_prob, half. simpl. apply leF_refl. Qed.

Lemma valid_third : valid_prob third.
Proof. unfold valid_prob, third. simpl. apply leF_step. Qed.

Lemma valid_two_thirds : valid_prob (fs (fs fz), fs (fs (fs fz))).
Proof. unfold valid_prob. simpl. apply leF_refl. Qed.

(******************************************************************************)
(* LEARNING CELL                                                             *)
(******************************************************************************)

Record LearningCell := mkCell {
  cell_threshold : FinProb;
  cell_budget : Budget;
  cell_heat : Heat
}.

(******************************************************************************)
(* ACTIVATE                                                                  *)
(******************************************************************************)

Definition activate (cell : LearningCell) (input : FinProb)
  : (Bool3 * LearningCell) :=
  match prob_le_b3 (cell_threshold cell) input (cell_budget cell) with
  | (result, b', h) =>
      (result, mkCell (cell_threshold cell) b' (add_heat (cell_heat cell) h))
  end.

(******************************************************************************)
(* ERODE - Decrease threshold                                                *)
(*                                                                          *)
(* (fs (fs n'), d) -> (fs n', d)    safe                                    *)
(* (fs fz, d) -> unchanged          BOUNDARY: 1/d is minimum               *)
(* (fz, d) -> unchanged             guard: already invalid                  *)
(*                                                                          *)
(* Lower boundary check is structural - free. One tick for the operation.   *)
(******************************************************************************)

Definition erode_threshold (cell : LearningCell) : LearningCell :=
  match cell_budget cell with
  | fz => cell
  | fs b' =>
      let (num, den) := cell_threshold cell in
      match num with
      | fz => cell
      | fs fz => cell                    (* BOUNDARY: 1/d *)
      | fs (fs n') =>
          mkCell (fs n', den) b' (add_heat (cell_heat cell) (fs fz))
      end
  end.

(******************************************************************************)
(* CONSTRICT - Increase threshold                                            *)
(*                                                                          *)
(* Must verify: fs num /= den (would be probability 1).                     *)
(* Uses fin_eq_b3 - COSTS BUDGET. Even checking a boundary costs.           *)
(*                                                                          *)
(* BTrue  -> fs num = den -> BLOCKED (at boundary)                          *)
(* BFalse -> fs num /= den -> safe to increment                             *)
(* BUnknown -> cannot verify -> BLOCKED (conservative)                      *)
(******************************************************************************)

Definition constrict_threshold (cell : LearningCell) : LearningCell :=
  match cell_budget cell with
  | fz => cell
  | fs b' =>
      let (num, den) := cell_threshold cell in
      match fin_eq_b3 (fs num) den b' with
      | (BTrue, b'', h) =>
          mkCell (num, den) b'' (add_heat (cell_heat cell) (fs h))
      | (BFalse, b'', h) =>
          mkCell (fs num, den) b'' (add_heat (cell_heat cell) (fs h))
      | (BUnknown, b'', h) =>
          mkCell (num, den) b'' (add_heat (cell_heat cell) (fs h))
      end
  end.

(******************************************************************************)
(* ORDERING ON FinProb (same denominator)                                    *)
(******************************************************************************)

Definition leFinProb_num (p1 p2 : FinProb) : Prop :=
  snd p1 = snd p2 /\ leF (fst p1) (fst p2).

(******************************************************************************)
(* HELPER LEMMAS                                                             *)
(******************************************************************************)

Lemma mult_fin_heat_no_budget : forall n m,
  mult_fin_heat n m fz = (fz, fz, fz).
Proof.
  intros n m. destruct m as [|m']; simpl; reflexivity.
Qed.

Lemma add_heat_geq : forall h1 h2, leF h1 (add_heat h1 h2).
Proof.
  intros h1 h2. induction h2 as [|h2' IH].
  - simpl. apply leF_refl.
  - simpl. apply leF_trans with (y := add_heat h1 h2').
    + exact IH.
    + apply leF_step.
Qed.

(* fin_eq_b3 never increases budget *)
Lemma fin_eq_b3_budget_le : forall n m b,
  leF (snd (fst (fin_eq_b3 n m b))) b.
Proof.
  intros n. induction n as [|n' IHn]; intros m b.
  - (* n = fz *)
    destruct b as [|b0].
    + simpl. apply leF_refl.
    + destruct m; simpl; apply leF_step.
  - (* n = fs n' *)
    destruct b as [|b0].
    + simpl. apply leF_refl.
    + destruct m as [|m'].
      * simpl. apply leF_step.
      * simpl.
        destruct (fin_eq_b3 n' m' b0) as [[r0 b0'] h0] eqn:E.
        simpl.
        apply leF_trans with (y := b0).
        -- assert (H := IHn m' b0). rewrite E in H. simpl in H. exact H.
        -- apply leF_step.
Qed.

Opaque fin_eq_b3.

(******************************************************************************)
(* THEOREM 1: HONESTY UNDER EXHAUSTION                                       *)
(******************************************************************************)

Lemma prob_le_b3_no_budget : forall p1 p2,
  fst (fst (prob_le_b3 p1 p2 fz)) = BUnknown.
Proof.
  intros [n1 d1] [n2 d2].
  unfold prob_le_b3.
  rewrite mult_fin_heat_no_budget.
  rewrite mult_fin_heat_no_budget.
  simpl. reflexivity.
Qed.

Theorem activate_no_budget_unknown : forall cell input,
  cell_budget cell = fz ->
  fst (activate cell input) = BUnknown.
Proof.
  intros cell input Hb.
  unfold activate. rewrite Hb.
  destruct (prob_le_b3 (cell_threshold cell) input fz) as [[r b'] h'] eqn:E.
  simpl.
  assert (Hu : fst (fst (prob_le_b3 (cell_threshold cell) input fz)) = BUnknown)
    by apply prob_le_b3_no_budget.
  rewrite E in Hu. simpl in Hu. exact Hu.
Qed.

(******************************************************************************)
(* THEOREM 2: ERODE RESPECTS LOWER BOUNDARY                                  *)
(******************************************************************************)

Theorem erode_at_boundary : forall d b h,
  erode_threshold (mkCell (fs fz, d) (fs b) h) = mkCell (fs fz, d) (fs b) h.
Proof. intros. simpl. reflexivity. Qed.

Theorem erode_never_reaches_zero : forall num den b h,
  num <> fz ->
  fst (cell_threshold (erode_threshold (mkCell (num, den) (fs b) h))) <> fz.
Proof.
  intros num den b h Hnonzero.
  simpl.
  destruct num as [|[|n']].
  - exfalso. apply Hnonzero. reflexivity.
  - simpl. discriminate.
  - simpl. discriminate.
Qed.

(******************************************************************************)
(* THEOREM 3: ERODE DECREASES                                                *)
(******************************************************************************)

Theorem erode_decreases : forall num den b h,
  leFinProb_num
    (cell_threshold (erode_threshold (mkCell (num, den) b h)))
    (num, den).
Proof.
  intros num den b h. unfold erode_threshold. simpl.
  destruct b as [|b'].
  - unfold leFinProb_num. simpl. split; [reflexivity | apply leF_refl].
  - destruct num as [|[|n']].
    + unfold leFinProb_num. simpl. split; [reflexivity | apply leF_refl].
    + unfold leFinProb_num. simpl. split; [reflexivity | apply leF_refl].
    + unfold leFinProb_num. simpl. split; [reflexivity | apply leF_step].
Qed.

Theorem erode_strictly_decreases : forall n' d b' h,
  fst (cell_threshold (erode_threshold (mkCell (fs (fs n'), d) (fs b') h))) = fs n'.
Proof. intros. simpl. reflexivity. Qed.

Theorem erode_preserves_denominator : forall num den b h,
  snd (cell_threshold (erode_threshold (mkCell (num, den) b h))) = den.
Proof.
  intros num den b h. unfold erode_threshold. simpl.
  destruct b as [|b'].
  - reflexivity.
  - destruct num as [|[|n']]; simpl; reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 4: CONSTRICT INCREASES                                            *)
(******************************************************************************)

Theorem constrict_increases : forall num den b h,
  leFinProb_num
    (num, den)
    (cell_threshold (constrict_threshold (mkCell (num, den) b h))).
Proof.
  intros num den b h. unfold constrict_threshold. simpl.
  destruct b as [|b'].
  - unfold leFinProb_num. simpl. split; [reflexivity | apply leF_refl].
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh].
    destruct r.
    + unfold leFinProb_num. simpl. split; [reflexivity | apply leF_refl].
    + unfold leFinProb_num. simpl. split; [reflexivity | apply leF_step].
    + unfold leFinProb_num. simpl. split; [reflexivity | apply leF_refl].
Qed.

Theorem constrict_preserves_denominator : forall num den b h,
  snd (cell_threshold (constrict_threshold (mkCell (num, den) b h))) = den.
Proof.
  intros num den b h. unfold constrict_threshold. simpl.
  destruct b as [|b'].
  - reflexivity.
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh].
    destruct r; reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 5: FROZEN WHEN EXHAUSTED                                          *)
(******************************************************************************)

Theorem erode_frozen : forall p h,
  erode_threshold (mkCell p fz h) = mkCell p fz h.
Proof. intros. simpl. reflexivity. Qed.

Theorem constrict_frozen : forall p h,
  constrict_threshold (mkCell p fz h) = mkCell p fz h.
Proof. intros. simpl. reflexivity. Qed.

(******************************************************************************)
(* THEOREM 6: ERODE COSTS ONE TICK (when it acts)                            *)
(******************************************************************************)

Theorem erode_consumes_one_tick : forall n' d b' h,
  cell_budget (erode_threshold (mkCell (fs (fs n'), d) (fs b') h)) = b'.
Proof. intros. simpl. reflexivity. Qed.

(* At boundary: no cost *)
Theorem erode_at_boundary_free : forall d b h,
  cell_budget (erode_threshold (mkCell (fs fz, d) (fs b) h)) = fs b.
Proof. intros. simpl. reflexivity. Qed.

(******************************************************************************)
(* THEOREM 7: CONSTRICT BUDGET NEVER INCREASES                               *)
(******************************************************************************)

Theorem constrict_budget_nonincreasing : forall num den b h,
  leF (cell_budget (constrict_threshold (mkCell (num, den) b h))) b.
Proof.
  intros num den b h. unfold constrict_threshold. simpl.
  destruct b as [|b'].
  - apply leF_refl.
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh] eqn:Echk.
    assert (Hle : leF b'' b').
    { assert (H := fin_eq_b3_budget_le (fs num) den b').
      rewrite Echk in H. simpl in H. exact H. }
    destruct r; simpl;
    (apply leF_trans with (y := b'); [ exact Hle | apply leF_step ]).
Qed.

(******************************************************************************)
(* THEOREM 8: HEAT MONOTONICITY (second law)                                 *)
(******************************************************************************)

Theorem erode_heat_increases : forall num den b h,
  leF h (cell_heat (erode_threshold (mkCell (num, den) b h))).
Proof.
  intros num den b h. unfold erode_threshold. simpl.
  destruct b as [|b'].
  - apply leF_refl.
  - destruct num as [|[|n']]; simpl.
    + apply leF_refl.
    + apply leF_refl.
    + apply leF_step.
Qed.

Theorem constrict_heat_increases : forall num den b h,
  leF h (cell_heat (constrict_threshold (mkCell (num, den) b h))).
Proof.
  intros num den b h. unfold constrict_threshold. simpl.
  destruct b as [|b'].
  - apply leF_refl.
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh].
    destruct r; simpl;
    (apply leF_trans with (y := add_heat h hh);
    [ apply add_heat_geq | apply leF_step ]).
Qed.

(******************************************************************************)
(* THEOREM 9: VALIDITY PRESERVATION UNDER ERODE                              *)
(******************************************************************************)

Theorem erode_preserves_validity : forall num den b h,
  valid_prob (num, den) ->
  valid_prob (cell_threshold (erode_threshold (mkCell (num, den) b h))).
Proof.
  intros num den b h Hvalid.
  unfold erode_threshold. simpl.
  destruct b as [|b'].
  - exact Hvalid.
  - destruct num as [|[|n']].
    + simpl in Hvalid. destruct Hvalid.
    + exact Hvalid.
    + simpl. simpl in Hvalid.
      apply leF_trans with (y := fs (fs (fs n'))).
      * apply leF_step.
      * exact Hvalid.
Qed.

(******************************************************************************)
(* THEOREM 10: BOUNDED LEARNING                                              *)
(******************************************************************************)

Fixpoint repeat_erode (cell : LearningCell) (fuel : Fin) : LearningCell :=
  match fuel with
  | fz => cell
  | fs fuel' => repeat_erode (erode_threshold cell) fuel'
  end.

Theorem exhausted_stays_frozen : forall p h fuel,
  repeat_erode (mkCell p fz h) fuel = mkCell p fz h.
Proof.
  intros p h fuel. induction fuel as [|fuel' IH].
  - simpl. reflexivity.
  - simpl. destruct p as [num den].
    destruct num as [|[|n']]; simpl; exact IH.
Qed.
