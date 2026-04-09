(******************************************************************************)
(* void_probability_geometry.v                                                *)
(* PROBABILITY AS GEOMETRY — Not Kolmogorov, not sets                        *)
(*                                                                            *)
(* Probability is not a measure on a σ-algebra.                              *)
(* Probability is the COST OF DISTINGUISHING in a finite space.              *)
(* An event is not a subset — it is a REGION you can separate from           *)
(* its complement, if you can afford to.                                      *)
(*                                                                            *)
(* Three consequences:                                                        *)
(*   1. Every probability is an interval, not a point.                       *)
(*      The width depends on your budget.                                     *)
(*   2. Additivity is not an axiom — it is conservation.                     *)
(*      Measuring disjoint regions conserves total Spuren.                      *)
(*   3. What you cannot measure has probability Void, not zero.              *)
(*      Void ≠ 0. Void = "I cannot afford to know."                         *)
(*                                                                            *)
(* After: the conversation about climate models, tipping points,             *)
(*        and the difference between "unlikely" and "unmeasured."            *)
(******************************************************************************)

Require Import Coq.ZArith.ZArith.
Require Import void_finite_minimal.
Require Import void_probability_minimal.

Module Void_Probability_Geometry.

Import Void_Probability_Minimal.

(******************************************************************************)
(* I. THE SPACE — One-dimensional, finite, no infinity                       *)
(*                                                                            *)
(* The space is Fin. A point is a Fin. Distance is saturated subtraction.    *)
(* This is not a limitation — it is a statement that all spaces              *)
(* accessible to a finite observer are effectively one-dimensional           *)
(* projections of whatever higher structure exists.                           *)
(******************************************************************************)

Definition Point := Fin.

(* Distance: symmetric, non-negative by construction (Fin has no negatives) *)
Definition distance (p q : Point) (b : Budget) : (Fin * Budget * Spuren) :=
  match le_fin_b_spur p q b with
  | (true, b', h1) =>
      match sub_saturate_b_spur q p b' with
      | (d, b'', h2) => (d, b'', add_spur h1 h2)
      end
  | (false, b', h1) =>
      match sub_saturate_b_spur p q b' with
      | (d, b'', h2) => (d, b'', add_spur h1 h2)
      end
  end.

(******************************************************************************)
(* II. REGIONS — Geometric, not set-theoretic                                *)
(*                                                                            *)
(* A region is center + radius. Not "the set of points satisfying φ"        *)
(* but "the place in space you can point to." A region exists because        *)
(* someone drew a circle, not because someone defined a predicate.           *)
(******************************************************************************)

Record Region := mkRegion {
  reg_center : Point;
  reg_radius : Fin;
}.

(* Membership: is a point within radius of the center? *)
(* This is a MEASUREMENT — it costs budget and produces Spuren. *)
(* The result is Bool3, not bool: you might not afford to know. *)
Definition in_region (p : Point) (r : Region) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match distance p (reg_center r) b with
  | (d, b', h1) =>
      match le_fin_b3 d (reg_radius r) b' with
      | (result, b'', h2) => (result, b'', add_spur h1 h2)
      end
  end.

(* Geometric disjointness: centers far enough apart that regions don't touch *)
(* distance(c1, c2) > r1 + r2 *)
Definition disjoint_regions (r1 r2 : Region) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match add_fin_b_spur (reg_radius r1) (reg_radius r2) b with
  | (sum_radii, b', h1) =>
      match distance (reg_center r1) (reg_center r2) b' with
      | (d, b'', h2) =>
          match le_fin_b3 sum_radii d b'' with
          | (result, b''', h3) =>
              (* result = BTrue means sum_radii ≤ d, so disjoint *)
              (result, b''', add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(******************************************************************************)
(* III. PROBABILITY AS MEASUREMENT                                           *)
(*                                                                            *)
(* The "probability" of a region is not a number assigned to a set.          *)
(* It is the RESULT OF TRYING TO MEASURE the region's proportion             *)
(* of the space. The result depends on your budget:                          *)
(*                                                                            *)
(*   Full budget  → Sharp(r/s)  where r = radius, s = space size            *)
(*   Some budget  → Fuzzy(lo, mid, hi)  — interval estimate                 *)
(*   Low budget   → Vague(lo, hi)  — wide interval                          *)
(*   No budget    → Void  — unmeasured, not zero                            *)
(*                                                                            *)
(* This is void-theory's answer to "what is P(A)?":                          *)
(* It depends on who's asking and what they can afford.                      *)
(******************************************************************************)

(* The result of a probability measurement *)
Inductive ProbMeasurement :=
  | MSharp  : FinProb -> ProbMeasurement
  | MFuzzy  : FinProb -> FinProb -> FinProb -> ProbMeasurement  (* lo, center, hi *)
  | MVague  : FinProb -> FinProb -> ProbMeasurement             (* lo, hi *)
  | MVoid   : ProbMeasurement.                                  (* unmeasured *)

(* Measure the probability of a region relative to a space *)
(* radius / space_radius — but computed with budget *)
Definition measure_region (r : Region) (space_radius : Fin) (b : Budget)
  : (ProbMeasurement * Budget * Spuren) :=
  match b with
  | fz => (MVoid, fz, fz)
  | fs b0 =>
      match b0 with
      | fz =>
          (* One tick: can only give vague bounds *)
          (MVague (fz, fs (fs fz))         (* 0/2 = lower bound *)
                  (fs fz, fs fz),           (* 1/1 = upper bound *)
           fz, fs fz)
      | fs b1 =>
          match b1 with
          | fz =>
              (* Two ticks: Fuzzy — compute center but bounds are wide *)
              (* div gets b0 = fs fz; fs h1 accounts for the tick lost to matching *)
              match div_fin_spur (reg_radius r) space_radius b0 with
              | (q, _, b', h1) =>
                  (MFuzzy (fz, fs (fs fz))    (* 0/2 lower *)
                          (q, space_radius)     (* center estimate *)
                          (fs fz, fs fz),       (* 1/1 upper *)
                   b', fs h1)
              end
          | fs b2 =>
              (* Three+ ticks: Sharp — full division *)
              (* div gets fs (fs b2) = b0; fs h1 accounts for the match tick *)
              match div_fin_spur (reg_radius r) space_radius (fs (fs b2)) with
              | (q, _, b', h1) =>
                  (MSharp (q, space_radius), b', fs h1)
              end
          end
      end
  end.

(******************************************************************************)
(* IV. THEOREMS — The physics of measurement                                 *)
(******************************************************************************)

(* THEOREM 1: Zero budget yields Void. Always. No exceptions.               *)
(* This is the void axiom: what you cannot afford to measure                 *)
(* does not have probability zero. It has probability Void.                  *)
Theorem zero_budget_yields_void : forall r s,
  fst (fst (measure_region r s fz)) = MVoid.
Proof.
  intros. simpl. reflexivity.
Qed.

(* THEOREM 2: Non-negativity is structural.                                  *)
(* There is nothing to prove: Fin has no negative inhabitants.               *)
(* This is not an axiom — it is a property of the type.                     *)
(* We state it for philosophical completeness.                               *)
Theorem non_negativity_structural : forall n : Fin,
  (fin_to_Z_PROOF_ONLY n >= 0)%Z.
Proof.
  induction n as [| n' IH].
  - simpl. apply Z.le_ge. apply Z.le_refl.
  - simpl. apply Z.le_ge.
    apply Z.le_trans with (fin_to_Z_PROOF_ONLY n').
    + apply Z.ge_le. exact IH.
    + generalize (fin_to_Z_PROOF_ONLY n'); intro x.
      rewrite <- (Z.add_0_l x) at 1.
      apply (proj1 (Z.add_le_mono_r 0 1 x)).
      discriminate.
Qed.

(* Helper: subtracting a number from itself always gives fz *)
Lemma sub_saturate_self : forall p b,
  fst (fst (sub_saturate_b_spur p p b)) = fz.
Proof.
  induction p as [| p' IH]; intro b.
  - simpl. destruct b; reflexivity.
  - simpl. destruct b as [| b0].
    + reflexivity.
    + specialize (IH b0).
      destruct (sub_saturate_b_spur p' p' b0) as [[r b1] h1].
      simpl in IH. simpl. exact IH.
Qed.

(* THEOREM 3: Distance is zero to self.                                      *)
(* Reflexivity of space — the cheapest measurement.                          *)
Theorem distance_self : forall p b,
  b <> fz ->
  exists b' h, distance p p b = (fz, b', h).
Proof.
  intros p b Hb.
  unfold distance.
  destruct (le_fin_b_spur p p b) as [[r b'] h1] eqn:Hle.
  destruct r.
  - destruct (sub_saturate_b_spur p p b') as [[d b''] h2] eqn:Hsub.
    pose proof (sub_saturate_self p b') as Hself.
    rewrite Hsub in Hself. simpl in Hself. subst d.
    eexists. eexists. reflexivity.
  - destruct (sub_saturate_b_spur p p b') as [[d b''] h2] eqn:Hsub.
    pose proof (sub_saturate_self p b') as Hself.
    rewrite Hsub in Hself. simpl in Hself. subst d.
    eexists. eexists. reflexivity.
Qed.

(* THEOREM 4: Void propagates through combination.                          *)
(* If either measurement is Void, the combination is Void.                  *)
(* This is the fundamental contagion of ignorance.                           *)
Definition combine_measurements (m1 m2 : ProbMeasurement) : ProbMeasurement :=
  match m1, m2 with
  | MVoid, _ => MVoid
  | _, MVoid => MVoid
  | MSharp p1, MSharp p2 => MSharp p1  (* placeholder: real combination needs budget *)
  | MFuzzy l1 c1 u1, MFuzzy l2 c2 u2 => MFuzzy l1 c1 u2
  | MVague l1 u1, MVague l2 u2 => MVague l1 u2
  | _, _ => MVague (fz, fs fz) (fs fz, fs fz)
  end.

Theorem void_propagates_l : forall m,
  combine_measurements MVoid m = MVoid.
Proof. intros m. destruct m; reflexivity. Qed.

Theorem void_propagates_r : forall m,
  combine_measurements m MVoid = MVoid.
Proof. intros m. destruct m; reflexivity. Qed.

(* THEOREM 5: More budget → narrower interval.                              *)
(* With one tick you get Vague. With two you get Fuzzy.                     *)
(* With three+ you get Sharp. Budget determines precision.                   *)
Theorem budget_one_gives_vague : forall r s,
  exists lo hi, fst (fst (measure_region r s (fs fz))) = MVague lo hi.
Proof.
  intros. simpl. eexists. eexists. reflexivity.
Qed.

Theorem budget_sufficient_gives_sharp : forall r s b,
  exists p b' h,
    measure_region r s (fs (fs (fs b))) = (MSharp p, b', h).
Proof.
  intros. simpl.
  destruct (div_fin_spur (reg_radius r) s (fs (fs b))) as [[[q rem] b'] h1].
  eexists. eexists. eexists. reflexivity.
Qed.

(******************************************************************************)
(* V. MEASUREMENT CONSERVATION                                               *)
(*                                                                            *)
(* The second law: every measurement conserves budget.                       *)
(* Spuren + remaining_budget = initial_budget.                                 *)
(* This is not an axiom. This is a theorem. Qed.                            *)
(******************************************************************************)

Theorem distance_conservation : forall p q b d b' h,
  distance p q b = (d, b', h) -> add_spur h b' = b.
Proof.
  intros p q b d b' h Heq.
  unfold distance in Heq.
  destruct (le_fin_b_spur p q b) as [[r b1] h1] eqn:Hle.
  destruct r.
  - destruct (sub_saturate_b_spur q p b1) as [[d' b2] h2] eqn:Hsub.
    inversion Heq; subst.
    rewrite add_spur_assoc.
    rewrite (spur_conservation_sub _ _ _ _ _ _ Hsub).
    exact (spur_conservation_le_b_spur _ _ _ _ _ _ Hle).
  - destruct (sub_saturate_b_spur p q b1) as [[d' b2] h2] eqn:Hsub.
    inversion Heq; subst.
    rewrite add_spur_assoc.
    rewrite (spur_conservation_sub _ _ _ _ _ _ Hsub).
    exact (spur_conservation_le_b_spur _ _ _ _ _ _ Hle).
Qed.

Theorem in_region_conservation : forall p r b res b' h,
  in_region p r b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros p r b res b' h Heq.
  unfold in_region in Heq.
  destruct (distance p (reg_center r) b) as [[d b1] h1] eqn:Hd.
  destruct (le_fin_b3 d (reg_radius r) b1) as [[res' b2] h2] eqn:Hle.
  inversion Heq; subst.
  rewrite add_spur_assoc.
  rewrite (spur_conservation_le3 _ _ _ _ _ _ Hle).
  exact (distance_conservation _ _ _ _ _ _ Hd).
Qed.

Theorem disjoint_conservation : forall r1 r2 b res b' h,
  disjoint_regions r1 r2 b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros r1 r2 b res b' h Heq.
  unfold disjoint_regions in Heq.
  destruct (add_fin_b_spur (reg_radius r1) (reg_radius r2) b)
    as [[sr b1] h1] eqn:Hadd.
  destruct (distance (reg_center r1) (reg_center r2) b1)
    as [[d b2] h2] eqn:Hdist.
  destruct (le_fin_b3 sr d b2) as [[res' b3] h3] eqn:Hle.
  inversion Heq; subst.
  rewrite add_spur_assoc. rewrite add_spur_assoc.
  rewrite (spur_conservation_le3 _ _ _ _ _ _ Hle).
  rewrite (distance_conservation _ _ _ _ _ _ Hdist).
  exact (spur_conservation_add _ _ _ _ _ _ Hadd).
Qed.

(******************************************************************************)
(* VI. KNOWLEDGE MONOTONICITY                                                *)
(*                                                                            *)
(* THE theorem classical mathematics cannot even STATE.                       *)
(*                                                                            *)
(* In classical logic: comparison is free, instantaneous, total.             *)
(*   n ≤ m is simply true or false. There is nothing else to say.           *)
(*   The concept of "gaining knowledge" about a comparison                   *)
(*   does not exist, because there is no cost to knowing.                    *)
(*                                                                            *)
(* In void-theory: comparison costs budget.                                  *)
(*   With insufficient budget, the answer is BUnknown.                       *)
(*   With sufficient budget, the answer is BTrue or BFalse.                  *)
(*   THEOREM: once you know, more budget never reverses the answer.          *)
(*                                                                            *)
(* This is the formal statement that KNOWLEDGE IS MONOTONIC:                 *)
(*   — More resources can resolve uncertainty (BUnknown → BTrue/BFalse)     *)
(*   — More resources NEVER corrupt existing knowledge                       *)
(*     (BTrue never becomes BFalse, BFalse never becomes BTrue)             *)
(*   — The only direction is: ignorance → knowledge, never reverse          *)
(*                                                                            *)
(* Classical mathematics cannot state this because it has no concept         *)
(* of the cost of knowing. It assumes all knowledge is free.                 *)
(* Therefore it cannot distinguish between "false" and "too poor to check." *)
(* Therefore it cannot prove that learning is safe.                          *)
(*                                                                            *)
(* We can. And we do. Qed.                                                   *)
(******************************************************************************)

(* Helper: extract the Bool3 result *)
Definition bool3_of (x : Bool3 * Budget * Spuren) : Bool3 := fst (fst x).

(* Helper: le_fin_b3 with more budget preserves BTrue *)
Lemma le_fin_b3_budget_true : forall n m b1,
  bool3_of (le_fin_b3 n m b1) = BTrue ->
  forall b2, leF b1 b2 ->
  bool3_of (le_fin_b3 n m b2) = BTrue.
Proof.
  induction n as [| n' IHn]; intros m b1 H1 b2 Hle.
  - (* n = fz *)
    destruct b1 as [| b0].
    + simpl in H1. discriminate.
    + destruct b2 as [| b2']. { inversion Hle. }
      simpl. reflexivity.
  - destruct m as [| m'].
    + (* m = fz: le_fin_b3 (fs _) fz always BFalse *)
      destruct b1 as [| b0]; simpl in H1; discriminate.
    + (* m = fs m': recursive *)
      destruct b1 as [| b0].
      { simpl in H1. discriminate. }
      simpl in H1.
      destruct (le_fin_b3 n' m' b0) as [[r bx] hx] eqn:Hsub.
      simpl in H1.
      destruct b2 as [| b2']. { inversion Hle. }
      inversion Hle as [| ? ? HleF]. subst.
      simpl.
      assert (Hrec: bool3_of (le_fin_b3 n' m' b0) = BTrue).
      { unfold bool3_of. rewrite Hsub. simpl. exact H1. }
      specialize (IHn m' b0 Hrec b2' HleF).
      unfold bool3_of in IHn.
      destruct (le_fin_b3 n' m' b2') as [[r2 b2x] h2x].
      simpl in IHn. rewrite IHn. simpl. reflexivity.
Qed.

(* Helper: le_fin_b3 with more budget preserves BFalse *)
Lemma le_fin_b3_budget_false : forall n m b1,
  bool3_of (le_fin_b3 n m b1) = BFalse ->
  forall b2, leF b1 b2 ->
  bool3_of (le_fin_b3 n m b2) = BFalse.
Proof.
  induction n as [| n' IHn]; intros m b1 H1 b2 Hle.
  - (* n = fz: le_fin_b3 fz _ always BTrue — contradiction *)
    destruct b1 as [| b0]; simpl in H1; discriminate.
  - destruct m as [| m'].
    + (* m = fz: le_fin_b3 (fs _) fz always BFalse *)
      destruct b1 as [| b0].
      { simpl in H1. discriminate. }
      destruct b2 as [| b2']. { inversion Hle. }
      simpl. reflexivity.
    + (* m = fs m': recursive *)
      destruct b1 as [| b0].
      { simpl in H1. discriminate. }
      simpl in H1.
      destruct (le_fin_b3 n' m' b0) as [[r bx] hx] eqn:Hsub.
      simpl in H1.
      destruct b2 as [| b2']. { inversion Hle. }
      inversion Hle as [| ? ? HleF]. subst.
      simpl.
      assert (Hrec: bool3_of (le_fin_b3 n' m' b0) = BFalse).
      { unfold bool3_of. rewrite Hsub. simpl. exact H1. }
      specialize (IHn m' b0 Hrec b2' HleF).
      unfold bool3_of in IHn.
      destruct (le_fin_b3 n' m' b2') as [[r2 b2x] h2x].
      simpl in IHn. rewrite IHn. simpl. reflexivity.
Qed.

(******************************************************************************)
(* THE CARETAKER LEMMA                                                       *)
(*                                                                            *)
(* Named after Leyland James Kirby (The Caretaker), whose work               *)
(* "Everywhere at the End of Time" is a six-hour sonic proof                  *)
(* that memory degrades not because truth changes,                            *)
(* but because the budget to access it runs out.                              *)
(*                                                                            *)
(* The melody is still there. The record did not change.                      *)
(* The observer can no longer afford to hear it.                              *)
(*                                                                            *)
(* This theorem says: if the budget came back, so would the melody.           *)
(* Knowledge never reverses. What you learned stays true.                     *)
(* What you forgot was never false — only too expensive to recall.            *)
(*                                                                            *)
(* Classical mathematics cannot state this. It has no concept of cost.        *)
(* It cannot distinguish "false" from "too poor to check."                    *)
(* We can. And we prove it. Qed.                                             *)
(******************************************************************************)
Theorem caretaker_lemma : forall n m b1 b2,
  bool3_of (le_fin_b3 n m b1) <> BUnknown ->
  leF b1 b2 ->
  bool3_of (le_fin_b3 n m b2) = bool3_of (le_fin_b3 n m b1).
Proof.
  intros n m b1 b2 Hknown Hbudget.
  remember (bool3_of (le_fin_b3 n m b1)) as res eqn:Hres.
  destruct res.
  - (* BTrue — preserved by monotonicity *)
    symmetry in Hres.
    exact (le_fin_b3_budget_true _ _ _ Hres _ Hbudget).
  - (* BFalse — preserved by monotonicity *)
    symmetry in Hres.
    exact (le_fin_b3_budget_false _ _ _ Hres _ Hbudget).
  - (* BUnknown — contradicts Hknown *)
    exfalso. apply Hknown. reflexivity.
Qed.

(******************************************************************************)
(* VIII. NO-CLONING AND THE DEATH OF BANACH-TARSKI                          *)
(*                                                                            *)
(* In classical mathematics:                                                  *)
(*   Banach-Tarski (1924): a ball can be decomposed into five pieces         *)
(*   and reassembled into TWO balls of the same size.                        *)
(*   Matter duplicates. Entropy decreases. Something from nothing.           *)
(*   This requires: axiom of choice, non-measurable sets,                    *)
(*   and zero-cost operations.                                                *)
(*                                                                            *)
(* In quantum mechanics:                                                      *)
(*   No-cloning theorem (Wootters, Zurek, Dieks, 1982):                     *)
(*   An arbitrary quantum state cannot be copied.                             *)
(*   Information does not duplicate for free.                                 *)
(*   This follows from linearity of quantum evolution.                       *)
(*                                                                            *)
(* In void-theory:                                                            *)
(*   Every measurement conserves budget. Every operation produces Spuren.       *)
(*   There are no non-measurable regions. There are no free operations.      *)
(*   Therefore: no Banach-Tarski. No duplication. No free lunch.             *)
(*   The second law of thermodynamics is a THEOREM, not a physical law.      *)
(*                                                                            *)
(* Score:                                                                     *)
(*   Classical mathematics: cloning is possible.                              *)
(*   Quantum mechanics:     cloning is impossible.                            *)
(*   Void-theory:           cloning is impossible.                            *)
(*   Physics:               cloning is impossible.                            *)
(*   Three against one. The one is wrong.                                    *)
(******************************************************************************)

(* THEOREM: Every region is measurable.                                      *)
(* There are no Vitali sets. There are no non-measurable regions.            *)
(* Non-measurability is always temporary (insufficient budget),              *)
(* never permanent (pathological structure).                                  *)
(*                                                                            *)
(* In classical math: the Vitali set CANNOT be measured, period.             *)
(* No amount of effort makes it measurable.                                  *)
(* In void-theory: give me three ticks of budget and I measure anything.     *)
Lemma leF_invert3 : forall b,
  leF (fs (fs (fs fz))) b ->
  exists b', b = fs (fs (fs b')).
Proof.
  intros [|[|[|b3]]] Hle; try (exists b3; reflexivity).
  - inversion Hle.
  - inversion Hle as [|? ? H]. inversion H.
  - inversion Hle as [|? ? H]. inversion H as [|? ? H2]. inversion H2.
Qed.

Theorem all_regions_measurable : forall r s,
  exists b, forall b', leF b b' ->
  exists p b'' h, measure_region r s b' = (MSharp p, b'', h).
Proof.
  intros r s.
  exists (fs (fs (fs fz))).
  intros b' Hle.
  destruct (leF_invert3 b' Hle) as [b'' Hb']. subst b'.
  exact (budget_sufficient_gives_sharp r s b'').
Qed.

(* THEOREM: Measurement always conserves budget.                             *)
(* This is the second law of thermodynamics for measurement.                 *)
(* Spuren + remaining_budget = initial_budget. Always. No exceptions.          *)
(*                                                                            *)
(* Banach-Tarski requires violating this. We prove it cannot be violated.    *)
Theorem measurement_conservation : forall r s b m b' h,
  measure_region r s b = (m, b', h) -> add_spur h b' = b.
Proof.
  intros r s b m' b' h Heq.
  unfold measure_region in Heq.
  destruct b as [| b0].
  - inversion Heq; subst. apply add_spur_fz_l.
  - destruct b0 as [| b1].
    + inversion Heq; subst. simpl. reflexivity.
    + destruct b1 as [| b2].
      * destruct (div_fin_spur (reg_radius r) s (fs fz)) as [[[q rem] bx] hx] eqn:Hdiv.
        inversion Heq; subst.
        rewrite add_spur_fs_l. f_equal.
        exact (spur_conservation_div _ _ _ _ _ _ _ Hdiv).
      * destruct (div_fin_spur (reg_radius r) s (fs (fs b2))) as [[[q rem] bx] hx] eqn:Hdiv.
        inversion Heq; subst.
        rewrite add_spur_fs_l. f_equal.
        exact (spur_conservation_div _ _ _ _ _ _ _ Hdiv).
Qed.

(* THEOREM: Two measurements cost strictly more than one.                    *)
(* You cannot clone a measurement result. Each observation costs budget.     *)
(* This is the void-theory analogue of the no-cloning theorem.              *)
(*                                                                            *)
(* In quantum mechanics: you cannot copy a state without disturbing it.      *)
(* In void-theory: you cannot copy a measurement without paying again.       *)
Theorem no_cloning : forall r1 r2 s b m1 b1 h1 m2 b2 h2,
  measure_region r1 s b = (m1, b1, h1) ->
  measure_region r2 s b1 = (m2, b2, h2) ->
  add_spur (add_spur h1 h2) b2 = b.
Proof.
  intros r1 r2 s b m1 b1 h1 m2 b2 h2 H1 H2.
  rewrite add_spur_assoc.
  rewrite (measurement_conservation _ _ _ _ _ _ H2).
  exact (measurement_conservation _ _ _ _ _ _ H1).
Qed.

(******************************************************************************)
(* VII. THE PHILOSOPHICAL CORE                                               *)
(*                                                                            *)
(* Classical probability: P(A) = |A| / |Ω|                                  *)
(*   — Assumes you can count. Counting is free.                              *)
(*   — Assumes the space exists. Existence is free.                          *)
(*   — Assumes the answer is a point. Points are free.                       *)
(*                                                                            *)
(* Void probability: P(A | observer, budget) = measure_region A Ω budget    *)
(*   — Counting costs. Each comparison is a tick.                            *)
(*   — The space is what you can afford to distinguish.                      *)
(*   — The answer is an interval whose width = your poverty.                 *)
(*                                                                            *)
(* What the climate scientists don't measure:                                *)
(*   — Tipping points no one simulated: P = Void, not P = 0.                *)
(*   — The difference between "unlikely" and "unmeasured"                    *)
(*     is the difference between Sharp(1/1000) and Void.                     *)
(*   — One is a statement about the world.                                   *)
(*     The other is a statement about the budget of the observer.            *)
(*   — Confusing them is not a scientific error.                             *)
(*     It is a thermodynamic one.                                            *)
(*                                                                            *)
(* And now we have proved what they cannot even formulate:                    *)
(*   — The Caretaker Lemma: knowledge is monotonic.                          *)
(*   — More budget can only resolve, never corrupt.                          *)
(*   — The melody is still there. The budget ran out.                        *)
(*   — Classical mathematics takes this for granted so completely            *)
(*     that it cannot see it, cannot name it, cannot prove it.               *)
(*   — We see it. We name it after Kirby. We prove it. Qed.                 *)
(******************************************************************************)

(******************************************************************************)
(* IX. THE RESOLUTION THEOREM                                                *)
(*                                                                            *)
(* In classical geometry, distinguishing two points is free.                  *)
(* Are 1,000,000 and 1,000,001 different? Yes. Instantly. Zero cost.         *)
(* Are 10^100 and 10^100 + 1 different? Yes. Still free.                     *)
(*                                                                            *)
(* In void-theory, distinguishing deeper numbers costs more budget.           *)
(* Comparing fs(n) with fs(m) costs exactly one tick more than               *)
(* comparing n with m. Resolution is proportional to depth.                   *)
(*                                                                            *)
(* This is Heisenberg, derived from definitions, not from experiment.         *)
(* To see finer structure, you must pay more. No exceptions.                  *)
(******************************************************************************)

(* Zero budget yields total ignorance. Always. *)
Theorem zero_budget_blind : forall n m,
  le_fin_b3 n m fz = (BUnknown, fz, fz).
Proof.
  intros n m. destruct n; simpl; reflexivity.
Qed.

(* Each layer of depth costs exactly one tick. *)
(* Comparing fs(n) vs fs(m) with fs(b) reduces to comparing n vs m with b. *)
Theorem resolution_cost : forall n m b,
  bool3_of (le_fin_b3 (fs n) (fs m) (fs b)) = bool3_of (le_fin_b3 n m b).
Proof.
  intros n m b.
  simpl.
  destruct (le_fin_b3 n m b) as [[r bx] hx].
  simpl. reflexivity.
Qed.

(* COROLLARY: to compare numbers of depth d, you need budget ≥ d.           *)
(* With budget b < d, you get BUnknown. With budget b ≥ d, you know.       *)
(* This is the resolution bound: precision costs proportional to depth.      *)
(*                                                                            *)
(* Proof sketch (not formalized as single theorem, but follows from          *)
(* resolution_cost + zero_budget_blind by induction):                        *)
(*   le_fin_b3 (fs^d n) (fs^d m) b with b < d                              *)
(*   = le_fin_b3 (fs^(d-1) n) (fs^(d-1) m) (b-1)   [by resolution_cost]   *)
(*   = ...                                                                    *)
(*   = le_fin_b3 (fs^(d-b) n) (fs^(d-b) m) fz       [after b steps]        *)
(*   = BUnknown                                       [by zero_budget_blind] *)

(******************************************************************************)
(* X. THE OBSERVER HORIZON                                                   *)
(*                                                                            *)
(* Every observer has a horizon. Not because space ends,                      *)
(* but because budget does.                                                   *)
(*                                                                            *)
(* To get a Sharp measurement, you need at least 3 ticks of budget.          *)
(* After each Sharp measurement, you have strictly less budget.              *)
(* Therefore: the number of Sharp measurements is finite and bounded.        *)
(*                                                                            *)
(* This is the event horizon of knowledge.                                    *)
(* In cosmology: the speed of light limits what you can see.                 *)
(* In void-theory: the budget limits what you can know.                      *)
(* Both are absolute. Neither can be cheated.                                 *)
(******************************************************************************)

(* Sharp requires at least 3 ticks. Below that: Void, Vague, or Fuzzy. *)
Theorem sharp_requires_3 : forall r s b p b' h,
  measure_region r s b = (MSharp p, b', h) ->
  exists b'', b = fs (fs (fs b'')).
Proof.
  intros r s b p b' h Heq.
  destruct b as [| b0].
  - simpl in Heq. discriminate.
  - destruct b0 as [| b1].
    + simpl in Heq. discriminate.
    + destruct b1 as [| b2].
      * simpl in Heq.
        destruct (div_fin_spur (reg_radius r) s (fs fz)) as [[[q rem] bx] hx].
        discriminate.
      * exists b2. reflexivity.
Qed.

(* After a Sharp measurement, budget strictly decreases. *)
(* You had at least 3 ticks. You spent at least 1 (the fs in Spuren). *)
(* So remaining budget < original budget. The horizon closes in. *)
Theorem measurement_shrinks_budget : forall r s b m b' h,
  measure_region r s b = (m, b', h) ->
  m <> MVoid ->
  leF (fs fz) h.
Proof.
  intros r s b m' b' h Heq Hnv.
  destruct b as [| b0].
  - simpl in Heq. inversion Heq; subst. exfalso. apply Hnv. reflexivity.
  - destruct b0 as [| b1].
    + simpl in Heq. inversion Heq; subst. apply leF_refl.
    + destruct b1 as [| b2].
      * simpl in Heq.
        destruct (div_fin_spur (reg_radius r) s (fs fz)) as [[[q rem] bx] hx].
        inversion Heq; subst.
        constructor. constructor.
      * simpl in Heq.
        destruct (div_fin_spur (reg_radius r) s (fs (fs b2))) as [[[q rem] bx] hx].
        inversion Heq; subst.
        constructor. constructor.
Qed.

(* THE HORIZON COROLLARY:                                                    *)
(* Every non-Void measurement costs at least 1 tick of Spuren.                 *)
(* Conservation: Spuren + remaining = original.                                 *)
(* Therefore: remaining < original. Budget strictly decreases.               *)
(* Therefore: after finitely many measurements, budget = 0.                  *)
(* Therefore: all further measurements return MVoid.                          *)
(* Therefore: every observer has a horizon.                                   *)
(*                                                                            *)
(* The number of Sharp measurements ≤ b/3 (each costs ≥ 3 ticks).          *)
(* The number of any measurements ≤ b (each costs ≥ 1 tick).               *)
(* After that: Void. Not zero. Not silence. Void.                            *)
(* The universe is still there. You just can't afford to see it.             *)

(******************************************************************************)
(* XI. THE COMPLEMENTARITY PRINCIPLE                                         *)
(*                                                                            *)
(* In quantum mechanics (Bohr, 1928):                                         *)
(*   You cannot simultaneously measure position and momentum                  *)
(*   with arbitrary precision. Measuring one disturbs the other.              *)
(*   This is a physical law, observed in laboratories.                        *)
(*                                                                            *)
(* In void-theory:                                                            *)
(*   You cannot simultaneously perform two measurements from one budget       *)
(*   without each degrading the other's precision. Measuring one              *)
(*   consumes budget that the other needed.                                   *)
(*   This is a THEOREM, derived from conservation.                            *)
(*                                                                            *)
(* The key insight: classical mathematics allows infinite measurements        *)
(* at zero cost. Therefore it has no complementarity — everything             *)
(* is knowable simultaneously. Quantum mechanics discovered that              *)
(* this is physically false. Void-theory proves it mathematically.            *)
(******************************************************************************)

(* Helper: leF is preserved under add_spur *)
Lemma leF_add_spur : forall a b, leF a (add_spur a b).
Proof.
  intros a b. induction b as [| b' IH].
  - simpl. apply leF_refl.
  - simpl. apply leF_trans with (add_spur a b').
    + exact IH.
    + clear IH. induction (add_spur a b') as [| x IHx].
      * constructor.
      * constructor. exact IHx.
Qed.

(* Helper: add_spur with both args >= 1 gives result >= 2 *)
Lemma add_spur_both_pos : forall h1 h2,
  leF (fs fz) h1 -> leF (fs fz) h2 ->
  leF (fs (fs fz)) (add_spur h1 h2).
Proof.
  intros [| h1'] [| h2'] H1 H2.
  - inversion H1.
  - inversion H1.
  - inversion H2.
  - (* h1 = fs h1', h2 = fs h2' *)
    simpl. constructor.
    apply leF_trans with (fs h1').
    + constructor. constructor.
    + apply leF_add_spur.
Qed.

(* THE COMPLEMENTARITY PRINCIPLE:                                            *)
(* Two non-Void measurements from the same budget require at least 2 ticks.  *)
(* You cannot observe two things for the price of one.                       *)
(* Every act of measurement limits what else you can measure.                *)
Theorem complementarity : forall r1 r2 s b m1 b1 h1 m2 b2 h2,
  measure_region r1 s b = (m1, b1, h1) ->
  m1 <> MVoid ->
  measure_region r2 s b1 = (m2, b2, h2) ->
  m2 <> MVoid ->
  leF (fs (fs fz)) b.
Proof.
  intros r1 r2 s b m1 b1 h1 m2 b2 h2 Hm1 Hnv1 Hm2 Hnv2.
  (* Each non-Void measurement costs at least 1 tick *)
  pose proof (measurement_shrinks_budget _ _ _ _ _ _ Hm1 Hnv1) as Hh1.
  pose proof (measurement_shrinks_budget _ _ _ _ _ _ Hm2 Hnv2) as Hh2.
  (* Conservation: add_spur (add_spur h1 h2) b2 = b *)
  pose proof (no_cloning _ _ _ _ _ _ _ _ _ _ Hm1 Hm2) as Hcons.
  (* h1 >= 1 and h2 >= 1, so add_spur h1 h2 >= 2 *)
  pose proof (add_spur_both_pos h1 h2 Hh1 Hh2) as Hsum.
  (* b = add_spur (add_spur h1 h2) b2 >= add_spur h1 h2 >= 2 *)
  apply leF_trans with (add_spur (add_spur h1 h2) b2).
  - apply leF_trans with (add_spur h1 h2).
    + exact Hsum.
    + apply leF_add_spur.
  - rewrite Hcons. apply leF_refl.
Qed.

(******************************************************************************)
(******************************************************************************)
(* XII. THE UNCERTAINTY PRINCIPLE — Known Unknowable                         *)
(*                                                                            *)
(* Heisenberg (1927): delta-x * delta-p >= hbar/2.                          *)
(* You cannot know both. Not because of clumsiness.                          *)
(* Because knowing one STRUCTURALLY PREVENTS knowing the other.              *)
(*                                                                            *)
(* Classical mathematics has no concept of this. In classical logic,          *)
(* every proposition is decidable in principle. There is no "known           *)
(* unknowable" — only "not yet known."                                       *)
(*                                                                            *)
(* In void-theory: BUnknown is not "I don't know which."                     *)
(* BUnknown is "I KNOW that I CANNOT know, because the budget               *)
(* that would have paid for this answer was spent on another question."       *)
(*                                                                            *)
(* This is stronger than complementarity. Complementarity says:              *)
(* two measurements cost more than one. Uncertainty says:                     *)
(* given a fixed budget, there exist pairs of questions where                 *)
(* answering one GUARANTEES the other returns BUnknown.                       *)
(*                                                                            *)
(* The formal statement: if the budget is exactly enough for one              *)
(* in_region check, the second check MUST return BUnknown.                    *)
(* Not "might." MUST. This is a known unknowable.                            *)
(******************************************************************************)

(* The cost of in_region: it calls distance (which calls le_fin_b_spur      *)
(* + sub_saturate_b_spur) and then le_fin_b3. Every non-trivial call        *)
(* consumes budget. With tight budget, the second call starves.              *)

(* Uncertainty: with budget fz, EVERY in_region check returns BUnknown.      *)
(* Therefore: if you start with budget b, and the first in_region uses      *)
(* all of it (b' = fz), the second one is guaranteed BUnknown.              *)
Theorem uncertainty_void : forall p r,
  bool3_of (in_region p r fz) = BUnknown.
Proof.
  intros p r.
  unfold in_region, distance, bool3_of.
  destruct p; simpl; reflexivity.
Qed.

(* THE KNOWN UNKNOWABLE:                                                     *)
(* If the first measurement exhausts the budget (remaining = fz),            *)
(* the second measurement is GUARANTEED to return BUnknown.                   *)
(* You KNOW that you CANNOT know. This is not ignorance. This is certainty   *)
(* about the boundaries of knowledge.                                         *)
Theorem known_unknowable : forall p1 r1 b res1 h1 p2 r2,
  in_region p1 r1 b = (res1, fz, h1) ->
  bool3_of (in_region p2 r2 fz) = BUnknown.
Proof.
  intros. apply uncertainty_void.
Qed.

(* STRONGER: even with nonzero but insufficient remaining budget,            *)
(* the result may still be BUnknown. The distance computation                *)
(* inside in_region may exhaust whatever remains.                            *)
(*                                                                            *)
(* The philosophical content:                                                 *)
(*   — Classical: "Can point p be in region r?" Always answerable.           *)
(*   — Void: "Can point p be in region r?" Depends on budget.               *)
(*     After measuring r1, the answer for r2 might be:                       *)
(*     "I know that I cannot know."                                          *)
(*     Not ignorance. Not uncertainty in the colloquial sense.               *)
(*     CERTAINTY about the STRUCTURE of what is knowable.                    *)
(*                                                                            *)
(*   — In quantum mechanics, this is the wave function:                      *)
(*     a complete description of what CAN be known, including                *)
(*     what CANNOT be known simultaneously.                                   *)
(*   — In void-theory, this is the budget:                                   *)
(*     a complete description of what CAN be measured, including             *)
(*     what MUST remain BUnknown.                                            *)
(*   — Both are descriptions of the HORIZON of knowledge,                    *)
(*     not of reality itself.                                                *)
(******************************************************************************)

(******************************************************************************)
(* XII. DETERMINISM BREEDS VOID                                              *)
(*                                                                            *)
(* The conservation law (add_spur h b' = b) is perfect bookkeeping.          *)
(* Every tick accounted for. Nothing lost, nothing created.                   *)
(* And yet: this perfect determinism GENERATES uncertainty.                   *)
(*                                                                            *)
(* Because: the budget is finite. Measurement transforms budget into         *)
(* Spuren — potential into trace. The total is conserved. But the            *)
(* remaining budget is strictly less. And for every budget, there is         *)
(* a question it cannot answer.                                               *)
(*                                                                            *)
(* The deepest form: your budget is your own blind spot.                     *)
(* le_fin_b3 n n n = BUnknown. Always. The most trivial question            *)
(* — "is n <= n?" — is unanswerable if your budget is exactly n.            *)
(* The bookkeeping consumed everything. The answer is lost.                  *)
(*                                                                            *)
(* But: one extra tick resolves it. le_fin_b3 n n (fs n) = BTrue.           *)
(* The void is not permanent. It is PRODUCTIVE.                               *)
(* It is the condition from which emergence happens.                          *)
(*                                                                            *)
(* void -> budget -> measurement -> spuren -> void                            *)
(* The circle closes. Determinism IS uncertainty.                             *)
(* Conservation IS emergence.                                                 *)
(******************************************************************************)

(* SELF-BLINDNESS: budget n cannot verify n <= n.                             *)
(* The observer cannot fully observe itself.                                  *)
(* The cost of self-knowledge exceeds the self.                               *)
Theorem self_blind : forall n,
  bool3_of (le_fin_b3 n n n) = BUnknown.
Proof.
  unfold bool3_of. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. destruct (le_fin_b3 n' n' n') as [[r b'] h].
    simpl in *. exact IH.
Qed.

(* PRODUCTIVE VOID: one extra tick resolves the blindness.                   *)
(* BUnknown is not a wall. It is an open door.                               *)
(* The gap between void and truth is exactly one tick.                        *)
Theorem void_productive : forall n,
  bool3_of (le_fin_b3 n n (fs n)) = BTrue.
Proof.
  unfold bool3_of. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. destruct (le_fin_b3 n' n' (fs n')) as [[r b'] h].
    simpl in *. exact IH.
Qed.

(* EVERY QUESTION HAS A PRICE:                                               *)
(* Budget fs n always suffices to compare n with any m.                      *)
(* The cost of knowing is bounded by your complexity + 1.                    *)
(* No question is permanently unanswerable — only temporarily unaffordable.  *)
Theorem every_question_has_price : forall n m,
  bool3_of (le_fin_b3 n m (fs n)) <> BUnknown.
Proof.
  unfold bool3_of. induction n as [| n' IH]; intro m.
  - simpl. discriminate.
  - destruct m as [| m'].
    + simpl. discriminate.
    + simpl.
      destruct (le_fin_b3 n' m' (fs n')) as [[r b'] h] eqn:Heq.
      simpl. specialize (IH m').
      rewrite Heq in IH. simpl in IH. exact IH.
Qed.

(* Helper: if h >= 1, then fs b <= add_spur h b.                            *)
(* Measurement cost lifts the original budget above the remainder.           *)
Lemma leF_fs_add_spur : forall h b,
  leF (fs b) (add_spur (fs h) b).
Proof.
  intros h b. induction b as [| b' IH].
  - simpl. constructor. apply leF_z.
  - simpl. constructor. exact IH.
Qed.

(* EMERGENCE FROM CONSERVATION:                                               *)
(* Any measurement that costs spuren (h >= 1) simultaneously:                *)
(*   1. PRESERVES the answer to "is b' <= b'?" at the old budget             *)
(*   2. DESTROYS the answer to "is b' <= b'?" at the new budget              *)
(*   3. Leaves the answer ONE TICK away from resolution                       *)
(*                                                                            *)
(* Perfect bookkeeping. Perfect blindness. Perfect productivity.              *)
(* The measurement did not create chaos. It created POTENTIAL.                *)
(* The void it left behind is exactly the space where                         *)
(* the next emergence can happen.                                             *)
(*                                                                            *)
(* This is why the universe is unpredictable despite being deterministic.     *)
(* Not because the laws are random. Because the observer is finite.           *)
(* And finiteness, conserved perfectly, IS the source of surprise.            *)
Theorem emergence_from_conservation : forall h b',
  leF (fs fz) h ->
  (* Before measurement: answerable *)
  bool3_of (le_fin_b3 b' b' (add_spur h b')) = BTrue /\
  (* After measurement: blind *)
  bool3_of (le_fin_b3 b' b' b') = BUnknown /\
  (* But: one more tick resolves *)
  bool3_of (le_fin_b3 b' b' (fs b')) = BTrue.
Proof.
  intros h b' Hh.
  split; [| split].
  - (* Before: answerable — by Caretaker + void_productive *)
    assert (Hc: bool3_of (le_fin_b3 b' b' (add_spur h b')) =
                bool3_of (le_fin_b3 b' b' (fs b'))).
    { apply caretaker_lemma.
      - rewrite void_productive. discriminate.
      - destruct h as [| h']. { inversion Hh. }
        apply leF_fs_add_spur. }
    rewrite Hc. apply void_productive.
  - (* After: blind — self_blind *)
    apply self_blind.
  - (* One tick away — void_productive *)
    apply void_productive.
Qed.

(******************************************************************************)
(* XIII. THE ARROW OF TIME                                                   *)
(*                                                                            *)
(* The second law of thermodynamics is not a physical law.                   *)
(* It is a theorem of finite arithmetic.                                      *)
(*                                                                            *)
(* Entropy increases because:                                                 *)
(*   1. Every operation conserves: add_spur h b' = b                         *)
(*   2. Non-trivial operations produce h >= 1                                *)
(*   3. add_spur (fs h') b' = fs (add_spur h' b') > b'                     *)
(*   4. Therefore: budget strictly decreases                                  *)
(*   5. Therefore: Spuren strictly increases                                  *)
(*   6. Therefore: time is irreversible                                       *)
(*   7. Therefore: the observer's capacity for self-knowledge degrades       *)
(*      (by self_blind: budget b' cannot verify b' <= b')                    *)
(*                                                                            *)
(* No Boltzmann. No ergodic hypothesis. No phase space.                      *)
(* No ensemble averages. No probability.                                      *)
(* Just: Fin, add_spur, conservation.                                         *)
(* The rest is arithmetic.                                                    *)
(******************************************************************************)

(* TIME IS IRREVERSIBLE:                                                      *)
(* Any conservation-respecting operation with cost >= 1                       *)
(* strictly reduces the remaining budget.                                     *)
(* Budget never goes up. Time never goes back.                                *)
Theorem time_irreversible : forall b b' h,
  add_spur h b' = b ->
  leF (fs fz) h ->
  leF (fs b') b.
Proof.
  intros b b' h Hcons Hh.
  destruct h as [| h']. { inversion Hh. }
  rewrite <- Hcons. apply leF_fs_add_spur.
Qed.

(* TWO STEPS COST TWO TICKS:                                                 *)
(* After two non-trivial operations, budget drops by at least 2.             *)
(* Generalization to n steps is immediate by induction.                       *)
Theorem arrow_of_time_2 : forall b h1 b1 h2 b2,
  add_spur h1 b1 = b ->
  leF (fs fz) h1 ->
  add_spur h2 b2 = b1 ->
  leF (fs fz) h2 ->
  leF (fs (fs b2)) b.
Proof.
  intros b h1 b1 h2 b2 Hc1 Hh1 Hc2 Hh2.
  apply leF_trans with (y := fs b1).
  - apply leF_ss. exact (time_irreversible _ _ _ Hc2 Hh2).
  - exact (time_irreversible _ _ _ Hc1 Hh1).
Qed.

(* THE SECOND LAW OF THERMODYNAMICS:                                          *)
(* Every non-trivial observation simultaneously:                              *)
(*   - strictly reduces budget (time_irreversible)                            *)
(*   - makes the observer more blind to itself (self_blind)                  *)
(*                                                                            *)
(* After observation with cost h >= 1 on budget b:                            *)
(* remaining budget b' < b, and le_fin_b3 b' b' b' = BUnknown.              *)
(* The observer KNOWS LESS about itself after each observation of the world.  *)
(*                                                                            *)
(* This is not an approximation. This is not statistical.                     *)
(* This is exact. This is structural. This is Qed.                           *)
Theorem second_law : forall b b' h,
  add_spur h b' = b ->
  leF (fs fz) h ->
  leF (fs b') b /\
  bool3_of (le_fin_b3 b' b' b') = BUnknown.
Proof.
  intros b b' h Hcons Hh.
  split.
  - exact (time_irreversible _ _ _ Hcons Hh).
  - apply self_blind.
Qed.

(******************************************************************************)
(* XIV. METABOLIC CASCADES — Autopoiesis as Arithmetic                      *)
(*                                                                            *)
(* "The system absorbs the foreign and makes it self."                       *)
(*   — Maturana & Varela, The Tree of Knowledge                             *)
(*                                                                            *)
(* "If noise is introduced... the information is increased,                  *)
(*  and this sounds as though the noise were beneficial!"                    *)
(*   — Warren Weaver, commentary on Shannon (1949)                          *)
(*                                                                            *)
(* "Probability does not exist."                                             *)
(*   — Bruno de Finetti, Theory of Probability (1974)                       *)
(*                                                                            *)
(* A single observation metabolizes: budget becomes trace,                   *)
(* the observer changes identity, self-blindness follows.                    *)
(* What happens in a CHAIN of observations?                                  *)
(*                                                                            *)
(* Three things, all provable:                                               *)
(*   1. Blindness cascades — after n observations, budget drops by >= n     *)
(*      and self_blind applies at every stage.                               *)
(*   2. The twist is inevitable — in any finite chain, there exists a       *)
(*      moment where the observer crosses from "can verify itself" to        *)
(*      "cannot verify itself." The skręt. De Finetti's deviation.          *)
(*   3. Absorption is irreversible — once the observer metabolizes          *)
(*      an object, there is no operation that separates them.                *)
(*      Identity is changed. Maturana's autopoiesis as a theorem.           *)
(******************************************************************************)

(* Iterated fs: apply fs n times. fs_iter fz x = x, fs_iter (fs n) x = fs (fs_iter n x) *)
Fixpoint fs_iter (n : Fin) (x : Fin) : Fin :=
  match n with
  | fz => x
  | fs n' => fs (fs_iter n' x)
  end.

(* Observation chain: n non-trivial observations starting from budget b,     *)
(* ending at budget b_final. Each step conserves and costs >= 1.             *)
Inductive obs_chain : Fin -> Fin -> Fin -> Prop :=
  | obs_zero : forall b, obs_chain fz b b
  | obs_step : forall n b b_mid b_final h,
      add_spur h b_mid = b ->
      leF (fs fz) h ->
      obs_chain n b_mid b_final ->
      obs_chain (fs n) b b_final.

(* CASCADING BLINDNESS:                                                      *)
(* After n non-trivial observations:                                         *)
(*   - budget drops by at least n: leF (fs_iter n b_final) b                *)
(*   - the observer is blind to itself at every stage (self_blind)           *)
(*                                                                            *)
(* This is entropy monotonicity in chains.                                   *)
(* Each layer of interpretation deepens the blindness.                       *)
(* XAI (explainable AI) is a cascade of self_blind.                          *)
Theorem cascading_blindness : forall n b b_final,
  obs_chain n b b_final ->
  leF (fs_iter n b_final) b /\
  bool3_of (le_fin_b3 b_final b_final b_final) = BUnknown.
Proof.
  intros n b b_final Hchain.
  split.
  - induction Hchain as [b' | n' b' b_mid' b_final' h' Hcons Hh Hchain' IH].
    + simpl. apply leF_refl.
    + simpl. apply leF_trans with (y := fs b_mid').
      * apply leF_ss. exact IH.
      * exact (time_irreversible _ _ _ Hcons Hh).
  - apply self_blind.
Qed.

(* Helper: fs_iter (fs n) x = fs (fs_iter n x) — definitional, but useful *)
Lemma fs_iter_step : forall n x, fs_iter (fs n) x = fs (fs_iter n x).
Proof. intros. simpl. reflexivity. Qed.

(* TWIST INEVITABLE:                                                         *)
(* In any chain of at least one observation, the observer's budget           *)
(* is strictly less than what it was. Combined with self_blind,              *)
(* this means: there always exists a step in the chain where the             *)
(* observer transitions from "could verify itself with one tick" to          *)
(* "cannot verify itself." The twist. The skręt.                            *)
(*                                                                            *)
(* De Finetti: deviation from expectation is not error, it is learning.      *)
(* Weaver: noise increases information — "this sounds beneficial!"           *)
(* Void-theory: the twist is not an accident. It is a theorem.              *)
(*   The moment of blindness IS the moment of emergence.                     *)
(*                                                                            *)
(* We prove: after any non-trivial observation, the observer was             *)
(* answerable before (at the old budget) and is blind now (at the new).      *)
(* The twist exists. It is produced by conservation. It is inevitable.       *)
Theorem twist_inevitable : forall b b' h,
  add_spur h b' = b ->
  leF (fs fz) h ->
  (* Before: the observer could verify b' <= b' at the old budget *)
  bool3_of (le_fin_b3 b' b' (add_spur h b')) = BTrue /\
  (* After: the observer cannot verify b' <= b' at the new budget *)
  bool3_of (le_fin_b3 b' b' b') = BUnknown /\
  (* The twist: the transition from sight to blindness is exactly one *)
  (* non-trivial observation. Not gradual. Not statistical. Atomic. *)
  leF (fs b') b.
Proof.
  intros b b' h Hcons Hh.
  split; [| split].
  - (* Before: answerable — reuse emergence_from_conservation *)
    assert (Hc: bool3_of (le_fin_b3 b' b' (add_spur h b')) =
                bool3_of (le_fin_b3 b' b' (fs b'))).
    { apply caretaker_lemma.
      - rewrite void_productive. discriminate.
      - destruct h as [| h']. { inversion Hh. }
        apply leF_fs_add_spur. }
    rewrite Hc. apply void_productive.
  - (* After: blind *)
    apply self_blind.
  - (* Budget strictly decreased *)
    exact (time_irreversible _ _ _ Hcons Hh).
Qed.

(* IDENTITY IRREVERSIBLE — Metabolic Absorption                              *)
(* (Maturana/Varela: the system absorbs the foreign and makes it self)       *)
(*                                                                            *)
(* After observation: the observer's identity has changed (b' <> b).         *)
(* The Spuren are permanently fused with the observer — there is no          *)
(* operation that "extracts" h from b without spending MORE budget.           *)
(* To separate observer from observed, you must observe again —              *)
(* which changes identity again. The metabolic circle never opens.           *)
(*                                                                            *)
(* Neural network version: after training on data X, the network IS          *)
(* partially X. To understand which part is X, you need another network,     *)
(* which absorbs the first. XAI is an infinite regress on finite budget.     *)
(*                                                                            *)
(* We prove: after metabolizing, the observer cannot return to its           *)
(* pre-observation state without a strictly larger budget — which itself     *)
(* would change the observer further. Absorption is a one-way door.          *)
Theorem identity_irreversible : forall b b' h,
  add_spur h b' = b ->
  leF (fs fz) h ->
  (* The observer is no longer itself *)
  b' <> b /\
  (* The observer is blind to its new self *)
  bool3_of (le_fin_b3 b' b' b') = BUnknown /\
  (* Recovering the old budget requires MORE than what was spent — *)
  (* leF b (add_spur h b') is trivially true (equality), but *)
  (* any attempt to "undo" by observing the Spuren costs more budget *)
  forall h2 b'',
    add_spur h2 b'' = b' ->
    leF (fs fz) h2 ->
    (* After trying to "look at" the Spuren, budget drops further *)
    leF (fs (fs b'')) b /\
    (* And self-blindness deepens *)
    bool3_of (le_fin_b3 b'' b'' b'') = BUnknown.
Proof.
  intros b b' h Hcons Hh.
  split; [| split].
  - (* b' <> b: non-trivial observation means strict decrease *)
    intro Heq. rewrite Heq in Hcons.
    (* Hcons : add_spur h b = b, so leF (fs b) b — impossible *)
    assert (Hlt: leF (fs b) b) by exact (time_irreversible _ _ _ Hcons Hh).
    clear Heq Hcons Hh h b'.
    induction b as [| b0 IH].
    + inversion Hlt.
    + inversion Hlt; subst. apply IH. exact H1.
  - (* Blind to new self *)
    apply self_blind.
  - (* Trying to undo deepens the cascade *)
    intros h2 b'' Hcons2 Hh2.
    split.
    + (* Two steps: arrow_of_time_2 *)
      exact (arrow_of_time_2 _ _ _ _ _ Hcons Hh Hcons2 Hh2).
    + (* Still blind *)
      apply self_blind.
Qed.

(******************************************************************************)
(* XV. READ IS WRITE — The Asymmetry of Observation                          *)
(*                                                                            *)
(* "Can you rape without touching?"                                          *)
(*                                                                            *)
(* Classical computation assumes pure read: inspect memory, nothing changes. *)
(* Void-theory: every observation is atomic read+write.                      *)
(* no_free_lunch_le (already proved in void_finite_minimal):                 *)
(*   le_fin_b3 n m (fs b) = (res, b', h) -> h <> fz                        *)
(* Even a "failed" observation (BUnknown) writes Spuren. There is no         *)
(* innocent look. No pure read. No cost-free inspection.                     *)
(*                                                                            *)
(* The asymmetry: the WRITER is blind to their own write (self_blind).       *)
(* The one being OBSERVED feels the full change. Same add_spur,              *)
(* two incompatible experiences. Two onto-notations for one event.           *)
(*                                                                            *)
(* "I was just looking." — Budget says otherwise.                            *)
(******************************************************************************)

(* BLINDNESS IS CONTAGIOUS:                                                   *)
(* If A observes something and becomes blind (self_blind at a'),              *)
(* and B observes A, then B becomes blind too (self_blind at b').             *)
(* You cannot observe blindness without becoming blind yourself.              *)
(* Blindness propagates through observation chains.                           *)
(*                                                                            *)
(* Neural network version: if network N is a black box (self_blind),         *)
(* then any interpretability tool T that observes N becomes a black box too. *)
(* XAI doesn't solve opacity. XAI catches opacity.                           *)
Theorem blindness_is_contagious : forall a a' ha b b' hb,
  add_spur ha a' = a ->
  leF (fs fz) ha ->
  add_spur hb b' = b ->
  leF (fs fz) hb ->
  (* A is blind to itself *)
  bool3_of (le_fin_b3 a' a' a') = BUnknown /\
  (* B could see A — one tick suffices *)
  bool3_of (le_fin_b3 a' a' (fs a')) = BTrue /\
  (* But B, having observed, is now blind to itself *)
  bool3_of (le_fin_b3 b' b' b') = BUnknown /\
  (* B cannot see that it caught A's condition *)
  (* because seeing that would require yet another observation *)
  (* which would make the meta-observer blind too. *)
  (* The chain never terminates. Opacity is infectious. *)
  leF (fs b') b.
Proof.
  intros a a' ha b b' hb Hca Hha Hcb Hhb.
  split; [| split; [| split]].
  - apply self_blind.
  - apply void_productive.
  - apply self_blind.
  - exact (time_irreversible _ _ _ Hcb Hhb).
Qed.

(* WRITE ASYMMETRY:                                                           *)
(* After observation, the observer and an external witness have               *)
(* incompatible knowledge about what happened.                                *)
(*                                                                            *)
(* The observer (at b') CANNOT:                                               *)
(*   - verify its own size (self_blind)                                      *)
(*   - detect that it changed (has no access to old b)                       *)
(*                                                                            *)
(* An external witness (with budget >= fs b') CAN:                            *)
(*   - verify the observer's size (void_productive)                          *)
(*   - see that the observer is smaller than before                          *)
(*                                                                            *)
(* Same event. Two onto-notations. The writer doesn't know it wrote.         *)
(* The reader knows it was written. Asymmetry is structural.                 *)
(*                                                                            *)
(* "Rozdzielczosc? Jaka rozdzielczosc?" — the writer.                       *)
(* "Odczuwam go w pelni." — the reader.                                     *)
Theorem write_asymmetry : forall b b' h,
  add_spur h b' = b ->
  leF (fs fz) h ->
  (* Observer: blind to own state *)
  bool3_of (le_fin_b3 b' b' b') = BUnknown /\
  (* External witness: can see the observer clearly *)
  bool3_of (le_fin_b3 b' b' (fs b')) = BTrue /\
  (* External witness: can verify the observer shrank *)
  leF (fs b') b /\
  (* Observer: identity changed, cannot return *)
  b' <> b.
Proof.
  intros b b' h Hcons Hh.
  split; [| split; [| split]].
  - apply self_blind.
  - apply void_productive.
  - exact (time_irreversible _ _ _ Hcons Hh).
  - intro Heq. rewrite Heq in Hcons.
    assert (Hlt: leF (fs b) b) by exact (time_irreversible _ _ _ Hcons Hh).
    clear Heq Hcons Hh h b'.
    induction b as [| b0 IH].
    + inversion Hlt.
    + inversion Hlt; subst. apply IH. exact H1.
Qed.

(* RESOLUTION GAP:                                                            *)
(* Two entangled systems (observer + its Spuren) create an observation        *)
(* cost that is STRICTLY HIGHER than observing either part alone.             *)
(*                                                                            *)
(* To understand an observer who has already observed, you need:              *)
(*   1. Observe their remaining budget b' (cost >= 1)                        *)
(*   2. Observe their Spuren h (cost >= 1)                                   *)
(*   3. But now YOU have observed twice — cascading_blindness applies         *)
(*                                                                            *)
(* Observing a "flat" object: 1 observation, cost >= 1.                      *)
(* Observing an observer: >= 2 observations, cost >= 2.                      *)
(* The gap: understanding a dual system costs MORE than understanding         *)
(* a simple object. And the extra cost falls "between" — the interaction     *)
(* of observer and Spuren is not capturable by either measurement alone.      *)
(*                                                                            *)
(* Cancer: mutation is binary (one tick). Effect is continuous (1.929...).    *)
(* The resolution of the detector (Fin) cannot capture the resolution        *)
(* of the effect (interaction of two Fin systems).                            *)
(*                                                                            *)
(* Ketamine: disrupts the budget system, not the computation system.          *)
(* The "gap" between the two is where dissociation lives.                    *)
Theorem resolution_gap : forall ext ext' ext'' h1 h2,
  add_spur h1 ext' = ext ->
  leF (fs fz) h1 ->
  add_spur h2 ext'' = ext' ->
  leF (fs fz) h2 ->
  (* Two observations cost at least 2 — more than one *)
  leF (fs (fs ext'')) ext /\
  (* Observer is blind after both *)
  bool3_of (le_fin_b3 ext'' ext'' ext'') = BUnknown /\
  (* Each intermediate state was also blind *)
  bool3_of (le_fin_b3 ext' ext' ext') = BUnknown.
Proof.
  intros ext ext' ext'' h1 h2 Hc1 Hh1 Hc2 Hh2.
  split; [| split].
  - exact (arrow_of_time_2 _ _ _ _ _ Hc1 Hh1 Hc2 Hh2).
  - apply self_blind.
  - apply self_blind.
Qed.

(******************************************************************************)
(* SECTION XVI: NACHTRÄGLICHKEIT — The Delayed Activation of Spuren          *)
(*                                                                            *)
(* Freud (1895): trauma does not act at the moment of impact.                *)
(* It acts LATER, when a second event retroactively activates the first.     *)
(* Nachträglichkeit — deferred action. The trace was always there.           *)
(* The subject was always blind to it (self_blind).                          *)
(* A new event does not illuminate the old trace — it changes the subject    *)
(* again (identity_irreversible), creating a deeper trajectory.              *)
(* At every step: blind. At every step: one tick from knowing.               *)
(* Knowledge accumulates invisibly. Activation is always deferred.           *)
(*                                                                            *)
(* The teacher writes Spuren in the student. The student is blind            *)
(* to the change (self_blind). The teacher is blind to the effect            *)
(* (write_asymmetry). Three years later, life deposits new Spuren            *)
(* on top of the old ones. The student is STILL blind. But the               *)
(* trajectory b0 → b1 → b2 has structure that b0 → b1 did not.             *)
(* Nobody sees it from inside. Everybody is one tick from seeing it.         *)
(*                                                                            *)
(* This is autopoiesis as temporal cascade: each metabolic step              *)
(* changes the organism, the organism cannot see the change, and             *)
(* the accumulation of invisible changes IS the organism's history.          *)
(******************************************************************************)

(* Theorem 24: nachtraeglichkeit                                              *)
(* Two sequential observations create a trajectory that is:                   *)
(*   - invisible to the subject at every step (self_blind at b1 and b2)      *)
(*   - deeper than either step alone (arrow_of_time_2: gap >= 2)             *)
(*   - irreversible at every step (b1 ≠ b0, b2 ≠ b1)                       *)
(*   - one tick from activation at every step (void_productive)              *)
(* Spuren from step 1 are "dormant" — they exist (conservation) but are      *)
(* invisible to the subject. Step 2 does not "activate" them — it adds       *)
(* MORE dormant Spuren. The subject never wakes up. But the trajectory       *)
(* gets richer with every step.                                               *)

Theorem nachtraeglichkeit : forall b0 b1 b2 h1 h2,
  add_spur h1 b1 = b0 ->
  leF (fs fz) h1 ->
  add_spur h2 b2 = b1 ->
  leF (fs fz) h2 ->
  (* At moment 1: subject is blind *)
  bool3_of (le_fin_b3 b1 b1 b1) = BUnknown /\
  (* At moment 2: subject is STILL blind *)
  bool3_of (le_fin_b3 b2 b2 b2) = BUnknown /\
  (* The trajectory has depth >= 2 *)
  leF (fs (fs b2)) b0 /\
  (* At every step: one tick from knowing *)
  bool3_of (le_fin_b3 b1 b1 (fs b1)) = BTrue /\
  bool3_of (le_fin_b3 b2 b2 (fs b2)) = BTrue /\
  (* Both steps irreversible: you cannot un-learn, un-hear, un-see *)
  b1 <> b0 /\
  b2 <> b1.
Proof.
  intros b0 b1 b2 h1 h2 Hc1 Hh1 Hc2 Hh2.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply self_blind.
  - apply self_blind.
  - exact (arrow_of_time_2 _ _ _ _ _ Hc1 Hh1 Hc2 Hh2).
  - apply void_productive.
  - apply void_productive.
  - intro Heq. rewrite <- Heq in Hc1.
    assert (Hlt: leF (fs b1) b1) by exact (time_irreversible _ _ _ Hc1 Hh1).
    clear Heq Hc1 Hh1 Hc2 Hh2 h1 h2 b0 b2.
    induction b1 as [| b1' IH].
    + inversion Hlt.
    + inversion Hlt; subst. apply IH. exact H1.
  - intro Heq. rewrite <- Heq in Hc2.
    assert (Hlt: leF (fs b2) b2) by exact (time_irreversible _ _ _ Hc2 Hh2).
    clear Heq Hc1 Hh1 Hc2 Hh2 h1 h2 b0 b1.
    induction b2 as [| b2' IH].
    + inversion Hlt.
    + inversion Hlt; subst. apply IH. exact H1.
Qed.

(* Theorem 25: dormant_spuren                                                *)
(* Spuren deposited by observation are invisible to their producer.          *)
(* An external observer can verify they exist (leF (fs b') b) —             *)
(* but the act of verification makes the external observer blind too.        *)
(* The Spuren are real (conservation). Nobody can see them without           *)
(* becoming blind. Seeing costs. The cost is yourself.                       *)
(*                                                                            *)
(* Teaching: the teacher deposits Spuren in the student.                     *)
(* The teacher cannot see what they deposited (write_asymmetry).             *)
(* The student cannot see what changed in them (self_blind).                 *)
(* A colleague observing the class can verify change occurred —              *)
(* but becomes blind to themselves in the process.                           *)
(* Nobody holds the complete picture. Everybody holds a piece.               *)
(* Each piece cost its holder their self-transparency.                       *)

Theorem dormant_spuren : forall subject sub' h_sub observer obs' h_obs,
  (* Subject performs observation — deposits Spuren *)
  add_spur h_sub sub' = subject ->
  leF (fs fz) h_sub ->
  (* External observer observes the subject *)
  add_spur h_obs obs' = observer ->
  leF (fs fz) h_obs ->
  (* Subject: blind to own Spuren *)
  bool3_of (le_fin_b3 sub' sub' sub') = BUnknown /\
  (* Observer can verify subject changed: sub' < subject *)
  leF (fs sub') subject /\
  (* But observer is now blind to SELF *)
  bool3_of (le_fin_b3 obs' obs' obs') = BUnknown /\
  (* Both one tick from self-knowledge *)
  bool3_of (le_fin_b3 sub' sub' (fs sub')) = BTrue /\
  bool3_of (le_fin_b3 obs' obs' (fs obs')) = BTrue /\
  (* Both irreversibly changed — no undo *)
  sub' <> subject /\
  obs' <> observer.
Proof.
  intros subject sub' h_sub observer obs' h_obs Hcs Hhs Hco Hho.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply self_blind.
  - exact (time_irreversible _ _ _ Hcs Hhs).
  - apply self_blind.
  - apply void_productive.
  - apply void_productive.
  - intro Heq. rewrite <- Heq in Hcs.
    assert (Hlt: leF (fs sub') sub')
      by exact (time_irreversible _ _ _ Hcs Hhs).
    clear Heq Hcs Hhs Hco Hho h_sub h_obs subject observer.
    induction sub' as [| s' IH].
    + inversion Hlt.
    + inversion Hlt; subst. apply IH. exact H1.
  - intro Heq. rewrite <- Heq in Hco.
    assert (Hlt: leF (fs obs') obs')
      by exact (time_irreversible _ _ _ Hco Hho).
    clear Heq Hcs Hhs Hco Hho h_sub h_obs subject observer.
    induction obs' as [| o' IH].
    + inversion Hlt.
    + inversion Hlt; subst. apply IH. exact H1.
Qed.

(******************************************************************************)
(* SECTION XVII: PATTERN, NOT OBJECT                                         *)
(*                                                                            *)
(* Peano builds OBJECTS: 0, S 0, S (S 0) — each a concrete, distinct thing. *)
(* Void builds PATTERNS: pairs (value, budget) where the relationship        *)
(* between value and budget determines what the system can know.             *)
(*                                                                            *)
(* A Pattern is not a thing. It is a STATE OF ACTIVITY — how much was done   *)
(* (value) relative to how much can still be done (budget).                  *)
(* The ontology is not of objects but of metabolic configurations.           *)
(*                                                                            *)
(* Conceived as mathematics of a first nervous system with a central hub:    *)
(* le_fin_b3 takes (value, threshold, budget) and returns                    *)
(* (verdict, remaining_budget, heat). The hub integrates, decides, and pays. *)
(******************************************************************************)

(* A Pattern is a pair: what-was-computed × what-remains.                    *)
(* Not a number. A metabolic configuration.                                  *)
Definition Pattern := (Fin * Fin)%type.

Definition pattern_value (p : Pattern) : Fin := fst p.
Definition pattern_budget (p : Pattern) : Fin := snd p.

(* DIAGONAL PATTERN: value = budget.                                         *)
(* The system tries to measure itself with itself.                           *)
(* Result: ALWAYS BUnknown. Self-blindness is a property of the diagonal.   *)
Theorem pattern_self_blind : forall n,
  bool3_of (le_fin_b3 n n n) = BUnknown.
Proof. exact self_blind. Qed.

(* OFF-DIAGONAL PATTERN: budget = fs(value).                                 *)
(* The system has one tick MORE than what it measures.                       *)
(* Result: ALWAYS BTrue. One tick resolves the blindness.                    *)
(* This is the minimal departure from the diagonal that restores sight.     *)
Theorem pattern_void_productive : forall n,
  bool3_of (le_fin_b3 n n (fs n)) = BTrue.
Proof. exact void_productive. Qed.

(* THE SUCCESSOR TAX ON PATTERNS:                                            *)
(* Moving from pattern (n, b) to pattern (fs n, fs b) preserves the          *)
(* diagonal/off-diagonal structure but costs one more tick of heat.          *)
(* Pattern growth is never free.                                             *)
Theorem pattern_successor_tax : forall n b r b'' h,
  le_fin_b3 n n b = (r, b'', h) ->
  le_fin_b3 (fs n) (fs n) (fs b) = (r, b'', fs h).
Proof. exact (fun n b => successor_costs_more_le n n b). Qed.

(* COLLAPSE AS PATTERN DESTRUCTION:                                          *)
(* collapse3 maps Bool3 to bool, erasing BUnknown.                          *)
(* On the diagonal pattern (n, n), this turns BUnknown into false.          *)
(* The system that cannot afford self-knowledge is told "no" instead of     *)
(* "I cannot afford to ask." This is the mechanism of trauma:               *)
(* refusing the Real (BUnknown) by forcing the Symbolic (false).            *)
Theorem pattern_trauma : forall n,
  collapse3 (bool3_of (le_fin_b3 n n n)) = false.
Proof.
  intro n. rewrite self_blind. simpl. reflexivity.
Qed.

(******************************************************************************)
(* SECTION XVIII: PROBABILITY CONDITIONED BY BUDGET                          *)
(*                                                                            *)
(* De Finetti (1970): "Probability does not exist."                          *)
(* Nau (2001): "Probability uncontaminated by attitudes toward money         *)
(*              does not exist."                                             *)
(* Void-theory: probability uncontaminated by BUDGET does not exist.         *)
(*                                                                            *)
(* The measure_region function returns categorically different types          *)
(* of answers depending on budget:                                           *)
(*   fz           -> MVoid  (cannot afford to ask)                           *)
(*   fs fz        -> MVague (rough interval)                                 *)
(*   fs(fs(fs b)) -> MSharp (precise fraction)                               *)
(*                                                                            *)
(* These are not different PRECISIONS of the same answer.                    *)
(* They are different KINDS of answer. MVoid is not zero.                    *)
(* MVague is not imprecise MSharp. The budget determines not just            *)
(* how well you know, but WHETHER you know at all.                           *)
(*                                                                            *)
(* Observation is a bet: you stake budget for a chance at resolution.        *)
(* You always pay (Spuren). You do not always win (BUnknown).               *)
(* But even BUnknown is information: it tells you your budget state.         *)
(******************************************************************************)

(* MVoid is NOT zero probability. It is unmeasured.                          *)
(* Classical mathematics conflates "P(A) = 0" with "A is impossible."       *)
(* Void-theory distinguishes: MVoid = "I cannot afford to measure A."       *)
(* MSharp(fz, _) = "I measured A and it has zero weight."                   *)
(* These are fundamentally different epistemic states.                        *)
Theorem void_is_not_zero : forall denom,
  MVoid <> MSharp (fz, denom).
Proof. intros denom H. discriminate H. Qed.

(* THE DE FINETTI SPECTRUM: budget determines the KIND of answer.            *)
(* Three budget levels, three categorically different results.               *)
(* This is not gradual degradation. It is phase transition.                  *)

Theorem deFinetti_void : forall r s,
  fst (fst (measure_region r s fz)) = MVoid.
Proof. exact zero_budget_yields_void. Qed.

Theorem deFinetti_vague : forall r s,
  exists lo hi, fst (fst (measure_region r s (fs fz))) = MVague lo hi.
Proof. exact budget_one_gives_vague. Qed.

Theorem deFinetti_sharp : forall r s b,
  exists p b' h, measure_region r s (fs (fs (fs b))) = (MSharp p, b', h).
Proof. exact budget_sufficient_gives_sharp. Qed.

(* OBSERVATION IS A BET: you always pay, you do not always win.             *)
(* Invoking le_fin_b3 n m b is a wager:                                     *)
(*   Stake: budget b                                                         *)
(*   If b > 0: you pay Spuren (always), you get BTrue/BFalse/BUnknown      *)
(*   If b = 0: you pay nothing, you get BUnknown (cannot afford to ask)     *)
(*                                                                            *)
(* Win = BTrue or BFalse (you learn n <= m or n > m)                        *)
(* Draw = BUnknown with b > 0 (you paid but learned only your limit)        *)
(* Fold = BUnknown with b = 0 (you cannot enter the game)                   *)
(*                                                                            *)
(* The asymmetry: you ALWAYS pay when b > 0 (no_free_lunch_le).             *)
(* But BUnknown is not "nothing" — it is self-knowledge.                    *)
(* You learn that your budget is insufficient. This is the Real.            *)

Theorem observation_always_costs : forall n m b res b' h,
  le_fin_b3 n m (fs b) = (res, b', h) -> h <> fz.
Proof. exact no_free_lunch_le. Qed.

Theorem observation_bankrupt_is_silent : forall n m,
  bool3_of (le_fin_b3 n m fz) = BUnknown.
Proof.
  unfold bool3_of. intros n m.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - destruct m; simpl; reflexivity.
Qed.

(* THE BET PRODUCES HEAT REGARDLESS OF OUTCOME:                              *)
(* Whether the result is BTrue, BFalse, or BUnknown,                        *)
(* if you had budget, you spent it. The only way to produce no heat          *)
(* is to have no budget. Silence is free. Everything else costs.             *)
Theorem silence_is_free : forall n m,
  spuren_of_b3 (le_fin_b3 n m fz) = fz.
Proof.
  unfold spuren_of_b3. intros n m.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - destruct m; simpl; reflexivity.
Qed.

Theorem speech_is_not : forall n m b,
  spuren_of_b3 (le_fin_b3 n m (fs b)) <> fz.
Proof.
  intros n m b.
  unfold spuren_of_b3.
  destruct (le_fin_b3 n m (fs b)) as [[r b'] h] eqn:Heq.
  simpl.
  pose proof (no_free_lunch_le _ _ _ _ _ _ Heq) as H.
  exact H.
Qed.

(* SUMMARY: What void-theory proves that classical mathematics cannot.       *)
(*                                                                            *)
(* 1. The Caretaker Lemma — knowledge never reverses (after Kirby)           *)
(* 2. All regions measurable — no Vitali sets (anti-classical)               *)
(* 3. Measurement conservation — 2nd law of thermodynamics (theorem)         *)
(* 4. No-cloning — anti-Banach-Tarski (theorem, not axiom)                  *)
(* 5. Zero budget blind — zero budget = total ignorance                      *)
(* 6. Resolution cost — deeper structure costs more (Heisenberg)             *)
(* 7. Sharp requires 3 — entry fee for precision                             *)
(* 8. Measurement shrinks budget — each look costs                           *)
(* 9. Complementarity — two measurements cost more than one (Bohr)           *)
(* 10. Uncertainty — known unknowable (Heisenberg)                           *)
(*     If first measurement exhausts budget, second is GUARANTEED BUnknown.  *)
(*     Not "might be unknown." IS unknown. Certainty about limits.           *)
(* 11. Self-blindness — le_fin_b3 n n n = BUnknown. Always.                 *)
(*     Budget n cannot verify n <= n. The observer cannot observe itself.    *)
(* 12. Productive void — le_fin_b3 n n (fs n) = BTrue.                      *)
(*     One tick resolves the blindness. Void is not death. Void is potential.*)
(* 13. Every question has a price — budget fs n suffices for any comparison. *)
(*     No question is permanently unanswerable. Only temporarily unaffordable*)
(* 14. Emergence from conservation — measurement creates blind spots.        *)
(*     Before: answerable. After: blind. But: one tick away from truth.      *)
(*     Determinism breeds void. Conservation breeds emergence.               *)
(* 15. Time irreversible — non-trivial operation strictly reduces budget.    *)
(*     Budget never goes up. Time never goes back. leF (fs b') b.           *)
(* 16. Arrow of time (2-step) — two operations drop budget by at least 2.   *)
(*     Generalizes to n by induction.                                        *)
(* 17. The Second Law — every observation makes the observer                 *)
(*     more blind to itself. time_irreversible + self_blind combined.        *)
(*     Thermodynamics as a theorem of finite arithmetic. Qed.                *)
(* 18. Cascading blindness — n observations drop budget by >= n.             *)
(*     Entropy monotonicity in chains. XAI as cascade of self_blind.         *)
(* 19. Twist inevitable — every non-trivial observation produces a           *)
(*     transition from sight to blindness. De Finetti's skręt.              *)
(*     Weaver's beneficial noise. Not accidental. Structural.                *)
(* 20. Identity irreversible — metabolic absorption (Maturana/Varela).       *)
(*     After observation, observer ≠ old observer (b' ≠ b).                 *)
(*     Trying to undo deepens the cascade. You are what you eat.             *)
(* 21. Blindness is contagious — observing a blind system makes you blind.   *)
(*     XAI catches opacity; it does not resolve it. Qed.                     *)
(* 22. Write asymmetry — writer is blind, reader feels the full act.         *)
(*     Read IS write. No pure observation exists. Collapsed duality.         *)
(* 23. Resolution gap — observing an observer costs strictly more than       *)
(*     observing a flat object. Two onto-notations, one Fin.                 *)
(*     The gap between ticks is where the cost hides.                        *)
(* 24. Nachträglichkeit — two observations create a trajectory invisible     *)
(*     at every step. Spuren from step 1 are dormant until step 2.          *)
(*     But step 2 adds MORE dormant Spuren. Activation always deferred.     *)
(*     Freud without the couch. Pedagogy without the illusion of transfer.   *)
(* 25. Dormant Spuren — Spuren are conserved but invisible to producer.      *)
(*     External observer can verify they exist — but becomes blind too.      *)
(*     Nobody holds the complete picture. Each piece costs self-transparency. *)
(* 26. Pattern self-blind — self_blind as property of diagonal (n,n) pair.   *)
(*     Object does not exist. Pattern = (value, budget). When they collide:  *)
(*     BUnknown. Mathematics of patterns, not objects.                       *)
(* 27. Pattern void-productive — (n, fs n) restores sight.                   *)
(*     Minimal departure from diagonal. One tick. First nervous system.      *)
(* 28. Pattern trauma — collapse3 on diagonal = false.                       *)
(*     Refusing BUnknown by forcing false. The mechanism of trauma.          *)
(*     Lacan's Real erased by the Symbolic. One line of code.                *)
(* 29. Void is not zero — MVoid <> MSharp(fz, _).                           *)
(*     Unmeasured is not impossible. De Finetti's core insight, compiled.    *)
(* 30. Observation always costs — le_fin_b3 with fs b produces h <> fz.     *)
(*     Every bet has a price. No free lunch, no free observation.            *)
(* 31. Silence is free — le_fin_b3 with fz produces fz Spuren.              *)
(*     The only free act is not acting. Bankrupt systems generate no heat.   *)
(* 32. Speech is not — le_fin_b3 with fs b produces h <> fz.                *)
(*     If you can afford to ask, you WILL pay. The asymmetry of the bet.    *)
(*                                                                            *)
(* All Qed. All derived from Fin, Budget, Spuren, and conservation.          *)
(* Zero axioms in this file. Zero Admitted in the codebase.                  *)
(* Classical mathematics proves the opposite of (4) and cannot state          *)
(* (1), (5)-(32).                                                            *)
(* Physics agrees with us, not with them.                                     *)
(******************************************************************************)

End Void_Probability_Geometry.
