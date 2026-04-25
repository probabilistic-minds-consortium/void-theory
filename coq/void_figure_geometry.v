(******************************************************************************)
(* void_figure_geometry.v -- Pattern-based figure geometry.                   *)
(*                                                                            *)
(* Figures as multi-dimensional patterns with built-in budget per coordinate. *)
(* Not objects in space -- patterns with resolution.                          *)
(*                                                                            *)
(* Depends only on: void_finite_minimal, void_probability_minimal,            *)
(*                  void_probability_geometry.                                *)
(* Does NOT depend on predictive_learning, mortal_regime, network_cell,       *)
(* mortal_network. This is mathematics, not a network.                        *)
(*                                                                            *)
(* STRICTLY FINITIST. ZERO nat. ZERO Admitted. ZERO new Axioms.               *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_probability_geometry.

Import Void_Probability_Minimal.
Import Void_Probability_Geometry.

(******************************************************************************)
(* PART 1: Figure -- multi-dimensional pattern.                               *)
(*                                                                            *)
(* A figure is a list of patterns (one per coordinate) plus a recognition    *)
(* radius. Each coordinate carries its own budget -- the resolution at which *)
(* it can be distinguished.                                                   *)
(******************************************************************************)

Record Figure := mkFigure {
  fig_center : list Pattern;
  fig_radius : Fin;
}.

(* Length of a list as Fin. No nat allowed anywhere. *)
Fixpoint length_fin {A : Type} (l : list A) : Fin :=
  match l with
  | []      => fz
  | _ :: rs => fs (length_fin rs)
  end.

Definition fig_dimension (f : Figure) : Fin :=
  length_fin (fig_center f).

Definition fig_values (f : Figure) : list Fin :=
  map pattern_value (fig_center f).

Definition fig_budgets (f : Figure) : list Fin :=
  map pattern_budget (fig_center f).

(* Sanity checks -- these compute and are trivially true. *)
Lemma fig_dimension_empty : forall r,
  fig_dimension (mkFigure [] r) = fz.
Proof. intro r. reflexivity. Qed.

Lemma fig_dimension_cons : forall p rs r,
  fig_dimension (mkFigure (p :: rs) r) = fs (length_fin rs).
Proof. intros p rs r. reflexivity. Qed.

(******************************************************************************)
(* PART 2: Distance between patterns, then between figures.                   *)
(*                                                                            *)
(* Two patterns differ in TWO dimensions: value and budget.                   *)
(* Manhattan: d(p1, p2) = |v1 - v2| + |b1 - b2|.                              *)
(* Cost: the measurement costs budget and produces Spuren, just like         *)
(* every other measurement in void-theory.                                    *)
(******************************************************************************)

(* Distance between two patterns. *)
Definition pattern_distance (p1 p2 : Pattern) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match distance (pattern_value p1) (pattern_value p2) b with
  | (dv, b1, h1) =>
      match distance (pattern_budget p1) (pattern_budget p2) b1 with
      | (db, b2, h2) =>
          match add_fin_b_spur dv db b2 with
          | (sum, b3, h3) => (sum, b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(* Distance between two figure centers (lists of patterns).                   *)
(* Zip semantics: shorter list terminates the sum; tail of longer ignored.    *)
Fixpoint figure_distance (c1 c2 : list Pattern) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match c1, c2 with
  | [], _           => (fz, b, fz)
  | _, []           => (fz, b, fz)
  | p1 :: rs1, p2 :: rs2 =>
      match pattern_distance p1 p2 b with
      | (d, b1, h1) =>
          match figure_distance rs1 rs2 b1 with
          | (drest, b2, h2) =>
              match add_fin_b_spur d drest b2 with
              | (sum, b3, h3) => (sum, b3, add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

(******************************************************************************)
(* PART 3: Recognition. Does a signal match a figure?                         *)
(*                                                                            *)
(* Compute distance(signal, center). If distance <= radius, BTrue.            *)
(* If distance > radius, BFalse. If cannot decide, BUnknown.                  *)
(******************************************************************************)

Definition recognize (signal : list Pattern) (fig : Figure) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match figure_distance signal (fig_center fig) b with
  | (dist, b1, h1) =>
      match le_fin_b3 dist (fig_radius fig) b1 with
      | (res, b2, h2) => (res, b2, add_spur h1 h2)
      end
  end.

(* ----- THEOREMS FOR PART 3 ----- *)

(* ----- Helper lemmas: at budget fz, everything saturates. ----- *)

(* sub_saturate_b_spur has `struct n` (or similar) -- need destruct n. *)
Lemma sub_saturate_fz : forall n m,
  sub_saturate_b_spur n m fz = (fz, fz, fz).
Proof. intros n m. destruct n; simpl; reflexivity. Qed.

(* add_fin_b_spur has `struct m`. *)
Lemma add_fin_b_spur_fz_local : forall n m,
  add_fin_b_spur n m fz = (n, fz, fz).
Proof. intros n m. destruct m; simpl; reflexivity. Qed.

(* distance on fz uses zero_budget_blind (from geometry module) +             *)
(* sub_saturate_fz. *)
Lemma distance_fz : forall n m,
  distance n m fz = (fz, fz, fz).
Proof.
  intros n m.
  unfold distance, le_fin_b_spur.
  rewrite (zero_budget_blind n m).
  simpl.
  rewrite sub_saturate_fz.
  reflexivity.
Qed.

(* pattern_distance at budget fz yields (fz, fz, fz). *)
Lemma pattern_distance_fz : forall p1 p2,
  pattern_distance p1 p2 fz = (fz, fz, fz).
Proof.
  intros p1 p2.
  unfold pattern_distance.
  rewrite distance_fz. simpl.
  rewrite distance_fz. simpl.
  reflexivity.
Qed.

(* figure_distance at budget fz yields (fz, fz, fz) for any two lists. *)
Lemma figure_distance_fz : forall c1 c2,
  figure_distance c1 c2 fz = (fz, fz, fz).
Proof.
  intros c1. induction c1 as [|p1 rs1 IH].
  - (* c1 = [] *) intro c2. simpl. reflexivity.
  - (* c1 = p1 :: rs1 *)
    intro c2. destruct c2 as [|p2 rs2].
    + (* c2 = [] *) simpl. reflexivity.
    + (* c2 = p2 :: rs2 *)
      simpl.
      destruct (pattern_distance p1 p2 fz) as [[d b1] h1] eqn:Hpd.
      rewrite pattern_distance_fz in Hpd. inversion Hpd; subst; clear Hpd.
      destruct (figure_distance rs1 rs2 fz) as [[drest b2] h2] eqn:Hfd.
      rewrite IH in Hfd. inversion Hfd; subst; clear Hfd.
      simpl. reflexivity.
Qed.

(* THEOREM: Zero budget -> cannot recognize.                                  *)
(* Without any resources you cannot distinguish match from mismatch.          *)
Theorem recognize_zero_budget_blind : forall signal fig,
  recognize signal fig fz = (BUnknown, fz, fz).
Proof.
  intros signal fig.
  unfold recognize.
  rewrite figure_distance_fz.
  simpl. reflexivity.
Qed.

(******************************************************************************)
(* PART 4: Relations between figures.                                         *)
(*                                                                            *)
(* Four primitive three-valued, budgeted relations:                          *)
(*   4a. overlap:          distance(c1, c2) < r1 + r2                        *)
(*   4b. disjoint:         distance(c1, c2) > r1 + r2                        *)
(*   4c. contains:         distance(c1, c2) + r_inner <= r_outer             *)
(*   4d. resolution_match: budget-lists of f1 and f2 are identical (dist=0)  *)
(*                                                                            *)
(* Disjoint is NOT the negation of overlap -- both can be BUnknown together. *)
(******************************************************************************)

(* 4a. overlap: centers closer than sum of radii. *)
Definition figures_overlap (f1 f2 : Figure) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match add_fin_b_spur (fig_radius f1) (fig_radius f2) b with
  | (sum_radii, b1, h1) =>
      match figure_distance (fig_center f1) (fig_center f2) b1 with
      | (d, b2, h2) =>
          (* fs d <= sum_radii iff d < sum_radii, strict inequality. *)
          match le_fin_b3 (fs d) sum_radii b2 with
          | (res, b3, h3) => (res, b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(* 4b. disjoint: centers farther than sum of radii. *)
Definition figures_disjoint (f1 f2 : Figure) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match add_fin_b_spur (fig_radius f1) (fig_radius f2) b with
  | (sum_radii, b1, h1) =>
      match figure_distance (fig_center f1) (fig_center f2) b1 with
      | (d, b2, h2) =>
          (* fs sum_radii <= d iff sum_radii < d, strict inequality. *)
          match le_fin_b3 (fs sum_radii) d b2 with
          | (res, b3, h3) => (res, b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(* 4c. contains: outer covers inner entirely. *)
Definition figure_contains (outer inner : Figure) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match figure_distance (fig_center outer) (fig_center inner) b with
  | (d, b1, h1) =>
      match add_fin_b_spur d (fig_radius inner) b1 with
      | (d_plus_r, b2, h2) =>
          match le_fin_b3 d_plus_r (fig_radius outer) b2 with
          | (res, b3, h3) => (res, b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(* Helper for 4d: Manhattan distance between two lists of budget values. *)
(* Same zip-sum structure as figure_distance, but over single Fin coords. *)
Fixpoint budget_list_distance (bs1 bs2 : list Fin) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match bs1, bs2 with
  | [], _           => (fz, b, fz)
  | _, []           => (fz, b, fz)
  | x1 :: rs1, x2 :: rs2 =>
      match distance x1 x2 b with
      | (d, b1, h1) =>
          match budget_list_distance rs1 rs2 b1 with
          | (drest, b2, h2) =>
              match add_fin_b_spur d drest b2 with
              | (sum, b3, h3) => (sum, b3, add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

(* 4d. resolution_match: figures look at the world with the same granularity.*)
(* BTrue iff budget-lists are identical (Manhattan distance = fz).            *)
Definition resolution_match (f1 f2 : Figure) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match budget_list_distance (fig_budgets f1) (fig_budgets f2) b with
  | (d, b1, h1) =>
      match le_fin_b3 d fz b1 with
      | (res, b2, h2) => (res, b2, add_spur h1 h2)
      end
  end.

(* ----- Zero-budget blind theorems for PART 4. ----- *)

(* Helper: budget_list_distance at budget fz is (fz, fz, fz). *)
Lemma budget_list_distance_fz : forall bs1 bs2,
  budget_list_distance bs1 bs2 fz = (fz, fz, fz).
Proof.
  intros bs1. induction bs1 as [|x1 rs1 IH].
  - intro bs2. simpl. reflexivity.
  - intro bs2. destruct bs2 as [|x2 rs2].
    + simpl. reflexivity.
    + simpl.
      destruct (distance x1 x2 fz) as [[d b1] h1] eqn:Hd.
      rewrite distance_fz in Hd. inversion Hd; subst; clear Hd.
      destruct (budget_list_distance rs1 rs2 fz) as [[drest b2] h2] eqn:Hbd.
      rewrite IH in Hbd. inversion Hbd; subst; clear Hbd.
      simpl. reflexivity.
Qed.

Theorem overlap_zero_budget_blind : forall f1 f2,
  figures_overlap f1 f2 fz = (BUnknown, fz, fz).
Proof.
  intros f1 f2.
  unfold figures_overlap.
  rewrite add_fin_b_spur_fz_local. simpl.
  rewrite figure_distance_fz. simpl.
  reflexivity.
Qed.

Theorem disjoint_zero_budget_blind : forall f1 f2,
  figures_disjoint f1 f2 fz = (BUnknown, fz, fz).
Proof.
  intros f1 f2.
  unfold figures_disjoint.
  rewrite add_fin_b_spur_fz_local. simpl.
  rewrite figure_distance_fz. simpl.
  reflexivity.
Qed.

Theorem contains_zero_budget_blind : forall outer inner,
  figure_contains outer inner fz = (BUnknown, fz, fz).
Proof.
  intros outer inner.
  unfold figure_contains.
  rewrite figure_distance_fz. simpl.
  rewrite add_fin_b_spur_fz_local. simpl.
  reflexivity.
Qed.

Theorem resolution_match_zero_budget_blind : forall f1 f2,
  resolution_match f1 f2 fz = (BUnknown, fz, fz).
Proof.
  intros f1 f2.
  unfold resolution_match.
  rewrite budget_list_distance_fz. simpl.
  reflexivity.
Qed.

(* ----- Heavy theorems for PART 4: exclusivity of disjoint vs overlap. ----- *)
(*                                                                            *)
(* Key insight: both figures_disjoint and figures_overlap share the SAME      *)
(* preparatory work (sum_radii, distance, residual budget b2). They differ   *)
(* only in the final le_fin_b3 call:                                         *)
(*   disjoint: le_fin_b3 (fs sum_radii) d          b2                        *)
(*   overlap : le_fin_b3 (fs d)          sum_radii b2                        *)
(* So we only need strict antisymmetry of le_fin_b3 at a fixed budget.       *)

(* One-step unfold for le_fin_b3 at the (fs,fs,fs) layer. Provides surgical  *)
(* rewriting without simpl's habit of recursively unfolding the inner call   *)
(* down to its body even when its budget is a variable.                      *)
Lemma le_fin_b3_fs_step : forall a b c,
  le_fin_b3 (fs (fs a)) (fs b) (fs c)
    = match le_fin_b3 (fs a) b c with
      | (r, bb, h) => (r, bb, fs h)
      end.
Proof. intros. reflexivity. Qed.

(* Strict antisymmetry: le_fin_b3 cannot simultaneously witness              *)
(*   (fs a) <= b   AND   (fs b) <= a                                         *)
(* i.e. cannot simultaneously say a < b and b < a. At fz budget both return  *)
(* BUnknown, and outside of that the Fin structure forbids both BTrue's.    *)
Lemma le_fin_b3_strict_antisymm :
  forall a b ba bb b1 h1 r2 b2 h2,
  le_fin_b3 (fs a) b ba = (BTrue, b1, h1) ->
  le_fin_b3 (fs b) a bb = (r2, b2, h2) ->
  r2 <> BTrue.
Proof.
  induction a as [| a' IHa];
    intros b ba bb b1 h1 r2 b2 h2 H1 H2 Habs; subst r2.
  - (* a = fz. H2 cannot say fs b <= fz at any budget. *)
    destruct bb as [| bb']; simpl in H2; inversion H2.
  - (* a = fs a'. Analyze H1 to pin down b and ba. *)
    destruct ba as [| ba'].
    { simpl in H1. inversion H1. }
    destruct b as [| b'].
    { simpl in H1. inversion H1. }
    rewrite le_fin_b3_fs_step in H1.
    destruct (le_fin_b3 (fs a') b' ba') as [[ri bi] hi] eqn:Ei.
    cbn iota in H1.
    inversion H1; subst; clear H1.
    (* Now analyze H2 symmetrically. *)
    destruct bb as [| bb'].
    { simpl in H2. inversion H2. }
    rewrite le_fin_b3_fs_step in H2.
    destruct (le_fin_b3 (fs b') a' bb') as [[ri2 bi2] hi2] eqn:Ei2.
    cbn iota in H2.
    inversion H2; subst; clear H2.
    (* Both inner calls return BTrue; IH closes the loop. *)
    exact (IHa _ _ _ _ _ _ _ _ Ei Ei2 eq_refl).
Qed.

(* If disjoint reports BTrue, overlap cannot also report BTrue. Both can be  *)
(* BUnknown (budget exhaustion) or one BTrue the other BFalse, but never    *)
(* both BTrue. This is the tractable half of the overlap/disjoint geometry. *)
Theorem disjoint_not_overlap :
  forall f1 f2 b rD bD hD rO bO hO,
  figures_disjoint f1 f2 b = (rD, bD, hD) ->
  figures_overlap  f1 f2 b = (rO, bO, hO) ->
  rD = BTrue ->
  rO <> BTrue.
Proof.
  intros f1 f2 b rD bD hD rO bO hO HD HO HT.
  subst rD.
  unfold figures_disjoint in HD.
  unfold figures_overlap  in HO.
  destruct (add_fin_b_spur (fig_radius f1) (fig_radius f2) b)
    as [[sum b1] hs] eqn:Esum.
  destruct (figure_distance (fig_center f1) (fig_center f2) b1)
    as [[d b2] hd2] eqn:Edist.
  destruct (le_fin_b3 (fs sum) d b2) as [[rd bd] hd] eqn:ELeD.
  destruct (le_fin_b3 (fs d) sum b2) as [[ro bo] ho] eqn:ELeO.
  inversion HD; subst; clear HD.
  inversion HO; subst; clear HO.
  exact (le_fin_b3_strict_antisymm _ _ _ _ _ _ _ _ _ ELeD ELeO).
Qed.

(* Mirror theorem: if overlap reports BTrue, disjoint cannot. *)
Theorem overlap_not_disjoint :
  forall f1 f2 b rD bD hD rO bO hO,
  figures_disjoint f1 f2 b = (rD, bD, hD) ->
  figures_overlap  f1 f2 b = (rO, bO, hO) ->
  rO = BTrue ->
  rD <> BTrue.
Proof.
  intros f1 f2 b rD bD hD rO bO hO HD HO HT.
  subst rO.
  unfold figures_disjoint in HD.
  unfold figures_overlap  in HO.
  destruct (add_fin_b_spur (fig_radius f1) (fig_radius f2) b)
    as [[sum b1] hs] eqn:Esum.
  destruct (figure_distance (fig_center f1) (fig_center f2) b1)
    as [[d b2] hd2] eqn:Edist.
  destruct (le_fin_b3 (fs sum) d b2) as [[rd bd] hd] eqn:ELeD.
  destruct (le_fin_b3 (fs d) sum b2) as [[ro bo] ho] eqn:ELeO.
  inversion HD; subst; clear HD.
  inversion HO; subst; clear HO.
  exact (le_fin_b3_strict_antisymm _ _ _ _ _ _ _ _ _ ELeO ELeD).
Qed.

(* Note on overlap_symmetric and contains_transitive:                         *)
(*                                                                            *)
(* overlap_symmetric would state figures_overlap f1 f2 b = figures_overlap    *)
(* f2 f1 b, but this fails at the budget/Spuren level because add_fin_b_spur *)
(* is not symmetric in its argument pair (it recurses on the first arg, so   *)
(* residual budget and Spuren depend on order). The Bool3 verdict IS         *)
(* commutative in the abstract semantics, but the concrete implementation    *)
(* leaves different audit trails. Proving bool3-level symmetry requires      *)
(* first proving an add_fin_b_spur symmetry lemma at the verdict projection, *)
(* which in turn needs figure_distance verdict symmetry. Both are            *)
(* architecturally missing and deferred to a future round.                   *)
(*                                                                            *)
(* contains_transitive would state figure_contains A B b = BTrue AND         *)
(* figure_contains B C b = BTrue -> figure_contains A C b = BTrue. This      *)
(* requires a triangle inequality on figure_distance that currently does     *)
(* not exist in the codebase; adding it means proving                        *)
(*   figure_distance x z b <= figure_distance x y b + figure_distance y z b  *)
(* at the verdict level, which is a substantial lemma. Also deferred.        *)

(******************************************************************************)
(* PART 5: Diagonal relations -- self-blind patterns lifted to figures.       *)
(*                                                                            *)
(* The base primitives live in void_probability_geometry:                     *)
(*   self_blind      : bool3_of (le_fin_b3 n n n)      = BUnknown             *)
(*   void_productive : bool3_of (le_fin_b3 n n (fs n)) = BTrue                *)
(*                                                                            *)
(* For figures we lift these conditionally: IF figure_distance yields a       *)
(* post-state in which the outer le_fin_b3 call reduces to the self_blind /   *)
(* void_productive shape, THEN recognize inherits that verdict.               *)
(*                                                                            *)
(* Unconditional witnesses (concrete figures and signals) are deferred to    *)
(* PART 9. These conditional lifts express the structural content: no matter *)
(* how the distance was computed, running out at the radius is blind, and    *)
(* exactly one tick more is productive.                                       *)
(******************************************************************************)

(* PART 5a. Diagonal figure blind.                                            *)
(* If the distance computation leaves residual budget = radius and returns a  *)
(* distance equal to the radius, recognize saturates at BUnknown.             *)
Theorem recognize_boundary_blind : forall signal fig b h,
  figure_distance signal (fig_center fig) b = (fig_radius fig, fig_radius fig, h) ->
  bool3_of (recognize signal fig b) = BUnknown.
Proof.
  intros signal fig b h Hfd.
  unfold recognize.
  rewrite Hfd.
  destruct (le_fin_b3 (fig_radius fig) (fig_radius fig) (fig_radius fig))
    as [[res bx] hx] eqn:Hle.
  unfold bool3_of. simpl.
  pose proof (self_blind (fig_radius fig)) as Hsb.
  unfold bool3_of in Hsb. rewrite Hle in Hsb. simpl in Hsb. exact Hsb.
Qed.

(* PART 5b. One tick off the diagonal -- productive.                          *)
(* If residual budget after distance equals fs (fig_radius fig) and distance  *)
(* equals the radius, recognize resolves to BTrue.                            *)
Theorem recognize_one_tick_productive : forall signal fig b h,
  figure_distance signal (fig_center fig) b
    = (fig_radius fig, fs (fig_radius fig), h) ->
  bool3_of (recognize signal fig b) = BTrue.
Proof.
  intros signal fig b h Hfd.
  unfold recognize.
  rewrite Hfd.
  destruct (le_fin_b3 (fig_radius fig) (fig_radius fig) (fs (fig_radius fig)))
    as [[res bx] hx] eqn:Hle.
  unfold bool3_of. simpl.
  pose proof (void_productive (fig_radius fig)) as Hvp.
  unfold bool3_of in Hvp. rewrite Hle in Hvp. simpl in Hvp. exact Hvp.
Qed.

(* PART 5c. Diagonal pattern: for a pattern on the value=budget diagonal,     *)
(* the le_fin_b3 n n n self-blind applies directly.                           *)
Corollary pattern_diagonal_blind : forall n,
  bool3_of (le_fin_b3 n n n) = BUnknown.
Proof. intro n. apply self_blind. Qed.

(* PART 5d. Off-diagonal pattern: one extra tick of budget resolves.          *)
Corollary pattern_diagonal_productive : forall n,
  bool3_of (le_fin_b3 n n (fs n)) = BTrue.
Proof. intro n. apply void_productive. Qed.

(* ----- Unconditional concrete witnesses for PART 5. -----                   *)

(* The minimal figure: empty center, zero radius. At budget fz, signal = the *)
(* (empty) center, distance saturates at fz = radius, residual budget = fz = *)
(* radius -- exactly the self-blind shape. At budget fs fz, the residual is *)
(* one tick above the radius -- exactly the void_productive shape.           *)
Definition fig_empty : Figure := mkFigure [] fz.

(* Concrete witness: recognize gets stuck at BUnknown precisely because the  *)
(* figure_distance output saturates the self-blind pattern of le_fin_b3.    *)
(* Instantiates recognize_boundary_blind at the minimal witness.             *)
Theorem diagonal_figure_blind :
  bool3_of (recognize [] fig_empty fz) = BUnknown.
Proof. eapply recognize_boundary_blind. reflexivity. Qed.

(* Concrete witness: one tick of budget above the radius turns the verdict  *)
(* from BUnknown to BTrue. Instantiates recognize_one_tick_productive at    *)
(* the minimal witness.                                                      *)
Theorem off_diagonal_productive :
  bool3_of (recognize [] fig_empty (fs fz)) = BTrue.
Proof. eapply recognize_one_tick_productive. reflexivity. Qed.

(* Sanity -- the witnesses compute to the claimed verdicts.                  *)
Eval compute in recognize [] fig_empty fz.
(* expected: (BUnknown, fz, fz) *)
Eval compute in recognize [] fig_empty (fs fz).
(* expected: (BTrue,    fz, fs fz) *)

(******************************************************************************)
(* PART 3 (deferred): recognize_cost_positive                                 *)
(*                                                                            *)
(* No free lunch at the figure level. Budget > fz and both lists non-empty   *)
(* forces Spuren > fz. Every recognition move leaves a trace -- there is no  *)
(* silent observation.                                                        *)
(*                                                                            *)
(* Chain of no-free-lunch lemmas, working bottom-up:                          *)
(*   le_fin_b3       (existing: no_free_lunch_le, void_finite_minimal)        *)
(*   le_fin_b_spur   (new: no_free_lunch_le_spur_local)                       *)
(*   distance        (new: distance_cost_positive)                            *)
(*   pattern_distance(new: pattern_distance_cost_positive)                    *)
(*   figure_distance (new: figure_distance_cons_cost_positive)                *)
(*   recognize       (theorem: recognize_cost_positive)                       *)
(******************************************************************************)

(* Utility: fs-ness survives add_spur on the left. *)
Lemma add_spur_neq_fz_l : forall a b, a <> fz -> add_spur a b <> fz.
Proof.
  intros a b Ha. destruct a as [| a'].
  - contradiction.
  - rewrite add_spur_fs_l. discriminate.
Qed.

(* le_fin_b_spur inherits no_free_lunch from le_fin_b3. *)
Lemma no_free_lunch_le_spur_local : forall n m b res b' h,
  le_fin_b_spur n m (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros n m b res b' h Heq.
  unfold le_fin_b_spur in Heq.
  destruct (le_fin_b3 n m (fs b)) as [[r bx] hx] eqn:Hle.
  inversion Heq; subst.
  exact (no_free_lunch_le _ _ _ _ _ _ Hle).
Qed.

(* distance costs at least one tick when budget > fz. *)
Lemma distance_cost_positive : forall p q b res b' h,
  distance p q (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros p q b res b' h Heq.
  unfold distance in Heq.
  destruct (le_fin_b_spur p q (fs b)) as [[r bx] hx] eqn:Hle.
  assert (Hhx: hx <> fz)
    by exact (no_free_lunch_le_spur_local _ _ _ _ _ _ Hle).
  destruct r.
  - destruct (sub_saturate_b_spur q p bx) as [[d byz] hy] eqn:Hsub.
    inversion Heq; subst.
    apply add_spur_neq_fz_l; exact Hhx.
  - destruct (sub_saturate_b_spur p q bx) as [[d byz] hy] eqn:Hsub.
    inversion Heq; subst.
    apply add_spur_neq_fz_l; exact Hhx.
Qed.

(* pattern_distance inherits cost from the first distance call. *)
Lemma pattern_distance_cost_positive : forall p1 p2 b res b' h,
  pattern_distance p1 p2 (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros p1 p2 b res b' h Heq.
  unfold pattern_distance in Heq.
  destruct (distance (pattern_value p1) (pattern_value p2) (fs b))
    as [[dv b1] h1] eqn:Hd1.
  assert (Hh1: h1 <> fz)
    by exact (distance_cost_positive _ _ _ _ _ _ Hd1).
  destruct (distance (pattern_budget p1) (pattern_budget p2) b1)
    as [[db b2] h2] eqn:Hd2.
  destruct (add_fin_b_spur dv db b2) as [[sum b3] h3] eqn:Hadd.
  inversion Heq; subst.
  apply add_spur_neq_fz_l; exact Hh1.
Qed.

(* figure_distance on two non-empty lists inherits cost from the head. *)
Lemma figure_distance_cons_cost_positive :
  forall p1 p2 rs1 rs2 b res b' h,
  figure_distance (p1 :: rs1) (p2 :: rs2) (fs b) = (res, b', h) ->
  h <> fz.
Proof.
  intros p1 p2 rs1 rs2 b res b' h Heq.
  simpl in Heq.
  destruct (pattern_distance p1 p2 (fs b)) as [[d b1] h1] eqn:Hpd.
  assert (Hh1: h1 <> fz)
    by exact (pattern_distance_cost_positive _ _ _ _ _ _ Hpd).
  destruct (figure_distance rs1 rs2 b1) as [[drest b2] h2] eqn:Hfd.
  destruct (add_fin_b_spur d drest b2) as [[sum b3] h3] eqn:Hadd.
  inversion Heq; subst.
  apply add_spur_neq_fz_l; exact Hh1.
Qed.

(* THEOREM: Recognition always costs Spuren when budget is positive and       *)
(* both signal and fig_center are non-empty. The figure-level "no free lunch".*)
Theorem recognize_cost_positive :
  forall p1 rs1 p2 rs2 r b res b' h,
  recognize (p1 :: rs1) (mkFigure (p2 :: rs2) r) (fs b) = (res, b', h) ->
  h <> fz.
Proof.
  intros p1 rs1 p2 rs2 r b res b' h Heq.
  unfold recognize in Heq.
  (* Reduce both Record projections; do NOT unfold figure_distance. *)
  cbn [fig_center fig_radius] in Heq.
  destruct (figure_distance (p1 :: rs1) (p2 :: rs2) (fs b))
    as [[dist b1] h1] eqn:Hfd.
  assert (Hh1: h1 <> fz)
    by exact (figure_distance_cons_cost_positive _ _ _ _ _ _ _ _ Hfd).
  destruct (le_fin_b3 dist r b1) as [[res2 b2] h2] eqn:Hle.
  inversion Heq; subst.
  apply add_spur_neq_fz_l; exact Hh1.
Qed.

(******************************************************************************)
(* PART 6: Projection -- dimensional compression.                             *)
(*                                                                            *)
(* project signal k = the first k coordinates of signal.                      *)
(* Discarding a coordinate leaves a trace (Spuren) even though you never     *)
(* looked at it. Forgetting is an act. Budget is not consumed (no measurement *)
(* happens on discarded coords), but the act of forgetting is recorded.      *)
(******************************************************************************)

(* Structural projection: take the first k coordinates. *)
Fixpoint project (signal : list Pattern) (k : Fin) : list Pattern :=
  match k, signal with
  | fz, _         => []
  | _, []         => []
  | fs k', p :: rs => p :: project rs k'
  end.

(* Number of coordinates discarded by projection. *)
Fixpoint discard_count (signal : list Pattern) (k : Fin) : Fin :=
  match signal with
  | []      => fz
  | _ :: rs =>
      match k with
      | fz     => fs (discard_count rs fz)
      | fs k'  => discard_count rs k'
      end
  end.

(* Projection with cost accounting.                                           *)
(* Budget is passed through untouched (no measurement).                       *)
(* Spuren records the act of discarding -- one tick per dropped coordinate.  *)
Definition projection_cost (signal : list Pattern) (k : Fin) (b : Budget)
  : (list Pattern * Budget * Spuren) :=
  (project signal k, b, discard_count signal k).

(* ----- Structural lemmas on project ----- *)

Lemma project_fz : forall s, project s fz = [].
Proof. intro s. destruct s; reflexivity. Qed.

Lemma project_nil : forall k, project [] k = [].
Proof. intro k. destruct k; reflexivity. Qed.

(* Projection on a non-empty list at fs k' unfolds by taking the head. *)
Lemma project_cons : forall p rs k',
  project (p :: rs) (fs k') = p :: project rs k'.
Proof. intros p rs k'. reflexivity. Qed.

(* ----- Structural lemmas on discard_count ----- *)

Lemma discard_count_nil : forall k, discard_count [] k = fz.
Proof. intro k. reflexivity. Qed.

(* At k=fz, every coordinate is discarded. *)
Lemma discard_count_fz : forall s, discard_count s fz = length_fin s.
Proof.
  intro s. induction s as [| p rs IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* At fs k', the head is kept; discard count comes from the tail. *)
Lemma discard_count_cons_fs : forall p rs k',
  discard_count (p :: rs) (fs k') = discard_count rs k'.
Proof. intros p rs k'. reflexivity. Qed.

(* ----- THEOREMS ----- *)

(* Structural content of "projection loses information":                     *)
(* If two signals agree on their head and their tails agree under k'-projection*)
(* then they agree under (fs k')-projection. This is the functoriality of    *)
(* project on prefix-equivalence.                                             *)
Theorem projection_loses_information :
  forall p rs1 rs2 k',
  project rs1 k' = project rs2 k' ->
  project (p :: rs1) (fs k') = project (p :: rs2) (fs k').
Proof.
  intros p rs1 rs2 k' Heq.
  rewrite !project_cons. rewrite Heq. reflexivity.
Qed.

(* Consequence: whatever the tails look like BEYOND the first k' positions,  *)
(* if their k'-projections match, the (fs k')-projections of the extended    *)
(* lists also match. Information past index k' is lost.                      *)

(* THEOREM: projection_cost at zero k discards everything.                    *)
(* Spuren equals the full length of the original signal.                      *)
Theorem projection_cost_total_erasure : forall s b,
  projection_cost s fz b = ([], b, length_fin s).
Proof.
  intros s b. unfold projection_cost.
  rewrite project_fz. rewrite discard_count_fz.
  reflexivity.
Qed.

(* THEOREM: projection on empty signal is free.                               *)
Theorem projection_cost_empty_free : forall k b,
  projection_cost [] k b = ([], b, fz).
Proof.
  intros k b. unfold projection_cost.
  rewrite project_nil. reflexivity.
Qed.

(* THEOREM: projection_costs_less (structural form).                          *)
(* Discarding anything (non-empty signal, k=fz) costs at least one tick.     *)
Theorem projection_discard_costs :
  forall p rs b,
  exists h, projection_cost (p :: rs) fz b = ([], b, fs h).
Proof.
  intros p rs b. unfold projection_cost.
  simpl discard_count.
  rewrite discard_count_fz.
  exists (length_fin rs).
  rewrite project_fz. reflexivity.
Qed.

(* THEOREM: projection_preserves_recognition (degenerate cases).             *)
(* Projecting to k=fz against the empty/zero-radius figure is blind at zero  *)
(* budget and immediately positive at any non-zero budget.                    *)
Theorem projection_preserves_recognition_zero_budget :
  forall signal,
  recognize (project signal fz) (mkFigure [] fz) fz = (BUnknown, fz, fz).
Proof.
  intro signal. rewrite project_fz. apply recognize_zero_budget_blind.
Qed.

(******************************************************************************)
(* PART 7: Vocabulary -- lookup in a dictionary of figures.                   *)
(*                                                                            *)
(* Vocabulary is a list of figures. Lookup walks the vocabulary sequentially. *)
(*                                                                            *)
(* Policy on BUnknown: conservative. If recognize returns BUnknown we cannot  *)
(* decide whether the signal matches, so we abort lookup and return None.    *)
(* We do NOT keep scanning -- a principled 'I don't know' ends the search.   *)
(* BFalse continues to the next entry. BTrue commits to the first match.    *)
(*                                                                            *)
(* Communication cost accounts for sender projection + receiver lookup.     *)
(******************************************************************************)

Definition Vocabulary := list Figure.

(* Sequential lookup in a vocabulary. Returns the first BTrue match, or None *)
(* either when the vocabulary is exhausted or recognition becomes undecided.*)
Fixpoint lookup (signal : list Pattern) (vocab : Vocabulary) (b : Budget)
  : (option Figure * Budget * Spuren) :=
  match vocab with
  | []          => (None, b, fz)
  | fig :: rest =>
      match recognize signal fig b with
      | (BTrue,   b', h1) => (Some fig, b', h1)
      | (BFalse,  b', h1) =>
          match lookup signal rest b' with
          | (result, b'', h2) => (result, b'', add_spur h1 h2)
          end
      | (BUnknown, b', h1) => (None, b', h1)
      end
  end.

(* Communication cost: sender projects (paying Spuren for discarded coords),  *)
(* receiver looks up the projected signal. Returns both Spuren tallies.      *)
Definition communication_cost
    (signal : list Pattern)
    (proj_dim : Fin)
    (vocab : Vocabulary)
    (b_sender b_receiver : Budget)
  : (Spuren * Spuren) :=
  match projection_cost signal proj_dim b_sender with
  | (projected, _, h_send) =>
      match lookup projected vocab b_receiver with
      | (_, _, h_recv) => (h_send, h_recv)
      end
  end.

(* ----- Structural lemmas ----- *)

Lemma lookup_empty_vocab : forall signal b,
  lookup signal [] b = (None, b, fz).
Proof. intros signal b. reflexivity. Qed.

(* At budget fz, the first recognize returns BUnknown, and lookup bails.     *)
Lemma lookup_zero_budget_stops : forall signal fig rest,
  lookup signal (fig :: rest) fz = (None, fz, fz).
Proof.
  intros signal fig rest. simpl.
  rewrite recognize_zero_budget_blind. reflexivity.
Qed.

(* ----- THEOREMS ----- *)

(* THEOREM: larger_vocab_costs_more (structural form).                        *)
(* If lookup exhausted the first vocab (returned None via BFalse chain),    *)
(* then appending more figures makes it check at least one more recognition. *)
(* Formally -- the BFalse-branch is the only way costs accumulate across    *)
(* vocab entries.                                                             *)
Lemma lookup_bfalse_continues :
  forall signal fig rest b b' h1,
  recognize signal fig b = (BFalse, b', h1) ->
  exists result b'' h2,
    lookup signal (fig :: rest) b = (result, b'', add_spur h1 h2) /\
    lookup signal rest b' = (result, b'', h2).
Proof.
  intros signal fig rest b b' h1 Hrec.
  simpl. rewrite Hrec.
  destruct (lookup signal rest b') as [[result b''] h2] eqn:Hl.
  exists result, b'', h2. split; reflexivity.
Qed.

(* THEOREM: at zero budget, lookup returns None regardless of vocab/signal. *)
Theorem lookup_zero_budget_blind :
  forall signal vocab,
  lookup signal vocab fz = (None, fz, fz).
Proof.
  intros signal vocab. destruct vocab as [| fig rest].
  - reflexivity.
  - apply lookup_zero_budget_stops.
Qed.

(* THEOREM: communication_always_costs_sender -- when discarding.            *)
(* If proj_dim = fz and signal is non-empty, sender pays Spuren > fz.       *)
Theorem communication_sender_costs_positive :
  forall p rs vocab b_sender b_receiver h_s h_r,
  communication_cost (p :: rs) fz vocab b_sender b_receiver = (h_s, h_r) ->
  h_s <> fz.
Proof.
  intros p rs vocab b_sender b_receiver h_s h_r Heq.
  unfold communication_cost in Heq.
  rewrite projection_cost_total_erasure in Heq.
  (* Heq : match ([], b_sender, length_fin (p :: rs)) with
              (projected, _, h_send) =>
              match lookup projected vocab b_receiver with
                (_, _, h_recv) => (h_send, h_recv)
              end
           end = (h_s, h_r) *)
  cbn iota in Heq.
  destruct (lookup [] vocab b_receiver) as [[o br] hr].
  inversion Heq; subst.
  simpl. discriminate.
Qed.

(* THEOREM: projection_increases_ambiguity.                                   *)
(* After fz-projection the signal is empty. On empty signal, figure_distance *)
(* with any figure is fz, so at sufficient budget every figure "matches".    *)
(* Concretely: two distinct figures both look the same from the empty prefix.*)
Theorem projection_collapses_signals_at_fz :
  forall s1 s2,
  project s1 fz = project s2 fz.
Proof.
  intros s1 s2. rewrite !project_fz. reflexivity.
Qed.

(* THEOREM: communication with empty vocabulary has zero receiver cost.      *)
Theorem communication_empty_vocab_receiver_free :
  forall signal proj_dim b_sender b_receiver,
  communication_cost signal proj_dim [] b_sender b_receiver
  = (discard_count signal proj_dim, fz).
Proof.
  intros signal proj_dim b_sender b_receiver.
  unfold communication_cost, projection_cost.
  simpl. reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*  PART 8 -- COLLECTIVE THEOREMS                                             *)
(*                                                                            *)
(*  Three slogans in finitist dress:                                          *)
(*                                                                            *)
(*  - no_free_communication: any non-empty message communicated by full      *)
(*    projection (fz) costs the sender nonzero Spuren -- there is no free    *)
(*    channel.                                                                *)
(*                                                                            *)
(*  - partial_vocabulary_sufficient: a vocabulary of a single figure already *)
(*    suffices to discriminate a positively-recognized signal. Precision     *)
(*    scales with K: K figures give K commitments, but even K = 1 lifts      *)
(*    recognition into lookup at the same budget/Spuren profile.              *)
(*                                                                            *)
(*  - vocabulary_convergence (Pawlak for figures): if two figures give the   *)
(*    same recognize response at the same budget, single-figure lookups      *)
(*    return at identical cost profiles -- naming their respective figures   *)
(*    is the only operational difference. From the measurement side they     *)
(*    are indistinguishable.                                                  *)
(*                                                                            *)
(******************************************************************************)

(* Corollary of communication_sender_costs_positive: at full projection on a  *)
(* non-empty signal, at least one actor paid.                                 *)
Theorem no_free_communication :
  forall p rs vocab b_sender b_receiver h_s h_r,
  communication_cost (p :: rs) fz vocab b_sender b_receiver = (h_s, h_r) ->
  h_s <> fz \/ h_r <> fz.
Proof.
  intros p rs vocab b_sender b_receiver h_s h_r Heq.
  left.
  exact (communication_sender_costs_positive _ _ _ _ _ _ _ Heq).
Qed.

(* A single-figure vocabulary already distinguishes a positively-recognized   *)
(* signal -- at exactly the cost that recognize paid.                         *)
Theorem partial_vocabulary_sufficient :
  forall signal fig b b' h,
  recognize signal fig b = (BTrue, b', h) ->
  lookup signal [fig] b = (Some fig, b', h).
Proof.
  intros signal fig b b' h Hrec.
  simpl. rewrite Hrec. reflexivity.
Qed.

(* Dual: a BFalse on a singleton vocabulary yields None at the same cost     *)
(* (the remainder [] contributes zero Spuren, which add_spur absorbs on the  *)
(* right).                                                                   *)
Theorem partial_vocabulary_rejects :
  forall signal fig b b' h,
  recognize signal fig b = (BFalse, b', h) ->
  lookup signal [fig] b = (None, b', h).
Proof.
  intros signal fig b b' h Hrec.
  simpl. rewrite Hrec. simpl. reflexivity.
Qed.

(* Pawlak-in-figures: if two figures give the same recognize response at the *)
(* same budget, their singleton-vocab lookups return identical cost profiles, *)
(* only differing in which figure is named.                                   *)
Theorem vocabulary_convergence :
  forall signal f1 f2 b b' h,
  recognize signal f1 b = (BTrue, b', h) ->
  recognize signal f2 b = (BTrue, b', h) ->
  lookup signal [f1] b = (Some f1, b', h) /\
  lookup signal [f2] b = (Some f2, b', h).
Proof.
  intros signal f1 f2 b b' h Hr1 Hr2. split.
  - simpl. rewrite Hr1. reflexivity.
  - simpl. rewrite Hr2. reflexivity.
Qed.

(* Convergence under rejection: two figures both giving BFalse at same cost  *)
(* yield identical lookup behavior (both rejected, same cost).               *)
Theorem vocabulary_convergence_reject :
  forall signal f1 f2 b b' h,
  recognize signal f1 b = (BFalse, b', h) ->
  recognize signal f2 b = (BFalse, b', h) ->
  lookup signal [f1] b = lookup signal [f2] b.
Proof.
  intros signal f1 f2 b b' h Hr1 Hr2.
  rewrite (partial_vocabulary_rejects _ _ _ _ _ Hr1).
  rewrite (partial_vocabulary_rejects _ _ _ _ _ Hr2).
  reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*  PART 9 -- CONCRETE WITNESS                                                *)
(*                                                                            *)
(*  Small 2D examples: three figures, two signals, evaluated under           *)
(*  Eval compute to show that the machinery reduces to concrete Bool3 tags   *)
(*  and concrete Spuren tallies.                                              *)
(*                                                                            *)
(******************************************************************************)

(* Local finite literals, kept small to keep reduction tractable. *)
Definition f1' : Fin := fs fz.
Definition f2' : Fin := fs (fs fz).
Definition f3' : Fin := fs (fs (fs fz)).
Definition f4' : Fin := fs (fs (fs (fs fz))).
Definition f5' : Fin := fs f4'.
Definition f6' : Fin := fs f5'.
Definition f7' : Fin := fs f6'.
Definition f8' : Fin := fs f7'.

(* Doubling helper so we can write big constants without pages of fs. *)
Fixpoint double_fin (n : Fin) : Fin :=
  match n with
  | fz     => fz
  | fs n'  => fs (fs (double_fin n'))
  end.

Definition f16' : Fin := double_fin f8'.
Definition f32' : Fin := double_fin f16'.
Definition f64' : Fin := double_fin f32'.

(* Three figures in 2D pattern space.                                         *)
(*                                                                            *)
(*   fig_high : high-value figure with ample budget per coord, tight radius. *)
(*   fig_low  : low-value figure, same budget profile.                       *)
(*   fig_blur : diagonal (value = budget) figure -> self-blind witness.      *)
Definition fig_high : Figure := mkFigure [(f2', f4'); (f1', f4')] f1'.
Definition fig_low  : Figure := mkFigure [(fz , f4'); (f2', f4')] f1'.
Definition fig_blur : Figure := mkFigure [(f1', f1'); (f1', f1')] f2'.

(* Two signals. *)
Definition sig_near_high : list Pattern := [(f2', f8'); (f1', f8')].
Definition sig_between   : list Pattern := [(f1', f4'); (f1', f4')].

(* ----- Eval compute witnesses ----- *)

(* recognize sig_near_high against fig_high at budget f64'.                   *)
(* Signal values match fig_high exactly; budgets differ (f8' vs f4'),       *)
(* but radius f1' is tolerant enough. *)
Eval compute in recognize sig_near_high fig_high f64'.

(* recognize sig_near_high against fig_low: first coord value differs (f2 vs fz).*)
Eval compute in recognize sig_near_high fig_low  f64'.

(* Overlap vs disjoint for fig_high and fig_low. *)
Eval compute in figures_overlap  fig_high fig_low f64'.
Eval compute in figures_disjoint fig_high fig_low f64'.

(* Resolution match: fig_high has per-coord budgets f4', fig_blur f1'.      *)
(* They look at different resolutions. *)
Eval compute in resolution_match fig_high fig_blur f64'.
Eval compute in resolution_match fig_high fig_low  f64'.

(* Projection: drop second coordinate, keep just first. *)
Eval compute in project         sig_near_high f1'.
Eval compute in projection_cost sig_near_high f1' f64'.

(* Lookup in a two-entry vocabulary. *)
Definition demo_vocab : Vocabulary := [fig_high; fig_low].
Eval compute in lookup sig_near_high demo_vocab f64'.

(* Communication cost: project down to first coord, then lookup. *)
Eval compute in communication_cost sig_near_high f1' demo_vocab f64' f64'.

(* fig_blur evaluated against itself: dist = 0 (exact match), radius = f2,  *)
(* so le_fin_b3 returns BTrue at large budget. A figure DOES recognize its *)
(* own center when well-funded. *)
Eval compute in recognize (fig_center fig_blur) fig_blur f64'.

(* Low-budget blindness: same query at f2' is insufficient -- figure_distance *)
(* alone burns the budget, forcing le_fin_b3 into BUnknown territory.        *)
Eval compute in recognize sig_near_high fig_high f2'.

(******************************************************************************)
(*                                                                            *)
(*  PART 10 -- ASYMMETRY AS POSITIVE CONTENT                                  *)
(*                                                                            *)
(*  Classical geometry, inherited from the 19th century (Peano, Cantor),     *)
(*  assumes symmetry: d(x,y) = d(y,x), overlap(A,B) = overlap(B,A), plus a   *)
(*  transitivity closure on containment. VOID rejects those assumptions at   *)
(*  the foundation, because every operation here carries a concrete budget   *)
(*  cost and emits a concrete Spuren tally, and those costs are not          *)
(*  symmetric. The primitive `add_fin_b_spur n m b` recurses on m: the       *)
(*  number of fs-unwrappings, the remaining budget, and the Spuren tally     *)
(*  all depend on which argument occupies the recursive slot. This is not    *)
(*  an accident to be patched away; it encodes the thesis that observation   *)
(*  in one direction is not the same observation as in the other.            *)
(*                                                                            *)
(*  The theorems below therefore do not try to prove symmetry. They prove    *)
(*  the opposite: we exhibit concrete finite witnesses where swapping        *)
(*  arguments changes the observable (result, remaining budget, Spuren)      *)
(*  tuple. Asymmetry is provable content, not absent content.                *)
(*                                                                            *)
(*  Consequence for the deferred list (see RAPORT_FIGURY.md): the earlier    *)
(*  `overlap_symmetric` and `contains_transitive` entries are NOT deferred;  *)
(*  they are REJECTED. Their classical statement is incompatible with the   *)
(*  finitist accounting of VOID, and the theorems in this part formalise    *)
(*  exactly why.                                                              *)
(*                                                                            *)
(******************************************************************************)

(* 10a. add_fin_b_spur is not symmetric in its first two arguments.          *)
(*                                                                            *)
(* Concrete trace at n = fz, m = f1', b = f2':                               *)
(*   add_fin_b_spur fz f1' f2' takes the fs m' / fs b' branch once,         *)
(*   consumes one budget unit and emits one Spuren unit                     *)
(*   -> result tuple (f1', f1', f1').                                       *)
(*   add_fin_b_spur f1' fz f2' hits the fz / _ branch immediately,          *)
(*   consumes nothing                                                        *)
(*   -> result tuple (f1', f2', fz).                                        *)
(* The sum is the same finite value f1'; the cost and the trace differ.     *)
Theorem add_fin_b_spur_order_asymmetric :
  add_fin_b_spur fz f1' f2' <> add_fin_b_spur f1' fz f2'.
Proof.
  compute. intro H. inversion H.
Qed.

(* 10b. The asymmetry of the primitive surfaces in figures_overlap.         *)
(* figures_overlap computes the radius sum as add_fin_b_spur r1 r2 b, with  *)
(* r1 on the left, so swapping f1 and f2 swaps the arguments of the adder  *)
(* and changes the budget that figure_distance then sees, and the Spuren   *)
(* accumulated along the way.                                               *)
Definition fig_zero_radius : Figure := mkFigure [] fz.
Definition fig_unit_radius : Figure := mkFigure [] f1'.

Theorem figures_overlap_order_asymmetric :
  figures_overlap fig_zero_radius fig_unit_radius f2'
  <> figures_overlap fig_unit_radius fig_zero_radius f2'.
Proof.
  compute. intro H. inversion H.
Qed.

(* 10c. Same asymmetry infects figures_disjoint, which also routes the      *)
(* radii through the same asymmetric adder.                                 *)
Theorem figures_disjoint_order_asymmetric :
  figures_disjoint fig_zero_radius fig_unit_radius f2'
  <> figures_disjoint fig_unit_radius fig_zero_radius f2'.
Proof.
  compute. intro H. inversion H.
Qed.

(* 10d. figure_contains likewise. Here the asymmetry is structurally even   *)
(* stronger: the outer and inner roles are built into the definition, so   *)
(* swapping them is a change of meaning, not just a change of cost.        *)
(* We make that explicit with a concrete witness where the verdict itself  *)
(* flips side.                                                              *)
Definition fig_small : Figure := mkFigure [] f1'.
Definition fig_big   : Figure := mkFigure [] f4'.

Theorem figure_contains_order_asymmetric :
  figure_contains fig_big fig_small f8'
  <> figure_contains fig_small fig_big f8'.
Proof.
  compute. intro H. inversion H.
Qed.

(* ----- Inspectable reductions ----- *)

(* Readers can check the asymmetry by eye by comparing these four tuples.   *)
Eval compute in add_fin_b_spur fz f1' f2'.
Eval compute in add_fin_b_spur f1' fz f2'.
Eval compute in figures_overlap  fig_zero_radius fig_unit_radius f2'.
Eval compute in figures_overlap  fig_unit_radius fig_zero_radius f2'.
Eval compute in figure_contains  fig_big          fig_small        f8'.
Eval compute in figure_contains  fig_small        fig_big          f8'.
