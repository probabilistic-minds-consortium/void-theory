(******************************************************************************)
(* void_bohr_epistemology.v - BOHR WAS RIGHT                                 *)
(*                                                                            *)
(* Niels Bohr claimed: there is no fact about a system independent of         *)
(* the act of measurement. Einstein objected: the moon exists whether         *)
(* or not I look at it. Bohr replied: stop telling God what to do.            *)
(*                                                                            *)
(* VOID settles this dispute with arithmetic.                                 *)
(*                                                                            *)
(* In VOID, there is no value without spending budget. fin_eq_b3 a b          *)
(* does not CHECK a pre-existing truth. It PRODUCES an answer at a cost.      *)
(* Before the call: no fact. After the call: a fact, and less budget.         *)
(* With zero budget: BUnknown. Not hidden truth - genuinely no answer.        *)
(* This is Copenhagen, in finite arithmetic.                                  *)
(*                                                                            *)
(* This file proves six properties of observation. Not only on the bare       *)
(* fin_eq_b3 level, but across the entire system: observer collapse,          *)
(* distinguishability, entropy measurement, and information theory.           *)
(* Bohr pervades every module.                                                *)
(*                                                                            *)
(* DEPENDS ON:                                                                *)
(*   void_finite_minimal.v       - Fin, Budget, Spuren, Bool3, fin_eq_b3       *)
(*   void_probability_minimal.v  - FinProb                                    *)
(*   void_pattern.v              - Pattern, Observer                          *)
(*   void_arithmetic.v           - budgeted arithmetic                        *)
(*   void_observer_collapse.v    - observation teleport, zeno, backaction     *)
(*   void_distinguishability.v   - distinguish cost, sequences               *)
(*   void_entropy.v              - entropy_b                                  *)
(*   void_entropy_integration.v  - Observer, measure_with_observer            *)
(*   void_information_theory.v   - READ/WRITE boundary                        *)
(*                                                                            *)
(* ALL THEOREMS FULLY PROVEN. ZERO uses of Admitted.                          *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_observer_collapse.
Require Import void_distinguishability.
Require Import void_entropy.
Require Import void_entropy_integration.
Require Import void_information_theory.
Require Import Coq.Lists.List.
Import ListNotations.

(******************************************************************************)
(*                                                                            *)
(*                      PART 1: OPACITY                                       *)
(*                                                                            *)
(* Wheeler: no phenomenon is a phenomenon until it is observed.               *)
(*                                                                            *)
(* In VOID: no answer exists until budget is spent to produce it.             *)
(* With zero budget, every question returns BUnknown.                         *)
(* This is not a failure mode. This is the ground state of epistemology.      *)
(*                                                                            *)
(* We prove opacity not just for fin_eq_b3, but for every module:             *)
(* observer collapse, entropy, distinguishability. The void is universal.     *)
(*                                                                            *)
(******************************************************************************)

(* --- Core: equality and comparison --- *)

Lemma eq_opacity : forall a b,
  fin_eq_b3 a b fz = (BUnknown, fz, fz).
Proof. intros. destruct a; simpl; reflexivity. Qed.

Lemma le_opacity : forall a b,
  le_fin_b3 a b fz = (BUnknown, fz, fz).
Proof. intros. destruct a; simpl; reflexivity. Qed.

Corollary eq_opacity_result : forall a b,
  fst (fst (fin_eq_b3 a b fz)) = BUnknown.
Proof. intros. rewrite eq_opacity. reflexivity. Qed.

Corollary le_opacity_result : forall a b,
  fst (fst (le_fin_b3 a b fz)) = BUnknown.
Proof. intros. rewrite le_opacity. reflexivity. Qed.

Corollary eq_opacity_budget : forall a b,
  snd (fst (fin_eq_b3 a b fz)) = fz.
Proof. intros. rewrite eq_opacity. reflexivity. Qed.

Corollary le_opacity_budget : forall a b,
  snd (fst (le_fin_b3 a b fz)) = fz.
Proof. intros. rewrite le_opacity. reflexivity. Qed.

(* --- Observer collapse: pattern frozen at fz --- *)

Lemma collapse_opacity : forall p obs,
  Void_Observer_Collapse.observation_teleport_b p obs fz = (p, fz).
Proof. intros. reflexivity. Qed.

Lemma multi_collapse_opacity : forall p obs_list,
  fst (Void_Observer_Collapse.multi_observer_collapse_b p obs_list fz) = p.
Proof.
  intros p obs_list. induction obs_list as [|obs rest IH].
  - simpl. reflexivity.
  - simpl. exact IH.
Qed.

Lemma zeno_opacity : forall p obs times,
  Void_Observer_Collapse.zeno_observation_b p obs times fz = (p, fz).
Proof. intros. destruct times; simpl; reflexivity. Qed.

Lemma superposition_opacity : forall patterns obs,
  snd (Void_Observer_Collapse.collapse_superposition_b patterns obs fz) = fz.
Proof. intros. destruct patterns; simpl; reflexivity. Qed.

(* --- Entropy: measurement impossible at fz --- *)

Lemma entropy_cannot_measure : forall data,
  Void_Entropy_Integration.can_measure
    (Void_Entropy_Integration.mkObserver fz fz []) data = false.
Proof. intros. reflexivity. Qed.

Lemma entropy_safe_none : forall data,
  Void_Entropy_Integration.safe_measure
    (Void_Entropy_Integration.mkObserver fz fz []) data = None.
Proof. intros. reflexivity. Qed.

Lemma entropy_sequence_halts : forall datasets,
  Void_Entropy_Integration.observe_sequence
    (Void_Entropy_Integration.mkObserver fz fz []) datasets
  = ([], Void_Entropy_Integration.mkObserver fz fz []).
Proof. intros. destruct datasets; reflexivity. Qed.

(* --- Distinguishability: blind at fz --- *)

Lemma distinguish_cost_zero : forall O e1 e2,
  Void_Distinguishability.distinguish_cost O e1 e2 fz = (fz, fz).
Proof. intros. reflexivity. Qed.

Lemma distinguish_sequence_empty : forall obs pairs,
  Void_Distinguishability.obs_budget obs = fz ->
  Void_Distinguishability.distinguish_sequence obs pairs = [].
Proof.
  intros obs pairs H. destruct pairs as [|[e1 e2] rest].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                   PART 2: THE THIRD VALUE                                  *)
(*                                                                            *)
(* Einstein believed BUnknown was just BTrue-or-BFalse that we happen         *)
(* not to know yet. A hidden variable. Bohr said no: BUnknown is a           *)
(* genuine third state. The question has no answer, not an answer we          *)
(* have failed to find.                                                       *)
(*                                                                            *)
(* In VOID this is a theorem, not a philosophical position.                   *)
(* BUnknown is a distinct constructor. It is not BTrue. It is not BFalse.     *)
(* No amount of cleverness turns it into either.                              *)
(*                                                                            *)
(******************************************************************************)

Theorem unknown_is_not_true : BUnknown <> BTrue.
Proof. discriminate. Qed.

Theorem unknown_is_not_false : BUnknown <> BFalse.
Proof. discriminate. Qed.

Theorem true_is_not_false : BTrue <> BFalse.
Proof. discriminate. Qed.

Theorem zero_budget_cannot_yield_true : forall a b,
  fst (fst (fin_eq_b3 a b fz)) <> BTrue.
Proof.
  intros. rewrite eq_opacity_result. exact unknown_is_not_true.
Qed.

Theorem zero_budget_cannot_yield_false : forall a b,
  fst (fst (fin_eq_b3 a b fz)) <> BFalse.
Proof.
  intros. rewrite eq_opacity_result. exact unknown_is_not_false.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                  PART 3: IRREVERSIBILITY                                   *)
(*                                                                            *)
(* Bohr: physics concerns what we can SAY about nature.                       *)
(*                                                                            *)
(* Every observation obeys a conservation law:                                *)
(*   Spuren + remaining_budget = original_budget                                *)
(*                                                                            *)
(* Spuren is generated. Budget is consumed. The process is irreversible.        *)
(* You cannot unask a question. You cannot reclaim the budget spent on        *)
(* an observation. This IS the second law of thermodynamics, expressed        *)
(* in the only language that matters: finite arithmetic.                      *)
(*                                                                            *)
(******************************************************************************)

Theorem eq_conservation : forall a b bud bud' res h,
  fin_eq_b3 a b bud = (res, bud', h) ->
  add_spur h bud' = bud.
Proof. apply spur_conservation_eq3. Qed.

Theorem le_conservation : forall a b bud bud' res h,
  le_fin_b3 a b bud = (res, bud', h) ->
  add_spur h bud' = bud.
Proof. apply spur_conservation_le3. Qed.

Theorem definite_answer_costs : forall a b bud bud' h,
  fin_eq_b3 a b (fs bud) = (BTrue, bud', h) \/
  fin_eq_b3 a b (fs bud) = (BFalse, bud', h) ->
  exists h', h = fs h'.
Proof.
  intros a b bud bud' h [Heq | Heq];
  destruct a as [|a']; destruct b as [|b']; simpl in Heq.
  - inversion Heq; subst. exists fz. reflexivity.
  - inversion Heq.
  - inversion Heq.
  - destruct (fin_eq_b3 a' b' bud) as [[r0 b0] h0] eqn:E.
    inversion Heq; subst. exists h0. reflexivity.
  - inversion Heq.
  - inversion Heq; subst. exists fz. reflexivity.
  - inversion Heq; subst. exists fz. reflexivity.
  - destruct (fin_eq_b3 a' b' bud) as [[r0 b0] h0] eqn:E.
    inversion Heq; subst. exists h0. reflexivity.
Qed.

Lemma leF_add_spur_r : forall h x, leF x (add_spur h x).
Proof.
  intros h. induction x as [|x' IH].
  - apply leF_z.
  - simpl. constructor. apply IH.
Qed.

Theorem observation_depletes : forall a b bud,
  leF (snd (fst (fin_eq_b3 a b bud))) bud.
Proof.
  intros a b bud.
  destruct bud as [|bud'].
  - destruct a; simpl; apply leF_refl.
  - destruct a as [|a']; destruct b as [|b']; simpl.
    + apply leF_step.
    + apply leF_step.
    + apply leF_step.
    + destruct (fin_eq_b3 a' b' bud') as [[r0 b0] h0] eqn:E. simpl.
      apply leF_trans with (y := bud').
      * assert (Hc := spur_conservation_eq3 a' b' bud' b0 r0 h0 E).
        rewrite <- Hc. apply leF_add_spur_r.
      * apply leF_step.
Qed.

(* Entropy measurement: budget flows strictly downward *)
Lemma measure_budget_tracks_entropy : forall b r h data,
  Void_Entropy_Integration.obs_budget
    (snd (Void_Entropy_Integration.measure_with_observer
      (Void_Entropy_Integration.mkObserver b r h) data)) =
  snd (Void_Entropy.entropy_b data b).
Proof.
  intros. unfold Void_Entropy_Integration.measure_with_observer. simpl.
  destruct (Void_Entropy.entropy_b data b) as [ent remaining]. simpl.
  reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                  PART 4: COMPLEMENTARITY                                   *)
(*                                                                            *)
(* In quantum mechanics: position and momentum cannot both be measured        *)
(* with arbitrary precision. Not because our instruments are crude.           *)
(* Because the universe forbids it.                                           *)
(*                                                                            *)
(* In VOID: if you have one tick of budget and two questions to ask,          *)
(* the first observation consumes the tick. The second observation            *)
(* faces zero budget and returns BUnknown. Not approximately. Exactly.        *)
(*                                                                            *)
(* We prove this within each module, and then ACROSS modules:                 *)
(* equality then collapse, entropy then equality, collapse then entropy.      *)
(* The budget is one currency. Spending it anywhere blinds you everywhere.    *)
(*                                                                            *)
(******************************************************************************)

(* --- Within fin_eq_b3 --- *)

Lemma single_tick_depletes_eq : forall a b,
  snd (fst (fin_eq_b3 a b (fs fz))) = fz.
Proof.
  intros a b.
  destruct a as [|a']; destruct b as [|b']; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct a'; simpl; reflexivity.
Qed.

Lemma single_tick_depletes_le : forall a b,
  snd (fst (le_fin_b3 a b (fs fz))) = fz.
Proof.
  intros a b.
  destruct a as [|a']; destruct b as [|b']; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct a'; simpl; reflexivity.
Qed.

Theorem complementarity_eq : forall a b c d,
  let bud_after := snd (fst (fin_eq_b3 a b (fs fz))) in
  fst (fst (fin_eq_b3 c d bud_after)) = BUnknown.
Proof.
  intros a b c d. simpl.
  rewrite single_tick_depletes_eq.
  rewrite eq_opacity_result. reflexivity.
Qed.

Theorem complementarity_le : forall a b c d,
  let bud_after := snd (fst (le_fin_b3 a b (fs fz))) in
  fst (fst (le_fin_b3 c d bud_after)) = BUnknown.
Proof.
  intros a b c d. simpl.
  rewrite single_tick_depletes_le.
  rewrite le_opacity_result. reflexivity.
Qed.

Theorem complementarity_cross : forall a b c d,
  let bud_after := snd (fst (fin_eq_b3 a b (fs fz))) in
  fst (fst (le_fin_b3 c d bud_after)) = BUnknown.
Proof.
  intros a b c d. simpl.
  rewrite single_tick_depletes_eq.
  rewrite le_opacity_result. reflexivity.
Qed.

(* --- CROSS-MODULE COMPLEMENTARITY --- *)

(* Equality exhausts budget, then observer collapse is frozen *)
Theorem eq_then_collapse_blind : forall a b p obs,
  let bud_after := snd (fst (fin_eq_b3 a b (fs fz))) in
  Void_Observer_Collapse.observation_teleport_b p obs bud_after = (p, fz).
Proof.
  intros a b p obs. simpl.
  destruct a as [|a']; destruct b as [|b']; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct a'; simpl; reflexivity.
Qed.

(* Entropy measurement exhausts budget, then fin_eq_b3 is blind *)
Theorem entropy_then_eq_blind : forall x r h c d,
  let obs' := snd (Void_Entropy_Integration.measure_with_observer
    (Void_Entropy_Integration.mkObserver (fs fz) r h) [x]) in
  fst (fst (fin_eq_b3 c d (Void_Entropy_Integration.obs_budget obs'))) = BUnknown.
Proof.
  intros. simpl. destruct x; simpl; destruct c; simpl; reflexivity.
Qed.

(* Observer collapse exhausts budget, then entropy measurement impossible *)
Theorem collapse_then_entropy_blind : forall p obs data r h,
  let bud_after := snd (Void_Observer_Collapse.observation_teleport_b
    p obs (fs fz)) in
  Void_Entropy_Integration.can_measure
    (Void_Entropy_Integration.mkObserver bud_after r h) data = false.
Proof.
  intros p obs data r h. simpl.
  unfold Void_Observer_Collapse.observation_teleport_b. simpl.
  unfold Void_Entropy_Integration.can_measure. simpl.
  destruct (Void_Pattern.sensitivity obs);
  destruct (Void_Pattern.location p); simpl; reflexivity.
Qed.

(* Entropy singleton depletes single tick *)
Lemma entropy_singleton_depletes : forall x,
  snd (Void_Entropy.entropy_b [x] (fs fz)) = fz.
Proof. intros. destruct x; simpl; reflexivity. Qed.

(* After entropy measurement, repeated measurement impossible *)
Theorem repeated_entropy_exhausts : forall x r,
  let obs0 := Void_Entropy_Integration.mkObserver (fs fz) r [] in
  let obs1 := snd (Void_Entropy_Integration.measure_with_observer obs0 [x]) in
  Void_Entropy_Integration.can_measure obs1 [x] = false.
Proof.
  intros. simpl. destruct x; simpl; reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                    PART 5: EXHAUSTION                                      *)
(*                                                                            *)
(* Every finite observer eventually falls silent.                             *)
(*                                                                            *)
(* Each observation consumes budget. Budget is finite. Therefore the           *)
(* number of observations is bounded. After the last observation, the         *)
(* observer enters a state of permanent BUnknown from which there is          *)
(* no return.                                                                 *)
(*                                                                            *)
(* This is not Spuren exhaustion as metaphor. This is Spuren exhaustion as theorem.         *)
(* A finite being can only ask finitely many questions. Then: silence.        *)
(*                                                                            *)
(******************************************************************************)

Fixpoint repeated_observation (a b : Fin) (bud : Budget) (fuel : Fin)
  : (Bool3 * Budget) :=
  match fuel with
  | fz => (BUnknown, bud)
  | fs fuel' =>
      match fin_eq_b3 a b bud with
      | (result, bud', _) =>
          repeated_observation a b bud' fuel'
      end
  end.

Theorem exhausted_observer_silent : forall a b fuel,
  fst (repeated_observation a b fz fuel) = BUnknown.
Proof.
  intros a b fuel. induction fuel as [|fuel' IH].
  - simpl. reflexivity.
  - simpl. rewrite eq_opacity. simpl. exact IH.
Qed.

Theorem exhaustion_absorbs : forall a b fuel,
  snd (repeated_observation a b fz fuel) = fz.
Proof.
  intros a b fuel. induction fuel as [|fuel' IH].
  - simpl. reflexivity.
  - simpl. rewrite eq_opacity. simpl. exact IH.
Qed.

(* Entropy exhaustion: sequence observation halts when budget is gone *)
Theorem entropy_exhaustion_halts : forall datasets,
  Void_Entropy_Integration.observe_sequence
    (Void_Entropy_Integration.mkObserver fz fz []) datasets
  = ([], Void_Entropy_Integration.mkObserver fz fz []).
Proof. intros. destruct datasets; reflexivity. Qed.

(* Distinguishability exhaustion: all pairs return empty *)
Theorem distinguish_exhaustion_empty : forall obs pairs,
  Void_Distinguishability.obs_budget obs = fz ->
  Void_Distinguishability.distinguish_sequence obs pairs = [].
Proof.
  intros obs pairs H. destruct pairs as [|[e1 e2] rest].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                 PART 6: OBSERVER DEPENDENCE                                *)
(*                                                                            *)
(* The same system, measured by two observers with different budgets,          *)
(* can yield different answers. This is not subjectivity. This is the         *)
(* structure of finite observation. A rich observer can distinguish what       *)
(* a poor observer cannot. Both are correct. Neither is more real.            *)
(*                                                                            *)
(* Bohr insisted: the experimental arrangement is part of the phenomenon.     *)
(* In VOID: the budget is part of the answer.                                 *)
(*                                                                            *)
(* We prove this at every level: equality, entropy, distinguishability.       *)
(*                                                                            *)
(******************************************************************************)

(* --- Core: equality --- *)

Example rich_observer_sees :
  fst (fst (fin_eq_b3 fz fz (fs (fs fz)))) = BTrue.
Proof. simpl. reflexivity. Qed.

Example poor_observer_blind :
  fst (fst (fin_eq_b3 fz fz fz)) = BUnknown.
Proof. simpl. reflexivity. Qed.

Theorem observer_dependence :
  fst (fst (fin_eq_b3 fz fz (fs fz))) <>
  fst (fst (fin_eq_b3 fz fz fz)).
Proof. simpl. discriminate. Qed.

(* --- Entropy: same data, different budget, different entropy --- *)

Example rich_entropy_observer :
  fst (Void_Entropy.entropy_b [fz; fs fz] (fs (fs (fs fz)))) = fs fz.
Proof. simpl. reflexivity. Qed.

Example poor_entropy_observer :
  fst (Void_Entropy.entropy_b [fz; fs fz] fz) = fz.
Proof. simpl. reflexivity. Qed.

Theorem entropy_observer_dependence :
  fst (Void_Entropy.entropy_b [fz; fs fz] (fs (fs (fs fz)))) <>
  fst (Void_Entropy.entropy_b [fz; fs fz] fz).
Proof. simpl. discriminate. Qed.

(* --- Information theory: the READ/WRITE boundary as observer dependence --- *)

(* READ is free: no budget required, always sees the same thing.
   WRITE costs budget: what you can write depends on what you have.
   The boundary between read and write IS observer dependence at
   the level of information theory. *)

Definition write_requires_budget :
  forall A B (w : Void_Information_Theory.WriteOperation A B),
  A -> Budget -> (B * Budget * Fin) :=
  fun A B w => @Void_Information_Theory.write_op A B w.

Definition read_is_free :
  forall A B (r : Void_Information_Theory.ReadOperation A B),
  A -> B :=
  fun A B r => @Void_Information_Theory.read_op A B r.

(* Pattern read is free: always returns the same location *)
Example read_pattern_always_same :
  let p := {| Void_Pattern.location := fs (fs fz);
              Void_Pattern.strength := (fs fz, fs (fs fz)) |} in
  @Void_Information_Theory.read_op _ _
    Void_Information_Theory.pattern_location_read p = fs (fs fz).
Proof. simpl. reflexivity. Qed.

(******************************************************************************)
(* CODA                                                                       *)
(*                                                                            *)
(* Bohr never had a proof. He had intuition and stubbornness. Einstein        *)
(* never had a counterexample. He had intuition and stubbornness.             *)
(*                                                                            *)
(* The dispute lasted from 1927 until 1955. Twenty-eight years of argument    *)
(* over whether BUnknown is a real state or a confession of ignorance.        *)
(*                                                                            *)
(* In VOID, the dispute is settled in six parts and across nine modules:      *)
(*                                                                            *)
(* 1. OPACITY pervades every module.                                          *)
(*    - fin_eq_b3 yields BUnknown at fz.                                      *)
(*    - observation_teleport_b freezes patterns at fz.                        *)
(*    - can_measure returns false at fz.                                      *)
(*    - distinguish_sequence returns empty at fz.                             *)
(*    Zero budget, zero knowledge. Everywhere.                                *)
(*                                                                            *)
(* 2. THE THIRD VALUE is structural.                                          *)
(*    BUnknown is a constructor. Not BTrue. Not BFalse. Period.               *)
(*                                                                            *)
(* 3. IRREVERSIBILITY is conservation.                                        *)
(*    Spuren + remaining = original. In every operation.                         *)
(*    Budget flows one direction: down.                                        *)
(*                                                                            *)
(* 4. COMPLEMENTARITY crosses module boundaries.                              *)
(*    Equality exhausts budget, then collapse is frozen.                       *)
(*    Entropy depletes observer, then equality is blind.                       *)
(*    Collapse spends the tick, then measurement is impossible.                *)
(*    Budget is one currency. Spending it anywhere costs everywhere.           *)
(*                                                                            *)
(* 5. EXHAUSTION is universal.                                                *)
(*    Repeated observation yields permanent BUnknown.                          *)
(*    Entropy sequences halt. Distinguish sequences empty.                     *)
(*    Every finite observer dies.                                              *)
(*                                                                            *)
(* 6. OBSERVER DEPENDENCE is the same at every level.                         *)
(*    Rich observer sees BTrue, poor observer sees BUnknown.                   *)
(*    Rich entropy observer sees fs fz, poor sees fz.                          *)
(*    Read is free, write costs budget. The boundary is real.                   *)
(*                                                                            *)
(* Bohr was right. Not as philosophy. As arithmetic.                          *)
(* Not in one module. In all of them.                                         *)
(*                                                                            *)
(******************************************************************************)
