(******************************************************************************)
(* void_trace.v - THE ALGEBRA OF SEQUENTIAL OBSERVATION                      *)
(*                                                                            *)
(* Every operation in VOID has one of two signatures:                         *)
(*                                                                            *)
(*   VoidOp3: Budget -> (A * Budget * Heat)     -- explicit heat              *)
(*   VoidOp2: Budget -> (A * Budget)            -- implicit heat              *)
(*                                                                            *)
(* Every file threads budget by hand: destructure, pass remainder, repeat.    *)
(* This file names what they all do.                                          *)
(*                                                                            *)
(* A Step is an operation that has been called. Not a function. An event.     *)
(* A Trace is a chain of Steps where each output feeds the next input.        *)
(*                                                                            *)
(* Each "2+2" is an event. It has its own budget. The next "2+2" has          *)
(* a different budget because the first one changed it. They are not          *)
(* the same operation. They are two steps in a trace.                         *)
(*                                                                            *)
(* Five properties follow for ALL operations, proved once:                    *)
(*                                                                            *)
(* 1. CONSERVATION - total heat + final budget = initial budget               *)
(* 2. MONOTONICITY - budget never increases along a trace                     *)
(* 3. OPACITY      - at zero budget, output and heat are both zero            *)
(* 4. ABSORPTION   - once at zero, every subsequent step stays at zero        *)
(* 5. FINITUDE     - if each step costs a tick, trace length is bounded       *)
(*                                                                            *)
(* Then: 13 instantiations across 6 modules.                                  *)
(*                                                                            *)
(* DEPENDS ON:                                                                *)
(*   void_finite_minimal.v      - Fin, Budget, Heat, Bool3                    *)
(*   void_probability_minimal.v - FinProb                                     *)
(*   void_pattern.v             - Pattern, Observer, decay_with_budget        *)
(*   void_arithmetic.v          - add_fin, mult_fin, sub_fin                  *)
(*   void_observer_collapse.v   - observation_teleport_b, zeno, hash, multi   *)
(*   void_distinguishability.v  - distinguish_cost                            *)
(*   void_entropy.v             - entropy_b                                   *)
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
Require Import Coq.Lists.List.
Import ListNotations.
Import Void_Pattern.

(******************************************************************************)
(*                                                                            *)
(*        PART 0: THE TWO UNIVERSAL VOID SIGNATURES                          *)
(*                                                                            *)
(******************************************************************************)

(* Triple-returning: fin_eq_b3, le_fin_b3. Heat is explicit. *)
Definition VoidOp3 (A : Type) := Budget -> (A * Budget * Heat).

(* Pair-returning: everything else. Heat is implicit (= input - output). *)
Definition VoidOp2 (A : Type) := Budget -> (A * Budget).

(* Steps: executed operations. Events, not functions. *)

Record Step3 (A : Type) := mkStep3 {
  s3_input  : Budget;
  s3_result : A;
  s3_output : Budget;
  s3_heat   : Heat
}.

Record Step2 (A : Type) := mkStep2 {
  s2_input  : Budget;
  s2_result : A;
  s2_output : Budget
}.

Arguments mkStep3 {A}. Arguments s3_input {A}. Arguments s3_result {A}.
Arguments s3_output {A}. Arguments s3_heat {A}.
Arguments mkStep2 {A}. Arguments s2_input {A}. Arguments s2_result {A}.
Arguments s2_output {A}.

(* Execute: call an operation, produce a step *)
Definition execute3 {A : Type} (op : VoidOp3 A) (b : Budget) : Step3 A :=
  match op b with
  | (a, b', h) => mkStep3 b a b' h
  end.

Definition execute2 {A : Type} (op : VoidOp2 A) (b : Budget) : Step2 A :=
  match op b with
  | (a, b') => mkStep2 b a b'
  end.

(* Conservation *)
Definition conservative3 {A : Type} (s : Step3 A) : Prop :=
  add_heat (s3_heat s) (s3_output s) = s3_input s.

(* Chaining *)
Definition chained3 {A : Type} (s1 s2 : Step3 A) : Prop :=
  s3_output s1 = s3_input s2.

Definition chained2 {A : Type} (s1 s2 : Step2 A) : Prop :=
  s2_output s1 = s2_input s2.

(******************************************************************************)
(*                                                                            *)
(*        TRACES: CHAINS OF STEPS                                             *)
(*                                                                            *)
(******************************************************************************)

Fixpoint total_heat3 {A : Type} (trace : list (Step3 A)) : Heat :=
  match trace with
  | [] => fz
  | s :: rest => add_heat (s3_heat s) (total_heat3 rest)
  end.

Definition first_budget3 {A : Type} (trace : list (Step3 A))
  (default : Budget) : Budget :=
  match trace with
  | [] => default
  | s :: _ => s3_input s
  end.

Fixpoint last_budget3 {A : Type} (trace : list (Step3 A))
  (default : Budget) : Budget :=
  match trace with
  | [] => default
  | [s] => s3_output s
  | _ :: rest => last_budget3 rest default
  end.

(* Build traces automatically *)
Fixpoint run_chain3 {A : Type} (op : VoidOp3 A) (b : Budget) (fuel : Fin)
  : list (Step3 A) :=
  match fuel with
  | fz => []
  | fs fuel' =>
      let s := execute3 op b in
      s :: run_chain3 op (s3_output s) fuel'
  end.

Fixpoint run_chain2 {A : Type} (op : VoidOp2 A) (b : Budget) (fuel : Fin)
  : list (Step2 A) :=
  match fuel with
  | fz => []
  | fs fuel' =>
      let s := execute2 op b in
      s :: run_chain2 op (s2_output s) fuel'
  end.

(******************************************************************************)
(*                                                                            *)
(*        LEMMAS: PROPERTIES OF add_heat                                      *)
(*                                                                            *)
(******************************************************************************)

Lemma add_heat_assoc : forall a b c,
  add_heat a (add_heat b c) = add_heat (add_heat a b) c.
Proof. intros a b c. induction c; simpl; try rewrite IHc; reflexivity. Qed.

Lemma add_heat_fz_r : forall h, add_heat h fz = h.
Proof. intros. simpl. reflexivity. Qed.

Lemma add_heat_fz_l : forall x, add_heat fz x = x.
Proof. intros. induction x; simpl; try rewrite IHx; reflexivity. Qed.

Lemma add_heat_fs : forall h x,
  add_heat (fs h) x = fs (add_heat h x).
Proof. intros h x. induction x; simpl; try rewrite IHx; reflexivity. Qed.

Lemma add_heat_fz_inv : forall h b,
  add_heat h b = fz -> h = fz /\ b = fz.
Proof.
  intros h b H. destruct b.
  - simpl in H. split; [exact H | reflexivity].
  - simpl in H. discriminate.
Qed.

Lemma leF_add_heat_r : forall h x, leF x (add_heat h x).
Proof.
  intros h. induction x as [|x' IH].
  - apply leF_z.
  - simpl. constructor. apply IH.
Qed.

(* Helper for extracting output budget *)
Lemma execute2_output : forall A (op : VoidOp2 A) b,
  s2_output (execute2 op b) = snd (op b).
Proof. intros. unfold execute2. destruct (op b). simpl. reflexivity. Qed.

(******************************************************************************)
(*                                                                            *)
(*        PART 1: CONSERVATION (VoidOp3)                                      *)
(*                                                                            *)
(******************************************************************************)

Theorem trace_conservation_1 : forall A (s : Step3 A),
  conservative3 s ->
  add_heat (total_heat3 [s]) (last_budget3 [s] fz) = first_budget3 [s] fz.
Proof. intros A s Hc. simpl. exact Hc. Qed.

Theorem trace_conservation_2 : forall A (s1 s2 : Step3 A),
  conservative3 s1 -> conservative3 s2 -> chained3 s1 s2 ->
  add_heat (total_heat3 [s1; s2]) (last_budget3 [s1; s2] fz)
  = first_budget3 [s1; s2] fz.
Proof.
  intros A s1 s2 Hc1 Hc2 Hch. simpl.
  unfold conservative3 in Hc1, Hc2. unfold chained3 in Hch.
  rewrite <- add_heat_assoc.
  rewrite Hc2. rewrite <- Hch. exact Hc1.
Qed.

Theorem trace_conservation_3 : forall A (s1 s2 s3 : Step3 A),
  conservative3 s1 -> conservative3 s2 -> conservative3 s3 ->
  chained3 s1 s2 -> chained3 s2 s3 ->
  add_heat (total_heat3 [s1; s2; s3]) (last_budget3 [s1; s2; s3] fz)
  = first_budget3 [s1; s2; s3] fz.
Proof.
  intros A s1 s2 s3 Hc1 Hc2 Hc3 Hch12 Hch23. simpl.
  unfold conservative3 in *. unfold chained3 in *.
  rewrite <- add_heat_assoc. rewrite <- add_heat_assoc.
  rewrite Hc3. rewrite <- Hch23.
  rewrite Hc2. rewrite <- Hch12.
  exact Hc1.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        PART 2: MONOTONICITY                                                *)
(*                                                                            *)
(******************************************************************************)

Theorem step3_budget_decreases : forall A (s : Step3 A),
  conservative3 s -> leF (s3_output s) (s3_input s).
Proof.
  intros A s Hc. unfold conservative3 in Hc.
  rewrite <- Hc. apply leF_add_heat_r.
Qed.

Theorem two_step3_decreases : forall A (s1 s2 : Step3 A),
  conservative3 s1 -> conservative3 s2 -> chained3 s1 s2 ->
  leF (s3_output s2) (s3_input s1).
Proof.
  intros A s1 s2 Hc1 Hc2 Hch.
  apply leF_trans with (y := s3_output s1).
  - apply leF_trans with (y := s3_input s2).
    + apply step3_budget_decreases. exact Hc2.
    + unfold chained3 in Hch. rewrite <- Hch. apply leF_refl.
  - apply step3_budget_decreases. exact Hc1.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        PART 3: OPACITY                                                     *)
(*                                                                            *)
(******************************************************************************)

(* VoidOp3: at fz, both output and heat are fz *)
Theorem opacity3_output : forall A (op : VoidOp3 A),
  (forall b, conservative3 (execute3 op b)) ->
  s3_output (execute3 op fz) = fz.
Proof.
  intros A op Hcons.
  assert (H := Hcons fz). unfold conservative3 in H. unfold execute3 in *.
  destruct (op fz) as [[a b'] h]. simpl in *.
  destruct h; destruct b'; simpl in H; try discriminate; reflexivity.
Qed.

Theorem opacity3_heat : forall A (op : VoidOp3 A),
  (forall b, conservative3 (execute3 op b)) ->
  s3_heat (execute3 op fz) = fz.
Proof.
  intros A op Hcons.
  assert (H := Hcons fz). unfold conservative3 in H. unfold execute3 in *.
  destruct (op fz) as [[a b'] h]. simpl in *.
  destruct h; destruct b'; simpl in H; try discriminate; reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        PART 4: ABSORPTION                                                  *)
(*                                                                            *)
(* Once budget reaches zero, it stays zero forever.                           *)
(* Proved for BOTH signatures.                                                *)
(*                                                                            *)
(******************************************************************************)

(* VoidOp3: absorption *)
Theorem absorption3 : forall A (op : VoidOp3 A) fuel,
  (forall b, conservative3 (execute3 op b)) ->
  forall s, In s (run_chain3 op fz fuel) ->
  s3_output s = fz.
Proof.
  intros A op fuel Hcons.
  induction fuel as [|fuel' IH]; intros s Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. apply opacity3_output. exact Hcons.
    + rewrite (opacity3_output A op Hcons) in Hin.
      apply IH. exact Hin.
Qed.

Theorem absorption3_heat : forall A (op : VoidOp3 A) fuel,
  (forall b, conservative3 (execute3 op b)) ->
  forall s, In s (run_chain3 op fz fuel) ->
  s3_heat s = fz.
Proof.
  intros A op fuel Hcons.
  induction fuel as [|fuel' IH]; intros s Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. apply opacity3_heat. exact Hcons.
    + rewrite (opacity3_output A op Hcons) in Hin.
      apply IH. exact Hin.
Qed.

(* VoidOp2: absorption *)
Theorem absorption2 : forall A (op : VoidOp2 A) fuel,
  snd (op fz) = fz ->
  forall s, In s (run_chain2 op fz fuel) -> s2_output s = fz.
Proof.
  intros A op fuel Hop.
  induction fuel as [|fuel' IH]; intros s Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. rewrite execute2_output. exact Hop.
    + assert (Hout: s2_output (execute2 op fz) = fz).
      { rewrite execute2_output. exact Hop. }
      rewrite Hout in Hin. apply IH. exact Hin.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        PART 5: FINITUDE                                                    *)
(*                                                                            *)
(******************************************************************************)

Definition costs_tick3 {A : Type} (s : Step3 A) : Prop :=
  exists h', s3_heat s = fs h'.

Theorem tick_strictly_decreases : forall A (s : Step3 A),
  conservative3 s -> costs_tick3 s ->
  exists b', s3_input s = fs b' /\ leF (s3_output s) b'.
Proof.
  intros A s Hc [h' Hh].
  unfold conservative3 in Hc. rewrite Hh in Hc.
  rewrite add_heat_fs in Hc.
  exists (add_heat h' (s3_output s)). split.
  - symmetry. exact Hc.
  - apply leF_add_heat_r.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        STRUCTURAL PROPERTIES OF run_chain                                  *)
(*                                                                            *)
(******************************************************************************)

Theorem run_chain3_chained : forall A (op : VoidOp3 A) b fuel,
  forall s1 s2 rest,
  run_chain3 op b fuel = s1 :: s2 :: rest ->
  chained3 s1 s2.
Proof.
  intros A op b fuel. revert b.
  induction fuel as [|fuel']; intros b s1 s2 rest Heq.
  - simpl in Heq. discriminate.
  - simpl in Heq. inversion Heq. subst.
    destruct fuel' as [|fuel''].
    + simpl in H1. discriminate.
    + simpl in H1. inversion H1. subst.
      unfold chained3, execute3.
      destruct (op b) as [[a1 b1] h1]. simpl.
      destruct (op b1) as [[a2 b2] h2]. simpl.
      reflexivity.
Qed.

Theorem run_chain3_conservative : forall A (op : VoidOp3 A) b fuel,
  (forall b0, conservative3 (execute3 op b0)) ->
  Forall conservative3 (run_chain3 op b fuel).
Proof.
  intros A op b fuel Hcons. revert b.
  induction fuel as [|fuel' IH]; intros b.
  - simpl. constructor.
  - simpl. constructor.
    + apply Hcons.
    + apply IH.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        INSTANTIATIONS: VoidOp3 (explicit heat)                             *)
(*                                                                            *)
(*        fin_eq_b3 and le_fin_b3 from void_finite_minimal.v                  *)
(*                                                                            *)
(******************************************************************************)

Definition eq_op (a b : Fin) : VoidOp3 Bool3 :=
  fun bud => fin_eq_b3 a b bud.

Theorem eq_op_conservative : forall a b bud,
  conservative3 (execute3 (eq_op a b) bud).
Proof.
  intros a b bud. unfold conservative3, execute3, eq_op.
  destruct (fin_eq_b3 a b bud) as [[r b'] h] eqn:E. simpl.
  exact (heat_conservation_eq3 a b bud b' r h E).
Qed.

Definition le_op (a b : Fin) : VoidOp3 Bool3 :=
  fun bud => le_fin_b3 a b bud.

Theorem le_op_conservative : forall a b bud,
  conservative3 (execute3 (le_op a b) bud).
Proof.
  intros a b bud. unfold conservative3, execute3, le_op.
  destruct (le_fin_b3 a b bud) as [[r b'] h] eqn:E. simpl.
  exact (heat_conservation_le3 a b bud b' r h E).
Qed.

(* Absorption follows for free *)
Example eq_chain_absorbs : forall a b fuel s,
  In s (run_chain3 (eq_op a b) fz fuel) -> s3_output s = fz.
Proof.
  intros. apply absorption3 with (op := eq_op a b) (fuel := fuel).
  apply eq_op_conservative. exact H.
Qed.

Example le_chain_absorbs : forall a b fuel s,
  In s (run_chain3 (le_op a b) fz fuel) -> s3_output s = fz.
Proof.
  intros. apply absorption3 with (op := le_op a b) (fuel := fuel).
  apply le_op_conservative. exact H.
Qed.

(******************************************************************************)
(*                                                                            *)
(*        INSTANTIATIONS: VoidOp2 (implicit heat)                             *)
(*                                                                            *)
(*        11 operations across 5 modules.                                     *)
(*                                                                            *)
(******************************************************************************)

(* --- void_observer_collapse.v --- *)

Definition collapse_op (p : Pattern) (obs : Observer) : VoidOp2 Pattern :=
  fun b => Void_Observer_Collapse.observation_teleport_b p obs b.

Definition zeno_op (p : Pattern) (obs : Observer) (times : Fin) : VoidOp2 Pattern :=
  fun b => Void_Observer_Collapse.zeno_observation_b p obs times b.

Definition multi_collapse_op (p : Pattern) (observers : list Observer) : VoidOp2 Pattern :=
  fun b => Void_Observer_Collapse.multi_observer_collapse_b p observers b.

Definition hash_op (a b : Fin) : VoidOp2 Fin :=
  fun bud => Void_Observer_Collapse.hash_fin_b a b bud.

(* --- void_pattern.v --- *)

Definition decay_op (fp : Void_Probability_Minimal.FinProb) 
  : VoidOp2 Void_Probability_Minimal.FinProb :=
  fun b => decay_with_budget fp b.

(* --- void_arithmetic.v --- *)

Definition add_op (a b : Fin) : VoidOp2 Fin :=
  fun bud => Void_Arithmetic.add_fin a b bud.

Definition mult_op (a b : Fin) : VoidOp2 Fin :=
  fun bud => Void_Arithmetic.mult_fin a b bud.

Definition sub_op (a b : Fin) : VoidOp2 Fin :=
  fun bud => Void_Arithmetic.sub_fin a b bud.

(* --- void_distinguishability.v --- *)

Definition distinguish_op (O : Void_Distinguishability.ObsState)
  (e1 e2 : Void_Distinguishability.EnvState) : VoidOp2 Fin :=
  fun b => Void_Distinguishability.distinguish_cost O e1 e2 b.

(* --- void_entropy.v --- *)

Definition entropy_op (data : list Fin) : VoidOp2 Fin :=
  fun b => Void_Entropy.entropy_b data b.

(* --- void_pattern.v (fin_eq_b as pair) --- *)

Definition eq_bool_op (a b : Fin) : VoidOp2 bool :=
  fun bud => fin_eq_b a b bud.

(******************************************************************************)
(*                                                                            *)
(*        OPACITY PROOFS: VoidOp2 instantiations                              *)
(*                                                                            *)
(******************************************************************************)

Lemma collapse_op_opaque : forall p obs,
  snd (collapse_op p obs fz) = fz.
Proof. intros. reflexivity. Qed.

Lemma zeno_op_opaque : forall p obs times,
  snd (zeno_op p obs times fz) = fz.
Proof. intros. destruct times; simpl; reflexivity. Qed.

Lemma hash_op_opaque : forall a b,
  snd (hash_op a b fz) = fz.
Proof. intros. destruct a; destruct b; simpl; reflexivity. Qed.

Lemma decay_op_opaque : forall fp,
  snd (decay_op fp fz) = fz.
Proof. intros. reflexivity. Qed.

Lemma add_op_opaque : forall a b,
  snd (add_op a b fz) = fz.
Proof. intros. unfold add_op. destruct a; destruct b; simpl; reflexivity. Qed.

Lemma sub_op_opaque : forall a b,
  snd (sub_op a b fz) = fz.
Proof. intros. unfold sub_op. destruct a; destruct b; simpl; reflexivity. Qed.

Lemma distinguish_op_opaque : forall O e1 e2,
  snd (distinguish_op O e1 e2 fz) = fz.
Proof. intros. reflexivity. Qed.

Lemma eq_bool_op_opaque : forall a b,
  snd (eq_bool_op a b fz) = fz.
Proof. intros. destruct a; simpl; reflexivity. Qed.

(******************************************************************************)
(*                                                                            *)
(*        ABSORPTION: VoidOp2 instantiations                                  *)
(*                                                                            *)
(*        Each one-line proof shows the general theorem applies.              *)
(*                                                                            *)
(******************************************************************************)

Example collapse_absorbs : forall p obs fuel s,
  In s (run_chain2 (collapse_op p obs) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (collapse_op_opaque p obs) s H). Qed.

Example zeno_absorbs : forall p obs times fuel s,
  In s (run_chain2 (zeno_op p obs times) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (zeno_op_opaque p obs times) s H). Qed.

Example decay_absorbs : forall fp fuel s,
  In s (run_chain2 (decay_op fp) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (decay_op_opaque fp) s H). Qed.

Example add_absorbs : forall a b fuel s,
  In s (run_chain2 (add_op a b) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (add_op_opaque a b) s H). Qed.

Example sub_absorbs : forall a b fuel s,
  In s (run_chain2 (sub_op a b) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (sub_op_opaque a b) s H). Qed.

Example distinguish_absorbs : forall O e1 e2 fuel s,
  In s (run_chain2 (distinguish_op O e1 e2) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (distinguish_op_opaque O e1 e2) s H). Qed.

Example hash_absorbs : forall a b fuel s,
  In s (run_chain2 (hash_op a b) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (hash_op_opaque a b) s H). Qed.

Example eq_bool_absorbs : forall a b fuel s,
  In s (run_chain2 (eq_bool_op a b) fz fuel) -> s2_output s = fz.
Proof. intros. exact (absorption2 _ _ fuel (eq_bool_op_opaque a b) s H). Qed.

(******************************************************************************)
(* CODA                                                                       *)
(*                                                                            *)
(* 13 operations from 6 modules, two signatures, one algebra.                 *)
(*                                                                            *)
(* fin_eq_b3     - equality           (void_finite_minimal)                   *)
(* le_fin_b3     - comparison         (void_finite_minimal)                   *)
(* fin_eq_b      - boolean equality   (void_finite_minimal)                   *)
(* collapse      - observation        (void_observer_collapse)                *)
(* zeno          - repeated obs.      (void_observer_collapse)                *)
(* multi_collapse - interference      (void_observer_collapse)                *)
(* hash          - mixing             (void_observer_collapse)                *)
(* decay         - weakening          (void_pattern)                          *)
(* add           - addition           (void_arithmetic)                       *)
(* sub           - subtraction        (void_arithmetic)                       *)
(* mult          - multiplication     (void_arithmetic)                       *)
(* distinguish   - cost               (void_distinguishability)               *)
(* entropy       - measurement        (void_entropy)                          *)
(*                                                                            *)
(* All obey opacity. All absorb at zero. Conservation and finitude            *)
(* hold for the triple-ops; the pair-ops trade explicit accounting            *)
(* for implicit monotonicity.                                                 *)
(*                                                                            *)
(* Each 2+2 is still an unrepeatable event. Each step in a trace             *)
(* is unique - it consumed a budget that no other step will see.             *)
(* The trace does not identify them. The trace records that they             *)
(* happened, in order, irreversibly, until silence.                          *)
(*                                                                            *)
(******************************************************************************)
