(******************************************************************************)
(* void_finite_minimal.v                                                      *)
(* TRULY finite - every operation costs                                       *)
(* Bool3 core + backward-compatible bool wrappers                             *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(******************************************************************************)
(* SYSTEM PARAMETERS - META-LEVEL ONLY                                       *)
(*                                                                            *)
(* INFINITY BRIDGE: Z appears here ONLY as meta-level witness.               *)
(* It is NEVER used in computation. Its role:                                *)
(*   MAX : Z      - bounds the Fin type from outside (specification only)    *)
(*   fin_to_Z_PROOF_ONLY - extraction for proof obligations, never computed  *)
(* No Fin operation touches Z. No theorem about Fin depends on Z             *)
(* except through the meta-axiom fin_bounded (which says Fin is finite).     *)
(******************************************************************************)

Parameter MAX : Z.
Axiom MAX_positive : (0 < MAX)%Z.

(******************************************************************************)
(* FINITE TYPE Fin — NOT PEANO                                               *)
(*                                                                            *)
(* Same constructors: fz, fs.  Different contract.                            *)
(* Peano: succession is free, unbounded, and builds ℕ.                       *)
(* Fin:   succession is bounded (fin_bounded), costs one irreversible tick   *)
(*        (no_free_lunch below), and builds FRACTIONS — not natural numbers. *)
(*        Probability is primitive: (Fin * Fin), not derived from ℝ.         *)
(*        Peano builds ℕ then asks how to get probability.                   *)
(*        VOID builds probability and observes: ℕ was never needed.          *)
(******************************************************************************)

Inductive Fin : Type :=
  | fz : Fin
  | fs : Fin -> Fin.

(* PROOF-ONLY: Never use in computation *)
Fixpoint fin_to_Z_PROOF_ONLY (n : Fin) : Z :=
  match n with
  | fz => 0%Z
  | fs n' => (1 + fin_to_Z_PROOF_ONLY n')%Z
  end.

(* The bound is an axiom about the type, not a computation *)
Axiom fin_bounded : forall n : Fin, (fin_to_Z_PROOF_ONLY n <= MAX)%Z.

(* NOTE ON "spur_monotone" FROM void_arithmetic.v:                          *)
(*   The original statement was:                                             *)
(*     forall n m b res b' h, add_fin_spur n m b = (res, b', h) ->          *)
(*       (fin_to_Z_PROOF_ONLY h >= 0)%Z.                                    *)
(*   This is vacuous: h : Fin, and Fin has no negative inhabitants.          *)
(*   Non-negativity is a property of the TYPE, not of the operation.         *)
(*   The real content is CONSERVATION: add_spur h b' = b.                    *)
(*   That is proven below as spur_conservation_add, _sub, _eq3, _le3.       *)
(*   There is nothing else to prove. The "philosophical excuse" was correct. *)

(******************************************************************************)
(* Fin Ã¢â€°Â¤ and basic lemmas                                                    *)
(******************************************************************************)

Inductive leF : Fin -> Fin -> Prop :=
  | leF_z  : forall m, leF fz m
  | leF_ss : forall n m, leF n m -> leF (fs n) (fs m).

Lemma leF_refl : forall x, leF x x.
Proof. induction x; constructor; auto. Qed.

Lemma leF_trans : forall x y z, leF x y -> leF y z -> leF x z.
Proof.
  intros x y z Hxy Hyz; revert x Hxy.
  induction Hyz; intros x Hxy.
  - inversion Hxy; constructor.
  - inversion Hxy; subst; constructor; auto.
Qed.

Lemma leF_step : forall x, leF x (fs x).
Proof. induction x; constructor; auto. Qed.

(******************************************************************************)
(* THREE-VALUED LOGIC                                                        *)
(******************************************************************************)

Inductive Bool3 : Type :=
  | BTrue : Bool3
  | BFalse : Bool3
  | BUnknown : Bool3.

Definition bool3_to_option (b : Bool3) : option bool :=
  match b with
  | BTrue => Some true
  | BFalse => Some false
  | BUnknown => None
  end.

(******************************************************************************)
(* BUDGET, HEAT, AND STATE                                                   *)
(******************************************************************************)

Definition Budget := Fin.
Definition Spuren := Fin.
Definition State := (Fin * Budget)%type.

Fixpoint add_spur (h1 h2 : Fin) : Fin :=
  match h2 with
  | fz => h1
  | fs h2' => fs (add_spur h1 h2')
  end.

Definition B (A : Type) := Budget -> (A * Budget * Spuren).

Definition ret {A : Type} (a : A) : B A :=
  fun b => (a, b, fz).

Definition bind {A C : Type} (ma : B A) (f : A -> B C) : B C :=
  fun budget =>
    match ma budget with
    | (a, b', h1) =>
        match f a b' with
        | (result, b'', h2) => (result, b'', add_spur h1 h2)
        end
    end.

Fixpoint spend_aux (b c : Fin) : (Budget * Spuren) :=
  match c with
  | fz => (b, fz)
  | fs c' =>
      match b with
      | fz => (fz, c)
      | fs b' =>
          match spend_aux b' c' with
          | (b'', h) => (b'', fs h)
          end
      end
  end.

Definition spend (cost : Fin) : B unit :=
  fun b => let (b', h) := spend_aux b cost in (tt, b', h).

(******************************************************************************)
(* COSTS AS PARAMETERS - NOT CONSTRUCTED                                     *)
(******************************************************************************)

Parameter comparison_cost : Fin.
Parameter arithmetic_cost : Fin.
Parameter construction_cost : Fin.

Axiom comparison_cost_positive   : exists n, comparison_cost = fs n.
Axiom arithmetic_cost_positive   : exists n, arithmetic_cost = fs n.
Axiom construction_cost_positive : exists n, construction_cost = fs n.

(******************************************************************************)
(* BOOTSTRAP BUDGET                                                          *)
(******************************************************************************)

Parameter initial_budget : Budget.
Axiom initial_budget_sufficient : exists n, initial_budget = fs (fs (fs n)).

(******************************************************************************)
(* CAP - EMERGENT FROM CONTOUR, NOT AXIOMATIC                                *)
(*                                                                            *)
(* Historycznie Cap byl Parameter'em na poziomie tego pliku, z aksjomatem    *)
(* Cap_positive zapewniajacym Cap > 0. To byla reifikacja 'zewnetrznego      *)
(* dekretu swiata' — void-theory tego nie dopuszcza. Pojemnosc systemu nie   *)
(* jest parametrem wszechswiata, lecz wynika z ksztaltu jego konturu.        *)
(*                                                                            *)
(* Per-instance capacity jest teraz polem rekordu Membrane (mem_capacity),   *)
(* a funkcja cap : Membrane -> Fin (zdefiniowana w void_membrane.v) czyta    *)
(* ja z konturu. cap jest funkcja membrany, nie odwrotnie.                    *)
(*                                                                            *)
(* A semipermeable boundary is a finite filter. It is not a backdoor to      *)
(* infinity. Any caller of assimilate_b_spur that would produce a budget     *)
(* exceeding cap m is responsible for truncating at its layer; the primitive *)
(* itself is pure structural addition with Spuren bookkeeping.               *)
(******************************************************************************)

(******************************************************************************)
(* BUDGET-AWARE OPS (3-valued core) - WITH SPUREN                            *)
(******************************************************************************)

Fixpoint fin_eq_b3 (n m : Fin) (b : Budget) : (Bool3 * Budget * Spuren) :=
  match b with
  | fz => (BUnknown, fz, fz)
  | fs b' =>
      match n, m with
      | fz, fz => (BTrue, b', fs fz)
      | fs n', fs m' =>
          match fin_eq_b3 n' m' b' with
          | (r, b'', h) => (r, b'', fs h)
          end
      | _, _ => (BFalse, b', fs fz)
      end
  end.

Fixpoint le_fin_b3 (n m : Fin) (b : Budget) : (Bool3 * Budget * Spuren) :=
  match b with
  | fz => (BUnknown, fz, fz)
  | fs b' =>
      match n, m with
      | fz, _ => (BTrue, b', fs fz)
      | fs _, fz => (BFalse, b', fs fz)
      | fs n', fs m' =>
          match le_fin_b3 n' m' b' with
          | (r, b'', h) => (r, b'', fs h)
          end
      end
  end.

(******************************************************************************)
(* NO FREE LUNCH — Every distinction costs.  Peano compares for free.        *)
(* In VOID, if you have budget, you pay.  h = fz only when b = fz.          *)
(******************************************************************************)

Lemma no_free_lunch_eq_aux : forall n m b,
  snd (fin_eq_b3 n m (fs b)) <> fz.
Proof.
  intros n m b; revert n m.
  induction b as [| b0 IH].
  - intros [|n'] [|m'].
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. destruct (fin_eq_b3 n' m' fz) as [[r b1] h1].
      simpl. discriminate.
  - intros [|n'] [|m'].
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. destruct (fin_eq_b3 n' m' (fs b0)) as [[r b1] h1].
      simpl. discriminate.
Qed.

Lemma no_free_lunch_eq : forall n m b res b' h,
  fin_eq_b3 n m (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros n m b res b' h Heq.
  pose proof (no_free_lunch_eq_aux n m b) as H.
  rewrite Heq in H. simpl in H. exact H.
Qed.

Lemma no_free_lunch_le_aux : forall n m b,
  snd (le_fin_b3 n m (fs b)) <> fz.
Proof.
  intros n m b; revert n m.
  induction b as [| b0 IH].
  - intros [|n'] [|m'].
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. destruct (le_fin_b3 n' m' fz) as [[r b1] h1].
      simpl. discriminate.
  - intros [|n'] m.
    + destruct m; simpl; discriminate.
    + destruct m as [|m'].
      * simpl. discriminate.
      * simpl. destruct (le_fin_b3 n' m' (fs b0)) as [[r b1] h1].
        simpl. discriminate.
Qed.

Lemma no_free_lunch_le : forall n m b res b' h,
  le_fin_b3 n m (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros n m b res b' h Heq.
  pose proof (no_free_lunch_le_aux n m b) as H.
  rewrite Heq in H. simpl in H. exact H.
Qed.


(******************************************************************************)
(* SUCCESSOR IS NOT FREE — The tax on fs.                                    *)
(*                                                                            *)
(* Peano: S n costs nothing. Comparing S n with S m costs the same as        *)
(* comparing n with m.                                                        *)
(* VOID: fs n costs ONE MORE TICK than n. Comparing fs n with fs m           *)
(* using budget fs b produces fs h Spuren, where h is the Spuren from        *)
(* comparing n with m using b. The successor adds exactly one tick of cost.  *)
(* This is NOT a design choice. It FOLLOWS from the definition of le_fin_b3  *)
(* and fin_eq_b3. The successor is structurally expensive.                   *)
(******************************************************************************)

Theorem successor_costs_more_le : forall n m b r b'' h,
  le_fin_b3 n m b = (r, b'', h) ->
  le_fin_b3 (fs n) (fs m) (fs b) = (r, b'', fs h).
Proof.
  intros n m b r b'' h Heq.
  simpl. rewrite Heq. reflexivity.
Qed.

Theorem successor_costs_more_eq : forall n m b r b'' h,
  fin_eq_b3 n m b = (r, b'', h) ->
  fin_eq_b3 (fs n) (fs m) (fs b) = (r, b'', fs h).
Proof.
  intros n m b r b'' h Heq.
  simpl. rewrite Heq. reflexivity.
Qed.

(* The combined statement: successor adds exactly one tick of heat.          *)
(* The Spuren of comparing successors is always fs(Spuren of predecessors).  *)
(* Peano promised free counting. This theorem is the invoice.                *)

Definition spuren_of_b3 (x : Bool3 * Budget * Spuren) : Spuren :=
  match x with (_, _, h) => h end.

Corollary successor_is_not_free_le : forall n m b,
  spuren_of_b3 (le_fin_b3 (fs n) (fs m) (fs b)) =
  fs (spuren_of_b3 (le_fin_b3 n m b)).
Proof.
  intros n m b.
  unfold spuren_of_b3.
  destruct (le_fin_b3 n m b) as [[r b''] h] eqn:Heq.
  rewrite (successor_costs_more_le _ _ _ _ _ _ Heq).
  reflexivity.
Qed.

Corollary successor_is_not_free_eq : forall n m b,
  spuren_of_b3 (fin_eq_b3 (fs n) (fs m) (fs b)) =
  fs (spuren_of_b3 (fin_eq_b3 n m b)).
Proof.
  intros n m b.
  unfold spuren_of_b3.
  destruct (fin_eq_b3 n m b) as [[r b''] h] eqn:Heq.
  rewrite (successor_costs_more_eq _ _ _ _ _ _ Heq).
  reflexivity.
Qed.

(******************************************************************************)
(* Collapse UnknownÃ¢â€ â€™false (WITH SPUREN)                                        *)
(******************************************************************************)

Definition collapse3 (r : Bool3) : bool :=
  match r with BTrue => true | _ => false end.

Definition fin_eq_b_spur (n m : Fin) (b : Budget) : (bool * Budget * Spuren) :=
  match fin_eq_b3 n m b with
  | (r, b', h) => (collapse3 r, b', h)
  end.

Definition le_fin_b_spur (n m : Fin) (b : Budget) : (bool * Budget * Spuren) :=
  match le_fin_b3 n m b with
  | (r, b', h) => (collapse3 r, b', h)
  end.

(******************************************************************************)
(* INTERVAL RESULTS & DECISION VARIANTS (use 3-valued core)                   *)
(******************************************************************************)

Inductive FinInterval : Type :=
  | Exact : Fin -> FinInterval
  | Range : Fin -> Fin -> FinInterval.

Definition min_fin_interval (n m : Fin) (b : Budget)
  : (FinInterval * Budget * Spuren) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (Exact n, b', h)
  | (BFalse, b', h)   => (Exact m, b', h)
  | (BUnknown, b', h) => (Range n m, b', h)
  end.

Definition max_fin_interval (n m : Fin) (b : Budget)
  : (FinInterval * Budget * Spuren) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (Exact m, b', h)
  | (BFalse, b', h)   => (Exact n, b', h)
  | (BUnknown, b', h) => (Range n m, b', h)
  end.

Definition min_fin_dec (n m : Fin) (b : Budget)
  : (Fin * Bool3 * Budget * Spuren) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (n, BTrue, b', h)
  | (BFalse, b', h)   => (m, BFalse, b', h)
  | (BUnknown, b', h) => (n, BUnknown, b', h)
  end.

Definition max_fin_dec (n m : Fin) (b : Budget)
  : (Fin * Bool3 * Budget * Spuren) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (m, BTrue, b', h)
  | (BFalse, b', h)   => (n, BFalse, b', h)
  | (BUnknown, b', h) => (m, BUnknown, b', h)
  end.

(******************************************************************************)
(* Arithmetic on Fin with budget/Spuren                                        *)
(******************************************************************************)

Fixpoint sub_saturate_b_spur (n m : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match b with
  | fz => (fz, fz, fz)
  | fs b' =>
      match n, m with
      | _,  fz      => (n, b', fs fz)
      | fz, _       => (fz, b', fs fz)
      | fs n', fs m' =>
          match sub_saturate_b_spur n' m' b' with
          | (r, b'', h) => (r, b'', fs h)
          end
      end
  end.

Fixpoint add_fin_b_spur (n m : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match m, b with
  | fz, _   => (n, b, fz)
  | _,  fz  => (n, fz, fz)
  | fs m', fs b' =>
      match add_fin_b_spur n m' b' with
      | (r, b'', h) => (fs r, b'', fs h)
      end
  end.

Definition dist_fin_b_spur (n m : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match le_fin_b3 n m b with
  | (BTrue,  b', h1) =>
      match sub_saturate_b_spur m n b' with
      | (d, b'', h2) => (d, b'', add_spur h1 h2)
      end
  | (BFalse, b', h1) =>
      match sub_saturate_b_spur n m b' with
      | (d, b'', h2) => (d, b'', add_spur h1 h2)
      end
  | (BUnknown, b', h) => (fz, b', h)
  end.

(******************************************************************************)
(* ASSIMILATE - THE BREATH PRIMITIVE                                         *)
(*                                                                            *)
(* Dual of spend. spend DECREASES budget and emits Spuren equal to the       *)
(* amount spent. assimilate INCREASES budget and emits Spuren equal to the   *)
(* amount ingested. In both, every tick of motion leaves exactly one tick    *)
(* of trace. There is no free lunch even when you are eating.                *)
(*                                                                            *)
(* Recursion is on gain, not on budget. That matters: gain comes from the    *)
(* collision with another contour, not from the system's own reserves. The   *)
(* cost of transduction is paid in Spuren, not in budget.                    *)
(*                                                                            *)
(* Dulcinea note: there is no regime in which assimilate is free. h = gain   *)
(* exactly, proved below. A semipermeable boundary is a finite filter, not   *)
(* a backdoor to infinity.                                                    *)
(*                                                                            *)
(* The primitive does NOT enforce cap. Callers (the membrane layer) must     *)
(* truncate gain so that b + gain <= cap m before invoking this primitive.   *)
(* At THIS layer, assimilate is pure structural addition with bookkeeping.   *)
(******************************************************************************)

Fixpoint assimilate_b_spur (gain : Fin) (b : Budget) : (Budget * Spuren) :=
  match gain with
  | fz => (b, fz)
  | fs gain' =>
      match assimilate_b_spur gain' b with
      | (b', h) => (fs b', fs h)
      end
  end.

Definition safe_succ_b_spur (n : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match b with
  | fz => (n, fz, fz)
  | fs b' => (fs n, b', fs fz)
  end.

Lemma no_free_lunch_sub_aux : forall n m b,
  snd (sub_saturate_b_spur n m (fs b)) <> fz.
Proof.
  intros n m b; revert n m.
  induction b as [| b0 IH].
  - intros [|n'] [|m'].
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. destruct (sub_saturate_b_spur n' m' fz) as [[r b1] h1].
      simpl. discriminate.
  - intros [|n'] [|m'].
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. destruct (sub_saturate_b_spur n' m' (fs b0)) as [[r b1] h1].
      simpl. discriminate.
Qed.

Lemma no_free_lunch_sub : forall n m b res b' h,
  sub_saturate_b_spur n m (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros n m b res b' h Heq.
  pose proof (no_free_lunch_sub_aux n m b) as H.
  rewrite Heq in H. simpl in H. exact H.
Qed.

Lemma no_free_lunch_add_aux : forall n m b,
  snd (add_fin_b_spur n (fs m) (fs b)) <> fz.
Proof.
  intros n m b. simpl.
  destruct (add_fin_b_spur n m b) as [[r b1] h1].
  simpl. discriminate.
Qed.

Lemma no_free_lunch_add : forall n m b res b' h,
  add_fin_b_spur n (fs m) (fs b) = (res, b', h) -> h <> fz.
Proof.
  intros n m b res b' h Heq.
  pose proof (no_free_lunch_add_aux n m b) as H.
  rewrite Heq in H. simpl in H. exact H.
Qed.

(* Breath still costs: a positive gain always emits positive Spuren.         *)
Lemma no_free_lunch_assimilate_aux : forall gain b,
  snd (assimilate_b_spur (fs gain) b) <> fz.
Proof.
  intros gain b. simpl.
  destruct (assimilate_b_spur gain b) as [b' h].
  simpl. discriminate.
Qed.

Lemma no_free_lunch_assimilate : forall gain b b' h,
  assimilate_b_spur (fs gain) b = (b', h) -> h <> fz.
Proof.
  intros gain b b' h Heq.
  pose proof (no_free_lunch_assimilate_aux gain b) as H.
  rewrite Heq in H. simpl in H. exact H.
Qed.

(* The central identity: Spuren emitted by assimilation equals gain ingested. *)
(* Every fs of gain leaves exactly one fs of trace. No smuggling.             *)
Lemma assimilate_spuren_equals_gain : forall gain b b' h,
  assimilate_b_spur gain b = (b', h) -> h = gain.
Proof.
  induction gain as [| gain' IH]; intros b b' h Heq.
  - (* gain = fz: returns (b, fz) *)
    simpl in Heq. inversion Heq; subst. reflexivity.
  - (* gain = fs gain': recurse *)
    simpl in Heq.
    destruct (assimilate_b_spur gain' b) as [b1 h1] eqn:Hassim.
    inversion Heq; subst.
    f_equal. exact (IH _ _ _ Hassim).
Qed.

(* Budget growth: final budget is initial budget plus Spuren (= plus gain). *)
(* This is the breath analogue of spend's conservation law, flipped:         *)
(*   spend:      add_spur h b' = b         (budget shrinks, trace grows)     *)
(*   assimilate: b' = add_spur b h         (budget grows, trace also grows)  *)
(* The trace is honestly on the left of the equation in both cases --        *)
(* it is never hidden.                                                        *)
Lemma assimilate_budget_growth : forall gain b b' h,
  assimilate_b_spur gain b = (b', h) -> b' = add_spur b h.
Proof.
  induction gain as [| gain' IH]; intros b b' h Heq.
  - (* gain = fz: returns (b, fz), add_spur b fz = b. *)
    simpl in Heq. inversion Heq; subst. simpl. reflexivity.
  - (* gain = fs gain': recurse *)
    simpl in Heq.
    destruct (assimilate_b_spur gain' b) as [b1 h1] eqn:Hassim.
    inversion Heq; subst.
    rewrite (IH _ _ _ Hassim).
    simpl. reflexivity.
Qed.

(* Corollary: the budget after assimilation equals the initial budget plus  *)
(* the gain ingested. Combines the two lemmas above.                        *)
Corollary assimilate_budget_equals_gain_plus_start :
  forall gain b b' h,
  assimilate_b_spur gain b = (b', h) -> b' = add_spur b gain.
Proof.
  intros gain b b' h Heq.
  rewrite (assimilate_budget_growth _ _ _ _ Heq).
  rewrite (assimilate_spuren_equals_gain _ _ _ _ Heq).
  reflexivity.
Qed.

Fixpoint mult_fin_spur (n m : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match m with
  | fz => (fz, b, fz)
  | fs m' =>
      match b with
      | fz => (fz, fz, fz)
      | fs b' =>
          match mult_fin_spur n m' b' with
          | (prod, b'', h1) =>
              match add_fin_b_spur prod n b'' with
              | (result, b''', h2) => (result, b''', fs (add_spur h1 h2))
              end
          end
      end
  end.

Fixpoint div_helper_spur (n m fuel : Fin) (acc : Fin) (b : Budget) 
  : (Fin * Fin * Budget * Spuren) :=
  match fuel with
  | fz => (acc, n, b, fz)
  | fs fuel' =>
      match b with
      | fz => (acc, n, fz, fz)
      | fs b' =>
          match le_fin_b_spur m n b' with
          | (true, b'', h1) =>
              match sub_saturate_b_spur n m b'' with
              | (n', b''', h2) =>
                  match b''' with
                  | fz => (acc, n', fz, fs (add_spur h1 h2))
                  | fs _ =>
                      match div_helper_spur n' m fuel' (fs acc) b''' with
                      | (q, r, b_final, h3) =>
                          (q, r, b_final, fs (add_spur (add_spur h1 h2) h3))
                      end
                  end
              end
          | (false, b'', h) => (acc, n, b'', fs h)
          end
      end
  end.

Definition div_fin_spur (n m : Fin) (b : Budget) : (Fin * Fin * Budget * Spuren) :=
  match m with
  | fz => (fz, n, b, fz)
  | _ => div_helper_spur n m n fz b
  end.

(******************************************************************************)
(* STATE TRANSITIONS WITH BUDGET AND HEAT                                    *)
(******************************************************************************)

Definition succ_with_spur (s : State) : (State * Spuren) :=
  match s with
  | (n, fz) => ((n, fz), fz)
  | (n, fs b') => ((fs n, b'), fs fz)
  end.

Fixpoint bounded_iter_with_spur (k : Fin) (f : State -> (State * Spuren)) (s : State)
  : (State * Spuren) :=
  match k with
  | fz => (s, fz)
  | fs k' =>
      match snd s with
      | fz => (s, fz)
      | _ =>
          match f s with
          | (s', h1) =>
              match bounded_iter_with_spur k' f s' with
              | (s'', h2) => (s'', add_spur h1 h2)
              end
          end
      end
  end.

(******************************************************************************)
(* CONSTRUCTION WITH COST AND HEAT                                           *)
(******************************************************************************)

(* NOTE: mk_fin_b_spur takes a Fin template, NOT nat.
   This keeps the entire construction pipeline within Fin — no infinity leak. *)
Fixpoint mk_fin_b_spur (n : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match n with
  | fz => (fz, b, fz)
  | fs n' =>
      match b with
      | fz => (fz, fz, fz)
      | fs b' =>
          match mk_fin_b_spur n' b' with
          | (f, b'', h) => (fs f, b'', fs h)
          end
      end
  end.

Definition make_two_spur   (b : Budget) : (Fin * Budget * Spuren) := mk_fin_b_spur (fs (fs fz)) b.
Definition make_three_spur (b : Budget) : (Fin * Budget * Spuren) := mk_fin_b_spur (fs (fs (fs fz))) b.
Definition make_five_spur  (b : Budget) : (Fin * Budget * Spuren) := mk_fin_b_spur (fs (fs (fs (fs (fs fz))))) b.
Definition make_ten_spur   (b : Budget) : (Fin * Budget * Spuren) := mk_fin_b_spur (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))) b.

(******************************************************************************)
(* BACKWARD COMPATIBILITY - Operations that return pairs, not triples        *)
(******************************************************************************)

Definition fin_eq_b (n m : Fin) (b : Budget) : (bool * Budget) :=
  match fin_eq_b_spur n m b with
  | (res, b', _) => (res, b')
  end.

Definition le_fin_b (n m : Fin) (b : Budget) : (bool * Budget) :=
  match le_fin_b_spur n m b with
  | (res, b', _) => (res, b')
  end.

Definition sub_saturate_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match sub_saturate_b_spur n m b with
  | (res, b', _) => (res, b')
  end.

Definition sub_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  sub_saturate_b n m b.

Definition add_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match add_fin_b_spur n m b with
  | (res, b', _) => (res, b')
  end.

Definition add_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  add_fin_b n m b.

Definition dist_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match dist_fin_b_spur n m b with
  | (res, b', _) => (res, b')
  end.

Definition safe_succ_b (n : Fin) (b : Budget) : (Fin * Budget) :=
  match safe_succ_b_spur n b with
  | (res, b', _) => (res, b')
  end.

Definition mult_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match mult_fin_spur n m b with
  | (res, b', _) => (res, b')
  end.

Definition div_fin (n m : Fin) (b : Budget) : (Fin * Fin * Budget) :=
  match div_fin_spur n m b with
  | (q, r, b', _) => (q, r, b')
  end.

Definition min_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => (n, b')
  | (false, b') => (m, b')
  end.

Definition max_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => (m, b')
  | (false, b') => (n, b')
  end.

Definition mk_fin_b (n : Fin) (b : Budget) : (Fin * Budget) :=
  match mk_fin_b_spur n b with
  | (res, b', _) => (res, b')
  end.

(* fin_from_fin_b: renamed from fin_from_nat_b — nat eliminated *)
Definition fin_from_fin_b (n : Fin) (b : Budget) : (Fin * Budget) :=
  mk_fin_b n b.

Definition make_two   (b : Budget) : (Fin * Budget) := mk_fin_b (fs (fs fz)) b.
Definition make_three (b : Budget) : (Fin * Budget) := mk_fin_b (fs (fs (fs fz))) b.
Definition make_five  (b : Budget) : (Fin * Budget) := mk_fin_b (fs (fs (fs (fs (fs fz))))) b.
Definition make_ten   (b : Budget) : (Fin * Budget) := mk_fin_b (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))) b.

(******************************************************************************)
(* STATE TRANSITIONS (no Spuren)                                              *)
(******************************************************************************)

Definition succ (s : State) : State :=
  match s with
  | (n, fz) => (n, fz)
  | (n, fs b') => (fs n, b')
  end.

Fixpoint bounded_iter (k : Fin) (f : State -> State) (s : State) : State :=
  match k with
  | fz => s
  | fs k' =>
      match snd s with
      | fz => s
      | _ => bounded_iter k' f (f s)
      end
  end.

(******************************************************************************)
(* NON-BUDGETED WRAPPERS (use initial_budget)                               *)
(******************************************************************************)

Definition fin_eq (n m : Fin) : bool :=
  fst (fin_eq_b n m initial_budget).

Definition le_fin (n m : Fin) : bool :=
  fst (le_fin_b n m initial_budget).

Definition add_simple (n m : Fin) : Fin :=
  fst (add_fin_b n m initial_budget).

Definition sub_simple (n m : Fin) : Fin :=
  fst (sub_saturate_b n m initial_budget).

Definition dist_fin (n m : Fin) : Fin :=
  fst (dist_fin_b n m initial_budget).

Definition min_fin (n m : Fin) : Fin :=
  fst (min_fin_b n m initial_budget).

Definition max_fin (n m : Fin) : Fin :=
  fst (max_fin_b n m initial_budget).

Definition fin_eq_LEGACY := fin_eq.
Definition le_fin_LEGACY := le_fin.
Definition add_simple_LEGACY := add_simple.


(******************************************************************************)
(* SPUR CONSERVATION LAW - PROVEN by structural induction                    *)
(*                                                                            *)
(* Previously Axiom. Now Qed. The proof follows the recursion of each        *)
(* operation: each step consumes one fs from budget and produces one fs of    *)
(* Spuren, so Spuren + remaining budget = original budget.                       *)
(******************************************************************************)

(* Helper: add_spur with fz on the left is identity *)
Lemma add_spur_fz_l : forall b, add_spur fz b = b.
Proof.
  induction b as [| b' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Helper: add_spur distributes over fs on the left *)
Lemma add_spur_fs_l : forall a b, add_spur (fs a) b = fs (add_spur a b).
Proof.
  intros a b; induction b as [| b' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Spuren addition is associative *)
Lemma add_spur_assoc : forall a b c,
  add_spur (add_spur a b) c = add_spur a (add_spur b c).
Proof.
  intros a b c; induction c as [| c' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma spur_conservation_eq3 : forall n m b b' res h,
  fin_eq_b3 n m b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros n m b; revert n m.
  induction b as [| b0 IH]; intros n m b' res h Heq.
  - (* b = fz: returns (BUnknown, fz, fz) — destruct n,m for simpl *)
    destruct n, m; simpl in Heq; inversion Heq; subst; reflexivity.
  - (* b = fs b0 — destruct n,m first so simpl can fire *)
    destruct n as [| n']; destruct m as [| m']; simpl in Heq.
    + (* fz, fz → (BTrue, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fz, fs m' → (BFalse, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fs n', fz → (BFalse, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fs n', fs m' → recurse with (r, b1, fs h1) *)
      destruct (fin_eq_b3 n' m' b0) as [[r b1] h1] eqn:Hle.
      inversion Heq; subst.
      rewrite add_spur_fs_l. f_equal. exact (IH _ _ _ _ _ Hle).
Qed.

(* Conservation for addition: each fs of m costs one fs of budget *)
Lemma spur_conservation_add : forall n m b b' res h,
  add_fin_b_spur n m b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros n m; revert n.
  induction m as [| m' IH]; intros n b b' res h Heq.
  - (* m = fz: returns (n, b, fz), goal: add_spur fz b = b *)
    simpl in Heq. inversion Heq; subst. apply add_spur_fz_l.
  - (* m = fs m' *)
    destruct b as [| b0].
    + (* b = fz: returns (n, fz, fz) *)
      simpl in Heq. inversion Heq; subst. reflexivity.
    + (* b = fs b0 *)
      simpl in Heq.
      destruct (add_fin_b_spur n m' b0) as [[r b1] h1] eqn:Hadd.
      inversion Heq; subst.
      rewrite add_spur_fs_l. f_equal. exact (IH _ _ _ _ _ Hadd).
Qed.

(* Conservation for subtraction: each step costs one fs of budget *)
Lemma spur_conservation_sub : forall n m b b' res h,
  sub_saturate_b_spur n m b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros n m b; revert n m.
  induction b as [| b0 IH]; intros n m b' res h Heq.
  - (* b = fz: returns (fz, fz, fz) — destruct n,m for simpl *)
    destruct n, m; simpl in Heq; inversion Heq; subst; reflexivity.
  - (* b = fs b0 — destruct n,m first so simpl can fire *)
    destruct n as [| n']; destruct m as [| m']; simpl in Heq.
    + (* fz, fz → (fz, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fz, fs m' → (fz, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fs n', fz → (fs n', b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fs n', fs m' → recurse *)
      destruct (sub_saturate_b_spur n' m' b0) as [[r b1] h1] eqn:Hsub.
      inversion Heq; subst.
      rewrite add_spur_fs_l. f_equal. exact (IH _ _ _ _ _ Hsub).
Qed.

(* Conservation for multiplication: each recursive step costs one tick *)
Lemma spur_conservation_mult : forall n m b b' res h,
  mult_fin_spur n m b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros n m; revert n.
  induction m as [| m' IH]; intros n b b' res h Heq.
  - (* m = fz: returns (fz, b, fz) *)
    simpl in Heq. inversion Heq; subst. apply add_spur_fz_l.
  - (* m = fs m' *)
    destruct b as [| b0].
    + (* b = fz: returns (fz, fz, fz) *)
      simpl in Heq. inversion Heq; subst. reflexivity.
    + (* b = fs b0 *)
      simpl in Heq.
      destruct (mult_fin_spur n m' b0) as [[prod b''] h1] eqn:Hmult.
      destruct (add_fin_b_spur prod n b'') as [[result b'''] h2] eqn:Hadd.
      inversion Heq; subst.
      rewrite add_spur_fs_l. f_equal.
      rewrite add_spur_assoc.
      rewrite (spur_conservation_add _ _ _ _ _ _ Hadd).
      exact (IH _ _ _ _ _ Hmult).
Qed.

Lemma spur_conservation_le3 : forall n m b b' res h,
  le_fin_b3 n m b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros n m b; revert n m.
  induction b as [| b0 IH]; intros n m b' res h Heq.
  - (* b = fz: returns (BUnknown, fz, fz) — destruct n for simpl *)
    destruct n; simpl in Heq; inversion Heq; subst; reflexivity.
  - (* b = fs b0 — destruct n first so simpl can fire *)
    destruct n as [| n']; [| destruct m as [| m']]; simpl in Heq.
    + (* fz, _ → (BTrue, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fs n', fz → (BFalse, b0, fs fz) *)
      inversion Heq; subst. rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + (* fs n', fs m' → recurse with (r, b1, fs h1) *)
      destruct (le_fin_b3 n' m' b0) as [[r b1] h1] eqn:Hle.
      inversion Heq; subst.
      rewrite add_spur_fs_l. f_equal. exact (IH _ _ _ _ _ Hle).
Qed.

(* Conservation for le_fin_b_spur: wraps le_fin_b3 with collapse3 *)
Lemma spur_conservation_le_b_spur : forall n m b br b' h,
  le_fin_b_spur n m b = (br, b', h) -> add_spur h b' = b.
Proof.
  intros n m b br b' h Heq.
  unfold le_fin_b_spur in Heq.
  destruct (le_fin_b3 n m b) as [[r b1] h1] eqn:Hle3.
  inversion Heq; subst.
  exact (spur_conservation_le3 _ _ _ _ _ _ Hle3).
Qed.

(* Conservation for div_helper_spur: induction on fuel *)
Lemma spur_conservation_div_helper : forall fuel n m acc b q r b' h,
  div_helper_spur n m fuel acc b = (q, r, b', h) -> add_spur h b' = b.
Proof.
  induction fuel as [| fuel' IH]; intros n m acc b q r b' h Heq.
  - (* fuel = fz: returns (acc, n, b, fz) *)
    simpl in Heq. inversion Heq; subst. apply add_spur_fz_l.
  - (* fuel = fs fuel' *)
    simpl in Heq.
    destruct b as [| b0].
    + (* b = fz: returns (acc, n, fz, fz) *)
      inversion Heq; subst. reflexivity.
    + (* b = fs b0 *)
      destruct (le_fin_b_spur m n b0) as [[br b1] h1] eqn:Hle.
      destruct br.
      * (* br = true: m <= n *)
        destruct (sub_saturate_b_spur n m b1) as [[n' b2] h2] eqn:Hsub.
        destruct b2 as [| b2'].
        -- (* b2 = fz: early termination *)
           inversion Heq; subst.
           rewrite add_spur_fs_l. f_equal. simpl.
           (* goal: add_spur h1 h2 = b0 *)
           (* h2 + fz = b1 => h2 = b1, then h1 + b1 = b0 *)
           pose proof (spur_conservation_sub _ _ _ _ _ _ Hsub) as Hsub_cons.
           simpl in Hsub_cons. rewrite Hsub_cons.
           exact (spur_conservation_le_b_spur _ _ _ _ _ _ Hle).
        -- (* b2 = fs b2': recurse *)
           destruct (div_helper_spur n' m fuel' (fs acc) (fs b2')) as [[[q0 r0] b_final] h3] eqn:Hdiv.
           inversion Heq; subst.
           rewrite add_spur_fs_l. f_equal.
           (* goal: add_spur (add_spur (add_spur h1 h2) h3) b_final = b0 *)
           rewrite add_spur_assoc. rewrite add_spur_assoc.
           (* goal: add_spur h1 (add_spur h2 (add_spur h3 b_final)) = b0 *)
           rewrite (IH _ _ _ _ _ _ _ _ Hdiv).
           (* goal: add_spur h1 (add_spur h2 (fs b2')) = b0 *)
           rewrite (spur_conservation_sub _ _ _ _ _ _ Hsub).
           (* goal: add_spur h1 b1 = b0 *)
           exact (spur_conservation_le_b_spur _ _ _ _ _ _ Hle).
      * (* br = false: m > n *)
        inversion Heq; subst.
        rewrite add_spur_fs_l. f_equal.
        exact (spur_conservation_le_b_spur _ _ _ _ _ _ Hle).
Qed.

(* Conservation for div_fin_spur: delegates to div_helper *)
Lemma spur_conservation_div : forall n m b q r b' h,
  div_fin_spur n m b = (q, r, b', h) -> add_spur h b' = b.
Proof.
  intros n m b q r b' h Heq.
  unfold div_fin_spur in Heq.
  destruct m as [| m'].
  - (* m = fz: returns (fz, n, b, fz) *)
    inversion Heq; subst. apply add_spur_fz_l.
  - (* m = fs m': delegates to div_helper_spur *)
    exact (spur_conservation_div_helper _ _ _ _ _ _ _ _ _ Heq).
Qed.

(* ================================================================ *)
(* SECTION: Thermodynamic Opening — Membrane                         *)
(* ================================================================ *)

(* A closed system with finite budget dies (time_irreversible +
   cascading_blindness). Living systems are operationally closed
   but thermodynamically open (Maturana/Varela, Schrodinger).
   Historically this section had a Record External as an 'opaque
   source of budget from outside'. That was a reification of
   observer/observed dualism. In the current frame every encounter
   is a collision of TWO contours — two Membranes. External znikl. *)

(* Membrane: a contour. It has a prototype (its geometric center),
   a tolerance (how wide the contour reaches), a capacity (the
   maximum budget its shape admits per intake — cap is a function
   of this geometry, not a decree of the world), and its current
   budget (the present tension of the contour). *)

(* Membrana jest rekurencyjnie zlozona: kazdy kontur moze zawierac
   liste wewnetrznych konturow (mem_inner). Atomowa membrana ma
   mem_inner = nil. Roznica miedzy "atomowa" a "zlozona" jest
   ilosciowa, nie jakosciowa: wszystkie membrany sa emergentnymi
   produktami percepcji, atomowe to po prostu te ktore wchlonely
   malo lub nic. *)

Inductive Membrane : Type := mkMembrane {
  mem_filter_center : list (Fin * Fin);  (* prototype of what passes through *)
  mem_filter_radius : Fin;               (* tolerance — how far from prototype *)
  mem_capacity : Fin;                    (* max budget admitted per intake *)
  mem_budget : Budget;                   (* membrane own budget for filtration *)
  mem_inner : list Membrane;             (* sub-contours; nil for atomic *)
}.
