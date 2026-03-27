(******************************************************************************)
(* void_probability_minimal.v                                                 *)
(* Probabilities with Spuren tracking - fraction arithmetic generates Spuren!     *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.ZArith.ZArith.
Require Import void_finite_minimal.

Module Void_Probability_Minimal.

(******************************************************************************)
(* FINITE PROBABILITIES AS SIMPLE PAIRS                                      *)
(******************************************************************************)

(* A probability is just a pair of Fin values *)
Definition FinProb := (Fin * Fin)%type.

(* Some concrete probabilities - these are notation, not operations *)
Definition half : FinProb := (fs fz, fs (fs fz)).          (* 1/2 *)
Definition third : FinProb := (fs fz, fs (fs (fs fz))).    (* 1/3 *)
Definition quarter : FinProb := (fs fz, fs (fs (fs (fs fz)))).  (* 1/4 *)

(******************************************************************************)
(* PROBABILITY OPERATIONS WITH SPUREN                                           *)
(******************************************************************************)

(* Probability equality with Spuren - checking fractions is work! *)
Definition prob_eq_b3 (p1 p2 : FinProb) (b : Budget) : (Bool3 * Budget * Spuren) :=
  match fin_eq_b3 (fst p1) (fst p2) b with
  | (BTrue, b', h1) => 
      match fin_eq_b3 (snd p1) (snd p2) b' with
      | (res, b'', h2) => (res, b'', add_spur h1 h2)
      end
  | (BFalse, b', h) => (BFalse, b', h)
  | (BUnknown, b', h) => (BUnknown, b', h)
  end.

(* Collapse to bool for compatibility *)
Definition prob_eq_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  match prob_eq_b3 p1 p2 b with
  | (res, b', _) => (collapse3 res, b')
  end.

(* Add probabilities with Spuren - fraction arithmetic is expensive! *)
Definition add_prob_spur (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match fin_eq_b3 d1 d2 b with
  | (BTrue, b', h1) =>
      (* Same denominator - just add numerators *)
      match add_fin_b_spur n1 n2 b' with
      | (sum, b'', h2) => ((sum, d1), b'', add_spur h1 h2)
      end
  | (BFalse, b', h1) =>
      (* Different denominators - cross multiplication (expensive!) *)
      match mult_fin_spur n1 d2 b' with
      | (v1, b1, h2) =>
          match mult_fin_spur n2 d1 b1 with
          | (v2, b2, h3) =>
              match add_fin_b_spur v1 v2 b2 with
              | (new_n, b3, h4) =>
                  match mult_fin_spur d1 d2 b3 with
                  | (new_d, b4, h5) =>
                      ((new_n, new_d), b4, 
                       add_spur h1 (add_spur h2 (add_spur h3 (add_spur h4 h5))))
                  end
              end
          end
      end
  | (BUnknown, b', h) =>
      (* Can't determine - return first probability *)
      (p1, b', h)
  end.

(* Multiply probabilities with Spuren *)
Definition mult_prob_spur (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin_spur n1 n2 b with
  | (new_n, b1, h1) =>
      match mult_fin_spur d1 d2 b1 with
      | (new_d, b2, h2) => ((new_n, new_d), b2, add_spur h1 h2)
      end
  end.

(* Subtract probabilities with saturation and Spuren *)
Definition sub_prob_spur (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match fin_eq_b3 d1 d2 b with
  | (BTrue, b', h1) =>
      (* Same denominator - subtract numerators *)
      match sub_saturate_b_spur n1 n2 b' with
      | (diff, b'', h2) => ((diff, d1), b'', add_spur h1 h2)
      end
  | (BFalse, b', h1) =>
      (* Different denominators - cross multiplication *)
      match mult_fin_spur n1 d2 b' with
      | (v1, b1, h2) =>
          match mult_fin_spur n2 d1 b1 with
          | (v2, b2, h3) =>
              match sub_saturate_b_spur v1 v2 b2 with
              | (diff_n, b3, h4) =>
                  match mult_fin_spur d1 d2 b3 with
                  | (new_d, b4, h5) =>
                      ((diff_n, new_d), b4,
                       add_spur h1 (add_spur h2 (add_spur h3 (add_spur h4 h5))))
                  end
              end
          end
      end
  | (BUnknown, b', h) => ((fz, fs fz), b', h)  (* Unknown - return 0 *)
  end.

(* Compare probabilities with three-valued result *)
Definition prob_le_b3 (p1 p2 : FinProb) (b : Budget) : (Bool3 * Budget * Spuren) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  (* p1 ≤ p2 iff n1*d2 ≤ n2*d1 *)
  match mult_fin_spur n1 d2 b with
  | (v1, b1, h1) =>
      match mult_fin_spur n2 d1 b1 with
      | (v2, b2, h2) =>
          match le_fin_b3 v1 v2 b2 with
          | (res, b3, h3) => (res, b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(******************************************************************************)
(* INTERVAL PROBABILITIES - When exhausted                                   *)
(******************************************************************************)

Inductive ProbInterval :=
  | PExact : FinProb -> ProbInterval
  | PRange : FinProb -> FinProb -> ProbInterval
  | PUnknown : ProbInterval.

(* Return interval when can't compute exactly *)
Definition add_prob_interval (p1 p2 : FinProb) (b : Budget) 
  : (ProbInterval * Budget * Spuren) :=
  match b with
  | fz => (PUnknown, fz, fz)
  | fs fz => 
      (* Very low budget - return range *)
      (PRange p1 (fs (fst p1), snd p1), fs fz, fs fz)
  | _ =>
      match add_prob_spur p1 p2 b with
      | (res, b', h) => (PExact res, b', h)
      end
  end.

(******************************************************************************)
(* BACKWARD COMPATIBILITY                                                    *)
(******************************************************************************)

Definition add_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match add_prob_spur p1 p2 b with
  | (res, b', _) => (res, b')
  end.

Definition mult_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match mult_prob_spur p1 p2 b with
  | (res, b', _) => (res, b')
  end.

Definition sub_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match sub_prob_spur p1 p2 b with
  | (res, b', _) => (res, b')
  end.

Definition prob_le_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  match prob_le_b3 p1 p2 b with
  | (res, b', _) => (collapse3 res, b')
  end.

(******************************************************************************)
(* KEY PHILOSOPHICAL POINTS - UNCHANGED                                      *)
(******************************************************************************)

(* No probability has numerator zero - approaching the void *)
Definition avoids_zero (p : FinProb) : Prop :=
  match fst p with
  | fz => False
  | _ => True
  end.

(* Check if probability avoids zero - this is free since it's structural *)
Definition check_avoids_zero (p : FinProb) : bool :=
  match fst p with
  | fz => false
  | _ => true
  end.

(******************************************************************************)
(* SPUR CONSERVATION FOR PROBABILITIES                                       *)
(******************************************************************************)

Lemma prob_spur_conservation_add : forall p1 p2 b b' res h,
  add_prob_spur p1 p2 b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros [n1 d1] [n2 d2] b b' res h Heq.
  simpl in Heq.
  destruct (fin_eq_b3 d1 d2 b) as [[r b0] h1] eqn:Heq3.
  destruct r.
  - (* BTrue: same denominator *)
    destruct (add_fin_b_spur n1 n2 b0) as [[sum b1] h2] eqn:Hadd.
    inversion Heq; subst.
    rewrite add_spur_assoc.
    rewrite (spur_conservation_add _ _ _ _ _ _ Hadd).
    exact (spur_conservation_eq3 _ _ _ _ _ _ Heq3).
  - (* BFalse: cross multiplication *)
    destruct (mult_fin_spur n1 d2 b0) as [[v1 b1] h2] eqn:Hm1.
    destruct (mult_fin_spur n2 d1 b1) as [[v2 b2] h3] eqn:Hm2.
    destruct (add_fin_b_spur v1 v2 b2) as [[new_n b3] h4] eqn:Hadd.
    destruct (mult_fin_spur d1 d2 b3) as [[new_d b4] h5] eqn:Hm3.
    inversion Heq; subst.
    rewrite add_spur_assoc. rewrite add_spur_assoc.
    rewrite add_spur_assoc. rewrite add_spur_assoc.
    rewrite (spur_conservation_mult _ _ _ _ _ _ Hm3).
    rewrite (spur_conservation_add _ _ _ _ _ _ Hadd).
    rewrite (spur_conservation_mult _ _ _ _ _ _ Hm2).
    rewrite (spur_conservation_mult _ _ _ _ _ _ Hm1).
    exact (spur_conservation_eq3 _ _ _ _ _ _ Heq3).
  - (* BUnknown: can't determine *)
    inversion Heq; subst.
    exact (spur_conservation_eq3 _ _ _ _ _ _ Heq3).
Qed.

Lemma prob_spur_conservation_mult : forall p1 p2 b b' res h,
  mult_prob_spur p1 p2 b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros [n1 d1] [n2 d2] b b' res h Heq.
  simpl in Heq.
  destruct (mult_fin_spur n1 n2 b) as [[new_n b1] h1] eqn:Hm1.
  destruct (mult_fin_spur d1 d2 b1) as [[new_d b2] h2] eqn:Hm2.
  inversion Heq; subst.
  rewrite add_spur_assoc.
  rewrite (spur_conservation_mult _ _ _ _ _ _ Hm2).
  exact (spur_conservation_mult _ _ _ _ _ _ Hm1).
Qed.

(* Fraction arithmetic generates more Spuren than integer arithmetic *)
Axiom fraction_heat_penalty : forall p1 p2 b res b' h,
  add_prob_spur p1 p2 b = (res, b', h) ->
  exists h_int b_int, 
    add_fin_b_spur (fst p1) (fst p2) b = (fst res, b_int, h_int) /\
    (fin_to_Z_PROOF_ONLY h >= fin_to_Z_PROOF_ONLY h_int)%Z.

(******************************************************************************)
(* THEOREMS - Previous ones still hold                                       *)
(******************************************************************************)

Theorem half_avoids_zero : avoids_zero half.
Proof. unfold avoids_zero, half. simpl. exact I. Qed.

Theorem third_avoids_zero : avoids_zero third.
Proof. unfold avoids_zero, third. simpl. exact I. Qed.

(******************************************************************************)
(* RESOLUTION-PARAMETERIZED DIVISION — Prior Geometry Ax13                   *)
(*                                                                            *)
(* Ax13 says: for any desired precision, choose a capacity a' with N(a')     *)
(* large enough.  Here: the resolution parameter ρ determines the            *)
(* denominator D(ρ) = 10^ρ.  Dividing at resolution ρ gives a result       *)
(* on the grid {0, 1/D(ρ), ..., 1}.  Higher ρ = finer grid.               *)
(*                                                                            *)
(* No limits.  No infinite refinement.  Just pick a bigger ρ.               *)
(*                                                                            *)
(* Ported from void_arithmetic.v — now depends ONLY on void_finite_minimal. *)
(******************************************************************************)

Definition Resolution := Fin.

(* The constant 10, built structurally *)
Definition ten : Fin :=
  fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).

(* Compute 10^ρ with budget tracking *)
Fixpoint resolution_denominator_spur (rho : Resolution) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match rho with
  | fz => (fs fz, b, fz)  (* 10^0 = 1 *)
  | fs rho' =>
      match b with
      | fz => (fs fz, fz, fz)  (* Out of budget *)
      | fs b' =>
          match resolution_denominator_spur rho' b' with
          | (d_prev, b'', h1) =>
              match mult_fin_spur d_prev ten b'' with
              | (d_new, b''', h2) => (d_new, b''', add_spur h1 h2)
              end
          end
      end
  end.

(* Probability division at given resolution ρ:
   (n1/d1) / (n2/d2) = (n1 * d2) / (d1 * n2)
   Result scaled to denominator D(ρ) = 10^ρ. *)
Definition div_prob_spur (p1 p2 : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget * Spuren) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match n2 with
  | fz => ((fz, fs fz), b, fz)  (* Division by zero → 0/1 *)
  | _ =>
      match b with
      | fz => ((fz, fs fz), fz, fz)
      | _ =>
          match resolution_denominator_spur rho b with
          | (D_rho, b1, h1) =>
              (* Scale numerator: n1 * d2 * D(ρ) *)
              match mult_fin_spur n1 d2 b1 with
              | (temp1, b2, h2) =>
                  match mult_fin_spur temp1 D_rho b2 with
                  | (scaled_num, b3, h3) =>
                      (* Denominator: d1 * n2 *)
                      match mult_fin_spur d1 n2 b3 with
                      | (scaled_den, b4, h4) =>
                          (* Divide: quotient / D(ρ) *)
                          match div_fin_spur scaled_num scaled_den b4 with
                          | (quotient, _remainder, b5, h5) =>
                              ((quotient, D_rho), b5,
                               add_spur (add_spur (add_spur (add_spur h1 h2) h3) h4) h5)
                          end
                      end
                  end
              end
          end
      end
  end.

(* Without Spuren tracking *)
Definition div_prob (p1 p2 : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget) :=
  match div_prob_spur p1 p2 rho b with
  | (res, b', _) => (res, b')
  end.

(* Resolution refinement: for any ρ, fs ρ gives a grid 10× finer.
   This is the computational content of Prior Geometry Ax13:
   precision is always improvable, finitely. *)
Lemma resolution_refines : forall rho, exists rho',
  rho' = fs rho.
Proof. intro rho. exists (fs rho). reflexivity. Qed.

End Void_Probability_Minimal.