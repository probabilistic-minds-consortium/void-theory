(******************************************************************************)
(* void_gates.v - PROBABILISTIC LOGIC GATES                                   *)
(* All operations are finite, all operations cost budget                      *)
(* NO INFINITY: no Nat, no Z, no R, no limits, no axiom of infinity          *)
(* SELF-CONTAINED: All arithmetic defined here                                *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Gates.

(******************************************************************************)
(* FINITE TYPES - from void_finite_minimal                                    *)
(******************************************************************************)

Inductive Fin : Type :=
  | fz : Fin
  | fs : Fin -> Fin.

Definition Budget := Fin.
Definition Spuren := Fin.

(* FinProb = (numerator, denominator) *)
Definition FinProb := (Fin * Fin)%type.

(******************************************************************************)
(* COMPARISON                                                                 *)
(******************************************************************************)

Fixpoint le_fin (n m : Fin) : bool :=
  match n, m with
  | fz, _ => true
  | fs _, fz => false
  | fs n', fs m' => le_fin n' m'
  end.

Fixpoint fin_eq (n m : Fin) : bool :=
  match n, m with
  | fz, fz => true
  | fs n', fs m' => fin_eq n' m'
  | _, _ => false
  end.

(******************************************************************************)
(* ARITHMETIC - all with budget tracking                                      *)
(******************************************************************************)

(* Predecessor - no cost, pure *)
Definition pred_fin (n : Fin) : Fin :=
  match n with
  | fz => fz
  | fs n' => n'
  end.

(* Addition with budget *)
Fixpoint add_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match m, b with
  | fz, _ => (n, b)
  | _, fz => (n, fz)  (* Exhausted *)
  | fs m', fs b' =>
      match add_fin_b (fs n) m' b' with
      | (result, b'') => (result, b'')
      end
  end.

(* Subtraction - saturating *)
Fixpoint sub_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match n, m, b with
  | _, fz, _ => (n, b)
  | fz, _, _ => (fz, b)
  | _, _, fz => (fz, fz)
  | fs n', fs m', fs b' => sub_fin n' m' b'
  end.

(* Multiplication with budget - O(n*m) cost *)
Fixpoint mul_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match n, b with
  | fz, _ => (fz, b)
  | _, fz => (fz, fz)
  | fs n', fs b' =>
      match mul_fin_b n' m b' with
      | (partial, b1) =>
          add_fin_b partial m b1
      end
  end.

(* Division helper with explicit fuel *)
Fixpoint div_fin_fuel (fuel : Fin) (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match fuel with
  | fz => (fz, b)  (* Fuel exhausted *)
  | fs fuel' =>
      match m, b with
      | fz, _ => (fz, b)        (* Division by zero = 0 *)
      | _, fz => (fz, fz)       (* Budget exhausted *)
      | _, fs b' =>
          match le_fin m n with
          | false => (fz, b')   (* m > n, result is 0 *)
          | true =>
              match sub_fin n m b' with
              | (diff, b1) =>
                  match div_fin_fuel fuel' diff m b1 with
                  | (quotient, b2) => (fs quotient, b2)
                  end
              end
          end
      end
  end.

(* Division: use n as fuel since n/m <= n *)
Definition div_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  div_fin_fuel n n m b.

(******************************************************************************)
(* CONSTANTS                                                                  *)
(******************************************************************************)

Definition fin1 : Fin := fs fz.
Definition fin2 : Fin := fs fin1.
Definition fin3 : Fin := fs fin2.
Definition fin5 : Fin := fs (fs fin3).
Definition fin8 : Fin := fs (fs (fs fin5)).
Definition fin9 : Fin := fs fin8.
Definition fin10 : Fin := fs fin9.

Definition resolution : Fin := fin10.
Definition prob_min : Fin := fin1.

Definition prob_max (den : Fin) : Fin :=
  match den with
  | fz => fz
  | fs d' => d'
  end.

Definition half : FinProb := (fin5, fin10).

(******************************************************************************)
(* CLAMPING                                                                   *)
(******************************************************************************)

Definition clamp_num (n den : Fin) : Fin :=
  match n with
  | fz => prob_min
  | _ => match le_fin n (prob_max den) with
         | true => n
         | false => prob_max den
         end
  end.

(******************************************************************************)
(* PROBABILITY ARITHMETIC                                                     *)
(******************************************************************************)

(* Multiply: (n1/d) * (n2/d) = n1*n2/d / d *)
Definition mul_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      let n1 := fst p1 in
      let n2 := fst p2 in
      let den := snd p1 in
      match mul_fin_b n1 n2 b' with
      | (product, b1) =>
          match div_fin_b product den b1 with
          | (scaled, b2) =>
              let clamped := clamp_num scaled den in
              ((clamped, den), b2)
          end
      end
  end.

(* Complement: 1 - p = (d - n) / d *)
Definition complement_b (p : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p, fz)
  | fs b' =>
      let n := fst p in
      let den := snd p in
      match sub_fin den n b' with
      | (diff, b1) =>
          let clamped := clamp_num diff den in
          ((clamped, den), b1)
      end
  end.

(******************************************************************************)
(* LOGIC GATES                                                                *)
(******************************************************************************)

(* AND: P(A ∧ B) = P(A) * P(B) *)
Definition gate_and_b (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  mul_prob_b a b budget.

(* OR: P(A ∨ B) = 1 - (1-A)(1-B) *)
Definition gate_or_b (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match complement_b a b0 with
      | (not_a, b1) =>
          match complement_b b b1 with
          | (not_b, b2) =>
              match mul_prob_b not_a not_b b2 with
              | (not_a_and_not_b, b3) =>
                  complement_b not_a_and_not_b b3
              end
          end
      end
  end.

(* NAND: P(¬(A ∧ B)) = 1 - P(A)*P(B) *)
Definition gate_nand_b (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match mul_prob_b a b b0 with
      | (a_and_b, b1) =>
          complement_b a_and_b b1
      end
  end.

(* NOR: P(¬(A ∨ B)) = (1-A)(1-B) *)
Definition gate_nor_b (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match complement_b a b0 with
      | (not_a, b1) =>
          match complement_b b b1 with
          | (not_b, b2) =>
              mul_prob_b not_a not_b b2
          end
      end
  end.

(* XOR: P(A ⊕ B) = AND(OR(A,B), NAND(A,B)) *)
Definition gate_xor_b (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match gate_or_b a b b0 with
      | (or_result, b1) =>
          match gate_nand_b a b b1 with
          | (nand_result, b2) =>
              gate_and_b or_result nand_result b2
          end
      end
  end.

(* XNOR: P(A ↔ B) = 1 - XOR(A,B) *)
Definition gate_xnor_b (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match gate_xor_b a b b0 with
      | (xor_result, b1) =>
          complement_b xor_result b1
      end
  end.

(* NOT: P(¬A) = 1 - P(A) *)
Definition gate_not_b (a : FinProb) (budget : Budget) : (FinProb * Budget) :=
  complement_b a budget.

(******************************************************************************)
(* SPUR TRACKING                                                              *)
(******************************************************************************)

Record GateResult := {
  result : FinProb;
  remaining_budget : Budget;
  spur_generated : Spuren
}.

Definition compute_spur (initial final : Budget) : Spuren :=
  fst (sub_fin initial final initial).

Definition gate_xor_spur (a b : FinProb) (budget : Budget) : GateResult :=
  let initial := budget in
  match gate_xor_b a b budget with
  | (res, remaining) =>
      {| result := res;
         remaining_budget := remaining;
         spur_generated := compute_spur initial remaining |}
  end.

(******************************************************************************)
(* UNIVERSALITY: All gates from NAND                                          *)
(******************************************************************************)

Definition not_from_nand (a : FinProb) (b : Budget) : (FinProb * Budget) :=
  gate_nand_b a a b.

Definition and_from_nand (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match gate_nand_b a b b0 with
      | (nand_ab, b1) => gate_nand_b nand_ab nand_ab b1
      end
  end.

Definition or_from_nand (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match gate_nand_b a a b0 with
      | (not_a, b1) =>
          match gate_nand_b b b b1 with
          | (not_b, b2) => gate_nand_b not_a not_b b2
          end
      end
  end.

Definition xor_from_nand (a b : FinProb) (budget : Budget) : (FinProb * Budget) :=
  match budget with
  | fz => (a, fz)
  | fs b0 =>
      match gate_nand_b a b b0 with
      | (nand_ab, b1) =>
          match gate_nand_b a nand_ab b1 with
          | (lhs, b2) =>
              match gate_nand_b b nand_ab b2 with
              | (rhs, b3) => gate_nand_b lhs rhs b3
              end
          end
      end
  end.

(******************************************************************************)
(* THEOREMS - only what we can prove                                          *)
(******************************************************************************)

(* Exhaustion returns first input unchanged *)
Theorem exhaustion_safe_xor : forall a b,
  fst (gate_xor_b a b fz) = a.
Proof.
  intros. unfold gate_xor_b. reflexivity.
Qed.

Theorem exhaustion_safe_and : forall a b,
  fst (gate_and_b a b fz) = a.
Proof.
  intros. unfold gate_and_b, mul_prob_b. reflexivity.
Qed.

Theorem exhaustion_safe_or : forall a b,
  fst (gate_or_b a b fz) = a.
Proof.
  intros. unfold gate_or_b. reflexivity.
Qed.

Theorem exhaustion_safe_nand : forall a b,
  fst (gate_nand_b a b fz) = a.
Proof.
  intros. unfold gate_nand_b. reflexivity.
Qed.

Theorem exhaustion_safe_nor : forall a b,
  fst (gate_nor_b a b fz) = a.
Proof.
  intros. unfold gate_nor_b. reflexivity.
Qed.

(* le_fin is reflexive *)
Theorem le_fin_refl : forall n, le_fin n n = true.
Proof.
  induction n; simpl; auto.
Qed.

(* fz is minimum *)
Theorem le_fin_fz : forall n, le_fin fz n = true.
Proof.
  destruct n; reflexivity.
Qed.

(* Subtraction with zero is identity *)
Theorem sub_fin_zero : forall n b, fst (sub_fin n fz b) = n.
Proof.
  intros. destruct n; destruct b; reflexivity.
Qed.

(* Zero minus anything is zero *)
Theorem zero_sub_fin : forall m b, fst (sub_fin fz m b) = fz.
Proof.
  intros. destruct m; destruct b; reflexivity.
Qed.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition mul_prob := mul_prob_b.
Definition complement := complement_b.
Definition gate_and := gate_and_b.
Definition gate_or := gate_or_b.
Definition gate_nand := gate_nand_b.
Definition gate_nor := gate_nor_b.
Definition gate_xor := gate_xor_b.
Definition gate_xnor := gate_xnor_b.
Definition gate_not := gate_not_b.

End Void_Gates.