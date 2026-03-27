(******************************************************************************)
(* void_probability_operations.v - PROBABILITY ARITHMETIC WRAPPERS           *)
(* Clean interfaces to existing probability operations from foundation        *)
(* NO new operations - only wraps void_probability_minimal.v                 *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Probability_Operations.

Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Arithmetic.Void_Probability_Division.

(******************************************************************************)
(* CORE OPERATIONS - Direct exports from existing modules                    *)
(******************************************************************************)

(* Multiplication for independent co-occurrence - from void_probability_minimal.v *)
Definition prob_mult_b := mult_prob_b.
Definition prob_mult_spur := mult_prob_spur.

(* Addition for combining probabilities - from void_probability_minimal.v *)
Definition prob_add_b := add_prob_b.
Definition prob_add_spur := add_prob_spur.

(* Subtraction with saturation - from void_probability_minimal.v *)
Definition prob_sub_b := sub_prob_b.
Definition prob_sub_spur := sub_prob_spur.

(* Comparison - from void_probability_minimal.v *)
Definition prob_le_b := Void_Probability_Minimal.prob_le_b.
Definition prob_le_b3 := Void_Probability_Minimal.prob_le_b3.
Definition prob_eq_b := Void_Probability_Minimal.prob_eq_b.
Definition prob_eq_b3 := Void_Probability_Minimal.prob_eq_b3.

(* Division - from void_arithmetic.v Void_Probability_Division module *)
Definition prob_div_b := div_prob.
Definition prob_div_spur := div_prob_spur.

(******************************************************************************)
(* COMPLEMENT - Using subtraction from implicit 1                            *)
(******************************************************************************)

(* Compute 1 - p with saturation *)
Definition prob_complement_b (p : FinProb) (b : Budget) : (FinProb * Budget) :=
  let (n, d) := p in
  (* 1 - (n/d) = (d-n)/d *)
  match sub_fin n d b with
  | (diff, b') => ((diff, d), b')
  end.

Definition prob_complement_spur (p : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  let (n, d) := p in
  match sub_fin_spur n d b with
  | (diff, b', h) => ((diff, d), b', h)
  end.

(******************************************************************************)
(* MIN AND MAX - Using comparison                                            *)
(******************************************************************************)

Definition prob_min_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match prob_le_b p1 p2 b with
  | (true, b') => (p1, b')
  | (false, b') => (p2, b')
  end.

Definition prob_max_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match prob_le_b p1 p2 b with
  | (true, b') => (p2, b')
  | (false, b') => (p1, b')
  end.

Definition prob_min_spur (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  match prob_le_b3 p1 p2 b with
  | (BTrue, b', h) => (p1, b', h)
  | (BFalse, b', h) => (p2, b', h)
  | (BUnknown, b', h) => (p1, b', h)  (* Default to first on unknown *)
  end.

Definition prob_max_spur (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  match prob_le_b3 p1 p2 b with
  | (BTrue, b', h) => (p2, b', h)
  | (BFalse, b', h) => (p1, b', h)
  | (BUnknown, b', h) => (p2, b', h)  (* Default to second on unknown *)
  end.

(******************************************************************************)
(* PREDICTION ACCURACY - Ratio of min to max                                 *)
(******************************************************************************)

(* Accuracy = min(predicted, actual) / max(predicted, actual) *)
Definition prediction_accuracy_b (predicted actual : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget) :=
  match b with
  | fz => ((fz, fs fz), fz)
  | fs b' =>
      match prob_min_b predicted actual b' with
      | (min_val, b1) =>
          match prob_max_b predicted actual b1 with
          | (max_val, b2) =>
              prob_div_b min_val max_val rho b2
          end
      end
  end.

Definition prediction_accuracy_spur (predicted actual : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget * Spuren) :=
  match b with
  | fz => ((fz, fs fz), fz, fz)
  | fs b' =>
      match prob_min_spur predicted actual b' with
      | (min_val, b1, h1) =>
          match prob_max_spur predicted actual b1 with
          | (max_val, b2, h2) =>
              match prob_div_spur min_val max_val rho b2 with
              | (result, b3, h3) => 
                  (result, b3, add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

(******************************************************************************)
(* WEIGHTED AVERAGE - For merging traces                                     *)
(******************************************************************************)

(* Weighted average: w*p1 + (1-w)*p2 where w is weight *)
Definition prob_weighted_avg_b (p1 p2 weight : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      (* Compute w*p1 *)
      match prob_mult_b weight p1 b' with
      | (weighted_p1, b1) =>
          (* Compute (1-w) *)
          match prob_complement_b weight b1 with
          | (one_minus_w, b2) =>
              (* Compute (1-w)*p2 *)
              match prob_mult_b one_minus_w p2 b2 with
              | (weighted_p2, b3) =>
                  (* Add the weighted terms *)
                  prob_add_b weighted_p1 weighted_p2 b3
              end
          end
      end
  end.

Definition prob_weighted_avg_spur (p1 p2 weight : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget * Spuren) :=
  match b with
  | fz => (p1, fz, fz)
  | fs b' =>
      match prob_mult_spur weight p1 b' with
      | (weighted_p1, b1, h1) =>
          match prob_complement_spur weight b1 with
          | (one_minus_w, b2, h2) =>
              match prob_mult_spur one_minus_w p2 b2 with
              | (weighted_p2, b3, h3) =>
                  match prob_add_spur weighted_p1 weighted_p2 b3 with
                  | (result, b4, h4) =>
                      (result, b4, 
                       add_spur h1 (add_spur h2 (add_spur h3 h4)))
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* DISTANCE - Complement of accuracy                                         *)
(******************************************************************************)

(* Distance = 1 - accuracy *)
Definition prob_distance_b (p1 p2 : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget) :=
  match b with
  | fz => ((fs fz, fs (fs fz)), fz)  (* Return 1/2 on exhaust *)
  | fs b' =>
      match prediction_accuracy_b p1 p2 rho b' with
      | (accuracy, b1) =>
          prob_complement_b accuracy b1
      end
  end.

Definition prob_distance_spur (p1 p2 : FinProb) (rho : Resolution) (b : Budget)
  : (FinProb * Budget * Spuren) :=
  match b with
  | fz => ((fs fz, fs (fs fz)), fz, fz)
  | fs b' =>
      match prediction_accuracy_spur p1 p2 rho b' with
      | (accuracy, b1, h1) =>
          match prob_complement_spur accuracy b1 with
          | (distance, b2, h2) => (distance, b2, add_spur h1 h2)
          end
      end
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition prob_mult_b_ext := prob_mult_b.
Definition prob_add_b_ext := prob_add_b.
Definition prob_sub_b_ext := prob_sub_b.
Definition prob_div_b_ext := prob_div_b.
Definition prob_complement_b_ext := prob_complement_b.
Definition prob_min_b_ext := prob_min_b.
Definition prob_max_b_ext := prob_max_b.
Definition prediction_accuracy_b_ext := prediction_accuracy_b.
Definition prob_weighted_avg_b_ext := prob_weighted_avg_b.
Definition prob_distance_b_ext := prob_distance_b.

End Void_Probability_Operations.

(******************************************************************************)
(* DESIGN PRINCIPLES                                                          *)
(*                                                                            *)
(* This module provides NO new operations. It only wraps existing proven     *)
(* operations from:                                                           *)
(* - void_probability_minimal.v (mult, add, sub, compare)                    *)
(* - void_arithmetic.v (division with resolution)                            *)
(*                                                                            *)
(* Every operation here composes from already-proven-terminating primitives. *)
(* No new recursion. No new Fixpoints. Just composition.                     *)
(*                                                                            *)
(* Complement uses subtraction: 1 - p = (d-n)/d                             *)
(* Min/max use comparison from prob_le_b                                     *)
(* Accuracy uses min, max, and division                                      *)
(* Weighted average uses multiplication, complement, and addition            *)
(* Distance uses accuracy and complement                                     *)
(*                                                                            *)
(* All operations respect budget conservation through their primitives.      *)
(******************************************************************************)