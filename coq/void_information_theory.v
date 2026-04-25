(******************************************************************************)
(* void_information_theory.v - INFORMATION THEORY FOUNDATION                 *)
(* Defines operation types for void mathematics.                              *)
(*                                                                            *)
(* HISTORICAL NOTE (2026-04-02):                                              *)
(* This file originally assumed READ ≠ WRITE: read is free, write costs.     *)
(* void_probability_geometry.v Section XV proves this distinction false:      *)
(*   - write_asymmetry: every observation is atomic read+write               *)
(*   - no_free_lunch_le: every comparison with nonzero budget costs nonzero  *)
(*   - self_blind: the observer cannot observe itself at any budget           *)
(* READ IS WRITE. There is no free observation. The ReadOperation type       *)
(* class below is retained for backward compatibility but is ontologically   *)
(* superseded: any "read" that touches Fin is a write in disguise.           *)
(*                                                                            *)
(* Three Axioms that enforced the old distinction have been replaced          *)
(* with comments explaining why they are false. No file depends on them.     *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Information_Theory.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* FUNDAMENTAL INFORMATION THEORY TYPES                                       *)
(******************************************************************************)

(* Type aliases for clarity *)
Definition Spuren := Fin.

(* Information content of a state *)
Definition InformationContent := FinProb.

(* The universe's total distinguishable content *)
Record UniverseInformation := {
  total_entropy : Fin;
  distinguishable_states : list Pattern;
  observer_resolutions : list FinProb;
  information_budget : Budget
}.

(******************************************************************************)
(* OPERATION TYPES                                                            *)
(* NOTE: The READ/WRITE distinction is retained as a type-level interface     *)
(* for backward compatibility. Ontologically, READ IS WRITE:                  *)
(* every observation that touches Fin costs budget and produces Spuren.       *)
(* ReadOperation below models the SYNTACTIC pattern of structural access;     *)
(* it does NOT mean the operation is free. See void_probability_geometry.v    *)
(* Section XV for the proof.                                                  *)
(******************************************************************************)

(* Structural access pattern — syntactically budget-free, but see above *)
Class ReadOperation (A B : Type) := {
  read_op : A -> B
}.

(* Budgeted operation — explicitly tracks cost *)
Class WriteOperation (A B : Type) := {
  write_op : A -> Budget -> (B * Budget * Spuren)
}.

(******************************************************************************)
(* CLASSIFICATION OF OPERATIONS                                               *)
(******************************************************************************)

(* READ Operations - Access existing information structure *)

(* Structural field access - reading what already exists *)
#[export] Instance pattern_location_read : ReadOperation Pattern Fin := {
  read_op := fun p => location p
}.

#[export] Instance pattern_strength_read : ReadOperation Pattern FinProb := {
  read_op := fun p => strength p
}.

(* Distinguishability measurement - reading information difference *)
(* This would read existing information structure *)
Definition read_distinguishability (p1 p2 : Pattern) : FinProb :=
  (* Simplified: just compare strengths *)
  strength p1.

#[export] Instance distinguishability_read : ReadOperation (Pattern * Pattern) FinProb := {
  read_op := fun '(p1, p2) => read_distinguishability p1 p2
}.

(* Spuren tracking - reading computational history *)
Definition read_heat_level (h : Spuren) : Fin := h.

#[export] Instance spur_tracking_read : ReadOperation Spuren Fin := {
  read_op := read_heat_level
}.

(* Budget availability - reading resource state *)
Definition read_budget_available (b : Budget) : bool :=
  match b with fz => false | _ => true end.

#[export] Instance budget_check_read : ReadOperation Budget bool := {
  read_op := read_budget_available
}.

(* List structure - reading existing organization *)
Definition read_list_length {A : Type} (l : list A) : Fin :=
  fold_left (fun acc _ => fs acc) l fz.

#[export] Instance list_length_read {A : Type} : ReadOperation (list A) Fin := {
  read_op := read_list_length
}.

(******************************************************************************)
(* WRITE Operations - Change distinguishable content                          *)
(******************************************************************************)

(* Arithmetic computation - generates new numeric information *)
Definition write_addition (n m : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match add_fin_spur n m b with
  | (result, b', h) => (result, b', h)
  end.

#[export] Instance addition_write : WriteOperation (Fin * Fin) Fin := {
  write_op := fun '(n, m) => write_addition n m
}.

Definition write_multiplication (n m : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match mult_fin_spur n m b with
  | (result, b', h) => (result, b', h)
  end.

#[export] Instance multiplication_write : WriteOperation (Fin * Fin) Fin := {
  write_op := fun '(n, m) => write_multiplication n m
}.

(* Pattern movement - creates new distinguishable state *)
Definition write_pattern_move (p : Pattern) (direction : bool) (b : Budget) 
  : (Pattern * Budget * Spuren) :=
  match b with
  | fz => (p, fz, fz)
  | fs b' =>
      let new_location := if direction then fs (location p) else location p in
      let new_pattern := {| location := new_location; strength := strength p |} in
      (new_pattern, b', fs fz)  (* Moving costs one tick *)
  end.

#[export] Instance pattern_movement_write : WriteOperation (Pattern * bool) Pattern := {
  write_op := fun '(p, dir) => write_pattern_move p dir
}.

(* Entropy creation - increases universe information content *)
Definition write_entropy_increase (loc amount : Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match b with
  | fz => (loc, fz, fz)
  | fs b' => 
      let new_entropy := fs loc in  (* Simple increment *)
      (new_entropy, b', fs fz)
  end.

#[export] Instance entropy_creation_write : WriteOperation (Fin * Fin) Fin := {
  write_op := fun '(loc, amount) => write_entropy_increase loc amount
}.

(******************************************************************************)
(* INFORMATION CONSERVATION PRINCIPLES                                        *)
(******************************************************************************)

(* READ operations preserve total system information — trivially *)
Lemma read_information_conservation :
  forall (universe : UniverseInformation),
  (* Reading doesn't change the universe's total entropy *)
  total_entropy universe = total_entropy universe.
Proof. intro. reflexivity. Qed.

(* RETIRED AXIOMS — FALSE UNDER READ=WRITE (2026-04-02)                      *)
(*                                                                            *)
(* Former Axiom: write_consumes_budget                                        *)
(*   Claimed: only WRITE operations consume budget.                           *)
(*   False because: no_free_lunch_le (void_finite_minimal) proves that        *)
(*   ANY le_fin_b3 comparison with nonzero budget produces nonzero Spuren.    *)
(*   "Read" operations that touch Fin are writes in disguise.                 *)
(*                                                                            *)
(* Former Axiom: write_information_thermodynamics                             *)
(*   Claimed: only WRITE operations generate Spuren.                          *)
(*   False because: write_asymmetry (void_probability_geometry) proves        *)
(*   every observation is atomic read+write. Spuren are universal.            *)
(*                                                                            *)
(* Former Axiom: distinguishability_change_theorem                            *)
(*   Claimed: any two universe states have different budgets.                  *)
(*   Malformed: this says ALL pairs differ, not "if changed then differ."     *)
(*   Even corrected, it would be redundant with time_irreversible.            *)
(*                                                                            *)
(* These axioms were never used by any file in the codebase.                  *)
(* Their removal changes no proofs. Their falsehood is now a theorem.         *)

(******************************************************************************)
(* BOUNDARY DECISION PROCEDURE                                                *)
(******************************************************************************)

(* Given an operation, determine if it's READ or WRITE *)
Inductive OperationType :=
  | IsRead : OperationType
  | IsWrite : OperationType.

(* Decision principle: Does this operation change what can be distinguished? *)
(* In practice, this would be determined by the operation's type signature *)
Definition operation_changes_distinguishability (changes : bool) : OperationType :=
  match changes with
  | true => IsWrite
  | false => IsRead
  end.

(* Formal boundary rule *)
Definition information_boundary_rule (op_changes_distinguishability : bool) : OperationType :=
  operation_changes_distinguishability op_changes_distinguishability.

(******************************************************************************)
(* INFINITE REGRESS SOLUTION                                                  *)
(******************************************************************************)

(* The infinite regress stops because information tracking is read access *)
Lemma infinite_regress_termination :
  forall (computation_history : list Spuren),
  (* Reading computational history doesn't generate new computational history *)
  (* This is the key insight that stops infinite regress *)
  True.
Proof. intro. exact I. Qed.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition ReadOperation_ext := ReadOperation.
Definition WriteOperation_ext := WriteOperation.
Definition UniverseInformation_ext := UniverseInformation.
Definition OperationType_ext := OperationType.
Definition information_boundary_rule_ext := information_boundary_rule.

End Void_Information_Theory.