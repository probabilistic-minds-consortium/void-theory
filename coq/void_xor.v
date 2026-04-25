(******************************************************************************)
(* void_xor.v — XOR AS EXISTENCE PROOF                                        *)
(*                                                                            *)
(* Not a benchmark.  A theorem.                                               *)
(* "There exist weights such that a void-network with finite budget           *)
(*  correctly classifies all four XOR inputs."                                *)
(* Classical nets prove this statistically.  We prove it with Qed.            *)
(*                                                                            *)
(* KEY DESIGN: dual-channel encoding.  Input (x,y) becomes [x; ¬x; y; ¬y].    *)
(* Negation is an explicit input, not an arithmetic trick.                    *)
(* This keeps partial_weighted_sum monotonic — no inhibition needed.          *)
(*                                                                            *)
(* ARCHITECTURE: two hidden neurons, one output.                              *)
(*   h1 = x ∧ ¬y    (weights pick input positions 0 and 3; threshold 3/4)    *)
(*   h2 = ¬x ∧ y    (weights pick input positions 1 and 2; threshold 3/4)    *)
(*   out = h1 ∨ h2  (weights pick both hidden; threshold 1/2)                 *)
(*                                                                            *)
(* Why 3/4 at the hidden layer?  prob_le_b3 fires on threshold ≤ input.       *)
(* With threshold 1/2, a single matching weight (1/2) ties the threshold      *)
(* (1/2 ≤ 1/2 = BTrue) — AND degrades to OR.  With 3/4, only both matches    *)
(* summing to 1 pass (3/4 ≤ 1 = BTrue; 3/4 ≤ 1/2 = BFalse).                   *)
(*                                                                            *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal,                 *)
(*             void_geometry, void_learning_cell, void_network                *)
(* ZERO Admitted.  ZERO new Axioms.                                           *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_geometry.
Require Import void_learning_cell.
Require Import void_network.

Import Void_Probability_Minimal.

(******************************************************************************)
(* PART 1: MULTI-LAYER PROPAGATION                                            *)
(*                                                                            *)
(* Fold a signal through a list of layers.  Each layer consumes its own       *)
(* budget from its cells; we thread updated layers out.                       *)
(******************************************************************************)

Fixpoint propagate_network (layers : list Layer) (input : Signal)
  : (Signal * list Layer) :=
  match layers with
  | [] => (input, [])
  | l :: rest =>
      match propagate_layer l input with
      | (output, l') =>
          match propagate_network rest output with
          | (final, rest') => (final, l' :: rest')
          end
      end
  end.

(******************************************************************************)
(* PART 2: DUAL-CHANNEL ENCODING                                              *)
(*                                                                            *)
(* Every Bool3 value gets two channels: the value and its negation.           *)
(* BTrue    becomes [BTrue;  BFalse]                                          *)
(* BFalse   becomes [BFalse; BTrue]                                           *)
(* BUnknown becomes [BUnknown; BUnknown]                                      *)
(*                                                                            *)
(* This lets a monotone (non-negative-weight) network compute non-monotone    *)
(* functions like XOR without inhibition: "¬x" is just another input.         *)
(******************************************************************************)

Definition encode_bool3 (x : Bool3) : Signal :=
  match x with
  | BTrue    => [BTrue;    BFalse]
  | BFalse   => [BFalse;   BTrue]
  | BUnknown => [BUnknown; BUnknown]
  end.

Definition encode_xor_input (x y : Bool3) : Signal :=
  encode_bool3 x ++ encode_bool3 y.
  (* Result layout: [x; ¬x; y; ¬y] — four channels. *)

(******************************************************************************)
(* PART 3: CONCRETE ARCHITECTURE                                              *)
(******************************************************************************)

(* Three-quarters as FinProb: 3/4 *)
Definition three_quarters : FinProb :=
  (fs (fs (fs fz)), fs (fs (fs (fs fz)))).

(* Zero-valued weight — contributes nothing when its channel fires.
   Not a valid_prob (num = fz), but weights don't require valid_prob;
   only thresholds do. *)
Definition zero_weight : FinProb := (fz, fs fz).

(* Both non-trivial thresholds satisfy valid_prob — needed for the record. *)
Lemma valid_three_quarters : valid_prob three_quarters.
Proof. unfold valid_prob, three_quarters. simpl. apply leF_refl. Qed.

(* valid_half is already proven in void_learning_cell.v;
   we re-export its conclusion for convenience. *)
Lemma valid_half_reexport : valid_prob half.
Proof. exact valid_half. Qed.

(* Big budget: fs iterated 30 times from fz.  Plenty for vm_compute to
   finish every comparison in the network.  Defined via a helper to avoid
   counting parentheses. *)
Fixpoint fs_iter (n : nat) (x : Fin) : Fin :=
  match n with
  | O => x
  | S n' => fs (fs_iter n' x)
  end.

Definition big_budget : Budget := fs_iter 500 fz.

Definition make_cell (thr : FinProb) : LearningCell :=
  mkCell thr big_budget fz.

(* Hidden neuron 1: detects x ∧ ¬y.
   Weights pick input positions 0 (= x) and 3 (= ¬y).
   Threshold 3/4 requires BOTH matches to fire. *)
Definition h1_cell : WeightedCell :=
  mkWeighted (make_cell three_quarters)
             [half; zero_weight; zero_weight; half].

(* Hidden neuron 2: detects ¬x ∧ y.
   Weights pick input positions 1 (= ¬x) and 2 (= y).
   Threshold 3/4, same as h1. *)
Definition h2_cell : WeightedCell :=
  mkWeighted (make_cell three_quarters)
             [zero_weight; half; half; zero_weight].

(* Output neuron: detects h1 ∨ h2.
   Two inputs (one per hidden neuron).  Threshold 1/2 fires on one match.
   The hidden neurons are mutually exclusive in valid XOR cases, so OR
   here correctly computes XOR of the original two Bool3 inputs. *)
Definition out_cell : WeightedCell :=
  mkWeighted (make_cell half) [half; half].

Definition hidden_layer : Layer := [h1_cell; h2_cell].
Definition output_layer : Layer := [out_cell].

Definition xor_net : list Layer := [hidden_layer; output_layer].

(******************************************************************************)
(* PART 4: FOUR CORRECTNESS LEMMAS — ONE PER XOR INPUT                        *)
(*                                                                            *)
(* Each is proved by vm_compute + reflexivity.  Everything is concrete:       *)
(* no free variables, no symbolic reasoning — just evaluate the network       *)
(* on the encoded input and observe the output matches the XOR truth table.  *)
(******************************************************************************)

Lemma xor_FF :
  fst (propagate_network xor_net (encode_xor_input BFalse BFalse)) = [BFalse].
Proof. vm_compute. reflexivity. Qed.

Lemma xor_FT :
  fst (propagate_network xor_net (encode_xor_input BFalse BTrue)) = [BTrue].
Proof. vm_compute. reflexivity. Qed.

Lemma xor_TF :
  fst (propagate_network xor_net (encode_xor_input BTrue BFalse)) = [BTrue].
Proof. vm_compute. reflexivity. Qed.

Lemma xor_TT :
  fst (propagate_network xor_net (encode_xor_input BTrue BTrue)) = [BFalse].
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* PART 5: HONESTY UNDER COMPLETE IGNORANCE                                   *)
(*                                                                            *)
(* When BOTH Bool3 inputs are BUnknown, every channel of the encoded          *)
(* signal is BUnknown, so all_unknown holds at every cell — fire_weighted     *)
(* shortcuts to BUnknown.  The network honestly says "I don't know".          *)
(******************************************************************************)

Lemma xor_both_unknown_honest :
  fst (propagate_network xor_net
        (encode_xor_input BUnknown BUnknown)) = [BUnknown].
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* KNOWN LIMITATION                                                           *)
(*                                                                            *)
(* partial_weighted_sum in void_network.v treats BUnknown identically to      *)
(* BFalse — it skips the weight silently.  This means mixed inputs (some      *)
(* known, some BUnknown) lose uncertainty: the network answers confidently    *)
(* based on partial information.                                              *)
(*                                                                            *)
(* Full honesty requires: BUnknown on a non-zero weight should poison the     *)
(* weighted sum → BUnknown output.  This is a future task                     *)
(* (void_network_strict.v) and does not affect the XOR existence proof,      *)
(* which only claims correctness on fully-known Bool3 inputs and fully-       *)
(* unknown Bool3 inputs.                                                      *)
(******************************************************************************)

(******************************************************************************)
(* STATUS                                                                     *)
(*                                                                            *)
(* FULLY PROVEN (vm_compute; reflexivity — zero Admits, zero new Axioms):     *)
(*   xor_FF, xor_FT, xor_TF, xor_TT     — XOR truth table, four Qed's        *)
(*   xor_both_unknown_honest            — honesty under complete ignorance   *)
(*   valid_three_quarters               — threshold validity for hidden      *)
(*   valid_half_reexport                — threshold validity for output      *)
(*                                                                            *)
(* This is the first void-network with machine-verified correctness.          *)
(* Classical neural nets prove XOR statistically after training.              *)
(* Here weights and thresholds are constructed by hand and the classification *)
(* is a theorem, closed under the pre-existing void-theory axioms.            *)
(******************************************************************************)
