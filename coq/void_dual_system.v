(******************************************************************************)
(* void_dual_system.v - THE COGNITIVE ROUTER                                 *)
(* System 1 (fast/habit) vs System 2 (slow/deliberate)                       *)
(*                                                                            *)
(* Kahneman in finite mathematics: thinking costs, habits are cheap.         *)
(* When orbits match, ride them. When they don't, pay for interference.      *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_phase_orbits.
Require Import void_interference_routing.
Require Import void_metaprobability.

Module Void_Dual_System.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Phase_Orbits.
Import Void_Interference_Routing.
Import Void_Metaprobability.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(*                                                                            *)
(* Daniel Kahneman identified two modes of thought:                          *)
(* - System 1: Fast, automatic, effortless, associative                      *)
(* - System 2: Slow, deliberate, effortful, rule-based                       *)
(*                                                                            *)
(* In VOID mathematics, this maps to:                                         *)
(* - System 1 = Phase Orbits: Patterns follow pre-established cycles.        *)
(*   Cheap (one tick to advance), deterministic, but inflexible.            *)
(* - System 2 = Interference Routing: Patterns navigate wave fields.         *)
(*   Expensive (many ticks), adaptive, but thermodynamically costly.         *)
(*                                                                            *)
(* The router decides: Can I use a cached orbit, or must I think deeply?     *)
(* Budget pressure forces reliance on System 1. Novelty demands System 2.    *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* SECTION 1: COGNITIVE STATE                                                *)
(******************************************************************************)

Record CognitiveState := {
  active_orbits : list PhaseOrbit;
  interference_field : InterferenceField;
  confidence_threshold : FinProb;
  switching_cost : Fin
}.

Definition default_confidence_threshold : FinProb := 
  (fs (fs fz), fs (fs (fs fz))).  (* 2/3 *)

Definition default_switching_cost : Fin := 
  fs (fs (fs fz)).  (* 3 ticks *)

Definition init_cognitive_state (field_budget : Budget) : CognitiveState :=
  {| active_orbits := [];
     interference_field := {| field_patterns := [];
                              field_budget := field_budget;
                              cached_maxima := [] |};
     confidence_threshold := default_confidence_threshold;
     switching_cost := default_switching_cost |}.

(******************************************************************************)
(* SECTION 2: ORBIT PREDICTION ERROR                                         *)
(******************************************************************************)

Definition orbit_predicted_location (orbit : PhaseOrbit) : Fin :=
  read_orbit_position (orbit_points orbit) (phase orbit).

Definition prediction_error_b (actual_loc : Fin) (orbit : PhaseOrbit) (b : Budget)
  : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      let predicted := orbit_predicted_location orbit in
      dist_fin_b actual_loc predicted b'
  end.

Definition error_acceptable_b (error : Fin) (threshold : FinProb) (b : Budget)
  : (bool * Budget) :=
  match b with
  | fz => (false, fz)
  | fs b' =>
      let tolerance := fst threshold in
      le_fin_b error tolerance b'
  end.

(******************************************************************************)
(* SECTION 3: FIND MATCHING ORBIT (System 1 lookup)                          *)
(******************************************************************************)

Fixpoint find_matching_orbit_helper (p : Pattern) (orbits : list PhaseOrbit)
                                     (best : option PhaseOrbit) (best_error : Fin)
                                     (fuel : Fin) (b : Budget) (acc_spur : Spuren)
  : (option PhaseOrbit * Fin * Budget * Spuren) :=
  match fuel with
  | fz => (best, best_error, b, acc_spur)
  | fs fuel' =>
      match orbits with
      | [] => (best, best_error, b, acc_spur)
      | orbit :: rest =>
          match b with
          | fz => (best, best_error, fz, acc_spur)
          | fs b' =>
              match prediction_error_b (location p) orbit b' with
              | (error, b1) =>
                  match le_fin_b error best_error b1 with
                  | (true, b2) =>
                      find_matching_orbit_helper p rest (Some orbit) error 
                                                  fuel' b2 (add_spur acc_spur operation_cost)
                  | (false, b2) =>
                      find_matching_orbit_helper p rest best best_error 
                                                  fuel' b2 (add_spur acc_spur operation_cost)
                  end
              end
          end
      end
  end.

Definition find_matching_orbit (p : Pattern) (orbits : list PhaseOrbit) 
                               (fuel : Fin) (b : Budget)
  : (option PhaseOrbit * Fin * Budget * Spuren) :=
  let max_error := fuel in
  find_matching_orbit_helper p orbits None max_error fuel b fz.

(******************************************************************************)
(* SECTION 4: SYSTEM 1 - ORBITAL ADVANCE                                     *)
(******************************************************************************)

Definition system1_advance_b (p : Pattern) (orbit : PhaseOrbit) (b : Budget)
  : (Pattern * PhaseOrbit * Budget * Spuren) :=
  match b with
  | fz => (p, orbit, fz, fz)
  | fs b' =>
      match write_advance_phase orbit b' with
      | (new_orbit, b1, sp) =>
          let new_location := read_orbit_position (orbit_points new_orbit) (phase new_orbit) in
          let new_pattern := {| location := new_location; 
                                strength := strength p |} in
          (new_pattern, new_orbit, b1, sp)
      end
  end.

(******************************************************************************)
(* SECTION 5: SYSTEM 2 - INTERFERENCE NAVIGATION                             *)
(******************************************************************************)

Fixpoint sub_fin_saturate (a b : Fin) : Fin :=
  match a, b with
  | fz, _ => fz
  | _, fz => a
  | fs a', fs b' => sub_fin_saturate a' b'
  end.

Definition system2_navigate_b (p : Pattern) (field : InterferenceField) (b : Budget)
  : (Pattern * InterferenceField * Budget * Spuren) :=
  match b with
  | fz => (p, field, fz, fz)
  | fs b' =>
      let surfer := {| surfer_pattern := p;
                       surf_budget := b';
                       momentum := fz |} in
      let result_surfer := surf_interference_b surfer field in
      let new_pattern := surfer_pattern result_surfer in
      let remaining_budget := surf_budget result_surfer in
      let sp := sub_fin_saturate b' remaining_budget in
      (new_pattern, field, remaining_budget, sp)
  end.

(******************************************************************************)
(* SECTION 6: BUDGET SPENDING                                                *)
(******************************************************************************)

Fixpoint spend_budget (cost : Fin) (b : Budget) : (Fin * Budget) :=
  match cost with
  | fz => (fz, b)
  | fs cost' =>
      match b with
      | fz => (fz, fz)
      | fs b' =>
          match spend_budget cost' b' with
          | (spent, remaining) => (fs spent, remaining)
          end
      end
  end.

(* Check if we could afford the full cost - uses fin_eq_b from void_finite_minimal *)
Definition could_afford (spent cost : Fin) (b : Budget) : (bool * Budget) :=
  fin_eq_b spent cost b.

(******************************************************************************)
(* SECTION 7: THE COGNITIVE ROUTER                                           *)
(******************************************************************************)

Definition replace_first_orbit (orbits : list PhaseOrbit) (new_orbit : PhaseOrbit)
  : list PhaseOrbit :=
  match orbits with
  | [] => [new_orbit]
  | _ :: rest => new_orbit :: rest
  end.

Definition try_system2 (p : Pattern) (state : CognitiveState) 
                       (b : Budget) (prior_spur : Spuren)
  : (Pattern * CognitiveState * Budget * Spuren) :=
  match b with
  | fz => (p, state, fz, prior_spur)
  | fs b' =>
      match spend_budget (switching_cost state) (fs b') with
      | (spent, remaining) =>
          (* Check if we paid full cost using fin_eq_b *)
          match could_afford spent (switching_cost state) remaining with
          | (false, b1) =>
              (* Could not afford switching cost - freeze *)
              (p, state, b1, prior_spur)
          | (true, b1) =>
              match b1 with
              | fz => (p, state, fz, prior_spur)
              | fs r' =>
                  match system2_navigate_b p (interference_field state) b1 with
                  | (new_pattern, new_field, b2, nav_spur) =>
                      let new_state := {| active_orbits := active_orbits state;
                                          interference_field := new_field;
                                          confidence_threshold := confidence_threshold state;
                                          switching_cost := switching_cost state |} in
                      (new_pattern, new_state, b2, add_spur prior_spur nav_spur)
                  end
              end
          end
      end
  end.

Definition cognitive_router (p : Pattern) (state : CognitiveState) 
                            (fuel : Fin) (b : Budget)
  : (Pattern * CognitiveState * Budget * Spuren) :=
  match b with
  | fz => (p, state, fz, fz)
  | fs b' =>
      match find_matching_orbit p (active_orbits state) fuel b' with
      | (None, _, b1, search_spur) =>
          try_system2 p state b1 search_spur
          
      | (Some orbit, error, b1, search_spur) =>
          match error_acceptable_b error (confidence_threshold state) b1 with
          | (true, b2) =>
              match system1_advance_b p orbit b2 with
              | (new_pattern, new_orbit, b3, advance_spur) =>
                  let new_orbits := replace_first_orbit (active_orbits state) new_orbit in
                  let new_state := {| active_orbits := new_orbits;
                                      interference_field := interference_field state;
                                      confidence_threshold := confidence_threshold state;
                                      switching_cost := switching_cost state |} in
                  (new_pattern, new_state, b3, add_spur search_spur advance_spur)
              end
              
          | (false, b2) =>
              try_system2 p state b2 search_spur
          end
      end
  end.

(******************************************************************************)
(* SECTION 8: ORBIT LEARNING                                                 *)
(******************************************************************************)

Fixpoint list_length_fin {A : Type} (l : list A) : Fin :=
  match l with
  | [] => fz
  | _ :: rest => fs (list_length_fin rest)
  end.

Definition learn_orbit_b (trajectory : list Fin) (state : CognitiveState) (b : Budget)
  : (CognitiveState * Budget * Spuren) :=
  match b with
  | fz => (state, fz, fz)
  | fs b' =>
      match trajectory with
      | [] => (state, b', fz)
      | _ =>
          let new_orbit := {| orbit_points := trajectory;
                              period := list_length_fin trajectory;
                              phase := fz;
                              stability := (fs fz, fs (fs fz));
                              orbit_budget := b' |} in
          let new_state := {| active_orbits := new_orbit :: active_orbits state;
                              interference_field := interference_field state;
                              confidence_threshold := confidence_threshold state;
                              switching_cost := switching_cost state |} in
          (new_state, b', operation_cost)
      end
  end.

(******************************************************************************)
(* SECTION 9: CONFIDENCE ADJUSTMENT                                          *)
(******************************************************************************)

Definition adjust_confidence_success_b (state : CognitiveState) (b : Budget)
  : (CognitiveState * Budget) :=
  match b with
  | fz => (state, fz)
  | fs b' =>
      let (num, denom) := confidence_threshold state in
      match safe_succ_b num b' with
      | (new_num, b1) =>
          let new_threshold := (new_num, denom) in
          ({| active_orbits := active_orbits state;
              interference_field := interference_field state;
              confidence_threshold := new_threshold;
              switching_cost := switching_cost state |}, b1)
      end
  end.

Definition adjust_confidence_failure_b (state : CognitiveState) (b : Budget)
  : (CognitiveState * Budget) :=
  match b with
  | fz => (state, fz)
  | fs b' =>
      let (num, denom) := confidence_threshold state in
      match num with
      | fz => (state, b')
      | fs num' =>
          let new_threshold := (num', denom) in
          ({| active_orbits := active_orbits state;
              interference_field := interference_field state;
              confidence_threshold := new_threshold;
              switching_cost := switching_cost state |}, b')
      end
  end.

(******************************************************************************)
(* SECTION 10: BATCH ROUTING                                                 *)
(******************************************************************************)

Fixpoint route_batch_b (patterns : list Pattern) (state : CognitiveState)
                        (fuel : Fin) (b : Budget) (acc_spur : Spuren)
  : (list Pattern * CognitiveState * Budget * Spuren) :=
  match fuel with
  | fz => ([], state, b, acc_spur)
  | fs fuel' =>
      match patterns with
      | [] => ([], state, b, acc_spur)
      | p :: rest =>
          match b with
          | fz => ([], state, fz, acc_spur)
          | fs b' =>
              match cognitive_router p state fuel' b' with
              | (routed_p, new_state, b1, sp) =>
                  match route_batch_b rest new_state fuel' b1 (add_spur acc_spur sp) with
                  | (routed_rest, final_state, b2, total_spur) =>
                      (routed_p :: routed_rest, final_state, b2, total_spur)
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition CognitiveState_ext := CognitiveState.
Definition cognitive_router_ext := cognitive_router.
Definition find_matching_orbit_ext := find_matching_orbit.
Definition learn_orbit_b_ext := learn_orbit_b.
Definition route_batch_b_ext := route_batch_b.
Definition init_cognitive_state_ext := init_cognitive_state.

(******************************************************************************)
(* PHILOSOPHICAL CODA                                                         *)
(*                                                                            *)
(* This is Kahneman's dual-process theory made thermodynamically honest.     *)
(*                                                                            *)
(* SYSTEM 1 (Orbits):                                                         *)
(* - Cached solutions from past experience                                   *)
(* - One tick to advance: nearly free                                        *)
(* - Deterministic: same orbit, same trajectory                              *)
(* - Fails on novelty: orbit mismatch triggers System 2                      *)
(*                                                                            *)
(* SYSTEM 2 (Interference):                                                  *)
(* - Active problem-solving through pattern navigation                       *)
(* - Many ticks to complete: thermodynamically expensive                     *)
(* - Adaptive: finds new solutions in interference field                     *)
(* - Succeeds on novelty: but costs budget and generates Spuren                *)
(*                                                                            *)
(* THE SWITCH:                                                                *)
(* - Switching itself costs: engaging deliberation is not free              *)
(* - When budget is low, System 1 is forced even if wrong                   *)
(* - Under resource pressure, we rely on habit even when inappropriate       *)
(*                                                                            *)
(* LEARNING:                                                                  *)
(* - Successful System 2 solutions can become System 1 orbits               *)
(* - Expertise = converting expensive inference to cheap habit               *)
(* - The goal is to make System 2 unnecessary through orbital caching        *)
(*                                                                            *)
(* This explains why tired people make worse decisions (forced System 1),    *)
(* why experts seem effortless (everything is cached), and why learning      *)
(* is hard (System 2 is expensive). The budget makes it real.               *)
(******************************************************************************)

End Void_Dual_System.