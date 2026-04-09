(******************************************************************************)
(* void_dual_system.v - THE COGNITIVE ROUTER                                 *)
(* System 1 (fast/heuristic) vs System 2 (slow/precise)                      *)
(*                                                                            *)
(* POST-R/W COLLAPSE: Nothing is cheap. Both systems cost budget.            *)
(* The difference is STRATEGY, not COST:                                     *)
(*   System 1 = accepts BUnknown, acts despite it (collapse3).              *)
(*   System 2 = pays extra budget (fs) to resolve BUnknown.                 *)
(* Kahneman was right about the EXISTENCE of two systems.                    *)
(* He was wrong about the REASON: it is not fast/cheap vs slow/expensive.   *)
(* It is blind-but-acting vs paying-for-sight.                               *)
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
(* PHILOSOPHICAL NOTE — POST-R/W COLLAPSE                                    *)
(*                                                                            *)
(* Daniel Kahneman identified two modes of thought:                          *)
(* - System 1: Fast, automatic, heuristic                                    *)
(* - System 2: Slow, deliberate, precise                                     *)
(*                                                                            *)
(* Kahneman's error: he described System 1 as "cheap" and System 2 as       *)
(* "expensive." After READ IS WRITE, nothing is cheap. Every observation     *)
(* costs budget and produces Spuren. The distinction is not about COST       *)
(* but about STRATEGY:                                                       *)
(*                                                                            *)
(* System 1 = COLLAPSE STRATEGY: Uses cached orbits AND collapse3.          *)
(*   When orbit lookup returns BUnknown (budget insufficient to verify       *)
(*   match quality), System 1 forces a decision: collapse3(BUnknown)=false, *)
(*   treat the best available orbit as good enough. Acts despite blindness.  *)
(*   Cost: same as System 2 for the base operation. Savings: does NOT pay   *)
(*   the extra tick to resolve BUnknown. Risk: wrong orbit, wrong decision. *)
(*                                                                            *)
(* System 2 = RESOLUTION STRATEGY: Pays extra budget (fs) to resolve        *)
(*   BUnknown into BTrue or BFalse before acting. Uses interference field   *)
(*   when no orbit is available. Cost: base + resolution tick.              *)
(*   Safety: knows whether the orbit matches. Risk: budget exhaustion.      *)
(*                                                                            *)
(* The router decides: Do I have budget to RESOLVE, or must I COLLAPSE?     *)
(* Under resource pressure, System 1 is forced — not because it is cheap,  *)
(* but because the organism cannot afford to know whether it is right.       *)
(* This is the thermodynamic tragedy of cognition under scarcity.            *)
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

(* OLD: error_acceptable_b returned bool — collapsing BUnknown silently.    *)
(* NEW: error_acceptable_b3 returns Bool3 — preserving the Real.            *)
(* The ROUTER decides what to do with BUnknown, not the comparison.         *)
Definition error_acceptable_b3 (error : Fin) (threshold : FinProb) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match b with
  | fz => (BUnknown, fz, fz)
  | fs b' =>
      let tolerance := fst threshold in
      le_fin_b3 error tolerance b'
  end.

(* System 1 strategy: collapse BUnknown to false — act despite blindness.  *)
(* This is the mechanism Kahneman misidentified as "fast and cheap."        *)
(* It is not cheap. It is BLIND.                                            *)
Definition error_acceptable_system1 (error : Fin) (threshold : FinProb) (b : Budget)
  : (bool * Budget * Spuren) :=
  match error_acceptable_b3 error threshold b with
  | (r, b', h) => (collapse3 r, b', h)
  end.

(* Backward compatibility — old signature for non-rewritten callers *)
Definition error_acceptable_b (error : Fin) (threshold : FinProb) (b : Budget)
  : (bool * Budget) :=
  match error_acceptable_b3 error threshold b with
  | (r, b', _) => (collapse3 r, b')
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

(* THE COGNITIVE ROUTER — POST-R/W COLLAPSE                                 *)
(*                                                                            *)
(* The router now makes a THREE-WAY decision based on Bool3:                 *)
(*   BTrue    → orbit matches, advance it (both systems would agree)        *)
(*   BFalse   → orbit does not match, engage System 2 (pay for new route)   *)
(*   BUnknown → CRITICAL FORK: budget insufficient to verify match          *)
(*              System 1: collapse3(BUnknown) = false, but act on orbit     *)
(*              anyway — blind action, the organism's gamble under scarcity  *)
(*              System 2: pay switching_cost to resolve — but can we afford? *)
(*              If switching_cost > remaining budget: FORCED System 1.       *)
(*              The tragedy: when you most need to know, you least can.      *)
Definition cognitive_router (p : Pattern) (state : CognitiveState)
                            (fuel : Fin) (b : Budget)
  : (Pattern * CognitiveState * Budget * Spuren) :=
  match b with
  | fz => (p, state, fz, fz)
  | fs b' =>
      match find_matching_orbit p (active_orbits state) fuel b' with
      | (None, _, b1, search_spur) =>
          (* No orbit found at all — System 2 is the only option *)
          try_system2 p state b1 search_spur

      | (Some orbit, error, b1, search_spur) =>
          (* Found an orbit. But can we VERIFY it matches? *)
          match error_acceptable_b3 error (confidence_threshold state) b1 with
          | (BTrue, b2, verify_spur) =>
              (* VERIFIED MATCH — both systems agree: advance the orbit *)
              match system1_advance_b p orbit b2 with
              | (new_pattern, new_orbit, b3, advance_spur) =>
                  let new_orbits := replace_first_orbit (active_orbits state) new_orbit in
                  let new_state := {| active_orbits := new_orbits;
                                      interference_field := interference_field state;
                                      confidence_threshold := confidence_threshold state;
                                      switching_cost := switching_cost state |} in
                  (new_pattern, new_state, b3,
                   add_spur search_spur (add_spur verify_spur advance_spur))
              end

          | (BFalse, b2, verify_spur) =>
              (* VERIFIED MISMATCH — orbit is wrong, pay for System 2 *)
              try_system2 p state b2 (add_spur search_spur verify_spur)

          | (BUnknown, b2, verify_spur) =>
              (* CRITICAL: Budget insufficient to verify. *)
              (* System 1 COLLAPSE: act on the orbit despite blindness. *)
              (* This is not a choice — it is forced by budget exhaustion. *)
              (* collapse3(BUnknown) = false, but we advance anyway *)
              (* because the alternative (System 2) costs MORE than we have. *)
              match system1_advance_b p orbit b2 with
              | (new_pattern, new_orbit, b3, advance_spur) =>
                  let new_orbits := replace_first_orbit (active_orbits state) new_orbit in
                  let new_state := {| active_orbits := new_orbits;
                                      interference_field := interference_field state;
                                      confidence_threshold := confidence_threshold state;
                                      switching_cost := switching_cost state |} in
                  (new_pattern, new_state, b3,
                   add_spur search_spur (add_spur verify_spur advance_spur))
              end
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
(* PHILOSOPHICAL CODA — POST-R/W COLLAPSE                                    *)
(*                                                                            *)
(* This is Kahneman's dual-process theory after thermodynamic correction.    *)
(*                                                                            *)
(* SYSTEM 1 (Collapse Strategy):                                             *)
(* - Uses cached orbits from past experience                                 *)
(* - When verification returns BUnknown: applies collapse3, acts anyway     *)
(* - Not cheap — BLIND. Same metabolic cost, less information.              *)
(* - Deterministic: same orbit, same trajectory, same blindness.            *)
(*                                                                            *)
(* SYSTEM 2 (Resolution Strategy):                                           *)
(* - Pays extra tick (fs) to resolve BUnknown before acting                 *)
(* - Uses interference field when no cached orbit available                  *)
(* - Not expensive — PRECISE. Extra cost buys sight.                        *)
(* - Adaptive: finds new solutions, but pays for each distinction.          *)
(*                                                                            *)
(* THE SWITCH:                                                                *)
(* - Not a choice between fast and slow, but between blind and seeing       *)
(* - When budget is low, System 1 is forced — organism cannot afford        *)
(*   to know whether its decision is right (void_productive denied)         *)
(* - Under scarcity, we collapse BUnknown to false — we refuse the Real    *)
(*   (Lacan) and force the Symbolic. This is the mechanism of trauma.       *)
(*                                                                            *)
(* LEARNING:                                                                  *)
(* - Successful System 2 resolutions become System 1 orbits                 *)
(* - Expertise = building orbits so good that collapse3 rarely lies         *)
(* - The expert's System 1 is not cheaper; it is LESS WRONG when blind     *)
(*                                                                            *)
(* IMPLICATIONS:                                                              *)
(* - Tired people do not make "faster" decisions — they make BLINDER ones   *)
(* - Experts are not "effortless" — their blindness is better calibrated    *)
(* - Trauma = System 1 hardcoded where System 2 was needed but unaffordable *)
(* - Therapy = restoring the option to pay for resolution (void_productive) *)
(*                                                                            *)
(* The budget does not make System 2 expensive.                              *)
(* It makes System 1 dangerous.                                              *)
(******************************************************************************)

End Void_Dual_System.