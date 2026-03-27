(******************************************************************************)
(* void_phase_orbits.v - BUDGET-AWARE ORBITAL DYNAMICS                       *)
(* Patterns follow predetermined orbits, but every step costs                *)
(* CLEANED: All operations cost one tick, no magic numbers                   *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_information_theory.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Phase_Orbits.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Information_Theory.

(******************************************************************************)
(* FUNDAMENTAL CONSTANT - One tick of time                                   *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.  (* The only arbitrary constant *)

(******************************************************************************)
(* CORE TYPES WITH BUDGET AWARENESS                                          *)
(******************************************************************************)

(* Phase orbit - a closed cycle in space *)
Record PhaseOrbit := {
  orbit_points : list Fin;  (* Closed cycle of positions *)
  period : Fin;             (* Time to complete orbit *)
  phase : Fin;              (* Current position in cycle *)
  stability : FinProb;      (* How strongly it holds patterns *)
  orbit_budget : Budget     (* Resources for orbit operations *)
}.

(* Pattern locked in orbit with its own budget *)
Record OrbitalPattern := {
  base_pattern : Pattern;
  current_orbit : PhaseOrbit;
  pattern_budget : Budget   (* Pattern's own resources *)
}.

(* System of multiple orbits *)
Record OrbitalSystem := {
  orbits : list PhaseOrbit;
  patterns : list OrbitalPattern;
  system_budget : Budget
}.

(******************************************************************************)
(* READ OPERATIONS - Access existing orbital structure                        *)
(******************************************************************************)

(* Read current phase - FREE *)
Definition read_phase (orbit : PhaseOrbit) : Fin :=
  phase orbit.

Instance phase_read : ReadOperation PhaseOrbit Fin := {
  read_op := read_phase
}.

(* Read orbit period - FREE *)
Definition read_period (orbit : PhaseOrbit) : Fin :=
  period orbit.

Instance period_read : ReadOperation PhaseOrbit Fin := {
  read_op := read_period
}.

(* Read stability - FREE *)
Definition read_stability (orbit : PhaseOrbit) : FinProb :=
  stability orbit.

Instance stability_read : ReadOperation PhaseOrbit FinProb := {
  read_op := read_stability
}.

(* Check if orbit is stable - FREE *)
Definition read_is_stable (orbit : PhaseOrbit) : bool :=
  match stability orbit with
  | (n, d) => negb (fin_eq n fz)  (* Stable if numerator non-zero *)
  end.

Instance is_stable_read : ReadOperation PhaseOrbit bool := {
  read_op := read_is_stable
}.

(* Get orbit position at phase - FREE *)
Fixpoint read_orbit_position (points : list Fin) (phase : Fin) : Fin :=
  match points, phase with
  | [], _ => fz
  | p :: _, fz => p
  | _ :: rest, fs phase' => read_orbit_position rest phase'
  end.

Instance orbit_position_read : ReadOperation (list Fin * Fin) Fin := {
  read_op := fun '(points, phase) => read_orbit_position points phase
}.

(******************************************************************************)
(* DYNAMIC COST FUNCTIONS - Costs emerge from context                        *)
(******************************************************************************)

(* Orbit step cost depends on stability - READ operation *)
Definition orbit_step_cost_dynamic (orbit : PhaseOrbit) : Fin :=
  (* Always one tick - stability affects success rate, not cost *)
  operation_cost.

Instance orbit_step_cost_read : ReadOperation PhaseOrbit Fin := {
  read_op := orbit_step_cost_dynamic
}.

(* Intersection check cost - READ operation *)
Definition intersection_check_cost_dynamic (system_budget : Budget) : Fin :=
  (* Always one tick - complexity handled by iteration *)
  operation_cost.

Instance intersection_cost_read : ReadOperation Budget Fin := {
  read_op := intersection_check_cost_dynamic
}.

(* Hop cost depends on orbit distance - READ operation *)
Definition orbit_hop_cost_dynamic (from_orbit to_orbit : PhaseOrbit) : Fin :=
  (* Always one tick - distance affects success probability *)
  operation_cost.

Instance hop_cost_read : ReadOperation (PhaseOrbit * PhaseOrbit) Fin := {
  read_op := fun '(from, to) => orbit_hop_cost_dynamic from to
}.

(******************************************************************************)
(* WRITE OPERATIONS - Change orbital state                                   *)
(******************************************************************************)

(* Advance phase - WRITE operation *)
Definition write_advance_phase (orbit : PhaseOrbit) (b : Budget) 
  : (PhaseOrbit * Budget * Spuren) :=
  match b with
  | fz => (orbit, fz, fz)
  | fs b' =>
      (* Increment phase modulo period *)
      let new_phase := 
        match le_fin_b (fs (phase orbit)) (period orbit) b' with
        | (true, b'') => fs (phase orbit)
        | (false, b'') => fz  (* Wrap around *)
        end in
      ({| orbit_points := orbit_points orbit;
          period := period orbit;
          phase := new_phase;
          stability := stability orbit;
          orbit_budget := orbit_budget orbit |}, b', fs fz)
  end.

Instance advance_phase_write : WriteOperation PhaseOrbit PhaseOrbit := {
  write_op := write_advance_phase
}.

(* Move pattern along orbit - WRITE operation *)
Definition write_orbital_step (op : OrbitalPattern) (b : Budget) 
  : (OrbitalPattern * Budget * Spuren) :=
  match b with
  | fz => (op, fz, fz)
  | fs b' =>
      (* Advance orbit phase *)
      match write_advance_phase (current_orbit op) b' with
      | (new_orbit, b'', h) =>
          (* Update pattern location to new orbit position *)
          let new_loc := read_orbit_position (orbit_points new_orbit) 
                                            (phase new_orbit) in
          let new_pattern := {| location := new_loc;
                               strength := strength (base_pattern op) |} in
          ({| base_pattern := new_pattern;
              current_orbit := new_orbit;
              pattern_budget := pattern_budget op |}, b'', h)
      end
  end.

Instance orbital_step_write : WriteOperation OrbitalPattern OrbitalPattern := {
  write_op := write_orbital_step
}.

(* Check orbit intersection - WRITE operation (computes new information) *)
Definition write_check_intersection (o1 o2 : PhaseOrbit) (b : Budget) 
  : (bool * Budget * Spuren) :=
  match b with
  | fz => (false, fz, fz)
  | fs b' =>
      (* Check if current positions match *)
      let pos1 := read_orbit_position (orbit_points o1) (phase o1) in
      let pos2 := read_orbit_position (orbit_points o2) (phase o2) in
      match fin_eq_b pos1 pos2 b' with
      | (equal, b'') => (equal, b'', fs fz)
      end
  end.

Instance intersection_check_write : WriteOperation (PhaseOrbit * PhaseOrbit) bool := {
  write_op := fun '(o1, o2) => write_check_intersection o1 o2
}.

(* Hop between orbits - WRITE operation *)
Definition write_orbit_hop (op : OrbitalPattern) (target : PhaseOrbit) (b : Budget)
  : (OrbitalPattern * Budget * Spuren) :=
  match b with
  | fz => (op, fz, fz)
  | fs b' =>
      (* Check if orbits intersect *)
      match write_check_intersection (current_orbit op) target b' with
      | (true, b'', h1) =>
          (* Can hop *)
          ({| base_pattern := base_pattern op;
              current_orbit := target;
              pattern_budget := pattern_budget op |}, b'', h1)
      | (false, b'', h1) =>
          (* Cannot hop - stay on current orbit *)
          (op, b'', h1)
      end
  end.

Instance orbit_hop_write : WriteOperation (OrbitalPattern * PhaseOrbit) OrbitalPattern := {
  write_op := fun '(op, target) => write_orbit_hop op target
}.

(* Check if can escape orbit - WRITE operation *)
Definition write_escape_check (op : OrbitalPattern) (b : Budget) 
  : (bool * Budget * Spuren) :=
  match b with
  | fz => (false, fz, fz)
  | fs b' =>
      (* Can escape if pattern is strong enough *)
      match le_fin_b (fst (stability (current_orbit op))) 
                     (fst (strength (base_pattern op))) b' with
      | (can_escape, b'') => (can_escape, b'', fs fz)
      end
  end.

Instance escape_check_write : WriteOperation OrbitalPattern bool := {
  write_op := write_escape_check
}.

(* Create simple circular orbit - WRITE operation *)
Definition write_circular_orbit (center : Fin) (radius : Fin) (b : Budget)
  : (PhaseOrbit * Budget * Spuren) :=
  match b with
  | fz => ({| orbit_points := [];
              period := fz;
              phase := fz;
              stability := (fz, fs fz);
              orbit_budget := fz |}, fz, fz)
  | fs b' =>
      (* Generate points around center *)
      let points := [center; fs center; fs (fs center); center] in
      ({| orbit_points := points;
          period := fs (fs (fs (fs fz)));  (* Length of points *)
          phase := fz;
          stability := (fs fz, fs (fs fz));  (* 1/2 stability *)
          orbit_budget := b' |}, b', fs fz)
  end.

Instance circular_orbit_write : WriteOperation (Fin * Fin) PhaseOrbit := {
  write_op := fun '(center, radius) => write_circular_orbit center radius
}.

(* Create figure-8 orbit - WRITE operation *)
Definition write_figure_eight_orbit (b : Budget) : (PhaseOrbit * Budget * Spuren) :=
  match b with
  | fz => ({| orbit_points := [];
              period := fz;
              phase := fz;
              stability := (fz, fs fz);
              orbit_budget := fz |}, fz, fz)
  | fs b' =>
      (* Simple figure-8 pattern *)
      let points := [fz; fs fz; fs (fs fz); fs fz; fz; 
                     fs (fs (fs fz)); fs (fs (fs (fs fz))); fs (fs (fs fz))] in
      ({| orbit_points := points;
          period := fs (fs (fs (fs (fs (fs (fs (fs fz)))))));  (* 8 *)
          phase := fz;
          stability := (fs (fs fz), fs (fs (fs fz)));  (* 2/3 stability *)
          orbit_budget := b' |}, b', fs fz)
  end.

Instance figure_eight_write : WriteOperation unit PhaseOrbit := {
  write_op := fun _ => write_figure_eight_orbit
}.

(* Perturb orbit with chaos - WRITE operation *)
Definition write_perturb_orbit (orbit : PhaseOrbit) (chaos : Fin) (b : Budget)
  : (PhaseOrbit * Budget * Spuren) :=
  match b with
  | fz => (orbit, fz, fz)
  | fs b' =>
      (* Add chaos to phase *)
      match add_fin (phase orbit) chaos b' with
      | (new_phase, b'') =>
          (* Decay stability *)
          match decay_with_budget (stability orbit) b'' with
          | (new_stability, b''') =>
              ({| orbit_points := orbit_points orbit;
                  period := period orbit;
                  phase := new_phase;
                  stability := new_stability;
                  orbit_budget := orbit_budget orbit |}, b''', fs fz)
          end
      end
  end.

Instance perturb_orbit_write : WriteOperation (PhaseOrbit * Fin) PhaseOrbit := {
  write_op := fun '(orbit, chaos) => write_perturb_orbit orbit chaos
}.

(******************************************************************************)
(* SYSTEM OPERATIONS                                                          *)
(******************************************************************************)

(* Evolve entire orbital system - WRITE operation *)
Definition write_evolve_system (sys : OrbitalSystem) (b : Budget) 
  : (OrbitalSystem * Budget * Spuren) :=
  match b with
  | fz => (sys, fz, fz)
  | fs b' =>
      (* Evolve all patterns *)
      let evolved := fold_left (fun acc op =>
        match acc with
        | (patterns, b_acc, h_acc) =>
            match b_acc with
            | fz => (patterns, fz, h_acc)
            | _ =>
                match write_orbital_step op b_acc with
                | (new_op, b'', h) => 
                    (new_op :: patterns, b'', add_spur h_acc h)
                end
            end
        end
      ) (patterns sys) ([], b', fz) in
      match evolved with
      | (new_patterns, b'', h) =>
          ({| orbits := orbits sys;
              patterns := rev new_patterns;
              system_budget := b'' |}, b'', h)
      end
  end.

Instance evolve_system_write : WriteOperation OrbitalSystem OrbitalSystem := {
  write_op := write_evolve_system
}.

(******************************************************************************)
(* HELPER FUNCTIONS                                                          *)
(******************************************************************************)

Definition rev {A : Type} := @List.rev A.

Definition negb (b : bool) : bool :=
  match b with true => false | false => true end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition PhaseOrbit_ext := PhaseOrbit.
Definition OrbitalPattern_ext := OrbitalPattern.
Definition OrbitalSystem_ext := OrbitalSystem.
Definition write_evolve_system_ext := write_evolve_system.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Phase orbits in void mathematics reveal resource truths:
   
   1. ONE TICK PER STEP - Following orbits, checking intersections,
      hopping - all cost exactly one tick. Complexity emerges from
      iteration, not from arbitrary difficulty.
   
   2. NO MAGIC PERIODS - Orbits have simple periods based on their
      point counts. No special significance to any particular period.
   
   3. STABILITY WITHOUT MAGIC - Orbit stability is just a probability,
      not tied to magic thresholds or special values.
   
   4. INTERSECTION IS SIMPLE - Two orbits intersect if they share a
      position. One tick to check, no complex geometry.
   
   5. CHAOS IS UNIFORM - Perturbations don't have special strengths.
      Every perturbation costs one tick and affects the system equally.
   
   This models orbital dynamics where patterns exhaust themselves through
   motion, not through encountering arbitrarily "difficult" regions. *)

End Void_Phase_Orbits.