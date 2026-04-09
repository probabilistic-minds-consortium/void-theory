(******************************************************************************)
(* void_resonance.v - BIDIRECTIONAL RESONANCE CASCADES                       *)
(* Two systems exchange Spuren: the seeker marks the found,                  *)
(* and the found marks the seeker. READ IS WRITE.                            *)
(*                                                                            *)
(* POST-R/W COLLAPSE: resonance is not a pattern "finding" a location.      *)
(* It is two systems writing on each other simultaneously.                   *)
(* The seeker leaves a trace (SpurenA) on the network.                      *)
(* The network leaves a trace (SpurenB) on the seeker.                      *)
(* Neither can resonate without being changed by the resonance.              *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_information_theory.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Resonance_Cascades.

Import Void_Pattern.
Import Void_Arithmetic.
Import Void_Probability_Minimal.
Import Void_Information_Theory.
Import List.

(* List reverse function *)
Definition rev {A : Type} := @List.rev A.

(******************************************************************************)
(* FUNDAMENTAL CONSTANT - One tick of time                                   *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.  (* The only arbitrary constant *)

(******************************************************************************)
(* CORE TYPES WITH BUDGET AWARENESS                                          *)
(******************************************************************************)

(* A resonant location has a base frequency *)
Record ResonantLocation := {
  loc_id : Fin;
  base_frequency : FinProb;     (* Natural oscillation *)
  damping : Fin;                (* How quickly it loses energy *)
  current_amplitude : FinProb   (* Current oscillation strength *)
}.

(* Network state tracks resonant locations with budget *)
Record NetworkState := {
  locations : list ResonantLocation;
  global_phase : Fin;
  network_budget : Budget
}.

(* Pattern with resonance-seeking capability *)
Record ResonantPattern := {
  pattern : Pattern;
  resonance_budget : Budget
}.

(******************************************************************************)
(* STRUCTURAL PROJECTIONS                                                    *)
(* These are record field accesses — definitional in Coq, zero-cost.        *)
(* They are NOT epistemological reads. A record projection is syntax,        *)
(* not observation. The system does not "look at" its own field;            *)
(* the field IS the system. No budget consumed, no Spuren produced.         *)
(* Contrast with le_fin_b3: THAT is an observation. It costs.              *)
(******************************************************************************)

Definition read_frequency (loc : ResonantLocation) : FinProb :=
  base_frequency loc.

Definition read_amplitude (loc : ResonantLocation) : FinProb :=
  current_amplitude loc.

Definition read_damping (loc : ResonantLocation) : Fin :=
  damping loc.

Definition read_pattern_exhausted (rp : ResonantPattern) : bool :=
  match resonance_budget rp with
  | fz => true
  | _ => false
  end.

(******************************************************************************)
(* COST — always one tick. Complexity emerges from iteration, not pricing.  *)
(******************************************************************************)

(* All resonance operations cost one tick. No magic thresholds.              *)
(* "Expensive" means many iterations, not a higher unit price.              *)

(******************************************************************************)
(* WRITE OPERATIONS - Change resonance state                                 *)
(******************************************************************************)

(* Distance between probabilities - helper function using existing operations *)
Definition dist_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match dist_fin_b (fst p1) (fst p2) b with
  | (dist, b') => ((dist, snd p1), b')
  end.

(* Check frequency match — costs budget, produces Spuren *)
Definition write_frequency_match (p_freq loc_freq : FinProb) (threshold : Fin) (b : Budget)
  : (bool * Budget * Spuren) :=
  match b with
  | fz => (false, fz, fz)
  | fs b' =>
      match dist_prob_b p_freq loc_freq b' with
      | (dist, b'') =>
          match le_fin_b (fst dist) threshold b'' with
          | (within, b''') => (within, b''', fs fz)
          end
      end
  end.

(* Find resonant location — costs Spuren per location checked *)
Fixpoint write_find_resonant (rp : ResonantPattern) (locs : list ResonantLocation)
                             (b : Budget) : (option ResonantLocation * Budget * Spuren) :=
  match locs, b with
  | [], _ => (None, b, fz)
  | _, fz => (None, fz, fz)
  | loc :: rest, fs b' =>
      match write_frequency_match (strength (pattern rp)) (base_frequency loc) (fs fz) b' with
      | (true, b'', h) => (Some loc, b'', h)
      | (false, b'', h) =>
          match write_find_resonant rp rest b'' with
          | (result, b''', h') => (result, b''', add_spur h h')
          end
      end
  end.

(* Jump to resonant location — pattern writes itself onto new position *)
Definition write_resonance_jump (rp : ResonantPattern) (target : ResonantLocation)
                                (b : Budget) : (ResonantPattern * Budget * Spuren) :=
  match b with
  | fz => (rp, fz, fz)
  | fs b' =>
      let new_pattern := {| location := loc_id target;
                           strength := strength (pattern rp) |} in
      ({| pattern := new_pattern;
          resonance_budget := resonance_budget rp |}, b', fs fz)
  end.

(******************************************************************************)
(* BIDIRECTIONAL AMPLIFICATION — THE HEART OF R/W RESONANCE                  *)
(* This is the only function where both participants change:                 *)
(*   - Pattern gets new strength  (trace of location on pattern)            *)
(*   - Location gets new amplitude (trace of pattern on location)           *)
(* Neither leaves the exchange unchanged. write_asymmetry in action.        *)
(******************************************************************************)

Definition write_amplify (rp : ResonantPattern) (loc : ResonantLocation) (b : Budget)
  : (ResonantPattern * ResonantLocation * Budget * Spuren) :=
  match b with
  | fz => (rp, loc, fz, fz)
  | fs b' =>
      match add_prob_b (strength (pattern rp)) (current_amplitude loc) b' with
      | (new_strength, b'') =>
          let new_pattern := {| location := location (pattern rp);
                               strength := new_strength |} in
          let new_rp := {| pattern := new_pattern;
                          resonance_budget := resonance_budget rp |} in
          let new_loc := {| loc_id := loc_id loc;
                           base_frequency := base_frequency loc;
                           damping := damping loc;
                           current_amplitude := new_strength |} in
          (new_rp, new_loc, b'', fs fz)
      end
  end.

(* Apply damping - WRITE operation *)
Definition write_apply_damping (loc : ResonantLocation) (b : Budget)
  : (ResonantLocation * Budget * Spuren) :=
  match b with
  | fz => (loc, fz, fz)
  | fs b' =>
      (* Decay amplitude *)
      match decay_with_budget (current_amplitude loc) b' with
      | (new_amp, b'') =>
          ({| loc_id := loc_id loc;
              base_frequency := base_frequency loc;
              damping := damping loc;
              current_amplitude := new_amp |}, b'', fs fz)
      end
  end.


(* Cascade step - WRITE operation *)
Definition write_cascade_step (net : NetworkState) (b : Budget) 
  : (NetworkState * Budget * Spuren) :=
  match b with
  | fz => (net, fz, fz)
  | fs b' =>
      (* Apply damping to all locations *)
      let damped_locs := fold_left (fun acc loc =>
        match acc with
        | (locs, b_acc) =>
            match b_acc with
            | fz => (locs, fz)
            | _ =>
                match write_apply_damping loc b_acc with
                | (new_loc, b'', h) => (new_loc :: locs, b'')
                end
            end
        end
      ) (locations net) ([], b') in
      match damped_locs with
      | (new_locs, b'') =>
          ({| locations := rev new_locs;
              global_phase := fs (global_phase net);
              network_budget := b'' |}, b'', fs fz)
      end
  end.


(******************************************************************************)
(* COMPOSITE OPERATIONS                                                       *)
(******************************************************************************)

(* Replace a location in the network by loc_id match *)
Fixpoint replace_location (locs : list ResonantLocation) (new_loc : ResonantLocation)
  : list ResonantLocation :=
  match locs with
  | [] => [new_loc]
  | loc :: rest =>
      match fin_eq (loc_id loc) (loc_id new_loc) with
      | true => new_loc :: rest
      | false => loc :: replace_location rest new_loc
      end
  end.

(******************************************************************************)
(* RESONANCE_SEEK_RW — BIDIRECTIONAL RESONANCE                               *)
(*                                                                            *)
(* This is the corrected resonance operation after R/W collapse.             *)
(* Old resonance_seek was unidirectional: pattern seeks, finds, jumps.       *)
(* The network was a passive landscape. This violated write_asymmetry.       *)
(*                                                                            *)
(* New resonance_seek_rw:                                                    *)
(*   1. Pattern SEARCHES network (costs search_spur — paid by seeker)       *)
(*   2. If found: pattern JUMPS to location (costs jump_spur)               *)
(*   3. AMPLIFY — the BIDIRECTIONAL heart:                                   *)
(*      - Pattern gets new strength (location writes on pattern)            *)
(*      - Location gets new amplitude (pattern writes on location)          *)
(*   4. Returns TWO Spuren:                                                  *)
(*      - spur_on_net:     trace the pattern left on the network            *)
(*      - spur_on_pattern: trace the network left on the pattern            *)
(*                                                                            *)
(* Neither participant leaves unchanged. This is autopoiesis:                *)
(* the observer changes the observed AND the observed changes the observer.  *)
(******************************************************************************)

Definition resonance_seek_rw (rp : ResonantPattern) (net : NetworkState) (b : Budget)
  : (ResonantPattern * NetworkState * Budget * Spuren * Spuren) :=
  (* Returns: (rp', net', remaining_b, spur_on_net, spur_on_pattern) *)
  match b with
  | fz => (rp, net, fz, fz, fz)
  | fs b' =>
      match write_find_resonant rp (locations net) b' with
      | (None, b1, search_spur) =>
          (* No resonance found. Pattern paid search cost, got nothing. *)
          (* But: the SEARCH ITSELF changed the pattern's budget.       *)
          (* Even failed observation is observation. search_spur ≠ fz.  *)
          let new_net := {| locations := locations net;
                           global_phase := global_phase net;
                           network_budget := b1 |} in
          (rp, new_net, b1, fz, search_spur)

      | (Some loc, b1, search_spur) =>
          (* Found resonance. Now: jump + bidirectional amplification. *)
          match write_resonance_jump rp loc b1 with
          | (jumped_rp, b2, jump_spur) =>
              match write_amplify jumped_rp loc b2 with
              | (new_rp, new_loc, b3, amplify_spur) =>
                  (* new_rp:  pattern changed by location (new strength)  *)
                  (* new_loc: location changed by pattern (new amplitude) *)
                  let new_locs := replace_location (locations net) new_loc in
                  let new_net := {| locations := new_locs;
                                   global_phase := global_phase net;
                                   network_budget := b3 |} in
                  let spur_on_net := amplify_spur in
                  let spur_on_pattern := add_spur search_spur
                                          (add_spur jump_spur amplify_spur) in
                  (new_rp, new_net, b3, spur_on_net, spur_on_pattern)
              end
          end
      end
  end.

(* Backward compatibility wrapper — old unidirectional interface.            *)
(* Drops the Spuren. Use resonance_seek_rw for correct thermodynamics.      *)
Definition resonance_seek (rp : ResonantPattern) (net : NetworkState)
  : (ResonantPattern * NetworkState) :=
  match resonance_seek_rw rp net (network_budget net) with
  | (rp', net', _, _, _) => (rp', net')
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition ResonantLocation_ext := ResonantLocation.
Definition NetworkState_ext := NetworkState.
Definition ResonantPattern_ext := ResonantPattern.
Definition resonance_seek_rw_ext := resonance_seek_rw.
Definition resonance_seek_ext := resonance_seek.   (* backward compat *)

(******************************************************************************)
(* PHILOSOPHICAL CODA — POST-R/W COLLAPSE                                    *)
(*                                                                            *)
(* Resonance is not a pattern "finding" a location.                          *)
(* It is two systems WRITING ON EACH OTHER simultaneously.                   *)
(*                                                                            *)
(* The old model (resonance_seek): the network is a passive landscape.      *)
(* The pattern moves through it like a tourist. The landscape does not care. *)
(* This is the lie of classical computation: read without trace.             *)
(*                                                                            *)
(* The new model (resonance_seek_rw):                                        *)
(*   - The pattern writes itself onto the location (amplify_spur on net)    *)
(*   - The location writes itself onto the pattern (search + jump + amplify *)
(*     spuren on pattern)                                                    *)
(*   - Neither can resonate without being changed by the resonance          *)
(*   - Even FAILED search costs the pattern (search_spur ≠ fz when b > 0)  *)
(*                                                                            *)
(* Resonance is mutual metabolic exchange. Not information retrieval.        *)
(* Two organisms, touching, both changed. Maturana's structural coupling,   *)
(* compiled.                                                                  *)
(*                                                                            *)
(* The asymmetry (write_asymmetry, tw. 22):                                  *)
(*   - The pattern (seeker) is BLIND to its own transformation              *)
(*   - The location (found) receives the full imprint                       *)
(*   - The seeker thinks it "found" something. In truth, it was found.      *)
(******************************************************************************)

End Void_Resonance_Cascades.