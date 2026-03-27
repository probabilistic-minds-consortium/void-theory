(******************************************************************************)
(* void_temporal_memory.v - TEMPORAL SUBSTRATE FOR FINITE LEARNING           *)
(* Built entirely from standard library proven-terminating functions         *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_information_theory.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Temporal_Memory.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Information_Theory.

(******************************************************************************)
(* STRATEGY: Use only proven-terminating standard library functions          *)
(*                                                                            *)
(* NO custom Fixpoint - use fold_left, map, filter instead                   *)
(* These are already proven to terminate in Coq.Lists.List                   *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* MEMORY TRACE - Pattern with temporal metadata                             *)
(******************************************************************************)

Record MemoryTrace := {
  trace_pattern : Pattern;
  trace_strength : FinProb;
  trace_age : Fin;
  trace_spur : Spuren;
  last_refreshed : Fin
}.

Record MemoryState := {
  traces : list MemoryTrace;
  current_tick : Fin;
  memory_budget : Budget;
  accumulated_spur : Spuren
}.

(******************************************************************************)
(* SINGLE-TRACE OPERATIONS - Not recursive                                   *)
(******************************************************************************)

(* Decay strength based on age *)
Definition decay_by_age (strength : FinProb) (age : Fin) (b : Budget)
  : (FinProb * Budget) :=
  match age with
  | fz => (strength, b)
  | fs fz => decay_with_budget strength b
  | fs (fs fz) =>
      match decay_with_budget strength b with
      | (d1, b1) => decay_with_budget d1 b1
      end
  | _ =>
      match decay_with_budget strength b with
      | (d1, b1) =>
          match decay_with_budget d1 b1 with
          | (d2, b2) => decay_with_budget d2 b2
          end
      end
  end.

(* Age and decay single trace *)
Definition decay_trace (trace : MemoryTrace) (b : Budget)
  : (MemoryTrace * Budget) :=
  match b with
  | fz => (trace, fz)
  | fs b' =>
      match safe_succ_b (trace_age trace) b' with
      | (new_age, b1) =>
          match decay_by_age (trace_strength trace) new_age b1 with
          | (new_strength, b2) =>
              ({| trace_pattern := trace_pattern trace;
                  trace_strength := new_strength;
                  trace_age := new_age;
                  trace_spur := add_spur (trace_spur trace) operation_cost;
                  last_refreshed := last_refreshed trace |}, b2)
          end
      end
  end.

(* Check if trace collapsed *)
Definition collapse_threshold : FinProb := (fs fz, fs (fs (fs (fs (fs fz))))).

Definition is_collapsed (trace : MemoryTrace) : bool :=
  match prob_le_b (trace_strength trace) collapse_threshold initial_budget with
  | (result, _) => result
  end.

(* Boost strength for refresh *)
Definition boost_strength (strength : FinProb) : FinProb :=
  let (n, d) := strength in
  match n with
  | fz => (fs fz, d)
  | fs n' =>
      match le_fin n d with
      | true => (fs n, d)
      | false => strength
      end
  end.

(* Refresh single trace *)
Definition refresh_trace (trace : MemoryTrace) (tick : Fin) (b : Budget)
  : (MemoryTrace * Budget) :=
  match b with
  | fz => (trace, fz)
  | fs b' =>
      let cost := match trace_age trace with
                  | fz => operation_cost
                  | fs fz => operation_cost
                  | fs (fs fz) => fs operation_cost
                  | _ => fs (fs operation_cost)
                  end in
      match le_fin_b cost b' b' with
      | (true, b1) =>
          match sub_fin b1 cost b1 with
          | (b2, _) =>
              ({| trace_pattern := trace_pattern trace;
                  trace_strength := boost_strength (trace_strength trace);
                  trace_age := fz;
                  trace_spur := add_spur (trace_spur trace) cost;
                  last_refreshed := tick |}, b2)
          end
      | (false, b1) => (trace, b1)
      end
  end.

(* Create new trace *)
Definition record_trace (pattern : Pattern) (tick : Fin) : MemoryTrace :=
  {| trace_pattern := pattern;
     trace_strength := strength pattern;
     trace_age := fz;
     trace_spur := operation_cost;
     last_refreshed := tick |}.

(******************************************************************************)
(* LIST OPERATIONS - Using fold_left (proven terminating)                    *)
(******************************************************************************)

(* Decay all traces using fold_left *)
Definition decay_all_traces (traces : list MemoryTrace) (b : Budget)
  : (list MemoryTrace * Budget) :=
  fold_left
    (fun '(acc_traces, acc_budget) trace =>
       match acc_budget with
       | fz => (acc_traces, fz)  (* Budget exhausted *)
       | fs b' =>
           match decay_trace trace b' with
           | (decayed, b_new) => (decayed :: acc_traces, b_new)
           end
       end)
    traces
    ([], b).

(* Filter collapsed traces using filter (proven terminating) *)
Definition forget_collapsed (traces : list MemoryTrace) : list MemoryTrace :=
  filter (fun t => negb (is_collapsed t)) traces.

(* Find traces at location using filter *)
Definition find_traces_at (traces : list MemoryTrace) (loc : Fin) : list MemoryTrace :=
  filter (fun t => fin_eq (location (trace_pattern t)) loc) traces.

(* Refresh traces at location using map *)
Definition refresh_at_location (traces : list MemoryTrace) (loc : Fin) 
                                (tick : Fin) (b : Budget)
  : (list MemoryTrace * Budget) :=
  fold_left
    (fun '(acc_traces, acc_budget) trace =>
       match acc_budget with
       | fz => (trace :: acc_traces, fz)
       | fs b' =>
           match fin_eq_b (location (trace_pattern trace)) loc b' with
           | (true, b1) =>
               match refresh_trace trace tick b1 with
               | (refreshed, b2) => (refreshed :: acc_traces, b2)
               end
           | (false, b1) => (trace :: acc_traces, b1)
           end
       end)
    traces
    ([], b).

(* Consolidate adjacent duplicates - single pass with fold_left *)
Definition consolidate_adjacent (traces : list MemoryTrace) (b : Budget)
  : (list MemoryTrace * Budget) :=
  match traces with
  | [] => ([], b)
  | first :: rest =>
      let '(result, last_trace, final_budget) :=
        fold_left
          (fun '(acc_traces, prev_trace, acc_budget) curr_trace =>
             match acc_budget with
             | fz => (prev_trace :: acc_traces, curr_trace, fz)
             | fs b' =>
                 match fin_eq_b (location (trace_pattern prev_trace))
                               (location (trace_pattern curr_trace)) b' with
                 | (true, b1) =>
                     (* Same location - keep stronger *)
                     match prob_le_b (trace_strength prev_trace)
                                    (trace_strength curr_trace) b1 with
                     | (true, b2) => (acc_traces, curr_trace, b2)
                     | (false, b2) => (acc_traces, prev_trace, b2)
                     end
                 | (false, b1) =>
                     (* Different - keep both *)
                     (prev_trace :: acc_traces, curr_trace, b1)
                 end
             end)
          rest
          ([], first, b)
      in (last_trace :: result, final_budget)
  end.

(******************************************************************************)
(* TEMPORAL ADVANCE - THE core operator                                      *)
(******************************************************************************)

Definition tick_forward (state : MemoryState) : MemoryState :=
  match memory_budget state with
  | fz => state
  | fs b' =>
      match safe_succ_b (current_tick state) b' with
      | (new_tick, b1) =>
          match decay_all_traces (traces state) b1 with
          | (decayed, b2) =>
              let surviving := forget_collapsed decayed in
              let sp := match sub_fin (fs b') b2 (fs b') with
                         | (consumed, _) => consumed
                         end in
              {| traces := surviving;
                 current_tick := new_tick;
                 memory_budget := b2;
                 accumulated_spur := add_spur (accumulated_spur state) sp |}
          end
      end
  end.

(******************************************************************************)
(* HIGH-LEVEL INTERFACE                                                      *)
(******************************************************************************)

(* Add new pattern to memory *)
Definition record_pattern (state : MemoryState) (pattern : Pattern)
  : MemoryState :=
  match memory_budget state with
  | fz => state
  | fs b' =>
      let new_trace := record_trace pattern (current_tick state) in
      let cost := match fst (strength pattern) with
                  | fz => operation_cost
                  | fs n => fs n
                  end in
      match sub_fin b' cost b' with
      | (b_new, _) =>
          {| traces := new_trace :: traces state;
             current_tick := current_tick state;
             memory_budget := b_new;
             accumulated_spur := add_spur (accumulated_spur state) cost |}
      end
  end.

(* Refresh memories at location *)
Definition refresh_location (state : MemoryState) (loc : Fin)
  : MemoryState :=
  match refresh_at_location (traces state) loc 
                           (current_tick state)
                           (memory_budget state) with
  | (refreshed, b_new) =>
      let sp := match sub_fin (memory_budget state) b_new 
                              (memory_budget state) with
                 | (consumed, _) => consumed
                 end in
      {| traces := refreshed;
         current_tick := current_tick state;
         memory_budget := b_new;
         accumulated_spur := add_spur (accumulated_spur state) sp |}
  end.

(* Consolidate memory *)
Definition consolidate_memory (state : MemoryState) : MemoryState :=
  match consolidate_adjacent (traces state) (memory_budget state) with
  | (consolidated, b_new) =>
      let sp := match sub_fin (memory_budget state) b_new 
                              (memory_budget state) with
                 | (consumed, _) => consumed
                 end in
      {| traces := consolidated;
         current_tick := current_tick state;
         memory_budget := b_new;
         accumulated_spur := add_spur (accumulated_spur state) sp |}
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition MemoryTrace_ext := MemoryTrace.
Definition MemoryState_ext := MemoryState.
Definition tick_forward_ext := tick_forward.
Definition record_pattern_ext := record_pattern.
Definition refresh_location_ext := refresh_location.
Definition consolidate_memory_ext := consolidate_memory.
Definition find_traces_at_ext := find_traces_at.

End Void_Temporal_Memory.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(*                                                                            *)
(* This module demonstrates VOID's meta-principle: don't prove termination   *)
(* yourself when proven-terminating operations already exist.                 *)
(*                                                                            *)
(* By using standard library functions (fold_left, map, filter), we:         *)
(* 1. Avoid termination checker battles                                      *)
(* 2. Build from verified foundations                                        *)
(* 3. Make code obviously correct by composition                             *)
(*                                                                            *)
(* TIME IS HEAT - Each tick accumulates consumed budget as Spuren              *)
(* MEMORY IS MAINTENANCE - Traces decay unless actively refreshed            *)
(* PARTIAL IS HONEST - fold_left stops when budget exhausts                  *)
(* COMPOSITION OVER RECURSION - Build from proven primitives                 *)
(******************************************************************************)