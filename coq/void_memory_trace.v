(******************************************************************************)
(* void_memory_trace.v - BUDGET-AWARE MEMORY TRACES                          *)
(* Following decay gradients costs resources                                  *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_time_memory_composition.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Memory_Trace.

(* Import all modules EXCEPT Void_Finite_Minimal (which doesn't exist) *)
Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Time_Memory_Composition.

(* Pure decay: reduce strength without budget *)
Definition decay_trace (mt : MemoryTrace) : MemoryTrace :=
  let (n, d) := strength mt in
  let new_strength := match n with
                      | fs (fs n') => (fs n', d)
                      | _ => (n, d)
                      end in
  {| remembered_tick := remembered_tick mt;
     strength := new_strength |}.

(******************************************************************************)
(* BUDGET-AWARE TYPES                                                         *)
(******************************************************************************)

(* Pattern with memory-surfing budget *)
Record MemorySurfer := {
  surfer_pattern : Pattern;
  surf_budget : Budget
}.

(* Memory bank with operation budget *)
Record BudgetedMemoryBank := {
  bank : MemoryBank;
  bank_budget : Budget
}.

(******************************************************************************)
(* HELPER FUNCTIONS TO AVOID AMBIGUITY                                       *)
(******************************************************************************)

(* Extract strength from pattern *)
Definition pattern_strength (p : Pattern) : FinProb :=
  Void_Pattern.strength p.

(* Extract strength from memory trace *)  
Definition trace_strength (mt : MemoryTrace) : FinProb :=
  match mt with
  | Build_MemoryTrace _ s => s
  end.

(* Extract tick from memory trace *)
Definition trace_tick (mt : MemoryTrace) : tick :=
  match mt with
  | Build_MemoryTrace t _ => t
  end.

(******************************************************************************)
(* BASIC OPERATIONS WITH BUDGET                                               *)
(******************************************************************************)

(* Alias to avoid name clash - costs budget to access *)
Definition mt_strength_b (mt : MemoryTrace) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => ((fz, fs fz), fz)
  | fs b' => (trace_strength mt, b')
  end.

(* Calculate gradient strength - costs budget *)
Definition trace_gradient_b (t1 t2 : MemoryTrace) (b : Budget) : (Fin * Budget) :=
  match mt_strength_b t1 b with
  | (s1, b1) =>
      match mt_strength_b t2 b1 with
      | (s2, b2) =>
          match le_fin_b (fst s1) (fst s2) b2 with
          | (true, b3) => sub_fin (fst s2) (fst s1) b3
          | (false, b3) => sub_fin (fst s1) (fst s2) b3
          end
      end
  end.

(* Extract location from tick - costs budget *)
Definition tick_location_b (t : tick) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      match t with
      | Tick s1 _ => (fst s1, b')
      end
  end.

(******************************************************************************)
(* GRADIENT FINDING WITH BUDGET                                               *)
(******************************************************************************)

(* Find steepest gradient - expensive search *)
Definition find_steepest_gradient_b (current_loc : Fin) 
                                   (bbank : BudgetedMemoryBank)
  : (option Fin * Budget) :=
  match traces (bank bbank), bank_budget bbank with
  | [], _ => (None, bank_budget bbank)
  | _, fz => (None, fz)
  | traces_list, budget =>
      (* Extract locations - costs budget per trace *)
      let extract_locs := fold_left (fun acc mt =>
        match acc with
        | (locs, b) =>
            match tick_location_b (trace_tick mt) b with
            | (loc, b') => (loc :: locs, b')
            end
        end
      ) traces_list ([], budget) in
      
      match extract_locs with
      | ([], b_final) => (None, b_final)
      | (loc :: locs, b_final) =>
          (* Check if at current location *)
          match fin_eq_b loc current_loc b_final with
          | (true, b') =>
              match locs with
              | [] => (None, b')
              | next :: _ => (Some next, b')
              end
          | (false, b') => (Some loc, b')
          end
      end
  end.

(* Follow freshest trace - costs budget to find *)
Definition follow_freshest_trace_b (ms : MemorySurfer) 
                                  (bbank : BudgetedMemoryBank)
  : (Fin * Budget) :=
  match traces (bank bbank), surf_budget ms with
  | [], _ => (location (surfer_pattern ms), surf_budget ms)
  | _, fz => (location (surfer_pattern ms), fz)
  | t :: ts, budget =>
      (* Find strongest trace - expensive operation *)
      let find_strongest := fold_left (fun acc mt =>
        match acc with
        | (best, b) =>
            match mt_strength_b best b with
            | (best_strength, b1) =>
                match mt_strength_b mt b1 with
                | (mt_strength, b2) =>
                    match le_fin_b (fst best_strength) (fst mt_strength) b2 with
                    | (true, b3) => (mt, b3)
                    | (false, b3) => (best, b3)
                    end
                end
            end
        end
      ) ts (t, budget) in
      
      match find_strongest with
      | (strongest, b_final) =>
          tick_location_b (trace_tick strongest) b_final
      end
  end.

(******************************************************************************)
(* SCENT FIELD CREATION - EXPENSIVE                                          *)
(******************************************************************************)

(* Create scent field - costs budget per trace *)
Definition scent_field_b (bbank : BudgetedMemoryBank) 
  : (list (Fin * Fin) * Budget) :=
  fold_left (fun acc mt =>
    match acc with
    | (field, b) =>
        match tick_location_b (remembered_tick mt) b with
        | (loc, b1) =>
            match mt_strength_b mt b1 with
            | (strength_prob, b2) =>
                ((loc, fst strength_prob) :: field, b2)
            end
        end
    end
  ) (traces (bank bbank)) ([], bank_budget bbank).

(******************************************************************************)
(* PATTERN MOVEMENT WITH BUDGET                                              *)
(******************************************************************************)

(* Follow decay trail - costs budget *)
Definition follow_decay_trail_b (ms : MemorySurfer) 
                               (bbank : BudgetedMemoryBank)
  : MemorySurfer :=
  match find_steepest_gradient_b (location (surfer_pattern ms)) bbank with
  | (None, b') => 
      {| surfer_pattern := surfer_pattern ms;
         surf_budget := b' |}
  | (Some new_loc, b') =>
      match decay_with_budget (pattern_strength (surfer_pattern ms)) b' with
      | (new_strength, b'') =>
          {| surfer_pattern := {| Void_Pattern.location := new_loc;
                                 Void_Pattern.strength := new_strength |};
             surf_budget := b'' |}
      end
  end.

  
  (* Pattern leaves trace - costs budget *)
Definition pattern_leaves_trace_b (ms : MemorySurfer) 
                                 (bbank : BudgetedMemoryBank)
  : BudgetedMemoryBank :=
  match surf_budget ms with
  | fz => bbank  (* No budget to leave trace *)
  | fs b' =>
      let loc := location (surfer_pattern ms) in
      let str := pattern_strength (surfer_pattern ms) in
      let t := Tick (loc, fs fz) (loc, fz) in
      let new_trace := Build_MemoryTrace t str in
      match write_store_observation (bank bbank) new_trace b' with
      | (new_bank, b'', _) =>
          {| bank := new_bank;
             bank_budget := b'' |}
      end
  end.

(******************************************************************************)
(* TRACE INTENSITY CALCULATION                                               *)
(******************************************************************************)

(* Trace intensity at location - expensive aggregation *)
Definition trace_intensity_at_b (loc : Fin) (bbank : BudgetedMemoryBank) 
  : (Fin * Budget) :=
  fold_left (fun acc mt =>
    match acc with
    | (intensity, b) =>
        match tick_location_b (remembered_tick mt) b with
        | (mt_loc, b1) =>
            match fin_eq_b mt_loc loc b1 with
            | (true, b2) =>
                match mt_strength_b mt b2 with
                | (strength_prob, b3) =>
                    add_fin intensity (fst strength_prob) b3
                end
            | (false, b2) => (intensity, b2)
            end
        end
    end
  ) (traces (bank bbank)) (fz, bank_budget bbank).

(******************************************************************************)
(* PATH FINDING WITH BUDGET                                                   *)
(******************************************************************************)

(* Find path through traces - limited by budget *)
Fixpoint trace_path_b (start : Fin) (bbank : BudgetedMemoryBank) (max_steps : Fin)
  : (list Fin * Budget) :=
  match max_steps, bank_budget bbank with
  | fz, b => ([start], b)
  | _, fz => ([start], fz)
  | fs steps', _ =>
      match find_steepest_gradient_b start bbank with
      | (None, b') => ([start], b')
      | (Some next, b') =>
          match trace_path_b next 
                {| bank := bank bbank; bank_budget := b' |} 
                steps' with
          | (path, b'') => (start :: path, b'')
          end
      end
  end.

(******************************************************************************)
(* AGING AND DECAY WITH BUDGET                                              *)
(******************************************************************************)

(* Age all traces - costs budget per trace *)
Definition age_all_traces_b (bbank : BudgetedMemoryBank) 
  : BudgetedMemoryBank :=
  let aged_traces_and_budget := fold_left (fun acc mt =>
    match acc with
    | (aged, b) =>
        match b with
        | fz => (aged, fz)
        | fs b' => (decay_trace mt :: aged, b')
        end
    end
  ) (traces (bank bbank)) ([], bank_budget bbank) in
  
  match aged_traces_and_budget with
  | (aged, b_final) =>
      {| bank := {| traces := aged;
                    capacity := capacity (bank bbank);
                    owner_resolution := owner_resolution (bank bbank) |};
         bank_budget := b_final |}
  end.

(******************************************************************************)
(* GRADIENT SURFING WITH BUDGET                                              *)
(******************************************************************************)

(* Surf gradient - each hop costs *)
Fixpoint surf_gradient_b (loc : Fin) (bbank : BudgetedMemoryBank) 
                        (momentum : Fin) : (Fin * Budget) :=
  match momentum, bank_budget bbank with
  | fz, b => (loc, b)
  | _, fz => (loc, fz)
  | fs m', _ =>
      match find_steepest_gradient_b loc bbank with
      | (None, b') => (loc, b')
      | (Some next, b') =>
          surf_gradient_b next 
            {| bank := bank bbank; bank_budget := b' |} 
            m'
      end
  end.

(* Pattern surfs gradient - momentum determines cost *)
Definition gradient_surf_b (ms : MemorySurfer) 
                          (bbank : BudgetedMemoryBank) 
                          (momentum : Fin)
  : MemorySurfer :=
  match surf_gradient_b (location (surfer_pattern ms)) bbank momentum with
  | (new_loc, b') =>
      match momentum with
      | fz => 
          {| surfer_pattern := {| Void_Pattern.location := new_loc;
                                 Void_Pattern.strength := pattern_strength (surfer_pattern ms) |};
             surf_budget := b' |}
      | fs _ =>
          match decay_with_budget (pattern_strength (surfer_pattern ms)) b' with
          | (new_strength, b'') =>
              {| surfer_pattern := {| Void_Pattern.location := new_loc;
                                     Void_Pattern.strength := new_strength |};
                 surf_budget := b'' |}
          end
      end
  end.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Memory traces in void mathematics embody temporal ecology:
   
   1. FOLLOWING COSTS - Tracing memories depletes the tracer. Each step
      along a decay gradient costs budget, limiting how far patterns can
      surf through memory space.
   
   2. TRACES DECAY - Memory traces weaken over time, creating gradients
      that patterns can follow. But following these gradients accelerates
      the follower's own decay.
   
   3. LEAVING TRACES COSTS - Creating new memory traces depletes the
      pattern's budget. Only well-resourced patterns can afford to leave
      strong traces.
   
   4. INTENSITY AGGREGATION - Computing the total trace intensity at a
      location requires examining all traces, an expensive operation that
      itself costs significant budget.
   
   5. AGING IS WORK - Even the passive decay of traces requires budget
      to compute. Time doesn't pass for free in void mathematics.
   
   This creates a poignant dynamic: patterns can follow the fading traces
   of their predecessors, but the very act of following accelerates their
   own dissolution into the void. *)

End Void_Memory_Trace.