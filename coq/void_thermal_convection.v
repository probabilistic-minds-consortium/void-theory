(******************************************************************************)
(* void_thermal_convection.v - BUDGET-AWARE THERMAL DYNAMICS                 *)
(* Spuren IS computational budget. Convection exhausts the system.             *)
(* Rising costs, sinking costs, circulation depletes - thermodynamics is real *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_pattern_thermo.
Require Import void_arithmetic.
Require Import void_information_theory.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Thermal_Convection.

Import Void_Pattern.
Import Void_Pattern_Thermo.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Information_Theory.

(******************************************************************************)
(* DYNAMIC COSTS BASED ON RESOURCE AVAILABILITY (READ OPERATIONS)            *)
(******************************************************************************)

(* Rise cost depends on layer budget - READ operation *)
Definition rise_cost_dynamic (layer_budget : Budget) : Fin :=
  match layer_budget with
  | fz => fs (fs fz)        (* Starved: expensive *)
  | fs fz => fs (fs fz)     (* Low: expensive *)  
  | _ => fs fz              (* Normal: standard *)
  end.

#[export] Instance rise_cost_read : ReadOperation Budget Fin := {
  read_op := rise_cost_dynamic
}.

(* Sink cost - always cheaper than rising (gravity helps) - READ operation *)
Definition sink_cost_dynamic (layer_budget : Budget) : Fin :=
  fs fz.  (* Always one tick - gravity makes this cheap *)

#[export] Instance sink_cost_read : ReadOperation Budget Fin := {
  read_op := sink_cost_dynamic
}.

(* Circulation cost based on cell energy - READ operation *)
Definition circulation_cost_dynamic (cell_budget : Budget) : Fin :=
  match cell_budget with
  | fz => fs (fs (fs fz))   (* Exhausted cell: very expensive *)
  | fs fz => fs (fs fz)     (* Low energy: expensive *)
  | _ => fs fz              (* Normal energy: standard *)
  end.

#[export] Instance circulation_cost_read : ReadOperation Budget Fin := {
  read_op := circulation_cost_dynamic
}.

(* Layer search cost based on available budget - READ operation *)
Definition layer_search_cost_dynamic (available_budget : Budget) : Fin :=
  match available_budget with
  | fz => fs (fs fz)        (* No budget: expensive to even try *)
  | _ => fs fz              (* Normal: standard search cost *)
  end.

#[export] Instance layer_search_cost_read : ReadOperation Budget Fin := {
  read_op := layer_search_cost_dynamic
}.

(* Temperature calculation cost based on layer budget - READ operation *)
Definition temperature_calc_cost_dynamic (layer_budget : Budget) : Fin :=
  match layer_budget with
  | fz => fs (fs fz)        (* No budget: expensive *)
  | _ => fs fz              (* Normal: standard *)
  end.

#[export] Instance temperature_calc_cost_read : ReadOperation Budget Fin := {
  read_op := temperature_calc_cost_dynamic
}.

(* Emergency multiplier based on crisis level - READ operation *)
Definition emergency_multiplier_dynamic (system_budget : Budget) : Fin :=
  match system_budget with
  | fz => fs (fs (fs (fs fz)))         (* Crisis: 4x *)
  | fs fz => fs (fs (fs fz))           (* Low: 3x *)
  | fs (fs fz) => fs (fs fz)           (* Moderate: 2x *)
  | _ => fs fz                         (* Normal: 1x *)
  end.

#[export] Instance emergency_multiplier_read : ReadOperation Budget Fin := {
  read_op := emergency_multiplier_dynamic
}.

(* Spuren threshold based on system state - READ operation *)
Definition spur_threshold_dynamic (system_budget : Budget) : Fin :=
  match system_budget with
  | fz => fz                (* No budget: even cold patterns try to move *)
  | fs fz => fs fz          (* Low budget: lower threshold *)
  | _ => fs (fs fz)         (* Normal: standard threshold *)
  end.

#[export] Instance spur_threshold_read : ReadOperation Budget Fin := {
  read_op := spur_threshold_dynamic
}.

(******************************************************************************)
(* HELPER OPERATIONS WITH BUDGET                                             *)
(******************************************************************************)

(* Boolean operations - structural *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Get pattern from ThermalPattern *)
Definition cold (tp : ThermalPattern) : Pattern := pattern tp.

(* Get Spuren from ThermalPattern *)
Definition spur_val (tp : ThermalPattern) : Fin := spur_generated tp.

(* Minimum with budget *)
Definition min_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => (n, b')
  | (false, b') => (m, b')
  end.

(* Decay for probabilities - needed for convection_strength *)
Definition decay_prob (p : FinProb) : FinProb :=
  match p with
  | (fs (fs n), d) => (fs n, d)
  | other => other
  end.

(******************************************************************************)
(* CORE TYPES WITH BUDGET AWARENESS                                          *)
(******************************************************************************)

(* Thermal layer with energy budget *)
Record ThermalLayer := {
  layer_height : Fin;
  layer_temp : Fin;
  layer_patterns : list ThermalPattern;
  layer_budget : Budget;  (* Layer's computational resources *)
  convection_strength : FinProb
}.

(* Convection cell with REAL energy consumption *)
Record ConvectionCell := {
  hot_layer : Fin;
  cold_layer : Fin;
  circulation_rate : Fin;
  cell_budget : Budget  (* Actually gets consumed! *)
}.

(* Thermal system with global budget *)
Record ThermalSystem := {
  layers : list ThermalLayer;
  cells : list ConvectionCell;
  gravity_strength : Fin;
  system_budget : Budget;  (* Total system energy *)
  total_spur : Fin        (* Spuren = spent budget *)
}.

(******************************************************************************)
(* THERMAL OPERATIONS WITH BUDGET AND HEAT                                   *)
(******************************************************************************)

(* Check if pattern is hot enough to rise - NOW WITH DYNAMIC THRESHOLD *)
Definition exceeds_heat_threshold_b (h : Fin) (b : Budget) : (bool * Budget) :=
  let threshold := spur_threshold_dynamic b in
  le_fin_b threshold h b.

(* Find cooler layer above - expensive search with dynamic cost *)
Definition find_cool_layer_above_b (current : Fin) (layers : list ThermalLayer) (b : Budget)
  : (option Fin * Budget) :=
  match b with
  | fz => (None, fz)
  | _ =>
      let search_cost := layer_search_cost_dynamic b in
      match sub_fin b search_cost b with
      | (_, b1) =>
          (* Search through layers *)
          fold_left (fun acc l =>
            match acc with
            | (Some found, b_acc) => (Some found, b_acc)  (* Already found *)
            | (None, b_acc) =>
                match b_acc with
                | fz => (None, fz)
                | fs b' =>
                    match le_fin_b current (layer_height l) b' with
                    | (above, b1) =>
                        match le_fin_b (layer_temp l) (fs fz) b1 with
                        | (cool, b2) =>
                            if andb above cool then
                              (Some (layer_height l), b2)
                            else
                              (None, b2)
                        end
                    end
                end
            end
          ) layers (None, b1)
      end
  end.

(* Find warmer layer below - expensive search with dynamic cost *)
Definition find_warm_layer_below_b (current : Fin) (layers : list ThermalLayer) (b : Budget)
  : (option Fin * Budget) :=
  match b with
  | fz => (None, fz)
  | _ =>
      let search_cost := layer_search_cost_dynamic b in
      match sub_fin b search_cost b with
      | (_, b1) =>
          fold_left (fun acc l =>
            match acc with
            | (Some found, b_acc) => (Some found, b_acc)
            | (None, b_acc) =>
                match b_acc with
                | fz => (None, fz)
                | fs b' =>
                    match le_fin_b (layer_height l) current b' with
                    | (below, b1) =>
                        match le_fin_b (fs fz) (layer_temp l) b1 with
                        | (warm, b2) =>
                            if andb below warm then
                              (Some (layer_height l), b2)
                            else
                              (None, b2)
                        end
                    end
                end
            end
          ) layers (None, b1)
      end
  end.

(* Thermal circulation - costs budget with dynamic pricing! *)
Definition thermal_circulation_b (tp : ThermalPattern) (sys : ThermalSystem)
  : (Fin * Budget) :=
  match system_budget sys with
  | fz => (location (cold tp), fz)  (* No budget - no movement *)
  | _ =>
      match exceeds_heat_threshold_b (spur_val tp) (system_budget sys) with
      | (hot_enough, b1) =>
          if hot_enough then
            (* Rise costs more than sinking - dynamic cost *)
            let rise_cost := rise_cost_dynamic (system_budget sys) in
            match sub_fin b1 rise_cost b1 with
            | (_, b2) =>
                match find_cool_layer_above_b (location (cold tp)) (layers sys) b2 with
                | (Some new_layer, b3) => (new_layer, b3)
                | (None, b3) => (location (cold tp), b3)
                end
            end
          else
            (* Sinking is cheaper - dynamic cost *)
            let sink_cost := sink_cost_dynamic (system_budget sys) in
            match sub_fin b1 sink_cost b1 with
            | (_, b2) =>
                match find_warm_layer_below_b (location (cold tp)) (layers sys) b2 with
                | (Some new_layer, b3) => (new_layer, b3)
                | (None, b3) => (location (cold tp), b3)
                end
            end
      end
  end.

(* Apply circulation to pattern - depletes pattern AND system *)
(* UPDATED to use explicit constructor *)
Definition circulate_pattern_b (tp : ThermalPattern) (sys : ThermalSystem)
  : (ThermalPattern * Budget) :=
  match thermal_circulation_b tp sys with
  | (new_loc, b1) =>
      match fin_eq_b new_loc (location (cold tp)) b1 with
      | (stayed, b2) =>
          if stayed then
            (* No movement - keep Spuren but lose budget *)
            (Build_ThermalPattern (cold tp) (spur_val tp) (compute_budget tp), b2)
          else
            (* Movement dissipates Spuren AND strength *)
            match decay_with_budget (strength (cold tp)) b2 with
            | (new_strength, b3) =>
                let new_spur := match spur_val tp with
                               | fz => fz
                               | fs h => h
                               end in
                let new_pattern := Build_Pattern new_loc new_strength in
                (Build_ThermalPattern new_pattern new_spur (compute_budget tp), b3)
            end
      end
  end.

(* Update layer temperature - costs budget to compute with dynamic cost *)
Definition update_layer_temperature_b (layer : ThermalLayer) : ThermalLayer :=
  match layer_budget layer with
  | fz => layer  (* No budget - frozen *)
  | _ =>
      let temp_calc_cost := temperature_calc_cost_dynamic (layer_budget layer) in
      match sub_fin (layer_budget layer) temp_calc_cost (layer_budget layer) with
      | (_, b1) =>
          (* Calculate total Spuren - expensive *)
          let calc_spur := fold_left (fun acc tp =>
            match acc with
            | (total, b_acc) =>
                match b_acc with
                | fz => (total, fz)
                | fs b' => 
                    match add_fin total (spur_val tp) b' with
                    | (new_total, b'') => (new_total, b'')
                    end
                end
            end
          ) (layer_patterns layer) (fz, b1) in
          
          match calc_spur with
          | (total_spur, b2) =>
              match min_fin_b total_spur (fs (fs (fs fz))) b2 with
              | (capped_spur, b3) =>
                  Build_ThermalLayer 
                    (layer_height layer)
                    capped_spur
                    (layer_patterns layer)
                    b3
                    (convection_strength layer)
              end
          end
      end
  end.

(* Step convection cell - actually consumes energy with dynamic cost! *)
Definition step_convection_cell_b (cell : ConvectionCell) : ConvectionCell :=
  match cell_budget cell with
  | fz => cell  (* No energy - frozen *)
  | _ =>
      let circ_cost := circulation_cost_dynamic (cell_budget cell) in
      match sub_fin (cell_budget cell) circ_cost (cell_budget cell) with
      | (_, b') =>
          Build_ConvectionCell
            (hot_layer cell)
            (cold_layer cell)
            (circulation_rate cell)
            b'  (* Energy depleted! *)
      end
  end.

(******************************************************************************)
(* SYSTEM EVOLUTION WITH BUDGET                                              *)
(******************************************************************************)

(* Evolve thermal system - expensive operation *)
Definition evolve_thermal_system_b (sys : ThermalSystem) : ThermalSystem :=
  match system_budget sys with
  | fz => sys  (* System frozen - no budget *)
  | _ =>
      (* Update patterns - very expensive *)
      let update_layers := fold_left (fun acc layer =>
        match acc with
        | (updated_layers, sys_b) =>
            match sys_b with
            | fz => (layer :: updated_layers, fz)
            | _ =>
                (* Circulate each pattern in layer *)
                let circulate_all := fold_left (fun acc2 tp =>
                  match acc2 with
                  | (patterns, b) =>
                      let temp_sys := Build_ThermalSystem
                                        (layers sys)
                                        (cells sys)
                                        (gravity_strength sys)
                                        b
                                        (total_spur sys) in
                      match circulate_pattern_b tp temp_sys with
                      | (new_tp, b') => (new_tp :: patterns, b')
                      end
                  end
                ) (layer_patterns layer) ([], sys_b) in
                
                match circulate_all with
                | (new_patterns, b1) =>
                    let updated_layer := 
                      update_layer_temperature_b
                        (Build_ThermalLayer
                           (layer_height layer)
                           (layer_temp layer)
                           new_patterns
                           (layer_budget layer)
                           (decay_prob (convection_strength layer))) in
                    (updated_layer :: updated_layers, b1)
                end
            end
        end
      ) (layers sys) ([], system_budget sys) in
      
      match update_layers with
      | (new_layers, b_final) =>
          (* Update cells *)
          let new_cells := map step_convection_cell_b (cells sys) in
          
          (* System cools - Spuren dissipates *)
          let new_spur := match total_spur sys with
                          | fz => fz
                          | fs h => h
                          end in
          
          Build_ThermalSystem
            new_layers
            new_cells
            (gravity_strength sys)
            b_final
            new_spur
      end
  end.

(******************************************************************************)
(* CRISIS OPERATIONS - COST MORE WITH DYNAMIC PRICING!                       *)
(******************************************************************************)

(* Calculate turbulence - costs budget *)
Definition turbulence_level_b (sys : ThermalSystem) : (Fin * Budget) :=
  fold_left (fun acc cell =>
    match acc with
    | (turb, b) =>
        match b with
        | fz => (turb, fz)
        | fs b' =>
            match add_fin turb (circulation_rate cell) b' with
            | (new_turb, b'') => (new_turb, b'')
            end
        end
    end
  ) (cells sys) (fz, system_budget sys).

(* Check for thermal runaway - costs budget *)
Definition thermal_runaway_b (sys : ThermalSystem) : (bool * Budget) :=
  match turbulence_level_b sys with
  | (turb, b) => le_fin_b (fs (fs (fs fz))) turb b
  end.

(* Emergency cooling - VERY expensive with dynamic multiplier! *)
Definition emergency_cooling_b (sys : ThermalSystem) : ThermalSystem :=
  match system_budget sys with
  | fz => sys  (* Can't afford emergency cooling! *)
  | _ =>
      (* Emergency operations cost MORE - dynamic multiplier *)
      let emergency_mult := emergency_multiplier_dynamic (system_budget sys) in
      let base_circ_cost := circulation_cost_dynamic (system_budget sys) in
      match mult_fin emergency_mult base_circ_cost (system_budget sys) with
      | (emergency_cost, b1) =>
          match le_fin_b emergency_cost b1 b1 with
          | (false, _) => sys  (* Can't afford it *)
          | (true, b2) =>
              match sub_fin b2 emergency_cost b2 with
              | (_, b3) =>
                  (* Dump all Spuren - expensive! *)
                  Build_ThermalSystem
                    (map (fun layer =>
                       Build_ThermalLayer
                         (layer_height layer)
                         fz
                         (map (fun tp =>
                           Build_ThermalPattern (cold tp) fz fz)  (* Patterns exhausted *)
                           (layer_patterns layer))
                         fz  (* Layers exhausted *)
                         (fs fz, fs (fs (fs (fs fz)))))
                       (layers sys))
                    []  (* All cells dead *)
                    (gravity_strength sys)
                    b3  (* Mostly depleted *)
                    fz
              end
          end
      end
  end.

(******************************************************************************)
(* INITIALIZATION WITH BUDGET                                                *)
(******************************************************************************)

(* Create thermal gradient - costs budget *)
Definition create_thermal_gradient_b (num_layers : Fin) (b : Budget)
  : (list ThermalLayer * Budget) :=
  match num_layers, b with
  | fz, _ => ([], b)
  | fs fz, _ =>
      ([Build_ThermalLayer fz (fs (fs fz)) [] b half], b)
  | fs (fs fz), fs b' =>
      ([Build_ThermalLayer fz (fs (fs fz)) [] b' half;
        Build_ThermalLayer (fs fz) fz [] b' half], b')
  | _, _ => ([], b)  (* Can't create more layers *)
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition ThermalLayer_ext := ThermalLayer.
Definition ConvectionCell_ext := ConvectionCell.
Definition ThermalSystem_ext := ThermalSystem.
Definition evolve_thermal_system_b_ext := evolve_thermal_system_b.

(******************************************************************************)
(* PHILOSOPHICAL NOTE - Now with TRUE emergent costs                         *)
(******************************************************************************)

(* Thermal convection in void mathematics reveals thermodynamic truth:
   
   1. HEAT IS COMPUTATION - Spuren isn't separate from budget; it IS spent
      budget. Every calculation generates Spuren, every movement dissipates it.
   
   2. COSTS EMERGE FROM SCARCITY - Rising costs more when resources are scarce.
      Emergency operations become prohibitively expensive as systems exhaust.
   
   3. NO MAGIC CONSTANTS - All costs emerge from actual resource availability.
      A well-funded system operates efficiently; a starved system pays more
      for every operation.
   
   4. CRISIS AMPLIFIES NATURALLY - Emergency multipliers scale with desperation.
      The system can price itself out of its own salvation.
   
   5. DEATH IS RESOURCE EXHAUSTION - Patterns freeze not because of arbitrary
      rules but because they literally cannot afford to continue operating.
   
   This models real thermodynamics: computation generates Spuren, scarcity
   drives up operational costs, and everything tends toward the most
   resource-efficient equilibrium until Spuren exhaustion. *)

End Void_Thermal_Convection.