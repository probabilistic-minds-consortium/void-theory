(******************************************************************************)
(* void_simulation.v - TEST SUITE FOR THE VOID BRAIN                         *)
(* Proof that the brain lives, thinks, heats up, and eventually dies         *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_sensory_transduction.
Require Import void_dual_system.
Require Import void_integrated_brain.

Module Void_Simulation.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Sensory_Transduction.
Import Void_Dual_System.
Import Void_Integrated_Brain.

(******************************************************************************)
(* SECTION 1: TEST CONFIGURATION - BUILDING LARGE BUDGETS                    *)
(******************************************************************************)

(* Base numbers *)
Definition fin_1 : Fin := fs fz.
Definition fin_2 : Fin := fs fin_1.
Definition fin_3 : Fin := fs fin_2.
Definition fin_4 : Fin := fs fin_3.
Definition fin_5 : Fin := fs fin_4.
Definition fin_6 : Fin := fs fin_5.
Definition fin_7 : Fin := fs fin_6.
Definition fin_8 : Fin := fs fin_7.
Definition fin_9 : Fin := fs fin_8.
Definition fin_10 : Fin := fs fin_9.

(* Tens *)
Definition fin_20 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_10))))))))).
Definition fin_30 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_20))))))))).
Definition fin_40 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_30))))))))).
Definition fin_50 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_40))))))))).
Definition fin_60 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_50))))))))).
Definition fin_70 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_60))))))))).
Definition fin_80 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_70))))))))).
Definition fin_90 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_80))))))))).
Definition fin_100 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_90))))))))).

(* Hundreds *)
Definition fin_110 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_100))))))))).
Definition fin_120 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_110))))))))).
Definition fin_130 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_120))))))))).
Definition fin_140 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_130))))))))).
Definition fin_150 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_140))))))))).
Definition fin_160 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_150))))))))).
Definition fin_170 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_160))))))))).
Definition fin_180 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_170))))))))).
Definition fin_190 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_180))))))))).
Definition fin_200 : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fin_190))))))))).

(* MAIN TEST BUDGET: 200 ticks *)
Definition test_budget : Budget := fin_200.

(* Fuel for recursion - needs to be large enough *)
Definition test_fuel : Fin := fin_50.

(* Sensor configuration *)
Definition max_val : Fin := fin_5.
Definition num_classes : Fin := fin_2.
Definition max_loc : Fin := fin_10.

(* Initialize the brain *)
Definition my_brain : VoidBrain := init_brain test_budget.

(******************************************************************************)
(* SECTION 2: TEST INPUTS                                                     *)
(******************************************************************************)

Definition input_bright_dark_bright : list Fin := [fin_5; fz; fin_5].
Definition input_all_dark : list Fin := [fz; fz; fz].
Definition input_gradient : list Fin := [fz; fin_2; fin_5].

Definition batch_same : list (list Fin) := 
  [input_bright_dark_bright; 
   input_bright_dark_bright; 
   input_bright_dark_bright].

Definition batch_varied : list (list Fin) :=
  [input_bright_dark_bright;
   input_all_dark;
   input_gradient].

(* Longer batch for learning test *)
Definition batch_long : list (list Fin) :=
  [input_bright_dark_bright;
   input_bright_dark_bright;
   input_bright_dark_bright;
   input_bright_dark_bright;
   input_bright_dark_bright].

(******************************************************************************)
(* SECTION 3: HELPER EXTRACTORS                                              *)
(******************************************************************************)

Definition get_output_class (result : VoidBrain * Fin * FinProb * Budget * Spuren) 
  : Fin :=
  match result with
  | (_, class, _, _, _) => class
  end.

Definition get_remaining_budget (result : VoidBrain * Fin * FinProb * Budget * Spuren) 
  : Budget :=
  match result with
  | (_, _, _, b, _) => b
  end.

Definition get_spur (result : VoidBrain * Fin * FinProb * Budget * Spuren) 
  : Spuren :=
  match result with
  | (_, _, _, _, h) => h
  end.

Definition get_confidence (result : VoidBrain * Fin * FinProb * Budget * Spuren) 
  : FinProb :=
  match result with
  | (_, _, conf, _, _) => conf
  end.

Definition get_brain (result : VoidBrain * Fin * FinProb * Budget * Spuren) 
  : VoidBrain :=
  match result with
  | (brain, _, _, _, _) => brain
  end.

(******************************************************************************)
(* SECTION 4: SCENARIO 1 - SINGLE CYCLE "HELLO WORLD"                        *)
(******************************************************************************)

Definition test_single_cycle : VoidBrain * Fin * FinProb * Budget * Spuren :=
  run_cycle my_brain input_bright_dark_bright max_val num_classes max_loc 
            test_fuel test_budget.

Definition single_output : Fin := get_output_class test_single_cycle.
Definition single_budget_after : Budget := get_remaining_budget test_single_cycle.
Definition single_spur : Spuren := get_spur test_single_cycle.
Definition single_confidence : FinProb := get_confidence test_single_cycle.
Definition single_brain_after : VoidBrain := get_brain test_single_cycle.

(******************************************************************************)
(* SECTION 5: SCENARIO 2 - BATCH LEARNING (SAME INPUT)                       *)
(******************************************************************************)

Definition test_batch_same : VoidBrain * list Fin * Budget * Spuren :=
  run_cycles my_brain batch_same max_val num_classes max_loc 
             test_fuel test_budget [].

Definition batch_outputs : list Fin :=
  match test_batch_same with
  | (_, outputs, _, _) => outputs
  end.

Definition batch_final_budget : Budget :=
  match test_batch_same with
  | (_, _, b, _) => b
  end.

Definition batch_total_spur : Spuren :=
  match test_batch_same with
  | (_, _, _, h) => h
  end.

Definition batch_final_brain : VoidBrain :=
  match test_batch_same with
  | (brain, _, _, _) => brain
  end.

(******************************************************************************)
(* SECTION 6: SCENARIO 3 - VARIED INPUT                                      *)
(******************************************************************************)

Definition test_batch_varied : VoidBrain * list Fin * Budget * Spuren :=
  run_cycles my_brain batch_varied max_val num_classes max_loc 
             test_fuel test_budget [].

Definition varied_outputs : list Fin :=
  match test_batch_varied with
  | (_, outputs, _, _) => outputs
  end.

Definition varied_spur : Spuren :=
  match test_batch_varied with
  | (_, _, _, h) => h
  end.

Definition varied_final_budget : Budget :=
  match test_batch_varied with
  | (_, _, b, _) => b
  end.

(******************************************************************************)
(* SECTION 7: SCENARIO 4 - LONG BATCH (5 REPEATS)                            *)
(******************************************************************************)

Definition test_batch_long : VoidBrain * list Fin * Budget * Spuren :=
  run_cycles my_brain batch_long max_val num_classes max_loc 
             test_fuel test_budget [].

Definition long_outputs : list Fin :=
  match test_batch_long with
  | (_, outputs, _, _) => outputs
  end.

Definition long_final_budget : Budget :=
  match test_batch_long with
  | (_, _, b, _) => b
  end.

Definition long_total_spur : Spuren :=
  match test_batch_long with
  | (_, _, _, h) => h
  end.

Definition long_final_brain : VoidBrain :=
  match test_batch_long with
  | (brain, _, _, _) => brain
  end.

(******************************************************************************)
(* SECTION 8: DIAGNOSTIC CHECKS                                              *)
(******************************************************************************)

Definition spur_after_single : Fin := brain_spur single_brain_after.
Definition traces_after_single : Fin := memory_trace_count single_brain_after.
Definition orbits_after_single : Fin := orbit_count single_brain_after.
Definition exhausted_after_single : bool := is_exhausted single_brain_after.

Definition spur_after_batch : Fin := brain_spur batch_final_brain.
Definition traces_after_batch : Fin := memory_trace_count batch_final_brain.
Definition exhausted_after_batch : bool := is_exhausted batch_final_brain.

Definition spur_after_long : Fin := brain_spur long_final_brain.
Definition traces_after_long : Fin := memory_trace_count long_final_brain.
Definition orbits_after_long : Fin := orbit_count long_final_brain.

(******************************************************************************)
(* SECTION 9: STRESS TEST - RUN UNTIL EXHAUSTION                             *)
(******************************************************************************)

Definition tiny_budget : Budget := fin_20.
Definition exhaustion_brain : VoidBrain := init_brain tiny_budget.

Definition many_inputs : list (list Fin) :=
  [input_bright_dark_bright;
   input_all_dark;
   input_gradient;
   input_bright_dark_bright;
   input_all_dark].

Definition test_exhaustion : VoidBrain * list Fin * Budget * Spuren :=
  run_cycles exhaustion_brain many_inputs max_val num_classes max_loc 
             test_fuel tiny_budget [].

Definition exhaustion_final_brain : VoidBrain :=
  match test_exhaustion with
  | (brain, _, _, _) => brain
  end.

Definition exhaustion_outputs : list Fin :=
  match test_exhaustion with
  | (_, outputs, _, _) => outputs
  end.

Definition exhaustion_remaining : Budget :=
  match test_exhaustion with
  | (_, _, b, _) => b
  end.

Definition did_exhaust : bool := is_exhausted exhaustion_final_brain.

(******************************************************************************)
(* SECTION 10: VERIFICATION LEMMAS                                           *)
(******************************************************************************)

Lemma fresh_brain_not_exhausted : 
  is_exhausted (init_brain (fs fz)) = false.
Proof.
  simpl. reflexivity.
Qed.

Lemma zero_budget_exhausted :
  is_exhausted (init_brain fz) = true.
Proof.
  simpl. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 11: LIVE COMPUTATION - SEE THE BRAIN THINK!                       *)
(******************************************************************************)

(* === SINGLE CYCLE === *)
Eval compute in single_output.
Eval compute in single_spur.
Eval compute in single_budget_after.
Eval compute in single_confidence.

(* === BATCH (3x same) === *)
Eval compute in batch_outputs.
Eval compute in batch_total_spur.
Eval compute in batch_final_budget.

(* === VARIED INPUTS === *)
Eval compute in varied_outputs.
Eval compute in varied_spur.
Eval compute in varied_final_budget.

(* === LONG BATCH (5x same) === *)
Eval compute in long_outputs.
Eval compute in long_total_spur.
Eval compute in long_final_budget.

(* === EXHAUSTION TEST === *)
Eval compute in exhaustion_outputs.
Eval compute in exhaustion_remaining.
Eval compute in did_exhaust.

(* === DIAGNOSTICS === *)
Eval compute in spur_after_single.
Eval compute in traces_after_single.
Eval compute in orbits_after_single.

Eval compute in traces_after_long.
Eval compute in orbits_after_long.

Definition simulation_complete : bool := true.

End Void_Simulation.