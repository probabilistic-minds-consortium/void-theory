(******************************************************************************)
(* void_budget_flow.v - BUDGET-AWARE ECOLOGICAL DYNAMICS                     *)
(* Patterns seek niches, not just resources                                  *)
(* CLEANED: Uniform costs, no special values                                  *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Budget_Flow.

Import Void_Pattern.
Import Void_Arithmetic.
Import Void_Probability_Minimal.

(******************************************************************************)
(* FUNDAMENTAL CONSTANT                                                       *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* HELPER FUNCTIONS                                                           *)
(******************************************************************************)

(* Distance between two Fin values - costs one tick *)
Definition dist_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      match le_fin_b n m b' with
      | (true, b1) => sub_fin m n b1
      | (false, b1) => sub_fin n m b1
      end
  end.

(* Helper to create sequence *)
Fixpoint seq_fin (n : Fin) : list Fin :=
  match n with
  | fz => []
  | fs n' => fz :: map fs (seq_fin n')
  end.

(* Length - costs one tick per element *)
Fixpoint length_fin_with_budget {A : Type} (l : list A) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: t, fs b' =>
      match length_fin_with_budget t b' with
      | (len, b'') => (fs len, b'')
      end
  end.

(* Simple modulo - costs one tick *)
Definition modulo_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      match m with
      | fz => (fz, b')
      | _ => 
          match le_fin_b n m b' with
          | (true, b1) => (n, b1)
          | (false, b1) => (fz, b1)
          end
      end
  end.

(* Boolean helper *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with true => b2 | false => false end.

(******************************************************************************)
(* PATTERN ECOLOGY WITH BUDGET                                                *)
(******************************************************************************)

(* Budget-aware pattern type *)
Record BudgetedPattern := {
  pattern : Pattern;
  movement_budget : Budget
}.

(* Budget-aware layer *)
Record BudgetedLayer := {
  layer : Layer;
  flow_budget : Budget
}.

(* Pattern preference - costs one tick *)
Definition pattern_preference_b (p : Pattern) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      (* Simple preference based on strength *)
      match fst (strength p) with
      | fz => (fz, b')
      | fs fz => (fs fz, b')
      | fs (fs _) => (fs (fs fz), b')
      end
  end.

(* Extract budget info - costs one tick per neuron *)
Fixpoint neuron_budgets_b (neurons : list Neuron) (b : Budget) 
  : (list (Fin * Budget) * Budget) :=
  match neurons, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | n :: rest, fs b' =>
      let neuron_budget := match refractory n with
                          | fz => fs (fs fz)  (* Active: has budget *)
                          | _ => fz            (* Refractory: no budget *)
                          end in
      match neuron_budgets_b rest b' with
      | (budgets, b'') => ((neuron_id n, neuron_budget) :: budgets, b'')
      end
  end.

(* Find complementary location - costs one tick *)
Definition find_complementary_location_b (bp : BudgetedPattern) 
                                        (budgets : list (Fin * Budget))
  : (option Fin * Budget) :=
  match movement_budget bp with
  | fz => (None, fz)
  | fs b' =>
      match pattern_preference_b (pattern bp) b' with
      | (pref, b1) =>
          match budgets with
          | [] => (None, b1)
          | (loc, _) :: _ => (Some loc, b1)  (* Simple: take first available *)
          end
      end
  end.

(* Ecological move - costs one tick *)
Definition ecological_move_b (bp : BudgetedPattern) (bl : BudgetedLayer) 
  : (BudgetedPattern * BudgetedLayer) :=
  match flow_budget bl with
  | fz => (bp, bl)
  | fs b' =>
      match neuron_budgets_b (neurons (layer bl)) b' with
      | (budgets, b1) =>
          match find_complementary_location_b 
                  {| pattern := pattern bp; movement_budget := b1 |} budgets with
          | (None, b2) => 
              ({| pattern := pattern bp; movement_budget := b2 |},
               {| layer := layer bl; flow_budget := b2 |})
          | (Some target, b2) =>
              (* Move pattern *)
              match decay_with_budget (strength (pattern bp)) b2 with
              | (new_strength, b3) =>
                  ({| pattern := {| location := target;
                                   strength := new_strength |};
                      movement_budget := b3 |},
                   {| layer := layer bl; flow_budget := b3 |})
              end
          end
      end
  end.

(* Cooperative competition - costs one tick *)
Fixpoint cooperative_competition_b (patterns : list BudgetedPattern) 
                                   (available : Budget) 
                                   (org_budget : Budget)
  : list (BudgetedPattern * Budget) :=
  match patterns, org_budget with
  | [], _ => []
  | _, fz => []
  | [p], _ => [(p, available)]
  | p :: rest, fs b' =>
      (* Simple equal sharing *)
      let share := match patterns with
                   | [] => available
                   | _ => operation_cost  (* Each gets one tick *)
                   end in
      (p, share) :: cooperative_competition_b rest 
                      (match available with fz => fz | fs a => a end) b'
  end.

(* Mutual aid - costs one tick *)
Definition mutual_aid_b (n1 n2 : Neuron) (b : Budget) 
  : ((Neuron * Neuron) * Budget) :=
  match b with
  | fz => ((n1, n2), fz)
  | fs b' =>
      (* Simple: if one is refractory, help it *)
      match refractory n1, refractory n2 with
      | fz, fs _ => 
          (* n2 needs help *)
          ((n1, {| neuron_id := neuron_id n2;
                   threshold := threshold n2;
                   accumulated := accumulated n2;
                   refractory := fz;  (* Clear refractory *)
                   maintained_patterns := maintained_patterns n2;
                   neuron_budget := neuron_budget n2;
                   neuron_spur := neuron_spur n2 |}), b')  (* Preserve Spuren *)
      | fs _, fz =>
          (* n1 needs help *)
          (({| neuron_id := neuron_id n1;
               threshold := threshold n1;
               accumulated := accumulated n1;
               refractory := fz;
               maintained_patterns := maintained_patterns n1;
               neuron_budget := neuron_budget n1;
               neuron_spur := neuron_spur n1 |}, n2), b')  (* Preserve Spuren *)
      | _, _ => ((n1, n2), b')  (* Both same state *)
      end
  end.

(* Adapt neuron - costs one tick *)
Definition adapt_neuron_to_patterns_b (n : Neuron) 
                                     (recent_patterns : list Pattern) 
                                     (b : Budget)
  : (Neuron * Budget) :=
  match b with
  | fz => (n, fz)
  | fs b' =>
      match recent_patterns with
      | [] => (n, b')
      | p :: _ =>
          (* Simple: adapt threshold to first pattern *)
          ({| neuron_id := neuron_id n;
              threshold := strength p;
              accumulated := accumulated n;
              refractory := refractory n;
              maintained_patterns := maintained_patterns n;
              neuron_budget := neuron_budget n;
              neuron_spur := neuron_spur n |}, b')  (* Preserve Spuren *)
      end
  end.

(* Pattern alliance - costs one tick *)
Definition pattern_alliance_b (bp1 bp2 : BudgetedPattern) 
  : (option BudgetedPattern * Budget) :=
  match movement_budget bp1 with
  | fz => (None, fz)
  | fs b' =>
      match fin_eq_b (location (pattern bp1)) (location (pattern bp2)) b' with
      | (false, b1) => (None, b1)
      | (true, b1) =>
          (* Merge patterns *)
          match add_prob_b (strength (pattern bp1)) 
                          (strength (pattern bp2)) b1 with
          | (sum_strength, b2) =>
              (Some {| pattern := {| location := location (pattern bp1);
                                    strength := sum_strength |};
                      movement_budget := b2 |}, b2)
          end
      end
  end.

(* Diversity bonus - costs one tick *)
Definition diversity_bonus_b (bl : BudgetedLayer) (gift : Budget) 
  : BudgetedLayer :=
  match flow_budget bl with
  | fz => bl
  | fs b' =>
      let layer_neurons := neurons (layer bl) in
      match layer_neurons with
      | [] => bl
      | n :: rest =>
          (* Simple: give to first neuron *)
          let updated := {| neuron_id := neuron_id n;
                           threshold := threshold n;
                           accumulated := accumulated n;
                           refractory := fz;  (* Clear refractory *)
                           maintained_patterns := maintained_patterns n;
                           neuron_budget := neuron_budget n;
                           neuron_spur := neuron_spur n |} in  (* Preserve Spuren *)
          {| layer := {| layer_id := layer_id (layer bl);
                        neurons := updated :: rest;
                        input_patterns := input_patterns (layer bl);
                        output_patterns := output_patterns (layer bl);
                        layer_budget := layer_budget (layer bl) |};
             flow_budget := b' |}
      end
  end.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Budget Flow embodies ecological thinking in void mathematics:
   
   1. ONE TICK PER INTERACTION - Finding niches, forming alliances,
      mutual aid - all cost exactly one tick. No operation is "harder."
   
   2. PATTERNS SEEK BALANCE - Not through complex calculations but
      simple preferences. Complexity emerges from iteration.
   
   3. COOPERATION IS SIMPLE - Patterns share equally, help uniformly.
      No complex negotiations, just one tick per interaction.
   
   4. NO MAGIC THRESHOLDS - Patterns cooperate or compete based on
      actual state, not arbitrary cutoffs.
   
   5. DIVERSITY THROUGH SIMPLICITY - Random selection isn't complex
      calculation but simple first-available or round-robin.
   
   This creates a dynamic ecology where every interaction costs the
   same, and complexity emerges from many simple, uniform exchanges
   rather than from complicated rules or special numbers. *)

End Void_Budget_Flow.