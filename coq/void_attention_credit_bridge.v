(******************************************************************************)
(* void_attention_credit_bridge.v                                            *)
(* BRIDGE: Maintenance economy meets learning economy                        *)
(*                                                                           *)
(* void_attention_cost.v manages trace survival (who lives, who dies).       *)
(* void_credit_propagation.v manages trace credit (who predicted well).      *)
(* Both operate on list MemoryTrace with Budget and Spuren.                    *)
(* This module connects them: maintain first, then evaluate credit.          *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_information_theory.
Require Import void_temporal_memory.
Require Import void_attention_cost.
Require Import void_credit_propagation.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Attention_Credit_Bridge.

Import Void_Temporal_Memory.
Import Void_Attention_Cost.
Import Void_Credit_Propagation.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* CONVERSION — LayerState and MaintenanceState hold the same data           *)
(******************************************************************************)

(* LayerState has layer_id where MaintenanceState has maintenance_tick.
   Both are Fin. The tick carries forward as-is. *)

Definition layer_to_maintenance (ls : LayerState) : MaintenanceState :=
  {| maintained_traces := layer_traces ls;
     maintenance_budget := layer_budget ls;
     maintenance_spur := layer_spur ls;
     maintenance_tick := layer_id ls |}.

Definition maintenance_to_layer (ms : MaintenanceState) (id : Fin) : LayerState :=
  {| layer_traces := maintained_traces ms;
     layer_budget := maintenance_budget ms;
     layer_spur := maintenance_spur ms;
     layer_id := id |}.

(******************************************************************************)
(* COMBINED STEP — maintain traces, then propagate credit                    *)
(******************************************************************************)

(* Run maintenance on a LayerState: decay traces, drop what you can't
   afford, return surviving traces with updated budget and Spuren.
   One tick per trace for counting + cost calculation. *)
Definition maintain_layer (ls : LayerState) : LayerState :=
  let ms := layer_to_maintenance ls in
  let maintained := apply_maintenance_tick ms in
  maintenance_to_layer maintained (layer_id ls).

(* Full cycle: maintain both layers, then propagate credit between them.
   Maintenance runs first — dead traces don't get evaluated for credit.
   Surviving traces get their chance at refund. *)
Definition maintain_then_credit (source target : LayerState)
                                 (links : list CreditLink)
  : CreditResult :=
  let maintained_source := maintain_layer source in
  let maintained_target := maintain_layer target in
  propagate_credits links maintained_source maintained_target.

(* Same as above but for the two-layer common case. *)
Definition maintain_then_credit_two (lower upper : LayerState)
                                     (links : list CreditLink)
  : (LayerState * LayerState) :=
  let result := maintain_then_credit lower upper links in
  (updated_source result, updated_target result).

(******************************************************************************)
(* CRISIS-AWARE CREDIT — skip credit when in maintenance crisis              *)
(******************************************************************************)

(* If a layer is in maintenance crisis, don't spend budget on credit
   evaluation — every tick matters for survival. Only propagate
   credit when both layers can afford it. *)
Definition crisis_aware_credit (source target : LayerState)
                                (links : list CreditLink)
  : CreditResult :=
  let ms_source := layer_to_maintenance source in
  let ms_target := layer_to_maintenance target in
  match maintenance_budget ms_source, maintenance_budget ms_target with
  | fz, _ =>
      (* Source dead — no credit to propagate *)
      {| updated_source := source;
         updated_target := target;
         credits_processed := fz;
         total_refunded := fz |}
  | _, fz =>
      (* Target dead — no credit to propagate *)
      {| updated_source := source;
         updated_target := target;
         credits_processed := fz;
         total_refunded := fz |}
  | fs b1, fs b2 =>
      match in_maintenance_crisis ms_source b1 with
      | (true, _) =>
          (* Source in crisis — maintain only, skip credit *)
          let maintained := maintain_layer source in
          {| updated_source := maintained;
             updated_target := target;
             credits_processed := fz;
             total_refunded := fz |}
      | (false, _) =>
          match in_maintenance_crisis ms_target b2 with
          | (true, _) =>
              (* Target in crisis — maintain only *)
              let maintained := maintain_layer target in
              {| updated_source := source;
                 updated_target := maintained;
                 credits_processed := fz;
                 total_refunded := fz |}
          | (false, _) =>
              (* Both healthy — maintain then credit *)
              maintain_then_credit source target links
          end
      end
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition layer_to_maintenance_ext := layer_to_maintenance.
Definition maintenance_to_layer_ext := maintenance_to_layer.
Definition maintain_layer_ext := maintain_layer.
Definition maintain_then_credit_ext := maintain_then_credit.
Definition crisis_aware_credit_ext := crisis_aware_credit.

End Void_Attention_Credit_Bridge.

(******************************************************************************)
(* WHY THIS BRIDGE EXISTS                                                     *)
(*                                                                            *)
(* void_attention_cost.v and void_credit_propagation.v both operate on       *)
(* lists of MemoryTrace with Budget and Spuren. Both import                    *)
(* void_temporal_memory.v. They never import each other.                     *)
(*                                                                            *)
(* Without this bridge:                                                       *)
(* - Maintenance drops traces that can't be afforded                         *)
(* - Credit evaluates traces for predictive accuracy                         *)
(* - These happen independently — a trace might get credit and then          *)
(*   immediately die from maintenance cost, or survive maintenance           *)
(*   but never get evaluated for credit                                      *)
(*                                                                            *)
(* With this bridge:                                                          *)
(* - maintain_then_credit: maintenance runs first (who survives?),           *)
(*   then credit runs on survivors (who predicted well?)                     *)
(* - crisis_aware_credit: if a layer can't afford maintenance,               *)
(*   don't waste budget on credit evaluation                                 *)
(*                                                                            *)
(* One tick per operation. No new logic. Composition of existing functions.   *)
(******************************************************************************)