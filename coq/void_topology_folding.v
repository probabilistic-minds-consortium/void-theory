(******************************************************************************)
(* void_topology_folding.v - BUDGET-AWARE DYNAMIC TOPOLOGY                    *)
(* Space itself can fold, but folding costs finite resources                 *)
(* CLEANED: All operations cost one tick, no magic numbers                   *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import void_information_theory.
Require Import void_distinguishability.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Topology_Folding.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.
Import Void_Information_Theory.
Import Void_Distinguishability.

(******************************************************************************)
(* FUNDAMENTAL CONSTANT - One tick of time                                   *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.  (* The only arbitrary constant *)

(******************************************************************************)
(* CORE TYPES WITH BUDGET AWARENESS                                          *)
(******************************************************************************)

(* A fold bridge connects two normally distant locations *)
Record FoldBridge := {
  end1 : Fin;
  end2 : Fin;
  stability : FinProb;
  maintenance_cost : Fin
}.

(* Network topology with foldable space *)
Record NetworkTopology := {
  size : Fin;
  bridges : list FoldBridge;
  fold_energy : Budget;           (* Energy available for folding *)
  ambient_curvature : FinProb;    (* Background space distortion *)
  topology_budget : Budget        (* Separate budget for operations *)
}.

(******************************************************************************)
(* READ OPERATIONS - Access existing topology structure                       *)
(******************************************************************************)

(* Read bridge endpoints - FREE *)
Definition read_bridge_endpoints (br : FoldBridge) : (Fin * Fin) :=
  (end1 br, end2 br).

Instance bridge_endpoints_read : ReadOperation FoldBridge (Fin * Fin) := {
  read_op := read_bridge_endpoints
}.

(* Read bridge stability - FREE *)
Definition read_bridge_stability (br : FoldBridge) : FinProb :=
  stability br.

Instance bridge_stability_read : ReadOperation FoldBridge FinProb := {
  read_op := read_bridge_stability
}.

(* Check if bridge exists - FREE *)
Definition read_bridge_exists (br : FoldBridge) : bool :=
  match stability br with
  | (fz, _) => false
  | _ => true
  end.

Instance bridge_exists_read : ReadOperation FoldBridge bool := {
  read_op := read_bridge_exists
}.

(* Count bridges - FREE *)
Fixpoint read_bridge_count (bridges : list FoldBridge) : Fin :=
  match bridges with
  | [] => fz
  | _ :: rest => fs (read_bridge_count rest)
  end.

Instance bridge_count_read : ReadOperation (list FoldBridge) Fin := {
  read_op := read_bridge_count
}.

(* Read network curvature - FREE *)
Definition read_curvature (net : NetworkTopology) : FinProb :=
  ambient_curvature net.

Instance curvature_read : ReadOperation NetworkTopology FinProb := {
  read_op := read_curvature
}.

(******************************************************************************)
(* DYNAMIC COST FUNCTIONS - Costs emerge from context                        *)
(******************************************************************************)

(* Fold cost depends on current curvature - READ operation *)
Definition fold_cost_dynamic (net : NetworkTopology) : Fin :=
  (* Always one tick - high curvature affects success rate, not cost *)
  operation_cost.

Instance fold_cost_read : ReadOperation NetworkTopology Fin := {
  read_op := fold_cost_dynamic
}.

(* Bridge maintenance depends on stability - READ operation *)
Definition maintenance_cost_dynamic (br : FoldBridge) : Fin :=
  (* Always one tick - weak bridges fail more often, not cost more *)
  operation_cost.

Instance maintenance_cost_read : ReadOperation FoldBridge Fin := {
  read_op := maintenance_cost_dynamic
}.

(* Wormhole cost depends on desperation - READ operation *)
Definition wormhole_cost_dynamic (net_budget : Budget) : Fin :=
  (* Always one tick - desperation affects success probability *)
  operation_cost.

Instance wormhole_cost_read : ReadOperation Budget Fin := {
  read_op := wormhole_cost_dynamic
}.

(* Stability threshold emerges from context - READ operation *)
Definition stability_threshold_dynamic (net : NetworkTopology) : FinProb :=
  (* Threshold based on ambient curvature *)
  match ambient_curvature net with
  | (n, d) =>
      match n with
      | fz => (fs fz, fs (fs (fs fz)))      (* Low curvature: 1/3 threshold *)
      | _ => (fs fz, fs (fs fz))            (* High curvature: 1/2 threshold *)
      end
  end.

Instance stability_threshold_read : ReadOperation NetworkTopology FinProb := {
  read_op := stability_threshold_dynamic
}.

(******************************************************************************)
(* WRITE OPERATIONS - Change topology state                                  *)
(******************************************************************************)

(* Fold space to create bridge - WRITE operation *)
Definition write_fold_space (net : NetworkTopology) (loc1 loc2 : Fin) (b : Budget)
  : (NetworkTopology * Budget * Spuren) :=
  match b with
  | fz => (net, fz, fz)
  | fs b' =>
      match fold_energy net with
      | fz => (net, b', fs fz)  (* No fold energy *)
      | fs fe' =>
          (* Create new bridge *)
          let new_bridge := {| end1 := loc1;
                              end2 := loc2;
                              stability := (fs fz, fs (fs fz));  (* Initial 1/2 stability *)
                              maintenance_cost := operation_cost |} in
          (* Increase curvature *)
          let new_curvature := 
            match ambient_curvature net with
            | (n, d) => 
                match add_fin n (fs fz) b' with
                | (new_n, b'') => ((new_n, d), b'')
                end
            end in
          match new_curvature with
          | (new_curv, b'') =>
              ({| size := size net;
                  bridges := new_bridge :: bridges net;
                  fold_energy := fe';
                  ambient_curvature := new_curv;
                  topology_budget := topology_budget net |}, b'', fs fz)
          end
      end
  end.

Instance fold_space_write : WriteOperation (NetworkTopology * Fin * Fin) NetworkTopology := {
  write_op := fun '(net, loc1, loc2) => write_fold_space net loc1 loc2
}.

(* Check if locations are bridged - WRITE operation (searches bridges) *)
Fixpoint write_check_bridged (loc1 loc2 : Fin) (bridges : list FoldBridge) (b : Budget)
  : (bool * Budget * Spuren) :=
  match bridges, b with
  | [], _ => (false, b, fz)
  | _, fz => (false, fz, fz)
  | br :: rest, fs b' =>
      match fin_eq_b (end1 br) loc1 b' with
      | (true, b1) =>
          match fin_eq_b (end2 br) loc2 b1 with
          | (true, b2) => (true, b2, fs fz)
          | (false, b2) =>
              match write_check_bridged loc1 loc2 rest b2 with
              | (result, b3, h) => (result, b3, fs h)
              end
          end
      | (false, b1) =>
          match write_check_bridged loc1 loc2 rest b1 with
          | (result, b2, h) => (result, b2, fs h)
          end
      end
  end.

Instance check_bridged_write : WriteOperation (Fin * Fin * list FoldBridge) bool := {
  write_op := fun '(loc1, loc2, bridges) => write_check_bridged loc1 loc2 bridges
}.

(* Jump through bridge - WRITE operation *)
Definition write_bridge_jump (p : Pattern) (br : FoldBridge) (b : Budget)
  : (Pattern * Budget * Spuren) :=
  match b with
  | fz => (p, fz, fz)
  | fs b' =>
      (* Check if at bridge endpoint *)
      match fin_eq_b (location p) (end1 br) b' with
      | (true, b1) =>
          (* Jump to other end *)
          ({| location := end2 br;
              strength := strength p |}, b1, fs fz)
      | (false, b1) =>
          match fin_eq_b (location p) (end2 br) b1 with
          | (true, b2) =>
              (* Jump to other end *)
              ({| location := end1 br;
                  strength := strength p |}, b2, fs fz)
          | (false, b2) =>
              (* Not at bridge - no jump *)
              (p, b2, fs fz)
          end
      end
  end.

Instance bridge_jump_write : WriteOperation (Pattern * FoldBridge) Pattern := {
  write_op := fun '(p, br) => write_bridge_jump p br
}.

(* Maintain bridges - WRITE operation *)
Definition write_maintain_bridges (net : NetworkTopology) (b : Budget)
  : (NetworkTopology * Budget * Spuren) :=
  match b with
  | fz => (net, fz, fz)
  | fs b' =>
      (* Decay all bridge stabilities *)
      let maintained := fold_left (fun acc br =>
        match acc with
        | (bridges, b_acc, h_acc) =>
            match b_acc with
            | fz => (bridges, fz, h_acc)
            | _ =>
                match decay_with_budget (stability br) b_acc with
                | (new_stability, b'') =>
                    if read_bridge_exists 
                       {| end1 := end1 br;
                          end2 := end2 br;
                          stability := new_stability;
                          maintenance_cost := maintenance_cost br |} then
                      ({| end1 := end1 br;
                          end2 := end2 br;
                          stability := new_stability;
                          maintenance_cost := maintenance_cost br |} :: bridges,
                       b'', fs h_acc)
                    else
                      (bridges, b'', fs h_acc)  (* Bridge collapsed *)
                end
            end
        end
      ) (bridges net) ([], b', fz) in
      match maintained with
      | (new_bridges, b'', h) =>
          ({| size := size net;
              bridges := rev new_bridges;
              fold_energy := fold_energy net;
              ambient_curvature := ambient_curvature net;
              topology_budget := b'' |}, b'', h)
      end
  end.

Instance maintain_bridges_write : WriteOperation NetworkTopology NetworkTopology := {
  write_op := write_maintain_bridges
}.

(* Create wormhole - desperate measure - WRITE operation *)
Definition write_create_wormhole (net : NetworkTopology) (loc1 loc2 : Fin) (b : Budget)
  : (NetworkTopology * Budget * Spuren) :=
  match b with
  | fz => (net, fz, fz)
  | fs b' =>
      (* Wormhole drastically increases curvature *)
      let critical_curv := (fs (fs fz), fs (fs (fs fz))) in  (* 2/3 *)
      (* Create unstable bridge *)
      let wormhole := {| end1 := loc1;
                        end2 := loc2;
                        stability := (fs fz, fs (fs (fs (fs fz))));  (* 1/4 - very unstable *)
                        maintenance_cost := operation_cost |} in
      ({| size := size net;
          bridges := wormhole :: bridges net;
          fold_energy := fz;  (* Exhausts fold energy *)
          ambient_curvature := critical_curv;
          topology_budget := topology_budget net |}, b', fs fz)
  end.

Instance wormhole_write : WriteOperation (NetworkTopology * Fin * Fin) NetworkTopology := {
  write_op := fun '(net, loc1, loc2) => write_create_wormhole net loc1 loc2
}.

(* Unfold space - reduce curvature - WRITE operation *)
Definition write_unfold_space (net : NetworkTopology) (b : Budget)
  : (NetworkTopology * Budget * Spuren) :=
  match b with
  | fz => (net, fz, fz)
  | fs b' =>
      (* Remove weakest bridge and reduce curvature *)
      match bridges net with
      | [] => (net, b', fs fz)
      | br :: rest =>
          (* Reduce curvature *)
          let new_curvature :=
            match ambient_curvature net with
            | (fs n, d) => (n, d)  (* Reduce numerator *)
            | other => other
            end in
          ({| size := size net;
              bridges := rest;  (* Remove first bridge *)
              fold_energy := fs (fold_energy net);  (* Recover some energy *)
              ambient_curvature := new_curvature;
              topology_budget := topology_budget net |}, b', fs fz)
      end
  end.

Instance unfold_space_write : WriteOperation NetworkTopology NetworkTopology := {
  write_op := write_unfold_space
}.

(* Check if space is critical - WRITE operation (computes threshold) *)
Definition write_check_critical (net : NetworkTopology) (b : Budget)
  : (bool * Budget * Spuren) :=
  match b with
  | fz => (false, fz, fz)
  | fs b' =>
      (* Critical if curvature exceeds threshold *)
      let threshold := stability_threshold_dynamic net in
      match le_fin_b (fst threshold) (fst (ambient_curvature net)) b' with
      | (critical, b'') => (critical, b'', fs fz)
      end
  end.

Instance check_critical_write : WriteOperation NetworkTopology bool := {
  write_op := write_check_critical
}.

(******************************************************************************)
(* HELPER FUNCTIONS                                                          *)
(******************************************************************************)

Definition rev {A : Type} := @List.rev A.

(******************************************************************************)
(* COMPOSITE OPERATIONS                                                       *)
(******************************************************************************)

(* Emergency unfold if critical - combines check and unfold *)
Definition emergency_unfold (net : NetworkTopology) (b : Budget)
  : (NetworkTopology * Budget) :=
  match write_check_critical net b with
  | (true, b', h1) =>
      (* Critical - must unfold *)
      match write_unfold_space net b' with
      | (net', b'', h2) => (net', b'')
      end
  | (false, b', h1) => (net, b')
  end.

(******************************************************************************)
(* OBSERVER IN TOPOLOGY                                                       *)
(* The observer is not external to space — they are IN it.                    *)
(* Position, trajectory, and accumulated topological Spuren.                    *)
(******************************************************************************)

(* An observer situated within a topology *)
Record TopologicalObserver := {
  topo_observer : ObserverWithBudget;
  topo_position : Fin;              (* Current location in network *)
  topo_trajectory : list Fin;       (* History of positions visited *)
  topo_spur : Spuren                  (* Accumulated topological Spuren *)
}.

(* Place an observer at a position — the birth of situated cognition *)
Definition place_observer (obs : ObserverWithBudget) (pos : Fin)
  : TopologicalObserver :=
  {| topo_observer := obs;
     topo_position := pos;
     topo_trajectory := [pos];
     topo_spur := fz |}.

(* Read observer's position - FREE (it's their own body) *)
Definition read_topo_position (tobs : TopologicalObserver) : Fin :=
  topo_position tobs.

(* Read observer's remaining budget - FREE *)
Definition read_topo_budget (tobs : TopologicalObserver) : Budget :=
  obs_budget (topo_observer tobs).

(* Consume one tick from a topological observer *)
Definition topo_tick (tobs : TopologicalObserver) : TopologicalObserver :=
  match obs_budget (topo_observer tobs) with
  | fz => tobs
  | fs b' =>
      {| topo_observer := {| observer := observer (topo_observer tobs);
                             obs_budget := b' |};
         topo_position := topo_position tobs;
         topo_trajectory := topo_trajectory tobs;
         topo_spur := fs (topo_spur tobs) |}
  end.

(******************************************************************************)
(* DDF FORWARD: OBSERVATION CHANGES TOPOLOGY                                  *)
(* You cannot look at a bridge without disturbing it.                         *)
(* You cannot scan space without distorting it.                               *)
(* The map is never the territory — because making the map changes            *)
(* the territory.                                                             *)
(******************************************************************************)

(* Observe a bridge — costs one tick, decays stability.
   The observer cannot passively inspect infrastructure.
   Every measurement is an intervention. *)
Definition observe_bridge (tobs : TopologicalObserver) (br : FoldBridge)
  : (FoldBridge * TopologicalObserver) :=
  match obs_budget (topo_observer tobs) with
  | fz => (br, tobs)  (* No budget — frozen, bridge untouched *)
  | fs b' =>
      (* DDF forward: looking at a bridge weakens it *)
      let observed_stability :=
        match stability br with
        | (fs (fs n), d) => (fs n, d)   (* Decay by one from observation *)
        | other => other                 (* Already at minimum — observation
                                            cannot destroy what is already fragile *)
        end in
      let observed_br :=
        {| end1 := end1 br;
           end2 := end2 br;
           stability := observed_stability;
           maintenance_cost := maintenance_cost br |} in
      let new_obs :=
        {| observer := observer (topo_observer tobs);
           obs_budget := b' |} in
      (observed_br,
       {| topo_observer := new_obs;
          topo_position := topo_position tobs;
          topo_trajectory := topo_trajectory tobs;
          topo_spur := fs (topo_spur tobs) |})
  end.

(* Scan local topology — costs one tick per bridge examined.
   Returns the number of bridges visible from current position.
   Each bridge examined decays slightly. *)
Fixpoint scan_local_topology (tobs : TopologicalObserver)
                             (brs : list FoldBridge)
  : (list FoldBridge * Fin * TopologicalObserver) :=
  match brs with
  | [] => ([], fz, tobs)
  | br :: rest =>
      match obs_budget (topo_observer tobs) with
      | fz => (br :: rest, fz, tobs)  (* Out of budget — stop scanning *)
      | _ =>
          (* Check if bridge touches observer's position *)
          match observe_bridge tobs br with
          | (observed_br, tobs') =>
              let touches :=
                match fin_eq_b (end1 br) (topo_position tobs)
                               (obs_budget (topo_observer tobs')) with
                | (true, _) => true
                | (false, _) =>
                    match fin_eq_b (end2 br) (topo_position tobs)
                                   (obs_budget (topo_observer tobs')) with
                    | (true, _) => true
                    | (false, _) => false
                    end
                end in
              match scan_local_topology tobs' rest with
              | (rest_brs, count, tobs'') =>
                  if touches then
                    (observed_br :: rest_brs, fs count, tobs'')
                  else
                    (observed_br :: rest_brs, count, tobs'')
              end
          end
      end
  end.

(******************************************************************************)
(* DDF BACKWARD: TOPOLOGY CHANGES OBSERVER                                    *)
(* Space is not passive substrate. Curved space taxes the observer.            *)
(* Unstable bridges inject uncertainty. The environment bites back.            *)
(******************************************************************************)

(* Curvature tax — existing in curved space costs extra budget.
   Flat space is free. Curved space drains you just by being there.
   This is the topological analogue of gravitational time dilation:
   the more curved the space, the more it costs to simply exist in it. *)
Definition curvature_tax (tobs : TopologicalObserver) (net : NetworkTopology)
  : TopologicalObserver :=
  match fst (ambient_curvature net) with
  | fz => tobs   (* Flat space — no tax *)
  | fs fz => tobs  (* Mild curvature — tolerable *)
  | fs (fs _) =>
      (* High curvature — costs one tick to endure *)
      topo_tick tobs
  end.

(* Bridge uncertainty injection — jumping through an unstable bridge
   injects extra Spuren into the observer. The passage leaves a mark.
   Stable bridges are clean passages. Unstable ones scar. *)
Definition bridge_uncertainty (tobs : TopologicalObserver) (br : FoldBridge)
  : TopologicalObserver :=
  match stability br with
  | (fs (fs _), _) => tobs    (* Stable — clean passage *)
  | (fs fz, _) =>
      (* Marginal — one unit of extra Spuren *)
      {| topo_observer := topo_observer tobs;
         topo_position := topo_position tobs;
         topo_trajectory := topo_trajectory tobs;
         topo_spur := fs (topo_spur tobs) |}
  | (fz, _) =>
      (* Collapsing — two units of extra Spuren *)
      {| topo_observer := topo_observer tobs;
         topo_position := topo_position tobs;
         topo_trajectory := topo_trajectory tobs;
         topo_spur := fs (fs (topo_spur tobs)) |}
  end.

(******************************************************************************)
(* OBSERVER-DRIVEN NAVIGATION                                                 *)
(* Movement through topology IS observation. Every step is a DDF event.       *)
(* The observer changes the bridge, the bridge changes the observer.          *)
(* There is no innocent passage.                                              *)
(******************************************************************************)

(* Observer jumps through a bridge — full DDF both directions.
   1. Check if at endpoint (costs tick)
   2. Jump (changes position and trajectory)
   3. DDF forward: bridge loses stability from use
   4. DDF backward: unstable bridge injects uncertainty *)
Definition observer_bridge_jump (tobs : TopologicalObserver) (br : FoldBridge)
  : (TopologicalObserver * FoldBridge) :=
  match obs_budget (topo_observer tobs) with
  | fz => (tobs, br)  (* Frozen — cannot move *)
  | fs b' =>
      (* Check if at end1 *)
      match fin_eq_b (topo_position tobs) (end1 br) b' with
      | (true, b1) =>
          (* Jump to end2 *)
          let jumped :=
            {| topo_observer := {| observer := observer (topo_observer tobs);
                                   obs_budget := b1 |};
               topo_position := end2 br;
               topo_trajectory := end2 br :: topo_trajectory tobs;
               topo_spur := fs (topo_spur tobs) |} in
          (* DDF forward: bridge decays from use *)
          let used_br :=
            {| end1 := end1 br;
               end2 := end2 br;
               stability := match stability br with
                            | (fs n, d) => (n, d)  (* Decay *)
                            | other => other
                            end;
               maintenance_cost := maintenance_cost br |} in
          (* DDF backward: bridge affects observer *)
          (bridge_uncertainty jumped used_br, used_br)
      | (false, b1) =>
          (* Check if at end2 *)
          match fin_eq_b (topo_position tobs) (end2 br) b1 with
          | (true, b2) =>
              (* Jump to end1 *)
              let jumped :=
                {| topo_observer := {| observer := observer (topo_observer tobs);
                                       obs_budget := b2 |};
                   topo_position := end1 br;
                   topo_trajectory := end1 br :: topo_trajectory tobs;
                   topo_spur := fs (topo_spur tobs) |} in
              let used_br :=
                {| end1 := end1 br;
                   end2 := end2 br;
                   stability := match stability br with
                                | (fs n, d) => (n, d)
                                | other => other
                                end;
                   maintenance_cost := maintenance_cost br |} in
              (bridge_uncertainty jumped used_br, used_br)
          | (false, b2) =>
              (* Not at bridge — still costs the check *)
              ({| topo_observer := {| observer := observer (topo_observer tobs);
                                      obs_budget := b2 |};
                  topo_position := topo_position tobs;
                  topo_trajectory := topo_trajectory tobs;
                  topo_spur := fs (topo_spur tobs) |}, br)
          end
      end
  end.

(* Observer folds space — creates bridge from current position to target.
   DDF both directions:
   - Forward: topology gains a bridge, curvature increases
   - Backward: observer pays budget + extra Spuren from folding effort
   Folding is the most violent topological act. *)
Definition observer_fold_space (tobs : TopologicalObserver)
                               (net : NetworkTopology) (target : Fin)
  : (TopologicalObserver * NetworkTopology) :=
  match obs_budget (topo_observer tobs) with
  | fz => (tobs, net)  (* Cannot fold — frozen *)
  | fs b' =>
      match fold_energy net with
      | fz => (tobs, net)  (* No fold energy — space resists *)
      | fs fe' =>
          (* Create bridge from here to there *)
          let new_bridge :=
            {| end1 := topo_position tobs;
               end2 := target;
               stability := (fs fz, fs (fs fz));  (* 1/2 — newborn bridges are fragile *)
               maintenance_cost := operation_cost |} in
          (* Increase curvature *)
          match add_fin (fst (ambient_curvature net)) (fs fz) b' with
          | (new_n, b'') =>
              let new_net :=
                {| size := size net;
                   bridges := new_bridge :: bridges net;
                   fold_energy := fe';
                   ambient_curvature := (new_n, snd (ambient_curvature net));
                   topology_budget := topology_budget net |} in
              (* Observer pays: budget consumed + double Spuren from effort *)
              let folded_tobs :=
                {| topo_observer := {| observer := observer (topo_observer tobs);
                                       obs_budget := b'' |};
                   topo_position := topo_position tobs;
                   topo_trajectory := topo_trajectory tobs;
                   topo_spur := fs (fs (topo_spur tobs)) |} in
              (* DDF backward: curved space taxes the folder *)
              (curvature_tax folded_tobs new_net, new_net)
          end
      end
  end.

(* Observer creates wormhole — desperate topological act.
   Exhausts all fold energy. Creates maximally unstable bridge.
   The observer pays dearly: triple Spuren, curvature shock. *)
Definition observer_create_wormhole (tobs : TopologicalObserver)
                                    (net : NetworkTopology) (target : Fin)
  : (TopologicalObserver * NetworkTopology) :=
  match obs_budget (topo_observer tobs) with
  | fz => (tobs, net)
  | fs b' =>
      let wormhole :=
        {| end1 := topo_position tobs;
           end2 := target;
           stability := (fs fz, fs (fs (fs (fs fz))));  (* 1/4 — barely there *)
           maintenance_cost := operation_cost |} in
      let critical_curv := (fs (fs fz), fs (fs (fs fz))) in  (* 2/3 *)
      let new_net :=
        {| size := size net;
           bridges := wormhole :: bridges net;
           fold_energy := fz;  (* All fold energy consumed *)
           ambient_curvature := critical_curv;
           topology_budget := topology_budget net |} in
      let desperate_tobs :=
        {| topo_observer := {| observer := observer (topo_observer tobs);
                               obs_budget := b' |};
           topo_position := topo_position tobs;
           topo_trajectory := topo_trajectory tobs;
           topo_spur := fs (fs (fs (topo_spur tobs))) |} in  (* Triple Spuren *)
      (* Curvature shock *)
      (curvature_tax desperate_tobs new_net, new_net)
  end.

(* Observer-driven emergency unfold — when curvature is critical,
   the observer sacrifices a bridge to survive. *)
Definition observer_emergency_unfold (tobs : TopologicalObserver)
                                     (net : NetworkTopology)
  : (TopologicalObserver * NetworkTopology) :=
  match write_check_critical net (obs_budget (topo_observer tobs)) with
  | (true, b', _) =>
      match write_unfold_space net b' with
      | (net', b'', _) =>
          let relieved_tobs :=
            {| topo_observer := {| observer := observer (topo_observer tobs);
                                   obs_budget := b'' |};
               topo_position := topo_position tobs;
               topo_trajectory := topo_trajectory tobs;
               topo_spur := fs (topo_spur tobs) |} in
          (relieved_tobs, net')
      end
  | (false, b', _) =>
      ({| topo_observer := {| observer := observer (topo_observer tobs);
                               obs_budget := b' |};
          topo_position := topo_position tobs;
          topo_trajectory := topo_trajectory tobs;
          topo_spur := topo_spur tobs |}, net)
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

(* Original infrastructure *)
Definition NetworkTopology_ext := NetworkTopology.
Definition FoldBridge_ext := FoldBridge.
Definition write_fold_space_ext := write_fold_space.
Definition write_bridge_jump_ext := write_bridge_jump.
Definition emergency_unfold_ext := emergency_unfold.

(* Observer-in-topology *)
Definition TopologicalObserver_ext := TopologicalObserver.
Definition place_observer_ext := place_observer.
Definition observe_bridge_ext := observe_bridge.
Definition scan_local_topology_ext := scan_local_topology.
Definition curvature_tax_ext := curvature_tax.
Definition bridge_uncertainty_ext := bridge_uncertainty.
Definition observer_bridge_jump_ext := observer_bridge_jump.
Definition observer_fold_space_ext := observer_fold_space.
Definition observer_create_wormhole_ext := observer_create_wormhole.
Definition observer_emergency_unfold_ext := observer_emergency_unfold.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* PHILOSOPHICAL NOTE — TOPOLOGY AS ONTO-EPISTEMOLOGY

   This module embodies the deepest consequence of VOID:
   space is not given — it is constructed, and construction
   has a cost that transforms both the constructor and the constructed.

   1. THE OBSERVER IS IN THE TOPOLOGY — not looking at it from
      outside. TopologicalObserver has position, trajectory, and
      accumulated Spuren. There is no God's-eye view of space.

   2. DDF FORWARD: OBSERVATION CHANGES SPACE — looking at a bridge
      weakens it. Scanning topology distorts it. The map is never
      the territory because making the map changes the territory.
      This is Heisenberg applied to geometry itself.

   3. DDF BACKWARD: SPACE CHANGES THE OBSERVER — curved space
      taxes the observer's budget. Unstable bridges inject Spuren.
      The environment is not passive substrate. It bites back.

   4. EVERY PASSAGE LEAVES A MARK — on both the bridge (stability
      decay) and the traveler (Spuren injection). There is no
      innocent movement through space. Every step is a wound
      and a gift, simultaneously.

   5. WORMHOLES AS DESPERATION — not forbidden, but ruinous.
      Triple Spuren, exhausted fold energy, critical curvature.
      The most violent act an observer can perform on space.

   6. MAINTENANCE IS ENTROPY — bridges decay, curvature tends
      toward flatness, fold energy depletes. Topology is
      thermodynamic. Structure costs energy to maintain.

   7. ONE TICK PER EVERYTHING — folding, jumping, observing,
      enduring curvature. No operation is privileged. The
      universe charges the same price for every question.

   This is geometry where the geometer is part of the figure,
   where measuring changes the measured, and where the cost of
   knowing where you are is paid in the currency of being able
   to go somewhere else. *)

End Void_Topology_Folding.