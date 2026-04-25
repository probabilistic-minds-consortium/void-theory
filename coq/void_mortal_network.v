(******************************************************************************)
(* void_mortal_network.v - N-LAYER MORTAL NETWORK + network_step              *)
(*                                                                            *)
(* Composes void_network_cell primitives (learn_step_open, transfer_credit,  *)
(* spawn_inherited) into an N-layer network and one step of its dynamics.   *)
(*                                                                            *)
(* NETWORK STRUCTURE (general):                                               *)
(*   net_layers : list (list LearningPredCell)                                *)
(*     First element is layer 0 (input-facing); last is the top layer.       *)
(*     Each layer is a list of cells.  Every cell in layer k sees the same  *)
(*     inputs and the same truth on any given step.                          *)
(*                                                                            *)
(* TWO CASCADE REGIMES (selected by net_regime field):                        *)
(*                                                                            *)
(*   RegimeAnySurprise (original):                                           *)
(*     layer 0     : inputs = raw_input, truth = raw_truth                   *)
(*     layer k+1   : inputs = surprises_to_cascade_inputs surps_k            *)
(*                   truth  = any_surprise surps_k                           *)
(*     Each higher layer predicts whether the layer below was surprised.    *)
(*     Pro: unsupervised (no external label needed past L0).                *)
(*     Con: L2+ signal degrades on nonlinear tasks (parity -> NoSurp=0).   *)
(*                                                                            *)
(*   RegimeTruthProp (new):                                                  *)
(*     layer 0     : inputs = raw_input, truth = raw_truth                   *)
(*     layer k+1   : inputs = surprises_to_cascade_inputs surps_k            *)
(*                   truth  = raw_truth  (BROADCAST, not any_surprise)       *)
(*     Every layer receives the ground-truth label.  Features flow up       *)
(*     (cascade inputs) but supervision is global.                          *)
(*     Pro: all layers learn the task (C1: L2-L4 alive vs dead).           *)
(*     Con: requires external supervisor at every step.                    *)
(*                                                                            *)
(* Use network_step_unified to dispatch on net_regime automatically.        *)
(* The cascade DOUBLES input width: each lower cell contributes two Bool3s *)
(* (direction, quality), interleaved.  A lower layer of N cells produces   *)
(* 2N inputs for the layer above.                                           *)
(*                                                                            *)
(* SURPRISE -> (direction, quality) MAP:                                      *)
(*   NoSurprise       -> (BUnknown, BTrue )  - computed, no direction       *)
(*   SurpriseFor      -> (BTrue,    BTrue )  - computed, wants more TRUE   *)
(*   SurpriseAgainst  -> (BFalse,   BTrue )  - computed, wants more FALSE  *)
(*   SurpriseUnknown  -> (BUnknown, BFalse)  - never reached a conclusion   *)
(*                                                                            *)
(* REWARD POLICY (top-down, per-cell):                                        *)
(*   For each adjacent pair (lower, upper), walk the pair of lists in       *)
(*   lockstep.  For each upper cell with NoSurprise, distribute one tick    *)
(*   (transfer_credit) to EVERY lower cell.  Dead lower cells absorb no-op  *)
(*   (L6).  Upper cells with SurpriseFor/Against/Unknown give nothing.      *)
(*   Cascade runs from the top layer downward.                               *)
(*                                                                            *)
(* SPAWN POLICY (per-cell, INHERITANCE-ONLY):                                 *)
(*   After learn + reward, any cell with budget=fz is replaced via          *)
(*   spawn_inherited from some source.  Source selection per cell:           *)
(*     - Compute UPPER CONSENSUS: fold the upper layer's prediction list   *)
(*       with interfere_b3 (BTrue+BFalse -> BUnknown, BUnknown absorbing). *)
(*       Consensus requires UNANIMOUS agreement above to produce anything  *)
(*       other than BUnknown.  Semantics taken from void_neural_theory's   *)
(*       interfere, inlined rather than imported across cell stacks.       *)
(*     - If the consensus matches surprise_to_bool3 of THIS cell's own     *)
(*       surprise (per_cell_policy), inherit from THIS dead cell: its     *)
(*       weights were not only informative but the whole layer above      *)
(*       agreed on them.                                                    *)
(*     - Else, inherit from a LIVING neighbor in the same layer.            *)
(*     - Fallback (entire layer dead, no living neighbor): inherit from     *)
(*       the head of the layer.  Still nonzero weights; still educable.    *)
(*   For the top layer (no upper oracle): consensus defaults to BUnknown  *)
(*   and per_cell_policy almost always returns false (unless the cell's   *)
(*   own surprise is SurpriseUnknown), so the top layer is mostly         *)
(*   replaced from neighbors / head fallback.  There is NEVER a zero-     *)
(*   weight spawn.  spawn_random is not in the call graph of this file.   *)
(*   It remains in void_network_cell as a documentary witness (lemma R3)  *)
(*   against tabula rasa.                                                   *)
(*                                                                            *)
(* CONSEQUENCE: every cell the network ever runs started life with weights *)
(* that had structure.  lpc_predict on such a cell returns BTrue/BFalse   *)
(* under suitable inputs, compute_surprise returns For/Against/No, and    *)
(* update_weights actually adjusts the weight vectors.  The factory-of-   *)
(* corpses failure mode (runtime: 200 deaths, all spawn_random, zero      *)
(* learning) is eliminated by construction.                                *)
(*                                                                            *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal,               *)
(*             void_predictive_learning, void_mortal_regime,                *)
(*             void_network_cell.                                           *)
(* ZERO Admitted.  ZERO new Axioms.                                         *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_predictive_learning.
Require Import void_mortal_regime.
Require Import void_network_cell.

Import Void_Probability_Minimal.

(******************************************************************************)
(* PART 0: Numeric helpers (moved above Part 1 so default_parent_budget can   *)
(* use fin_double).  Starter/parent budgets have to be large enough that     *)
(* lpc_predict (accumulate_for + accumulate_against + two le_fin_b3 calls)  *)
(* plus compute_surprise plus update_weights complete in a single cell tick  *)
(* without exhausting the cell.  With the previous values (f8 / f4) cells   *)
(* burn out mid-predict, return BUnknown, never reach the learning phase - *)
(* the Unknown-loop regime.                                                 *)
(******************************************************************************)

Fixpoint fin_double (n : Fin) : Fin :=
  match n with
  | fz    => fz
  | fs n' => fs (fs (fin_double n'))
  end.

(* Small Fin abbreviations and the large-power constants.  f128 is used   *)
(* by default_parent_budget below AND re-exposed as f128 in PART 4 for   *)
(* starter_budget.  One copy only; PART 4 just re-points.                *)
Definition f1  : Fin := fs fz.
Definition f2  : Fin := fs (fs fz).
Definition f3  : Fin := fs (fs (fs fz)).
Definition f4  : Fin := fs (fs (fs (fs fz))).
Definition f8  : Fin := fs (fs (fs (fs (fs (fs (fs (fs fz))))))).
Definition f16  : Fin := fin_double f8.
Definition f32  : Fin := fin_double f16.
Definition f64  : Fin := fin_double f32.
Definition f128 : Fin := fin_double f64.
Definition f256 : Fin := fin_double f128.
Definition f512 : Fin := fin_double f256.
Definition f1024 : Fin := fin_double f512.

(******************************************************************************)
(* PART 1: Network record + small helpers                                     *)
(******************************************************************************)

Inductive Regime : Type :=
  | RegimeAnySurprise
  | RegimeTruthProp.

Record Network := mkNet {
  net_regime : Regime ;
  net_layers : list (list LearningPredCell)
}.

(* DIRECTION-AWARE cascade mapping.  Previously SurpriseFor and             *)
(* SurpriseAgainst both collapsed to BTrue, and NoSurprise / SurpriseUnknown *)
(* to BFalse / BUnknown respectively - upper layer saw only 'was there a    *)
(* disagreement' and could not learn to distinguish which direction the    *)
(* lower layer erred in.                                                    *)
(*                                                                            *)
(* Under the new mapping:                                                   *)
(*   SurpriseFor     -> BTrue   (lower underestimated - world more TRUE)    *)
(*   SurpriseAgainst -> BFalse  (lower overestimated - world more FALSE)   *)
(*   NoSurprise      -> BUnknown (collapsed with Unknown: nothing to learn)*)
(*   SurpriseUnknown -> BUnknown                                             *)
(*                                                                            *)
(* Cost: upper layer loses the ability to distinguish 'agreement' from     *)
(* 'pure noise' - both are now BUnknown.  This is a deliberate neurotic    *)
(* geometry: success and confusion share a signal, only error-direction   *)
(* can activate learning.                                                   *)
Definition surprise_to_bool3 (s : Surprise) : Bool3 :=
  match s with
  | NoSurprise      => BUnknown
  | SurpriseFor     => BTrue
  | SurpriseAgainst => BFalse
  | SurpriseUnknown => BUnknown
  end.

(* QUALITY CHANNEL.  Second projection of the cascade signal from each cell. *)
(* The direction channel (surprise_to_bool3) cannot distinguish NoSurprise  *)
(* from SurpriseUnknown: both collapse to BUnknown.  The quality channel    *)
(* carries the missing discriminator - 'did this cell reach a conclusion    *)
(* at all?'  SurpriseFor, SurpriseAgainst, NoSurprise all get BTrue       *)
(* because the computation ran to completion.  SurpriseUnknown gets        *)
(* BFalse because the cell either exhausted budget or received BUnknown   *)
(* inputs and never produced a directional answer.                         *)
(*                                                                            *)
(* Upper-layer cells receive direction and quality interleaved, so for a   *)
(* lower layer of N cells the upper layer sees 2N inputs.  The quality     *)
(* bit is precisely the discriminator that `spur` already encodes inside   *)
(* each cell (high spur for NoSurprise, low spur for SurpriseUnknown) -    *)
(* we surface it explicitly into the cascade instead of propagating spur.  *)
Definition surprise_quality (s : Surprise) : Bool3 :=
  match s with
  | NoSurprise      => BTrue
  | SurpriseFor     => BTrue
  | SurpriseAgainst => BTrue
  | SurpriseUnknown => BFalse
  end.

(* Flatten a list of surprises into the interleaved Bool3 input vector for *)
(* the next layer up.  For N surprises produces 2N Bool3s:                *)
(*   [dir_0; qual_0; dir_1; qual_1; ...; dir_{N-1}; qual_{N-1}].          *)
Fixpoint surprises_to_cascade_inputs (surps : list Surprise) : list Bool3 :=
  match surps with
  | []        => []
  | s :: rest =>
      surprise_to_bool3 s
        :: surprise_quality s
        :: surprises_to_cascade_inputs rest
  end.

(* any_surprise must agree with surprise_to_bool3 as the TRUTH signal for *)
(* the upper layer.  First-wins on direction: the first cell that fired a *)
(* directional surprise sets the truth for the whole layer above.  Ties  *)
(* across cells (mixed For/Against) still resolve to the first seen -   *)
(* arbitrary, but deterministic.                                           *)
Fixpoint any_surprise (surps : list Surprise) : Bool3 :=
  match surps with
  | []                    => BUnknown
  | SurpriseFor     :: _  => BTrue
  | SurpriseAgainst :: _  => BFalse
  | _ :: rest             => any_surprise rest
  end.

Definition bool3_eq (a b : Bool3) : bool :=
  match a, b with
  | BTrue,    BTrue    => true
  | BFalse,   BFalse   => true
  | BUnknown, BUnknown => true
  | _, _               => false
  end.

(* Bool3 interference, matching the semantics of void_neural_theory.v's
   `interfere`: BTrue ^ BFalse = BUnknown (disagreement produces ignorance),
   BUnknown is absorbing.  Conservative lattice consensus.  Inlined here
   rather than imported because void_neural_theory sits on the older       *)
(* void_learning_cell stack and pulling it in would mix the two cell      *)
(* models.  Definitional parity with the old file is intentional.         *)
Definition interfere_b3 (a b : Bool3) : Bool3 :=
  match a, b with
  | BTrue,    BTrue    => BTrue
  | BFalse,   BFalse   => BFalse
  | BTrue,    BFalse   => BUnknown
  | BFalse,   BTrue    => BUnknown
  | BUnknown, _        => BUnknown
  | _,        BUnknown => BUnknown
  end.

(* Aggregate a list of Bool3 predictions into a single consensus Bool3.   *)
(* Conservative: any disagreement or any ignorance drives the consensus   *)
(* to BUnknown.  Empty prediction list defaults to BUnknown -- i.e.       *)
(* nothing-to-say is ignorance, not NoSurprise.  This keeps the top-layer *)
(* boundary case honest: no oracle above means we never claim a match.    *)
Fixpoint aggregate_preds (preds : list Bool3) : Bool3 :=
  match preds with
  | []      => BUnknown
  | [p]     => p
  | p :: rs => interfere_b3 p (aggregate_preds rs)
  end.

(* Per-cell policy: the upper layer's consensus prediction (single Bool3 *)
(* post-aggregation) is compared with the Bool3-image of this cell's own  *)
(* surprise.  If they match, the cell's weights were predictable from    *)
(* above -> inherit from the dead cell.  Otherwise the cell was opaque   *)
(* to the layer above -> inherit from a living neighbor.                  *)
Definition per_cell_policy (upper_consensus : Bool3) (s : Surprise) : bool :=
  bool3_eq upper_consensus (surprise_to_bool3 s).

Fixpoint find_living (cells : list LearningPredCell) : option LearningPredCell :=
  match cells with
  | []        => None
  | c :: rest =>
      match lpc_budget c with
      | fz => find_living rest
      | _  => Some c
      end
  end.

(******************************************************************************)
(* PART 2: Per-layer learn pass                                               *)
(******************************************************************************)

Fixpoint step_layer (cells : list LearningPredCell) (inputs : list Bool3)
                    (truth : Bool3)
  : list LearningPredCell * list Bool3 * list Surprise :=
  match cells with
  | []       => ([], [], [])
  | c :: cs  =>
      match learn_step_open c inputs truth with
      | (c', pred, surp) =>
          match step_layer cs inputs truth with
          | (cs', preds, surps) => (c' :: cs', pred :: preds, surp :: surps)
          end
      end
  end.

(******************************************************************************)
(* PART 3: Forward cascade through all layers                                 *)
(*                                                                            *)
(* Returns per-layer: stepped cells, predictions, surprises.  The cascade   *)
(* is indexed by the layer list itself (structural recursion on layers).    *)
(******************************************************************************)

Fixpoint cascade (layers : list (list LearningPredCell))
                 (inputs : list Bool3) (truth : Bool3)
  : list (list LearningPredCell) * list (list Bool3) * list (list Surprise) :=
  match layers with
  | []       => ([], [], [])
  | L :: rest =>
      match step_layer L inputs truth with
      | (L', preds, surps) =>
          let next_inputs := surprises_to_cascade_inputs surps in
          let next_truth  := any_surprise surps in
          match cascade rest next_inputs next_truth with
          | (rest', preds_rest, surps_rest) =>
              (L' :: rest', preds :: preds_rest, surps :: surps_rest)
          end
      end
  end.

(******************************************************************************)
(* PART 4: Reward propagation                                                 *)
(*                                                                            *)
(* distribute_one_tick: one tick from a SINGLE sender cell to each receiver *)
(* in the list, in order.  Dead receivers absorb no-op via transfer_credit  *)
(* L6.  Sender's budget drops until exhausted.                              *)
(*                                                                            *)
(* reward_pair: for each pair (upper_cell, upper_surp) walked in lockstep, *)
(* if upper had NoSurprise, upper distributes one tick per lower cell.     *)
(* Upper cells with any other surprise give nothing.                         *)
(*                                                                            *)
(* apply_rewards_topdown: recurse on the tail first to compute the rewarded *)
(* state of everything above L, then fire reward_pair between L and the    *)
(* now-rewarded L'.  Cascades budget downward.                               *)
(******************************************************************************)

Fixpoint distribute_one_tick (sender : LearningPredCell)
                             (receivers : list LearningPredCell)
  : LearningPredCell * list LearningPredCell :=
  match receivers with
  | []       => (sender, [])
  | r :: rs  =>
      match transfer_credit sender r (fs fz) with
      | (s', r') =>
          match distribute_one_tick s' rs with
          | (s_final, rs') => (s_final, r' :: rs')
          end
      end
  end.

Fixpoint reward_pair (uppers : list LearningPredCell)
                     (lowers : list LearningPredCell)
                     (upper_surps : list Surprise)
  : list LearningPredCell * list LearningPredCell :=
  match uppers, upper_surps with
  | [], _         => ([], lowers)
  | _ :: _, []    => (uppers, lowers)
  | u :: us, s :: srest =>
      match s with
      | NoSurprise =>
          match distribute_one_tick u lowers with
          | (u', lowers') =>
              match reward_pair us lowers' srest with
              | (us', lowers'') => (u' :: us', lowers'')
              end
          end
      | _ =>
          match reward_pair us lowers srest with
          | (us', lowers') => (u :: us', lowers')
          end
      end
  end.

Fixpoint apply_rewards_topdown (layers : list (list LearningPredCell))
                               (surps : list (list Surprise))
  : list (list LearningPredCell) :=
  match layers with
  | []       => []
  | L :: rest =>
      match rest with
      | [] => [L]
      | _  =>
          match apply_rewards_topdown rest (tl surps) with
          | []               => [L]
          | L'_after :: rest_after =>
              let s_above :=
                match tl surps with
                | s' :: _ => s'
                | []      => []
                end in
              match reward_pair L'_after L s_above with
              | (L'_spent, L_rewarded) =>
                  L_rewarded :: L'_spent :: rest_after
              end
          end
      end
  end.

(******************************************************************************)
(* PART 5: Dead-cell policy - DEATH STAYS DEAD (repair phase is no-op)       *)
(*                                                                            *)
(* Historical note.  Earlier policy: if a cell died (budget=fz) during a     *)
(* step, we respawned it in-slot via spawn_inherited, drawing weights from  *)
(* either the dead cell itself (when the upper layer agreed with its last  *)
(* behavior) or from a living neighbor.  This satisfied the hand-wavy N2   *)
(* invariant "no dead cell after a step" but paid a heavy price: it        *)
(* overwrote specific cell function with whichever neighbor happened to be *)
(* at the head of the list.  The diagnostic in tmp_network_run showed      *)
(* cell_16_quality_reader (deliberately miswired) dying after one update  *)
(* and getting nuked by cell_16_direction_reader's starter weights.  That  *)
(* is "budowanie na grobach" - building on graves.  Not a feature.         *)
(*                                                                            *)
(* New policy.  replace_if_dead_source is identity.  Dead cells stay dead  *)
(* and keep returning SurpriseUnknown from lpc_predict.  The network grows *)
(* exclusively through network_spawn_explorer (budding), which inserts    *)
(* NEW cells at the end of a chosen layer without touching any existing   *)
(* slots.  A dead slot is an honest silence, not a lie propped up by     *)
(* a copy of its neighbor.                                                  *)
(*                                                                            *)
(* The per_cell_policy / upper_consensus / neighbor machinery below is    *)
(* now dead code from a dynamics perspective - replace_dead_per_layer     *)
(* computes and ignores these values.  Kept for one release in case we    *)
(* want to re-introduce more refined death policies (e.g., inherit from   *)
(* an off-slot ancestor).  Scheduled for deletion after the budding-only *)
(* regime is confirmed stable.                                             *)
(******************************************************************************)

(* Retained for network_spawn_explorer (make_explorer), which budgets a   *)
(* newly inserted cell at f128.  No longer used in replace_if_dead_source. *)
Definition default_parent_budget : Fin := f128.

(* DEATH-STAYS-DEAD.  Previously: if c was dead, spawn a replacement from  *)
(* source (the "budowanie na grobach" policy - in-slot inheritance from   *)
(* a neighbor).  That policy wiped specific cell function the moment its *)
(* budget ran out, and was confirmed to overwrite miswired learning      *)
(* cells with their aligned neighbors (see tmp_network_run diagnostic).  *)
(*                                                                        *)
(* Now: replace_if_dead_source is identity.  Dead cells stay dead and    *)
(* keep returning SurpriseUnknown via lpc_predict's budget check.  The   *)
(* only way to grow the network is network_spawn_explorer, which adds   *)
(* NEW cells at the end of a layer without touching existing slots.     *)
(*                                                                        *)
(* The `source` argument is retained for signature compatibility with    *)
(* replace_dead_per_layer callers; it is no longer consulted.            *)
Definition replace_if_dead_source (c : LearningPredCell)
                                  (_source : LearningPredCell)
  : LearningPredCell := c.

Fixpoint replace_dead_per_layer (upper_consensus : Bool3)
                                (neighbor : LearningPredCell)
                                (cells : list LearningPredCell)
                                (surps : list Surprise)
  : list LearningPredCell :=
  match cells with
  | []       => []
  | c :: cs  =>
      let source :=
        match surps with
        | s :: _ =>
            if per_cell_policy upper_consensus s then c else neighbor
        | []     => neighbor
        end in
      let srest :=
        match surps with
        | _ :: r => r
        | []     => []
        end in
      replace_if_dead_source c source
      :: replace_dead_per_layer upper_consensus neighbor cs srest
  end.

(* pick_neighbor: live cell if any, else head of list.  Used by              *)
(* replace_all_layers which guards against the empty-layer case, so the      *)
(* second branch here is only reached when the layer is entirely dead.       *)
Definition pick_neighbor (cells : list LearningPredCell)
                         (head_fallback : LearningPredCell)
  : LearningPredCell :=
  match find_living cells with
  | Some n => n
  | None   => head_fallback
  end.

Fixpoint replace_all_layers (layers : list (list LearningPredCell))
                            (preds : list (list Bool3))
                            (surps : list (list Surprise))
  : list (list LearningPredCell) :=
  match layers with
  | []       => []
  | L :: rest =>
      match L with
      | []        =>
          [] :: replace_all_layers rest (tl preds) (tl surps)
      | c0 :: _   =>
          let upper_consensus :=
            match preds with
            | _ :: p_above :: _ => aggregate_preds p_above
            | _                 => BUnknown
            end in
          let s_this :=
            match surps with
            | s :: _ => s
            | []     => []
            end in
          let neighbor := pick_neighbor L c0 in
          let L_replaced :=
            replace_dead_per_layer upper_consensus neighbor L s_this in
          L_replaced :: replace_all_layers rest (tl preds) (tl surps)
      end
  end.

(******************************************************************************)
(* PART 6: network_step                                                       *)
(******************************************************************************)

Definition network_step (net : Network) (raw_input : list Bool3) (truth : Bool3)
  : Network :=
  match cascade (net_layers net) raw_input truth with
  | (layers_learned, preds, surps) =>
      let layers_rewarded := apply_rewards_topdown layers_learned surps in
      let layers_final    := replace_all_layers layers_rewarded preds surps in
      mkNet (net_regime net) layers_final
  end.

(* Verbose variant: returns both the stepped network AND the per-layer         *)
(* surprise vectors from the forward cascade.  Used for runtime inspection     *)
(* without duplicating the cascade computation.  The stepped network is       *)
(* identical to what network_step returns on the same inputs (same cascade).  *)
Definition network_step_verbose (net : Network) (raw_input : list Bool3) (truth : Bool3)
  : Network * list (list Surprise) :=
  match cascade (net_layers net) raw_input truth with
  | (layers_learned, preds, surps) =>
      let layers_rewarded := apply_rewards_topdown layers_learned surps in
      let layers_final    := replace_all_layers layers_rewarded preds surps in
      (mkNet (net_regime net) layers_final, surps)
  end.

(******************************************************************************)
(* PART 6a: TRUTH-PROPAGATION CASCADE                                         *)
(*                                                                            *)
(* Alternative cascade regime: every layer receives the SAME ground-truth    *)
(* (the raw task target), rather than any_surprise of the layer below.       *)
(* Cascade features still flow upward (surprises -> inputs), but the         *)
(* training signal is broadcast.  This enables end-to-end supervised         *)
(* learning across all layers.                                                *)
(*                                                                            *)
(* Empirical result (C1): any_surprise kills L2+ prediction on parity       *)
(* (NoSurp = 0 by E2), while truth_prop keeps all layers active.           *)
(******************************************************************************)

Fixpoint cascade_truth_prop (layers : list (list LearningPredCell))
                            (inputs : list Bool3) (truth : Bool3)
  : list (list LearningPredCell) * list (list Bool3) * list (list Surprise) :=
  match layers with
  | []       => ([], [], [])
  | L :: rest =>
      match step_layer L inputs truth with
      | (L', preds, surps) =>
          let next_inputs := surprises_to_cascade_inputs surps in
          (* KEY DIFFERENCE: truth stays the same, not any_surprise surps. *)
          match cascade_truth_prop rest next_inputs truth with
          | (rest', preds_rest, surps_rest) =>
              (L' :: rest', preds :: preds_rest, surps :: surps_rest)
          end
      end
  end.

Definition network_step_truth_prop (net : Network)
                                    (raw_input : list Bool3) (truth : Bool3)
  : Network * list (list Surprise) :=
  match cascade_truth_prop (net_layers net) raw_input truth with
  | (layers_learned, preds, surps) =>
      let layers_rewarded := apply_rewards_topdown layers_learned surps in
      let layers_final    := replace_all_layers layers_rewarded preds surps in
      (mkNet (net_regime net) layers_final, surps)
  end.

(* Unified step: dispatches on net_regime.                                     *)
(* RegimeAnySurprise -> original cascade (any_surprise truth propagation).    *)
(* RegimeTruthProp   -> broadcast ground-truth to every layer.               *)
Definition network_step_unified (net : Network)
                                 (raw_input : list Bool3) (truth : Bool3)
  : Network * list (list Surprise) :=
  match net_regime net with
  | RegimeAnySurprise => network_step_verbose net raw_input truth
  | RegimeTruthProp   => network_step_truth_prop net raw_input truth
  end.

(******************************************************************************)
(* PART 6b: RANDOM EXPLORER SPAWN                                             *)
(*                                                                            *)
(* Separate from network_step dead-cell replacement.  This operation adds    *)
(* a NEW cell to a chosen layer, inheriting weights from the layer head.     *)
(* The Python runtime calls this with a random layer index after each step.  *)
(*                                                                            *)
(* Width mismatch: adding a cell to layer k extends the cascade output for   *)
(* layer k+1 by 2 inputs (direction + quality).  Existing cells in k+1 have *)
(* weight vectors of the old width -- the extra inputs are silently ignored  *)
(* by accumulate (zip semantics).  The new cell is invisible to the layer    *)
(* above until cells above respawn with wider inherited weights.  This is    *)
(* intentional: a newborn must earn attention.                                *)
(*                                                                            *)
(* Inheritance: the explorer inherits from the HEAD of the target layer.     *)
(* Not zeros (R3 forbids tabula rasa).  Not a neighbor -- the explorer is    *)
(* placed at the end, so it inherits the perspective of position 0, which   *)
(* is maximally different from its own position.  Trauma from the old head  *)
(* seeds the new cell worldview.                                             *)
(******************************************************************************)

(* Fin-valued length for the preservation lemma.  VT is strictly          *)
(* finitist - Coq's stdlib `length` returns nat, which we do not allow. *)
Fixpoint length_fin {A : Type} (l : list A) : Fin :=
  match l with
  | []      => fz
  | _ :: rs => fs (length_fin rs)
  end.

(* Fin-indexed head-lookup on a list of layers.  Returns None when the   *)
(* index is out of range.  Parallels Coq's nth_error but indexed by Fin. *)
Fixpoint nth_fin_layers (layers : list (list LearningPredCell)) (n : Fin)
  : option (list LearningPredCell) :=
  match layers, n with
  | [],       _    => None
  | L :: _,   fz   => Some L
  | _ :: rs,  fs m => nth_fin_layers rs m
  end.

Fixpoint insert_at_layer (n : Fin) (cell : LearningPredCell)
                         (layers : list (list LearningPredCell))
  : list (list LearningPredCell) :=
  match layers, n with
  | [],       _    => []
  | L :: rest, fz  => (L ++ [cell]) :: rest
  | L :: rest, fs m => L :: insert_at_layer m cell rest
  end.

Definition make_explorer (layers : list (list LearningPredCell))
                         (layer_idx : Fin)
  : option LearningPredCell :=
  match nth_fin_layers layers layer_idx with
  | None          => None
  | Some []       => None
  | Some (c :: _) => Some (spawn_inherited c default_parent_budget)
  end.

Definition network_spawn_explorer (net : Network) (layer_idx : Fin)
  : Network :=
  match make_explorer (net_layers net) layer_idx with
  | None      => net
  | Some cell => mkNet (net_regime net) (insert_at_layer layer_idx cell (net_layers net))
  end.

Lemma make_explorer_alive :
  forall layers idx cell,
    make_explorer layers idx = Some cell ->
    lpc_budget cell <> fz.
Proof.
  intros layers idx cell Hexp.
  unfold make_explorer in Hexp.
  destruct (nth_fin_layers layers idx) as [L|] eqn:Enth.
  - destruct L as [| c rest].
    + discriminate.
    + inversion Hexp; subst.
      unfold spawn_inherited. simpl.
      unfold default_parent_budget. cbn.
      intro H. discriminate.
  - discriminate.
Qed.

Lemma insert_at_layer_preserves_num_layers :
  forall n cell layers,
    length_fin (insert_at_layer n cell layers) = length_fin layers.
Proof.
  intros n cell layers. revert n.
  induction layers as [| L rest IH]; intros n.
  - destruct n; reflexivity.
  - destruct n as [| m].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(* Full step WITH explorer spawn.  learn + reward + replace_dead + budding. *)
(* layer_idx chooses the target layer (Fin, out-of-range = no spawn).      *)
(* An external runtime (Python harness or nat-free Coq scheduler) passes   *)
(* a Fin index each step.                                                   *)
Definition network_step_with_explorer (net : Network)
                                      (raw_input : list Bool3) (truth : Bool3)
                                      (layer_idx : Fin)
  : Network :=
  let net' := network_step net raw_input truth in
  network_spawn_explorer net' layer_idx.

(* Verbose + explorer. *)
Definition network_step_with_explorer_verbose (net : Network)
                                              (raw_input : list Bool3) (truth : Bool3)
                                              (layer_idx : Fin)
  : Network * list (list Surprise) :=
  match network_step_verbose net raw_input truth with
  | (net', surps) => (network_spawn_explorer net' layer_idx, surps)
  end.

(******************************************************************************)
(* PART 7: LENGTH-PRESERVATION LEMMAS                                         *)
(******************************************************************************)

Lemma step_layer_preserves_length :
  forall cells inputs truth cells' preds surps,
    step_layer cells inputs truth = (cells', preds, surps) ->
    length cells = length cells'.
Proof.
  induction cells as [| c cs IH]; intros inputs truth cells' preds surps Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - simpl in Heq.
    destruct (learn_step_open c inputs truth) as [[c' p] s].
    destruct (step_layer cs inputs truth) as [[cs'' preds''] surps''] eqn:Erec.
    inversion Heq; subst.
    simpl. f_equal. eapply IH. exact Erec.
Qed.

Lemma distribute_one_tick_preserves_length :
  forall receivers sender sender' receivers',
    distribute_one_tick sender receivers = (sender', receivers') ->
    length receivers = length receivers'.
Proof.
  induction receivers as [| r rs IH]; intros sender sender' receivers' Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - simpl in Heq.
    destruct (transfer_credit sender r (fs fz)) as [s' r'] eqn:Etrans.
    destruct (distribute_one_tick s' rs) as [s_final rs''] eqn:Edist.
    inversion Heq; subst.
    simpl. f_equal. eapply IH. exact Edist.
Qed.

Lemma reward_pair_preserves_upper_length :
  forall uppers lowers upper_surps uppers' lowers',
    reward_pair uppers lowers upper_surps = (uppers', lowers') ->
    length uppers = length uppers'.
Proof.
  induction uppers as [| u us IH]; intros lowers upper_surps uppers' lowers' Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - destruct upper_surps as [| s srest].
    + simpl in Heq. inversion Heq. reflexivity.
    + simpl in Heq. destruct s.
      * (* NoSurprise *)
        destruct (distribute_one_tick u lowers) as [u' lowers0] eqn:Edist.
        destruct (reward_pair us lowers0 srest) as [us' lowers1] eqn:Erec.
        inversion Heq; subst.
        simpl. f_equal. eapply IH. exact Erec.
      * destruct (reward_pair us lowers srest) as [us' lowers0] eqn:Erec.
        inversion Heq; subst.
        simpl. f_equal. eapply IH. exact Erec.
      * destruct (reward_pair us lowers srest) as [us' lowers0] eqn:Erec.
        inversion Heq; subst.
        simpl. f_equal. eapply IH. exact Erec.
      * destruct (reward_pair us lowers srest) as [us' lowers0] eqn:Erec.
        inversion Heq; subst.
        simpl. f_equal. eapply IH. exact Erec.
Qed.

Lemma reward_pair_preserves_lower_length :
  forall uppers lowers upper_surps uppers' lowers',
    reward_pair uppers lowers upper_surps = (uppers', lowers') ->
    length lowers = length lowers'.
Proof.
  induction uppers as [| u us IH]; intros lowers upper_surps uppers' lowers' Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - destruct upper_surps as [| s srest].
    + simpl in Heq. inversion Heq. reflexivity.
    + simpl in Heq. destruct s.
      * destruct (distribute_one_tick u lowers) as [u' lowers0] eqn:Edist.
        destruct (reward_pair us lowers0 srest) as [us' lowers1] eqn:Erec.
        inversion Heq; subst.
        apply distribute_one_tick_preserves_length in Edist.
        rewrite Edist. eapply IH. exact Erec.
      * destruct (reward_pair us lowers srest) as [us' lowers0] eqn:Erec.
        inversion Heq; subst. eapply IH. exact Erec.
      * destruct (reward_pair us lowers srest) as [us' lowers0] eqn:Erec.
        inversion Heq; subst. eapply IH. exact Erec.
      * destruct (reward_pair us lowers srest) as [us' lowers0] eqn:Erec.
        inversion Heq; subst. eapply IH. exact Erec.
Qed.

Lemma replace_dead_per_layer_preserves_length :
  forall preds neighbor cells surps,
    length (replace_dead_per_layer preds neighbor cells surps) = length cells.
Proof.
  intros preds neighbor cells. revert preds.
  induction cells as [| c cs IH]; intros preds surps.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(******************************************************************************)
(* PART 8: STEP PRESERVATION LEMMAS                                          *)
(*                                                                            *)
(* Under death-stays-dead, N2 ("no dead cells after step") is no longer     *)
(* true and was never really right: it was a promise we kept by overwriting *)
(* dead cells with living copies of their neighbors, destroying specific    *)
(* function.  The replacement invariants we want now are weaker but          *)
(* honest:                                                                   *)
(*                                                                            *)
(*   (a) replace_if_dead_source is identity: the repair phase does not move *)
(*       any cell.  Dead cells fall through unchanged, live cells unchanged. *)
(*   (b) replace_dead_per_layer and replace_all_layers preserve length      *)
(*       (already proved - see replace_dead_per_layer_preserves_length).    *)
(*   (c) Growth only comes from network_spawn_explorer, whose own lemma    *)
(*       (insert_at_layer_preserves_num_layers) already confirms the        *)
(*       number of layers is invariant under budding.                       *)
(******************************************************************************)

Lemma replace_if_dead_source_id :
  forall c source,
    replace_if_dead_source c source = c.
Proof.
  intros c source. unfold replace_if_dead_source. reflexivity.
Qed.

(* The whole per-layer repair phase is a no-op on cells under the new       *)
(* policy.  Useful as a rewriting lemma for any downstream proof that      *)
(* wants to "see through" replace_dead_per_layer.                           *)
Lemma replace_dead_per_layer_id :
  forall upper_consensus neighbor cells surps,
    replace_dead_per_layer upper_consensus neighbor cells surps = cells.
Proof.
  intros upper_consensus neighbor cells. revert upper_consensus neighbor.
  induction cells as [| c cs IH]; intros upper_consensus neighbor surps.
  - reflexivity.
  - simpl. rewrite replace_if_dead_source_id. f_equal.
    apply IH.
Qed.

(* And replace_all_layers is identity on layers.                            *)
Lemma replace_all_layers_id :
  forall layers preds surps,
    replace_all_layers layers preds surps = layers.
Proof.
  induction layers as [| L rest IH]; intros preds surps.
  - reflexivity.
  - simpl. destruct L as [| c0 crest].
    + f_equal. apply IH.
    + rewrite replace_dead_per_layer_id. f_equal. apply IH.
Qed.

(* Live cell stays live across the repair phase (trivially, because the    *)
(* repair phase is identity on cells).  Preserved for downstream callers   *)
(* that reference replace_if_dead_source_live_identity by name.             *)
Lemma replace_if_dead_source_live_identity :
  forall c source b',
    lpc_budget c = fs b' ->
    replace_if_dead_source c source = c.
Proof.
  intros c source _ _.
  apply replace_if_dead_source_id.
Qed.

(******************************************************************************)
(* PART 9b: TRUTH-PROP CASCADE PRESERVATION LEMMAS                            *)
(******************************************************************************)

Lemma cascade_truth_prop_preserves_length :
  forall layers inputs truth layers' preds surps,
    cascade_truth_prop layers inputs truth = (layers', preds, surps) ->
    length layers = length layers'.
Proof.
  induction layers as [| L rest IH]; intros inputs truth layers' preds surps Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - simpl in Heq.
    destruct (step_layer L inputs truth) as [[L' preds0] surps0] eqn:Estep.
    destruct (cascade_truth_prop rest (surprises_to_cascade_inputs surps0) truth)
      as [[rest' preds_rest] surps_rest] eqn:Erec.
    inversion Heq; subst.
    simpl. f_equal. eapply IH. exact Erec.
Qed.

Lemma cascade_truth_prop_preserves_layer_count :
  forall layers inputs truth layers' preds surps,
    cascade_truth_prop layers inputs truth = (layers', preds, surps) ->
    length surps = length layers.
Proof.
  induction layers as [| L rest IH]; intros inputs truth layers' preds surps Heq.
  - simpl in Heq. inversion Heq. reflexivity.
  - simpl in Heq.
    destruct (step_layer L inputs truth) as [[L' preds0] surps0] eqn:Estep.
    destruct (cascade_truth_prop rest (surprises_to_cascade_inputs surps0) truth)
      as [[rest' preds_rest] surps_rest] eqn:Erec.
    inversion Heq; subst.
    simpl. f_equal. eapply IH. exact Erec.
Qed.

(* E3: cascade_truth_prop passes truth unchanged to every layer.             *)
(* This is trivial by structural induction: truth never changes in the       *)
(* recursive call.  We state it as: the surps output has length = layers,   *)
(* and each step_layer call received the SAME truth argument.  Since this   *)
(* is baked into the Fixpoint definition itself, the strongest statement    *)
(* is the preservation lemma above plus the observation that truth is a     *)
(* parameter, not a computed value.  No separate lemma needed beyond E1/E2. *)

(******************************************************************************)
(* PART 10: CONCRETE WITNESS - 3 layers, 14 cells, educable starter         *)
(*                                                                            *)
(* Three layers.  Layer 0 has 8 cells, each expecting 3 raw inputs.  Layer *)
(* 1 has 4 cells, each expecting 8 inputs (one per layer-0 surprise).  Layer *)
(* 2 has 2 cells, each expecting 4 inputs (one per layer-1 surprise).       *)
(* Every starter cell has ASYMMETRIC nonzero weights (not zeros_fin), so   *)
(* lpc_predict can produce BTrue/BFalse and update_weights can actually    *)
(* fire.  The witness proves the N-layer network reduces end-to-end.        *)
(******************************************************************************)

(* f1..f8 and f16..f128 already defined in PART 0 above.                  *)

(* Learning rate 1/2.  Numerator = fs fz = 1, so update_weights fires with *)
(* a real adjustment per application (see lpc_learning_rate in             *)
(* void_predictive_learning.v).  The previous value (fz, fs fz) = 0/1      *)
(* froze weight updates entirely while keeping the network topologically    *)
(* alive - an easy semantic-vs-topological trap.                            *)
Definition starter_lr   : FinProb := half.
Definition starter_wmax : Fin     := f2.
(* Budget must be large enough to cover lpc_predict (accumulate_for +      *)
(* accumulate_against + two le_fin_b3) plus compute_surprise plus         *)
(* update_weights in a single tick.  With budget f8 the cell exhausts     *)
(* during predict and returns BUnknown, producing SurpriseUnknown only   *)
(* - the network never enters a learning state.  Raised to f128 so the   *)
(* learning window opens and we can observe actual weight updates.       *)
Definition starter_budget : Fin   := f128.

(* Width-scaled budget.  lpc_predict and update_weights both iterate over  *)
(* the input vector.  A 16-input cell burns roughly 8x the budget per tick *)
(* compared to a 3-input cell.  With a uniform starter_budget = f128 the   *)
(* 3-input layer 0 survived comfortably while every 16-input layer 1 cell  *)
(* exhausted its budget inside 4-5 ticks, producing the "death spiral"     *)
(* observed in tmp_depth_probe: L1 collapsed to all-dead, the cascade to   *)
(* L2+ degenerated to all-BUnknown, and any layer above L1 became         *)
(* structurally inert (0 directional surprises across the whole run).     *)
(*                                                                          *)
(* Width-scaled budget restores proportionality: wider inputs → bigger    *)
(* starting budget.  f1024 for 16-input (8x) and f512 for 8-input (4x)    *)
(* are chosen so that at XOR rates (~30-60 budget units per step for L1)  *)
(* every starter cell survives the full 12-step probe with margin.         *)
Definition starter_budget_16 : Fin := f1024.
Definition starter_budget_8  : Fin := f512.

(* 3-input starter: for=[2;1;0], against=[0;1;2]. Both directions live. *)
Definition base_cell_3 : LearningPredCell :=
  mkLPC [f2; f1; fz] [fz; f1; f2]
        starter_budget fz starter_lr starter_wmax.

(* Layer 0 diversity bank.  Eight distinct 3-input weight profiles so that *)
(* a given input triggers heterogeneous surprises across the layer.  With *)
(* a homogeneous layer (8x base_cell_3) the cascade to layer 1 sees the   *)
(* same signal eight times and there is no pattern to learn.  Diverse     *)
(* starters break that symmetry: on the same input some cells agree with *)
(* truth, some do not, and the mix is what the layer above can            *)
(* eventually fit.  Every profile respects lpc_weight_max = f2 and every *)
(* profile has at least one nonzero weight in both for and against       *)
(* directions (R3: no tabula rasa).                                       *)
Definition cell_3_pro_first : LearningPredCell :=
  mkLPC [f2; f1; fz] [fz; f1; f2]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_pro_third : LearningPredCell :=
  mkLPC [fz; f1; f2] [f2; f1; fz]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_middle : LearningPredCell :=
  mkLPC [f1; f2; f1] [f1; fz; f1]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_edges : LearningPredCell :=
  mkLPC [f1; fz; f1] [fz; f2; fz]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_outer : LearningPredCell :=
  mkLPC [f2; fz; f2] [fz; f2; fz]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_inner : LearningPredCell :=
  mkLPC [fz; f2; fz] [f2; fz; f2]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_all_for : LearningPredCell :=
  mkLPC [f2; f2; f2] [fz; fz; fs fz]
        starter_budget fz starter_lr starter_wmax.

Definition cell_3_all_against : LearningPredCell :=
  mkLPC [fz; fz; fs fz] [f2; f2; f2]
        starter_budget fz starter_lr starter_wmax.

Definition layer0_diverse : list LearningPredCell :=
  [ cell_3_pro_first
  ; cell_3_pro_third
  ; cell_3_middle
  ; cell_3_edges
  ; cell_3_outer
  ; cell_3_inner
  ; cell_3_all_for
  ; cell_3_all_against
  ].

(* 8-input starter.  Uses starter_budget_8 (4x f128) so 8-input cells in  *)
(* upper layers survive the full probe window.                             *)
Definition base_cell_8 : LearningPredCell :=
  mkLPC [f2; f1; fz; f1; f2; f1; fz; f1]
        [fz; f1; f2; f1; fz; f1; f2; f1]
        starter_budget_8 fz starter_lr starter_wmax.

(* 4-input starter. *)
Definition base_cell_4 : LearningPredCell :=
  mkLPC [f2; f1; fz; f1] [fz; f1; f2; f1]
        starter_budget fz starter_lr starter_wmax.

(* 16-input starter.  Required for layer 1 after the cascade doubling: *)
(* 8 cells in layer 0 produce 8 surprises, flattened to 16 Bool3 via  *)
(* surprises_to_cascade_inputs (direction + quality interleaved).     *)
(*                                                                     *)
(* Quality slots (odd positions 1,3,5,...,15) start at fz so the      *)
(* quality channel does not contribute to prediction at t=0 and does  *)
(* not interfere with directional signal.  Learning may populate      *)
(* quality weights later via update_weights firing on BTrue inputs   *)
(* at those positions.  Direction slots (even positions 0,2,...,14)  *)
(* carry the same [f2;f1;fz;f1] pattern as the original 8-wide cell, *)
(* repeated twice to span 16 inputs.                                  *)
Definition base_cell_16 : LearningPredCell :=
  mkLPC [f2; fz; f1; fz; fz; fz; f1; fz;
         f2; fz; f1; fz; fz; fz; f1; fz]
        [fz; fz; f1; fz; f2; fz; f1; fz;
         fz; fz; f1; fz; f2; fz; f1; fz]
        starter_budget_16 fz starter_lr starter_wmax.

(* Layer 1 diversity bank.  Four distinct 16-input profiles.  At least one *)
(* of them (cell_16_quality_reader) is systematically misaligned with the *)
(* cascade encoding - it places its starter weights at QUALITY slots     *)
(* (odd positions) instead of direction slots (even).  That cell will    *)
(* mispredict the direction signal and emit SurpriseFor/SurpriseAgainst, *)
(* triggering update_weights and actual learning at layer 1.             *)

(* (a) cell_16_direction_reader: same as base_cell_16.  Aligned. *)
Definition cell_16_direction_reader : LearningPredCell :=
  mkLPC [f2; fz; f1; fz; fz; fz; f1; fz;
         f2; fz; f1; fz; fz; fz; f1; fz]
        [fz; fz; f1; fz; f2; fz; f1; fz;
         fz; fz; f1; fz; f2; fz; f1; fz]
        starter_budget_16 fz starter_lr starter_wmax.

(* (b) cell_16_quality_reader: weights at odd positions, even zero.  This *)
(* cell "reads" quality as if it were direction - will be structurally   *)
(* wrong and forced to learn.                                             *)
Definition cell_16_quality_reader : LearningPredCell :=
  mkLPC [fz; f2; fz; f1; fz; fz; fz; f1;
         fz; f2; fz; f1; fz; fz; fz; f1]
        [fz; fz; fz; f1; fz; f2; fz; f1;
         fz; fz; fz; f1; fz; f2; fz; f1]
        starter_budget_16 fz starter_lr starter_wmax.

(* (c) cell_16_first_half_focus: weights only in first 8 positions (reads *)
(* only first 4 lower-layer cells).                                       *)
Definition cell_16_first_half_focus : LearningPredCell :=
  mkLPC [f2; fz; f1; fz; f2; fz; f1; fz;
         fz; fz; fz; fz; fz; fz; fz; fz]
        [fz; fz; f1; fz; fz; fz; f1; fz;
         fz; fz; fz; fz; fz; fz; fz; fz]
        starter_budget_16 fz starter_lr starter_wmax.

(* (d) cell_16_second_half_focus: weights only in last 8 positions (reads *)
(* only last 4 lower-layer cells).                                        *)
Definition cell_16_second_half_focus : LearningPredCell :=
  mkLPC [fz; fz; fz; fz; fz; fz; fz; fz;
         f2; fz; f1; fz; f2; fz; f1; fz]
        [fz; fz; fz; fz; fz; fz; fz; fz;
         fz; fz; f1; fz; fz; fz; f1; fz]
        starter_budget_16 fz starter_lr starter_wmax.

Definition layer1_diverse : list LearningPredCell :=
  [ cell_16_direction_reader
  ; cell_16_quality_reader
  ; cell_16_first_half_focus
  ; cell_16_second_half_focus
  ].

(* Layer-2+ diversity bank.  Four distinct 8-input profiles that ALL avoid  *)
(* the symmetric tie of base_cell_8.  base_cell_8 has weights_for and       *)
(* weights_against summing to identical totals at the cascade-typical input *)
(* (BFalse, BTrue, BFalse, BTrue, BFalse, BTrue, BFalse, BTrue) - emitted   *)
(* when the lower layer fires SurpriseAgainst on all four cells.  At that   *)
(* input acc_f = 4 = acc_a, lpc_predict returns BUnknown, the surprise is   *)
(* SurpriseUnknown, and update_weights is a no-op.  Four identical          *)
(* base_cell_8s freeze together forever.  These four profiles each break    *)
(* the symmetry asymmetrically so at least two cells produce a directional  *)
(* prediction on that input.                                                 *)
(*                                                                            *)
(* Verified analytically against input (F,T,F,T,F,T,F,T):                    *)
(*   (a) cell_8_quality_for_heavy:  acc_f=8 acc_a=2  -> BTrue                *)
(*   (b) cell_8_dir_against_heavy:  acc_f=2 acc_a=8  -> BFalse               *)
(*   (c) cell_8_first_half_for:     acc_f=4 acc_a=2  -> BTrue                *)
(*   (d) cell_8_second_half_against:acc_f=2 acc_a=4  -> BFalse               *)
(* Two predict BTrue, two predict BFalse.  Whatever the cascaded truth from *)
(* below, at least two cells produce SurpriseFor or SurpriseAgainst, so     *)
(* update_weights fires and the layer can learn.  All four respect          *)
(* lpc_weight_max = f2 and have at least one nonzero weight in both for    *)
(* and against (R3: no tabula rasa).                                         *)

(* (a) Quality bits dominate prediction.  Heavy positive weights at odd    *)
(* (quality) positions.  When the lower layer fires anything non-Unknown   *)
(* (NoSurprise / SurpriseFor / SurpriseAgainst), all quality bits = BTrue, *)
(* and this cell predicts BTrue strongly.                                   *)
Definition cell_8_quality_for_heavy : LearningPredCell :=
  mkLPC [fz; f2; fz; f2; fz; f2; fz; f2]
        [fs fz; fz; fz; fz; fs fz; fz; fz; fz]
        starter_budget_8 fz starter_lr starter_wmax.

(* (b) Direction bits going BFalse drive prediction BFalse.  Mirror of (a). *)
(* Heavy negative (against) weights at even (direction) positions.  When    *)
(* lower cells fire SurpriseAgainst, dir bits = BFalse and this cell        *)
(* predicts BFalse.                                                          *)
Definition cell_8_dir_against_heavy : LearningPredCell :=
  mkLPC [fz; fs fz; fz; fz; fz; fs fz; fz; fz]
        [f2; fz; f2; fz; f2; fz; f2; fz]
        starter_budget_8 fz starter_lr starter_wmax.

(* (c) Focus on first half (lower cells 0,1).  Strong for-bias on first 4  *)
(* positions, weak against-bias on last 4.                                  *)
Definition cell_8_first_half_for : LearningPredCell :=
  mkLPC [f2; f2; f2; f2; fz; fz; fz; fz]
        [fz; fz; fz; fz; fs fz; fz; fs fz; fz]
        starter_budget_8 fz starter_lr starter_wmax.

(* (d) Focus on second half (lower cells 2,3).  Mirror of (c).             *)
Definition cell_8_second_half_against : LearningPredCell :=
  mkLPC [fz; fz; fz; fz; fs fz; fz; fs fz; fz]
        [fz; fz; fz; fz; f2; f2; f2; f2]
        starter_budget_8 fz starter_lr starter_wmax.

Definition layer_deep_diverse : list LearningPredCell :=
  [ cell_8_quality_for_heavy
  ; cell_8_dir_against_heavy
  ; cell_8_first_half_for
  ; cell_8_second_half_against
  ].

(* Replicate a cell n times (Fin n). *)
Fixpoint replicate_cell (n : Fin) (c : LearningPredCell)
  : list LearningPredCell :=
  match n with
  | fz    => []
  | fs n' => c :: replicate_cell n' c
  end.

(* Cascade doubles the width of the input vector from layer k to layer   *)
(* k+1 because each lower cell contributes both a direction bit and a    *)
(* quality bit.  So layer 1 cells now see 16 inputs (8 lower cells * 2) *)
(* and layer 2 cells see 8 inputs (4 lower cells * 2).                   *)
(*                                                                         *)
(* Layer 0 uses layer0_diverse: 8 distinct weight profiles so the layer  *)
(* produces heterogeneous surprises and the cascade to layer 1 carries   *)
(* structure instead of a homogeneous signal.                            *)
Definition starter_net : Network :=
  mkNet RegimeAnySurprise
    [ layer0_diverse                     (* layer 0: 8 cells,  3-input  *)
    ; layer1_diverse                     (* layer 1: 4 cells, 16-input  *)
    ; replicate_cell f2 base_cell_8      (* layer 2: 2 cells,  8-input  *)
    ].

Example starter_net_layer_count :
  length (net_layers starter_net) = 3.
Proof. reflexivity. Qed.

Example starter_net_layer0_count :
  length (nth 0 (net_layers starter_net) []) = 8.
Proof. reflexivity. Qed.

Example starter_net_layer1_count :
  length (nth 1 (net_layers starter_net) []) = 4.
Proof. reflexivity. Qed.

Example starter_net_layer2_count :
  length (nth 2 (net_layers starter_net) []) = 2.
Proof. reflexivity. Qed.
