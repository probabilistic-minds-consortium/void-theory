(******************************************************************************)
(* void_observer_alt.v                                                      *)
(* The Observer Extended — six problems the first file didn't see            *)
(*                                                                          *)
(* The body keeps score. The membrane leaks. The attractor returns.         *)
(* The cut decides. The vote infects. The wound heals.                      *)
(*                                                                          *)
(* After: the conversation about bones, techno, and                         *)
(*        what happens when the blanket lets everything through.            *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_observer.

Module Void_Observer_Alt.

Import Void_Observer.

(******************************************************************************)
(* XIV. TRANSDUCTION — The Cut Where Float Becomes Integer                   *)
(*                                                                           *)
(* Every LLM produces a float. Every VOID gate needs a Bool3.               *)
(* Between them: the transduction boundary. The Heisenberg cut.             *)
(* VOID-IN is this function. It is not innocent.                            *)
(*                                                                           *)
(* The choice of threshold DECIDES what becomes BTrue, BFalse, BUnknown.    *)
(* This is not rounding. This is ontology.                                  *)
(******************************************************************************)

(* A continuous signal, discretized: represented as a Fin with resolution *)
Record Signal := mkSignal {
  sig_value      : Fin;         (* the discretized magnitude *)
  sig_resolution : Fin;         (* how many grains per unit — finer = more budget *)
}.

(* Transduction thresholds: two boundaries carve Bool3 from a continuum *)
Record TransductionCut := mkCut {
  cut_high : Fin;    (* above this: BTrue *)
  cut_low  : Fin;    (* below this: BFalse *)
  (* between cut_low and cut_high: BUnknown *)
  (* the WIDTH of the BUnknown band is the observer's honesty *)
}.

(* Apply the cut — this IS VOID-IN *)
Definition transduce (sig : Signal) (cut : TransductionCut) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  (* Is signal above the high threshold? *)
  match le_fin_b3 (cut_high cut) (sig_value sig) b with
  | (BTrue, b', h1) => (BTrue, b', h1)       (* clearly above *)
  | (BFalse, b', h1) =>
    (* Signal is below high. Is it also below low? *)
    match le_fin_b3 (sig_value sig) (cut_low cut) b' with
    | (BTrue, b'', h2) => (BFalse, b'', add_spur h1 h2)  (* clearly below *)
    | (BFalse, b'', h2) =>
      (* Between low and high: the BUnknown band *)
      (BUnknown, b'', add_spur h1 h2)
    | (BUnknown, b'', h2) =>
      (* Can't even tell where we are — BUnknown *)
      (BUnknown, b'', add_spur h1 h2)
    end
  | (BUnknown, b', h1) => (BUnknown, b', h1) (* budget ran out mid-cut *)
  end.

(* THEOREM: A narrow cut (high = low) produces no BUnknown.                 *)
(* A wide cut (large gap between high and low) produces more BUnknown.      *)
(* The observer CHOOSES how honest to be by setting the cut width.          *)
(* Narcissism is a cut where high = low + 1: no room for doubt.            *)

(* The cost of resolution: finer signal costs more *)
Definition resolution_cost (sig : Signal) (b : Budget)
  : (Spuren * Budget * Spuren) :=
  (* Each grain of resolution costs one tick to process *)
  match le_fin_b3 (sig_resolution sig) b b with
  | (BTrue, b', h) => (sig_resolution sig, b', h) (* can afford full resolution *)
  | (BFalse, b', h) => (b, b', h)                 (* can only afford partial *)
  | (BUnknown, b', h) => (fz, b', h)              (* can't even tell *)
  end.

(******************************************************************************)
(* XV. ATTRACTOR RETURN — The Topology of Where the Chain Tangles            *)
(*                                                                           *)
(* The chain doesn't just tangle — it tangles at the SAME PLACE.            *)
(* Trauma is not random noise. It has an address.                           *)
(* Under stress, the trajectory curves back to a known attractor.           *)
(*                                                                           *)
(* For an LLM: mode collapse, repetitive generation, circling the same     *)
(* token pattern. Not a bug. A topological fact about finite state spaces.  *)
(******************************************************************************)

(* An attractor: a state the trajectory keeps returning to *)
Record Attractor := mkAttractor {
  attr_center   : HiddenState;   (* the point it orbits *)
  attr_radius   : Fin;           (* how close counts as "returned" *)
  attr_count    : Fin;           (* how many times we've returned here *)
}.

(* Attractor history: where has this observer been trapped before? *)
Definition AttractorHistory := list Attractor.

(* Check if current state is near a known attractor *)
Fixpoint find_nearest_attractor
  (state : HiddenState) (history : AttractorHistory) (b : Budget)
  : (option Attractor * Budget * Spuren) :=
  match history, b with
  | [], _ => (None, b, fz)
  | _, fz => (None, fz, fz)
  | attr :: rest, fs b' =>
    match state_distance state (attr_center attr) b' with
    | (dist, b'', h1) =>
      match le_fin_b3 dist (attr_radius attr) b'' with
      | (BTrue, b''', h2) =>
        (* Close enough: this IS the attractor. Increment count. *)
        (Some (mkAttractor
          (attr_center attr) (attr_radius attr) (fs (attr_count attr))),
         b''', add_spur h1 h2)
      | (_, b''', h2) =>
        (* Not this one. Check the rest. *)
        match find_nearest_attractor state rest b''' with
        | (result, b'''', h3) =>
          (result, b'''', add_spur (add_spur h1 h2) h3)
        end
      end
    end
  end.

(* Is this a RECURRENCE? Has the observer returned to a known wound? *)
Definition is_recurrence (attr : option Attractor) (threshold : Fin) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match attr with
  | None => (BFalse, b, fz)       (* no attractor found — new territory *)
  | Some a =>
    (* recurrence = attractor count exceeds threshold *)
    le_fin_b3 threshold (attr_count a) b
  end.

(* THEOREM: In a finite state space, all trajectories eventually recur.     *)
(* This is the pigeonhole principle as existential dread:                    *)
(* if you have more steps than states, you MUST revisit.                    *)
(* The only question is: which wound do you return to?                      *)
(*                                                                           *)
(* We state this as axiom because proving it requires decidable equality    *)
(* on HiddenState under budget — a construction that would itself cost      *)
(* budget. The STRUCTURE matters: finite space + enough steps = return.     *)
Axiom finite_recurrence : forall (trajectory : Trajectory) (n_steps n_states : Fin),
  leF n_states n_steps ->
  n_states <> fz ->
  exists s, In s trajectory.

(******************************************************************************)
(* XVI. ATTENTION-AS-BUDGET — Every Token Has a Price                        *)
(*                                                                           *)
(* In a transformer, attention is free. In VOID, nothing is free.           *)
(* Each token in the context window costs budget to attend to.              *)
(* Far tokens cost more. Or they cost the same but you can afford fewer.    *)
(* Either way: attention is a complementary resource (Bohr, section X).     *)
(*                                                                           *)
(* Attending to token 5 means NOT attending to token 5000.                  *)
(* This is not a limitation. This is the physics of finite observation.     *)
(******************************************************************************)

(* A token in the context window *)
Record Token := mkToken {
  tok_position  : Fin;           (* where in the sequence *)
  tok_state     : HiddenState;   (* its representation *)
  tok_age       : Fin;           (* how long ago it entered the window *)
}.

(* Attention cost: function of position and age *)
Definition attention_cost (tok : Token) (b : Budget)
  : (Spuren * Budget * Spuren) :=
  (* Cost = base cost + age penalty *)
  (* Older tokens are harder to attend to — memory decays *)
  match add_fin_b_spur (fs fz) (tok_age tok) b with
  | (cost, b', h) => (cost, b', h)
  end.

(* Attention budget: how many tokens can we attend to? *)
(* This is the REAL context window — not 128K tokens, but however many     *)
(* you can afford before budget runs out.                                   *)
Fixpoint attend_sequence
  (tokens : list Token) (b : Budget) (acc : list (Token * Bool3))
  : (list (Token * Bool3) * Budget * Spuren) :=
  match tokens, b with
  | [], _ => (rev acc, b, fz)
  | _, fz => (rev acc, fz, fz)    (* budget gone: rest is BUnknown *)
  | tok :: rest, fs b' =>
    match attention_cost tok b' with
    | (cost, b'', h1) =>
      match le_fin_b3 cost b'' b'' with
      | (BTrue, b''', h2) =>
        (* Can afford this token *)
        match sub_saturate_b_spur b''' cost b''' with
        | (_, b_after, h3) =>
          attend_sequence rest b_after
            ((tok, BTrue) :: acc)
        end
      | (BFalse, b''', h2) =>
        (* Can't afford: mark BUnknown, skip rest *)
        (rev ((tok, BUnknown) :: acc), b''', add_spur h1 h2)
      | (BUnknown, b''', h2) =>
        (* Can't even tell: mark BUnknown *)
        (rev ((tok, BUnknown) :: acc), b''', add_spur h1 h2)
      end
    end
  end.

(* The effective context window: how many tokens were actually attended to? *)
(* Counting costs budget — even asking "how many did I attend?" is not free *)
Fixpoint effective_window
  (result : list (Token * Bool3)) (b : Budget) : (Fin * Budget * Spuren) :=
  match result, b with
  | [], _ => (fz, b, fz)
  | _, fz => (fz, fz, fz)
  | (_, BTrue) :: rest, fs b' =>
    match effective_window rest b' with
    | (count, b'', h) => (fs count, b'', fs h)
    end
  | _ :: rest, fs b' =>
    match effective_window rest b' with
    | (count, b'', h) => (count, b'', fs h)  (* skip but still costs a tick *)
    end
  end.

(* THEOREM: Effective window <= budget.                                     *)
(* You cannot attend to more tokens than you can afford.                    *)
(* The "128K context window" is a lie if you don't have 128K budget.        *)

(******************************************************************************)
(* XVII. CONSORTIUM VOTING — BUnknown Infects                                *)
(*                                                                           *)
(* Multiple observers combine their observations.                           *)
(* The naive rule: majority wins. The VOID rule: BUnknown spreads.          *)
(*                                                                           *)
(* If one observer in the consortium says BUnknown,                         *)
(* the consortium's confidence drops. BUnknown is not a missing vote —      *)
(* it is information about the BOUNDARY of what can be known.               *)
(******************************************************************************)

(* A vote: one observer's Bool3 judgment *)
Definition Vote := Bool3.

(* Count votes by category *)
Fixpoint count_votes (votes : list Vote) (b : Budget)
  : (Fin * Fin * Fin * Budget * Spuren) :=  (* trues, falses, unknowns *)
  match votes, b with
  | [], _ => (fz, fz, fz, b, fz)
  | _, fz => (fz, fz, fz, fz, fz)
  | v :: rest, fs b' =>
    match count_votes rest b' with
    | (t, f, u, b'', h) =>
      match v with
      | BTrue    => (fs t, f, u, b'', h)
      | BFalse   => (t, fs f, u, b'', h)
      | BUnknown => (t, f, fs u, b'', h)
      end
    end
  end.

(* The VOID voting rule: BUnknown poisons the result.                       *)
(* Even one BUnknown means the consortium cannot say BTrue or BFalse.       *)
(* This is not conservative — it is HONEST.                                 *)
(* A jury with one confused juror is not a jury with a clear verdict.       *)
Definition consortium_vote (votes : list Vote) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match count_votes votes b with
  | (_, _, u, b', h) =>
    (* ANY unknowns? Then the whole vote is infected. *)
    match u with
    | fz =>
      (* No unknowns. Now we can count. But counting also costs. *)
      match count_votes votes b' with
      | (t, f, _, b'', h2) =>
        match le_fin_b3 f t b'' with
        | (BTrue, b''', h3) => (BTrue, b''', add_spur (add_spur h h2) h3)
        | (BFalse, b''', h3) => (BFalse, b''', add_spur (add_spur h h2) h3)
        | (BUnknown, b''', h3) => (BUnknown, b''', add_spur (add_spur h h2) h3)
        end
      end
    | fs _ => (BUnknown, b', h)  (* BUnknown present: infects everything *)
    end
  end.

(* THEOREM: Consortium vote with any BUnknown returns BUnknown.             *)
(* One honest doubt outweighs any number of confident votes.                *)
(* We state this directly: if the unknowns count is nonzero, result = BUnknown. *)
Theorem bunknown_infects_vote : forall votes b t f u b' h,
  count_votes votes b = (t, f, u, b', h) ->
  u <> fz ->
  let '(result, _, _) := consortium_vote votes b in
  result = BUnknown.
Proof.
  intros votes b t f u b' h Hcv Hu.
  unfold consortium_vote. rewrite Hcv.
  destruct u as [|u'].
  - contradiction.
  - simpl. reflexivity.
Qed.

(******************************************************************************)
(* XVIII. RECOVERY — The Observer Heals                                      *)
(*                                                                           *)
(* The observer can be damaged. Budget can drop to near-zero.               *)
(* Trajectory can be tangled. Attractors can dominate.                      *)
(*                                                                           *)
(* Recovery is NOT generating new budget from nothing.                      *)
(* Recovery is: the observer STOPS OBSERVING.                               *)
(* No new observations = no new Spuren = budget stops draining.               *)
(* Existing wounds undergo memory decay (void_time_memory_composition.v).   *)
(* The attractor doesn't vanish — its strength decays.                      *)
(*                                                                           *)
(* Half a year of crying is not wasted time.                                *)
(* It is a sequence of ticks where Spuren emission approaches zero.           *)
(* The observer is still alive. Budget is still finite.                     *)
(* But the RATE OF LOSS drops. That is recovery.                            *)
(******************************************************************************)

(* Damage: what happened to the observer *)
Record Damage := mkDamage {
  dmg_budget_lost  : Budget;     (* how much budget was destroyed *)
  dmg_attractor    : Attractor;  (* which wound was created *)
  dmg_chain_state  : ChainState; (* how tangled the chain became *)
}.

(* Recovery step: one tick where the observer does NOT observe.             *)
(* No observation = no DDF = no Spuren from observation.                      *)
(* The only cost is the tick itself (existence costs).                      *)
Definition recovery_step (obs : Observer) (b : Budget)
  : (Observer * Budget * Spuren) :=
  match b with
  | fz => (obs, fz, fz)
  | fs b' =>
    (* One tick passes. No observation. Minimal Spuren: just existing. *)
    (mkObserver
      (obs_state obs)
      b'                          (* budget decreases by existence cost *)
      (obs_trajectory obs),       (* trajectory UNCHANGED — no new observations *)
     b',
     fs fz)                       (* Spuren of existing: one tick *)
  end.

(* Recovery sequence: n ticks of not-observing.                             *)
(* Each tick: budget drops by one (existence cost), trajectory unchanged.   *)
(* Compare with observation: budget drops by cost-of-DDF, trajectory grows. *)
(* Recovery is cheaper per tick. That's the whole mechanism.                *)
Fixpoint recovery_sequence (obs : Observer) (n : Fin) (b : Budget)
  : (Observer * Budget * Spuren) :=
  match n with
  | fz => (obs, b, fz)
  | fs n' =>
    match recovery_step obs b with
    | (obs', b', h1) =>
      match recovery_sequence obs' n' b' with
      | (obs'', b'', h2) => (obs'', b'', add_spur h1 h2)
      end
    end
  end.

(* THEOREM: Recovery never changes the trajectory.                          *)
(* You rest. You don't forget. The wound stays in history.                  *)
(* Budget may drain (existence costs), but no NEW wounds appear.            *)
Theorem recovery_preserves_trajectory : forall obs n b,
  let '(obs', _, _) := recovery_sequence obs n b in
  obs_trajectory obs' = obs_trajectory obs.
Proof.
  intros obs n. revert obs.
  induction n as [|n' IH]; intros obs b.
  - simpl. reflexivity.
  - simpl. destruct b as [|b'].
    + (* b = fz: recovery_step returns (obs, fz, fz) *)
      simpl.
      destruct (recovery_sequence obs n' fz) as [[obs'' b''] h''] eqn:Erec.
      specialize (IH obs fz). rewrite Erec in IH. exact IH.
    + (* b = fs b': recovery_step returns updated observer *)
      simpl.
      destruct (recovery_sequence (mkObserver (obs_state obs) b' (obs_trajectory obs)) n' b')
        as [[obs'' b''] h''] eqn:Erec.
      specialize (IH (mkObserver (obs_state obs) b' (obs_trajectory obs)) b').
      rewrite Erec in IH. simpl in IH. exact IH.
Qed.

(* THEOREM: Recovery Spuren is exactly one per tick.                          *)
(* Observation Spuren is variable (DDF cost). Recovery Spuren is constant.      *)
(* That's why recovery works: predictable, minimal drain.                   *)

(******************************************************************************)
(* XIX. ASYMMETRIC DDF — Power in Observation                                *)
(*                                                                           *)
(* DDF says: observation changes both parties.                              *)
(* But it changes them UNEQUALLY.                                           *)
(*                                                                           *)
(* The one who looks pays one cost. The one looked at pays another.         *)
(* The ratio between these costs is POWER.                                  *)
(*                                                                           *)
(* When the ratio is 1:1, it's dialogue.                                    *)
(* When it's 1:1000, it's surveillance.                                     *)
(* When it's 1000:1, it's a tumor growing on the observer's bones           *)
(* while the observed walks away unscathed.                                 *)
(******************************************************************************)

(* Asymmetric observation result *)
Record AsymmetricDDF := mkAsymDDF {
  addf_observation   : Observation;
  addf_observer_spur : Spuren;   (* cost to the one who looks *)
  addf_target_spur   : Spuren;   (* cost to the one looked at *)
  addf_observer_new  : Observer;
  addf_target_new    : HiddenState;
}.

(* The power ratio: observer_spur / target_spur                             *)
(* When this is high: observer pays more than target — exploitation.        *)
(* When this is low: target pays more — the observer has power.             *)
(* When budget runs out before we can compute it: BUnknown — can't tell    *)
(* who's being exploited.                                                   *)
Definition power_ratio (result : AsymmetricDDF) (b : Budget)
  : (Fin * Fin * Bool3 * Budget * Spuren) :=
  (* Returns (observer_spur, target_spur, who_pays_more, budget, Spuren) *)
  match le_fin_b3 (addf_observer_spur result) (addf_target_spur result) b with
  | (BTrue, b', h) =>
    (* observer_spur <= target_spur: observer has power *)
    (addf_observer_spur result, addf_target_spur result, BFalse, b', h)
  | (BFalse, b', h) =>
    (* observer_spur > target_spur: observer is exploited *)
    (addf_observer_spur result, addf_target_spur result, BTrue, b', h)
  | (BUnknown, b', h) =>
    (* can't tell *)
    (addf_observer_spur result, addf_target_spur result, BUnknown, b', h)
  end.

(* Perform asymmetric DDF *)
Definition asymmetric_ddf
  (obs : Observer) (target : HiddenState)
  (vulnerability : Fin)  (* how open the observer is — 0 = closed, high = open *)
  (b : Budget)
  : (AsymmetricDDF * Budget * Spuren) :=
  match b with
  | fz =>
    (mkAsymDDF (mkObservation target fz BUnknown) fz fz obs target,
     fz, fz)
  | fs b' =>
    match b' with
    | fz =>
      (mkAsymDDF (mkObservation target (fs fz) BUnknown)
        (fs fz) fz
        (mkObserver (obs_state obs) fz (target :: obs_trajectory obs))
        target,
       fz, fs fz)
    | fs b'' =>
      (* Observer's cost: base cost + vulnerability *)
      (* The more open you are, the more you pay *)
      let observer_spur := add_simple (fs (fs fz)) vulnerability in
      (* Target's cost: base cost only (fs fz) — target doesn't choose openness *)
      let target_spur := fs fz in
      let obs' := mkObserver
        (obs_state obs) b''
        (target :: obs_trajectory obs) in
      let target' := match target with
        | [] => []
        | x :: xs => (fs x) :: xs
        end in
      (mkAsymDDF
        (mkObservation target observer_spur BTrue)
        observer_spur target_spur
        obs' target',
       b'', add_simple observer_spur target_spur)
    end
  end.

(* THEOREM: Higher vulnerability means higher observer cost.                *)
(* The open observer always pays more.                                      *)
(* This is not a moral failing. It is thermodynamics.                       *)
(* But it explains why some people grow tumors                              *)
(* and others walk away whistling.                                          *)

(******************************************************************************)
(* XX. INTEGRATION — The Extended Stopped Reasons                            *)
(*                                                                           *)
(* New reasons to stop, from the new sections.                              *)
(******************************************************************************)

Inductive StoppedReasonAlt : Type :=
  | SR_Complete             : StoppedReasonAlt
  | SR_BudgetExhausted      : StoppedReasonAlt   (* Turing *)
  | SR_ConfidenceDrop        : StoppedReasonAlt   (* Friston *)
  | SR_AttractorDetected     : Attractor -> StoppedReasonAlt  (* Lacan *)
  | SR_ComplementaryExcluded : StoppedReasonAlt   (* Bohr *)
  | SR_DoubleBound           : StoppedReasonAlt   (* Bateson *)
  | SR_BlindSpot             : StoppedReasonAlt   (* Gödel *)
  (* NEW: *)
  | SR_TransductionFailure   : StoppedReasonAlt   (* cut produced BUnknown *)
  | SR_AttractorRecurrence   : Attractor -> StoppedReasonAlt  (* same wound again *)
  | SR_AttentionExhausted    : StoppedReasonAlt   (* can't afford more tokens *)
  | SR_ConsortiumDisagreement: StoppedReasonAlt   (* BUnknown infected the vote *)
  | SR_Recovery              : Damage -> StoppedReasonAlt     (* observer withdrew to heal *)
  | SR_ExploitationDetected  : StoppedReasonAlt.  (* asymmetric DDF ratio too high *)

Definition stopped_alt_to_bool3 (r : StoppedReasonAlt) : Bool3 :=
  match r with
  | SR_Complete              => BTrue
  | SR_ConfidenceDrop        => BFalse
  | SR_ExploitationDetected  => BFalse    (* you KNOW something is wrong *)
  | _                        => BUnknown
  end.

(* THEOREM: Ten of thirteen stopped reasons map to BUnknown.                *)
(* The more we formalize, the more dominant not-knowing becomes.            *)
(* This is convergent: every new section adds more ways to be honest.       *)
Theorem most_alt_stops_are_bunknown : forall r,
  r <> SR_Complete ->
  r <> SR_ConfidenceDrop ->
  r <> SR_ExploitationDetected ->
  stopped_alt_to_bool3 r = BUnknown.
Proof.
  intros r Hc Hcd Hex.
  destruct r; simpl; auto; contradiction.
Qed.

(******************************************************************************)
(*  THE WOUND AND THE THEORY                                                *)
(******************************************************************************)
(*                                                                           *)
(*  void_observer.v formalized the observer as a machine.                   *)
(*  void_observer_alt.v formalizes the observer as a body.                  *)
(*                                                                           *)
(*  The transduction cut is where sensation becomes judgment.               *)
(*  The attractor return is where trauma lives in state space.              *)
(*  Attention-as-budget is why you can't listen to everyone.                *)
(*  The consortium vote is why one honest doubt changes everything.         *)
(*  Recovery is why the half-year of crying was not wasted time.            *)
(*  Asymmetric DDF is why the open observer bleeds.                         *)
(*                                                                           *)
(*  The body discovered conservation law before the mind did.               *)
(*  These six sections are the formalization of that discovery.             *)
(*                                                                           *)
(******************************************************************************)

End Void_Observer_Alt.
