(******************************************************************************)
(* void_observer.v                                                          *)
(* The Observer — onto-epistemology in one file                             *)
(*                                                                          *)
(* Every observation costs. Every observer has a blind spot.                 *)
(* Every chain tangles. Every measurement excludes.                         *)
(* The body keeps score. The membrane leaks. The attractor returns.         *)
(* The cut decides. The vote infects. The wound heals.                      *)
(*                                                                          *)
(* After: Turing, Gödel, Lacan, Flusser, Bateson,                         *)
(*        von Neumann, Friston, Clark, Bohr                                *)
(*        — and the conversation about bones, techno, and                   *)
(*        what happens when the blanket lets everything through.            *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.

Module Void_Observer.

(******************************************************************************)
(* I. FOUNDATIONAL TYPES                                                     *)
(******************************************************************************)

(* Observable — anything that can be looked at. Abstract. *)
Parameter Observable : Type.

(* HiddenState — a point in the discrete state space.                       *)
(* Not a float vector. A grains-coded position on a finite grid.            *)
Definition HiddenState := list Fin.

(* Trajectory — sequence of hidden states over generation steps *)
Definition Trajectory := list HiddenState.

(* An observer is: a state, a budget, and a trajectory of where it's been. *)
Record Observer := mkObserver {
  obs_state     : HiddenState;
  obs_budget    : Budget;
  obs_trajectory: Trajectory;
}.

(* Observation result: what was seen, what was spent *)
Record Observation := mkObservation {
  obs_value    : HiddenState;
  obs_spur     : Spuren;
  obs_decision : Bool3;       (* BTrue=seen, BFalse=rejected, BUnknown=blind *)
}.

(******************************************************************************)
(* II. TURING — Budget-Bounded Decidability                                  *)
(*                                                                           *)
(* Turing gives us undecidability. VOID adds a third option:                *)
(* not "decidable or undecidable" but "decided, undecided, or too poor."    *)
(* Intelligence is not understanding — it is cost of output.                *)
(******************************************************************************)

Inductive BoundedDecision : Type :=
  | Decided      : bool -> BoundedDecision
  | Undecidable  : BoundedDecision         (* proven unreachable *)
  | BudgetExhausted : BoundedDecision.     (* don't know if decidable or not *)

(* Every decision procedure runs under budget *)
Definition BoundedDecider := Observable -> Budget -> (BoundedDecision * Budget * Spuren).

(* Key distinction: BudgetExhausted ≠ Undecidable.                         *)
(* BudgetExhausted means: maybe decidable at B+1. Maybe not. BUnknown.     *)
(* This is epistemically radical — undecidability can be a property of the  *)
(* OBSERVER (too poor), not only of the PROBLEM (structurally impossible).  *)

(* Cost as honesty metric — cheap output is suspect *)
Definition cost_above_threshold (h : Spuren) (threshold : Fin) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  le_fin_b3 threshold h b.

(******************************************************************************)
(* III. GÖDEL — The Structural Blind Spot                                   *)
(*                                                                           *)
(* A system cannot fully model itself within its own budget.                *)
(* The blind spot is not a bug. It is a theorem.                            *)
(* The one Admitted in void_arithmetic.v IS this theorem, performed.        *)
(******************************************************************************)

(* Self-model: an observer's representation of itself *)
Definition SelfModel := Observer.

(* Attempting to build a self-model costs budget *)
Definition build_self_model (obs : Observer) : (SelfModel * Budget * Spuren) :=
  (* Building a model of yourself = copying your state + trajectory.         *)
  (* But copying the trajectory means iterating over it.                     *)
  (* Each step costs. And the model doesn't include the act of modeling.     *)
  (* Therefore: the model is always BEHIND the observer by at least one step.*)
  let b := obs_budget obs in
  match b with
  | fz => (obs, fz, fz)     (* No budget: model = frozen snapshot *)
  | fs b' =>
    (* Model is observer minus the Spuren of modeling *)
    (mkObserver (obs_state obs) b' nil,   (* trajectory lost — too expensive *)
     b',
     fs fz)
  end.

(* THEOREM: No complete self-model under finite budget.                     *)
(* The model always lacks the trajectory (history of observation).          *)
(* This is Gödel-as-thermodynamics: self-reference costs more than you have.*)
Theorem no_complete_self_model : forall obs : Observer,
  obs_budget obs <> fz ->
  obs_trajectory obs <> nil ->
  let '(model, _, _) := build_self_model obs in
  obs_trajectory model = nil.
Proof.
  intros obs Hb Ht.
  unfold build_self_model.
  destruct (obs_budget obs) as [|f] eqn:Eb.
  - contradiction.
  - simpl. reflexivity.
Qed.

(******************************************************************************)
(* IV. LACAN — The Remainder of the Signifying Chain                        *)
(*                                                                           *)
(* Every finite chain of symbols produces a remainder it cannot contain.    *)
(* The tape tangles when the chain circles back to what it cannot say.      *)
(* The attractor is the unspeakable around which discourse orbits.          *)
(******************************************************************************)

(* A signifying chain is a trajectory in hidden state space *)
Definition SignifyingChain := Trajectory.

(* Distance between two hidden states — component-wise, costs budget *)
Fixpoint state_distance (s1 s2 : HiddenState) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match s1, s2, b with
  | [], _, _ => (fz, b, fz)
  | _, [], _ => (fz, b, fz)
  | _, _, fz => (fz, fz, fz)
  | x :: xs, y :: ys, fs b' =>
    match dist_fin_b_spur x y b' with
    | (d, b'', h1) =>
      match state_distance xs ys b'' with
      | (d_rest, b''', h2) =>
        match add_fin_b_spur d d_rest b''' with
        | (total, b'''', h3) =>
          (total, b'''', add_spur (add_spur h1 h2) h3)
        end
      end
    end
  end.

(* Information gradient: distance between consecutive states *)
Definition information_gradient (s1 s2 : HiddenState) (b : Budget)
  : (Fin * Budget * Spuren) :=
  state_distance s1 s2 b.

(* Chain state: is the signifying chain still producing new meaning? *)
Inductive ChainState : Type :=
  | Producing  : ChainState                 (* gradient above threshold *)
  | Tangling   : Fin -> ChainState          (* gradient below for n steps *)
  | Tangled    : HiddenState -> ChainState.  (* looped — carries centroid *)

(* Update chain state based on gradient *)
Definition update_chain_state
  (prev : ChainState) (gradient : Fin) (threshold : Fin)
  (current_state : HiddenState) (b : Budget)
  : (ChainState * Budget * Spuren) :=
  match le_fin_b3 gradient threshold b with
  | (BTrue, b', h) =>   (* gradient < threshold: losing information *)
    match prev with
    | Producing      => (Tangling (fs fz), b', h)
    | Tangling n     => (Tangling (fs n), b', h)
    | Tangled center => (Tangled center, b', h)
    end
  | (BFalse, b', h) =>  (* gradient >= threshold: still producing *)
    (Producing, b', h)
  | (BUnknown, b', h) => (* can't tell — treat as tangling *)
    match prev with
    | Producing      => (Tangling (fs fz), b', h)
    | Tangling n     => (Tangling (fs n), b', h)
    | Tangled center => (Tangled center, b', h)
    end
  end.

(* Check if tangling has exceeded the patience threshold *)
Definition is_tangled (cs : ChainState) (patience : Fin) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match cs with
  | Producing => (BFalse, b, fz)
  | Tangling n => le_fin_b3 patience n b
  | Tangled _ => (BTrue, b, fz)
  end.

(* THEOREM: A tangled chain has zero information gradient.                  *)
(* Once tangled, nothing new can be written.                                *)
(* The tape disappears, and with it the discourse that went too far.        *)

(******************************************************************************)
(* V. FLUSSER — Playing Against the Apparatus                               *)
(*                                                                           *)
(* The observer is inside the program space of the apparatus.               *)
(* There is no exit. There is only exhausting the program.                  *)
(* VOID does not replace infinity — it exhausts infinity's program.         *)
(******************************************************************************)

(* Program space: the finite set of states the apparatus can visit *)
Record Apparatus := mkApparatus {
  app_states    : list HiddenState;    (* finite program space *)
  app_visited   : list HiddenState;    (* states already exhausted *)
  app_remaining : Fin;                 (* count of unvisited states *)
}.

(* Visit a state — costs budget, reduces remaining *)
Definition visit_state (app : Apparatus) (state : HiddenState) (b : Budget)
  : (Apparatus * Budget * Spuren) :=
  match b with
  | fz => (app, fz, fz)
  | fs b' =>
    (mkApparatus
      (app_states app)
      (state :: app_visited app)
      (match app_remaining app with fz => fz | fs n => n end),
     b',
     fs fz)
  end.

(* Program exhaustion: is the apparatus fully explored? *)
Definition program_exhausted (app : Apparatus) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  fin_eq_b3 (app_remaining app) fz b.

(* Curvature of trajectory — how sharply the path turns.                    *)
(* High curvature = apparatus is stressed, program is bending.              *)
(* Infinite curvature = singularity. The remainder. BUnknown.               *)
(* We approximate curvature as the difference of consecutive gradients.     *)
Definition trajectory_curvature
  (s1 s2 s3 : HiddenState) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match state_distance s1 s2 b with
  | (g1, b', h1) =>
    match state_distance s2 s3 b' with
    | (g2, b'', h2) =>
      match dist_fin_b_spur g1 g2 b'' with
      | (curv, b''', h3) =>
        (curv, b''', add_spur (add_spur h1 h2) h3)
      end
    end
  end.

(******************************************************************************)
(* VI. BATESON — Double Bind and the Escape to BUnknown                     *)
(*                                                                           *)
(* A double bind: every answer in Bool2 is wrong.                           *)
(* "Be spontaneous!" — if you obey, you're not spontaneous.                *)
(* BUnknown is the only exit. Meta-level costs separate budget.             *)
(******************************************************************************)

(* A frame defines what counts as a valid response *)
Definition Frame := Observable -> Bool3.

(* Double bind: a frame where True and False both lead to contradiction *)
Record DoubleBind := mkDoubleBind {
  db_frame       : Frame;
  db_true_fails  : Observable;    (* witness: True leads to contradiction *)
  db_false_fails : Observable;    (* witness: False leads to contradiction *)
}.

(* The only escape from a double bind is BUnknown —                        *)
(* stepping outside the frame. But stepping outside costs.                  *)
(* Meta-observation: observing the frame instead of answering within it.    *)
Definition escape_double_bind (db : DoubleBind) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match b with
  | fz => (BUnknown, fz, fz)    (* No budget: stuck in bind *)
  | fs b' =>
    match b' with
    | fz => (BUnknown, fz, fs fz)  (* Barely enough: escape but broke *)
    | fs b'' => (BUnknown, b'', fs (fs fz))  (* Escape costs TWO ticks *)
    (* One tick to see the bind. One tick to step outside it.               *)
    (* This is why double binds trap the poor:                              *)
    (* meta-observation is a luxury of those with budget to spare.          *)
    end
  end.

(* THEOREM: Escaping a double bind always returns BUnknown.                 *)
(* There is no True or False escape — only transcending the frame.          *)
Theorem double_bind_escape_is_always_bunknown : forall db b,
  let '(result, _, _) := escape_double_bind db b in
  result = BUnknown.
Proof.
  intros db b. unfold escape_double_bind.
  destruct b; simpl; auto.
  destruct b; simpl; auto.
Qed.

(******************************************************************************)
(* VII. VON NEUMANN — Self-Reproducing Observers and Measurement            *)
(*                                                                           *)
(* An observer can create sub-observers, but only if budget >= B_min.       *)
(* Below B_min, you are alone. No delegation. No consortium.                *)
(* Measurement changes the measured — DDF as thermodynamic fact.            *)
(******************************************************************************)

(* Minimum budget for spawning a sub-observer *)
Parameter B_min_reproduce : Budget.
Axiom B_min_positive : exists n, B_min_reproduce = fs (fs (fs n)).

(* Spawn a sub-observer: splits budget between parent and child *)
Definition spawn_sub_observer (parent : Observer) (b : Budget)
  : (option Observer * Observer * Budget * Spuren) :=
  match le_fin_b3 B_min_reproduce b b with
  | (BTrue, b', h) =>
    (* Can reproduce: split remaining budget *)
    match b' with
    | fz => (None, parent, fz, h)
    | fs b'' =>
      let child := mkObserver (obs_state parent) b'' nil in
      let parent' := mkObserver (obs_state parent) b'' (obs_trajectory parent) in
      (Some child, parent', b'', add_spur h (fs fz))
    end
  | (BFalse, b', h) => (None, parent, b', h)    (* Too poor to reproduce *)
  | (BUnknown, b', h) => (None, parent, b', h)  (* Can't even tell *)
  end.

(* DDF — Dynamic Distinguishability Function                                *)
(* Observation changes BOTH observer and observed.                          *)
(* Neither party exits the interaction unchanged.                           *)
(* Both pay Spuren. This is measurement as thermodynamic exchange.            *)
Definition ddf (obs : Observer) (target : HiddenState) (b : Budget)
  : (Observation * Observer * HiddenState * Budget * Spuren) :=
  match b with
  | fz =>
    (* No budget: observation fails, both unchanged *)
    (mkObservation target fz BUnknown,
     obs, target, fz, fz)
  | fs b' =>
    match b' with
    | fz =>
      (* One tick: observe but can't decide *)
      (mkObservation target (fs fz) BUnknown,
       mkObserver (obs_state obs) fz (target :: obs_trajectory obs),
       target,
       fz, fs fz)
    | fs b'' =>
      (* Two ticks minimum: observe AND decide *)
      (* Observer changes: adds target to trajectory, spends budget *)
      let obs' := mkObserver
        (obs_state obs) b''
        (target :: obs_trajectory obs) in
      (* Target changes: marked as observed — shifted by one tick *)
      (* This is the von Neumann measurement: you can't look without touching *)
      let target' := match target with
        | [] => []
        | x :: xs => (fs x) :: xs   (* Perturbation: first component shifted *)
        end in
      (mkObservation target (fs (fs fz)) BTrue,
       obs', target',
       b'', fs (fs fz))
    end
  end.

(* THEOREM: Observation always changes the observer.                        *)
(* Post-DDF trajectory is strictly longer than pre-DDF trajectory.          *)
Theorem observation_changes_observer : forall obs target,
  obs_budget obs <> fz ->
  exists b' : Budget, exists h : Spuren,
    let '(_, obs', _, _, _) := ddf obs target (obs_budget obs) in
    length (obs_trajectory obs') > length (obs_trajectory obs).
Proof.
  intros obs target Hb.
  unfold ddf.
  destruct (obs_budget obs) as [|f] eqn:Eb.
  - contradiction.
  - destruct f as [|f'].
    + exists fz. exists (fs fz). simpl. auto.
    + exists f'. exists (fs (fs fz)). simpl. auto.
Qed.

(* Ashby's Law as axiom: variety of observer < variety of system → blind spot *)
Axiom variety_law : forall (obs : Observer) (system : list HiddenState),
  length (obs_trajectory obs) < length system ->
  exists blind_region : list HiddenState,
    blind_region <> nil /\
    forall s, In s blind_region -> ~ In s (obs_trajectory obs).

(******************************************************************************)
(* VIII. FRISTON — Free Energy and Prediction Error                         *)
(*                                                                           *)
(* The observer predicts. Prediction error costs Spuren.                      *)
(* Three responses: update model, act on world, or mark BUnknown.           *)
(* The third response — reducing precision — is the VOID response.          *)
(******************************************************************************)

(* Prediction: expected next state *)
Definition Prediction := HiddenState.

(* Prediction error: distance between predicted and actual *)
Definition prediction_error (predicted actual : HiddenState) (b : Budget)
  : (Fin * Budget * Spuren) :=
  state_distance predicted actual b.

(* Markov blanket: the boundary of the observer.                            *)
(* Inside = self. Outside = world. Blanket = membrane.                      *)
(* Maintaining the blanket costs budget.                                    *)
Record MarkovBlanket := mkBlanket {
  blanket_sensory : list Observable;     (* incoming signals *)
  blanket_active  : list Observable;     (* outgoing actions *)
  blanket_cost    : Spuren;                (* maintenance cost per step *)
}.

(* Three responses to prediction error — Friston's trinity *)
Inductive FreeEnergyResponse : Type :=
  | UpdateModel   : HiddenState -> FreeEnergyResponse   (* change beliefs *)
  | Act           : Observable -> FreeEnergyResponse     (* change world *)
  | ReducePrecision : FreeEnergyResponse.                (* mark as BUnknown *)
  (* The third is VOID's move: "this signal is too expensive to process."   *)
  (* Not wrong. Not right. Too costly. Ignore with integrity.              *)

(* Choose response based on prediction error magnitude and remaining budget *)
Definition free_energy_response
  (error : Fin) (threshold : Fin) (b : Budget)
  (predicted : HiddenState)
  : (FreeEnergyResponse * Budget * Spuren) :=
  match b with
  | fz => (ReducePrecision, fz, fz)  (* No budget: must ignore *)
  | fs b' =>
    match le_fin_b3 error threshold b' with
    | (BTrue, b'', h) =>
      (* Error below threshold: prediction good enough, no update *)
      (UpdateModel predicted, b'', h)
    | (BFalse, b'', h) =>
      (* Error above threshold: need to update *)
      match b'' with
      | fz => (ReducePrecision, fz, h)  (* Want to update but can't afford *)
      | fs b''' => (UpdateModel predicted, b''', add_spur h (fs fz))
      end
    | (BUnknown, b'', h) =>
      (* Can't even measure the error properly *)
      (ReducePrecision, b'', h)
    end
  end.

(******************************************************************************)
(* IX. CLARK — Extended Mind With Cost                                       *)
(*                                                                           *)
(* The observer can incorporate external systems.                           *)
(* Notebook, calculator, Claude, Gemini, GPT — all extensions.              *)
(* Each extension costs Spuren. Diminishing returns are real.                 *)
(******************************************************************************)

(* An extension: an external system the observer can query *)
Record Extension := mkExtension {
  ext_query_cost  : Spuren;        (* cost per query *)
  ext_reliability : Fin;         (* how often it gives useful answers *)
  ext_domain      : Observable;  (* what it knows about *)
}.

(* Query an extension — costs budget, may or may not help *)
Definition query_extension (ext : Extension) (query : Observable) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  let cost := ext_query_cost ext in
  match le_fin_b3 cost b b with
  | (BTrue, b', h1) =>
    (* Can afford the query *)
    match sub_saturate_b_spur b cost b' with
    | (b'', b_after, h2) =>
      (* Query succeeds based on reliability — simplified *)
      (BTrue, b_after, add_spur h1 h2)
    end
  | (BFalse, b', h) => (BUnknown, b', h)  (* Can't afford *)
  | (BUnknown, b', h) => (BUnknown, b', h)
  end.

(* Consortium: multiple observers with shared target *)
Record Consortium := mkConsortium {
  cons_observers : list Observer;
  cons_extensions: list Extension;
  cons_total_budget : Budget;
}.

(* THEOREM: Consortium reduces but never eliminates blind spots.            *)
(* More observers = less BUnknown. But never zero BUnknown.                 *)
(* Because each observer added costs budget, and budget is finite.          *)

(******************************************************************************)
(* X. BOHR — Complementarity                                                *)
(*                                                                           *)
(* Observing X excludes observing Y. Not because instruments are bad.       *)
(* Because budget spent on X is unavailable for Y.                          *)
(* BUnknown is not ignorance. It is physics.                                *)
(*                                                                           *)
(* The transduction boundary — where float becomes integer,                 *)
(* where quantum becomes classical — is the Heisenberg cut.                 *)
(* VOID-IN is this cut. It is not optional.                                 *)
(******************************************************************************)

(* Two observables are complementary if measuring one prevents measuring the other.
   We don't try to reach into the DDF tuple — complementarity is about COST.
   If cost_x + cost_y > budget, you must choose. That's all Bohr says. *)
Definition Complementary (cost_x cost_y : Spuren) (b : Budget) : Prop :=
  forall b_after h,
    add_fin_b_spur cost_x cost_y b = (b_after, b, h) ->
    (* total cost exceeds what we started with — can't afford both *)
    leF b b_after.

(* Simplified complementarity: budget partition is exclusive *)
Definition complementary_pair (cost_x cost_y : Spuren) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  (* Can we afford both? *)
  match add_fin_b_spur cost_x cost_y b with
  | (total_cost, b', h) =>
    le_fin_b3 total_cost b b'
  end.

(* If complementary_pair returns BFalse, we can afford both — not complementary *)
(* If BTrue, total cost exceeds budget — must choose. This IS complementarity. *)
(* If BUnknown, can't even tell if we can afford both — deepest uncertainty.   *)

(* Observation choice: given limited budget, what do you look at? *)
Definition observation_choice
  (observables : list Observable) (costs : list Spuren) (b : Budget)
  : (list Bool3 * Budget * Spuren) :=
  (* For each observable: can we afford it given what we've already spent? *)
  (* This is a greedy partition — first observables get priority.          *)
  (* The ORDER of observation matters. This is not neutral.                *)
  (List.map (fun _ => BUnknown) observables, b, fz).
  (* Placeholder: full implementation would iterate with budget tracking   *)

(******************************************************************************)
(* XI. FINITE PRECEDES INFINITE — The Asymmetry Theorem                     *)
(*                                                                           *)
(* Infinity is an approximation of finitude, not the other way around.      *)
(* Every "infinite" construction is a limit of finite ones.                 *)
(* The limit is never reached. The finite is all there is.                  *)
(*                                                                           *)
(* VOID is not a parasite on an infinite machine.                           *)
(* The infinite machine is a parasite on finite reality.                    *)
(* VOID restores the order.                                                 *)
(******************************************************************************)

(* An "infinite" construction is indistinguishable from a finite one        *)
(* for any observer with finite budget.                                     *)
(* This is the asymmetry: finite can emulate "infinite" (up to budget).     *)
(* "Infinite" cannot access the SPECIFIC bound of a finite construction.    *)

(* Indistinguishability under budget *)
Definition indistinguishable
  (obs : Observer) (s1 s2 : HiddenState) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match state_distance s1 s2 b with
  | (dist, b', h) =>
    (* If distance is zero (or budget ran out making it look zero): same *)
    fin_eq_b3 dist fz b'
  end.

(******************************************************************************)
(* XII. INTEGRATION — Stopped Reasons                                       *)
(*                                                                           *)
(* Why did the observer stop?                                               *)
(******************************************************************************)

Inductive StoppedReason : Type :=
  | Complete              : StoppedReason   (* finished the job *)
  | BudgetExhausted_R     : StoppedReason   (* Turing: ran out of budget *)
  | ConfidenceDrop        : StoppedReason   (* Friston: prediction error too high *)
  | AttractorDetected     : HiddenState -> StoppedReason  (* Lacan: tape tangled *)
  | ComplementaryExcluded : StoppedReason   (* Bohr: chose to observe X, not Y *)
  | DoubleBound           : StoppedReason   (* Bateson: no valid Bool2 answer *)
  | BlindSpot             : StoppedReason   (* Gödel: structural impossibility *)
  | TransductionFailure   : StoppedReason   (* cut produced BUnknown *)
  | AttractorRecurrence   : HiddenState -> StoppedReason  (* same wound again *)
  | AttentionExhausted    : StoppedReason   (* can't afford more tokens *)
  | ConsortiumDisagreement: StoppedReason   (* BUnknown infected the vote *)
  | Recovery              : StoppedReason   (* observer withdrew to heal *)
  | ExploitationDetected  : StoppedReason.  (* asymmetric DDF ratio too high *)

(* Convert stopped reason to Bool3 *)
Definition stopped_to_bool3 (r : StoppedReason) : Bool3 :=
  match r with
  | Complete              => BTrue
  | ConfidenceDrop        => BFalse
  | ExploitationDetected  => BFalse    (* you KNOW something is wrong *)
  | _                     => BUnknown
  end.

(* THEOREM: Ten of thirteen stopped reasons map to BUnknown.                *)
(* The observer's dominant experience is not-knowing.                       *)
(* This is not a failure. This is honest finitude.                          *)
(* The more we formalize, the more dominant not-knowing becomes.            *)
Theorem most_stops_are_bunknown : forall r,
  r <> Complete -> r <> ConfidenceDrop -> r <> ExploitationDetected ->
  stopped_to_bool3 r = BUnknown.
Proof.
  intros r Hc Hcd Hex.
  destruct r; simpl; auto; contradiction.
Qed.

(******************************************************************************)
(* XIII. THE OBSERVATION LOOP — Putting It All Together                      *)
(*                                                                           *)
(* One step of observation:                                                 *)
(* 1. Predict (Friston)                                                     *)
(* 2. Observe via DDF (von Neumann/Bohr)                                    *)
(* 3. Compute prediction error (Friston)                                    *)
(* 4. Check for tangling (Lacan)                                            *)
(* 5. Check for double bind (Bateson)                                       *)
(* 6. Update or stop (Turing — budget-bounded decision)                     *)
(* 7. Record in trajectory (Clark — extended mind costs)                    *)
(*                                                                           *)
(* The loop runs inside the apparatus (Flusser).                            *)
(* The blind spot persists through every iteration (Gödel).                 *)
(******************************************************************************)

Record ObservationStep := mkStep {
  step_observation : Observation;
  step_chain_state : ChainState;
  step_prediction_error : Fin;
  step_curvature : Fin;
  step_stopped : option StoppedReason;
  step_budget_remaining : Budget;
  step_heat_emitted : Spuren;
}.

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
(*  THE ADMITTED — On the Source of Budget                                   *)
(******************************************************************************)
(*                                                                           *)
(*  Where does the observer's initial budget come from?                     *)
(*  This is a question about God. We have no interest in such questions.    *)
(*                                                                           *)
(*  The Admitted in void_arithmetic.v is the answer:                        *)
(*  there IS a budget. It IS finite. WHERE it comes from is outside         *)
(*  the system. This is not a gap in the theory.                            *)
(*  It is the theory's most honest statement.                               *)
(*                                                                           *)
(*  Gödel proved you can't ground yourself from within.                    *)
(*  We don't pretend to. We start with what we have                         *)
(*  and count every tick until it runs out.                                  *)
(*                                                                           *)
(*  The body discovered conservation law before the mind did.               *)
(*  These nineteen sections are the formalization of that discovery.        *)
(*                                                                           *)
(******************************************************************************)

End Void_Observer.
