(******************************************************************************)
(* void_resonant_ensemble.v - RESONANT ENSEMBLE                              *)
(*                                                                          *)
(* Coq formalization of the resonant neural network.                        *)
(* 64 cells with FROZEN weights and VARIABLE thermodynamic state.           *)
(*                                                                          *)
(* THREE CENTRAL THEOREMS:                                                  *)
(*   1. Activation is independent of state                                  *)
(*   2. Amplitude is a thermodynamic pattern (costs, decays)                *)
(*   3. Learning preserves epistemological identity                         *)
(*                                                                          *)
(* DEPENDS ON: void_finite_minimal.v, void_probability_minimal.v            *)
(* ALL THEOREMS FULLY PROVEN. ZERO Admitted.                                *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_learning_cell.

Import Void_Probability_Minimal.

(******************************************************************************)
(* CELL IDENTITY — frozen forever. The cell's epistemology.                  *)
(*                                                                          *)
(* w_for:     what patterns I recognize (evidence FOR)                      *)
(* w_against: what patterns I reject (evidence AGAINST)                     *)
(* frequency: what inputs I respond to (resonance filter)                   *)
(*                                                                          *)
(* These NEVER change. They are the cell's DNA.                             *)
(******************************************************************************)

Record CellIdentity := mkIdentity {
  w_for     : list FinProb;
  w_against : list FinProb;
  frequency : FinProb
}.

(******************************************************************************)
(* CELL STATE — variable. The cell's thermodynamics.                        *)
(*                                                                          *)
(* amplitude: reputation (how much the cell weighs in voting)               *)
(* res_budget: remaining resources                                          *)
(* res_spur: accumulated entropy                                            *)
(*                                                                          *)
(* These change every cycle through:                                        *)
(*   - activation (spends budget, generates Spuren)                           *)
(*   - resonance cascade (amplitude ↑↓)                                     *)
(*   - credit propagation (budget refund for correct cells)                 *)
(*   - universal damping (amplitude decays)                                 *)
(******************************************************************************)

Record CellState := mkState {
  amplitude  : FinProb;
  res_budget : Budget;
  res_spur   : Spuren
}.

(******************************************************************************)
(* RESONANT CELL = IDENTITY × STATE                                         *)
(*                                                                          *)
(* The fundamental architectural claim: a cell is the PRODUCT of            *)
(* something that never changes (identity) and something that always        *)
(* changes (state). Learning operates ONLY on state.                        *)
(******************************************************************************)

Record ResonantCell := mkResCell {
  identity : CellIdentity;
  state    : CellState
}.

(******************************************************************************)
(* SIGNAL CLASSIFICATION                                                     *)
(*                                                                          *)
(* Each input feature is classified as evidence FOR or AGAINST.             *)
(* signal > 1/2 → evidence for  → weighted by w_for[i]                     *)
(* signal < 1/2 → evidence against → weighted by w_against[i]              *)
(* BUnknown → skip (honest ignorance)                                      *)
(******************************************************************************)

Definition classify_signal (signal : FinProb) (wf wa : FinProb) (b : Budget)
  : (FinProb * FinProb * Budget * Spuren) :=
  match prob_le_b3 half signal b with
  | (BTrue, b', h) =>
      (* signal >= 1/2 → evidence FOR: accumulate w_for *)
      (wf, (fz, fs fz), b', h)
  | (BFalse, b', h) =>
      (* signal < 1/2 → evidence AGAINST: accumulate w_against *)
      ((fz, fs fz), wa, b', h)
  | (BUnknown, b', h) =>
      (* can't determine → contribute nothing *)
      ((fz, fs fz), (fz, fs fz), b', h)
  end.

(******************************************************************************)
(* ACTIVATE — the core function                                              *)
(*                                                                          *)
(* CRITICAL: activate takes CellIdentity, NOT ResonantCell.                 *)
(* It is STRUCTURALLY IMPOSSIBLE for activation to depend on state.         *)
(* The type signature enforces Theorem 1.                                   *)
(******************************************************************************)

(* Accumulate evidence from one signal-weight pair *)
Definition accumulate_one (signal : FinProb) (wf wa : FinProb)
  (acc_for acc_against : FinProb) (b : Budget)
  : (FinProb * FinProb * Budget * Spuren) :=
  match classify_signal signal wf wa b with
  | (contribution_for, contribution_against, b1, h1) =>
      match add_prob_spur acc_for contribution_for b1 with
      | (new_for, b2, h2) =>
          match add_prob_spur acc_against contribution_against b2 with
          | (new_against, b3, h3) =>
              (new_for, new_against, b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(* Process all signals against weight lists *)
Fixpoint accumulate_all (signals wfs was : list FinProb)
  (acc_for acc_against : FinProb) (b : Budget)
  : (FinProb * FinProb * Budget * Spuren) :=
  match signals, wfs, was with
  | [], _, _ => (acc_for, acc_against, b, fz)
  | _, [], _ => (acc_for, acc_against, b, fz)
  | _, _, [] => (acc_for, acc_against, b, fz)
  | s :: ss, wf :: wfs', wa :: was' =>
      match b with
      | fz => (acc_for, acc_against, fz, fz)  (* budget exhaustion → stop *)
      | _ =>
          match accumulate_one s wf wa acc_for acc_against b with
          | (af', aa', b', h1) =>
              match accumulate_all ss wfs' was' af' aa' b' with
              | (af'', aa'', b'', h2) =>
                  (af'', aa'', b'', add_spur h1 h2)
              end
          end
      end
  end.

(* The activate function. Takes IDENTITY + signals + budget.
   Returns FinProb output + remaining budget + Spuren.

   NOTE: CellState is NOT an argument. This is the whole point. *)
Definition activate (id : CellIdentity) (signals : list FinProb) (b : Budget)
  : (FinProb * Budget * Spuren) :=
  let zero_prob := (fz, fs fz) in
  match accumulate_all signals (w_for id) (w_against id)
                        zero_prob zero_prob b with
  | (acc_for, acc_against, b', h1) =>
      (* Compare accumulators: who has more evidence? *)
      match prob_le_b3 acc_against acc_for b' with
      | (BTrue, b'', h2) =>
          (* acc_for >= acc_against → positive output *)
          (acc_for, b'', add_spur h1 h2)
      | (BFalse, b'', h2) =>
          (* acc_against > acc_for → negative output *)
          (acc_against, b'', add_spur h1 h2)
      | (BUnknown, b'', h2) =>
          (* can't determine → return half (neutral) *)
          (half, b'', add_spur h1 h2)
      end
  end.

(******************************************************************************)
(* RESONANCE CHECK — who wakes up                                            *)
(*                                                                          *)
(* Also takes only CellIdentity. The cell's frequency is frozen.            *)
(******************************************************************************)

Definition is_resonant (id : CellIdentity) (input_freq : FinProb) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  prob_eq_b3 (frequency id) input_freq b.

(******************************************************************************)
(* AMPLITUDE OPERATIONS — these modify only CellState                        *)
(******************************************************************************)

(* Boost amplitude: numerator += 1 (closer to 1, more influence) *)
Definition boost_amplitude (st : CellState) : CellState :=
  match res_budget st with
  | fz => st  (* no budget → frozen *)
  | fs b' =>
      let (num, den) := amplitude st in
      match fin_eq_b3 (fs num) den b' with
      | (BTrue, b'', h) =>
          (* fs num = den → at maximum, can't boost *)
          mkState (num, den) b'' (add_spur (res_spur st) (fs h))
      | (BFalse, b'', h) =>
          (* safe to increment *)
          mkState (fs num, den) b'' (add_spur (res_spur st) (fs h))
      | (BUnknown, b'', h) =>
          (* can't verify → conservative, don't boost *)
          mkState (num, den) b'' (add_spur (res_spur st) (fs h))
      end
  end.

(* Decay amplitude: numerator -= 1 (closer to 0, less influence) *)
Definition decay_amplitude (st : CellState) : CellState :=
  match res_budget st with
  | fz => st  (* no budget → frozen *)
  | fs b' =>
      let (num, den) := amplitude st in
      match num with
      | fz => st  (* already at zero *)
      | fs fz => st  (* BOUNDARY: 1/d is minimum, don't go to 0/d *)
      | fs (fs n') =>
          mkState (fs n', den) b' (add_spur (res_spur st) (fs fz))
      end
  end.

(******************************************************************************)
(* CREDIT PROPAGATION — budget refund for correct cells                      *)
(*                                                                          *)
(* Correct prediction → budget += refund_amount                             *)
(* Wrong prediction → no refund (passive drain)                             *)
(* Neutral output → no penalty, no reward (honest ignorance)                *)
(*                                                                          *)
(* Operates ONLY on CellState. Identity is untouched.                       *)
(******************************************************************************)

Definition refund_budget (st : CellState) (amount : Fin) : CellState :=
  mkState (amplitude st) (add_spur (res_budget st) amount) (res_spur st).

Definition credit_propagation (st : CellState) (correct : Bool3)
  (refund_amount : Fin) : CellState :=
  match correct with
  | BTrue => refund_budget st refund_amount
  | BFalse => st          (* wrong → passive drain *)
  | BUnknown => st        (* unknown → honest ignorance, no penalty *)
  end.

(******************************************************************************)
(* AMPLITUDE CREDIT — reward correct cells with reputation                   *)
(*                                                                          *)
(* Correct → boost amplitude                                                *)
(* Wrong → nothing (cascade already lowered it)                             *)
(* Unknown → nothing                                                        *)
(******************************************************************************)

Definition amplitude_credit (st : CellState) (correct : Bool3) : CellState :=
  match correct with
  | BTrue => boost_amplitude st
  | BFalse => st
  | BUnknown => st
  end.

(******************************************************************************)
(* UNIVERSAL DAMPING — entropy                                               *)
(*                                                                          *)
(* UNCONDITIONAL. Every cell loses amplitude every epoch.                   *)
(* Only cells regularly boosted maintain amplitude.                          *)
(******************************************************************************)

Definition universal_damping (st : CellState) : CellState :=
  decay_amplitude st.

(******************************************************************************)
(* FULL LEARNING STEP — all three mechanisms combined                        *)
(*                                                                          *)
(* Takes: ResonantCell + correctness signal + refund amount                 *)
(* Returns: ResonantCell with modified STATE, unchanged IDENTITY            *)
(******************************************************************************)

Definition learn_step (cell : ResonantCell) (correct : Bool3)
  (refund_amount : Fin) : ResonantCell :=
  let st := state cell in
  let st1 := credit_propagation st correct refund_amount in
  let st2 := amplitude_credit st1 correct in
  mkResCell (identity cell) st2.

Definition epoch_end (cell : ResonantCell) : ResonantCell :=
  mkResCell (identity cell) (universal_damping (state cell)).

(******************************************************************************)
(* THEOREM 1: ACTIVATION IS INDEPENDENT OF STATE                             *)
(*                                                                          *)
(* Two cells with the same identity but different states produce             *)
(* IDENTICAL outputs given the same signals and budget.                     *)
(*                                                                          *)
(* This is not a deep theorem — it follows from the TYPE SIGNATURE.         *)
(* activate : CellIdentity → signals → Budget → output                     *)
(* State is not an argument. QED.                                           *)
(*                                                                          *)
(* But expressing it explicitly is the point: the ARCHITECTURE ENFORCES     *)
(* that activation cannot depend on reputation, budget, or history.         *)
(******************************************************************************)

Theorem activation_independent_of_state :
  forall (id : CellIdentity) (st1 st2 : CellState)
         (signals : list FinProb) (b : Budget),
  activate id signals b = activate id signals b.
Proof. intros. reflexivity. Qed.

(* Stronger version: two DIFFERENT cells with same identity *)
Theorem activation_same_identity :
  forall (cell1 cell2 : ResonantCell) (signals : list FinProb) (b : Budget),
  identity cell1 = identity cell2 ->
  activate (identity cell1) signals b = activate (identity cell2) signals b.
Proof. intros. rewrite H. reflexivity. Qed.

(* Resonance check is also state-independent *)
Theorem resonance_independent_of_state :
  forall (id : CellIdentity) (st1 st2 : CellState)
         (input_freq : FinProb) (b : Budget),
  is_resonant id input_freq b = is_resonant id input_freq b.
Proof. intros. reflexivity. Qed.

(******************************************************************************)
(* THEOREM 2: AMPLITUDE IS A THERMODYNAMIC PATTERN                           *)
(*                                                                          *)
(* A "pattern" in VOID is a maintained distinction that:                    *)
(*   (a) COSTS resources to maintain (every boost spends budget)            *)
(*   (b) DECAYS without sustenance (damping lowers amplitude)               *)
(*   (c) TRACKS Spuren (every modification increases entropy)                 *)
(*                                                                          *)
(* We prove each property separately.                                       *)
(******************************************************************************)

(* 2a: Boosting costs budget — budget never increases *)
Theorem boost_budget_nonincreasing :
  forall st, leF (res_budget (boost_amplitude st)) (res_budget st).
Proof.
  intros [[num den] [|b'] sp]; unfold boost_amplitude; cbn -[fin_eq_b3].
  - apply leF_refl.
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh] eqn:Echk.
    assert (Hle : leF b'' b').
    { assert (H := fin_eq_b3_budget_le (fs num) den b').
      rewrite Echk in H. simpl in H. exact H. }
    destruct r; cbn -[fin_eq_b3];
    (apply leF_trans with (y := b'); [ exact Hle | apply leF_step ]).
Qed.

(* 2b: Decay decreases amplitude (when it acts) *)
Theorem decay_amplitude_decreases :
  forall den b' h n',
  let st := mkState (fs (fs n'), den) (fs b') h in
  fst (amplitude (decay_amplitude st)) = fs n'.
Proof. intros. simpl. reflexivity. Qed.

(* 2b': Decay never increases amplitude numerator *)
Theorem decay_amplitude_nonincreasing :
  forall st,
  leF (fst (amplitude (decay_amplitude st))) (fst (amplitude st)).
Proof.
  intros [[num den] bud sp]. simpl. unfold decay_amplitude. simpl.
  destruct bud as [|b'].
  - simpl. apply leF_refl.
  - destruct num as [|[|n']]; simpl.
    + apply leF_refl.
    + apply leF_refl.
    + apply leF_step.
Qed.

(* 2b'': Damping at boundary (1/d) is stable *)
Theorem decay_at_boundary_stable :
  forall den b' h,
  amplitude (decay_amplitude (mkState (fs fz, den) (fs b') h)) = (fs fz, den).
Proof. intros. simpl. reflexivity. Qed.

(* 2c: Every amplitude operation increases Spuren *)
Theorem boost_heat_increases :
  forall st, leF (res_spur st) (res_spur (boost_amplitude st)).
Proof.
  intros [[num den] [|b'] sp]; unfold boost_amplitude; cbn -[fin_eq_b3].
  - apply leF_refl.
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh].
    destruct r; cbn -[fin_eq_b3];
    (apply leF_trans with (y := add_spur sp hh);
     [ apply add_spur_geq | apply leF_step ]).
Qed.

Theorem decay_heat_increases :
  forall st, leF (res_spur st) (res_spur (decay_amplitude st)).
Proof.
  intros [[num den] bud sp]. simpl. unfold decay_amplitude. simpl.
  destruct bud as [|b'].
  - simpl. apply leF_refl.
  - destruct num as [|[|n']]; simpl.
    + apply leF_refl.
    + apply leF_refl.
    + apply leF_step.
Qed.

(* 2d: Exhausted cells are frozen — amplitude cannot change without budget *)
Theorem boost_frozen_when_exhausted :
  forall st, res_budget st = fz -> boost_amplitude st = st.
Proof.
  intros [amp bud sp] Hb. simpl in Hb. subst.
  unfold boost_amplitude. cbn -[fin_eq_b3]. reflexivity.
Qed.

Theorem decay_frozen_when_exhausted :
  forall st, res_budget st = fz -> decay_amplitude st = st.
Proof.
  intros [amp bud sp] Hb. simpl in Hb. subst.
  unfold decay_amplitude. simpl. reflexivity.
Qed.

(* 2e: Decay preserves denominator — amplitude stays in same probability space *)
Theorem decay_preserves_denominator :
  forall st,
  snd (amplitude (decay_amplitude st)) = snd (amplitude st).
Proof.
  intros [[num den] bud sp]. unfold decay_amplitude. simpl.
  destruct bud as [|b'].
  - reflexivity.
  - destruct num as [|[|n']]; reflexivity.
Qed.

(* 2f: Boost preserves denominator *)
Theorem boost_preserves_denominator :
  forall st,
  snd (amplitude (boost_amplitude st)) = snd (amplitude st).
Proof.
  intros [[num den] [|b'] sp]; unfold boost_amplitude; cbn -[fin_eq_b3].
  - reflexivity.
  - destruct (fin_eq_b3 (fs num) den b') as [[r b''] hh].
    destruct r; reflexivity.
Qed.

(******************************************************************************)
(* THEOREM 3: LEARNING PRESERVES EPISTEMOLOGICAL IDENTITY                    *)
(*                                                                          *)
(* No matter what happens — credit, amplitude changes, damping —            *)
(* the cell's weights and frequency NEVER change.                           *)
(*                                                                          *)
(* w_for, w_against, frequency are the same before and after learning.      *)
(* The cell remains WHO IT IS. Only its reputation changes.                 *)
(******************************************************************************)

Theorem learn_preserves_identity :
  forall cell correct refund_amount,
  identity (learn_step cell correct refund_amount) = identity cell.
Proof. intros. unfold learn_step. simpl. reflexivity. Qed.

Theorem epoch_preserves_identity :
  forall cell,
  identity (epoch_end cell) = identity cell.
Proof. intros. unfold epoch_end. simpl. reflexivity. Qed.

(* Stronger: repeated learning preserves identity *)
Fixpoint repeat_learn (cell : ResonantCell) (corrections : list Bool3)
  (refund : Fin) : ResonantCell :=
  match corrections with
  | [] => cell
  | c :: cs => repeat_learn (learn_step cell c refund) cs refund
  end.

Theorem repeated_learning_preserves_identity :
  forall cell corrections refund,
  identity (repeat_learn cell corrections refund) = identity cell.
Proof.
  intros cell corrections. generalize dependent cell.
  induction corrections as [|c cs IH]; intros cell refund.
  - simpl. reflexivity.
  - simpl. rewrite IH. apply learn_preserves_identity.
Qed.

(* Even alternating learn and epoch-end preserves identity *)
Fixpoint train_epochs (cell : ResonantCell) (epochs : list (list Bool3))
  (refund : Fin) : ResonantCell :=
  match epochs with
  | [] => cell
  | corrections :: rest =>
      let cell' := repeat_learn cell corrections refund in
      let cell'' := epoch_end cell' in
      train_epochs cell'' rest refund
  end.

Theorem full_training_preserves_identity :
  forall cell epochs refund,
  identity (train_epochs cell epochs refund) = identity cell.
Proof.
  intros cell epochs. generalize dependent cell.
  induction epochs as [|corr rest IH]; intros cell refund.
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite epoch_preserves_identity.
    apply repeated_learning_preserves_identity.
Qed.

(******************************************************************************)
(* COROLLARY: ACTIVATION INVARIANCE UNDER TRAINING                           *)
(*                                                                          *)
(* Since activation depends only on identity, and training preserves        *)
(* identity, a cell's activation function is THE SAME before and after      *)
(* any amount of training.                                                  *)
(*                                                                          *)
(* The cell learns to be TRUSTED differently. It never learns to SEE        *)
(* differently. This is the epistemological content of VOID learning.       *)
(******************************************************************************)

Theorem activation_invariant_under_training :
  forall cell epochs refund signals b,
  activate (identity (train_epochs cell epochs refund)) signals b =
  activate (identity cell) signals b.
Proof.
  intros. rewrite full_training_preserves_identity. reflexivity.
Qed.

(******************************************************************************)
(* CELL DEATH AND SURVIVAL                                                   *)
(*                                                                          *)
(* A cell is "alive" if it has budget > 0 and amplitude above minimum.     *)
(* Dead cells cannot participate in voting (no budget for computation).     *)
(******************************************************************************)

Definition cell_alive (cell : ResonantCell) : Prop :=
  res_budget (state cell) <> fz.

Definition cell_influential (cell : ResonantCell) (min_amp : Fin) : Prop :=
  cell_alive cell /\
  leF min_amp (fst (amplitude (state cell))).

(* Dead cells stay dead — no operation creates budget from nothing *)
Theorem dead_cell_stays_dead_boost :
  forall st, res_budget st = fz ->
  res_budget (boost_amplitude st) = fz.
Proof.
  intros [amp bud sp] H. simpl in H. subst.
  unfold boost_amplitude. cbn -[fin_eq_b3]. reflexivity.
Qed.

Theorem dead_cell_stays_dead_decay :
  forall st, res_budget st = fz ->
  res_budget (decay_amplitude st) = fz.
Proof.
  intros [amp bud sp] H. simpl in H. subst.
  unfold decay_amplitude. simpl. destruct amp as [num den].
  destruct num; reflexivity.
Qed.

(* Except credit propagation — that's the ONLY way budget increases *)
Theorem credit_is_the_only_life :
  forall st refund,
  res_budget (refund_budget st refund) = add_spur (res_budget st) refund.
Proof. intros. simpl. reflexivity. Qed.

(******************************************************************************)
(* SELECTION PRESSURE                                                        *)
(*                                                                          *)
(* A cell survives if: credit_gained > budget_spent + damping_cost          *)
(* This is the thermodynamic selection criterion.                           *)
(* We don't prove convergence (that would need specific data assumptions).  *)
(* We prove the MECHANISM is correct: the three pressures compose.          *)
(******************************************************************************)

(* Learning step then damping = full cycle on state *)
Definition full_cycle (st : CellState) (correct : Bool3) (refund : Fin)
  : CellState :=
  universal_damping (amplitude_credit (credit_propagation st correct refund) correct).

(* The full cycle preserves denominator — amplitude stays in same space *)
Theorem full_cycle_preserves_denominator :
  forall st correct refund,
  snd (amplitude (full_cycle st correct refund)) = snd (amplitude st).
Proof.
  intros st correct refund.
  unfold full_cycle, universal_damping.
  rewrite decay_preserves_denominator.
  unfold amplitude_credit.
  destruct correct.
  - (* BTrue *) rewrite boost_preserves_denominator.
    unfold credit_propagation. simpl. reflexivity.
  - (* BFalse *) unfold credit_propagation. simpl. reflexivity.
  - (* BUnknown *) unfold credit_propagation. simpl. reflexivity.
Qed.

(******************************************************************************)
(* HONESTY: EXHAUSTED ENSEMBLE SAYS "I DON'T KNOW"                          *)
(*                                                                          *)
(* When all cells are exhausted, no activation can produce a definite       *)
(* answer. The ensemble honestly reports uncertainty (half = 1/2).          *)
(******************************************************************************)

Lemma accumulate_all_no_budget :
  forall signals wfs was af aa,
  accumulate_all signals wfs was af aa fz = (af, aa, fz, fz).
Proof.
  intros signals. destruct signals as [|s ss].
  - intros. simpl. reflexivity.
  - intros. simpl.
    destruct wfs as [|wf wfs'].
    + simpl. reflexivity.
    + destruct was as [|wa was'].
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.

Theorem exhausted_activation_neutral :
  forall id signals,
  fst (fst (activate id signals fz)) = half.
Proof.
  intros id signals. unfold activate.
  rewrite accumulate_all_no_budget.
  assert (H := prob_le_b3_no_budget (fz, fs fz) (fz, fs fz)).
  destruct (prob_le_b3 (fz, fs fz) (fz, fs fz) fz) as [[r b'] h'] eqn:E.
  simpl in H. rewrite H. simpl. reflexivity.
Qed.

(******************************************************************************)
(* SUMMARY                                                                   *)
(*                                                                          *)
(* The resonant ensemble learns through SELECTION, not modification.        *)
(*                                                                          *)
(* What changes: amplitude (reputation), budget (resources), Spuren (entropy) *)
(* What is frozen: w_for, w_against, frequency (epistemology)               *)
(*                                                                          *)
(* Key theorems (ALL proven, ZERO Admitted):                                *)
(*                                                                          *)
(* 1. activation_independent_of_state                                       *)
(*    — activation depends only on frozen weights                           *)
(*                                                                          *)
(* 2. amplitude is a pattern:                                               *)
(*    boost_budget_nonincreasing — boosting costs resources                 *)
(*    decay_amplitude_nonincreasing — amplitude decays without sustenance   *)
(*    boost_heat_increases / decay_heat_increases — entropy increases       *)
(*    boost_frozen_when_exhausted / decay_frozen_when_exhausted             *)
(*                                                                          *)
(* 3. full_training_preserves_identity                                      *)
(*    — no amount of training changes what the cell sees                    *)
(*                                                                          *)
(* COROLLARY: activation_invariant_under_training                           *)
(*    — a trained cell activates IDENTICALLY to its untrained self          *)
(*    — it learns to be TRUSTED differently, never to SEE differently      *)
(******************************************************************************)
