(******************************************************************************)
(* void_pattern.v - Pattern interference with Spuren tracking                   *)
(* Observation generates Spuren! Interference creates thermodynamic cost!       *)
(* CLEANED: No magic numbers, uniform costs                                   *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.ZArith.ZArith.

Module Void_Pattern.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* BASIC TYPES                                                                *)
(******************************************************************************)

Record Pattern := {
  location : Fin;
  strength : FinProb
}.

Record Observer := {
  sensitivity : Fin;
  obs_budget : Budget;
  obs_spur : Spuren
}.

(* No privileged observers - create them as needed *)

(******************************************************************************)
(* HELPERS WITH BUDGET                                                        *)
(******************************************************************************)

(* Generic list operations with budget *)
Fixpoint existsb_with_budget {A : Type} (f : A -> Budget -> (bool * Budget)) 
                             (l : list A) (b : Budget) : (bool * Budget) :=
  match l, b with
  | [], _ => (false, b)
  | _, fz => (false, fz)
  | x :: xs, fs b' =>
      match f x b' with
      | (true, b'') => (true, b'')
      | (false, b'') => existsb_with_budget f xs b''
      end
  end.

Fixpoint length_fin_with_budget {A : Type} (l : list A) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: t, fs b' => 
      match length_fin_with_budget t b' with
      | (len, b'') => (fs len, b'')
      end
  end.

(* Probability operations *)
Definition add_prob_with_budget (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      match le_fin_b (fst p1) (fst p2) b' with
      | (true, b'') => (p2, b'')
      | (false, b'') => (p1, b'')
      end
  end.

(******************************************************************************)
(* CORE OPERATIONS WITH SPUREN                                                 *)
(******************************************************************************)

(* Decay with Spuren - uniform cost *)
Definition decay_with_spur (p : FinProb) (b : Budget) : (FinProb * Budget * Spuren) :=
  match b with
  | fz => (p, fz, fz)
  | fs b' =>
      match p with
      | (fs (fs n), d) => ((fs n, d), b', operation_cost)
      | other => (other, b', operation_cost)
      end
  end.

(* Pattern interference with Spuren tracking - no magic numbers *)
Definition interfere_spur (p1 p2 : Pattern) (b : Budget) 
  : (list Pattern * Budget * Spuren) :=
  match fin_eq_b3 (location p1) (location p2) b with
  | (BTrue, b1, h1) =>
      (* Same location - patterns interfere *)
      match decay_with_spur (strength p1) b1 with
      | (s1', b2, h2) =>
          match decay_with_spur (strength p2) b2 with
          | (s2', b3, h3) =>
              (* Just return the decayed patterns, no magic third pattern *)
              ([{| location := location p1; strength := s1' |};
                {| location := location p2; strength := s2' |}], 
               b3,
               add_spur h1 (add_spur h2 h3))
          end
      end
  | (BFalse, b1, h1) =>
      (* Different locations - minimal interference *)
      match decay_with_spur (strength p1) b1 with
      | (s1', b2, h2) =>
          match decay_with_spur (strength p2) b2 with
          | (s2', b3, h3) =>
              ([{| location := location p1; strength := s1' |};
                {| location := location p2; strength := s2' |}], 
               b3,
               add_spur h1 (add_spur h2 h3))
          end
      end
  | (BUnknown, b1, h1) =>
      (* Can't determine - return original patterns *)
      ([p1; p2], b1, h1)
  end.

(* Observer sees pattern with Spuren generation *)
Definition can_see_spur (obs : Observer) (p : Pattern) 
  : (Bool3 * Observer) :=
  match le_fin_b3 (sensitivity obs) (fst (strength p)) (obs_budget obs) with
  | (result, b', h) => 
      (result, 
       {| sensitivity := sensitivity obs; 
          obs_budget := b';
          obs_spur := add_spur (obs_spur obs) h |})
  end.

(* Observation exhausts observer and generates Spuren *)
Definition observe_interference_spur (obs : Observer) (p1 p2 : Pattern) 
  : (list Pattern * Observer) :=
  match interfere_spur p1 p2 (obs_budget obs) with
  | (patterns, b', h) =>
      (patterns, 
       {| sensitivity := sensitivity obs; 
          obs_budget := b';
          obs_spur := add_spur (obs_spur obs) h |})
  end.

(******************************************************************************)
(* NEURONS WITH SPUREN                                                         *)
(******************************************************************************)

Record Neuron := {
  neuron_id : Fin;
  threshold : FinProb;
  accumulated : FinProb;
  refractory : Fin;
  maintained_patterns : list Fin;
  neuron_budget : Budget;
  neuron_spur : Spuren
}.

(* Check if pattern location is maintained - generates Spuren *)
Fixpoint is_maintained_spur (locs : list Fin) (p : Fin) (b : Budget) 
  : (bool * Budget * Spuren) :=
  match locs, b with
  | [], _ => (false, b, fz)
  | _, fz => (false, fz, fz)
  | h :: t, _ =>
      match fin_eq_b_spur h p b with
      | (true, b', h) => (true, b', h)
      | (false, b', h) => 
          match is_maintained_spur t p b' with
          | (res, b'', h') => (res, b'', add_spur h h')
          end
      end
  end.

(* Neuron observes pattern - generates Spuren *)
Definition observe_pattern_spur (n : Neuron) (p : Pattern) : Neuron :=
  match le_fin_b3 (fs fz) (refractory n) (neuron_budget n) with
  | (BTrue, _, _) => n  (* Refractory - no change *)
  | (_, b', h1) =>
      match is_maintained_spur (maintained_patterns n) (location p) b' with
      | (true, b'', h2) =>
          match prob_le_b3 (accumulated n) (strength p) b'' with
          | (res, b''', h3) =>
              let new_acc := match res with
                            | BTrue => strength p
                            | _ => accumulated n
                            end in
              {| neuron_id := neuron_id n;
                 threshold := threshold n;
                 accumulated := new_acc;
                 refractory := refractory n;
                 maintained_patterns := maintained_patterns n;
                 neuron_budget := b''';
                 neuron_spur := add_spur (neuron_spur n) 
                                        (add_spur h1 (add_spur h2 h3)) |}
          end
      | (false, b'', h2) => 
          {| neuron_id := neuron_id n;
             threshold := threshold n;
             accumulated := accumulated n;
             refractory := refractory n;
             maintained_patterns := maintained_patterns n;
             neuron_budget := b'';
             neuron_spur := add_spur (neuron_spur n) (add_spur h1 h2) |}
      end
  end.

(* Fire neuron - generates Spuren like any operation *)
Definition fire_neuron_spur (n : Neuron) : (Neuron * option Pattern) :=
  match neuron_budget n with
  | fz => (n, None)
  | _ =>
      match refractory n with
      | fs _ => (n, None)  (* Still refractory *)
      | fz =>
          match prob_le_b3 (threshold n) (accumulated n) (neuron_budget n) with
          | (BTrue, b', h) =>
              (* FIRING! One tick refractory, normal Spuren *)
              ({| neuron_id := neuron_id n;
                  threshold := threshold n;
                  accumulated := (fs fz, snd (accumulated n));
                  refractory := operation_cost;  (* One tick refractory *)
                  maintained_patterns := maintained_patterns n;
                  neuron_budget := b';
                  neuron_spur := add_spur (neuron_spur n) h |},
               Some {| location := neuron_id n; strength := accumulated n |})
          | (_, b', h) =>
              ({| neuron_id := neuron_id n;
                  threshold := threshold n;
                  accumulated := accumulated n;
                  refractory := refractory n;
                  maintained_patterns := maintained_patterns n;
                  neuron_budget := b';
                  neuron_spur := add_spur (neuron_spur n) h |}, None)
          end
      end
  end.

(******************************************************************************)
(* BACKWARD COMPATIBILITY WRAPPERS                                           *)
(******************************************************************************)

(* Old decay function *)
Definition decay_with_budget (p : FinProb) (b : Budget) : (FinProb * Budget) :=
  match decay_with_spur p b with
  | (res, b', _) => (res, b')
  end.

(* Old interfere function *)
Definition interfere (p1 p2 : Pattern) (b : Budget) : (list Pattern * Budget) :=
  match interfere_spur p1 p2 b with
  | (patterns, b', _) => (patterns, b')
  end.

Definition interfere_with_budget := interfere.

(* Old can_see - collapse Bool3 to bool *)
Definition can_see (obs : Observer) (p : Pattern) : (bool * Observer) :=
  match can_see_spur obs p with
  | (res, obs') => (collapse3 res, obs')
  end.

Definition can_see_with_budget := can_see.

(* Old observe_interference *)
Definition observe_interference (obs : Observer) (p1 p2 : Pattern) 
  : (list Pattern * Observer) :=
  observe_interference_spur obs p1 p2.

(* Old is_maintained *)
Definition is_maintained (locs : list Fin) (p : Fin) (b : Budget) : (bool * Budget) :=
  match is_maintained_spur locs p b with
  | (res, b', _) => (res, b')
  end.

Definition is_maintained_with_budget (n : Neuron) (p : Pattern) (b : Budget)
  : (bool * Budget) :=
  is_maintained (maintained_patterns n) (location p) b.

(* Old observe_pattern *)
Definition observe_pattern (n : Neuron) (p : Pattern) : Neuron :=
  observe_pattern_spur n p.

Definition observe_pattern_with_budget := observe_pattern.

(* Old fire_neuron *)
Definition fire_neuron (n : Neuron) : (Neuron * option Pattern) :=
  fire_neuron_spur n.

Definition fire_neuron_with_budget := fire_neuron.

(* Should fire - for compatibility *)
Definition should_fire (n : Neuron) : bool :=
  match neuron_budget n with
  | fz => false
  | _ =>
      match refractory n with
      | fz => 
          match prob_le_b (threshold n) (accumulated n) (neuron_budget n) with
          | (result, _) => result
          end
      | _ => false
      end
  end.

Definition should_fire_with_budget (n : Neuron) : (bool * Budget) :=
  (should_fire n, neuron_budget n).

(* Process patterns *)
Fixpoint process_patterns (n : Neuron) (ps : list Pattern) : Neuron :=
  match ps with
  | [] => n
  | p :: rest =>
      match neuron_budget n with
      | fz => n
      | _ => process_patterns (observe_pattern_spur n p) rest
      end
  end.

Definition process_patterns_with_budget := process_patterns.

(* Tick refractory *)
Definition tick_refractory (n : Neuron) : Neuron :=
  {| neuron_id := neuron_id n;
     threshold := threshold n;
     accumulated := accumulated n;
     refractory := match refractory n with
                   | fz => fz
                   | fs r => r
                   end;
     maintained_patterns := maintained_patterns n;
     neuron_budget := neuron_budget n;
     neuron_spur := neuron_spur n |}.

Definition tick_refractory_with_budget := tick_refractory.

(******************************************************************************)
(* LAYERS - Complete version                                                  *)
(******************************************************************************)

Record Layer := {
  layer_id : Fin;
  neurons : list Neuron;
  input_patterns : list Pattern;
  output_patterns : list Pattern;
  layer_budget : Budget
}.

(* Process one neuron in layer context *)
Definition process_neuron_in_layer (n : Neuron) (inputs : list Pattern) : (Neuron * option Pattern) :=
  let n' := process_patterns n inputs in
  let n'' := tick_refractory n' in
  fire_neuron n''.

(* Layer step - simplified but complete *)
Definition layer_step (l : Layer) : Layer :=
  match layer_budget l with
  | fz => l
  | _ =>
      let results := map (fun n => process_neuron_in_layer n (input_patterns l)) (neurons l) in
      let new_neurons := map fst results in
      let new_patterns := fold_left (fun acc r =>
        match snd r with
        | Some p => p :: acc
        | None => acc
        end) results [] in
      {| layer_id := layer_id l;
         neurons := new_neurons;
         input_patterns := input_patterns l;
         output_patterns := new_patterns;
         layer_budget := match layer_budget l with
                        | fz => fz
                        | fs b => b
                        end |}
  end.

Definition layer_step_with_budget := layer_step.

(* Connect layers *)
Definition feed_forward (l1 l2 : Layer) : Layer :=
  {| layer_id := layer_id l2;
     neurons := neurons l2;
     input_patterns := output_patterns l1;
     output_patterns := output_patterns l2;
     layer_budget := layer_budget l2 |}.

(******************************************************************************)
(* EXPORTS FOR OTHER MODULES                                                  *)
(******************************************************************************)

Definition Pattern_ext := Pattern.
Definition Neuron_ext := Neuron.
Definition Layer_ext := Layer.
Definition Observer_ext := Observer.

(******************************************************************************)
(* SPUR CONSERVATION AXIOMS                                                  *)
(******************************************************************************)

(* Helper: decay_with_spur conserves budget *)
Lemma decay_with_spur_conservation : forall p b p' b' h,
  decay_with_spur p b = (p', b', h) -> add_spur h b' = b.
Proof.
  intros [n d] b p' b' h Heq.
  simpl in Heq.
  destruct b as [| b0].
  - inversion Heq; subst. apply add_spur_fz_l.
  - destruct n as [| [| n']].
    + inversion Heq; subst. unfold operation_cost.
      rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + inversion Heq; subst. unfold operation_cost.
      rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
    + inversion Heq; subst. unfold operation_cost.
      rewrite add_spur_fs_l. rewrite add_spur_fz_l. reflexivity.
Qed.

Lemma pattern_spur_conservation : forall p1 p2 b patterns b' h,
  interfere_spur p1 p2 b = (patterns, b', h) ->
  add_spur h b' = b.
Proof.
  intros p1 p2 b patterns b' h Heq.
  unfold interfere_spur in Heq.
  destruct (fin_eq_b3 (location p1) (location p2) b) as [[r b1] h1] eqn:Heq3.
  destruct r.
  - (* BTrue *)
    destruct (decay_with_spur (strength p1) b1) as [[s1' b2] h2] eqn:Hd1.
    destruct (decay_with_spur (strength p2) b2) as [[s2' b3] h3] eqn:Hd2.
    inversion Heq; subst.
    rewrite add_spur_assoc. rewrite add_spur_assoc.
    rewrite (decay_with_spur_conservation _ _ _ _ _ Hd2).
    rewrite (decay_with_spur_conservation _ _ _ _ _ Hd1).
    exact (spur_conservation_eq3 _ _ _ _ _ _ Heq3).
  - (* BFalse *)
    destruct (decay_with_spur (strength p1) b1) as [[s1' b2] h2] eqn:Hd1.
    destruct (decay_with_spur (strength p2) b2) as [[s2' b3] h3] eqn:Hd2.
    inversion Heq; subst.
    rewrite add_spur_assoc. rewrite add_spur_assoc.
    rewrite (decay_with_spur_conservation _ _ _ _ _ Hd2).
    rewrite (decay_with_spur_conservation _ _ _ _ _ Hd1).
    exact (spur_conservation_eq3 _ _ _ _ _ _ Heq3).
  - (* BUnknown *)
    inversion Heq; subst.
    exact (spur_conservation_eq3 _ _ _ _ _ _ Heq3).
Qed.

(* Helper: add_spur never decreases in Z — no lia, no omega *)
Lemma add_spur_nondecreasing_Z : forall a h,
  (fin_to_Z_PROOF_ONLY (add_spur a h) >= fin_to_Z_PROOF_ONLY a)%Z.
Proof.
  intros a h. induction h as [| h' IH].
  - simpl. apply Z.le_ge. apply Z.le_refl.
  - simpl.
    apply Z.le_ge.
    apply Z.le_trans with (fin_to_Z_PROOF_ONLY (add_spur a h')).
    + apply Z.ge_le. exact IH.
    + generalize (fin_to_Z_PROOF_ONLY (add_spur a h')); intro x.
      rewrite <- (Z.add_0_l x) at 1.
      apply (proj1 (Z.add_le_mono_r 0 1 x)).
      discriminate.
Qed.

(* Observation Spuren never decreases — proven from definition *)
Lemma observation_heat_principle : forall obs p res obs',
  can_see_spur obs p = (res, obs') ->
  (fin_to_Z_PROOF_ONLY (obs_spur obs') >= fin_to_Z_PROOF_ONLY (obs_spur obs))%Z.
Proof.
  intros obs p res obs' Heq.
  unfold can_see_spur in Heq.
  destruct (le_fin_b3 (sensitivity obs) (fst (strength p)) (obs_budget obs))
    as [[r b'] h] eqn:Hle.
  inversion Heq; subst. simpl.
  apply add_spur_nondecreasing_Z.
Qed.

(* Helper: le_fin_b3 is monotone — if s2 ≤ x returns BTrue and s1 ≤ s2, then s1 ≤ x returns BTrue *)
Lemma le_fin_b3_monotone : forall s1 s2,
  leF s1 s2 ->
  forall x b b1 h1,
  le_fin_b3 s2 x b = (BTrue, b1, h1) ->
  exists b3 h3, le_fin_b3 s1 x b = (BTrue, b3, h3).
Proof.
  intros s1 s2 Hle. induction Hle as [m | n m Hle' IH].
  - (* leF_z: s1 = fz, s2 = m *)
    intros x b b1 h1 H.
    destruct b as [| b'].
    + (* b = fz: fixpoint needs first-arg constructor to unfold *)
      destruct m; simpl in H; inversion H.
    + simpl. eexists. eexists. reflexivity.
  - (* leF_ss: s1 = fs n, s2 = fs m — first arg is constructor *)
    intros x b b1 h1 H.
    destruct b as [| b'].
    + simpl in H. inversion H.
    + destruct x as [| x'].
      * simpl in H. inversion H.
      * simpl in H.
        destruct (le_fin_b3 m x' b') as [[[] b2] h2] eqn:Hm;
          try (inversion H; fail).
        (* Only BTrue case survives — Hm : le_fin_b3 m x' b' = (BTrue, b2, h2) *)
        specialize (IH x' b' b2 h2 Hm).
        destruct IH as [b3 [h3 Hn]].
        simpl. rewrite Hn.
        eexists. eexists. reflexivity.
Qed.

(* The pattern hierarchy theorem — proven from monotonicity *)
Lemma strong_sees_more : forall p b s1 s2,
  b <> fz ->
  leF s1 s2 ->
  fst (can_see {| sensitivity := s2; obs_budget := b; obs_spur := fz |} p) = true ->
  fst (can_see {| sensitivity := s1; obs_budget := b; obs_spur := fz |} p) = true.
Proof.
  intros p b s1 s2 Hb Hle Hsee.
  unfold can_see, can_see_spur in *.
  simpl (sensitivity _) in *. simpl (obs_budget _) in *. simpl (obs_spur _) in *.
  destruct (le_fin_b3 s2 (fst (strength p)) b) as [[[] b2] h2] eqn:Hs2;
    simpl in Hsee; try discriminate.
  pose proof (le_fin_b3_monotone _ _ Hle _ _ _ _ Hs2) as [b3 [h3 Hs1]].
  rewrite Hs1. simpl. reflexivity.
Qed.

End Void_Pattern.