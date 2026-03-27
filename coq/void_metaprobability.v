(******************************************************************************)
(* void_metaprobability.v - PROBABILITY OF PROBABILITY                        *)
(* When you're uncertain about your uncertainty                               *)
(* CLEANED: All operations cost one tick, no magic hierarchies                *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Metaprobability.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* FUNDAMENTAL CONSTANT                                                       *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* HELPER DEFINITIONS                                                          *)
(******************************************************************************)

(* Multiply probabilities - costs one tick *)
Definition mult_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      let (n1, d1) := p1 in
      let (n2, d2) := p2 in
      match mult_fin n1 n2 b' with
      | (new_n, b1) =>
          match mult_fin d1 d2 b1 with
          | (new_d, b2) => ((new_n, new_d), b2)
          end
      end
  end.

(* Difference between probabilities - costs one tick *)
Definition prob_diff_with_budget (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      let (n1, d1) := p1 in
      let (n2, d2) := p2 in
      match mult_fin n1 d2 b' with
      | (v1, b1) =>
          match mult_fin n2 d1 b1 with
          | (v2, b2) =>
              match mult_fin d1 d2 b2 with
              | (common_d, b3) =>
                  match le_fin_b v1 v2 b3 with
                  | (true, b4) => 
                      match sub_fin v2 v1 b4 with
                      | (diff_n, b5) => ((diff_n, common_d), b5)
                      end
                  | (false, b4) =>
                      match sub_fin v1 v2 b4 with
                      | (diff_n, b5) => ((diff_n, common_d), b5)
                      end
                  end
              end
          end
      end
  end.

(* Boolean helper *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(******************************************************************************)
(* METAPROBABILITY - Uncertainty about uncertainty                           *)
(******************************************************************************)

Inductive MetaProb :=
  | Sharp : FinProb -> MetaProb
    (* "I know exactly" *)
  | Fuzzy : FinProb -> FinProb -> FinProb -> MetaProb  
    (* (lower, center, upper) bounds *)
  | Vague : FinProb -> FinProb -> MetaProb
    (* "Somewhere between these" *)
  | Exhausted : MetaProb
    (* "I have no idea" *)
  | Void : MetaProb
    (* Complete uncertainty *).

(******************************************************************************)
(* CONFIDENCE OPERATIONS - All cost one tick                                 *)
(******************************************************************************)

(* Confidence naturally decays without maintenance *)
Definition decay_confidence (mp : MetaProb) : MetaProb :=
  match mp with
  | Sharp p => Fuzzy p p p
  | Fuzzy l c u => 
      let l' := match l with
                | (fs n, d) => (n, d)
                | _ => l
                end in
      let u' := match u with
                | (n, fs (fs d)) => (n, fs (fs (fs d)))
                | _ => u
                end in
      Vague l' u'
  | Vague l u => Exhausted
  | Exhausted => Void
  | Void => Void
  end.

(* Maintaining confidence costs one tick regardless of level *)
Definition maintain_confidence_b (mp : MetaProb) (b : Budget) 
  : (MetaProb * Budget) :=
  match b with
  | fz => (decay_confidence mp, fz)  (* No budget - forced decay *)
  | fs b' => (mp, b')  (* One tick to maintain any confidence level *)
  end.

(******************************************************************************)
(* METAPROBABILITY ARITHMETIC                                                *)
(******************************************************************************)

(* Adding metaprobabilities - costs one tick *)
Definition add_metaprob_b (mp1 mp2 : MetaProb) (b : Budget) 
  : (MetaProb * Budget) :=
  match b with
  | fz => (Exhausted, fz)
  | fs b' =>
      match mp1, mp2 with
      | Void, _ => (Void, b')
      | _, Void => (Void, b')
      | Exhausted, _ => (Exhausted, b')
      | _, Exhausted => (Exhausted, b')
      
      | Sharp p1, Sharp p2 =>
          match add_prob_b p1 p2 b' with
          | (sum, b'') => (Sharp sum, b'')
          end
          
      | Sharp p, Fuzzy l c u
      | Fuzzy l c u, Sharp p =>
          match add_prob_b p c b' with
          | (new_c, b'') => (Fuzzy l new_c u, b'')
          end
          
      | Fuzzy l1 c1 u1, Fuzzy l2 c2 u2 =>
          match add_prob_b c1 c2 b' with
          | (new_c, b'') => (Fuzzy l1 new_c u2, b'')
          end
          
      | Vague l1 u1, Vague l2 u2 =>
          match add_prob_b l1 u2 b' with
          | (new_bound, b'') => (Vague l1 new_bound, b'')
          end
          
      | _, _ => (Exhausted, b')
      end
  end.

(******************************************************************************)
(* BAYESIAN UPDATE - Costs one tick                                          *)
(******************************************************************************)

Definition tired_update_b (prior : MetaProb) (evidence : FinProb) (b : Budget)
  : (MetaProb * Budget) :=
  match b with
  | fz => (Exhausted, fz)
  | fs b' =>
      match prior with
      | Void => (Void, b')
      | Exhausted => (Exhausted, b')
      | Sharp p =>
          match mult_prob_b p evidence b' with
          | (updated, b'') => (Sharp updated, b'')
          end
      | Fuzzy l c u =>
          match mult_prob_b c evidence b' with
          | (new_c, b'') => (Fuzzy l new_c u, b'')
          end
      | Vague l u =>
          (* Update midpoint *)
          match add_prob_b l u b' with
          | (sum, b1) =>
              match mult_prob_b sum evidence b1 with
              | (updated, b2) => (Vague l u, b2)
              end
          end
      end
  end.

(******************************************************************************)
(* CONFIDENCE COMPOSITION - Second-order uncertainty                         *)
(******************************************************************************)

Inductive MetaMetaProb :=
  | Certain : MetaProb -> MetaMetaProb
  | Doubtful : MetaProb -> MetaProb -> MetaMetaProb
  | Confused : MetaMetaProb.

(* Second-order operations also cost one tick *)
Definition maintain_metameta_b (mmp : MetaMetaProb) (b : Budget)
  : (MetaMetaProb * Budget) :=
  match b with
  | fz => (Confused, fz)
  | fs b' => (mmp, b')
  end.

(******************************************************************************)
(* PROBABILITY COLLAPSE - Costs one tick                                     *)
(******************************************************************************)

Definition observe_metaprob_b (mp : MetaProb) (observer_energy : Budget)
  : (FinProb * Budget) :=
  match observer_energy with
  | fz => (half, fz)
  | fs b' =>
      match mp with
      | Void => (half, b')
      | Exhausted => (half, b')
      | Sharp p => (p, b')
      | Fuzzy l c u => (c, b')
      | Vague l u =>
          match add_prob_b l u b' with
          | (sum, b'') => ((fst sum, fs (snd sum)), b'')
          end
      end
  end.

(******************************************************************************)
(* CONFIDENCE NAVIGATION - One tick per step                                 *)
(******************************************************************************)

(* Navigate toward sustainable confidence - costs one tick per step *)
Fixpoint seek_sustainable_confidence_b (mp : MetaProb) (steps : Fin) (b : Budget)
  : (MetaProb * Budget) :=
  match steps, b with
  | fz, _ => (mp, b)
  | _, fz => (Void, fz)
  | fs steps', fs b' =>
      (* Each step costs one tick to decay confidence *)
      seek_sustainable_confidence_b (decay_confidence mp) steps' b'
  end.

(******************************************************************************)
(* PROBABILITY RANGES                                                         *)
(******************************************************************************)

Inductive ProbRange :=
  | Exact : FinProb -> ProbRange
  | Interval : FinProb -> FinProb -> FinProb -> ProbRange
  | Band : FinProb -> FinProb -> ProbRange  (* Simplified - no confidence level *)
  | Spread : FinProb -> ProbRange
  | Unknown : ProbRange.

(* Range operations cost one tick *)
Definition combine_ranges_b (r1 r2 : ProbRange) 
                           (op : FinProb -> FinProb -> Budget -> (FinProb * Budget)) 
                           (b : Budget) 
  : (ProbRange * Budget) :=
  match b with
  | fz => (Unknown, fz)
  | fs b' =>
      match r1, r2 with
      | Unknown, _ => (Unknown, b')
      | _, Unknown => (Unknown, b')
      
      | Exact p1, Exact p2 =>
          match op p1 p2 b' with
          | (result, b'') => (Exact result, b'')
          end
          
      | Interval min1 likely1 max1, Interval min2 likely2 max2 =>
          match op likely1 likely2 b' with
          | (new_likely, b'') => (Interval min1 new_likely max2, b'')
          end
          
      | Band center1 width1, Band center2 width2 =>
          match op center1 center2 b' with
          | (new_center, b'') =>
              match add_prob_b width1 width2 b'' with
              | (combined_width, b''') =>
                  (Band new_center combined_width, b''')
              end
          end
          
      | _, _ => (Unknown, b')
      end
  end.

(* Check range containment - costs one tick *)
Definition in_range_b (p : FinProb) (r : ProbRange) (b : Budget) 
  : (FinProb * Budget) :=
  match b with
  | fz => (half, fz)
  | fs b' =>
      match r with
      | Unknown => (half, b')
      | Exact p' =>
          match prob_eq_b p p' b' with
          | (true, b'') => ((fs (fs fz), fs (fs (fs fz))), b'')  (* 2/3 *)
          | (false, b'') => ((fs fz, fs (fs (fs fz))), b'')     (* 1/3 *)
          end
      | Interval min likely max =>
          match le_fin_b (fst p) (fst max) b' with
          | (in_range, b'') =>
              if in_range then
                ((fs fz, fs (fs fz)), b'')  (* 1/2 - in range *)
              else
                ((fs fz, fs (fs (fs (fs fz)))), b'')  (* 1/4 - out *)
          end
      | Band center width =>
          match prob_diff_with_budget p center b' with
          | (dist, b'') => (dist, b'')  (* Distance is confidence *)
          end
      | Spread center => (half, b')
      end
  end.

(* Range evolution - costs one tick per step *)
Fixpoint evolve_range_b (r : ProbRange) (time_steps : Fin) (b : Budget) 
  : (ProbRange * Budget) :=
  match time_steps, b with
  | fz, _ => (r, b)
  | _, fz => (Unknown, fz)
  | fs steps', fs b' =>
      match r with
      | Exact p => evolve_range_b (Interval p p p) steps' b'
      | Interval min likely max =>
          (* Simplified spreading *)
          evolve_range_b (Band likely min) steps' b'
      | Band center width =>
          (* Width naturally increases *)
          evolve_range_b (Spread center) steps' b'
      | Spread _ => (Unknown, b')
      | Unknown => (Unknown, b')
      end
  end.

(******************************************************************************)
(* THEOREMS — The claims above are not philosophy. They are Qed.             *)
(******************************************************************************)

(* Void is the thermodynamic ground state: decay cannot escape it. *)
Theorem void_is_fixed_point : decay_confidence Void = Void.
Proof. reflexivity. Qed.

(* Exhausted decays to Void in one step. *)
Theorem exhausted_decays_to_void : decay_confidence Exhausted = Void.
Proof. reflexivity. Qed.

(* ANY metaprobability decays to Void in at most 4 steps. *)
Theorem decay_terminates : forall mp,
  decay_confidence (decay_confidence (decay_confidence (decay_confidence mp))) = Void.
Proof.
  intro mp. destruct mp; reflexivity.
Qed.

(* Once Void, always Void — iterated decay is absorbed. *)
Theorem decay_idempotent_at_void : forall n,
  seek_sustainable_confidence_b Void n fz = (Void, fz).
Proof.
  intro n. destruct n; reflexivity.
Qed.

(* No budget forces decay — you cannot maintain without paying. *)
Theorem no_budget_forces_decay : forall mp,
  maintain_confidence_b mp fz = (decay_confidence mp, fz).
Proof. intro mp. reflexivity. Qed.

(* Maintenance with budget preserves confidence exactly. *)
Theorem maintenance_preserves : forall mp b,
  maintain_confidence_b mp (fs b) = (mp, b).
Proof. intros. reflexivity. Qed.

(* Observing Void yields half — maximum entropy. *)
Theorem observe_void_is_half : forall b,
  observe_metaprob_b Void (fs b) = (half, b).
Proof. intros. reflexivity. Qed.

(* Observing Exhausted also yields half — no information left. *)
Theorem observe_exhausted_is_half : forall b,
  observe_metaprob_b Exhausted (fs b) = (half, b).
Proof. intros. reflexivity. Qed.

(* Void absorbs addition — uncertainty is contagious. *)
Theorem void_absorbs_add_l : forall mp b,
  fst (add_metaprob_b Void mp (fs b)) = Void.
Proof. intros mp b. destruct mp; reflexivity. Qed.

Theorem void_absorbs_add_r : forall mp b,
  fst (add_metaprob_b mp Void (fs b)) = Void.
Proof.
  intros mp b. destruct mp; reflexivity.
Qed.

(* No budget yields Exhausted — not Void, because you tried. *)
Theorem no_budget_add_exhausted : forall mp1 mp2,
  add_metaprob_b mp1 mp2 fz = (Exhausted, fz).
Proof. intros. reflexivity. Qed.

(* Void absorbs Bayesian update — evidence cannot update ignorance. *)
Theorem void_absorbs_update : forall ev b,
  tired_update_b Void ev (fs b) = (Void, b).
Proof. intros. reflexivity. Qed.

(* Exhausted absorbs update — too tired to learn. *)
Theorem exhausted_absorbs_update : forall ev b,
  tired_update_b Exhausted ev (fs b) = (Exhausted, b).
Proof. intros. reflexivity. Qed.

(* Second-order confusion is also a fixed point. *)
Theorem confused_is_ground_state : forall mmp,
  maintain_metameta_b mmp fz = (Confused, fz).
Proof. intros. reflexivity. Qed.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition MetaProb_ext := MetaProb.
Definition ProbRange_ext := ProbRange.
Definition tired_update_b_ext := tired_update_b.
Definition observe_metaprob_b_ext := observe_metaprob_b.
Definition combine_ranges_b_ext := combine_ranges_b.
Definition in_range_b_ext := in_range_b.

End Void_Metaprobability.