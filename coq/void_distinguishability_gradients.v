(* void_distinguishability_gradients.v - Patterns seek uniqueness or blend *)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_distinguishability.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistinguishabilityGradients.

(* Import all existing definitions *)
Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Distinguishability.
Import Void_Arithmetic.
Import ListNotations.
Open Scope list_scope.

(* Missing helper definitions *)
Definition ten : Fin := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).

(* Decay: reduce numerator by 1, preserving probability structure *)
Definition decay (p : FinProb) : FinProb :=
  match p with
  | (fs (fs n), d) => (fs n, d)
  | other => other
  end.

(* Non-budgeted equality for compatibility *)
Definition fin_eq (n m : Fin) : bool :=
  fst (fin_eq_b n m initial_budget).

(* Non-budgeted less-equal for compatibility *)
Definition le_fin (n m : Fin) : bool :=
  fst (le_fin_b n m initial_budget).

(* Non-budgeted distance for compatibility *)
Definition dist_fin (n m : Fin) : Fin :=
  fst (dist_fin_b n m initial_budget).

(* Non-budgeted add for compatibility *)
Definition add_simple (n m : Fin) : Fin :=
  fst (add_fin_b n m initial_budget).

(* Predecessor function *)
Definition pred_fin (n : Fin) : Fin :=
  match n with
  | fz => fz
  | fs n' => n'
  end.

(* Boolean operations *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Check if Fin is even *)
Fixpoint even_fin (n : Fin) : bool :=
  match n with
  | fz => true
  | fs fz => false
  | fs (fs n') => even_fin n'
  end.

(* Helper: forallb *)
Fixpoint forallb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | h :: t => andb (f h) (forallb f t)
  end.

(* Helper: existsb *)
Fixpoint existsb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t => if f h then true else existsb f t
  end.

(* Helper: get patterns at a specific location *)
Definition patterns_at_location (loc : Fin) (patterns : list Pattern) : list Pattern :=
  filter (fun p => fin_eq (location p) loc) patterns.

(* Helper: count patterns at location *)
Definition count_at_location (loc : Fin) (patterns : list Pattern) : Fin :=
  fold_left (fun acc p => if fin_eq (location p) loc then fs acc else acc) 
            patterns fz.

(* Helper: sample nearby locations *)
Definition nearby_locations (center : Fin) : list Fin :=
  match center with
  | fz => [fz; fs fz; fs (fs fz)]
  | fs fz => [fz; fs fz; fs (fs fz); fs (fs (fs fz))]
  | _ => [pred_fin center; center; fs center]
  end.

(* Measure local crowding - how many patterns share this location *)
Definition local_crowding (loc : Fin) (patterns : list Pattern) : Fin :=
  count_at_location loc patterns.

(* Simplified distinguishability at a location *)
(* More patterns at location = less distinguishable *)
Definition location_distinguishability (p : Pattern) (loc : Fin) 
                                       (patterns : list Pattern) : FinProb :=
  let crowd := local_crowding loc patterns in
  match crowd with
  | fz => (fs (fs (fs fz)), fs (fs (fs (fs fz))))      (* 3/4 - very distinguishable *)
  | fs fz => half                                        (* 1/2 - somewhat distinguishable *)
  | fs (fs fz) => (fs fz, fs (fs (fs fz)))             (* 1/3 - crowded *)
  | _ => (fs fz, fs (fs (fs (fs fz))))                 (* 1/4 - very crowded *)
  end.

(* Find location with maximum distinguishability *)
Definition distinction_gradient (p : Pattern) (neighbors : list Pattern) : Fin :=
  let candidates := nearby_locations (location p) in
  match candidates with
  | [] => location p
  | loc :: rest =>
      fold_left (fun best_loc new_loc =>
        let best_dist := location_distinguishability p best_loc neighbors in
        let new_dist := location_distinguishability p new_loc neighbors in
        if le_fin (fst best_dist) (fst new_dist) then new_loc else best_loc
      ) rest loc
  end.

(* Inverse - find where pattern blends in most *)
Definition blending_gradient (p : Pattern) (neighbors : list Pattern) : Fin :=
  let candidates := nearby_locations (location p) in
  match candidates with
  | [] => location p
  | loc :: rest =>
      fold_left (fun best_loc new_loc =>
        let best_crowd := local_crowding best_loc neighbors in
        let new_crowd := local_crowding new_loc neighbors in
        if le_fin best_crowd new_crowd then new_loc else best_loc
      ) rest loc
  end.

(* Movement strategies based on pattern strength *)
Inductive DistinctionStrategy :=
  | Individuate    (* Seek uniqueness *)
  | Conform        (* Blend in *)
  | Oscillate      (* Alternate between both *).

(* Choose strategy based on pattern state *)
Definition choose_distinction_strategy (p : Pattern) : DistinctionStrategy :=
  match fst (strength p) with
  | fz => Conform              (* Dead patterns don't care *)
  | fs fz => Conform           (* Weak patterns hide *)
  | fs (fs fz) => Oscillate    (* Medium patterns explore *)
  | _ => Individuate           (* Strong patterns distinguish *)
  end.

(* Move according to strategy *)
Definition distinction_move (p : Pattern) (neighbors : list Pattern) 
                           (phase : Fin) : Pattern :=
  let strategy := choose_distinction_strategy p in
  let new_loc := 
    match strategy with
    | Individuate => distinction_gradient p neighbors
    | Conform => blending_gradient p neighbors
    | Oscillate => 
        if even_fin phase then 
          distinction_gradient p neighbors
        else 
          blending_gradient p neighbors
    end in
  {| location := new_loc;
     strength := if fin_eq new_loc (location p) then
                   strength p  (* No move, no decay *)
                 else
                   decay (strength p) |}.

(* System-wide distinguishability measure *)
Definition system_distinguishability (patterns : list Pattern) : FinProb :=
  match patterns with
  | [] => half
  | _ =>
      (* Count unique locations *)
      let location_counts := map (fun p => local_crowding (location p) patterns) patterns in
      (* Higher crowding = lower distinguishability *)
      match fold_left add_simple location_counts fz with
      | fz => (fs (fs (fs fz)), fs (fs (fs (fs fz))))  (* All alone = 3/4 *)
      | fs fz => half                                    (* Some crowding = 1/2 *)
      | fs (fs _) => (fs fz, fs (fs (fs fz)))          (* Very crowded = 1/3 *)
      end
  end.

(* Crisis: too uniform - inject diversity *)
Definition uniformity_crisis (patterns : list Pattern) : bool :=
  match patterns with
  | [] => false
  | p :: rest =>
      (* Check if all patterns at same location *)
      forallb (fun p' => fin_eq (location p) (location p')) rest
  end.

(* Emergency diversity injection *)
Definition diversity_injection (patterns : list Pattern) : list Pattern :=
  match patterns with
  | [] => []
  | [p] => [p]
  | p1 :: p2 :: rest =>
      (* Force patterns to opposite ends *)
      {| location := fz; 
         strength := strength p1 |} ::
      {| location := ten;
         strength := strength p2 |} ::
      rest
  end.

(* Repulsion field - patterns create zones others avoid *)
Definition repulsion_strength (p : Pattern) : Fin :=
  match fst (strength p) with
  | fz => fz
  | fs fz => fz
  | fs (fs fz) => fs fz
  | _ => fs (fs fz)  (* Strong patterns repel more *)
  end.

(* Check if location is too close to strong pattern *)
Definition in_repulsion_zone (loc : Fin) (p : Pattern) : bool :=
  le_fin (dist_fin loc (location p)) (repulsion_strength p).

(* Gradient considering repulsion *)
Definition repulsion_aware_gradient (p : Pattern) (neighbors : list Pattern) : Fin :=
  let candidates := nearby_locations (location p) in
  (* Filter out locations in repulsion zones of strong patterns *)
  let valid_locs := filter (fun loc =>
    negb (existsb (fun other => 
      andb (negb (fin_eq (location p) (location other)))
           (in_repulsion_zone loc other)
    ) neighbors)
  ) candidates in
  match valid_locs with
  | [] => location p  (* No valid moves *)
  | loc :: _ => loc   (* Take first valid *)
  end.

End DistinguishabilityGradients.