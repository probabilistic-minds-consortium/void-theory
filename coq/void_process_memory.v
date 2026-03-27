(******************************************************************************)
(* void_process_memory.v - FINITE PROCESS MEMORY PRIMITIVES                  *)
(* Patterns that know how to regenerate themselves, approximately            *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Process_Memory.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* HELPER FUNCTIONS - Define what we need locally                            *)
(******************************************************************************)

(* Decay for probabilities - reduce strength *)
Definition decay_prob (p : FinProb) : FinProb :=
  match p with
  | (fs (fs n), d) => (fs n, d)  (* Reduce numerator *)
  | other => other
  end.

(* Simple length function for lists *)
Fixpoint length_fin {A : Type} (l : list A) : Fin :=
  match l with
  | [] => fz
  | _ :: t => fs (length_fin t)
  end.

(* Simple filter *)
Fixpoint filter {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => if f h then h :: filter f t else filter f t
  end.

(* Check if Spuren is less than threshold *)
Definition le_spur (h1 h2 : Spuren) : bool :=
  match le_fin_b h1 h2 initial_budget with
  | (b, _) => b
  end.

(* Decay with budget tracking *)
Definition decay_with_budget (p : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p, fz)
  | fs b' => (decay_prob p, b')
  end.

(******************************************************************************)
(* HELPER - Probability "closeness" without distance                         *)
(******************************************************************************)

(* Check if two probabilities are indistinguishable enough *)
Definition probs_similar_b (p1 p2 : FinProb) (tolerance : FinProb) (b : Budget)
  : (bool * Budget) :=
  match prob_eq_b p1 p2 b with
  | (true, b') => (true, b')  (* Exact match *)
  | (false, b') =>
      (* Check if both are "small" or both are "large" *)
      match prob_le_b p1 tolerance b' with
      | (true, b'') =>
          prob_le_b p2 tolerance b''  (* Both small *)
      | (false, b'') =>
          match prob_le_b tolerance p1 b'' with
          | (true, b3) => prob_le_b tolerance p2 b3  (* Both large *)
          | (false, b3) => (false, b3)
          end
      end
  end.

(******************************************************************************)
(* CORE PRIMITIVE: Approximate regeneration cycles                           *)
(******************************************************************************)

Record ProcessGhost := {
  trigger : Pattern;                (* Activation pattern *)
  echo_sequence : list Pattern;     (* What it regenerates *)
  fidelity : FinProb;              (* Matching tolerance *)
  remaining_echoes : Fin;          (* Finite replay count *)
  echo_spur : Spuren                 (* Spuren from past regenerations *)
}.

(* Helper: Add degradation to patterns based on Spuren *)
Definition degrade_patterns_b (patterns : list Pattern) (h : Spuren) (b : Budget)
  : (list Pattern * Budget) :=
  match h with
  | fz => (patterns, b)  (* No Spuren, no degradation *)
  | _ =>
      fold_left (fun acc p =>
        match acc with
        | (ps, budget) =>
            match budget with
            | fz => (ps, fz)
            | fs b' =>
                match decay_with_budget (strength p) b' with
                | (decayed, b'') => 
                    ({| location := location p; strength := decayed |} :: ps, b'')
                end
            end
        end
      ) patterns ([], b)
  end.

(* The fundamental operation: approximate regeneration *)
Definition echo_process_b (pg : ProcessGhost) (input : Pattern) (b : Budget)
  : (option (list Pattern) * ProcessGhost * Budget * Spuren) :=
  match remaining_echoes pg with
  | fz => (None, pg, b, fs fz)  (* Ghost exhausted *)
  | fs n =>
      match fin_eq_b (location input) (location (trigger pg)) b with
      | (true, b1) =>
          (* Check if strength is similar enough *)
          match probs_similar_b (strength input) (strength (trigger pg)) 
                                (fidelity pg) b1 with
          | (true, b2) =>
              (* Regenerate with degradation proportional to accumulated Spuren *)
              match degrade_patterns_b (echo_sequence pg) (echo_spur pg) b2 with
              | (degraded_echo, b3) =>
                  (Some degraded_echo,
                   {| trigger := trigger pg;
                      echo_sequence := echo_sequence pg;
                      fidelity := decay_prob (fidelity pg);  (* Degrades *)
                      remaining_echoes := n;
                      echo_spur := add_spur (echo_spur pg) (fs (fs fz)) |},
                   b3,
                   fs (fs fz))
              end
          | (false, b2) => (None, pg, b2, fs fz)
          end
      | (false, b1) => (None, pg, b1, fs fz)
      end
  end.

(******************************************************************************)
(* UPDATE HELPER                                                              *)
(******************************************************************************)

(* Update a ghost in the list *)
Fixpoint update_ghost (ghosts : list ProcessGhost) 
                      (old new : ProcessGhost) : list ProcessGhost :=
  match ghosts with
  | [] => []
  | g :: gs =>
      (* Can't use pattern equality, so use location as ID *)
      match fin_eq_b (location (trigger g)) (location (trigger old)) 
                     initial_budget with
      | (true, _) => new :: gs
      | (false, _) => g :: update_ghost gs old new
      end
  end.

(******************************************************************************)
(* PROCESS MEMORY BANK - Finite collection of ghosts                         *)
(******************************************************************************)

Record ProcessMemoryBank := {
  ghosts : list ProcessGhost;
  bank_capacity : Fin;        (* Maximum ghosts *)
  total_spur : Spuren;          (* Bank temperature *)
  bank_budget : Budget
}.

(* Add ghost if capacity allows *)
Definition add_ghost (bank : ProcessMemoryBank) (g : ProcessGhost) 
  : ProcessMemoryBank :=
  match le_fin_b (length_fin (ghosts bank)) (bank_capacity bank) 
                 (bank_budget bank) with
  | (true, b') =>
      {| ghosts := g :: ghosts bank;
         bank_capacity := bank_capacity bank;
         total_spur := total_spur bank;
         bank_budget := b' |}
  | (false, b') => bank  (* At capacity *)
  end.

(* Learn by creating new ghost from pattern sequence *)
Definition learn_ghost_b (patterns : list Pattern) (b : Budget)
  : (option ProcessGhost * Budget) :=
  match patterns with
  | [] => (None, b)
  | trigger :: echo =>
      match le_fin_b (length_fin echo) (fs (fs (fs fz))) b with
      | (true, b1) =>  (* Max 3 echoes *)
          (Some {| trigger := trigger;
                   echo_sequence := echo;
                   fidelity := (fs (fs fz), fs (fs (fs fz)));  (* 2/3 *)
                   remaining_echoes := fs (fs (fs (fs (fs fz))));  (* 5 uses *)
                   echo_spur := fz |},
           b1)
      | (false, b1) => (None, b1)  (* Sequence too long *)
      end
  end.

(* Bank recall - search all ghosts for match *)
Definition bank_recall_b (bank : ProcessMemoryBank) (input : Pattern)
  : (list Pattern * ProcessMemoryBank) :=
  match bank_budget bank with
  | fz => ([], bank)  (* Bank frozen *)
  | _ =>
      fold_left (fun acc ghost =>
        match acc with
        | (patterns, current_bank) =>
            match echo_process_b ghost input (bank_budget current_bank) with
            | (Some echoes, ghost', b', h) =>
                (patterns ++ echoes,
                 {| ghosts := update_ghost (ghosts current_bank) ghost ghost';
                    bank_capacity := bank_capacity current_bank;
                    total_spur := add_spur (total_spur current_bank) h;
                    bank_budget := b' |})
            | (None, _, b', h) =>
                (patterns,
                 {| ghosts := ghosts current_bank;
                    bank_capacity := bank_capacity current_bank;
                    total_spur := add_spur (total_spur current_bank) h;
                    bank_budget := b' |})
            end
        end
      ) (ghosts bank) ([], bank)
  end.

(******************************************************************************)
(* FORGET MECHANISM - Hot ghosts evaporate                                   *)
(******************************************************************************)

Definition evaporate_ghosts_b (bank : ProcessMemoryBank) : ProcessMemoryBank :=
  let survivors := filter (fun g => 
    match remaining_echoes g with
    | fz => false  (* Dead ghost *)
    | _ => le_spur (echo_spur g) (total_spur bank)  (* Cool enough to survive *)
    end
  ) (ghosts bank) in
  {| ghosts := survivors;
     bank_capacity := bank_capacity bank;
     total_spur := match total_spur bank with
                   | fz => fz
                   | fs h => h  (* Bank cools *)
                   end;
     bank_budget := bank_budget bank |}.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition ProcessGhost_ext := ProcessGhost.
Definition ProcessMemoryBank_ext := ProcessMemoryBank.
Definition echo_process_b_ext := echo_process_b.
Definition bank_recall_b_ext := bank_recall_b.
Definition learn_ghost_b_ext := learn_ghost_b.
Definition evaporate_ghosts_b_ext := evaporate_ghosts_b.

End Void_Process_Memory.