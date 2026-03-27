Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.

Module Void_Finite_Randomness.

  Import Void_Probability_Minimal.
  Import Void_Arithmetic.
  
  (* Randomness is just pattern mixing with budget *)
  Record RandomState := {
    pattern : Fin;
    mix_budget : Budget;
    mix_spur : Spuren
  }.
  
  (* Draw "randomness" - just mix and extract *)
  Definition draw_b3 (state : RandomState) (b : Budget) 
    : (Bool3 * RandomState * Budget * Spuren) :=
    match b with
    | fz => (BUnknown, state, fz, fz)  (* No budget = Unknown *)
    | fs b' =>
        match mix_budget state with
        | fz => (BUnknown, state, b', fs fz)  (* State exhausted *)
        | fs mb =>
            (* Mix pattern with itself - creates variation *)
            match mult_fin (pattern state) (fs (fs (fs fz))) b' with
            | (mixed, b'') =>
                match add_fin mixed (fs (fs (fs (fs (fs fz))))) b'' with
                | (new_pattern, b''') =>
                    (* Extract bit from low-order structure *)
                    match le_fin_b new_pattern (fs (fs (fs (fs (fs fz))))) b''' with
                    | (true, b_final) =>
                        (BTrue, {| pattern := new_pattern;
                                  mix_budget := mb;
                                  mix_spur := fs (mix_spur state) |},
                         b_final, fs fz)
                    | (false, b_final) =>
                        (BFalse, {| pattern := new_pattern;
                                   mix_budget := mb;
                                   mix_spur := fs (mix_spur state) |},
                         b_final, fs fz)
                    end
                end
            end
        end
    end.
  
  Theorem exhaustion_is_unknown : forall state b,
    mix_budget state = fz ->
    exists res state' b' h,
    draw_b3 state b = (res, state', b', h) /\
    res = BUnknown.
  Proof.
    intros state b H_exhausted.
    unfold draw_b3.
    destruct b.
    - exists BUnknown, state, fz, fz.
      split; reflexivity.
    - rewrite H_exhausted.
      exists BUnknown, state, b, (fs fz).
      split; reflexivity.
  Qed.
  
  End Void_Finite_Randomness.