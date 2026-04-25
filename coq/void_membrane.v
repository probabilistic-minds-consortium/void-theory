(* void_membrane.v — Probabilistic Topology of Membranes *)
(* VOID Theory — Gustaw Wojnowski, 2026                 *)
(*                                                        *)
(* Faza 2 (2026-04-22): External znikl. Kazde spotkanie   *)
(* to zderzenie dwoch Membran. Jeden budzet na kontur     *)
(* (mem_budget), ktory placi za wszystko — rozpoznanie,   *)
(* przyjecie, operacje.                                   *)
(*                                                        *)
(* System = kontur = membrana. Nie ma sys_budget jako     *)
(* osobnej puli. mem_budget m1 to jedyny zasob ktory m1   *)
(* wnosi do spotkania. mem_budget m2 to to co m2 ma       *)
(* do zaoferowania.                                       *)
(*                                                        *)
(* Dependencies:                                          *)
(*   void_finite_minimal (Fin, Budget, Membrane)         *)
(*   void_probability_minimal                             *)
(*   void_probability_geometry (Pattern, distance)        *)
(*   void_figure_geometry (Figure, recognize)             *)

Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_probability_geometry.
Require Import void_figure_geometry.
Import Void_Probability_Minimal.
Import Void_Probability_Geometry.

(* ================================================================ *)
(* cap — pojemnosc wynika z konturu membrany                        *)
(* ================================================================ *)
(* Historycznie Cap byl globalnym Parameter'em w void_finite_minimal *)
(* z aksjomatem Cap_positive. To byla reifikacja 'dekretu swiata' — *)
(* void-theory tego nie dopuszcza. Pojemnosc jest funkcja membrany, *)
(* nie odwrotnie. cap czyta mem_capacity z geometrii konturu.       *)
(* Cap_positive jako aksjomat znika — w jego miejsce pojawia sie    *)
(* lokalny lemat cap_positive_of_nonzero_capacity.                   *)

Definition cap (m : Membrane) : Fin := mem_capacity m.

Lemma cap_positive_of_nonzero_capacity :
  forall m, mem_capacity m <> fz -> cap m <> fz.
Proof.
  intros m H. unfold cap. exact H.
Qed.

(* ================================================================ *)
(* PART 0: Bridge — Membrane as Figure                              *)
(* ================================================================ *)

(* A membrane filter IS a figure: center = mem_filter_center,
   radius = mem_filter_radius. This converts between primitives. *)

Definition membrane_as_figure (m : Membrane) : Figure :=
  mkFigure (mem_filter_center m) (mem_filter_radius m).

(* ================================================================ *)
(* PART 1: intake — zderzenie dwoch konturow                         *)
(* ================================================================ *)

(* intake: m1 obserwuje m2.
   - m1 uzywa swojego budzetu do recognize na mem_filter_center m2.
     To jest 'percepcja': m1 widzi centrum geometrii m2.
   - Jesli BTrue: transfer = min(mem_budget m2, mem_capacity m1).
     m1 zyskuje transfer (assimilate do swojego budzetu).
     m2 traci transfer (spend ze swojego budzetu).
   - Jesli BFalse: sygnal odrzucony. Nie ma transferu.
     m1 i tak zaplacil recognize_cost. m2 nie traci nic.
   - Jesli BUnknown: m1 nie stac na rozpoznanie (slepota).
     Nie ma transferu. Cisza jest darmowa.

   Wynik: (admitted, m1', m2', total_spuren).
   admitted = ile zostalo przetransferowane (fz jesli nie BTrue).

   Spuren sa sumowane z czterech zrodel: recognize, min_fin_dec,
   assimilate_b_spur, spend_aux. Zaden ruch nie jest darmowy. *)

Definition intake (m1 m2 : Membrane)
  : (Fin * Membrane * Membrane * Spuren) :=
  match recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1) with
  | (BTrue, b1, h_rec) =>
      match min_fin_dec (mem_budget m2) (mem_capacity m1) b1 with
      | (admitted, _, b1_min, h_min) =>
          match assimilate_b_spur admitted b1_min with
          | (b1_final, h_assim) =>
              match spend_aux (mem_budget m2) admitted with
              | (b2_final, h_spend) =>
                  let m1' := mkMembrane (mem_filter_center m1)
                                        (mem_filter_radius m1)
                                        (mem_capacity m1)
                                        b1_final
                                        (mem_inner m1) in
                  let m2' := mkMembrane (mem_filter_center m2)
                                        (mem_filter_radius m2)
                                        (mem_capacity m2)
                                        b2_final
                                        (mem_inner m2) in
                  (admitted, m1', m2',
                   add_spur (add_spur (add_spur h_rec h_min) h_assim) h_spend)
              end
          end
      end
  | (BFalse, b1, h_rec) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b1
                            (mem_inner m1) in
      (fz, m1', m2, h_rec)
  | (BUnknown, b1, h_rec) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b1
                            (mem_inner m1) in
      (fz, m1', m2, h_rec)
  end.

(* Helpers: extract components *)
Definition intake_admitted (r : Fin * Membrane * Membrane * Spuren) : Fin :=
  fst (fst (fst r)).

Definition intake_m1 (r : Fin * Membrane * Membrane * Spuren) : Membrane :=
  snd (fst (fst r)).

Definition intake_m2 (r : Fin * Membrane * Membrane * Spuren) : Membrane :=
  snd (fst r).

Definition intake_spuren (r : Fin * Membrane * Membrane * Spuren) : Spuren :=
  snd r.

(* ================================================================ *)
(* Abbreviations                                                     *)
(* ================================================================ *)

Local Definition f1 := fs fz.
Local Definition f2 := fs (fs fz).
Local Definition f4' := fs (fs (fs (fs fz))).
Local Definition f8' := fs (fs (fs (fs (fs (fs (fs (fs fz))))))).
Local Definition f16' := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))))))).

(* ================================================================ *)
(* Test membranes                                                    *)
(* ================================================================ *)

(* 1D membrane — zywa, budget=16, filter_center=[(1,4)], radius=2, capacity=4.
   Atomowa: mem_inner = nil. *)
Definition test_membrane_1 : Membrane :=
  mkMembrane ((f1, f4') :: nil) f2 f4' f16' nil.

(* 1D martwa — ten sam ksztalt, budget=0. Atomowa. *)
Definition test_membrane_dead : Membrane :=
  mkMembrane ((f1, f4') :: nil) f2 f4' fz nil.

(* Zrodlo dopasowane: geometria podobna do test_membrane_1, duzy budget. Atomowa. *)
Definition test_source_match : Membrane :=
  mkMembrane ((f2, f4') :: nil) f2 f4' f4' nil.
  (* center=[(2,4)] — odleglosc 1 od test_membrane_1 przy tym samym budzecie *)

(* Zrodlo niedopasowane: odlegla geometria. Atomowa. *)
Definition test_source_nomatch : Membrane :=
  mkMembrane ((f8', f4') :: nil) f2 f4' f4' nil.

(* Witnesses *)
Eval compute in intake test_membrane_1 test_source_match.
Eval compute in intake test_membrane_1 test_source_nomatch.
Eval compute in intake test_membrane_dead test_source_match.

(* ================================================================ *)
(* PART 2: Closed System Dies                                       *)
(* ================================================================ *)

(* A system step consumes budget. Abstract model. *)

Definition system_step (b : Budget) : Budget :=
  match b with
  | fz => fz
  | fs b' => b'
  end.

Fixpoint closed_run (b : Budget) (steps : Fin) : Budget :=
  match steps with
  | fz => b
  | fs steps' => closed_run (system_step b) steps'
  end.

Lemma closed_run_self : forall b,
  closed_run b b = fz.
Proof.
  induction b as [| b' IH].
  - simpl. reflexivity.
  - simpl. exact IH.
Qed.

Theorem closed_system_dies : forall b,
  closed_run b b = fz.
Proof. exact closed_run_self. Qed.

Lemma system_step_fz : system_step fz = fz.
Proof. reflexivity. Qed.

Lemma closed_run_fz : forall steps,
  closed_run fz steps = fz.
Proof.
  induction steps as [| s' IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

(* ================================================================ *)
(* PART 3: Shape Preservation                                        *)
(* ================================================================ *)

(* intake nigdy nie zmienia geometrii membran — center, radius, capacity
   sa strukturalnymi niezmiennikami. Zmienia sie tylko mem_budget. *)

Theorem intake_preserves_m1_center : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_filter_center m1' = mem_filter_center m1.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
Qed.

Theorem intake_preserves_m1_radius : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_filter_radius m1' = mem_filter_radius m1.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
Qed.

Theorem intake_preserves_m1_capacity : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_capacity m1' = mem_capacity m1.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
Qed.

Theorem intake_preserves_m2_center : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_filter_center m2' = mem_filter_center m2.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. reflexivity.
  - inversion Hintake; subst. reflexivity.
Qed.

Theorem intake_preserves_m2_radius : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_filter_radius m2' = mem_filter_radius m2.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. reflexivity.
  - inversion Hintake; subst. reflexivity.
Qed.

Theorem intake_preserves_m2_capacity : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_capacity m2' = mem_capacity m2.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. reflexivity.
  - inversion Hintake; subst. reflexivity.
Qed.

(* ================================================================ *)
(* PART 4: Zero-budget silence — boundary dissolves                  *)
(* ================================================================ *)

(* m1 o zerowym budzecie nie moze nawet sprawdzac. Cisza jest calkowita:
   zero admitted, m1 zostaje z fz, m2 nietknieta, zero Spuren. *)

Theorem intake_zero_budget_silent : forall m1 m2,
  mem_budget m1 = fz ->
  intake m1 m2 = (fz,
                  mkMembrane (mem_filter_center m1)
                             (mem_filter_radius m1)
                             (mem_capacity m1)
                             fz
                             (mem_inner m1),
                  m2,
                  fz).
Proof.
  intros m1 m2 Hb.
  unfold intake, membrane_as_figure.
  rewrite Hb.
  rewrite (recognize_zero_budget_blind (mem_filter_center m2)
    (mkFigure (mem_filter_center m1) (mem_filter_radius m1))).
  simpl. reflexivity.
Qed.

(* ================================================================ *)
(* PART 5: Trace inheritance i No-Dulcinea                           *)
(* ================================================================ *)

(* Jesli recognize zemitowal Spuren, intake musi je oddziedziczyc. *)

Theorem intake_inherits_recognize_trace :
  forall m1 m2 adm m1' m2' h res b1 h_rec,
  intake m1 m2 = (adm, m1', m2', h) ->
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (res, b1, h_rec) ->
  h_rec <> fz ->
  h <> fz.
Proof.
  intros m1 m2 adm m1' m2' h res b1 h_rec Hintake Hrec Hh_rec.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst.
    apply add_spur_neq_fz_l.
    apply add_spur_neq_fz_l.
    apply add_spur_neq_fz_l.
    exact Hh_rec.
  - inversion Hintake; subst. exact Hh_rec.
  - inversion Hintake; subst. exact Hh_rec.
Qed.

(* Pozytywny budget + niepuste centra oboch membran -> Spuren zawsze emitowane. *)

Theorem intake_no_dulcinea :
  forall m1 m2 adm m1' m2' h p1 rs1 p2 rs2 b',
  mem_budget m1 = fs b' ->
  mem_filter_center m2 = p1 :: rs1 ->
  mem_filter_center m1 = p2 :: rs2 ->
  intake m1 m2 = (adm, m1', m2', h) ->
  h <> fz.
Proof.
  intros m1 m2 adm m1' m2' h p1 rs1 p2 rs2 b' Hb Hsig Hctr Hintake.
  assert (Hfig: membrane_as_figure m1
                = mkFigure (p2 :: rs2) (mem_filter_radius m1)).
  { unfold membrane_as_figure. rewrite Hctr. reflexivity. }
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  assert (Hh_rec: h_rec <> fz).
  { rewrite Hsig in Hrec.
    rewrite Hfig in Hrec.
    rewrite Hb in Hrec.
    exact (recognize_cost_positive _ _ _ _ _ _ _ _ _ Hrec). }
  exact (intake_inherits_recognize_trace _ _ _ _ _ _ _ _ _
           Hintake Hrec Hh_rec).
Qed.

(* Dispatch: BFalse i BUnknown admituja fz, m2 nietknieta. *)

Theorem intake_reject_silent :
  forall m1 m2 adm m1' m2' h b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BFalse, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  adm = fz /\ m2' = m2 /\ h = h_rec.
Proof.
  intros m1 m2 adm m1' m2' h b1 h_rec Hrec Hintake.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  inversion Hintake; subst.
  split; [|split]; reflexivity.
Qed.

Theorem intake_unknown_silent :
  forall m1 m2 adm m1' m2' h b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BUnknown, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  adm = fz /\ m2' = m2 /\ h = h_rec.
Proof.
  intros m1 m2 adm m1' m2' h b1 h_rec Hrec Hintake.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  inversion Hintake; subst.
  split; [|split]; reflexivity.
Qed.

(* BTrue: admitted to min z (mem_budget m2) i (mem_capacity m1). *)

Theorem intake_match_admits_input :
  forall m1 m2 adm m1' m2' h b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BTrue, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  adm = mem_budget m2 \/ adm = mem_capacity m1.
Proof.
  intros m1 m2 adm m1' m2' h b1 h_rec Hrec Hintake.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  unfold min_fin_dec in Hintake.
  destruct (le_fin_b3 (mem_budget m2) (mem_capacity m1) b1)
    as [[r bx] hx] eqn:Hle.
  destruct r.
  - destruct (assimilate_b_spur (mem_budget m2) bx) as [b1f hf] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) (mem_budget m2)) as [b2f hs] eqn:Hspend.
    inversion Hintake; subst. left. reflexivity.
  - destruct (assimilate_b_spur (mem_capacity m1) bx) as [b1f hf] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) (mem_capacity m1)) as [b2f hs] eqn:Hspend.
    inversion Hintake; subst. right. reflexivity.
  - destruct (assimilate_b_spur (mem_budget m2) bx) as [b1f hf] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) (mem_budget m2)) as [b2f hs] eqn:Hspend.
    inversion Hintake; subst. left. reflexivity.
Qed.

(* Dead m1 -> admits nothing. *)

Theorem dead_m1_admits_nothing : forall m1 m2,
  mem_budget m1 = fz ->
  intake_admitted (intake m1 m2) = fz.
Proof.
  intros m1 m2 Hb.
  unfold intake_admitted.
  rewrite (intake_zero_budget_silent m1 m2 Hb).
  simpl. reflexivity.
Qed.

Theorem dead_m1_system_dies : forall m1 m2 b,
  mem_budget m1 = fz ->
  intake_admitted (intake m1 m2) = fz /\ closed_run b b = fz.
Proof.
  intros m1 m2 b Hb.
  split.
  - exact (dead_m1_admits_nothing m1 m2 Hb).
  - exact (closed_system_dies b).
Qed.

(* ================================================================ *)
(* PART 6: Thermodynamic step                                        *)
(* ================================================================ *)

(* thermo_step: jeden pelny cykl metaboliczny.
   1. intake m1 m2 — m1 placi recognize + min_fin_dec, zyskuje admitted,
      m2 traci admitted.
   2. spend op_cost z budzetu m1 — wewnetrzna operacja.
   Wynik: (m1_final, m2_final, total_spuren).

   Nie ma osobnego sys_budget. mem_budget m1 jest JEDYNYM budzetem
   systemu (= konturu). Placi za wszystko. *)

Definition thermo_step (m1 m2 : Membrane) (op_cost : Fin)
  : (Membrane * Membrane * Spuren) :=
  match intake m1 m2 with
  | (admitted, m1_after, m2_after, h_intake) =>
      match spend_aux (mem_budget m1_after) op_cost with
      | (b1_final, h_spend) =>
          let m1_final := mkMembrane (mem_filter_center m1_after)
                                     (mem_filter_radius m1_after)
                                     (mem_capacity m1_after)
                                     b1_final
                                     (mem_inner m1_after) in
          (m1_final, m2_after, add_spur h_intake h_spend)
      end
  end.

Fixpoint thermo_cycle (m1 m2 : Membrane) (op_cost : Fin) (steps : Fin)
  : (Membrane * Membrane * Spuren) :=
  match steps with
  | fz => (m1, m2, fz)
  | fs steps' =>
      match thermo_step m1 m2 op_cost with
      | (m1a, m2a, h1) =>
          match thermo_cycle m1a m2a op_cost steps' with
          | (m1b, m2b, h2) => (m1b, m2b, add_spur h1 h2)
          end
      end
  end.

Lemma thermo_cycle_zero_steps : forall m1 m2 op,
  thermo_cycle m1 m2 op fz = (m1, m2, fz).
Proof. intros. reflexivity. Qed.

(* Witnesses *)
Eval compute in thermo_step test_membrane_1 test_source_match f1.
Eval compute in thermo_cycle test_membrane_1 test_source_match f1 f2.
Eval compute in thermo_cycle test_membrane_dead test_source_match f1 f2.

(* ================================================================ *)
(* PART 7: Thermo-survival / thermo-death (Runda 2)                  *)
(* ================================================================ *)

(* Shape preservation: thermo_step nie rusza geometrii obu membran. *)

Theorem thermo_step_preserves_m1_shape :
  forall m1 m2 op_cost m1' m2' h,
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  mem_filter_center m1' = mem_filter_center m1 /\
  mem_filter_radius m1' = mem_filter_radius m1 /\
  mem_capacity m1'      = mem_capacity m1.
Proof.
  intros m1 m2 op_cost m1' m2' h Hstep.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[adm m1_int] m2_int] h_intake] eqn:Hintake.
  destruct (spend_aux (mem_budget m1_int) op_cost) as [b1f h_sp] eqn:Hsp.
  inversion Hstep; subst.
  simpl.
  split; [|split].
  - exact (intake_preserves_m1_center _ _ _ _ _ _ Hintake).
  - exact (intake_preserves_m1_radius _ _ _ _ _ _ Hintake).
  - exact (intake_preserves_m1_capacity _ _ _ _ _ _ Hintake).
Qed.

Theorem thermo_step_preserves_m2_shape :
  forall m1 m2 op_cost m1' m2' h,
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  mem_filter_center m2' = mem_filter_center m2 /\
  mem_filter_radius m2' = mem_filter_radius m2 /\
  mem_capacity m2'      = mem_capacity m2.
Proof.
  intros m1 m2 op_cost m1' m2' h Hstep.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[adm m1_int] m2_int] h_intake] eqn:Hintake.
  destruct (spend_aux (mem_budget m1_int) op_cost) as [b1f h_sp] eqn:Hsp.
  inversion Hstep; subst.
  split; [|split].
  - exact (intake_preserves_m2_center _ _ _ _ _ _ Hintake).
  - exact (intake_preserves_m2_radius _ _ _ _ _ _ Hintake).
  - exact (intake_preserves_m2_capacity _ _ _ _ _ _ Hintake).
Qed.

(* Dead m1: intake jest cichy, wiec thermo_step redukuje sie do
   czystego spend op_cost z zerowego budzetu (ktory zostaje fz). *)

Lemma spend_aux_zero_budget : forall c, spend_aux fz c = (fz, c).
Proof.
  destruct c as [| c']; simpl; reflexivity.
Qed.

Theorem thermo_step_dead_m1_only_spends :
  forall m1 m2 op_cost m1' m2' h,
  mem_budget m1 = fz ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  mem_budget m1' = fz /\ m2' = m2.
Proof.
  intros m1 m2 op_cost m1' m2' h Hb Hstep.
  unfold thermo_step in Hstep.
  rewrite (intake_zero_budget_silent m1 m2 Hb) in Hstep.
  destruct op_cost as [| op']; simpl in Hstep;
    inversion Hstep; subst; simpl; split; reflexivity.
Qed.

(* Dead m1 + zero cost = perfect stasis: no motion, no trace. *)

Corollary thermo_step_dead_stasis :
  forall m1 m2 m1' m2' h,
  mem_budget m1 = fz ->
  thermo_step m1 m2 fz = (m1', m2', h) ->
  mem_budget m1' = fz /\ m2' = m2 /\ h = fz.
Proof.
  intros m1 m2 m1' m2' h Hb Hstep.
  unfold thermo_step in Hstep.
  rewrite (intake_zero_budget_silent m1 m2 Hb) in Hstep.
  simpl in Hstep.
  inversion Hstep; subst.
  simpl.
  split; [|split]; reflexivity.
Qed.

(* Death is absorbing: once m1 is dead, it stays dead across thermo_step. *)

Theorem thermo_step_dead_m1_stays_dead :
  forall m1 m2 op_cost m1' m2' h,
  mem_budget m1 = fz ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  mem_budget m1' = fz.
Proof.
  intros m1 m2 op_cost m1' m2' h Hb Hstep.
  destruct (thermo_step_dead_m1_only_spends _ _ _ _ _ _ Hb Hstep) as [H1 _].
  exact H1.
Qed.

Theorem thermo_cycle_dead_m1_stays_dead :
  forall steps m1 m2 op_cost m1' m2' h,
  mem_budget m1 = fz ->
  thermo_cycle m1 m2 op_cost steps = (m1', m2', h) ->
  mem_budget m1' = fz.
Proof.
  induction steps as [| steps' IH];
    intros m1 m2 op_cost m1' m2' h Hb Hcycle.
  - simpl in Hcycle. inversion Hcycle; subst. exact Hb.
  - simpl in Hcycle.
    destruct (thermo_step m1 m2 op_cost) as [[m1a m2a] h1] eqn:Hstep.
    assert (Hm1a_dead : mem_budget m1a = fz)
      by exact (thermo_step_dead_m1_stays_dead _ _ _ _ _ _ Hb Hstep).
    destruct (thermo_cycle m1a m2a op_cost steps') as [[m1b m2b] h2] eqn:Hrec.
    inversion Hcycle; subst.
    exact (IH _ _ _ _ _ _ Hm1a_dead Hrec).
Qed.

(* Witnesses Runda 2 *)
Eval compute in thermo_step test_membrane_dead test_source_match fz.
Eval compute in thermo_step test_membrane_dead test_source_match f2.
Eval compute in thermo_cycle test_membrane_dead test_source_match f1 f4'.

(* ================================================================ *)
(* PART 8: Pozytywne warunki przetrwania (Runda 3)                   *)
(* ================================================================ *)

(* Teza: po intake m1 otrzymal admitted (zysk) i zaplacil h_intake
   w Spuren, a jego budzet jest teraz b1_after_intake. Spend op_cost
   z tego budzetu daje finalny stan. Trzy regime'y:
     balanced: op_cost = admitted  -> mem_budget m1' = mem_budget m1_int - admitted + admitted = mem_budget m1_int
                                      (czyli to co bylo po samym intake, przed spend)
     surplus:  admitted = op_cost + s -> mem_budget m1' > mem_budget m1_int - op_cost
     deficit:  op_cost = admitted + d -> mem_budget m1' = fst (spend_aux (mem_budget m1_int) d - admitted added back)

   Uwaga semantyczna (vs Runda 3 fazy 1): 'balanced' nie oznacza
   juz 'budzet m1 nietkniety'. Oznacza 'budzet po spend rowny
   budzetowi po intake'. Recognize_cost jest zawsze oplacany —
   percepcja nigdy nie jest darmowa. *)

Lemma spend_aux_add_cancel : forall c b,
  spend_aux (add_spur b c) c = (b, c).
Proof.
  induction c as [| c' IHc']; intro b.
  - simpl. destruct b; simpl; reflexivity.
  - simpl. rewrite IHc'. reflexivity.
Qed.

Lemma add_spur_comm_local : forall a b, add_spur a b = add_spur b a.
Proof.
  intros a b. induction b as [| b' IH].
  - simpl. rewrite add_spur_fz_l. reflexivity.
  - simpl. rewrite IH. rewrite add_spur_fs_l. reflexivity.
Qed.

(* BALANCED REGIME: kiedy op_cost = admitted, net zmiana budzetu m1
   od stanu 'po recognize+min_fin_dec, przed assimilate' wynosi zero.
   Zysk z assimilate (admitted) jest dokladnie placony przez spend.
   Recognize_cost zawsze placony — percepcja nigdy darmowa.

   Twierdzenie: istnieje b1_pre (budzet m1 przed assimilate) taki ze
   m1_int ma budzet = b1_pre + admitted (po assimilate),
   a m1' ma budzet = b1_pre (po spend admitted).
   W przypadku BFalse/BUnknown admitted=fz, wiec b1_pre = m1_int.budget. *)

Theorem thermo_step_balanced_preserves_intake_budget :
  forall m1 m2 m1' m2' h admitted m1_int m2_int h_intake,
  intake m1 m2 = (admitted, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 admitted = (m1', m2', h) ->
  exists b1_pre,
    mem_budget m1_int = add_spur b1_pre admitted /\
    mem_budget m1'    = b1_pre /\
    m2' = m2_int.
Proof.
  intros m1 m2 m1' m2' h admitted m1_int m2_int h_intake Hintake Hstep.
  unfold thermo_step in Hstep.
  rewrite Hintake in Hstep.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2f h_spend_intake] eqn:Hspend_intake.
    inversion Hintake; subst.
    simpl in Hstep.
    assert (Hb1f : b1_final = add_spur b1_min admitted).
    { exact (assimilate_budget_equals_gain_plus_start _ _ _ _ Hassim). }
    rewrite Hb1f in Hstep.
    rewrite spend_aux_add_cancel in Hstep.
    simpl in Hstep.
    inversion Hstep; subst.
    exists b1_min. simpl.
    split; [|split]; reflexivity.
  - (* BFalse: admitted=fz. spend_aux b1 fz = (b1, fz). *)
    inversion Hintake; subst.
    simpl in Hstep.
    destruct b1 as [| b0] eqn:Eb.
    + simpl in Hstep.
      inversion Hstep; subst.
      exists fz. simpl. split; [reflexivity | split; reflexivity].
    + simpl in Hstep.
      inversion Hstep; subst.
      exists (fs b0). simpl. split; [reflexivity | split; reflexivity].
  - (* BUnknown: analogicznie *)
    inversion Hintake; subst.
    simpl in Hstep.
    destruct b1 as [| b0] eqn:Eb.
    + simpl in Hstep.
      inversion Hstep; subst.
      exists fz. simpl. split; [reflexivity | split; reflexivity].
    + simpl in Hstep.
      inversion Hstep; subst.
      exists (fs b0). simpl. split; [reflexivity | split; reflexivity].
Qed.

(* SURPLUS REGIME: jesli admitted = op_cost + surplus, to budzet m1
   po spend rosnie o surplus ponad (b1_final - admitted), czyli:
   mem_budget m1' = add_spur b1_min surplus  (gdzie b1_min = budzet
   m1 po recognize + min_fin_dec, przed assimilate). *)

Theorem thermo_step_surplus_grows :
  forall m1 m2 m1' m2' h op_cost surplus m1_int m2_int h_intake,
  surplus <> fz ->
  intake m1 m2 = (add_spur op_cost surplus, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  exists b1_min,
    mem_budget m1_int = add_spur b1_min (add_spur op_cost surplus) /\
    mem_budget m1'   = add_spur b1_min surplus /\
    m2' = m2_int.
Proof.
  intros m1 m2 m1' m2' h op_cost surplus m1_int m2_int h_intake Hsurp Hintake Hstep.
  unfold thermo_step in Hstep.
  rewrite Hintake in Hstep.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2f h_spend_intake] eqn:Hspend_intake.
    inversion Hintake as [[Hadm Hm1_int Hm2_int Hh_intake]]. subst.
    simpl in Hstep.
    assert (Hb1f : b1_final = add_spur b1_min (add_spur op_cost surplus)).
    { exact (assimilate_budget_equals_gain_plus_start _ _ _ _ Hassim). }
    rewrite Hb1f in Hstep.
    (* spend_aux (add_spur b1_min (add_spur op_cost surplus)) op_cost.
       Chcemy pokazac = (add_spur b1_min surplus, op_cost). *)
    assert (Hrewrite : add_spur b1_min (add_spur op_cost surplus)
                       = add_spur (add_spur b1_min surplus) op_cost).
    { rewrite (add_spur_comm_local op_cost surplus).
      rewrite <- add_spur_assoc.
      reflexivity. }
    rewrite Hrewrite in Hstep.
    rewrite spend_aux_add_cancel in Hstep.
    simpl in Hstep.
    inversion Hstep; subst.
    exists b1_min. simpl.
    split; [|split]; reflexivity.
  - (* BFalse: intake daje admitted=fz, ale admitted=add_spur op_cost surplus.
       Z surplus <> fz dostajemy sprzecznosc. *)
    inversion Hintake as [[Hadm Hm1_int Hm2_int Hh_intake]].
    destruct surplus as [| s'].
    + exfalso. apply Hsurp. reflexivity.
    + simpl in Hadm. discriminate.
  - (* BUnknown: analogicznie *)
    inversion Hintake as [[Hadm Hm1_int Hm2_int Hh_intake]].
    destruct surplus as [| s'].
    + exfalso. apply Hsurp. reflexivity.
    + simpl in Hadm. discriminate.
Qed.

(* DEFICIT REGIME: jesli op_cost = admitted + deficit, to spend
   po intake drenuje deficit z pre-intake budzetu b1_min.
   Dla uproszczenia zwracamy zaleznosc od b1_min zamiast od oryginalnego
   mem_budget m1 (rownowazne modulo recognize_cost). *)

Theorem thermo_step_deficit_drains :
  forall m1 m2 m1' m2' h admitted deficit m1_int m2_int h_intake,
  intake m1 m2 = (admitted, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 (add_spur admitted deficit) = (m1', m2', h) ->
  exists b1_min,
    mem_budget m1_int = add_spur b1_min admitted /\
    mem_budget m1'   = fst (spend_aux b1_min deficit) /\
    m2' = m2_int.
Proof.
  intros m1 m2 m1' m2' h admitted deficit m1_int m2_int h_intake Hintake Hstep.
  unfold thermo_step in Hstep.
  rewrite Hintake in Hstep.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2f h_spend_intake] eqn:Hspend_intake.
    inversion Hintake as [[Hadm Hm1_int Hm2_int Hh_intake]]. subst.
    simpl in Hstep.
    assert (Hb1f : b1_final = add_spur b1_min admitted).
    { exact (assimilate_budget_equals_gain_plus_start _ _ _ _ Hassim). }
    rewrite Hb1f in Hstep.
    (* spend_aux (add_spur b1_min admitted) (add_spur admitted deficit)
       = (fst (spend_aux b1_min deficit), add_spur admitted (snd (spend_aux b1_min deficit))).
       To jest Hsplit z Fazy 1, tutaj ponownie dowodzimy lokalnie. *)
    assert (Hsplit : forall c d b,
            spend_aux (add_spur b c) (add_spur c d)
            = (fst (spend_aux b d), add_spur c (snd (spend_aux b d)))).
    { clear. induction c as [| c' IHc']; intros d b.
      - simpl. rewrite !add_spur_fz_l.
        destruct (spend_aux b d) as [b0 hsp0]. reflexivity.
      - simpl. rewrite (add_spur_fs_l c' d). simpl.
        rewrite (IHc' d b).
        destruct (spend_aux b d) as [b0 hsp0].
        simpl. rewrite (add_spur_fs_l c' hsp0). reflexivity. }
    rewrite Hsplit in Hstep.
    destruct (spend_aux b1_min deficit) as [b_d h_sp] eqn:Hsp_d.
    simpl in Hstep.
    inversion Hstep; subst.
    exists b1_min. simpl.
    rewrite Hsp_d. simpl.
    split; [reflexivity | split; reflexivity].
  - (* BFalse: admitted = fz. intake zwraca m1_int z budget = b1. *)
    inversion Hintake as [[Hadm Hm1_int Hm2_int Hh_intake]]. subst.
    simpl in Hstep.
    rewrite add_spur_fz_l in Hstep.
    destruct (spend_aux b1 deficit) as [b_d h_sp] eqn:Hsp_d.
    inversion Hstep; subst.
    exists b1. simpl.
    rewrite Hsp_d. simpl.
    split; [reflexivity | split; reflexivity].
  - (* BUnknown: analogicznie *)
    inversion Hintake as [[Hadm Hm1_int Hm2_int Hh_intake]]. subst.
    simpl in Hstep.
    rewrite add_spur_fz_l in Hstep.
    destruct (spend_aux b1 deficit) as [b_d h_sp] eqn:Hsp_d.
    inversion Hstep; subst.
    exists b1. simpl.
    rewrite Hsp_d. simpl.
    split; [reflexivity | split; reflexivity].
Qed.

(* Witnesses Runda 3 *)
Eval compute in thermo_step test_membrane_1 test_source_match f1.
Eval compute in thermo_step test_membrane_1 test_source_match f2.
Eval compute in thermo_step test_membrane_1 test_source_match f8'.

(* ================================================================ *)
(* PART 9: Compound Membranes — Parasitic Maintenance (Runda 4)      *)
(* ================================================================ *)

(* Od Fazy 2 Membrane jest Inductive z polem mem_inner : list Membrane. *)
(* Atomowa membrana ma mem_inner = nil. Zlozona ma niepusta liste       *)
(* wewnetrznych konturow. Ontologicznie: roznica ilosciowa, nie         *)
(* jakosciowa. Wszystkie membrany sa emergentnymi produktami percepcji; *)
(* atomowe to te, ktore nie wchlonely gruntu dla wlasnej zagnieżdżonej  *)
(* struktury.                                                           *)
(*                                                                       *)
(* Podstawa teoretyczna: Twierdzenie 8.15 (Parasitic Maintenance /      *)
(* Zero Marginal Cost) z void_no_infinity.pdf, sekcja 8.5:              *)
(*                                                                       *)
(*   Jesli testy wzorca pi2 sa podzbiorem testow wzorca pi1 (T2 ⊆ T1)   *)
(*   to M(pi1 ∪ pi2) = M(pi1).                                           *)
(*                                                                       *)
(* Znaczenie dla membran: wewnetrzna membrana nie wymaga wlasnej pracy  *)
(* utrzymujacej, jezeli jej dystynkcje sa juz implikowane przez         *)
(* dystynkcje outer'a. Jej "istnienie" jest epifenomenalne na pracy     *)
(* zewnetrza — rides na jego shape'ie.                                  *)
(*                                                                       *)
(* PIERWSZA FORMALNA KONSEKWENCJA: intake, thermo_step i thermo_cycle   *)
(* nie zmieniaja mem_inner. Wynika z tego, ze atomowosc jest niezmien-  *)
(* nicza pod dynamika — obecne prymitywy NIE produkuja spontanicznie   *)
(* wewnetrznej struktury. Emergencja compound'u wymaga OSOBNYCH         *)
(* operacji, ktore zostana wprowadzone w nastepnej rundzie.             *)
(* ================================================================ *)

(* -- Preservation of mem_inner through intake -- *)

Theorem intake_preserves_m1_inner : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. simpl. reflexivity.
Qed.

Theorem intake_preserves_m2_inner : forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  mem_inner m2' = mem_inner m2.
Proof.
  intros m1 m2 adm m1' m2' h Hintake.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1] h_rec] eqn:Hrec.
  destruct res.
  - destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1)
      as [[[adm0 flag] b1_min] h_min] eqn:Hmin.
    destruct (assimilate_b_spur adm0 b1_min) as [b1_final h_assim] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) adm0) as [b2_final h_spend] eqn:Hspend.
    inversion Hintake; subst. simpl. reflexivity.
  - inversion Hintake; subst. reflexivity.
  - inversion Hintake; subst. reflexivity.
Qed.

(* -- Preservation through thermo_step -- *)

Theorem thermo_step_preserves_m1_inner : forall m1 m2 op m1' m2' h,
  thermo_step m1 m2 op = (m1', m2', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  intros m1 m2 op m1' m2' h Hstep.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[adm m1_int] m2_int] h_intake] eqn:Hintake.
  destruct (spend_aux (mem_budget m1_int) op) as [b1f h_sp] eqn:Hsp.
  inversion Hstep; subst. simpl.
  exact (intake_preserves_m1_inner _ _ _ _ _ _ Hintake).
Qed.

Theorem thermo_step_preserves_m2_inner : forall m1 m2 op m1' m2' h,
  thermo_step m1 m2 op = (m1', m2', h) ->
  mem_inner m2' = mem_inner m2.
Proof.
  intros m1 m2 op m1' m2' h Hstep.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[adm m1_int] m2_int] h_intake] eqn:Hintake.
  destruct (spend_aux (mem_budget m1_int) op) as [b1f h_sp] eqn:Hsp.
  inversion Hstep; subst.
  exact (intake_preserves_m2_inner _ _ _ _ _ _ Hintake).
Qed.

(* -- Preservation through thermo_cycle (induction on steps) -- *)

Theorem thermo_cycle_preserves_m1_inner : forall steps m1 m2 op m1' m2' h,
  thermo_cycle m1 m2 op steps = (m1', m2', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  induction steps as [| steps' IH]; intros m1 m2 op m1' m2' h Hcycle.
  - simpl in Hcycle. inversion Hcycle; subst. reflexivity.
  - simpl in Hcycle.
    destruct (thermo_step m1 m2 op) as [[m1a m2a] h1] eqn:Hstep.
    destruct (thermo_cycle m1a m2a op steps') as [[m1b m2b] h2] eqn:Hrec.
    inversion Hcycle; subst.
    rewrite (IH _ _ _ _ _ _ Hrec).
    exact (thermo_step_preserves_m1_inner _ _ _ _ _ _ Hstep).
Qed.

Theorem thermo_cycle_preserves_m2_inner : forall steps m1 m2 op m1' m2' h,
  thermo_cycle m1 m2 op steps = (m1', m2', h) ->
  mem_inner m2' = mem_inner m2.
Proof.
  induction steps as [| steps' IH]; intros m1 m2 op m1' m2' h Hcycle.
  - simpl in Hcycle. inversion Hcycle; subst. reflexivity.
  - simpl in Hcycle.
    destruct (thermo_step m1 m2 op) as [[m1a m2a] h1] eqn:Hstep.
    destruct (thermo_cycle m1a m2a op steps') as [[m1b m2b] h2] eqn:Hrec.
    inversion Hcycle; subst.
    rewrite (IH _ _ _ _ _ _ Hrec).
    exact (thermo_step_preserves_m2_inner _ _ _ _ _ _ Hstep).
Qed.

(* -- Atomicity predicate -- *)

Definition is_atomic (m : Membrane) : Prop := mem_inner m = nil.

(* Atomowosc jest decydowalna — strukturalnie, bez budzetu *)
Definition is_atomic_bool (m : Membrane) : bool :=
  match mem_inner m with
  | nil => true
  | _   => false
  end.

Lemma is_atomic_bool_correct : forall m,
  is_atomic_bool m = true <-> is_atomic m.
Proof.
  intros m. unfold is_atomic, is_atomic_bool.
  destruct (mem_inner m) as [| x xs]; split; intro H; try reflexivity; try discriminate.
Qed.

(* -- Atomicity invariance under dynamics -- *)

(* Jesli m1 i m2 byly atomowe, to po dowolnym intake obie pozostaja    *)
(* atomowe. Zaden nowy inner kontur sie nie pojawia spontanicznie.    *)

Theorem intake_preserves_atomicity : forall m1 m2 adm m1' m2' h,
  is_atomic m1 -> is_atomic m2 ->
  intake m1 m2 = (adm, m1', m2', h) ->
  is_atomic m1' /\ is_atomic m2'.
Proof.
  intros m1 m2 adm m1' m2' h Ha1 Ha2 Hintake.
  unfold is_atomic in *.
  split.
  - rewrite (intake_preserves_m1_inner _ _ _ _ _ _ Hintake). exact Ha1.
  - rewrite (intake_preserves_m2_inner _ _ _ _ _ _ Hintake). exact Ha2.
Qed.

Theorem thermo_step_preserves_atomicity : forall m1 m2 op m1' m2' h,
  is_atomic m1 -> is_atomic m2 ->
  thermo_step m1 m2 op = (m1', m2', h) ->
  is_atomic m1' /\ is_atomic m2'.
Proof.
  intros m1 m2 op m1' m2' h Ha1 Ha2 Hstep.
  unfold is_atomic in *.
  split.
  - rewrite (thermo_step_preserves_m1_inner _ _ _ _ _ _ Hstep). exact Ha1.
  - rewrite (thermo_step_preserves_m2_inner _ _ _ _ _ _ Hstep). exact Ha2.
Qed.

Theorem thermo_cycle_preserves_atomicity : forall steps m1 m2 op m1' m2' h,
  is_atomic m1 -> is_atomic m2 ->
  thermo_cycle m1 m2 op steps = (m1', m2', h) ->
  is_atomic m1' /\ is_atomic m2'.
Proof.
  intros steps m1 m2 op m1' m2' h Ha1 Ha2 Hcycle.
  unfold is_atomic in *.
  split.
  - rewrite (thermo_cycle_preserves_m1_inner _ _ _ _ _ _ _ Hcycle). exact Ha1.
  - rewrite (thermo_cycle_preserves_m2_inner _ _ _ _ _ _ _ Hcycle). exact Ha2.
Qed.

(* -- Tesy: test_membrane_1 itd. sa atomowe -- *)
Lemma test_membrane_1_atomic : is_atomic test_membrane_1.
Proof. unfold is_atomic, test_membrane_1. simpl. reflexivity. Qed.

Lemma test_source_match_atomic : is_atomic test_source_match.
Proof. unfold is_atomic, test_source_match. simpl. reflexivity. Qed.

(* -- Bottom-up death: if outer and all inner are dead, the compound  *)
(*    is fully dead -- *)

(* all_inner_budget_zero: wszystkie wewnetrzne membrany maja budget=fz. *)
(* Uwaga: na tym etapie nie rekuzujemy w glab wewnetrznych inner'ow — *)
(* to byloby pelne drzewne recursive definition, ktorego Coq nie       *)
(* akceptuje bez custom induction principle. Tutaj pierwsza warstwa     *)
(* jest wystarczajaca dla base case: flat compound.                     *)

Definition all_inner_budget_zero (m : Membrane) : Prop :=
  Forall (fun m' => mem_budget m' = fz) (mem_inner m).

(* Pelna smierc membrany plaskiej (pierwszy poziom zagnieżdżenia): *)
(* outer budget = fz AND wszystkie bezposrednie inner maja budget = fz. *)
(* To jest base case dla bottom-up death. Pelna rekursja w glab jest   *)
(* przedmiotem przyszlej rundy. *)

Definition flat_dead (m : Membrane) : Prop :=
  mem_budget m = fz /\ all_inner_budget_zero m.

(* Atomowa martwa membrana ma trywialnie all_inner_budget_zero (pusta *)
(* lista spelnia Forall vacuously). *)

Lemma atomic_all_inner_budget_zero : forall m,
  is_atomic m -> all_inner_budget_zero m.
Proof.
  intros m Ha. unfold all_inner_budget_zero, is_atomic in *.
  rewrite Ha. apply Forall_nil.
Qed.

Theorem atomic_zero_budget_is_flat_dead : forall m,
  is_atomic m -> mem_budget m = fz -> flat_dead m.
Proof.
  intros m Ha Hb. unfold flat_dead. split.
  - exact Hb.
  - exact (atomic_all_inner_budget_zero m Ha).
Qed.

(* Smierc flat_dead jest stabilna pod intake (m1 martwa => m1' martwa,  *)
(* m2' = m2 jesli m1 miala zerowy budzet — patrz intake_zero_budget_    *)
(* silent). Kluczowe: mem_inner m1' = mem_inner m1, wiec Forall przechodzi. *)

Theorem intake_flat_dead_m1_stays_dead : forall m1 m2 adm m1' m2' h,
  flat_dead m1 ->
  intake m1 m2 = (adm, m1', m2', h) ->
  flat_dead m1'.
Proof.
  intros m1 m2 adm m1' m2' h [Hb Hinner] Hintake.
  unfold flat_dead. split.
  - (* mem_budget m1' = fz: skorzystaj z intake_zero_budget_silent *)
    rewrite (intake_zero_budget_silent m1 m2 Hb) in Hintake.
    inversion Hintake; subst. simpl. reflexivity.
  - (* all_inner_budget_zero m1': preservation of mem_inner *)
    unfold all_inner_budget_zero.
    rewrite (intake_preserves_m1_inner _ _ _ _ _ _ Hintake).
    exact Hinner.
Qed.

Theorem thermo_step_flat_dead_m1_stays_dead : forall m1 m2 op m1' m2' h,
  flat_dead m1 ->
  thermo_step m1 m2 op = (m1', m2', h) ->
  flat_dead m1'.
Proof.
  intros m1 m2 op m1' m2' h [Hb Hinner] Hstep.
  unfold flat_dead. split.
  - (* mem_budget m1' = fz: intake daje dead m1, potem spend fz daje fz *)
    exact (thermo_step_dead_m1_stays_dead _ _ _ _ _ _ Hb Hstep).
  - (* all_inner_budget_zero m1': preservation of mem_inner *)
    unfold all_inner_budget_zero.
    rewrite (thermo_step_preserves_m1_inner _ _ _ _ _ _ Hstep).
    exact Hinner.
Qed.

(* ================================================================ *)
(* PART 10: EMBED — Parasitic Maintenance constructive (Runda 5)     *)
(*                                                                    *)
(* VOID-pure design: zadnych "cosmic pool" predykatow. Test inkluzji *)
(* filtrow placi m1 BEZPOSREDNIO z mem_budget, emituje Spuren        *)
(* proporcjonalne do pracy wykonanej, i zwraca Bool3 — jesli budzet  *)
(* pada w polowie sprawdzania, wynik to BUnknown (nie false, nie     *)
(* true). Short-circuit na BFalse przy pierwszej niezgodzie.          *)
(*                                                                    *)
(* Maintenance cost pozostaje zero — Runda 4 preservation theorems   *)
(* pokazuja ze intake/thermo_step/thermo_cycle nie ruszaja mem_inner.*)
(* Thm 8.15 w calosci = embed (ta runda) + Runda 4 preservation.     *)
(* ================================================================ *)

(* --- fin_pair_eq_spur: test rownosci pary z budzetem --- *)

Definition fin_pair_eq_spur (p q : Fin * Fin) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  let (a, b_p) := p in
  let (c, d) := q in
  match fin_eq_b3 a c b with
  | (BTrue, b1, h1) =>
      match fin_eq_b3 b_p d b1 with
      | (r, b2, h2) => (r, b2, add_spur h1 h2)
      end
  | (BFalse, b1, h1) => (BFalse, b1, h1)
  | (BUnknown, b1, h1) => (BUnknown, b1, h1)
  end.

(* --- pair_in_list_spur: czy para jest w liscie, z budzetem --- *)

Fixpoint pair_in_list_spur (p : Fin * Fin) (xs : list (Fin * Fin)) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match xs with
  | nil => (BFalse, b, fz)
  | x :: xs' =>
      match fin_pair_eq_spur p x b with
      | (BTrue, b1, h1) => (BTrue, b1, h1)
      | (BFalse, b1, h1) =>
          match pair_in_list_spur p xs' b1 with
          | (r, b2, h2) => (r, b2, add_spur h1 h2)
          end
      | (BUnknown, b1, h1) => (BUnknown, b1, h1)
      end
  end.

(* --- filter_subset_spur: czy xs ⊆ ys jako lista par --- *)

Fixpoint filter_subset_spur (xs ys : list (Fin * Fin)) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match xs with
  | nil => (BTrue, b, fz)  (* vacuous truth, zero koszt *)
  | x :: xs' =>
      match pair_in_list_spur x ys b with
      | (BTrue, b1, h1) =>
          match filter_subset_spur xs' ys b1 with
          | (r, b2, h2) => (r, b2, add_spur h1 h2)
          end
      | (BFalse, b1, h1) => (BFalse, b1, h1)  (* short-circuit *)
      | (BUnknown, b1, h1) => (BUnknown, b1, h1)
      end
  end.

(* --- filter_implies_spur: pelny test inkluzji T2 ⊆ T1 --- *)
(*                                                                    *)
(*   1. filter_subset_spur (center m2) (center m1) b                  *)
(*      — czy wszystkie pary z m2 sa w m1.                            *)
(*   2. le_fin_b3 (radius m2) (radius m1)                             *)
(*      — czy tolerance m2 nie szersza.                               *)
(*                                                                    *)
(* Short-circuit: porazka lub BUnknown w (1) konczy bez sprawdzania   *)
(* (2). No free lunch: kazdy tick budzetu m1 konsumowany pokrywa     *)
(* tick Spuren emitowanych. Spur conservation gwarantowane.           *)

Definition filter_implies_spur (m1 m2 : Membrane) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match filter_subset_spur (mem_filter_center m2) (mem_filter_center m1) b with
  | (BTrue, b1, h1) =>
      match le_fin_b3 (mem_filter_radius m2) (mem_filter_radius m1) b1 with
      | (r, b2, h2) => (r, b2, add_spur h1 h2)
      end
  | (BFalse, b1, h1) => (BFalse, b1, h1)
  | (BUnknown, b1, h1) => (BUnknown, b1, h1)
  end.

(* --- embed: trojwartosciowy, placi z mem_budget m1 proporcjonalnie --- *)
(*                                                                       *)
(* BTrue: m2 prependowany do mem_inner, budget/Spuren z testu.          *)
(* BFalse: inner niezmieniony, budget/Spuren z testu (do pierwszej      *)
(*         niezgody — short-circuit).                                   *)
(* BUnknown: budzet wyczerpany przed konkluzja; inner niezmieniony,    *)
(*         budget = fz (padl), Spuren = co wyemitowal test.             *)

Definition embed (m1 m2 : Membrane) : Membrane * Spuren :=
  match filter_implies_spur m1 m2 (mem_budget m1) with
  | (BTrue, b', h) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b'
                            (m2 :: mem_inner m1) in
      (m1', h)
  | (BFalse, b', h) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b'
                            (mem_inner m1) in
      (m1', h)
  | (BUnknown, b', h) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b'
                            (mem_inner m1) in
      (m1', h)
  end.

(* ---- Preservation of outer shape (unconditional) ---- *)

Theorem embed_preserves_outer_center : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  mem_filter_center m1' = mem_filter_center m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold embed in Hembed.
  destruct (filter_implies_spur m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hfilt.
  destruct r; inversion Hembed; subst; simpl; reflexivity.
Qed.

Theorem embed_preserves_outer_radius : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  mem_filter_radius m1' = mem_filter_radius m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold embed in Hembed.
  destruct (filter_implies_spur m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hfilt.
  destruct r; inversion Hembed; subst; simpl; reflexivity.
Qed.

Theorem embed_preserves_outer_capacity : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  mem_capacity m1' = mem_capacity m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold embed in Hembed.
  destruct (filter_implies_spur m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hfilt.
  destruct r; inversion Hembed; subst; simpl; reflexivity.
Qed.

(* ---- Branch-specific semantics ---- *)

(* BTrue: inner grows by prepending m2 *)
Theorem embed_btrue_grows_inner : forall m1 m2 m1' h b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  embed m1 m2 = (m1', h) ->
  mem_inner m1' = m2 :: mem_inner m1.
Proof.
  intros m1 m2 m1' h b' Hfilt Hembed.
  unfold embed in Hembed.
  rewrite Hfilt in Hembed.
  inversion Hembed; subst. simpl. reflexivity.
Qed.

(* BFalse: inner unchanged *)
Theorem embed_bfalse_preserves_inner : forall m1 m2 m1' h b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BFalse, b', h) ->
  embed m1 m2 = (m1', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  intros m1 m2 m1' h b' Hfilt Hembed.
  unfold embed in Hembed.
  rewrite Hfilt in Hembed.
  inversion Hembed; subst. simpl. reflexivity.
Qed.

(* BUnknown: inner unchanged *)
Theorem embed_bunknown_preserves_inner : forall m1 m2 m1' h b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BUnknown, b', h) ->
  embed m1 m2 = (m1', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  intros m1 m2 m1' h b' Hfilt Hembed.
  unfold embed in Hembed.
  rewrite Hfilt in Hembed.
  inversion Hembed; subst. simpl. reflexivity.
Qed.

(* ---- Budget/Spuren semantics ---- *)

(* Budget po embed = budget po tescie, niezaleznie od branch'u. *)
Theorem embed_budget_from_test : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  exists r b', filter_implies_spur m1 m2 (mem_budget m1) = (r, b', h)
               /\ mem_budget m1' = b'.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold embed in Hembed.
  destruct (filter_implies_spur m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hfilt.
  (* destruct zamienia filter_implies_spur w Hembed i goal na (r, b', h');
     Hfilt kapsuluje oryginalna rownosc. Po destruct r + inversion + subst
     pierwszy subgoal redukuje do identity — reflexivity starcza. *)
  destruct r; inversion Hembed; subst.
  - exists BTrue, b'. split; reflexivity.
  - exists BFalse, b'. split; reflexivity.
  - exists BUnknown, b'. split; reflexivity.
Qed.

(* ---- Compound production: BTrue embed -> non-atomic outer ---- *)

Theorem embed_btrue_produces_compound : forall m1 m2 m1' h b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  embed m1 m2 = (m1', h) ->
  is_atomic_bool m1' = false.
Proof.
  intros m1 m2 m1' h b' Hfilt Hembed.
  unfold is_atomic_bool.
  rewrite (embed_btrue_grows_inner _ _ _ _ _ Hfilt Hembed).
  reflexivity.
Qed.

(* ---- m2 in mem_inner m1' po BTrue embed ---- *)

Theorem embed_btrue_m2_in_inner : forall m1 m2 m1' h b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  embed m1 m2 = (m1', h) ->
  In m2 (mem_inner m1').
Proof.
  intros m1 m2 m1' h b' Hfilt Hembed.
  rewrite (embed_btrue_grows_inner _ _ _ _ _ Hfilt Hembed).
  simpl. left. reflexivity.
Qed.

(* ================================================================ *)
(* CAPSTONE: Parasitic Maintenance formalized.                       *)
(*                                                                    *)
(* Po BTrue embed'ie inner pozostaje w liscie outer'a POD            *)
(* ZADNYM thermo_step/thermo_cycle — zaden nie ruszy mem_inner.      *)
(* Inner "istnieje" tylko dzieki outer'owej pracy recognize'u, ktora *)
(* juz implikuje jego dystynkcje. Inner sam nic nie robi, nie placi,  *)
(* nie emituje. To jest formalna inkarnacja Thm 8.15.                *)
(* ================================================================ *)

Theorem embed_zero_marginal_maintenance_step :
  forall m1 m2 m1' h m_other op m1'' m_other' h_step b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  embed m1 m2 = (m1', h) ->
  thermo_step m1' m_other op = (m1'', m_other', h_step) ->
  mem_inner m1'' = m2 :: mem_inner m1.
Proof.
  intros m1 m2 m1' h m_other op m1'' m_other' h_step b'
         Hfilt Hembed Hstep.
  rewrite (thermo_step_preserves_m1_inner _ _ _ _ _ _ Hstep).
  exact (embed_btrue_grows_inner _ _ _ _ _ Hfilt Hembed).
Qed.

Theorem embed_zero_marginal_maintenance_cycle :
  forall m1 m2 m1' h m_other op steps m1'' m_other' h_cycle b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  embed m1 m2 = (m1', h) ->
  thermo_cycle m1' m_other op steps = (m1'', m_other', h_cycle) ->
  mem_inner m1'' = m2 :: mem_inner m1.
Proof.
  intros m1 m2 m1' h m_other op steps m1'' m_other' h_cycle b'
         Hfilt Hembed Hcycle.
  rewrite (thermo_cycle_preserves_m1_inner _ _ _ _ _ _ _ Hcycle).
  exact (embed_btrue_grows_inner _ _ _ _ _ Hfilt Hembed).
Qed.

(* ---- Witnesses: konkretne embed computations ---- *)

(* Kandydat z filterem identycznym do test_membrane_1 — T2 ⊆ T1. *)
Definition test_inner_fits : Membrane :=
  mkMembrane ((f1, f4') :: nil) f1 f4' f2 nil.

(* Kandydat z innym filterem — nie implied. *)
Definition test_inner_mismatch : Membrane :=
  mkMembrane ((f2, f1) :: nil) f1 f4' f2 nil.

(* Dead outer test. *)
Definition test_membrane_1_dead : Membrane :=
  mkMembrane ((f1, f4') :: nil) f2 f4' fz nil.

(* BTrue embed: filter matches, m2 embedded. *)
Eval compute in embed test_membrane_1 test_inner_fits.

(* BFalse embed (albo BUnknown jesli budzet padnie) — filter mismatch. *)
Eval compute in embed test_membrane_1 test_inner_mismatch.

(* Dead outer: filter_implies_spur startuje z budzet=fz, co dekonstruuje *)
(* do BUnknown natychmiast. Inner niezmienione, Spuren=fz. *)
Eval compute in embed test_membrane_1_dead test_inner_fits.

(* ================================================================ *)
(* PODSUMOWANIE TWIERDZEN                                            *)
(*                                                                   *)
(*   Structural:                                                     *)
(*     cap_positive_of_nonzero_capacity                              *)
(*     closed_system_dies                                            *)
(*                                                                   *)
(*   Shape preservation (PART 3):                                    *)
(*     intake_preserves_m1_center/radius/capacity                    *)
(*     intake_preserves_m2_center/radius/capacity                    *)
(*                                                                   *)
(*   Dispatch + trace (PART 4-5):                                    *)
(*     intake_zero_budget_silent                                     *)
(*     intake_inherits_recognize_trace                               *)
(*     intake_no_dulcinea                                            *)
(*     intake_reject_silent / intake_unknown_silent                  *)
(*     intake_match_admits_input                                     *)
(*     dead_m1_admits_nothing / dead_m1_system_dies                  *)
(*                                                                   *)
(*   Thermo-survival (PART 7, Runda 2):                              *)
(*     thermo_step_preserves_m1_shape / preserves_m2_shape           *)
(*     thermo_step_dead_m1_only_spends                               *)
(*     thermo_step_dead_stasis                                       *)
(*     thermo_step_dead_m1_stays_dead                                *)
(*     thermo_cycle_dead_m1_stays_dead                               *)
(*                                                                   *)
(*   Pozytywna termodynamika (PART 8, Runda 3):                      *)
(*     thermo_step_balanced_preserves_intake_budget                  *)
(*     thermo_step_surplus_grows                                     *)
(*     thermo_step_deficit_drains                                    *)
(*                                                                   *)
(* Zero Admitted. Zero nowych Axiomow. Zero nat. Zero Dulcinea.      *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 11: CONSERVATION of Rundy 5 (Runda 6)                        *)
(*                                                                    *)
(* Cztery helpery Rundy 5 (fin_pair_eq_spur, pair_in_list_spur,      *)
(* filter_subset_spur, filter_implies_spur) i embed dostaja formalne *)
(* lemmaty konserwacji: dla kazdego `(r, b', h)` zwroconego przez    *)
(* operacje platna, `add_spur h b' = b` (budzet wejsciowy). Zadne     *)
(* Spuren nie powstaja bez ubytku budzetu proporcjonalnego.          *)
(*                                                                    *)
(* Baza: spur_conservation_eq3, spur_conservation_le3 z              *)
(* void_finite_minimal.v (fin_eq_b3 i le_fin_b3).                    *)
(*                                                                    *)
(* Capstone: embed_no_free_lunch — jesli embed zwrocil ten sam       *)
(* budzet (bez ubytku), to nie wyemitowal zadnych Spuren. Zaden      *)
(* free lunch w compound growth.                                     *)
(* ================================================================ *)

(* ---- Helpery algebry Spuren niedowiedzione w finite_minimal ---- *)

(* add_spur nie ma self-loop: dla h != fz, add_spur h b != b. *)
Lemma add_spur_no_selfloop : forall a b, add_spur (fs a) b <> b.
Proof.
  intros a b; induction b as [| b' IH]; simpl.
  - discriminate.
  - intro H. apply IH. injection H as Heq. exact Heq.
Qed.

(* Wnioskowanie: add_spur h b = b => h = fz. *)
Lemma add_spur_cancel_right : forall h b, add_spur h b = b -> h = fz.
Proof.
  intros h b Hadd.
  destruct h as [| h'].
  - reflexivity.
  - exfalso. apply (add_spur_no_selfloop h' b). exact Hadd.
Qed.

(* ---- Conservation dla helperow Rundy 5 ---- *)

Lemma fin_pair_eq_spur_conservation : forall p q b r b' h,
  fin_pair_eq_spur p q b = (r, b', h) -> add_spur h b' = b.
Proof.
  intros [a b_p] [c d] b r b' h Heq.
  unfold fin_pair_eq_spur in Heq.
  cbn in Heq.
  destruct (fin_eq_b3 a c b) as [[r1 b1] h1] eqn:Hec.
  destruct r1.
  - (* BTrue: recurses on second component *)
    destruct (fin_eq_b3 b_p d b1) as [[r2 b2] h2] eqn:Hed.
    inversion Heq; subst.
    rewrite add_spur_assoc.
    rewrite (spur_conservation_eq3 _ _ _ _ _ _ Hed).
    exact (spur_conservation_eq3 _ _ _ _ _ _ Hec).
  - (* BFalse: short-circuit *)
    inversion Heq; subst.
    exact (spur_conservation_eq3 _ _ _ _ _ _ Hec).
  - (* BUnknown: budget exhausted *)
    inversion Heq; subst.
    exact (spur_conservation_eq3 _ _ _ _ _ _ Hec).
Qed.

Lemma pair_in_list_spur_conservation : forall p xs b r b' h,
  pair_in_list_spur p xs b = (r, b', h) -> add_spur h b' = b.
Proof.
  intros p. induction xs as [| x xs' IH]; intros b r b' h Heq.
  - (* nil: returns (BFalse, b, fz) *)
    simpl in Heq. inversion Heq; subst.
    apply add_spur_fz_l.
  - (* x :: xs' *)
    simpl in Heq.
    destruct (fin_pair_eq_spur p x b) as [[r1 b1] h1] eqn:Hpair.
    destruct r1.
    + (* BTrue: short-circuit found *)
      inversion Heq; subst.
      exact (fin_pair_eq_spur_conservation _ _ _ _ _ _ Hpair).
    + (* BFalse: recurse on xs' *)
      destruct (pair_in_list_spur p xs' b1) as [[r2 b2] h2] eqn:Hrec.
      inversion Heq; subst.
      rewrite add_spur_assoc.
      rewrite (IH _ _ _ _ Hrec).
      exact (fin_pair_eq_spur_conservation _ _ _ _ _ _ Hpair).
    + (* BUnknown *)
      inversion Heq; subst.
      exact (fin_pair_eq_spur_conservation _ _ _ _ _ _ Hpair).
Qed.

Lemma filter_subset_spur_conservation : forall xs ys b r b' h,
  filter_subset_spur xs ys b = (r, b', h) -> add_spur h b' = b.
Proof.
  induction xs as [| x xs' IH]; intros ys b r b' h Heq.
  - (* nil: returns (BTrue, b, fz) *)
    simpl in Heq. inversion Heq; subst.
    apply add_spur_fz_l.
  - (* x :: xs' *)
    simpl in Heq.
    destruct (pair_in_list_spur x ys b) as [[r1 b1] h1] eqn:Hin.
    destruct r1.
    + (* BTrue: continue with xs' *)
      destruct (filter_subset_spur xs' ys b1) as [[r2 b2] h2] eqn:Hrec.
      inversion Heq; subst.
      rewrite add_spur_assoc.
      rewrite (IH _ _ _ _ _ Hrec).
      exact (pair_in_list_spur_conservation _ _ _ _ _ _ Hin).
    + (* BFalse: short-circuit *)
      inversion Heq; subst.
      exact (pair_in_list_spur_conservation _ _ _ _ _ _ Hin).
    + (* BUnknown *)
      inversion Heq; subst.
      exact (pair_in_list_spur_conservation _ _ _ _ _ _ Hin).
Qed.

Lemma filter_implies_spur_conservation : forall m1 m2 b r b' h,
  filter_implies_spur m1 m2 b = (r, b', h) -> add_spur h b' = b.
Proof.
  intros m1 m2 b r b' h Heq.
  unfold filter_implies_spur in Heq.
  destruct (filter_subset_spur (mem_filter_center m2) (mem_filter_center m1) b)
    as [[r1 b1] h1] eqn:Hsub.
  destruct r1.
  - (* BTrue: continue with radius check *)
    destruct (le_fin_b3 (mem_filter_radius m2) (mem_filter_radius m1) b1)
      as [[r2 b2] h2] eqn:Hle.
    inversion Heq; subst.
    rewrite add_spur_assoc.
    rewrite (spur_conservation_le3 _ _ _ _ _ _ Hle).
    exact (filter_subset_spur_conservation _ _ _ _ _ _ Hsub).
  - (* BFalse: short-circuit before radius *)
    inversion Heq; subst.
    exact (filter_subset_spur_conservation _ _ _ _ _ _ Hsub).
  - (* BUnknown *)
    inversion Heq; subst.
    exact (filter_subset_spur_conservation _ _ _ _ _ _ Hsub).
Qed.

(* ---- Embed conservation ---- *)

Theorem embed_conservation : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  add_spur h (mem_budget m1') = mem_budget m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold embed in Hembed.
  destruct (filter_implies_spur m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hfilt.
  destruct r; inversion Hembed; subst; simpl;
    exact (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt).
Qed.

(* ---- Capstone: No Free Lunch for Embed ---- *)

(* Jesli embed zwrocil niezmiennionym budzet, to nie wyemitowal Spuren.
   W druga strone: jesli nie wyemitowal Spuren, to budzet nietkniety.
   Rownowaznosc — zero pracy iff zero kosztu. *)

Theorem embed_no_free_lunch : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  (mem_budget m1' = mem_budget m1 <-> h = fz).
Proof.
  intros m1 m2 m1' h Hembed.
  split.
  - intros Hbudget.
    pose proof (embed_conservation _ _ _ _ Hembed) as Hcons.
    rewrite Hbudget in Hcons.
    exact (add_spur_cancel_right _ _ Hcons).
  - intros Hh; subst h.
    pose proof (embed_conservation _ _ _ _ Hembed) as Hcons.
    rewrite add_spur_fz_l in Hcons.
    exact Hcons.
Qed.

(* ---- Capstone: No Dulcinea w compound growth ---- *)

(* Kontrapozycja: jesli jakakolwiek praca wykonana (h <> fz), to
   budzet sie zmniejszyl. Zaden region, w ktorym embed placil 0
   i zyskal compound, nie istnieje. *)

Theorem embed_no_dulcinea : forall m1 m2 m1' h,
  embed m1 m2 = (m1', h) ->
  h <> fz ->
  mem_budget m1' <> mem_budget m1.
Proof.
  intros m1 m2 m1' h Hembed Hh Hbudget.
  apply Hh.
  apply (proj1 (embed_no_free_lunch _ _ _ _ Hembed)).
  exact Hbudget.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE KONSERWACJI                                          *)
(*                                                                   *)
(*   Baza (void_finite_minimal.v, istniejace):                       *)
(*     spur_conservation_eq3 (fin_eq_b3)                             *)
(*     spur_conservation_le3 (le_fin_b3)                             *)
(*                                                                   *)
(*   Spuren algebra (PART 11, nowe):                                 *)
(*     add_spur_no_selfloop                                          *)
(*     add_spur_cancel_right                                         *)
(*                                                                   *)
(*   Conservation dla Rundy 5 (PART 11, nowe):                       *)
(*     fin_pair_eq_spur_conservation                                 *)
(*     pair_in_list_spur_conservation                                *)
(*     filter_subset_spur_conservation                               *)
(*     filter_implies_spur_conservation                              *)
(*     embed_conservation                                            *)
(*                                                                   *)
(*   Capstones:                                                      *)
(*     embed_no_free_lunch (iff)                                     *)
(*     embed_no_dulcinea (contrapozycja)                             *)
(*                                                                   *)
(* Kazda obserwacja w Rundzie 5 jest teraz formalnie "platna" —      *)
(* brak pracy = brak kosztu, kazda tick kosztu = tick Spuren.        *)
(* Parasitic Maintenance ma solidna fiskalna podstawe.               *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 12: BASE CONSERVATION — spend_aux, recognize (Runda 7)        *)
(*                                                                    *)
(* Runda 5/6 pokryly embed i jego helpery. Pozostaje audytowac       *)
(* bazowe operacje importowane z fundamentu: spend_aux, recognize.   *)
(*                                                                    *)
(* Kluczowa obserwacja: spend_aux NIE satysfakcjonuje standardowej   *)
(* konserwacji `add_spur h b' = b`. W trybie niedoboru budzetu       *)
(* (c > b), spend_aux zwraca (fz, c) — Spuren = pelny zamowiony koszt*)
(* niezaleznie od tego, ile pracy realnie wykonano. To jest feature, *)
(* nie bug: system ksieguje DLUG epistemologiczny jako Spuren.       *)
(*                                                                    *)
(* Prawdziwy niezmiennik: h = c zawsze. Spuren rownaja sie kosztowi  *)
(* zamowionemu, nie kosztowi zaplaconemu.                             *)
(* ================================================================ *)

(* ---- spend_aux: Spuren zawsze rownaja sie zamowionemu kosztowi ---- *)

Lemma spend_aux_spuren_equals_cost : forall b c b' h,
  spend_aux b c = (b', h) -> h = c.
Proof.
  intros b c; revert b.
  induction c as [| c' IH]; intros b b' h Heq.
  - (* c = fz: spend_aux b fz = (b, fz). Destruct b zeby simpl zredukowal. *)
    destruct b as [| b0]; simpl in Heq;
      inversion Heq; subst; reflexivity.
  - (* c = fs c' *)
    destruct b as [| b0].
    + (* b = fz: spend_aux fz (fs c') = (fz, fs c') *)
      simpl in Heq. inversion Heq; subst. reflexivity.
    + (* b = fs b0: recurse *)
      simpl in Heq.
      destruct (spend_aux b0 c') as [b2 h2] eqn:Hrec.
      inversion Heq; subst.
      f_equal. exact (IH _ _ _ Hrec).
Qed.

(* ---- No Free Lunch dla spend: kazdy niezerowy koszt emituje Spuren ---- *)

Lemma no_free_lunch_spend : forall b c b' h,
  spend_aux b (fs c) = (b', h) -> h <> fz.
Proof.
  intros b c b' h Heq.
  rewrite (spend_aux_spuren_equals_cost _ _ _ _ Heq).
  discriminate.
Qed.

(* ---- Strukturalna relacja `c <=_s b` (finistyczna, czysto rekursywna) ---- *)

(* Dla spend_aux w trybie dostatku konserwacja zachodzi, ale wymaga  *)
(* gwarancji ze c <= b. Definiujemy to strukturalnie, bez budzetu:  *)

Fixpoint le_struct (n m : Fin) : bool :=
  match n, m with
  | fz, _ => true
  | fs _, fz => false
  | fs n', fs m' => le_struct n' m'
  end.

(* ---- Spend conservation w trybie dostatku ---- *)

Lemma spend_aux_conservation_sufficient : forall b c b' h,
  le_struct c b = true ->
  spend_aux b c = (b', h) ->
  add_spur h b' = b.
Proof.
  intros b c; revert b.
  induction c as [| c' IH]; intros b b' h Hle Heq.
  - (* c = fz: destruct b zeby simpl zadzialal dla spend_aux *)
    destruct b as [| b0]; simpl in Heq;
      inversion Heq; subst; apply add_spur_fz_l.
  - (* c = fs c' *)
    destruct b as [| b0].
    + (* b = fz: niemozliwe bo le_struct (fs c') fz = false *)
      simpl in Hle. discriminate.
    + (* b = fs b0: rekursuj *)
      simpl in Hle.  (* Hle : le_struct c' b0 = true *)
      simpl in Heq.
      destruct (spend_aux b0 c') as [b2 h2] eqn:Hrec.
      inversion Heq; subst.
      rewrite add_spur_fs_l.
      f_equal.
      exact (IH _ _ _ Hle Hrec).
Qed.

(* ---- Capstone: No Dulcinea dla spend ---- *)

(* Jesli spend emitowal h niezerowe, to koszt byl niezerowy. *)
(* Kontrapozycja: h = fz implikuje c = fz.                   *)

Lemma spend_aux_no_dulcinea : forall b c b' h,
  spend_aux b c = (b', h) -> h = fz -> c = fz.
Proof.
  intros b c b' h Heq Hh.
  pose proof (spend_aux_spuren_equals_cost _ _ _ _ Heq) as Hhc.
  rewrite Hh in Hhc. symmetry. exact Hhc.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE BASE CONSERVATION                                     *)
(*                                                                    *)
(*   le_struct  (pomocnicza)                                          *)
(*                                                                    *)
(*   spend_aux (PART 12):                                             *)
(*     spend_aux_spuren_equals_cost         (h = c zawsze)            *)
(*     no_free_lunch_spend                  (c <> fz -> h <> fz)      *)
(*     spend_aux_conservation_sufficient    (le_struct c b -> cons)   *)
(*     spend_aux_no_dulcinea                (h = fz -> c = fz)        *)
(*                                                                    *)
(* Obserwacja metodologiczna: spend_aux w trybie niedoboru budzetu   *)
(* emituje Spuren > budzet dostepny. To jest UCZCIWE: system notuje  *)
(* dlug epistemologiczny. Conservation standardowa zachodzi TYLKO    *)
(* w trybie dostatku (le_struct c b).                                *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 13: CONSERVATION DLA RECOGNIZE (Runda 7 cd.)                 *)
(*                                                                    *)
(* figure_geometry definiuje pattern_distance / figure_distance /    *)
(* recognize ale NIE dostarcza twierdzen konserwacji. To uzupelnienie*)
(* audytu Rundy 7: kazda operacja propagujaca budget w membranie     *)
(* musi miec parowany conservation lemma.                             *)
(*                                                                    *)
(* Kompozycja:                                                        *)
(*   pattern_distance = distance + distance + add_fin_b_spur          *)
(*   figure_distance  = pattern_distance + rekursja + add_fin_b_spur  *)
(*   recognize        = figure_distance + le_fin_b3                   *)
(* ================================================================ *)

(* ---- pattern_distance_conservation ---- *)

Lemma pattern_distance_conservation : forall p1 p2 b d b' h,
  pattern_distance p1 p2 b = (d, b', h) -> add_spur h b' = b.
Proof.
  intros p1 p2 b d b' h Heq.
  unfold pattern_distance in Heq.
  destruct (distance (pattern_value p1) (pattern_value p2) b)
    as [[dv b1] h1] eqn:Hdv.
  destruct (distance (pattern_budget p1) (pattern_budget p2) b1)
    as [[db b2] h2] eqn:Hdb.
  destruct (add_fin_b_spur dv db b2) as [[sum b3] h3] eqn:Hadd.
  inversion Heq; subst.
  rewrite add_spur_assoc.
  rewrite add_spur_assoc.
  rewrite (spur_conservation_add _ _ _ _ _ _ Hadd).
  rewrite (distance_conservation _ _ _ _ _ _ Hdb).
  exact (distance_conservation _ _ _ _ _ _ Hdv).
Qed.

(* ---- figure_distance_conservation (rekursywne) ---- *)

Lemma figure_distance_conservation : forall c1 c2 b d b' h,
  figure_distance c1 c2 b = (d, b', h) -> add_spur h b' = b.
Proof.
  intros c1.
  induction c1 as [| p1 rs1 IH]; intros c2 b d b' h Heq.
  - (* c1 = [] : figure_distance [] _ b = (fz, b, fz) *)
    simpl in Heq. inversion Heq; subst. apply add_spur_fz_l.
  - (* c1 = p1 :: rs1 *)
    destruct c2 as [| p2 rs2].
    + (* c2 = [] : figure_distance _ [] b = (fz, b, fz) *)
      simpl in Heq. inversion Heq; subst. apply add_spur_fz_l.
    + (* c2 = p2 :: rs2 : rekursja *)
      simpl in Heq.
      destruct (pattern_distance p1 p2 b) as [[dp b1] h1] eqn:Hpd.
      destruct (figure_distance rs1 rs2 b1) as [[drest b2] h2] eqn:Hfd.
      destruct (add_fin_b_spur dp drest b2) as [[sum b3] h3] eqn:Hadd.
      inversion Heq; subst.
      rewrite add_spur_assoc.
      rewrite add_spur_assoc.
      rewrite (spur_conservation_add _ _ _ _ _ _ Hadd).
      rewrite (IH _ _ _ _ _ Hfd).
      exact (pattern_distance_conservation _ _ _ _ _ _ Hpd).
Qed.

(* ---- recognize_conservation ---- *)

Lemma recognize_conservation : forall signal fig b res b' h,
  recognize signal fig b = (res, b', h) -> add_spur h b' = b.
Proof.
  intros signal fig b res b' h Heq.
  unfold recognize in Heq.
  destruct (figure_distance signal (fig_center fig) b)
    as [[dist b1] h1] eqn:Hfd.
  destruct (le_fin_b3 dist (fig_radius fig) b1) as [[r b2] h2] eqn:Hle.
  inversion Heq; subst.
  rewrite add_spur_assoc.
  rewrite (spur_conservation_le3 _ _ _ _ _ _ Hle).
  exact (figure_distance_conservation _ _ _ _ _ _ Hfd).
Qed.

(* ---- No Free Lunch dla recognize ---- *)

(* Jesli recognize zwrocilo Spuren = fz, to albo budzet wejsciowy    *)
(* byl fz, albo fig_center i signal byly puste. W kazdym wypadku    *)
(* b' = b — membrana nie zmienila stanu budzetu.                     *)

Lemma recognize_no_free_change : forall signal fig b res b' h,
  recognize signal fig b = (res, b', h) ->
  h = fz -> b' = b.
Proof.
  intros signal fig b res b' h Heq Hh.
  pose proof (recognize_conservation _ _ _ _ _ _ Heq) as Hcons.
  rewrite Hh in Hcons.
  rewrite add_spur_fz_l in Hcons.
  exact Hcons.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 13                                               *)
(*                                                                    *)
(*   pattern_distance_conservation   add_spur h b' = b                *)
(*   figure_distance_conservation    add_spur h b' = b                *)
(*   recognize_conservation          add_spur h b' = b                *)
(*   recognize_no_free_change        h = fz -> b' = b                 *)
(*                                                                    *)
(* Po PART 13 recognize — glowna funkcja dyskryminacji membrany —    *)
(* ma formalna konserwacje Spuren. Klasyfikacja nigdy nie jest darma:*)
(* h zapisuje dokladny koszt budzetowy procesu rozpoznawania.        *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 14: INTAKE CONSERVATION — REJECTED BRANCHES (Runda 7 cd.)    *)
(*                                                                    *)
(* intake ma 3 galezie wg recognize:                                  *)
(*   BTrue    -> admission (4 sub-operacje, transfer admitted)       *)
(*   BFalse   -> rejection (tylko recognize)                          *)
(*   BUnknown -> rejection epistemiczna (tylko recognize)             *)
(*                                                                    *)
(* Tutaj formalizujemy BFalse i BUnknown — sa bezposrednia            *)
(* konsekwencja recognize_conservation, bo m2 nie zmienia sie a       *)
(* jedyna praca to sama klasyfikacja.                                 *)
(*                                                                    *)
(* Galaz BTrue wymaga osobnego traktowania (PART 15) bo transfer      *)
(* admitted powoduje ze h_assim + h_spend = 2*admitted — Spuren        *)
(* swiadcza o obu stronach ruchu masy, ktora sumarycznie sie znosi.  *)
(* ================================================================ *)

(* ---- BFalse: struktura wyniku intake ---- *)

Lemma intake_BFalse_structure : forall m1 m2 b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BFalse, b1, h_rec) ->
  intake m1 m2 = (fz,
                  mkMembrane (mem_filter_center m1)
                             (mem_filter_radius m1)
                             (mem_capacity m1)
                             b1
                             (mem_inner m1),
                  m2,
                  h_rec).
Proof.
  intros m1 m2 b1 h_rec Hrec.
  unfold intake.
  rewrite Hrec.
  reflexivity.
Qed.

(* ---- BUnknown: struktura wyniku intake ---- *)

Lemma intake_BUnknown_structure : forall m1 m2 b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BUnknown, b1, h_rec) ->
  intake m1 m2 = (fz,
                  mkMembrane (mem_filter_center m1)
                             (mem_filter_radius m1)
                             (mem_capacity m1)
                             b1
                             (mem_inner m1),
                  m2,
                  h_rec).
Proof.
  intros m1 m2 b1 h_rec Hrec.
  unfold intake.
  rewrite Hrec.
  reflexivity.
Qed.

(* ---- Konserwacja na galeziach odrzucenia ---- *)

(* Gdy recognize odrzuca, mem_budget m1' = b1 (wynik recognize)       *)
(* i h = h_rec. Konserwacja intake sprowadza sie do recognize_cons.   *)

Lemma intake_BFalse_conservation : forall m1 m2 b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BFalse, b1, h_rec) ->
  add_spur h_rec b1 = mem_budget m1.
Proof.
  intros m1 m2 b1 h_rec Hrec.
  exact (recognize_conservation _ _ _ _ _ _ Hrec).
Qed.

Lemma intake_BUnknown_conservation : forall m1 m2 b1 h_rec,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BUnknown, b1, h_rec) ->
  add_spur h_rec b1 = mem_budget m1.
Proof.
  intros m1 m2 b1 h_rec Hrec.
  exact (recognize_conservation _ _ _ _ _ _ Hrec).
Qed.

(* ---- m2 niezmieniona na galeziach odrzucenia ---- *)

Lemma intake_BFalse_m2_unchanged : forall m1 m2 b1 h_rec adm m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BFalse, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  m2' = m2.
Proof.
  intros m1 m2 b1 h_rec adm m1' m2' h Hrec Hintake.
  rewrite (intake_BFalse_structure _ _ _ _ Hrec) in Hintake.
  inversion Hintake; subst. reflexivity.
Qed.

Lemma intake_BUnknown_m2_unchanged : forall m1 m2 b1 h_rec adm m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BUnknown, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  m2' = m2.
Proof.
  intros m1 m2 b1 h_rec adm m1' m2' h Hrec Hintake.
  rewrite (intake_BUnknown_structure _ _ _ _ Hrec) in Hintake.
  inversion Hintake; subst. reflexivity.
Qed.

(* ---- admitted = fz na galeziach odrzucenia ---- *)

Lemma intake_BFalse_admitted_zero : forall m1 m2 b1 h_rec adm m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BFalse, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  adm = fz.
Proof.
  intros m1 m2 b1 h_rec adm m1' m2' h Hrec Hintake.
  rewrite (intake_BFalse_structure _ _ _ _ Hrec) in Hintake.
  inversion Hintake; subst. reflexivity.
Qed.

Lemma intake_BUnknown_admitted_zero : forall m1 m2 b1 h_rec adm m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BUnknown, b1, h_rec) ->
  intake m1 m2 = (adm, m1', m2', h) ->
  adm = fz.
Proof.
  intros m1 m2 b1 h_rec adm m1' m2' h Hrec Hintake.
  rewrite (intake_BUnknown_structure _ _ _ _ Hrec) in Hintake.
  inversion Hintake; subst. reflexivity.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 14                                               *)
(*                                                                    *)
(*   intake_BFalse_structure         exposes reject shape             *)
(*   intake_BUnknown_structure       exposes reject shape             *)
(*   intake_BFalse_conservation      add_spur h_rec b1 = budget m1    *)
(*   intake_BUnknown_conservation    add_spur h_rec b1 = budget m1    *)
(*   intake_BFalse_m2_unchanged      m2' = m2                         *)
(*   intake_BUnknown_m2_unchanged    m2' = m2                         *)
(*   intake_BFalse_admitted_zero     adm = fz                         *)
(*   intake_BUnknown_admitted_zero   adm = fz                         *)
(*                                                                    *)
(* Odrzucenie jest formalnie tanie: koszt = koszt rozpoznania, m2    *)
(* nietknieta. Membrana placi za proces klasyfikacji, nie za brak    *)
(* przyjecia.                                                         *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 15: INTAKE BTrue — HELPERS I NO-FREE-LUNCH (Runda 7 cd.)     *)
(*                                                                    *)
(* Galaz BTrue ma cztery podoperacje: recognize, min_fin_dec,         *)
(* assimilate_b_spur, spend_aux. Tu formalizujemy:                    *)
(*   (a) konserwacje min_fin_dec (pomocnicza)                         *)
(*   (b) tozsamosci sredniego poziomu: h_assim = adm, h_spend = adm   *)
(*   (c) no-free-lunch dla intake w trybie BTrue                      *)
(*                                                                    *)
(* Master theorem dla calego bilansu BTrue (suma budzetow m1 + m2)   *)
(* zostaje na PART 16 — wymaga przemiennosci add_spur i guard         *)
(* le_struct admitted (mem_budget m2), ktore trzeba oddzielnie        *)
(* wydobyc z min_fin_dec.                                             *)
(* ================================================================ *)

(* ---- min_fin_dec: konserwacja Spuren ---- *)

Lemma min_fin_dec_conservation : forall n m b r cmp b' h,
  min_fin_dec n m b = (r, cmp, b', h) -> add_spur h b' = b.
Proof.
  intros n m b r cmp b' h Heq.
  unfold min_fin_dec in Heq.
  destruct (le_fin_b3 n m b) as [[r' b''] h''] eqn:Hle.
  destruct r'; inversion Heq; subst;
    exact (spur_conservation_le3 _ _ _ _ _ _ Hle).
Qed.

(* ---- Tozsamosci "per-operation" na galezi BTrue ---- *)

(* Te lematy sa niezalezne od intake — mowia o posczegolnych sub-ops. *)
(* Ich kompozycja daje rachunek BTrue bez walki z Coq iota-redukcja. *)

Lemma assim_h_equals_gain :
  forall gain b b' h,
  assimilate_b_spur gain b = (b', h) ->
  h = gain.
Proof.
  intros. exact (assimilate_spuren_equals_gain _ _ _ _ H).
Qed.

Lemma assim_budget_is_growth :
  forall gain b b' h,
  assimilate_b_spur gain b = (b', h) ->
  b' = add_spur b gain.
Proof.
  intros gain b b' h Hassim.
  pose proof (assimilate_budget_growth _ _ _ _ Hassim) as Hgrow.
  pose proof (assimilate_spuren_equals_gain _ _ _ _ Hassim) as Hh.
  rewrite Hh in Hgrow. exact Hgrow.
Qed.

Lemma spend_h_equals_cost :
  forall b c b' h,
  spend_aux b c = (b', h) ->
  h = c.
Proof.
  intros. exact (spend_aux_spuren_equals_cost _ _ _ _ H).
Qed.

(* Pomocnicza wersja add_spur z fs po prawej: wydobywa fs na zewnatrz.  *)
(* Mamy add_spur_fs_l : add_spur (fs a) b = fs (add_spur a b). Tutaj    *)
(* potrzebujemy drugiej strony: add_spur a (fs b) = fs (add_spur a b). *)
Lemma add_spur_fs_r : forall a b, add_spur a (fs b) = fs (add_spur a b).
Proof.
  intros a b.
  rewrite (add_spur_comm_local a (fs b)).
  rewrite add_spur_fs_l.
  rewrite (add_spur_comm_local b a).
  reflexivity.
Qed.

(* ---- No Free Lunch dla intake BTrue ---- *)

(* Jesli admitted > 0 w galezi BTrue, to Spuren calkowite > 0.        *)
(* Transfer nie zachodzi bezslownie: h zawiera co najmniej slad       *)
(* asymilacji (i jeszcze drugi z wydatku — h = add_spur ... h_spend). *)

Lemma intake_BTrue_no_free_lunch :
  forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  adm <> fz ->
  h <> fz.
Proof.
  intros m1 m2 adm m1' m2' h Hintake Hadm.
  unfold intake in Hintake.
  destruct (recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1))
    as [[res b1'] h_rec'] eqn:Hrec2.
  destruct res.
  - (* BTrue branch *)
    destruct (min_fin_dec (mem_budget m2) (mem_capacity m1) b1')
      as [[[a cmp] bm] hm] eqn:Hmin.
    destruct (assimilate_b_spur a bm) as [bf ha] eqn:Hassim.
    destruct (spend_aux (mem_budget m2) a) as [bf2 hs] eqn:Hspend.
    inversion Hintake; subst.
    pose proof (spend_aux_spuren_equals_cost _ _ _ _ Hspend) as Hhs.
    subst hs.
    destruct adm as [| adm'].
    + exfalso. apply Hadm. reflexivity.
    + rewrite add_spur_fs_r. discriminate.
  - (* BFalse branch: adm = fz, sprzecznosc z Hadm *)
    inversion Hintake; subst. exfalso. apply Hadm. reflexivity.
  - (* BUnknown branch: adm = fz, sprzecznosc z Hadm *)
    inversion Hintake; subst. exfalso. apply Hadm. reflexivity.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 15                                               *)
(*                                                                    *)
(*   min_fin_dec_conservation      add_spur h b' = b                  *)
(*   add_spur_fs_r                 pomocniczy succ-right              *)
(*   assim_h_equals_gain           h_assim = gain                     *)
(*   assim_budget_is_growth        b' = add_spur b gain               *)
(*   spend_h_equals_cost           h = cost                           *)
(*   intake_BTrue_no_free_lunch    adm <> fz -> h <> fz (master)      *)
(*                                                                    *)
(* PART 15 buduje scaffolding dla BTrue bez walki z Coq iota.        *)
(* Per-operation tozsamosci + master no-free-lunch capstone dla      *)
(* calego intake. Kazdy rzeczywisty transfer admitted pozostawia     *)
(* niezerowy slad w calkowitym Spuren intake.                         *)
(* Total conservation (m1+m2 fiscal) pozostaje na PART 17.            *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 16: THERMO_STEP NO-FREE-LUNCH (Runda 7 cd.)                  *)
(*                                                                    *)
(* thermo_step m1 m2 op_cost = intake + spend_aux na m1_after.        *)
(* Spuren zlozone: h = add_spur h_intake h_spend.                     *)
(*                                                                    *)
(* Dwa capstone'y:                                                    *)
(*   (1) op_cost <> fz -> h <> fz (bo h_spend = op_cost)              *)
(*   (2) adm     <> fz -> h <> fz (przez intake_BTrue_no_free_lunch)  *)
(*                                                                    *)
(* Kazda forma realnej pracy w membranowym kroku termodynamicznym    *)
(* pozostawia slad.                                                   *)
(* ================================================================ *)

(* ---- Capstone 1: niezerowy koszt operacji -> niezerowe Spuren ---- *)

Lemma thermo_step_no_free_lunch_op :
  forall m1 m2 op_cost m1' m2' h,
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  op_cost <> fz ->
  h <> fz.
Proof.
  intros m1 m2 op_cost m1' m2' h Hstep Hop.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[adm m1_int] m2_int] h_intake] eqn:Hintake.
  destruct (spend_aux (mem_budget m1_int) op_cost) as [b1f hs] eqn:Hsp.
  inversion Hstep; subst.
  pose proof (spend_aux_spuren_equals_cost _ _ _ _ Hsp) as Hhs.
  subst hs.
  (* h = add_spur h_intake op_cost *)
  destruct op_cost as [| oc'].
  - exfalso. apply Hop. reflexivity.
  - rewrite add_spur_fs_r. discriminate.
Qed.

(* ---- Capstone 2: niezerowe admitted w intake -> niezerowe Spuren - *)

Lemma thermo_step_no_free_lunch_admitted :
  forall m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake,
  intake m1 m2 = (adm, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  adm <> fz ->
  h <> fz.
Proof.
  intros m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake
         Hintake Hstep Hadm.
  pose proof (intake_BTrue_no_free_lunch _ _ _ _ _ _ Hintake Hadm) as Hhi.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[a mi1] mi2] hi] eqn:Hi.
  inversion Hintake; subst.
  clear Hi.
  destruct (spend_aux (mem_budget m1_int) op_cost) as [b1f hs] eqn:Hsp.
  inversion Hstep; subst.
  destruct h_intake as [| hi'].
  - exfalso. apply Hhi. reflexivity.
  - rewrite add_spur_fs_l. discriminate.
Qed.

(* ---- m2 w thermo_step pochodzi wylacznie z intake ---- *)

(* Spend dziala tylko na m1_int, nie dotyka m2. Dlatego m2' z        *)
(* thermo_step = m2_int z intake.                                     *)

Lemma thermo_step_m2_is_intake_m2 :
  forall m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake,
  intake m1 m2 = (adm, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  m2' = m2_int.
Proof.
  intros m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake
         Hintake Hstep.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[a mi1] mi2] hi] eqn:Hi.
  inversion Hintake; subst.
  clear Hi.
  destruct (spend_aux (mem_budget m1_int) op_cost) as [b1f hs] eqn:Hsp.
  inversion Hstep; subst. reflexivity.
Qed.

(* ---- Struktura Spuren: h = add_spur h_intake h_spend ---- *)

Lemma thermo_step_spuren_decomposition :
  forall m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake,
  intake m1 m2 = (adm, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  h = add_spur h_intake op_cost.
Proof.
  intros m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake
         Hintake Hstep.
  unfold thermo_step in Hstep.
  destruct (intake m1 m2) as [[[a mi1] mi2] hi] eqn:Hi.
  inversion Hintake; subst.
  clear Hi.
  destruct (spend_aux (mem_budget m1_int) op_cost) as [b1f hs] eqn:Hsp.
  pose proof (spend_aux_spuren_equals_cost _ _ _ _ Hsp) as Hhs.
  subst hs.
  inversion Hstep; subst.
  reflexivity.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 16                                               *)
(*                                                                    *)
(*   thermo_step_no_free_lunch_op         op_cost <> fz -> h <> fz    *)
(*   thermo_step_no_free_lunch_admitted   adm <> fz -> h <> fz        *)
(*   thermo_step_m2_is_intake_m2          m2' = m2_int                *)
(*   thermo_step_spuren_decomposition     h = h_intake + op_cost      *)
(*                                                                    *)
(* Kazda forma pracy w kroku termodynamicznym — koszt operacji,      *)
(* transfer admitted, lub rozpoznanie — zostawia niezerowy slad      *)
(* w Spuren. Membrana nigdy nie krada z rzeczywistosci.              *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 17: INTAKE BTrue — BILANS FISKALNY (Runda 8 cd.)             *)
(*                                                                    *)
(* Na galezi BTrue intake dokonuje trzech realnych zmian:             *)
(*   - recognize   : m1 budget -> b1           (Spuren h_rec)        *)
(*   - min_fin_dec : b1 -> bm, wyznacza admitted (Spuren h_min)      *)
(*   - assimilate  : bm -> m1' budget = add_spur bm admitted         *)
(*                   (rosnie — dualne prawo, Spuren h_assim=admitted)*)
(*   - spend_aux   : m2 budget -> m2' budget                         *)
(*                   (pod guardem le_struct, Spuren h_spend=admitted)*)
(*                                                                    *)
(* Tutaj formalizujemy rachunek bilansowy bez niepotrzebnych         *)
(* zalozen. Dwie strony transferu sa udowodnione niezaleznie; full   *)
(* master sklada je wszystkie razem.                                  *)
(* ================================================================ *)

(* ---- Dekompozycja Spuren na galezi BTrue ---- *)

(* Gdy wiemy, ze recognize dal BTrue z (b1, h_rec) i min_fin_dec     *)
(* dal (admitted, _, bm, h_min), to Spuren intake rozklada sie na    *)
(* sume czterech skladnikow w scislej kolejnosci.                    *)

Lemma intake_BTrue_spuren_sum :
  forall m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BTrue, b1, h_rec) ->
  min_fin_dec (mem_budget m2) (mem_capacity m1) b1
    = (admitted, cmp, bm, h_min) ->
  intake m1 m2 = (admitted, m1', m2', h) ->
  h = add_spur (add_spur (add_spur h_rec h_min) admitted) admitted.
Proof.
  intros m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h
         Hrec Hmin Hintake.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  rewrite Hmin in Hintake.
  destruct (assimilate_b_spur admitted bm) as [bf ha] eqn:Hassim.
  destruct (spend_aux (mem_budget m2) admitted) as [bf2 hs] eqn:Hsp.
  inversion Hintake; subst.
  pose proof (assimilate_spuren_equals_gain _ _ _ _ Hassim) as Hha.
  pose proof (spend_aux_spuren_equals_cost _ _ _ _ Hsp) as Hhs.
  subst ha hs.
  reflexivity.
Qed.

(* ---- Strona m1: asymilacja jako czysty wzrost (dualne prawo) ---- *)

(* m1' budget = add_spur bm admitted. Zaden guard nie jest potrzebny  *)
(* — assimilate_b_spur to rekursja po gain, zawsze kompozycyjnie      *)
(* uczciwa. Jedyny warunek to ze recognize i min_fin_dec juz          *)
(* "zaplacily" swoje h_rec i h_min z budzetu klasyfikatora.           *)

Lemma intake_BTrue_m1_fiscal :
  forall m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BTrue, b1, h_rec) ->
  min_fin_dec (mem_budget m2) (mem_capacity m1) b1
    = (admitted, cmp, bm, h_min) ->
  intake m1 m2 = (admitted, m1', m2', h) ->
  mem_budget m1' = add_spur bm admitted.
Proof.
  intros m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h
         Hrec Hmin Hintake.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  rewrite Hmin in Hintake.
  destruct (assimilate_b_spur admitted bm) as [bf ha] eqn:Hassim.
  destruct (spend_aux (mem_budget m2) admitted) as [bf2 hs] eqn:Hsp.
  inversion Hintake; subst.
  simpl.
  pose proof (assim_budget_is_growth _ _ _ _ Hassim) as Hgrow.
  exact Hgrow.
Qed.

(* ---- Strona m2: wydatek z guardem dostatku ---- *)

(* Pod warunkiem `le_struct admitted (mem_budget m2) = true`          *)
(* (dostatek na transfer), m2' budget spelnia klasyczne prawo         *)
(* zachowania: add_spur admitted m2' = m2 budget. Bez tego guardu     *)
(* spend_aux wchodzi w tryb niedoboru i rownanie nie zachodzi        *)
(* — wtedy Spuren przekracza budzet (dlug epistemologiczny, PART 12).*)

Lemma intake_BTrue_m2_fiscal :
  forall m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BTrue, b1, h_rec) ->
  min_fin_dec (mem_budget m2) (mem_capacity m1) b1
    = (admitted, cmp, bm, h_min) ->
  intake m1 m2 = (admitted, m1', m2', h) ->
  le_struct admitted (mem_budget m2) = true ->
  add_spur admitted (mem_budget m2') = mem_budget m2.
Proof.
  intros m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h
         Hrec Hmin Hintake Hle.
  unfold intake in Hintake.
  rewrite Hrec in Hintake.
  rewrite Hmin in Hintake.
  destruct (assimilate_b_spur admitted bm) as [bf ha] eqn:Hassim.
  destruct (spend_aux (mem_budget m2) admitted) as [bf2 hs] eqn:Hsp.
  inversion Hintake; subst.
  simpl.
  pose proof (spend_aux_conservation_sufficient _ _ _ _ Hle Hsp) as Hcons.
  pose proof (spend_aux_spuren_equals_cost _ _ _ _ Hsp) as Hhs.
  rewrite Hhs in Hcons.
  exact Hcons.
Qed.

(* ---- Master: pelny bilans fiskalny BTrue ---- *)

(* Kompozycja trzech poprzednich: pod guardem dostatku, kazdy aspekt *)
(* transferu zostaje zaksiegowany explicit.                          *)

Lemma intake_BTrue_fiscal_master :
  forall m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h,
  recognize (mem_filter_center m2) (membrane_as_figure m1) (mem_budget m1)
    = (BTrue, b1, h_rec) ->
  min_fin_dec (mem_budget m2) (mem_capacity m1) b1
    = (admitted, cmp, bm, h_min) ->
  le_struct admitted (mem_budget m2) = true ->
  intake m1 m2 = (admitted, m1', m2', h) ->
     mem_budget m1' = add_spur bm admitted
  /\ add_spur admitted (mem_budget m2') = mem_budget m2
  /\ h = add_spur (add_spur (add_spur h_rec h_min) admitted) admitted.
Proof.
  intros m1 m2 b1 h_rec admitted cmp bm h_min m1' m2' h
         Hrec Hmin Hle Hintake.
  split; [| split].
  - exact (intake_BTrue_m1_fiscal _ _ _ _ _ _ _ _ _ _ _
             Hrec Hmin Hintake).
  - exact (intake_BTrue_m2_fiscal _ _ _ _ _ _ _ _ _ _ _
             Hrec Hmin Hintake Hle).
  - exact (intake_BTrue_spuren_sum _ _ _ _ _ _ _ _ _ _ _
             Hrec Hmin Hintake).
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 17                                               *)
(*                                                                    *)
(*   intake_BTrue_spuren_sum     h = ((h_rec + h_min) + adm) + adm    *)
(*   intake_BTrue_m1_fiscal      m1' = add_spur bm admitted           *)
(*   intake_BTrue_m2_fiscal      add_spur adm m2' = m2  (pod guardem) *)
(*   intake_BTrue_fiscal_master  pelny trojskladnikowy bilans         *)
(*                                                                    *)
(* Po PART 17 galaz BTrue intake ma pelny audyt fiskalny. Dwa strony *)
(* transferu sa udowodnione jako niezalezne fakty (wzrost m1 bez     *)
(* guarda + spadek m2 pod guardem dostatku), master sklada je razem. *)
(*                                                                    *)
(* Obserwacja kluczowa: 2*admitted w Spuren to nie blad. To formalny*)
(* zapis, ze transfer ma DWIE strony — asymilacja u odbiorcy i       *)
(* wydatek u dawcy. Oba realne, oba widoczne w Spuren, oba konieczne *)
(* w bilansie. System nie przemilcza ze transfer byl dwustronny.     *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 18: THERMO_CYCLE NO-FREE-LUNCH (Runda 8 cd.)                 *)
(*                                                                    *)
(* thermo_cycle skleja thermo_step rekurencyjnie po `steps`. Spuren  *)
(* cyklu to add_spur h_step h_rest, dlatego jesli jakikolwiek krok   *)
(* emituje niezerowe Spuren, cala cykliczna suma tez jest niezerowa.*)
(*                                                                    *)
(* Dowod przez indukcje po steps + helper add_spur_nonzero_l.        *)
(*                                                                    *)
(* Po PART 18 cala warstwa termodynamiczna (spend, intake,           *)
(* thermo_step, thermo_cycle) ma pelny audyt no-free-lunch.          *)
(* ================================================================ *)

(* ---- Helper: add_spur zachowuje niezerowosc lewego operandu ---- *)

Lemma add_spur_nonzero_l : forall a b, a <> fz -> add_spur a b <> fz.
Proof.
  intros a b Ha.
  destruct a as [| a'].
  - exfalso. apply Ha. reflexivity.
  - rewrite add_spur_fs_l. discriminate.
Qed.

(* Symetryczny wariant — add_spur nonzero po prawej ---- *)

Lemma add_spur_nonzero_r : forall a b, b <> fz -> add_spur a b <> fz.
Proof.
  intros a b Hb.
  destruct b as [| b'].
  - exfalso. apply Hb. reflexivity.
  - rewrite add_spur_fs_r. discriminate.
Qed.

(* ---- No Free Lunch dla thermo_cycle (op_cost) ---- *)

(* Jesli op_cost niezerowy i wykonamy >= 1 krok, to Spuren cyklu     *)
(* jest niezerowe. Dowod: indukcja po steps. W kroku succ wydobywamy *)
(* thermo_step_no_free_lunch_op aby pokazac, ze pierwszy h_step jest *)
(* niezerowy, po czym add_spur_nonzero_l domyka.                     *)

Lemma thermo_cycle_no_free_lunch_op :
  forall steps m1 m2 op m1' m2' h,
  thermo_cycle m1 m2 op steps = (m1', m2', h) ->
  op <> fz ->
  steps <> fz ->
  h <> fz.
Proof.
  intros steps. induction steps as [| steps' IH];
    intros m1 m2 op m1' m2' h Hcyc Hop Hsteps.
  - (* steps = fz: sprzecznosc z Hsteps *)
    exfalso. apply Hsteps. reflexivity.
  - (* steps = fs steps' *)
    simpl in Hcyc.
    destruct (thermo_step m1 m2 op) as [[m1a m2a] h1] eqn:Hstep.
    destruct (thermo_cycle m1a m2a op steps') as [[m1b m2b] h2] eqn:Hrec.
    inversion Hcyc; subst.
    pose proof (thermo_step_no_free_lunch_op _ _ _ _ _ _ Hstep Hop) as Hh1.
    apply add_spur_nonzero_l. exact Hh1.
Qed.

(* ---- Dekompozycja Spuren na jeden krok + reszta cyklu ---- *)

(* Eksponuje strukture thermo_cycle w kroku succ: h = h_step + h_rest.*)
(* Wariant hypothesis-style: caller dostarcza Hstep i Hrec,            *)
(* co pozwala ominac iota-redukcje scrutinee w `destruct eqn:`.        *)

Lemma thermo_cycle_succ_spuren :
  forall steps' m1 m2 op m1' m2' h m1a m2a h1 m1b m2b h2,
  thermo_step m1 m2 op = (m1a, m2a, h1) ->
  thermo_cycle m1a m2a op steps' = (m1b, m2b, h2) ->
  thermo_cycle m1 m2 op (fs steps') = (m1', m2', h) ->
  m1' = m1b /\ m2' = m2b /\ h = add_spur h1 h2.
Proof.
  intros steps' m1 m2 op m1' m2' h m1a m2a h1 m1b m2b h2
         Hstep Hrec Hcyc.
  simpl in Hcyc.
  rewrite Hstep in Hcyc.
  rewrite Hrec in Hcyc.
  inversion Hcyc; subst.
  split; [reflexivity | split; reflexivity].
Qed.

(* ---- Indukcyjne prawo: niezerowy krok gdziekolwiek -> niezerowy h *)

(* Mocniejsze twierdzenie: jesli pierwszy krok dal niezerowe Spuren, *)
(* to cala suma cyklu tez jest niezerowa. Nie wymaga op_cost <> fz   *)
(* explicit; wystarcza obserwacja ze ktorys krok zostawil slad.      *)

Lemma thermo_cycle_first_step_nonzero :
  forall steps' m1 m2 op m1' m2' h m1a m2a h1,
  thermo_step m1 m2 op = (m1a, m2a, h1) ->
  thermo_cycle m1 m2 op (fs steps') = (m1', m2', h) ->
  h1 <> fz ->
  h <> fz.
Proof.
  intros steps' m1 m2 op m1' m2' h m1a m2a h1 Hstep Hcyc Hh1.
  simpl in Hcyc.
  rewrite Hstep in Hcyc.
  destruct (thermo_cycle m1a m2a op steps') as [[m1b m2b] h2] eqn:Hrec.
  inversion Hcyc; subst.
  apply add_spur_nonzero_l. exact Hh1.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 18                                               *)
(*                                                                    *)
(*   add_spur_nonzero_l              a <> fz -> add_spur a b <> fz    *)
(*   add_spur_nonzero_r              b <> fz -> add_spur a b <> fz    *)
(*   thermo_cycle_no_free_lunch_op   op <> fz, steps <> fz -> h <> fz *)
(*   thermo_cycle_succ_spuren        h = h_step + h_rest (struktura)  *)
(*   thermo_cycle_first_step_nonzero h1 <> fz -> h <> fz              *)
(*                                                                    *)
(* Po PART 18 warstwa termodynamiczna ma domkniety audyt.             *)
(* Cykl termodynamiczny nie moze uciec od zaplaty — kazda iteracja    *)
(* z niezerowym kosztem lub niezerowym admitted emituje Spuren,       *)
(* a cykliczna agregacja propaguje niezerowosc przez add_spur.        *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 19: THERMO-LAYER DULCINEA CAPSTONE (Runda 8 zamkniecie)      *)
(*                                                                    *)
(* Spaja no-free-lunch z PART 16 i 18 w jedno domykajace twierdzenie.*)
(*                                                                    *)
(* Postac disjunktywna: jesli albo koszt operacji, albo transfer     *)
(* admitted byl niezerowy, Spuren musi byc niezerowy.                *)
(*                                                                    *)
(* Postac contrapozytywna ("dulcinea-free"): Spuren = fz implikuje   *)
(* ze wszystkie zrodla pracy byly zerowe. Nie ma regionu, w ktorym   *)
(* membrana wykonuje prace bez sladu.                                 *)
(* ================================================================ *)

(* ---- Disjunktywne no-free-lunch dla thermo_step ---- *)

Lemma thermo_step_no_free_lunch_disjunctive :
  forall m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake,
  intake m1 m2 = (adm, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  (op_cost <> fz \/ adm <> fz) ->
  h <> fz.
Proof.
  intros m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake
         Hintake Hstep Hor.
  destruct Hor as [Hop | Hadm].
  - exact (thermo_step_no_free_lunch_op _ _ _ _ _ _ Hstep Hop).
  - exact (thermo_step_no_free_lunch_admitted
             _ _ _ _ _ _ _ _ _ _ Hintake Hstep Hadm).
Qed.

(* ---- Dulcinea-free dla thermo_step (contrapozycja) ---- *)

(* Jesli h = fz, to zarowno op_cost = fz jak i adm = fz.              *)
(* Zadna praca nie zostala wykonana bez sladu.                        *)

Lemma thermo_step_dulcinea_free :
  forall m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake,
  intake m1 m2 = (adm, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  h = fz ->
  op_cost = fz /\ adm = fz.
Proof.
  intros m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake
         Hintake Hstep Hh.
  split.
  - (* op_cost = fz *)
    destruct op_cost as [| oc'].
    + reflexivity.
    + exfalso.
      apply (thermo_step_no_free_lunch_op _ _ _ _ _ _ Hstep).
      * discriminate.
      * exact Hh.
  - (* adm = fz *)
    destruct adm as [| a'].
    + reflexivity.
    + exfalso.
      apply (thermo_step_no_free_lunch_admitted
               _ _ _ _ _ _ _ _ _ _ Hintake Hstep).
      * discriminate.
      * exact Hh.
Qed.

(* ---- Dulcinea-free dla thermo_cycle ---- *)

(* Jesli cykl emitowal zero Spuren, to albo nie wykonano kroku       *)
(* (steps = fz), albo koszt operacji byl trywialny (op = fz).        *)
(* Rekurencyjna wersja zasady "nie ma darmowej pracy".                *)

Lemma thermo_cycle_dulcinea_free :
  forall steps m1 m2 op m1' m2' h,
  thermo_cycle m1 m2 op steps = (m1', m2', h) ->
  h = fz ->
  op = fz \/ steps = fz.
Proof.
  intros steps m1 m2 op m1' m2' h Hcyc Hh.
  destruct op as [| op'].
  - left. reflexivity.
  - destruct steps as [| steps'].
    + right. reflexivity.
    + (* steps = fs steps', op = fs op': sprzecznosc z thermo_cycle_no_free_lunch_op *)
      exfalso.
      apply (thermo_cycle_no_free_lunch_op _ _ _ _ _ _ _ Hcyc).
      * discriminate.
      * discriminate.
      * exact Hh.
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 19                                               *)
(*                                                                    *)
(*   thermo_step_no_free_lunch_disjunctive                            *)
(*     (op_cost <> fz \/ adm <> fz) -> h <> fz                        *)
(*                                                                    *)
(*   thermo_step_dulcinea_free                                        *)
(*     h = fz -> op_cost = fz /\ adm = fz                             *)
(*                                                                    *)
(*   thermo_cycle_dulcinea_free                                       *)
(*     h = fz -> op = fz \/ steps = fz                                *)
(*                                                                    *)
(* Runda 8 zamknieta. Warstwa termodynamiczna membrany ma formalny   *)
(* dowod, ze w zadnym punkcie — ani na poziomie pojedynczego kroku,  *)
(* ani na poziomie cyklu — nie istnieje region pracy bez sladu.      *)
(* Dulcinea nie istnieje nawet jako mozliwosc kompozycyjna.          *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 20: INTAKE + THERMO_STEP FULL DULCINEA (Runda 8 zamkniecie)  *)
(*                                                                    *)
(* Ostateczne zamkniecie warstwy membranowej. Dwa twierdzenia:        *)
(*                                                                    *)
(*   (1) intake_dulcinea_free — na poziomie intake:                   *)
(*       h_intake = fz => adm = fz                                    *)
(*                                                                    *)
(*   (2) thermo_step_full_dulcinea — na poziomie thermo_step:         *)
(*       h = fz => op_cost = fz /\ adm = fz /\ h_intake = fz          *)
(*                                                                    *)
(* Drugie twierdzenie jest mocniejsze niz PART 19 dulcinea_free —    *)
(* pokazuje, ze h = fz na poziomie thermo_step wymusza zero na       *)
(* wszystkich trzech niezaleznych zrodlach pracy (koszt operacji,    *)
(* transfer admitted, proces rozpoznania).                            *)
(* ================================================================ *)

(* ---- Dulcinea-free dla intake ---- *)

(* Jesli intake emitowal zero Spuren, to zadne admitted nie zostalo  *)
(* przepuszczone. Contrapozycja intake_BTrue_no_free_lunch.          *)

Lemma intake_dulcinea_free :
  forall m1 m2 adm m1' m2' h,
  intake m1 m2 = (adm, m1', m2', h) ->
  h = fz ->
  adm = fz.
Proof.
  intros m1 m2 adm m1' m2' h Hintake Hh.
  destruct adm as [| adm'].
  - reflexivity.
  - exfalso.
    apply (intake_BTrue_no_free_lunch _ _ _ _ _ _ Hintake).
    + discriminate.
    + exact Hh.
Qed.

(* ---- Full Dulcinea-free dla thermo_step ---- *)

(* Rozszerzenie PART 19: jesli thermo_step emitowal zero Spuren,     *)
(* to wszystkie trzy zrodla pracy byly trywialne. Uzywa              *)
(* thermo_step_spuren_decomposition aby rozbic h na h_intake + op.   *)

Lemma thermo_step_full_dulcinea :
  forall m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake,
  intake m1 m2 = (adm, m1_int, m2_int, h_intake) ->
  thermo_step m1 m2 op_cost = (m1', m2', h) ->
  h = fz ->
  op_cost = fz /\ adm = fz /\ h_intake = fz.
Proof.
  intros m1 m2 op_cost m1' m2' h adm m1_int m2_int h_intake
         Hintake Hstep Hh.
  pose proof (thermo_step_spuren_decomposition
                _ _ _ _ _ _ _ _ _ _ Hintake Hstep) as Hdec.
  rewrite Hh in Hdec.
  symmetry in Hdec.
  (* Hdec : add_spur h_intake op_cost = fz *)
  assert (Hint_fz : h_intake = fz).
  { destruct h_intake as [| hi'].
    - reflexivity.
    - exfalso. rewrite add_spur_fs_l in Hdec. discriminate. }
  rewrite Hint_fz in Hdec.
  rewrite add_spur_fz_l in Hdec.
  (* Hdec : op_cost = fz *)
  split; [exact Hdec | split; [| exact Hint_fz]].
  (* adm = fz via intake_dulcinea_free *)
  exact (intake_dulcinea_free _ _ _ _ _ _ Hintake Hint_fz).
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 20                                               *)
(*                                                                    *)
(*   intake_dulcinea_free                                             *)
(*     h_intake = fz -> adm = fz                                      *)
(*                                                                    *)
(*   thermo_step_full_dulcinea                                        *)
(*     h = fz -> op_cost = fz /\ adm = fz /\ h_intake = fz            *)
(*                                                                    *)
(* Runda 8 calkowicie zamknieta. Kazdy poziom membrany (spend,       *)
(* recognize, intake, thermo_step, thermo_cycle) ma dowod, ze Spuren *)
(* = fz wymusza trywialnosc wszystkich zrodel pracy. Dulcinea nie    *)
(* istnieje jako region, punkt, ani jako mozliwosc kompozycyjna.     *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 21: BRIDGE T2 ⊆ T1 — computational to Prop-level (Runda 9) *)
(*                                                                    *)
(* Comment na poczatku pliku zapowiadal: jesli testy wzorca pi2 sa *)
(* podzbiorem testow wzorca pi1 (T2 subset T1). W module PART 10    *)
(* embed                                                              *)
(* uzywa filter_implies_spur ktora zwraca BTrue gdy (1) wszystkie   *)
(* pary z mem_filter_center m2 sa w mem_filter_center m1 i (2)      *)
(* mem_filter_radius m2 <= mem_filter_radius m1.                     *)
(*                                                                    *)
(* Dotad mielismy tylko operacyjne twierdzenia o filter_implies_spur *)
(* (conservation, no-free-lunch, branch semantics). Brakowalo        *)
(* BRIDGE'A — formalnego polaczenia obliczeniowego wyniku BTrue z   *)
(* Prop-poziomowym stwierdzeniem inkluzji zbiorow.                   *)
(*                                                                    *)
(* Bridge ma dwa znaczenia:                                           *)
(*   1. Soundness obliczeniowy: BTrue zwrocone przez test implikuje *)
(*      semantyczna inkluzje. Test jest POPRAWNY — nie oszukuje.     *)
(*   2. Epistemologiczna dyscyplina: BUnknown != inkluzja fails.    *)
(*      Brak budzetu oznacza niewiedze, nie negacje. Test odmawia    *)
(*      udawania wyroku gdy nie stac go na rozpoznanie.              *)
(*                                                                    *)
(* Ten part buduje soundness. Kompletnosc (jesli inkluzja zachodzi  *)
(* i budzet starcza -> BTrue) jest osobny plant — wymaga minimum     *)
(* budget. Nie wchodzimy w to dzis.                                   *)
(* ================================================================ *)

(* ---- Soundness dla fin_eq_b3 ---- *)

Lemma fin_eq_b3_btrue_implies_eq : forall n m b b' h,
  fin_eq_b3 n m b = (BTrue, b', h) -> n = m.
Proof.
  induction n as [|n' IH]; intros m b b' h Heq.
  - destruct b as [|b''].
    + simpl in Heq. discriminate.
    + destruct m as [|m'].
      * reflexivity.
      * simpl in Heq. discriminate.
  - destruct b as [|b''].
    + simpl in Heq. discriminate.
    + destruct m as [|m'].
      * simpl in Heq. discriminate.
      * simpl in Heq.
        destruct (fin_eq_b3 n' m' b'') as [[r0 b0] h0] eqn:Hrec.
        inversion Heq; subst.
        f_equal. exact (IH m' b'' b' h0 Hrec).
Qed.

(* ---- Soundness dla fin_pair_eq_spur ---- *)

Lemma fin_pair_eq_spur_btrue_implies_eq :
  forall p q b b' h,
  fin_pair_eq_spur p q b = (BTrue, b', h) -> p = q.
Proof.
  intros [a b_p] [c d] b b' h Heq.
  unfold fin_pair_eq_spur in Heq.
  destruct (fin_eq_b3 a c b) as [[r1 b1] h1] eqn:Heq1.
  destruct r1.
  - destruct (fin_eq_b3 b_p d b1) as [[r2 b2] h2] eqn:Heq2.
    inversion Heq; subst.
    apply fin_eq_b3_btrue_implies_eq in Heq1.
    apply fin_eq_b3_btrue_implies_eq in Heq2.
    subst. reflexivity.
  - discriminate.
  - discriminate.
Qed.

(* ---- Soundness dla pair_in_list_spur ---- *)

Lemma pair_in_list_spur_btrue_implies_in :
  forall p xs b b' h,
  pair_in_list_spur p xs b = (BTrue, b', h) -> In p xs.
Proof.
  intros p xs. induction xs as [| x xs' IH]; intros b b' h Heq.
  - simpl in Heq. discriminate.
  - simpl in Heq.
    destruct (fin_pair_eq_spur p x b) as [[r1 b1] h1] eqn:Heq1.
    destruct r1.
    + apply fin_pair_eq_spur_btrue_implies_eq in Heq1.
      subst x. left. reflexivity.
    + destruct (pair_in_list_spur p xs' b1) as [[r2 b2] h2] eqn:Heq2.
      inversion Heq; subst.
      right. exact (IH b1 b' h2 Heq2).
    + discriminate.
Qed.

(* ---- Soundness dla filter_subset_spur ---- *)

Lemma filter_subset_spur_btrue_implies_subset :
  forall xs ys b b' h,
  filter_subset_spur xs ys b = (BTrue, b', h) ->
  forall p, In p xs -> In p ys.
Proof.
  intros xs. induction xs as [| x xs' IH]; intros ys b b' h Heq p Hin.
  - simpl in Hin. contradiction.
  - simpl in Heq.
    destruct (pair_in_list_spur x ys b) as [[r1 b1] h1] eqn:Heq1.
    destruct r1.
    + destruct (filter_subset_spur xs' ys b1) as [[r2 b2] h2] eqn:Heq2.
      inversion Heq; subst.
      simpl in Hin. destruct Hin as [Hhead | Htail].
      * subst x.
        exact (pair_in_list_spur_btrue_implies_in p ys b b1 h1 Heq1).
      * exact (IH ys b1 b' h2 Heq2 p Htail).
    + discriminate.
    + discriminate.
Qed.

(* ---- Soundness dla le_fin_b3 ---- *)

Lemma le_fin_b3_btrue_implies_le_struct :
  forall n m b b' h,
  le_fin_b3 n m b = (BTrue, b', h) -> le_struct n m = true.
Proof.
  induction n as [|n' IH]; intros m b b' h Heq.
  - simpl. reflexivity.
  - destruct b as [|b''].
    + simpl in Heq. discriminate.
    + destruct m as [|m'].
      * simpl in Heq. discriminate.
      * simpl in Heq.
        destruct (le_fin_b3 n' m' b'') as [[r0 b0] h0] eqn:Hrec.
        inversion Heq; subst.
        simpl. exact (IH m' b'' b' h0 Hrec).
Qed.

(* ---- Prop-level filter subset ---- *)

(* T2 ⊆ T1 jako Prop: kazdy punkt filtra m2 jest punktem filtra m1, *)
(* oraz tolerancja m2 nie szersza niz m1.                          *)

Definition filter_subset_prop (m1 m2 : Membrane) : Prop :=
  (forall p, In p (mem_filter_center m2) -> In p (mem_filter_center m1))
  /\ le_struct (mem_filter_radius m2) (mem_filter_radius m1) = true.

(* ---- GLOWNY BRIDGE: computational BTrue -> Prop-level subset ---- *)

Theorem filter_implies_spur_btrue_bridge :
  forall m1 m2 b b' h,
  filter_implies_spur m1 m2 b = (BTrue, b', h) ->
  filter_subset_prop m1 m2.
Proof.
  intros m1 m2 b b' h Hfilt.
  unfold filter_implies_spur in Hfilt.
  destruct (filter_subset_spur (mem_filter_center m2)
                               (mem_filter_center m1) b)
    as [[r1 b1] h1] eqn:Hsub.
  destruct r1.
  - destruct (le_fin_b3 (mem_filter_radius m2)
                        (mem_filter_radius m1) b1)
      as [[r2 b2] h2] eqn:Hle.
    inversion Hfilt; subst.
    split.
    + exact (filter_subset_spur_btrue_implies_subset
               _ _ _ _ _ Hsub).
    + exact (le_fin_b3_btrue_implies_le_struct
               _ _ _ _ _ Hle).
  - discriminate.
  - discriminate.
Qed.

(* ---- BRIDGE dla embed: BTrue branch -> semantic subset ---- *)

(* Jesli embed sukcesem (BTrue zwrocone przez filter_implies_spur) *)
(* to semantyka inkluzji jest zapewniona. Embed nie ryzykuje —      *)
(* dostajesz compound tylko gdy test faktycznie wykazal inkluzje.  *)

Theorem embed_btrue_implies_filter_subset :
  forall m1 m2 m1' h b',
  filter_implies_spur m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  embed m1 m2 = (m1', h) ->
  filter_subset_prop m1 m2.
Proof.
  intros m1 m2 m1' h b' Hfilt _.
  exact (filter_implies_spur_btrue_bridge _ _ _ _ _ Hfilt).
Qed.

(* ================================================================ *)
(* PODSUMOWANIE PART 21                                               *)
(*                                                                    *)
(*   fin_eq_b3_btrue_implies_eq                                       *)
(*   fin_pair_eq_spur_btrue_implies_eq                                *)
(*   pair_in_list_spur_btrue_implies_in                               *)
(*   filter_subset_spur_btrue_implies_subset                          *)
(*   le_fin_b3_btrue_implies_le_struct                                *)
(*   filter_implies_spur_btrue_bridge                                 *)
(*   embed_btrue_implies_filter_subset                                *)
(*                                                                    *)
(* Po PART 21 warstwa embed'u ma bridge soundness: obliczeniowy     *)
(* BTrue gwarantuje semantyczna inkluzje T2 ⊆ T1. To domyka         *)
(* lukke miedzy programistyczna procedurowym testem a formalnym    *)
(* Prop-poziomowym stwierdzeniem. Test jest POPRAWNY.                *)
(*                                                                    *)
(* BUnknown i BFalse nie sa objete bridge-em — zgodnie z VOID-em.  *)
(* BFalse mowi: znalazlem jawny konflikt. BUnknown mowi: nie stac   *)
(* mnie na rozstrzygniecie. Zaden z nich nie neguje inkluzji        *)
(* semantycznie — sa to rozne epistemologicznie stany. Kompletnosc *)
(* (semantic subset + budget starczy -> BTrue) to osobny kierunek, *)
(* bedzie musial poczekac albo zostac wyciagniety do osobnego      *)
(* artykulu o relacji test-vs-prop w VOID.                          *)
(* ================================================================ *)

(* ================================================================ *)
(* PART 22: DEEP EMBED — rekursyjne sprawdzanie compound (Runda 9)  *)
(*                                                                    *)
(* Plain embed (PART 10) sprawdza tylko outer: filter_implies_spur   *)
(* m1 m2. Jesli m1 jest compound (mem_inner m1 <> nil), nie dotyka  *)
(* ukrytych warstw. To jest wystarczajace dla Thm 8.15 (parasitic   *)
(* maintenance), ale niewystarczajace dla twierdzen typu: m2 jest   *)
(* zgodne z cala struktura m1.                                       *)
(*                                                                    *)
(* Deep embed wymaga, zeby m2 przeszlo filter_implies_spur nie      *)
(* tylko przeciw outer'owi m1 ale takze przeciw kazdej wewnetrznej *)
(* membranie z mem_inner m1. Short-circuit na pierwszym BFalse/     *)
(* BUnknown. Konjunkcja.                                             *)
(*                                                                    *)
(* To nie jest rekursja przez Membrane jako drzewo (nie schodzimy w *)
(* mem_inner mem_inner); jest to rekursja po liscie mem_inner m1    *)
(* na jednym poziomie. Glebokosc jest ograniczona do jednego        *)
(* poziomu wgl. VOID nie oferuje structural rekursji po Membrane    *)
(* bez fuel'a (mem_inner ma typ list Membrane, wiec Coq przyjmuje  *)
(* fixpoint po liscie, ale nie po Membrane samo w sobie).           *)
(*                                                                    *)
(* Pelniejsza wersja (drzewiaste sprawdzanie) wymagalaby fuel'a lub *)
(* separate Membrane_rect na wzor List_rect. Nie wchodzimy dzis.    *)
(* ================================================================ *)

(* ---- all_inner_accept_spur: kazdy inner m1 akceptuje m2? ---- *)

Fixpoint all_inner_accept_spur
           (inners : list Membrane) (m : Membrane) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match inners with
  | nil => (BTrue, b, fz)
  | i :: rest =>
      match filter_implies_spur i m b with
      | (BTrue, b1, h1) =>
          match all_inner_accept_spur rest m b1 with
          | (r, b2, h2) => (r, b2, add_spur h1 h2)
          end
      | (BFalse, b1, h1) => (BFalse, b1, h1)
      | (BUnknown, b1, h1) => (BUnknown, b1, h1)
      end
  end.

(* ---- deep_accepts: outer + wszystkie inner ---- *)

Definition deep_accepts (m1 m2 : Membrane) (b : Budget)
  : (Bool3 * Budget * Spuren) :=
  match filter_implies_spur m1 m2 b with
  | (BTrue, b1, h1) =>
      match all_inner_accept_spur (mem_inner m1) m2 b1 with
      | (r, b2, h2) => (r, b2, add_spur h1 h2)
      end
  | (BFalse, b1, h1) => (BFalse, b1, h1)
  | (BUnknown, b1, h1) => (BUnknown, b1, h1)
  end.

(* ---- deep_embed: embed tylko jesli deep_accepts BTrue ---- *)

Definition deep_embed (m1 m2 : Membrane) : Membrane * Spuren :=
  match deep_accepts m1 m2 (mem_budget m1) with
  | (BTrue, b', h) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b'
                            (m2 :: mem_inner m1) in
      (m1', h)
  | (BFalse, b', h) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b'
                            (mem_inner m1) in
      (m1', h)
  | (BUnknown, b', h) =>
      let m1' := mkMembrane (mem_filter_center m1)
                            (mem_filter_radius m1)
                            (mem_capacity m1)
                            b'
                            (mem_inner m1) in
      (m1', h)
  end.

(* ---- Conservation dla all_inner_accept_spur ---- *)

Lemma all_inner_accept_spur_conservation :
  forall inners m b r b' h,
  all_inner_accept_spur inners m b = (r, b', h) ->
  add_spur h b' = b.
Proof.
  intros inners m. induction inners as [| i rest IH]; intros b r b' h Heq.
  - simpl in Heq. inversion Heq; subst.
    apply add_spur_fz_l.
  - simpl in Heq.
    destruct (filter_implies_spur i m b) as [[r1 b1] h1] eqn:Hfilt.
    destruct r1.
    + destruct (all_inner_accept_spur rest m b1) as [[r2 b2] h2] eqn:Hrec.
      inversion Heq; subst.
      pose proof (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt) as Hc1.
      pose proof (IH _ _ _ _ Hrec) as Hc2.
      rewrite <- Hc1. rewrite <- Hc2.
      apply add_spur_assoc.
    + inversion Heq; subst.
      exact (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt).
    + inversion Heq; subst.
      exact (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt).
Qed.

(* ---- Conservation dla deep_accepts ---- *)

Lemma deep_accepts_conservation :
  forall m1 m2 b r b' h,
  deep_accepts m1 m2 b = (r, b', h) ->
  add_spur h b' = b.
Proof.
  intros m1 m2 b r b' h Heq.
  unfold deep_accepts in Heq.
  destruct (filter_implies_spur m1 m2 b) as [[r1 b1] h1] eqn:Hfilt.
  destruct r1.
  - destruct (all_inner_accept_spur (mem_inner m1) m2 b1)
      as [[r2 b2] h2] eqn:Hinner.
    inversion Heq; subst.
    pose proof (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt) as Hc1.
    pose proof (all_inner_accept_spur_conservation _ _ _ _ _ _ Hinner) as Hc2.
    rewrite <- Hc1. rewrite <- Hc2.
    apply add_spur_assoc.
  - inversion Heq; subst.
    exact (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt).
  - inversion Heq; subst.
    exact (filter_implies_spur_conservation _ _ _ _ _ _ Hfilt).
Qed.

(* ---- deep_embed conservation: budget po = test result ---- *)

Theorem deep_embed_conservation :
  forall m1 m2 m1' h,
  deep_embed m1 m2 = (m1', h) ->
  add_spur h (mem_budget m1') = mem_budget m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold deep_embed in Hembed.
  destruct (deep_accepts m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hdeep.
  pose proof (deep_accepts_conservation _ _ _ _ _ _ Hdeep) as Hc.
  destruct r; inversion Hembed; subst; simpl; exact Hc.
Qed.

(* ---- Outer shape preservation ---- *)

Theorem deep_embed_preserves_outer_center : forall m1 m2 m1' h,
  deep_embed m1 m2 = (m1', h) ->
  mem_filter_center m1' = mem_filter_center m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold deep_embed in Hembed.
  destruct (deep_accepts m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hdeep.
  destruct r; inversion Hembed; subst; simpl; reflexivity.
Qed.

Theorem deep_embed_preserves_outer_radius : forall m1 m2 m1' h,
  deep_embed m1 m2 = (m1', h) ->
  mem_filter_radius m1' = mem_filter_radius m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold deep_embed in Hembed.
  destruct (deep_accepts m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hdeep.
  destruct r; inversion Hembed; subst; simpl; reflexivity.
Qed.

Theorem deep_embed_preserves_outer_capacity : forall m1 m2 m1' h,
  deep_embed m1 m2 = (m1', h) ->
  mem_capacity m1' = mem_capacity m1.
Proof.
  intros m1 m2 m1' h Hembed.
  unfold deep_embed in Hembed.
  destruct (deep_accepts m1 m2 (mem_budget m1))
    as [[r b'] h'] eqn:Hdeep.
  destruct r; inversion Hembed; subst; simpl; reflexivity.
Qed.

(* ---- BTrue branch: inner grows ---- *)

Theorem deep_embed_btrue_grows_inner : forall m1 m2 m1' h b',
  deep_accepts m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  deep_embed m1 m2 = (m1', h) ->
  mem_inner m1' = m2 :: mem_inner m1.
Proof.
  intros m1 m2 m1' h b' Hdeep Hembed.
  unfold deep_embed in Hembed.
  rewrite Hdeep in Hembed.
  inversion Hembed; subst. simpl. reflexivity.
Qed.

(* ---- BFalse branch: inner preserved ---- *)

Theorem deep_embed_bfalse_preserves_inner : forall m1 m2 m1' h b',
  deep_accepts m1 m2 (mem_budget m1) = (BFalse, b', h) ->
  deep_embed m1 m2 = (m1', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  intros m1 m2 m1' h b' Hdeep Hembed.
  unfold deep_embed in Hembed.
  rewrite Hdeep in Hembed.
  inversion Hembed; subst. simpl. reflexivity.
Qed.

(* ---- BUnknown branch: inner preserved ---- *)

Theorem deep_embed_bunknown_preserves_inner : forall m1 m2 m1' h b',
  deep_accepts m1 m2 (mem_budget m1) = (BUnknown, b', h) ->
  deep_embed m1 m2 = (m1', h) ->
  mem_inner m1' = mem_inner m1.
Proof.
  intros m1 m2 m1' h b' Hdeep Hembed.
  unfold deep_embed in Hembed.
  rewrite Hdeep in Hembed.
  inversion Hembed; subst. simpl. reflexivity.
Qed.

(* ---- Deep BTrue -> outer bridge propaguje ---- *)

(* Jesli deep_accepts zwrocilo BTrue, to w szczegolnosci             *)
(* filter_implies_spur m1 m2 zwrocilo BTrue, wiec Prop-poziomowa    *)
(* inkluzja outer'a jest zagwarantowana przez bridge z PART 21.     *)

Theorem deep_accepts_btrue_implies_outer_subset :
  forall m1 m2 b b' h,
  deep_accepts m1 m2 b = (BTrue, b', h) ->
  filter_subset_prop m1 m2.
Proof.
  intros m1 m2 b b' h Hdeep.
  unfold deep_accepts in Hdeep.
  destruct (filter_implies_spur m1 m2 b) as [[r1 b1] h1] eqn:Hfilt.
  destruct r1.
  - exact (filter_implies_spur_btrue_bridge _ _ _ _ _ Hfilt).
  - discriminate.
  - discriminate.
Qed.

(* ---- Deep BTrue -> wszystkie inner akceptuja m2 ---- *)

(* Rekurencyjne: jesli deep_accepts BTrue, kazda inner membrana      *)
(* z mem_inner m1 takze zwrocila BTrue w filter_implies_spur (z     *)
(* odpowiednim budzetem). Forall-postac.                             *)

Lemma all_inner_accept_btrue_forall :
  forall inners m b b' h,
  all_inner_accept_spur inners m b = (BTrue, b', h) ->
  forall i, In i inners ->
  exists bi bi' hi,
    filter_implies_spur i m bi = (BTrue, bi', hi).
Proof.
  intros inners m. induction inners as [| x rest IH];
    intros b b' h Heq i Hin.
  - simpl in Hin. contradiction.
  - simpl in Heq.
    destruct (filter_implies_spur x m b) as [[r1 b1] h1] eqn:Hfilt.
    destruct r1.
    + destruct (all_inner_accept_spur rest m b1)
        as [[r2 b2] h2] eqn:Hrec.
      inversion Heq; subst.
      simpl in Hin. destruct Hin as [Hhead | Htail].
      * subst x.
        exists b, b1, h1. exact Hfilt.
      * exact (IH _ _ _ Hrec i Htail).
    + discriminate.
    + discriminate.
Qed.

(* ---- Deep BTrue -> kazda inner ma Prop-poziomowy subset z m2 ---- *)

Theorem deep_accepts_btrue_implies_all_inner_subset :
  forall m1 m2 b b' h,
  deep_accepts m1 m2 b = (BTrue, b', h) ->
  forall i, In i (mem_inner m1) -> filter_subset_prop i m2.
Proof.
  intros m1 m2 b b' h Hdeep i Hin.
  unfold deep_accepts in Hdeep.
  destruct (filter_implies_spur m1 m2 b) as [[r1 b1] h1] eqn:Hfilt.
  destruct r1.
  - destruct (all_inner_accept_spur (mem_inner m1) m2 b1)
      as [[r2 b2] h2] eqn:Hinner.
    inversion Hdeep; subst.
    destruct (all_inner_accept_btrue_forall _ _ _ _ _ Hinner i Hin)
      as [bi [bi' [hi Hfi]]].
    exact (filter_implies_spur_btrue_bridge _ _ _ _ _ Hfi).
  - discriminate.
  - discriminate.
Qed.

(* ---- CAPSTONE: deep_embed BTrue -> compound jest caly spojny ---- *)

(* Po deep_embed z wynikiem BTrue, m2 dolacza do compound m1, ale    *)
(* TYLKO dlatego ze m2 jest zgodne z outer'em m1 ORAZ z kazda       *)
(* istniejaca wewnetrzna membrana m1. Deep embed nie dolozy m2 do   *)
(* struktury ktora go odrzuca na jakimkolwiek poziomie.             *)

Theorem deep_embed_btrue_full_compatibility :
  forall m1 m2 m1' h b',
  deep_accepts m1 m2 (mem_budget m1) = (BTrue, b', h) ->
  deep_embed m1 m2 = (m1', h) ->
  filter_subset_prop m1 m2 /\
  (forall i, In i (mem_inner m1) -> filter_subset_prop i m2).
Proof.
  intros m1 m2 m1' h b' Hdeep _.
  split.
  - exact (deep_accepts_btrue_implies_outer_subset _ _ _ _ _ Hdeep).
  - exact (deep_accepts_btrue_implies_all_inner_subset _ _ _ _ _ Hdeep).
Qed.

(* No-free-lunch dla all_inner_accept_spur wymagalby lematow         *)
(* no-free-lunch dla filter_implies_spur i filter_subset_spur ktore *)
(* nie byly dotad udowodnione. Zostawiamy na pozniej — Runda 10     *)
(* czyli "filter no free lunch". Capstone compound compatibility    *)
(* nie wymaga ich.                                                    *)

(* ================================================================ *)
(* PODSUMOWANIE PART 22                                               *)
(*                                                                    *)
(*   all_inner_accept_spur                                            *)
(*   deep_accepts                                                     *)
(*   deep_embed                                                       *)
(*                                                                    *)
(*   all_inner_accept_spur_conservation                               *)
(*   deep_accepts_conservation                                        *)
(*   deep_embed_conservation                                          *)
(*                                                                    *)
(*   deep_embed_preserves_outer_center                                *)
(*   deep_embed_preserves_outer_radius                                *)
(*   deep_embed_preserves_outer_capacity                              *)
(*                                                                    *)
(*   deep_embed_btrue_grows_inner                                     *)
(*   deep_embed_bfalse_preserves_inner                                *)
(*   deep_embed_bunknown_preserves_inner                              *)
(*                                                                    *)
(*   deep_accepts_btrue_implies_outer_subset                          *)
(*   all_inner_accept_btrue_forall                                    *)
(*   deep_accepts_btrue_implies_all_inner_subset                      *)
(*   deep_embed_btrue_full_compatibility (CAPSTONE)                   *)
(*                                                                    *)
(* Po PART 22 mamy deep embed ze wszystkimi klasycznymi twierdzeniami*)
(* operacyjnymi (conservation, outer shape preservation, branch      *)
(* semantics) oraz capstone'em full compatibility: BTrue z deep      *)
(* embed implikuje Prop-poziomowa kompatybilnosc m2 z outer'em m1   *)
(* i z kazdym inner'em m1. Compound jest caly spojny po operacji.   *)
(* ================================================================ *)
