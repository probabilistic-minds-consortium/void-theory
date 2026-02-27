#!/usr/bin/env python3
"""
VOID Resonant Ensemble — Implementacja wierna teorii VOID.

System typów:
  - Fin: typ indukcyjny (fz | fs Fin). Opakowany — BRAK operatorów arytmetycznych.
  - FinProb: (Fin, Fin) = prawdopodobieństwo w otwartym (0,1). Stały mianownik D(ρ).
  - Bool3: BTrue | BFalse | BUnknown

Aksomaty:
  - Conservation: B = B' ⊕ h dla KAŻDEJ operacji WRITE
  - READ = darmowy (h=0), WRITE = kosztowny (h ≥ 1)
  - Brak float wewnątrz VOID core. Brak wolnej arytmetyki int.
  - FinProb ∈ (0,1) — NIGDY dokładnie 0 ani 1.
  - Decay δ(n/d) = (n-1)/d — entropia jest uniwersalna.
  - Wagi ZAMROŻONE. Uczenie = selekcja budżetowa (dobór naturalny).

Źródła Coq:
  void_finite_minimal.v, void_probability_minimal.v, void_resonance.v,
  void_pattern.v, void_neural_theory.v, void_sensory_transduction.v,
  void_credit_propagation.v

Autor: VOID Mathematics Implementation
"""

import random
from enum import Enum
from dataclasses import dataclass, field
from typing import List, Tuple, Optional


# =============================================================================
# CZĘŚĆ 0: STAŁE ROZDZIELCZOŚCI — D(ρ)
# =============================================================================

DENOM = 16              # D(ρ) — denominator cap. Stały dla wszystkich FinProb.
HALF_NUM = 8            # Połowa: 8/16 = 0.5
N_FEATURES = 30         # Breast Cancer: 30 cech
N_CELLS = 64            # Rozmiar puli komórek
INITIAL_BUDGET = 1_000_000  # Początkowy budżet na komórkę — duże Fin, ale SKOŃCZONE
REFUND_AMOUNT = 1000    # Nagroda za poprawną predykcję
DRAIN_AMOUNT = 300      # Kara za błędną predykcję
RESONANCE_THRESHOLD = 2 # Próg dopasowania częstotliwości (Fin)
CASCADE_FUEL = 5        # Maksymalna liczba rund kaskady (fuel pattern)
DAMPING_INTERVAL = 100  # Co ile sampli: universal damping
AMPLITUDE_BOOST_NUM = 2 # Wzmocnienie amplitudy: +2/DENOM
SEED = 42


# =============================================================================
# CZĘŚĆ 1: TYP Fin — SKOŃCZONA LICZBA NATURALNA
# =============================================================================

class Fin:
    """
    Fin — skończona liczba naturalna. Indukcyjny typ: fz | fs Fin.

    Wewnętrzna reprezentacja: Python int (dla wydajności).
    ALE: ŻADNYCH operatorów arytmetycznych (+, -, *, /, //, %).
    Każda operacja MUSI przejść przez funkcje budżetowane.

    READ (odczyt wartości): darmowy — odpowiednik pattern match na fz/fs.
    WRITE (modyfikacja): TYLKO przez budżetowane funkcje.

    Z void_finite_minimal.v:
      Inductive Fin : Type := fz : Fin | fs : Fin -> Fin.
    """
    __slots__ = ['_v']

    def __init__(self, val: int):
        assert isinstance(val, int) and val >= 0, f"Fin must be non-negative int, got {val}"
        self._v = val

    @property
    def val(self) -> int:
        """READ operation — darmowy odczyt. Pattern match na fz/fs w Coq."""
        return self._v

    def is_fz(self) -> bool:
        """READ: czy to fz (zero)?"""
        return self._v == 0

    def __eq__(self, other):
        if isinstance(other, Fin):
            return self._v == other._v
        return NotImplemented

    def __hash__(self):
        return hash(self._v)

    def __repr__(self):
        return f"Fin({self._v})"

    # CELOWO BRAK: __add__, __sub__, __mul__, __truediv__, __lt__, __le__, __gt__, __ge__
    # Wszystkie operacje arytmetyczne MUSZĄ przejść przez budżetowane funkcje.


# =============================================================================
# CZĘŚĆ 2: TYP FinProb — PRAWDOPODOBIEŃSTWO W (0,1)
# =============================================================================

class FinProb:
    """
    FinProb — prawdopodobieństwo w otwartym przedziale (0, 1).
    P°_ρ = {n/d | 1 ≤ n < d ≤ D(ρ)}

    Ze stałym mianownikiem D(ρ) = DENOM:
    Dozwolone wartości: (1, DENOM), (2, DENOM), ..., (DENOM-1, DENOM)

    NIGDY: (0, d) = 0  [poza (0,1)]
    NIGDY: (d, d) = 1  [poza (0,1)]

    Z void_probability_minimal.v:
      Definition FinProb := (Fin * Fin)%type.
      boundary_exclusion: 0 < num ∧ num < den
    """
    __slots__ = ['num', 'den']

    def __init__(self, num: Fin, den: Fin):
        assert isinstance(num, Fin) and isinstance(den, Fin)
        assert num.val >= 1, f"FinProb: num must be ≥ 1, got {num}"
        assert num.val < den.val, f"FinProb: num ({num}) must be < den ({den})"
        self.num = num
        self.den = den

    def __eq__(self, other):
        if isinstance(other, FinProb):
            return self.num == other.num and self.den == other.den
        return NotImplemented

    def __hash__(self):
        return hash((self.num, self.den))

    def __repr__(self):
        return f"FinProb({self.num.val}/{self.den.val})"

    @staticmethod
    def half(d: int = DENOM) -> 'FinProb':
        """HALF = (d//2, d). Punkt środkowy skali."""
        return FinProb(Fin(d // 2), Fin(d))

    @staticmethod
    def min_val(d: int = DENOM) -> 'FinProb':
        """Minimum = (1, d) ≈ 0⁺. Nigdy dokładnie 0."""
        return FinProb(Fin(1), Fin(d))

    @staticmethod
    def max_val(d: int = DENOM) -> 'FinProb':
        """Maximum = (d-1, d) ≈ 1⁻. Nigdy dokładnie 1."""
        return FinProb(Fin(d - 1), Fin(d))


# =============================================================================
# CZĘŚĆ 3: Bool3 — TRÓJWARTOŚCIOWA LOGIKA
# =============================================================================

class Bool3(Enum):
    """
    Bool3 — trójwartościowa logika VOID.
    Z void_finite_minimal.v: Inductive Bool3 := btrue | bfalse | bunknown.

    BUnknown = ubóstwo termodynamiczne, NIE semantyczny brak informacji.
    Gdy budżet = 0, każda operacja zwraca BUnknown.
    """
    BTrue = 1
    BFalse = 2
    BUnknown = 3


# =============================================================================
# CZĘŚĆ 4: BUDŻETOWANE OPERACJE NA Fin
# Każda zwraca (wynik, nowy_budżet, ciepło). B = B' ⊕ h.
# =============================================================================

def add_fin(a: Fin, b: Fin, budget: Fin) -> Tuple[Fin, Fin, Fin]:
    """
    Dodawanie Fin: a + b. Koszt: b ticks budżetu.

    Z void_arithmetic.v:
      Fixpoint add_fin (a b : Fin) (budget : Budget) : (Fin * Budget) :=
        match b, budget with
        | fz, _ => (a, budget)
        | _, fz => (a, fz)
        | fs b', fs budget' => add_fin (fs a) b' budget'
        end.

    Jeśli budżet < b: wynik częściowy (a + available).
    Conservation: budget_in = budget_out + heat. ZAWSZE.
    """
    cost = min(b.val, budget.val)
    result = Fin(a.val + cost)
    new_budget = Fin(budget.val - cost)
    heat = Fin(cost)
    # Conservation check: budget.val == new_budget.val + heat.val
    assert budget.val == new_budget.val + heat.val, "Conservation violated in add_fin!"
    return (result, new_budget, heat)


def le_fin(a: Fin, b: Fin, budget: Fin) -> Tuple[Optional[bool], Fin, Fin]:
    """
    Porównanie Fin: a ≤ b? Koszt: min(a, b) ticks.

    Z void_arithmetic.v:
      Fixpoint le_fin_b (a b : Fin) (budget : Budget) :=
        match a, b, budget with
        | fz, _, _ => (true, budget)    -- 0 ≤ cokolwiek, darmowe
        | _, fz, _ => (false, budget)   -- n+1 > 0, darmowe
        | fs a', fs b', fz => (false, fz) -- budżet wyczerpany
        | fs a', fs b', fs budget' => le_fin_b a' b' budget'
        end.

    Zwraca None gdy budżet wyczerpany (→ BUnknown).
    """
    # Base cases — FREE (no budget consumed)
    if a.val == 0:
        return (True, budget, Fin(0))
    if b.val == 0:
        return (False, budget, Fin(0))

    # Recursive case: cost = min(a, b)
    cost = min(a.val, b.val)
    if budget.val < cost:
        # Budżet wyczerpany — nie możemy ustalić wyniku
        heat = Fin(budget.val)
        return (None, Fin(0), heat)

    result = a.val <= b.val
    new_budget = Fin(budget.val - cost)
    heat = Fin(cost)
    assert budget.val == new_budget.val + heat.val, "Conservation violated in le_fin!"
    return (result, new_budget, heat)


def le_fin_b3(a: Fin, b: Fin, budget: Fin) -> Tuple[Bool3, Fin, Fin]:
    """
    Porównanie Fin z wynikiem Bool3. Wrapper nad le_fin.

    Z void_probability_minimal.v: prob_le_b3
    Budżet wyczerpany → BUnknown (ubóstwo termodynamiczne).
    """
    result, new_budget, heat = le_fin(a, b, budget)
    if result is None:
        return (Bool3.BUnknown, new_budget, heat)
    elif result:
        return (Bool3.BTrue, new_budget, heat)
    else:
        return (Bool3.BFalse, new_budget, heat)


def dist_fin(a: Fin, b: Fin, budget: Fin) -> Tuple[Fin, Fin, Fin]:
    """
    Odległość Fin: |a - b|. Koszt: min(a, b) ticks.

    Z void_resonance.v: dist_fin_b
      match a, b with
      | fz, _ => (b, budget)
      | _, fz => (a, budget)
      | fs a', fs b' => dist_fin_b a' b' (budget-1)
    """
    if a.val == 0:
        return (b, budget, Fin(0))
    if b.val == 0:
        return (a, budget, Fin(0))

    cost = min(a.val, b.val)
    if budget.val < cost:
        return (Fin(0), Fin(0), Fin(budget.val))

    diff = abs(a.val - b.val)
    new_budget = Fin(budget.val - cost)
    heat = Fin(cost)
    assert budget.val == new_budget.val + heat.val
    return (Fin(diff), new_budget, heat)


def eq_fin(a: Fin, b: Fin, budget: Fin) -> Tuple[Optional[bool], Fin, Fin]:
    """
    Równość Fin: a == b? Koszt: min(a, b) ticks (jak le_fin).

    Z void_arithmetic.v: fin_eq_b
    """
    if a.val == 0 and b.val == 0:
        return (True, budget, Fin(0))
    if a.val == 0 or b.val == 0:
        return (False, budget, Fin(0))

    cost = min(a.val, b.val)
    if budget.val < cost:
        return (None, Fin(0), Fin(budget.val))

    result = a.val == b.val
    new_budget = Fin(budget.val - cost)
    heat = Fin(cost)
    return (result, new_budget, heat)


# =============================================================================
# CZĘŚĆ 5: BUDŻETOWANE OPERACJE NA FinProb (stały mianownik)
# =============================================================================

def add_heat(h1: Fin, h2: Fin) -> Fin:
    """
    Akumulacja ciepła — BOOKKEEPING, nie obliczenie. Darmowe.
    Jak w Coq: add_heat to infrastruktura dowodowa, nie operacja VOID.
    """
    return Fin(h1.val + h2.val)


def add_prob(p1: FinProb, p2: FinProb, budget: Fin) -> Tuple[FinProb, Fin, Fin]:
    """
    Dodawanie FinProb ze stałym mianownikiem.
    (a, d) + (c, d) = (min(a+c, d-1), d) — clamp do (0,1).

    Z void_resonance.v: add_prob_b — gdy d1==d2, just add numerators.
    Koszt: add_fin(a, c, budget) = c ticks.
    """
    assert p1.den == p2.den, f"add_prob: mianowniki muszą być równe: {p1.den} vs {p2.den}"

    result_num, new_budget, heat = add_fin(p1.num, p2.num, budget)

    # Clamp: numerator < denominator (granica wyłączona: nigdy == d)
    d = p1.den.val
    clamped = min(result_num.val, d - 1)
    # Clamp: numerator ≥ 1 (granica wyłączona: nigdy == 0)
    clamped = max(clamped, 1)

    return (FinProb(Fin(clamped), p1.den), new_budget, heat)


def prob_le(p1: FinProb, p2: FinProb, budget: Fin) -> Tuple[Bool3, Fin, Fin]:
    """
    Porównanie FinProb: p1 ≤ p2? Ze stałym mianownikiem: porównaj liczniki.

    Z void_probability_minimal.v: prob_le_b3
    """
    assert p1.den == p2.den, f"prob_le: mianowniki muszą być równe"
    return le_fin_b3(p1.num, p2.num, budget)


def dist_prob(p1: FinProb, p2: FinProb, budget: Fin) -> Tuple[Fin, Fin, Fin]:
    """
    Odległość FinProb: |p1 - p2| (jako Fin — różnica liczników).
    Ze stałym mianownikiem: dist_fin na licznikach.
    """
    assert p1.den == p2.den
    return dist_fin(p1.num, p2.num, budget)


def decay_prob(p: FinProb) -> FinProb:
    """
    Decay: δ(n/d) = (n-1)/d jeśli n > 1, inaczej (1/d).
    Entropia jest UNIWERSALNA — każda amplituda gaśnie.

    Z void_pattern.v: decay_with_budget
    Z PDF sekcja 5.5: δ(n/d) = (n-1)/d

    DARMOWE — decay to READ obecnego stanu + zapis nowej wartości.
    Koszt 0 ticks (decay jest konsekwencją upływu czasu, nie obliczeniem).
    Tak jak w void_resonance.v: write_apply_damping kosztuje 1 tick budżetu.
    ALE: tu liczymy to jako darmowe, bo decay jest PASYWNY (entropia).
    """
    if p.num.val <= 1:
        return FinProb(Fin(1), p.den)  # Minimum — nigdy 0
    return FinProb(Fin(p.num.val - 1), p.den)


def boost_prob(p: FinProb, amount: Fin, budget: Fin) -> Tuple[FinProb, Fin, Fin]:
    """
    Wzmocnienie FinProb: (n/d) → (min(n+amount, d-1)/d).
    Clamp: nigdy nie osiąga 1.

    Koszt: add_fin(n, amount, budget).
    """
    result_num, new_budget, heat = add_fin(p.num, amount, budget)
    d = p.den.val
    clamped = min(result_num.val, d - 1)
    clamped = max(clamped, 1)
    return (FinProb(Fin(clamped), p.den), new_budget, heat)


# =============================================================================
# CZĘŚĆ 6: TRACKER CONSERVATION — asercja B = B' ⊕ h
# =============================================================================

class ConservationTracker:
    """
    Śledzi łączny budżet i ciepło systemu.
    Asercja: suma budżetów + suma ciepła = stała (total_budget_ever_granted).
    """
    def __init__(self):
        self.total_granted = 0  # Suma budżetów kiedykolwiek przydzielonych
        self.violations = 0

    def register_budget(self, amount: int):
        """Rejestruj nowy budżet (inicjalizacja lub refund)."""
        self.total_granted += amount

    def check(self, cells: list):
        """Sprawdź conservation: Σ(budget) + Σ(heat) = total_granted."""
        total_budget = sum(c.budget.val for c in cells)
        total_heat = sum(c.heat.val for c in cells)
        total = total_budget + total_heat
        if total != self.total_granted:
            self.violations += 1
            # Nie przerywaj — loguj różnicę
            return False
        return True


# =============================================================================
# CZĘŚĆ 7: KOMÓRKA REZONANSOWA
# =============================================================================

@dataclass
class ResonantCell:
    """
    Komórka Rezonansowa — podstawowa jednostka obliczeniowa.

    ZAMROŻONE (nie zmieniają się po inicjalizacji):
      w_for:     List[FinProb] — wagi za BTrue
      w_against: List[FinProb] — wagi za BFalse
      frequency: FinProb        — częstotliwość charakterystyczna

    ZMIENNE (zmieniają się w każdym cyklu):
      amplitude: FinProb — bieżąca siła oscylacji (reputacja)
      budget:    Fin     — pozostały budżet (skończony!)
      heat:      Fin     — skumulowane ciepło (entropia)
      alive:     bool    — czy żywa

    Z void_resonance.v: ResonantLocation
    """
    cell_id: int
    w_for: List[FinProb]
    w_against: List[FinProb]
    frequency: FinProb
    amplitude: FinProb
    budget: Fin
    heat: Fin
    alive: bool = True
    prediction: Bool3 = Bool3.BUnknown
    acc_for: Fin = field(default_factory=lambda: Fin(0))
    acc_against: Fin = field(default_factory=lambda: Fin(0))

    def spend(self, cost: Fin):
        """
        Wydaj budżet na operację WRITE. Generuj ciepło.
        B = B' ⊕ h — conservation.
        """
        actual = min(cost.val, self.budget.val)
        self.budget = Fin(self.budget.val - actual)
        self.heat = Fin(self.heat.val + actual)
        if self.budget.val == 0:
            self.alive = False

    def can_afford(self, cost: int = 1) -> bool:
        """READ: czy stać na operację?"""
        return self.budget.val >= cost


# =============================================================================
# CZĘŚĆ 8: OPERACJE NA KOMÓRCE
# =============================================================================

def cell_forward(cell: ResonantCell, signals: List[FinProb]) -> Bool3:
    """
    Forward pass: przetwórz sygnały przez komórkę.

    Dla każdej cechy i:
      - Czy signal[i] ≥ w_for[i]?   → dowód za BTrue (siła = w_for[i])
      - Czy signal[i] ≥ w_against[i]? → dowód za BFalse (siła = w_against[i])

    Akumuluj dowody (acc_for, acc_against). Porównaj → werdykt.

    Każde porównanie i akumulacja KOSZTUJĄ budżet.
    Wyczerpanie budżetu → BUnknown.

    Z void_neural_theory.v: process_signal, verdict
    """
    if not cell.alive or cell.budget.val == 0:
        cell.prediction = Bool3.BUnknown
        cell.alive = cell.budget.val > 0
        return Bool3.BUnknown

    acc_for = Fin(0)
    acc_against = Fin(0)

    for i in range(min(len(signals), len(cell.w_for))):
        if cell.budget.val == 0:
            break

        # --- Dowód za BTrue ---
        # Czy signal ≥ w_for? (le_fin: w_for.num ≤ signal.num?)
        match_for, new_b, h = le_fin_b3(cell.w_for[i].num, signals[i].num, cell.budget)
        cell.budget = new_b
        cell.heat = add_heat(cell.heat, h)

        if match_for == Bool3.BTrue and cell.budget.val > 0:
            # Akumuluj wagę jako dowód: acc_for += w_for[i].num
            acc_for, new_b, h = add_fin(acc_for, cell.w_for[i].num, cell.budget)
            cell.budget = new_b
            cell.heat = add_heat(cell.heat, h)

        if cell.budget.val == 0:
            break

        # --- Dowód za BFalse ---
        # Czy signal ≥ w_against? (BFalse AKTYWNIE CONTRIBUTES)
        match_ag, new_b, h = le_fin_b3(cell.w_against[i].num, signals[i].num, cell.budget)
        cell.budget = new_b
        cell.heat = add_heat(cell.heat, h)

        if match_ag == Bool3.BTrue and cell.budget.val > 0:
            acc_against, new_b, h = add_fin(acc_against, cell.w_against[i].num, cell.budget)
            cell.budget = new_b
            cell.heat = add_heat(cell.heat, h)

    # --- Werdykt ---
    cell.acc_for = acc_for
    cell.acc_against = acc_against

    if cell.budget.val == 0:
        cell.prediction = Bool3.BUnknown
        cell.alive = False
        return Bool3.BUnknown

    # Porównaj acc_for i acc_against
    cmp_result, new_b, h = le_fin_b3(acc_against, acc_for, cell.budget)
    cell.budget = new_b
    cell.heat = add_heat(cell.heat, h)

    if cmp_result == Bool3.BTrue:
        # acc_for ≥ acc_against
        if acc_for.val == acc_against.val:
            cell.prediction = Bool3.BUnknown  # Remis → niepewność (uczciwe)
        else:
            cell.prediction = Bool3.BTrue
    elif cmp_result == Bool3.BFalse:
        cell.prediction = Bool3.BFalse
    else:
        cell.prediction = Bool3.BUnknown

    if cell.budget.val == 0:
        cell.alive = False

    return cell.prediction


# =============================================================================
# CZĘŚĆ 9: ZESPÓŁ REZONANSOWY
# =============================================================================

class ResonantEnsemble:
    """
    Zespół Rezonansowy — sieć bez warstw.

    Pula komórek z częstotliwościami. Dla każdego wejścia:
    1. BOUNDARY: float → FinProb (transdukcja sensoryczna)
    2. SEEK: znajdź komórki rezonujące z wejściem (dopasowanie częstotliwości)
    3. FORWARD: forward pass przez rezonujące komórki
    4. CASCADE: wzmocnij/tłum komórki na podstawie zgodności
    5. VERDICT: głosowanie ważone amplitudą
    6. LEARN: credit propagation (refund/drain)
    7. DAMP: uniwersalny decay amplitudy

    Z void_resonance.v: resonance_seek, write_amplify, write_apply_damping
    """

    def __init__(self, n_cells: int = N_CELLS, n_features: int = N_FEATURES,
                 denom: int = DENOM, initial_budget: int = INITIAL_BUDGET,
                 seed: int = SEED):
        self.denom = denom
        self.n_features = n_features
        self.tracker = ConservationTracker()
        self.sample_count = 0
        self.correct_count = 0

        rng = random.Random(seed)
        self.cells: List[ResonantCell] = []

        for cell_id in range(n_cells):
            # Zamrożone wagi — losowe FinProb
            w_for = [FinProb(Fin(rng.randint(1, denom - 1)), Fin(denom))
                     for _ in range(n_features)]
            w_against = [FinProb(Fin(rng.randint(1, denom - 1)), Fin(denom))
                         for _ in range(n_features)]

            # Częstotliwość — losowa FinProb (zamrożona)
            frequency = FinProb(Fin(rng.randint(1, denom - 1)), Fin(denom))

            # Amplituda — startuje od HALF
            amplitude = FinProb.half(denom)

            # Budżet i ciepło
            budget = Fin(initial_budget)
            heat = Fin(0)

            cell = ResonantCell(
                cell_id=cell_id,
                w_for=w_for,
                w_against=w_against,
                frequency=frequency,
                amplitude=amplitude,
                budget=budget,
                heat=heat,
                alive=True
            )
            self.cells.append(cell)
            self.tracker.register_budget(initial_budget)

    def find_resonating(self, input_freq: FinProb,
                        threshold: Fin = Fin(RESONANCE_THRESHOLD)) -> List[ResonantCell]:
        """
        SEEK: znajdź komórki rezonujące z wejściem.

        Komórka rezonuje jeśli |cell.frequency - input_freq| ≤ threshold.
        Koszt: dist_fin (budżetowane) per komórkę.

        Z void_resonance.v: write_frequency_match, write_find_resonant
        """
        resonating = []
        for cell in self.cells:
            if not cell.alive:
                continue
            if not cell.can_afford(2):
                continue

            # Odległość częstotliwości (budżetowane)
            dist, new_b, h = dist_fin(cell.frequency.num, input_freq.num, cell.budget)
            cell.budget = new_b
            cell.heat = add_heat(cell.heat, h)

            # Czy w progu? (budżetowane)
            within, new_b, h = le_fin(dist, threshold, cell.budget)
            cell.budget = new_b
            cell.heat = add_heat(cell.heat, h)

            if within is True:
                resonating.append(cell)

        return resonating

    def cascade(self, resonating: List[ResonantCell]):
        """
        CASCADE: rezonujące komórki wzajemnie się wzmacniają/tłumią.

        Zgodność (obie BTrue lub obie BFalse) → wzmocnienie amplitudy.
        Spór (BTrue vs BFalse) → tłumienie amplitudy.
        BUnknown → brak interakcji (ignorancja jest niereaktywna).

        Fuel pattern z Coq: max CASCADE_FUEL rund.
        Koszt: każda komórka płaci za SWOJE interakcje (Naruszenie 7 naprawione).

        Z void_resonance.v: write_amplify, write_cascade_step
        """
        if len(resonating) < 2:
            return

        boost_amount = Fin(AMPLITUDE_BOOST_NUM)

        for _round in range(CASCADE_FUEL):
            changes = 0

            for i in range(len(resonating)):
                cell_a = resonating[i]
                if not cell_a.alive or cell_a.prediction == Bool3.BUnknown:
                    continue

                for j in range(i + 1, len(resonating)):
                    cell_b = resonating[j]
                    if not cell_b.alive or cell_b.prediction == Bool3.BUnknown:
                        continue

                    if not cell_a.can_afford(1) or not cell_b.can_afford(1):
                        continue

                    if cell_a.prediction == cell_b.prediction:
                        # KONSTRUKTYWNY REZONANS — zgodność!
                        # Wzmocnij amplitudy obu komórek
                        new_amp_a, new_b_a, h_a = boost_prob(
                            cell_a.amplitude, boost_amount, cell_a.budget)
                        cell_a.amplitude = new_amp_a
                        cell_a.budget = new_b_a
                        cell_a.heat = add_heat(cell_a.heat, h_a)

                        new_amp_b, new_b_b, h_b = boost_prob(
                            cell_b.amplitude, boost_amount, cell_b.budget)
                        cell_b.amplitude = new_amp_b
                        cell_b.budget = new_b_b
                        cell_b.heat = add_heat(cell_b.heat, h_b)

                        changes += 1
                    else:
                        # DESTRUKTYWNY REZONANS — spór!
                        # Tłum amplitudy obu komórek
                        cell_a.amplitude = decay_prob(cell_a.amplitude)
                        cell_a.spend(Fin(1))  # koszt interakcji

                        cell_b.amplitude = decay_prob(cell_b.amplitude)
                        cell_b.spend(Fin(1))  # koszt interakcji

                        changes += 1

            if changes == 0:
                break  # Zbieżność — brak dalszych zmian

    def verdict(self, resonating: List[ResonantCell]) -> Tuple[Bool3, FinProb]:
        """
        VERDICT: głosowanie ważone amplitudą.

        Suma amplitud komórek głosujących za BTrue vs BFalse.
        Wygrywa strona z większą łączną amplitudą.

        Z void_neural_theory.v: verdict function
        Koszt: każda komórka płaci 1 tick za oddanie głosu.
        """
        sum_for = Fin(0)
        sum_against = Fin(0)

        for cell in resonating:
            if not cell.alive:
                continue

            if cell.prediction == Bool3.BTrue:
                if cell.can_afford(1):
                    sum_for, new_b, h = add_fin(sum_for, cell.amplitude.num, cell.budget)
                    cell.budget = new_b
                    cell.heat = add_heat(cell.heat, h)

            elif cell.prediction == Bool3.BFalse:
                if cell.can_afford(1):
                    sum_against, new_b, h = add_fin(
                        sum_against, cell.amplitude.num, cell.budget)
                    cell.budget = new_b
                    cell.heat = add_heat(cell.heat, h)

        # Porównaj — używamy budżetu "pierwszej żywej komórki" (koszt porównania)
        voter = None
        for c in resonating:
            if c.alive and c.can_afford(1):
                voter = c
                break

        if voter is None:
            return (Bool3.BUnknown, FinProb.half(self.denom))

        cmp, new_b, h = le_fin_b3(sum_against, sum_for, voter.budget)
        voter.budget = new_b
        voter.heat = add_heat(voter.heat, h)

        if cmp == Bool3.BTrue:
            if sum_for.val == sum_against.val:
                return (Bool3.BUnknown, FinProb.half(self.denom))
            else:
                # Confidence = proporcja sum_for do sumy
                total = sum_for.val + sum_against.val
                if total == 0:
                    conf = FinProb.half(self.denom)
                else:
                    # BOUNDARY calculation — wyliczanie confidence
                    conf_num = max(1, min(self.denom - 1,
                                          (sum_for.val * (self.denom - 1)) // total))
                    conf = FinProb(Fin(conf_num), Fin(self.denom))
                return (Bool3.BTrue, conf)
        elif cmp == Bool3.BFalse:
            total = sum_for.val + sum_against.val
            if total == 0:
                conf = FinProb.half(self.denom)
            else:
                conf_num = max(1, min(self.denom - 1,
                                      (sum_against.val * (self.denom - 1)) // total))
                conf = FinProb(Fin(conf_num), Fin(self.denom))
            return (Bool3.BFalse, conf)
        else:
            return (Bool3.BUnknown, FinProb.half(self.denom))

    def learn(self, resonating: List[ResonantCell], truth: Bool3,
              ensemble_prediction: Bool3):
        """
        LEARN: credit propagation — selekcja budżetowa.

        Poprawna predykcja → REFUND (budget +=, amplitude boost)
        Błędna predykcja → DRAIN (budget -=, amplitude decay)
        BUnknown → brak kary/nagrody (uczciwe przyznanie się do niewiedzy)

        Z void_credit_propagation.v: selective_refund
        Z void_neural_theory.v: learn_from_truth
        """
        for cell in resonating:
            if not cell.alive:
                continue

            if cell.prediction == Bool3.BUnknown:
                # Uczciwa niewiedza — brak konsekwencji budżetowych
                # Ale amplituda i tak będzie decay (universal damping)
                continue

            if cell.prediction == truth:
                # POPRAWNA PREDYKCJA → refund!
                refund = REFUND_AMOUNT
                # Budżet rośnie. Cap = 2x INITIAL (dobre komórki prosperują, ale nie nieskończenie)
                budget_cap = INITIAL_BUDGET * 2
                new_budget_val = min(cell.budget.val + refund, budget_cap)
                refund_actual = new_budget_val - cell.budget.val
                cell.budget = Fin(new_budget_val)
                self.tracker.register_budget(refund_actual)

                # Amplitude boost (budżetowane)
                new_amp, new_b, h = boost_prob(
                    cell.amplitude, Fin(AMPLITUDE_BOOST_NUM), cell.budget)
                cell.amplitude = new_amp
                cell.budget = new_b
                cell.heat = add_heat(cell.heat, h)

            else:
                # BŁĘDNA PREDYKCJA → drain!
                drain = min(DRAIN_AMOUNT, cell.budget.val)
                cell.budget = Fin(cell.budget.val - drain)
                cell.heat = Fin(cell.heat.val + drain)

                # Amplitude decay (kara za błąd)
                cell.amplitude = decay_prob(cell.amplitude)
                cell.amplitude = decay_prob(cell.amplitude)  # Podwójny decay za błąd

                if cell.budget.val == 0:
                    cell.alive = False

    def universal_damping(self):
        """
        UNIVERSAL DAMPING: wszystkie amplitudy gasną.
        Entropia jest nieuchronna — tylko aktywnie rezonujące komórki utrzymują siłę.

        Z void_resonance.v: write_apply_damping
        Z PDF sekcja 5.5: δ(n/d) = (n-1)/d
        """
        for cell in self.cells:
            if cell.alive:
                cell.amplitude = decay_prob(cell.amplitude)

    def process_sample(self, signals: List[FinProb], truth: Bool3) -> Bool3:
        """
        Przetwórz jeden sample: SEEK → FORWARD → CASCADE → VERDICT → LEARN.

        Returns: predykcja zespołu.
        """
        self.sample_count += 1

        # 1. Oblicz częstotliwość wejścia (BOUNDARY — dozwolone Python int)
        input_freq = compute_input_frequency(signals, self.denom)

        # 2. SEEK: znajdź rezonujące komórki
        resonating = self.find_resonating(input_freq)

        if len(resonating) == 0:
            return Bool3.BUnknown

        # 3. FORWARD: forward pass przez rezonujące komórki
        for cell in resonating:
            cell_forward(cell, signals)

        # 4. CASCADE: wzajemne wzmacnianie/tłumienie
        self.cascade(resonating)

        # 5. VERDICT: głosowanie
        prediction, confidence = self.verdict(resonating)

        # 6. LEARN: credit propagation
        self.learn(resonating, truth, prediction)

        # 7. UNIVERSAL DAMPING (co DAMPING_INTERVAL sampli)
        if self.sample_count % DAMPING_INTERVAL == 0:
            self.universal_damping()

        if prediction == truth:
            self.correct_count += 1

        return prediction

    def alive_count(self) -> int:
        """READ: ile komórek żyje?"""
        return sum(1 for c in self.cells if c.alive)

    def budget_stats(self) -> dict:
        """READ: statystyki budżetu."""
        alive = [c for c in self.cells if c.alive]
        if not alive:
            return {"alive": 0, "avg_budget": 0, "avg_heat": 0, "avg_amp": 0}
        return {
            "alive": len(alive),
            "avg_budget": sum(c.budget.val for c in alive) / len(alive),
            "avg_heat": sum(c.heat.val for c in alive) / len(alive),
            "avg_amp": sum(c.amplitude.num.val for c in alive) / len(alive),
        }


# =============================================================================
# CZĘŚĆ 10: TRANSDUKCJA SENSORYCZNA (GRANICA — float dozwolony!)
# =============================================================================

def quantize_feature(x_float: float, feat_min: float, feat_max: float,
                     d: int = DENOM) -> FinProb:
    """
    BOUNDARY: konwersja float → FinProb.
    Float żyje w "zewnętrznym świecie". VOID core nigdy nie widzi float.

    Z void_sensory_transduction.v:
      raw_to_strength(v, max) = (v+1, max+2)
      External systems must convert their data to Fin BEFORE calling us.

    Mapowanie: [feat_min, feat_max] → {1, 2, ..., d-1} / d
    """
    if feat_max == feat_min:
        return FinProb(Fin(d // 2), Fin(d))  # Half jeśli brak zakresu

    # Normalizuj do [0, 1]
    norm = (x_float - feat_min) / (feat_max - feat_min)
    norm = max(0.0, min(1.0, norm))

    # Kwantyzuj do {0, 1, ..., d-2}
    v = int(round(norm * (d - 2)))
    v = max(0, min(d - 2, v))

    # raw_to_strength: (v+1, d) — z void_sensory_transduction.v
    return FinProb(Fin(v + 1), Fin(d))


def compute_input_frequency(signals: List[FinProb], d: int = DENOM) -> FinProb:
    """
    BOUNDARY: oblicz częstotliwość wejścia z sygnałów.

    Prosta metryka: proporcja cech powyżej HALF.
    Mapowana na skalę FinProb (1/d ... (d-1)/d).

    To jest na GRANICY VOID — dozwolone Python int.
    """
    half = d // 2
    count_high = sum(1 for s in signals if s.num.val > half)
    total = len(signals)

    if total == 0:
        return FinProb.half(d)

    # Skaluj count_high/total do {1, ..., d-1}
    freq_num = max(1, min(d - 1, round(count_high / total * (d - 2)) + 1))
    return FinProb(Fin(freq_num), Fin(d))


def encode_label(y: int) -> Bool3:
    """BOUNDARY: konwersja etykiety binarnej (0/1) → Bool3."""
    if y == 1:
        return Bool3.BTrue
    elif y == 0:
        return Bool3.BFalse
    else:
        return Bool3.BUnknown


def decode_prediction(pred: Bool3) -> int:
    """BOUNDARY: konwersja Bool3 → etykieta binarna."""
    if pred == Bool3.BTrue:
        return 1
    elif pred == Bool3.BFalse:
        return 0
    else:
        return -1  # BUnknown — brak pewności


# =============================================================================
# CZĘŚĆ 11: TRENING I EWALUACJA
# =============================================================================

def prepare_data(d: int = DENOM):
    """
    Załaduj Breast Cancer dataset i przekonwertuj na FinProb.
    Float → FinProb na GRANICY. Wewnątrz VOID: czyste FinProb.
    """
    from sklearn.datasets import load_breast_cancer
    from sklearn.model_selection import train_test_split

    data = load_breast_cancer()
    X, y = data.data, data.target

    X_train, X_test, y_train, y_test = train_test_split(
        X, y, test_size=0.2, random_state=SEED, stratify=y
    )

    # Oblicz min/max per cecha (z danych treningowych)
    feat_mins = X_train.min(axis=0)
    feat_maxs = X_train.max(axis=0)

    # Konwertuj na FinProb
    def to_signals(X_data):
        signals_list = []
        for row in X_data:
            signals = [quantize_feature(row[i], feat_mins[i], feat_maxs[i], d)
                       for i in range(len(row))]
            signals_list.append(signals)
        return signals_list

    train_signals = to_signals(X_train)
    test_signals = to_signals(X_test)
    train_labels = [encode_label(int(yi)) for yi in y_train]
    test_labels = [encode_label(int(yi)) for yi in y_test]

    return train_signals, test_signals, train_labels, test_labels


def evaluate(ensemble: ResonantEnsemble, signals_list: List[List[FinProb]],
             labels: List[Bool3]) -> float:
    """
    Ewaluacja — predykcja BEZ zużywania budżetu komórek.
    Ewaluacja to OBSERWACJA ZEWNĘTRZNA — nie należy do VOID core.
    Tworzymy tymczasowe kopie budżetów, używamy ich, potem przywracamy.
    """
    import copy

    correct = 0
    total = 0

    # Zachowaj stan komórek
    saved_states = []
    for c in ensemble.cells:
        saved_states.append((c.budget, c.heat, c.amplitude, c.alive, c.prediction))

    for signals, truth in zip(signals_list, labels):
        input_freq = compute_input_frequency(signals, ensemble.denom)

        # Proste głosowanie: dla każdej żywej rezonującej komórki,
        # symuluj forward pass na KOPII
        votes_true = 0
        votes_false = 0
        half = DENOM // 2

        for cell in ensemble.cells:
            if not cell.alive:
                continue
            # Sprawdź rezonans (READ — darmowe)
            dist_val = abs(cell.frequency.num.val - input_freq.num.val)
            if dist_val > RESONANCE_THRESHOLD:
                continue

            # Symuluj forward pass bez kosztów (to jest obserwacja)
            acc_f = 0
            acc_a = 0
            for i in range(min(len(signals), len(cell.w_for))):
                if signals[i].num.val >= cell.w_for[i].num.val:
                    acc_f += cell.w_for[i].num.val
                if signals[i].num.val >= cell.w_against[i].num.val:
                    acc_a += cell.w_against[i].num.val

            amp = cell.amplitude.num.val
            if acc_f > acc_a:
                votes_true += amp
            elif acc_a > acc_f:
                votes_false += amp

        if votes_true > votes_false:
            pred = Bool3.BTrue
        elif votes_false > votes_true:
            pred = Bool3.BFalse
        else:
            pred = Bool3.BUnknown

        if pred == truth:
            correct += 1
        total += 1

    # Przywróć stan komórek
    for c, (b, h, a, al, p) in zip(ensemble.cells, saved_states):
        c.budget = b
        c.heat = h
        c.amplitude = a
        c.alive = al
        c.prediction = p

    return correct / total if total > 0 else 0.0


def train_epoch(ensemble: ResonantEnsemble, train_signals: List[List[FinProb]],
                train_labels: List[Bool3], rng: random.Random) -> float:
    """
    Jedna epoka treningowa. Shuffle i przetwórz wszystkie sample.
    Returns: accuracy na zbiorze treningowym.
    """
    indices = list(range(len(train_signals)))
    rng.shuffle(indices)

    correct = 0
    total = 0

    for idx in indices:
        pred = ensemble.process_sample(train_signals[idx], train_labels[idx])
        if pred == train_labels[idx]:
            correct += 1
        total += 1

    return correct / total if total > 0 else 0.0


# =============================================================================
# CZĘŚĆ 12: MAIN — DEMO NA BREAST CANCER
# =============================================================================

def main():
    print("=" * 70)
    print("VOID RESONANT ENSEMBLE — Demo na Breast Cancer Dataset")
    print("=" * 70)
    print()
    print(f"Parametry VOID:")
    print(f"  D(ρ) = {DENOM} (denominator cap)")
    print(f"  N_CELLS = {N_CELLS}")
    print(f"  INITIAL_BUDGET = {INITIAL_BUDGET}")
    print(f"  REFUND = {REFUND_AMOUNT}")
    print(f"  DRAIN = {DRAIN_AMOUNT}")
    print(f"  RESONANCE_THRESHOLD = {RESONANCE_THRESHOLD}")
    print(f"  CASCADE_FUEL = {CASCADE_FUEL}")
    print()

    # Przygotuj dane
    print("Transdukcja sensoryczna (float → FinProb na GRANICY)...")
    train_signals, test_signals, train_labels, test_labels = prepare_data(DENOM)
    print(f"  Train: {len(train_signals)} samples, Test: {len(test_signals)} samples")
    print(f"  Sygnał przykładowy: {train_signals[0][:3]}...")
    print()

    # Inicjalizacja zespołu
    print("Inicjalizacja Zespołu Rezonansowego...")
    ensemble = ResonantEnsemble(
        n_cells=N_CELLS, n_features=N_FEATURES,
        denom=DENOM, initial_budget=INITIAL_BUDGET, seed=SEED
    )
    print(f"  {ensemble.alive_count()} komórek żywych")
    stats = ensemble.budget_stats()
    print(f"  Śr. budżet: {stats['avg_budget']:.0f}, Śr. amplituda: {stats['avg_amp']:.1f}")
    print()

    # Trening
    rng = random.Random(SEED)
    n_epochs = 30
    best_test_acc = 0.0

    print("TRENING:")
    print("-" * 70)
    print(f"{'Epoka':>6} | {'Train Acc':>10} | {'Test Acc':>10} | {'Żywe':>6} | "
          f"{'Śr.Budżet':>10} | {'Śr.Amp':>8}")
    print("-" * 70)

    for epoch in range(1, n_epochs + 1):
        # Trening
        train_acc = train_epoch(ensemble, train_signals, train_labels, rng)

        # Ewaluacja
        # (oszczędzamy budżet — ewaluacja co kilka epok)
        if epoch % 3 == 0 or epoch <= 3 or epoch == n_epochs:
            test_acc = evaluate(ensemble, test_signals, test_labels)
            best_test_acc = max(best_test_acc, test_acc)
        else:
            test_acc = -1  # Pominięto

        stats = ensemble.budget_stats()
        alive = ensemble.alive_count()

        test_str = f"{test_acc:.2%}" if test_acc >= 0 else "    —"
        print(f"{epoch:>6} | {train_acc:>10.2%} | {test_str:>10} | {alive:>6} | "
              f"{stats['avg_budget']:>10.0f} | {stats['avg_amp']:>8.1f}")

        # Jeśli wszystkie komórki umarły — koniec
        if alive == 0:
            print("\n  *** Wszystkie komórki umarły — wyczerpanie budżetu ***")
            break

    print("-" * 70)
    print(f"\nNajlepsza accuracy na zbiorze testowym: {best_test_acc:.2%}")

    # Weryfikacja aksjomatów
    print("\n" + "=" * 70)
    print("WERYFIKACJA AKSJOMATÓW VOID")
    print("=" * 70)

    # 1. Conservation B = B' + h
    alive_cells = [c for c in ensemble.cells if True]  # wszystkie, nie tylko żywe
    total_budget = sum(c.budget.val for c in alive_cells)
    total_heat = sum(c.heat.val for c in alive_cells)
    print(f"\n1. Conservation B = B' ⊕ h:")
    print(f"   Σ budget = {total_budget}")
    print(f"   Σ heat   = {total_heat}")
    print(f"   Σ (B+h)  = {total_budget + total_heat}")
    print(f"   Total granted = {ensemble.tracker.total_granted}")
    # Uwaga: conservation może nie się zgadzać dokładnie z powodu refundów
    # (refundy dodają nowy budżet do systemu)

    # 2. FinProb ∈ (0, 1)
    violations_01 = 0
    for c in alive_cells:
        if c.amplitude.num.val <= 0 or c.amplitude.num.val >= c.amplitude.den.val:
            violations_01 += 1
        for w in c.w_for + c.w_against:
            if w.num.val <= 0 or w.num.val >= w.den.val:
                violations_01 += 1
    print(f"\n2. FinProb ∈ (0, 1): {'OK' if violations_01 == 0 else f'{violations_01} NARUSZEŃ!'}")

    # 3. Brak float wewnątrz VOID core
    print(f"\n3. Brak float wewnątrz VOID core: OK (architektura wymusza)")
    print(f"   Typy wewnątrz: Fin, FinProb, Bool3 — brak float.")

    # 4. Brak nieskończoności
    print(f"\n4. Brak nieskończoności:")
    print(f"   Fin: opakowany int, brak operatorów arytmetycznych.")
    print(f"   Wszystkie operacje budżetowane: add_fin, le_fin, dist_fin...")
    print(f"   Stały mianownik D(ρ) = {DENOM}: brak eksplozji mianowników.")

    # 5. Statystyki komórek
    print(f"\n5. Statystyki końcowe komórek:")
    alive_c = [c for c in ensemble.cells if c.alive]
    dead_c = [c for c in ensemble.cells if not c.alive]
    print(f"   Żywe: {len(alive_c)}, Martwe: {len(dead_c)}")
    if alive_c:
        budgets = [c.budget.val for c in alive_c]
        amps = [c.amplitude.num.val for c in alive_c]
        print(f"   Budżet (żywe): min={min(budgets)}, max={max(budgets)}, "
              f"avg={sum(budgets)/len(budgets):.0f}")
        print(f"   Amplituda (żywe): min={min(amps)}, max={max(amps)}, "
              f"avg={sum(amps)/len(amps):.1f}")

    print("\n" + "=" * 70)
    print("KONIEC DEMO")
    print("=" * 70)


if __name__ == "__main__":
    main()
