"""
Resonant Ensemble — VOID neural network implementation.
64 cells with frozen weights, thermodynamic selection.
Trains on Wisconsin Breast Cancer, outputs cell topology as JSON for visualization.

NO FLOATS in VOID logic. Only integers and FinProb(n, d).
Floats ONLY in preprocessing (encode_features, compute_mi_ranking) — boundary with external world.
"""
import json
import random
from dataclasses import dataclass, field
from typing import List, Tuple, Optional

# ============================================================
# FinProb — rational probability (numerator, denominator)
# ALL comparisons via cross-multiplication. NO val(). NO floats.
# ============================================================
@dataclass
class FinProb:
    n: int
    d: int
    def __repr__(self):
        return f"{self.n}/{self.d}"

ZERO = FinProb(0, 1)
HALF = FinProb(1, 2)
DENOM = 16  # weight precision

def fp(n, d):
    return FinProb(n, d)

# a > b  ↔  a.n * b.d > b.n * a.d
def fp_gt(a: FinProb, b: FinProb) -> bool:
    return a.n * b.d > b.n * a.d

# a < b
def fp_lt(a: FinProb, b: FinProb) -> bool:
    return a.n * b.d < b.n * a.d

# a >= b
def fp_ge(a: FinProb, b: FinProb) -> bool:
    return a.n * b.d >= b.n * a.d

# a <= b
def fp_le(a: FinProb, b: FinProb) -> bool:
    return a.n * b.d <= b.n * a.d

# a == b
def fp_eq(a: FinProb, b: FinProb) -> bool:
    return a.n * b.d == b.n * a.d

# |a - b| <= threshold  (all FinProb, all integer)
# |a.n/a.d - b.n/b.d| <= t.n/t.d
# |a.n * b.d - b.n * a.d| * t.d <= t.n * a.d * b.d
def fp_dist_le(a: FinProb, b: FinProb, threshold: FinProb) -> bool:
    diff = abs(a.n * b.d - b.n * a.d)
    return diff * threshold.d <= threshold.n * a.d * b.d

# ============================================================
# ResonantCell
# ============================================================
@dataclass
class ResonantCell:
    cell_id: int
    cell_group: str
    # FROZEN (epistemology)
    w_for: List[FinProb] = field(default_factory=list)
    w_against: List[FinProb] = field(default_factory=list)
    frequency: FinProb = field(default_factory=lambda: HALF)
    # VARIABLE (thermodynamics)
    amplitude: FinProb = field(default_factory=lambda: FinProb(500, 1000))
    budget: int = 2000000
    heat: int = 0
    # tracking
    correct_count: int = 0
    wrong_count: int = 0
    activation_count: int = 0

def init_cells(n_features: int, mi_ranking: List[int]) -> List[ResonantCell]:
    """Committee of Experts: 64 cells.
    Each cell watches 1 feature with a specific threshold and polarity.
    8 top features × 4 thresholds × 2 polarities = 64 cells.

    Encoding in w_for/w_against:
    - Watched feature i: w_for[i].n = threshold (1-15), w_against[i].n = 15 (flag)
    - Other features: w_for[i].n = 0, w_against[i].n = 0 (ignored)
    - Polarity: stored in cell_group name ("POS" = high→FOR, "NEG" = high→AGAINST)
    """
    cells = []
    cell_id = 0

    # 8 top MI features, 4 threshold levels, 2 polarities
    top_features = mi_ranking[:8]
    thresholds = [3, 6, 10, 13]  # spread across [0, DENOM]

    for feat_idx in top_features:
        for thr in thresholds:
            for polarity in ("POS", "NEG"):
                w_for = []
                w_against = []
                for fi in range(n_features):
                    if fi == feat_idx:
                        # w_for.n = threshold, w_against.n = 15 (watched flag)
                        w_for.append(FinProb(thr, DENOM))
                        w_against.append(FinProb(15, DENOM))
                    else:
                        w_for.append(FinProb(0, DENOM))
                        w_against.append(FinProb(0, DENOM))

                cells.append(ResonantCell(
                    cell_id=cell_id,
                    cell_group=polarity,
                    w_for=w_for, w_against=w_against,
                    frequency=HALF,
                ))
                cell_id += 1

    return cells

# ============================================================
# Forward pass
# ============================================================
def input_frequency(signals: List[FinProb], n_features: int) -> FinProb:
    """Compute input frequency — pure integer.
    weighted_center = sum(i * s.n) / (sum(s.n) * n_features)
    Result as FinProb with shared denominator."""
    weighted_sum = 0  # integer
    total_weight = 0  # integer
    for i, s in enumerate(signals):
        weighted_sum += i * s.n
        total_weight += s.n
    if total_weight == 0:
        return HALF
    # center = weighted_sum / (total_weight * n_features)
    # FinProb: n = weighted_sum, d = total_weight * n_features
    # Clamp to [1, d-1]
    d = total_weight * n_features
    n = max(1, min(d - 1, weighted_sum))
    return FinProb(n, d)

RESONANCE_THRESHOLD = FinProb(1, 2)  # 0.5 — all cells active

def is_resonant(cell: ResonantCell, inp_freq: FinProb) -> bool:
    return fp_dist_le(cell.frequency, inp_freq, RESONANCE_THRESHOLD)

def activate_cell(cell: ResonantCell, signals: List[FinProb]) -> Tuple[FinProb, int]:
    """Threshold activation — pure integer.
    For each watched feature (w_against[i].n > 0):
      threshold = w_for[i].n
      if signal > threshold: high = True
      if signal < threshold: high = False
    POS polarity: high → FOR (output > 50). NEG polarity: high → AGAINST (output < 50).
    Confidence scales with distance from threshold."""
    heat = 1  # cost of activation

    for i, s in enumerate(signals):
        if cell.w_against[i].n == 0:
            continue  # not watching this feature
        # Found watched feature
        threshold = cell.w_for[i].n
        distance = s.n - threshold  # signed: positive = above threshold

        if distance == 0:
            return FinProb(50, 100), heat  # exactly at threshold = neutral

        # Confidence: |distance| out of max possible (DENOM)
        # Output: 50 ± (49 * |distance|) // DENOM
        shift = (49 * abs(distance)) // DENOM

        if cell.cell_group == "POS":
            # high signal → FOR (output > 50)
            if distance > 0:
                out_n = 50 + shift
            else:
                out_n = 50 - shift
        else:  # NEG
            # high signal → AGAINST (output < 50)
            if distance > 0:
                out_n = 50 - shift
            else:
                out_n = 50 + shift

        out_n = max(1, min(99, out_n))
        return FinProb(out_n, 100), heat

    # No watched feature found (shouldn't happen)
    return FinProb(50, 100), heat

# ============================================================
# Resonance cascade
# ============================================================
def resonance_cascade(active_cells, outputs, max_rounds=3):
    for _ in range(max_rounds):
        changes = 0
        for i in range(len(active_cells)):
            for j in range(i + 1, len(active_cells)):
                ca, cb = active_cells[i], active_cells[j]
                if ca.budget <= 0 or cb.budget <= 0:
                    continue
                oa = outputs[ca.cell_id]
                ob = outputs[cb.cell_id]
                # a_yes: output > 1/2  ↔  n * 2 > d
                a_yes = oa.n * 2 > oa.d
                b_yes = ob.n * 2 > ob.d
                ca.budget -= 1; ca.heat += 1

                if a_yes == b_yes:
                    if ca.amplitude.n < ca.amplitude.d - 1:
                        ca.amplitude = FinProb(ca.amplitude.n + 1, ca.amplitude.d)
                    if cb.amplitude.n < cb.amplitude.d - 1:
                        cb.amplitude = FinProb(cb.amplitude.n + 1, cb.amplitude.d)
                    ca.budget -= 1; ca.heat += 1
                    changes += 1
                else:
                    if ca.amplitude.n > 1:
                        ca.amplitude = FinProb(ca.amplitude.n - 1, ca.amplitude.d)
                    if cb.amplitude.n > 1:
                        cb.amplitude = FinProb(cb.amplitude.n - 1, cb.amplitude.d)
                    changes += 1
        if changes == 0:
            break

# ============================================================
# Verdict — pure integer
# ============================================================
# Thresholds as FinProb for integer comparison
AMP_MIN = FinProb(1, 20)     # 0.05
OUT_FOR = FinProb(55, 100)   # 0.55
OUT_AG = FinProb(45, 100)    # 0.45
OUT_HALF = FinProb(1, 2)     # 0.5

def verdict(active_cells, outputs) -> Tuple[Optional[bool], FinProb]:
    """Pure integer verdict. Returns (decision, confidence_as_FinProb)."""
    # Filter voters: amplitude > AMP_MIN
    voters = []
    for c in active_cells:
        if fp_gt(c.amplitude, AMP_MIN):
            if c.cell_id in outputs:
                voters.append((c, outputs[c.cell_id]))
    if not voters:
        return None, ZERO

    # Weight = amplitude.n * |2*out.n - out.d|
    # (all amplitudes share denominator 1000, all outputs share denominator 100,
    #  so integer weights are comparable)
    w_for = 0   # integer accumulator
    w_against = 0

    for cell, out in voters:
        confidence = abs(2 * out.n - out.d)  # 0 at 0.5, max at 0 or 1
        weight = cell.amplitude.n * confidence
        # out > 55/100  ↔  out.n * 100 > 55 * out.d
        if out.n * 100 > 55 * out.d:
            w_for += weight
        # out < 45/100  ↔  out.n * 100 < 45 * out.d
        elif out.n * 100 < 45 * out.d:
            w_against += weight

    total = w_for + w_against
    if total == 0:
        return None, ZERO
    if w_for > w_against:
        return True, FinProb(w_for, total)
    elif w_against > w_for:
        return False, FinProb(w_against, total)
    else:
        return None, ZERO

# ============================================================
# Learning — pure integer
# ============================================================
REFUND = 50

def _cell_says_yes(out: FinProb) -> bool:
    """out > 1/2  ↔  out.n * 2 > out.d"""
    return out.n * 2 > out.d

def _cell_is_neutral(out: FinProb) -> bool:
    """45/100 <= out <= 55/100
    ↔  out.n * 100 >= 45 * out.d  AND  out.n * 100 <= 55 * out.d"""
    cross = out.n * 100
    return cross >= 45 * out.d and cross <= 55 * out.d

def credit_propagation(cell, cell_output, truth_bool):
    if _cell_is_neutral(cell_output):
        return
    if _cell_says_yes(cell_output) == truth_bool:
        cell.budget += REFUND
        cell.correct_count += 1
    else:
        cell.wrong_count += 1

def amplitude_credit(cell, cell_output, truth_bool):
    if _cell_is_neutral(cell_output):
        return
    # Confidence: how far from neutral (0 to 49 on 100-scale output)
    confidence = abs(2 * cell_output.n - cell_output.d)  # 0 at 0.5, 100 at edges

    if _cell_says_yes(cell_output) == truth_bool:
        # Correct: small reward, bigger if barely correct (good discrimination)
        # confidence close to 0 → good discrimination → reward 10
        # confidence high → obvious → reward 1
        reward = max(1, 10 - (confidence // 10))
        new_n = min(cell.amplitude.d - 1, cell.amplitude.n + reward)
    else:
        # Wrong: penalty scales with confidence (confident + wrong = catastrophic)
        # confidence 0 → barely wrong → penalty 5
        # confidence 100 → confidently wrong → penalty 50
        penalty = 5 + (confidence // 2)
        new_n = max(1, cell.amplitude.n - penalty)

    if new_n != cell.amplitude.n:
        cell.amplitude = FinProb(new_n, cell.amplitude.d)
        cell.budget -= 1
        cell.heat += 1

def universal_damping(cells):
    for cell in cells:
        total = cell.correct_count + cell.wrong_count
        # accuracy < 1/2  ↔  correct_count * 2 < total
        if total > 10 and cell.correct_count * 2 < total:
            if cell.budget > 0 and cell.amplitude.n > 1:
                cell.amplitude = FinProb(cell.amplitude.n - 1, cell.amplitude.d)
                cell.budget -= 1
                cell.heat += 1

# ============================================================
# Encode features as FinProb
# (PREPROCESSING — boundary with external world. Floats allowed here.)
# ============================================================
def encode_features(X_row, feature_mins, feature_maxs) -> List[FinProb]:
    signals = []
    for i, val in enumerate(X_row):
        rng = feature_maxs[i] - feature_mins[i]
        if rng == 0:
            signals.append(HALF)
        else:
            normalized = (val - feature_mins[i]) / rng
            n = max(0, min(DENOM, int(normalized * DENOM)))
            signals.append(FinProb(n, DENOM))
    return signals

# ============================================================
# MI ranking (PREPROCESSING — floats allowed)
# ============================================================
def compute_mi_ranking(X, y):
    scores = []
    for feat_idx in range(X.shape[1]):
        corr = abs(sum((X[:, feat_idx] - X[:, feat_idx].mean()) *
                       (y - y.mean())) / len(y))
        scores.append((corr, feat_idx))
    scores.sort(reverse=True)
    return [idx for _, idx in scores]

# ============================================================
# Train
# ============================================================
AMP_HIGH = FinProb(1, 4)       # 0.25
AMP_INFLUENTIAL = FinProb(1, 8) # 0.125

def train(X, y, feature_names, n_epochs=25):
    random.seed(42)
    feature_mins = X.min(axis=0)
    feature_maxs = X.max(axis=0)
    n_features = X.shape[1]

    mi_ranking = compute_mi_ranking(X, y)
    cells = init_cells(n_features, mi_ranking)

    epoch_stats = []

    for epoch in range(n_epochs):
        correct_total = 0
        unknown_total = 0
        total = 0

        indices = list(range(len(X)))
        random.shuffle(indices)

        for idx in indices:
            signals = encode_features(X[idx], feature_mins, feature_maxs)
            truth = bool(y[idx])
            inp_freq = input_frequency(signals, n_features)

            active = [c for c in cells if is_resonant(c, inp_freq) and c.budget > 0]
            if not active:
                unknown_total += 1
                total += 1
                continue

            outputs = {}
            for cell in active:
                out, h = activate_cell(cell, signals)
                outputs[cell.cell_id] = out
                cell.budget -= h
                cell.heat += h
                cell.activation_count += 1

            decision, confidence = verdict(active, outputs)

            for cell in active:
                if cell.cell_id in outputs:
                    credit_propagation(cell, outputs[cell.cell_id], truth)
                    amplitude_credit(cell, outputs[cell.cell_id], truth)

            total += 1
            if decision == truth:
                correct_total += 1
            elif decision is None:
                unknown_total += 1

        universal_damping(cells)

        alive = sum(1 for c in cells if c.budget > 0)
        # high_amp: amplitude > 1/4  ↔  n * 4 > d
        high_amp = sum(1 for c in cells if c.amplitude.n * 4 > c.amplitude.d)
        acc_n = correct_total
        acc_d = max(1, total)
        epoch_stats.append({
            "epoch": epoch,
            "accuracy_n": acc_n,
            "accuracy_d": acc_d,
            "alive": alive,
            "high_amp": high_amp,
            "unknown": unknown_total,
        })
        # Print uses integer fraction
        pct = (acc_n * 1000) // acc_d  # integer per-mille
        print(f"Epoch {epoch:2d}: acc={acc_n}/{acc_d} ({pct}‰) alive={alive} high_amp={high_amp} unknown={unknown_total}")

    # Build output — store n/d pairs, NOT floats
    cell_data = []
    for c in cells:
        total_decisions = c.correct_count + c.wrong_count
        cell_data.append({
            "id": c.cell_id,
            "group": c.cell_group,
            "frequency_n": c.frequency.n,
            "frequency_d": c.frequency.d,
            "amplitude_n": c.amplitude.n,
            "amplitude_d": c.amplitude.d,
            "budget": c.budget,
            "heat": c.heat,
            "alive": c.budget > 0,
            # influential: amplitude > 1/8  ↔  n * 8 > d
            "influential": c.budget > 0 and c.amplitude.n * 8 > c.amplitude.d,
            "correct": c.correct_count,
            "wrong": c.wrong_count,
            "activations": c.activation_count,
            "accuracy_n": c.correct_count,
            "accuracy_d": max(1, total_decisions),
            # w_for / w_against as n values (denominator is always DENOM)
            "w_for_n": [w.n for w in c.w_for],
            "w_against_n": [w.n for w in c.w_against],
            "w_denom": DENOM,
        })

    return {
        "cells": cell_data,
        "epochs": epoch_stats,
        "feature_names": list(feature_names),
        "mi_ranking": mi_ranking,
    }

# ============================================================
# Main
# ============================================================
if __name__ == "__main__":
    from sklearn.datasets import load_breast_cancer
    data = load_breast_cancer()
    X, y = data.data, data.target

    result = train(X, y, data.feature_names, n_epochs=25)

    with open("/sessions/laughing-hopeful-bohr/ensemble_data.json", "w") as f:
        json.dump(result, f, indent=2)

    print(f"\nSurviving: {sum(1 for c in result['cells'] if c['alive'])}/64")
    print(f"Influential: {sum(1 for c in result['cells'] if c['influential'])}/64")
    print(f"Data saved to ensemble_data.json")
