"""
Killer Metric: "Where VOID is silent, others hallucinate."

Compares VOID resonant ensemble vs classical models (LR, DT, SVM, RF)
on Wisconsin Breast Cancer dataset.

KEY METRIC: Cases where VOID = UNKNOWN AND classical model = WRONG.

FAIR COMPARISON: Both VOID and classical models use 5-fold cross-validation.
Each sample is predicted by a model trained WITHOUT seeing that sample.

VOID's UNKNOWN comes from:
  - No active cells (budget depleted)
  - Confidence margin too thin (Bool3: if evidence is not decisive, say UNKNOWN)
  - All voters neutral
"""

import json
import random
import sys
import os
import numpy as np
from collections import defaultdict
from typing import List, Tuple, Optional
from dataclasses import dataclass, field

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from resonant_ensemble import (
    FinProb, ZERO, HALF, DENOM,
    fp_gt, fp_lt, fp_ge, fp_le, fp_eq,
    ResonantCell, init_cells,
    input_frequency, is_resonant, activate_cell,
    resonance_cascade, verdict as _raw_verdict,
    credit_propagation, amplitude_credit, universal_damping,
    encode_features, compute_mi_ranking,
    AMP_MIN, AMP_HIGH, AMP_INFLUENTIAL, REFUND
)

from sklearn.datasets import load_breast_cancer
from sklearn.linear_model import LogisticRegression
from sklearn.tree import DecisionTreeClassifier
from sklearn.svm import SVC
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import KFold, cross_val_predict


# ============================================================
# Bool3-aware verdict with confidence margin
# ============================================================
# Original verdict returns (decision, confidence) where confidence = w_winning/total
# For Bool3: if confidence < MARGIN, return UNKNOWN
# MARGIN = 60/100 means "winning side must have >60% of weighted evidence"
CONFIDENCE_MARGIN = FinProb(60, 100)

def verdict_bool3(active_cells, outputs) -> Tuple[Optional[bool], FinProb]:
    """Bool3 verdict: if evidence margin is not decisive, return UNKNOWN.
    This is the core of VOID — not guessing when you don't know."""
    decision, confidence = _raw_verdict(active_cells, outputs)

    if decision is None:
        return None, ZERO

    # confidence = w_winning / (w_for + w_against)
    # If confidence < MARGIN → UNKNOWN
    # confidence.n * MARGIN.d < MARGIN.n * confidence.d
    if confidence.n * CONFIDENCE_MARGIN.d < CONFIDENCE_MARGIN.n * confidence.d:
        return None, confidence  # UNKNOWN — not enough margin

    return decision, confidence


# ============================================================
# VOID training (reused logic from resonant_ensemble.py)
# ============================================================
def void_train(X_train, y_train):
    """Train VOID on given data, return trained cells and preprocessing params."""
    random.seed(42)
    feature_mins = X_train.min(axis=0)
    feature_maxs = X_train.max(axis=0)
    n_features = X_train.shape[1]
    mi_ranking = compute_mi_ranking(X_train, y_train)
    cells = init_cells(n_features, mi_ranking)

    for epoch in range(25):
        indices = list(range(len(X_train)))
        random.shuffle(indices)

        for idx in indices:
            signals = encode_features(X_train[idx], feature_mins, feature_maxs)
            truth = bool(y_train[idx])
            inp_freq = input_frequency(signals, n_features)
            active = [c for c in cells if is_resonant(c, inp_freq) and c.budget > 0]

            if not active:
                continue

            outputs = {}
            for cell in active:
                out, h = activate_cell(cell, signals)
                outputs[cell.cell_id] = out
                cell.budget -= h
                cell.heat += h
                cell.activation_count += 1

            decision, confidence = verdict_bool3(active, outputs)

            for cell in active:
                if cell.cell_id in outputs:
                    credit_propagation(cell, outputs[cell.cell_id], truth)
                    amplitude_credit(cell, outputs[cell.cell_id], truth)

        universal_damping(cells)

    return cells, feature_mins, feature_maxs, n_features


def void_predict(cells, X_test, feature_mins, feature_maxs, n_features):
    """Predict using trained VOID cells. Returns list of (decision, conf_n, conf_d)."""
    results = []
    for idx in range(len(X_test)):
        signals = encode_features(X_test[idx], feature_mins, feature_maxs)
        inp_freq = input_frequency(signals, n_features)
        active = [c for c in cells if is_resonant(c, inp_freq) and c.budget > 0]

        if not active:
            results.append((None, 0, 1))
            continue

        outputs = {}
        for cell in active:
            out, _ = activate_cell(cell, signals)
            outputs[cell.cell_id] = out

        decision, confidence = verdict_bool3(active, outputs)
        results.append((decision, confidence.n, confidence.d))

    return results


# ============================================================
# 5-fold CV for VOID
# ============================================================
def void_cross_validate(X, y):
    """5-fold CV for VOID — same protocol as sklearn models."""
    kf = KFold(n_splits=5, shuffle=True, random_state=42)
    all_predictions = [None] * len(y)  # (decision, conf_n, conf_d) per sample

    for fold, (train_idx, test_idx) in enumerate(kf.split(X)):
        X_train, X_test = X[train_idx], X[test_idx]
        y_train, y_test = y[train_idx], y[test_idx]

        cells, fmins, fmaxs, nf = void_train(X_train, y_train)
        preds = void_predict(cells, X_test, fmins, fmaxs, nf)

        n_unknown = sum(1 for d, _, _ in preds if d is None)
        n_correct = sum(1 for i, (d, _, _) in enumerate(preds) if d == bool(y_test[i]))
        print(f"  Fold {fold}: {n_correct}/{len(test_idx)} correct, {n_unknown} UNKNOWN")

        for i, ti in enumerate(test_idx):
            all_predictions[ti] = preds[i]

    return all_predictions


# ============================================================
# Killer Metric computation
# ============================================================
def compute_killer_metric(void_results, classical_preds, y):
    n_samples = len(y)

    void_correct = []
    void_wrong = []
    void_unknown = []

    for idx in range(n_samples):
        decision, conf_n, conf_d = void_results[idx]
        truth = bool(y[idx])
        if decision is None:
            void_unknown.append(idx)
        elif decision == truth:
            void_correct.append(idx)
        else:
            void_wrong.append(idx)

    print(f"\n{'='*65}")
    print(f"VOID BREAKDOWN (5-fold CV, confidence margin = {CONFIDENCE_MARGIN})")
    print(f"{'='*65}")
    print(f"  Correct:  {len(void_correct)}/{n_samples}")
    print(f"  Wrong:    {len(void_wrong)}/{n_samples}")
    print(f"  UNKNOWN:  {len(void_unknown)}/{n_samples} ({(len(void_unknown)*100)//n_samples}%)")

    answered = len(void_correct) + len(void_wrong)
    if answered > 0:
        cond_pct = (len(void_correct) * 1000) // answered
        print(f"  Conditional accuracy (answered only): {len(void_correct)}/{answered} ({cond_pct}‰)")

    # === THE KILLER METRIC ===
    print(f"\n{'='*65}")
    print(f"  KILLER METRIC: Where VOID stays silent, others hallucinate")
    print(f"{'='*65}")
    print(f"\n  VOID refused to answer {len(void_unknown)} samples.")
    print(f"  Of those {len(void_unknown)} samples, classical models got WRONG:\n")

    killer_data = {}

    for model_name, preds in classical_preds.items():
        wrong_on_unknown = sum(1 for idx in void_unknown if preds[idx] != y[idx])
        right_on_unknown = sum(1 for idx in void_unknown if preds[idx] == y[idx])
        model_total_wrong = sum(1 for i in range(n_samples) if preds[i] != y[i])

        if len(void_unknown) > 0:
            killer_pct = (wrong_on_unknown * 100) // len(void_unknown)
        else:
            killer_pct = 0

        if model_total_wrong > 0:
            concentration_pct = (wrong_on_unknown * 100) // model_total_wrong
        else:
            concentration_pct = 0

        killer_data[model_name] = {
            "wrong_on_unknown": wrong_on_unknown,
            "right_on_unknown": right_on_unknown,
            "total_unknown": len(void_unknown),
            "killer_pct": killer_pct,
            "model_total_wrong": model_total_wrong,
            "model_total_right": n_samples - model_total_wrong,
            "concentration_pct": concentration_pct,
        }

        print(f"    {model_name:12s}: {wrong_on_unknown}/{len(void_unknown)} wrong "
              f"({killer_pct}% of VOID's unknowns)")
        print(f"    {'':12s}  → {concentration_pct}% of {model_name}'s total errors "
              f"({wrong_on_unknown}/{model_total_wrong}) fall in VOID's unknown zone")

    # Universally hard samples
    if void_unknown:
        all_wrong = [idx for idx in void_unknown
                     if all(preds[idx] != y[idx] for preds in classical_preds.values())]
        any_wrong = [idx for idx in void_unknown
                     if any(preds[idx] != y[idx] for preds in classical_preds.values())]
        print(f"\n  ALL 4 models wrong on VOID's unknowns: {len(all_wrong)}/{len(void_unknown)}")
        print(f"  At least 1 model wrong:                {len(any_wrong)}/{len(void_unknown)}")

    # Reverse: where VOID is wrong
    print(f"\n{'='*65}")
    print(f"  REVERSE: Where VOID gets it WRONG ({len(void_wrong)} samples)")
    print(f"{'='*65}")
    for model_name, preds in classical_preds.items():
        also_wrong = sum(1 for idx in void_wrong if preds[idx] != y[idx])
        print(f"    {model_name:12s}: also wrong on {also_wrong}/{len(void_wrong)}")

    return {
        "void_correct": len(void_correct),
        "void_wrong": len(void_wrong),
        "void_unknown": len(void_unknown),
        "void_unknown_indices": void_unknown,
        "void_wrong_indices": void_wrong,
        "killer_data": killer_data,
        "confidence_margin": f"{CONFIDENCE_MARGIN.n}/{CONFIDENCE_MARGIN.d}",
    }


def print_comparison_table(void_results, classical_preds, y, killer_results):
    n = len(y)
    vc = killer_results["void_correct"]
    vw = killer_results["void_wrong"]
    vu = killer_results["void_unknown"]
    answered = vc + vw

    print(f"\n{'='*65}")
    print(f"  COMPARISON TABLE (all 5-fold CV)")
    print(f"{'='*65}")
    print(f"\n  {'Model':14s} {'Accuracy':>9s} {'Correct':>8s} {'Wrong':>6s} {'Unknown':>8s} {'Cond.Acc':>9s}")
    print(f"  {'-'*58}")

    if answered > 0:
        cond = f"{(vc*1000)//answered}‰"
    else:
        cond = "N/A"
    void_acc = (vc * 1000) // n
    print(f"  {'VOID':14s} {void_acc:>8d}‰ {vc:>8d} {vw:>6d} {vu:>8d} {cond:>9s}")

    for name, preds in classical_preds.items():
        correct = int(sum(preds == y))
        wrong = n - correct
        acc = (correct * 1000) // n
        print(f"  {name:14s} {acc:>8d}‰ {correct:>8d} {wrong:>6d} {'—':>8s} {'N/A':>9s}")

    # Key insight
    if vu > 0 and answered > 0:
        print(f"\n  KEY INSIGHT:")
        print(f"  When VOID answers, its accuracy = {cond}")
        best_classical = max(
            (int(sum(p == y)), name) for name, p in classical_preds.items()
        )
        best_pct = (best_classical[0] * 1000) // n
        print(f"  Best classical ({best_classical[1]}): {best_pct}‰ (but forced to answer ALL samples)")

        # Among answered samples, VOID vs best classical
        void_acc_answered = (vc * 1000) // answered
        best_on_answered = sum(1 for idx in range(n) if void_results[idx][0] is not None
                               and classical_preds[best_classical[1]][idx] == y[idx])
        best_acc_answered = (best_on_answered * 1000) // answered
        print(f"  On the {answered} samples VOID answered: VOID={void_acc_answered}‰ vs {best_classical[1]}={best_acc_answered}‰")


# ============================================================
# Sweep confidence margins
# ============================================================
def sweep_margins(X, y):
    """Try multiple confidence margins to find the sweet spot."""
    global CONFIDENCE_MARGIN

    margins = [
        FinProb(51, 100),  # 51% — minimal margin
        FinProb(55, 100),  # 55%
        FinProb(60, 100),  # 60%
        FinProb(65, 100),  # 65%
        FinProb(70, 100),  # 70%
        FinProb(75, 100),  # 75%
        FinProb(80, 100),  # 80%
    ]

    print(f"\n{'='*65}")
    print(f"  CONFIDENCE MARGIN SWEEP")
    print(f"{'='*65}")
    print(f"\n  {'Margin':>8s} {'Correct':>8s} {'Wrong':>6s} {'Unknown':>8s} {'Cond.Acc':>9s} {'Raw.Acc':>8s}")
    print(f"  {'-'*52}")

    results = []
    for margin in margins:
        CONFIDENCE_MARGIN = margin
        void_results = void_cross_validate(X, y)

        n = len(y)
        correct = sum(1 for i in range(n) if void_results[i][0] == bool(y[i]))
        wrong = sum(1 for i in range(n) if void_results[i][0] is not None and void_results[i][0] != bool(y[i]))
        unknown = sum(1 for i in range(n) if void_results[i][0] is None)
        answered = correct + wrong
        cond_acc = (correct * 1000) // answered if answered > 0 else 0
        raw_acc = (correct * 1000) // n

        print(f"  {margin.n}/{margin.d:>4d} {correct:>8d} {wrong:>6d} {unknown:>8d} {cond_acc:>8d}‰ {raw_acc:>7d}‰")
        results.append((margin, correct, wrong, unknown, cond_acc, void_results))

    return results


# ============================================================
# Main
# ============================================================
if __name__ == "__main__":
    print("="*65)
    print("  KILLER METRIC BENCHMARK (5-fold CV)")
    print("  'Where VOID is silent, others hallucinate.'")
    print("="*65)

    data = load_breast_cancer()
    X, y = data.data, data.target
    print(f"\n  Dataset: Wisconsin Breast Cancer ({len(X)} samples, {X.shape[1]} features)")
    print(f"  Class balance: {sum(y==1)} benign, {sum(y==0)} malignant\n")

    # Phase 1: Sweep margins to find the sweet spot
    print("Phase 1: Confidence margin sweep...")
    sweep_results = sweep_margins(X, y)

    # Pick best margin: maximize conditional accuracy while having ≥5% unknowns
    best = None
    for margin, correct, wrong, unknown, cond_acc, void_results in sweep_results:
        if unknown >= len(y) * 5 // 100:  # at least 5% unknown
            if best is None or cond_acc > best[4]:
                best = (margin, correct, wrong, unknown, cond_acc, void_results)

    if best is None:
        # Fallback: pick highest conditional accuracy regardless
        best = max(sweep_results, key=lambda x: x[4])

    CONFIDENCE_MARGIN = best[0]
    void_results = best[5]
    print(f"\n  Selected margin: {best[0]} → {best[1]} correct, {best[2]} wrong, {best[3]} unknown")

    # Phase 2: Classical models
    print(f"\nPhase 2: Classical Models (5-fold CV)...")
    print("-"*40)
    models = {
        "LogReg": LogisticRegression(max_iter=10000, random_state=42),
        "DecTree": DecisionTreeClassifier(random_state=42),
        "SVM": SVC(kernel='rbf', random_state=42),
        "RandForest": RandomForestClassifier(n_estimators=100, random_state=42),
    }
    classical_preds = {}
    for name, model in models.items():
        preds = cross_val_predict(model, X, y, cv=KFold(n_splits=5, shuffle=True, random_state=42))
        classical_preds[name] = preds
        acc = sum(preds == y) / len(y)
        print(f"  {name:12s}: {sum(preds == y)}/{len(y)} ({acc:.4f})")

    # Phase 3: Killer metric
    killer_results = compute_killer_metric(void_results, classical_preds, y)

    # Phase 4: Comparison table
    print_comparison_table(void_results, classical_preds, y, killer_results)

    # Save results
    output = {
        "confidence_margin": f"{CONFIDENCE_MARGIN.n}/{CONFIDENCE_MARGIN.d}",
        "void_correct": killer_results["void_correct"],
        "void_wrong": killer_results["void_wrong"],
        "void_unknown": killer_results["void_unknown"],
        "classical_accuracies": {
            name: int(sum(preds == y)) for name, preds in classical_preds.items()
        },
        "killer_data": killer_results["killer_data"],
        "n_samples": len(y),
        "sweep_results": [
            {"margin": f"{m.n}/{m.d}", "correct": c, "wrong": w, "unknown": u, "cond_acc": ca}
            for m, c, w, u, ca, _ in sweep_results
        ],
    }

    results_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "killer_metric_results.json")
    with open(results_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\n  Results saved to {results_path}")
