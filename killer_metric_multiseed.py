"""
Multi-seed Killer Metric experiment.
Runs the full 5-fold CV comparison 5 times with different seeds.
Reports mean ± std for all key metrics.
"""

import json
import random
import sys
import os
import numpy as np
from typing import List, Tuple, Optional
from scipy.stats import fisher_exact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from resonant_ensemble import (
    FinProb, ZERO, HALF, DENOM,
    fp_gt, ResonantCell, init_cells,
    input_frequency, is_resonant, activate_cell,
    verdict as _raw_verdict,
    credit_propagation, amplitude_credit, universal_damping,
    encode_features, compute_mi_ranking,
    AMP_MIN,
)

from sklearn.datasets import load_breast_cancer
from sklearn.linear_model import LogisticRegression
from sklearn.tree import DecisionTreeClassifier
from sklearn.svm import SVC
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import KFold, cross_val_predict

CONFIDENCE_MARGIN = FinProb(80, 100)

def verdict_bool3(active_cells, outputs):
    decision, confidence = _raw_verdict(active_cells, outputs)
    if decision is None:
        return None, ZERO
    if confidence.n * CONFIDENCE_MARGIN.d < CONFIDENCE_MARGIN.n * confidence.d:
        return None, confidence
    return decision, confidence


def void_train(X_train, y_train, seed):
    random.seed(seed)
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


def run_single_seed(X, y, seed):
    """Run full experiment with one seed. Returns all metrics."""
    kf = KFold(n_splits=5, shuffle=True, random_state=seed)

    # VOID 5-fold CV
    void_preds = [None] * len(y)
    for train_idx, test_idx in kf.split(X):
        cells, fmins, fmaxs, nf = void_train(X[train_idx], y[train_idx], seed)
        preds = void_predict(cells, X[test_idx], fmins, fmaxs, nf)
        for i, ti in enumerate(test_idx):
            void_preds[ti] = preds[i]

    # Classical models (same fold structure)
    models = {
        "LogReg": LogisticRegression(max_iter=10000, random_state=seed),
        "DecTree": DecisionTreeClassifier(random_state=seed),
        "SVM": SVC(kernel='rbf', random_state=seed),
        "RandForest": RandomForestClassifier(n_estimators=100, random_state=seed),
    }
    classical_preds = {}
    for name, model in models.items():
        preds = cross_val_predict(model, X, y, cv=KFold(n_splits=5, shuffle=True, random_state=seed))
        classical_preds[name] = preds

    # Compute metrics
    n = len(y)
    void_correct = sum(1 for i in range(n) if void_preds[i][0] == bool(y[i]))
    void_wrong = sum(1 for i in range(n) if void_preds[i][0] is not None and void_preds[i][0] != bool(y[i]))
    void_unknown = sum(1 for i in range(n) if void_preds[i][0] is None)
    void_unknown_idx = [i for i in range(n) if void_preds[i][0] is None]
    answered = void_correct + void_wrong
    cond_acc = void_correct / answered if answered > 0 else 0
    raw_acc = void_correct / n

    result = {
        "seed": seed,
        "void_correct": void_correct,
        "void_wrong": void_wrong,
        "void_unknown": void_unknown,
        "void_cond_acc": cond_acc,
        "void_raw_acc": raw_acc,
        "classical": {},
        "enrichment": {},
    }

    va = n - void_unknown  # answered count

    for name, preds in classical_preds.items():
        model_correct = int(sum(preds == y))
        model_wrong = n - model_correct
        model_acc = model_correct / n

        wrong_on_unknown = sum(1 for idx in void_unknown_idx if preds[idx] != y[idx])
        right_on_unknown = sum(1 for idx in void_unknown_idx if preds[idx] == y[idx])
        wrong_outside = model_wrong - wrong_on_unknown
        right_outside = (n - model_wrong) - right_on_unknown

        err_unknown = wrong_on_unknown / void_unknown if void_unknown > 0 else 0
        err_answered = wrong_outside / va if va > 0 else 0
        enrichment = err_unknown / err_answered if err_answered > 0 else float('inf')

        # Fisher exact
        table = [[wrong_on_unknown, wrong_outside],
                 [right_on_unknown, right_outside]]
        odds, pval = fisher_exact(table, alternative='greater')

        # Concentration: % of model errors in unknown zone
        concentration = wrong_on_unknown / model_wrong if model_wrong > 0 else 0

        result["classical"][name] = {
            "accuracy": model_acc,
            "correct": model_correct,
            "wrong": model_wrong,
        }
        result["enrichment"][name] = {
            "wrong_on_unknown": wrong_on_unknown,
            "err_unknown": err_unknown,
            "err_answered": err_answered,
            "enrichment": enrichment,
            "concentration": concentration,
            "fisher_p": pval,
            "odds_ratio": odds,
        }

    return result


# ============================================================
# Also run margin sweep across seeds
# ============================================================
def margin_sweep_single_seed(X, y, seed):
    """Sweep confidence margins for one seed."""
    global CONFIDENCE_MARGIN
    margins = [FinProb(n, 100) for n in [51, 55, 60, 65, 70, 75, 80, 85, 90]]
    results = []
    kf = KFold(n_splits=5, shuffle=True, random_state=seed)

    for margin in margins:
        CONFIDENCE_MARGIN = margin
        void_preds = [None] * len(y)
        for train_idx, test_idx in kf.split(X):
            cells, fmins, fmaxs, nf = void_train(X[train_idx], y[train_idx], seed)
            preds = void_predict(cells, X[test_idx], fmins, fmaxs, nf)
            for i, ti in enumerate(test_idx):
                void_preds[ti] = preds[i]

        n = len(y)
        correct = sum(1 for i in range(n) if void_preds[i][0] == bool(y[i]))
        wrong = sum(1 for i in range(n) if void_preds[i][0] is not None and void_preds[i][0] != bool(y[i]))
        unknown = sum(1 for i in range(n) if void_preds[i][0] is None)
        answered = correct + wrong
        cond_acc = correct / answered if answered > 0 else 0

        results.append({
            "margin": margin.n,
            "correct": correct,
            "wrong": wrong,
            "unknown": unknown,
            "cond_acc": cond_acc,
            "raw_acc": correct / n,
            "unknown_pct": unknown / n,
        })

    CONFIDENCE_MARGIN = FinProb(80, 100)  # restore
    return results


# ============================================================
# Main
# ============================================================
if __name__ == "__main__":
    data = load_breast_cancer()
    X, y = data.data, data.target
    n = len(y)

    seeds = [42, 123, 456, 789, 2025]

    print("="*65)
    print("  MULTI-SEED KILLER METRIC EXPERIMENT")
    print(f"  Seeds: {seeds}")
    print(f"  Dataset: Wisconsin BC ({n} samples)")
    print(f"  Confidence margin: {CONFIDENCE_MARGIN}")
    print("="*65)

    all_results = []
    for i, seed in enumerate(seeds):
        print(f"\n--- Seed {seed} ({i+1}/{len(seeds)}) ---")
        result = run_single_seed(X, y, seed)
        all_results.append(result)
        print(f"  VOID: {result['void_correct']}/{n} correct, "
              f"{result['void_wrong']} wrong, {result['void_unknown']} unknown, "
              f"cond_acc={result['void_cond_acc']:.4f}")
        for name, enr in result["enrichment"].items():
            print(f"  {name}: enrichment={enr['enrichment']:.2f}x, p={enr['fisher_p']:.6f}")

    # Aggregate
    print(f"\n{'='*65}")
    print(f"  AGGREGATED RESULTS (mean ± std over {len(seeds)} seeds)")
    print(f"{'='*65}\n")

    # VOID stats
    void_cond_accs = [r["void_cond_acc"] for r in all_results]
    void_raw_accs = [r["void_raw_acc"] for r in all_results]
    void_unknowns = [r["void_unknown"] for r in all_results]
    void_wrongs = [r["void_wrong"] for r in all_results]

    print(f"  VOID conditional accuracy: {np.mean(void_cond_accs):.4f} ± {np.std(void_cond_accs):.4f}")
    print(f"  VOID raw accuracy:         {np.mean(void_raw_accs):.4f} ± {np.std(void_raw_accs):.4f}")
    print(f"  VOID unknowns:             {np.mean(void_unknowns):.1f} ± {np.std(void_unknowns):.1f}")
    print(f"  VOID wrong:                {np.mean(void_wrongs):.1f} ± {np.std(void_wrongs):.1f}")

    # Classical + enrichment
    model_names = list(all_results[0]["classical"].keys())
    for name in model_names:
        accs = [r["classical"][name]["accuracy"] for r in all_results]
        enrichments = [r["enrichment"][name]["enrichment"] for r in all_results]
        concentrations = [r["enrichment"][name]["concentration"] for r in all_results]
        pvals = [r["enrichment"][name]["fisher_p"] for r in all_results]

        print(f"\n  {name}:")
        print(f"    Accuracy:      {np.mean(accs):.4f} ± {np.std(accs):.4f}")
        print(f"    Enrichment:    {np.mean(enrichments):.2f}x ± {np.std(enrichments):.2f}")
        print(f"    Concentration: {np.mean(concentrations):.2%} ± {np.std(concentrations):.2%}")
        print(f"    Fisher p-vals: {['%.6f'%p for p in pvals]}")
        print(f"    All significant (p<0.05): {all(p < 0.05 for p in pvals)}")

    # Margin sweep (on seed 42 only — for the curve)
    print(f"\n{'='*65}")
    print(f"  CONFIDENCE MARGIN SWEEP (seed=42)")
    print(f"{'='*65}")
    sweep = margin_sweep_single_seed(X, y, 42)
    print(f"\n  {'Margin':>8s} {'Correct':>8s} {'Wrong':>6s} {'Unknown':>8s} {'Unk%':>6s} {'Cond.Acc':>9s} {'Raw.Acc':>8s}")
    print(f"  {'-'*56}")
    for s in sweep:
        print(f"  {s['margin']:>6d}% {s['correct']:>8d} {s['wrong']:>6d} {s['unknown']:>8d} "
              f"{s['unknown_pct']:>5.1%} {s['cond_acc']:>8.4f} {s['raw_acc']:>7.4f}")

    # Save everything
    output = {
        "experiment": "Multi-seed Killer Metric",
        "dataset": "Wisconsin Breast Cancer",
        "n_samples": n,
        "confidence_margin": "80/100",
        "seeds": seeds,
        "per_seed": all_results,
        "aggregated": {
            "void_cond_acc_mean": float(np.mean(void_cond_accs)),
            "void_cond_acc_std": float(np.std(void_cond_accs)),
            "void_raw_acc_mean": float(np.mean(void_raw_accs)),
            "void_raw_acc_std": float(np.std(void_raw_accs)),
            "void_unknown_mean": float(np.mean(void_unknowns)),
            "void_unknown_std": float(np.std(void_unknowns)),
            "void_wrong_mean": float(np.mean(void_wrongs)),
            "void_wrong_std": float(np.std(void_wrongs)),
        },
        "margin_sweep": sweep,
    }

    for name in model_names:
        accs = [r["classical"][name]["accuracy"] for r in all_results]
        enrichments = [r["enrichment"][name]["enrichment"] for r in all_results]
        concentrations = [r["enrichment"][name]["concentration"] for r in all_results]
        pvals = [r["enrichment"][name]["fisher_p"] for r in all_results]
        output["aggregated"][name] = {
            "acc_mean": float(np.mean(accs)),
            "acc_std": float(np.std(accs)),
            "enrichment_mean": float(np.mean(enrichments)),
            "enrichment_std": float(np.std(enrichments)),
            "concentration_mean": float(np.mean(concentrations)),
            "concentration_std": float(np.std(concentrations)),
            "fisher_pvals": [float(p) for p in pvals],
            "all_significant": bool(all(p < 0.05 for p in pvals)),
        }

    with open("killer_metric_multiseed.json", "w") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\n  Results saved to killer_metric_multiseed.json")
