"""Train VoidCloud on multiple datasets, export topology data as JSON for visualization."""
import json
import random
import copy
import sys
sys.path.insert(0, '/sessions/laughing-hopeful-bohr/mnt/void-theory')
import void_cloud as vc
from sklearn.datasets import load_breast_cancer, load_wine, load_iris, load_digits
import numpy as np

def train_and_export(X, y, dataset_name, class_names, n_neurons=64, k=8, n_ticks=3,
                     n_epochs=80, lr=5, seed=42):
    """Train VoidCloud and export topology + metrics."""
    random.seed(seed)
    feature_mins = X.min(axis=0)
    feature_maxs = X.max(axis=0)
    n_features = X.shape[1]

    neurons = vc.init_cloud(n_features, n_neurons, k)

    # Save initial topology
    init_positions = [(n.pos_x, n.pos_y) for n in neurons]
    init_connections = [(n.nid, list(n.neighbor_ids)) for n in neurons]

    best_neurons = copy.deepcopy(neurons)
    best_score = -999999

    epoch_snapshots = []

    for epoch in range(n_epochs):
        correct, wrong, unknown = 0, 0, 0
        indices = list(range(len(X)))
        random.shuffle(indices)

        for idx in indices:
            signals = vc.encode_features(X[idx], feature_mins, feature_maxs)
            truth = bool(y[idx])
            decision = vc.train_step(neurons, signals, truth, n_ticks, lr)
            if decision is None: unknown += 1
            elif decision == truth: correct += 1
            else: wrong += 1

        score = correct * 10 - wrong * 30
        if score > best_score:
            best_score = score
            best_neurons = copy.deepcopy(neurons)

        if epoch % 10 == 0 and epoch >= 20:
            vc._connect_neighbors(neurons, k, preserve_weights=True)

        if epoch % 5 == 0 or epoch == n_epochs - 1:
            epoch_snapshots.append({
                "epoch": epoch,
                "correct": correct,
                "wrong": wrong,
                "unknown": unknown,
            })

    # Final evaluation with best checkpoint
    preds = vc.predict_cloud(best_neurons, X, feature_mins, feature_maxs, n_ticks)
    correct = sum(1 for i, (d, _) in enumerate(preds) if d == bool(y[i]))
    wrong = sum(1 for i, (d, _) in enumerate(preds) if d is not None and d != bool(y[i]))
    unknown = sum(1 for d, _ in preds if d is None)
    answered = correct + wrong
    ca = (correct * 1000) // answered if answered > 0 else 0
    cov = (answered * 100) // len(X)

    # Export neuron data from best checkpoint
    neuron_data = []
    for n in best_neurons:
        activity = n.state - vc.S_DENOM // 2
        neuron_data.append({
            "id": n.nid,
            "x": n.pos_x,
            "y": n.pos_y,
            "neighbors": list(n.neighbor_ids),
            "state": n.state,
            "activity": activity,
            "correct": n.correct_count,
            "wrong": n.wrong_count,
            "is_output": n.is_output,
            "amplitude": n.amplitude_n,
            "n_features": len(n.input_mask),
            "feature_mask": list(n.input_mask),
        })

    # Initial positions for animation
    init_data = []
    for i, (px, py) in enumerate(init_positions):
        init_data.append({"id": i, "x": px, "y": py})

    return {
        "name": dataset_name,
        "class_names": class_names,
        "n_samples": len(X),
        "n_features": n_features,
        "n_neurons": n_neurons,
        "k_neighbors": k,
        "n_ticks": n_ticks,
        "metrics": {
            "correct": correct,
            "wrong": wrong,
            "unknown": unknown,
            "coverage_pct": cov,
            "cond_accuracy_permille": ca,
        },
        "neurons": neuron_data,
        "initial_positions": init_data,
        "training_history": epoch_snapshots,
    }


# ============================================================
# Dataset 1: Breast Cancer (binary, 569 samples, 30 features)
# ============================================================
print("Training on Breast Cancer...")
bc = load_breast_cancer()
result_bc = train_and_export(bc.data, bc.target, "Breast Cancer Wisconsin",
                             ["Malignant", "Benign"],
                             n_neurons=64, k=8, n_ticks=3, n_epochs=80, lr=5)
print(f"  → {result_bc['metrics']}")

# ============================================================
# Dataset 2: Wine (binary: class 0 vs rest, 178 samples, 13 features)
# ============================================================
print("Training on Wine...")
wine = load_wine()
y_wine = (wine.target == 0).astype(int)  # class 0 vs rest
result_wine = train_and_export(wine.data, y_wine, "Wine Quality",
                               ["Other", "Class 0"],
                               n_neurons=48, k=6, n_ticks=3, n_epochs=80, lr=5)
print(f"  → {result_wine['metrics']}")

# ============================================================
# Dataset 3: Iris (binary: setosa vs rest, 150 samples, 4 features)
# ============================================================
print("Training on Iris...")
iris = load_iris()
y_iris = (iris.target == 0).astype(int)  # setosa vs rest
result_iris = train_and_export(iris.data, y_iris, "Iris (Setosa vs Rest)",
                               ["Non-Setosa", "Setosa"],
                               n_neurons=32, k=6, n_ticks=3, n_epochs=60, lr=5)
print(f"  → {result_iris['metrics']}")

# ============================================================
# Dataset 4: Digits 0 vs 1 (binary, ~360 samples, 64 features)
# ============================================================
print("Training on Digits 0v1...")
digits = load_digits()
mask = (digits.target == 0) | (digits.target == 1)
X_dig = digits.data[mask]
y_dig = digits.target[mask]
result_digits = train_and_export(X_dig, y_dig, "Digits (0 vs 1)",
                                  ["Digit 0", "Digit 1"],
                                  n_neurons=64, k=8, n_ticks=3, n_epochs=80, lr=5)
print(f"  → {result_digits['metrics']}")

# ============================================================
# Save all
# ============================================================
all_data = {
    "datasets": [result_bc, result_wine, result_iris, result_digits],
    "model_info": {
        "name": "VoidCloud v3",
        "description": "Graph-based neural network, no layers, self-organizing topology",
        "W_DENOM": vc.W_DENOM,
        "S_DENOM": vc.S_DENOM,
        "POS_SCALE": vc.POS_SCALE,
        "FOR_THRESH": vc.FOR_THRESH_N,
        "AG_THRESH": vc.AG_THRESH_N,
    }
}

with open('/sessions/laughing-hopeful-bohr/mnt/void-theory/void_cloud_viz_data.json', 'w') as f:
    json.dump(all_data, f)

print("\nAll data exported to void_cloud_viz_data.json")
for d in all_data["datasets"]:
    m = d["metrics"]
    print(f"  {d['name']:<30s}: {m['cond_accuracy_permille']}‰ ca, {m['coverage_pct']}% cov, "
          f"{m['correct']}/{m['wrong']}/{m['unknown']}")
