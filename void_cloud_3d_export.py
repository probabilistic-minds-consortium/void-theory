"""Train VoidCloud (3D) on multiple datasets, export for Three.js visualization.
Includes tick-by-tick state history for signal propagation animation."""
import json, random, copy, sys
sys.path.insert(0, '/sessions/laughing-hopeful-bohr/mnt/void-theory')
import void_cloud as vc
from sklearn.datasets import load_breast_cancer, load_wine, load_iris, load_digits
import numpy as np

def train_and_export(X, y, dataset_name, class_names, n_neurons=64, k=8,
                     n_ticks=3, n_epochs=80, lr=5, seed=5):
    random.seed(seed)
    feature_mins = X.min(axis=0)
    feature_maxs = X.max(axis=0)
    n_features = X.shape[1]
    neurons = vc.init_cloud(n_features, n_neurons, k)

    # Save initial positions
    init_pos = [(n.pos_x, n.pos_y, n.pos_z) for n in neurons]

    best_neurons = copy.deepcopy(neurons)
    best_score = -999999
    history = []

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

        if epoch % rewire == 0 and epoch >= 20:
            vc._connect_neighbors(neurons, k, preserve_weights=True)

        if epoch % 5 == 0 or epoch == n_epochs - 1:
            history.append({"epoch": epoch, "correct": correct, "wrong": wrong, "unknown": unknown})

    # Get tick-by-tick propagation for samples: positive, negative, AND unknown
    sample_idx_pos = next(i for i in range(len(y)) if y[i] == 1)
    sample_idx_neg = next(i for i in range(len(y)) if y[i] == 0)

    # Find an UNKNOWN sample
    sample_idx_unk = None
    for sidx in range(len(X)):
        signals = vc.encode_features(X[sidx], feature_mins, feature_maxs)
        out_state, _, _ = vc.cloud_forward(best_neurons, signals, n_ticks)
        dec, _ = vc.verdict(out_state)
        if dec is None:
            sample_idx_unk = sidx
            break

    tick_snapshots = []
    samples = [("positive", sample_idx_pos), ("negative", sample_idx_neg)]
    if sample_idx_unk is not None:
        samples.append(("unknown", sample_idx_unk))

    for label, sidx in samples:
        signals = vc.encode_features(X[sidx], feature_mins, feature_maxs)
        out_state, tick_hist, _ = vc.cloud_forward(best_neurons, signals, n_ticks)
        dec, conf = vc.verdict(out_state)
        tick_snapshots.append({
            "label": label,
            "sample_idx": int(sidx),
            "ticks": tick_hist,
            "verdict": "FOR" if dec is True else ("AGAINST" if dec is False else "UNKNOWN"),
            "output_state": out_state,
        })

    # Final eval
    preds = vc.predict_cloud(best_neurons, X, feature_mins, feature_maxs, n_ticks)
    correct = sum(1 for i, (d, _) in enumerate(preds) if d == bool(y[i]))
    wrong = sum(1 for i, (d, _) in enumerate(preds) if d is not None and d != bool(y[i]))
    unknown = sum(1 for d, _ in preds if d is None)
    answered = correct + wrong
    ca = (correct * 1000) // answered if answered > 0 else 0
    cov = (answered * 100) // len(X)

    neuron_data = []
    for n in best_neurons:
        neuron_data.append({
            "id": n.nid, "x": n.pos_x, "y": n.pos_y, "z": n.pos_z,
            "neighbors": list(n.neighbor_ids),
            "state": n.state,
            "correct": n.correct_count, "wrong": n.wrong_count,
            "is_output": n.is_output,
            "amplitude": n.amplitude_n,
            "n_features": len(n.input_mask),
        })

    init_data = [{"id": i, "x": p[0], "y": p[1], "z": p[2]} for i, p in enumerate(init_pos)]

    return {
        "name": dataset_name, "class_names": class_names,
        "n_samples": len(X), "n_features": n_features,
        "n_neurons": n_neurons, "k_neighbors": k, "n_ticks": n_ticks,
        "metrics": {"correct": correct, "wrong": wrong, "unknown": unknown,
                     "coverage_pct": cov, "cond_accuracy_permille": ca},
        "neurons": neuron_data,
        "initial_positions": init_data,
        "training_history": history,
        "signal_propagation": tick_snapshots,
    }


rewire = 10

# Breast Cancer
print("Breast Cancer...")
bc = load_breast_cancer()
r1 = train_and_export(bc.data, bc.target, "Breast Cancer", ["Malignant","Benign"],
                      n_neurons=64, k=8, n_ticks=3, n_epochs=80, lr=5)
print(f"  {r1['metrics']}")

# Wine
print("Wine...")
wine = load_wine()
y_w = (wine.target == 0).astype(int)
r2 = train_and_export(wine.data, y_w, "Wine", ["Other","Class 0"],
                      n_neurons=48, k=6, n_ticks=3, n_epochs=80, lr=5)
print(f"  {r2['metrics']}")

# Iris
print("Iris...")
iris = load_iris()
y_i = (iris.target == 0).astype(int)
r3 = train_and_export(iris.data, y_i, "Iris", ["Non-Setosa","Setosa"],
                      n_neurons=32, k=6, n_ticks=3, n_epochs=60, lr=5)
print(f"  {r3['metrics']}")

# Digits
print("Digits 0v1...")
digits = load_digits()
mask = (digits.target == 0) | (digits.target == 1)
X_d, y_d = digits.data[mask], digits.target[mask]
r4 = train_and_export(X_d, y_d, "Digits 0v1", ["Zero","One"],
                      n_neurons=64, k=8, n_ticks=3, n_epochs=80, lr=5)
print(f"  {r4['metrics']}")

all_data = {
    "datasets": [r1, r2, r3, r4],
    "model_info": {
        "name": "VoidCloud v3", "W_DENOM": 128, "S_DENOM": 64,
        "POS_SCALE": 1000, "FOR_THRESH": 36, "AG_THRESH": 28,
    }
}

with open('/sessions/laughing-hopeful-bohr/mnt/void-theory/void_cloud_3d_data.json', 'w') as f:
    json.dump(all_data, f)

print("\nExported to void_cloud_3d_data.json")
