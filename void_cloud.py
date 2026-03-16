"""
VOID Cloud Network v3 — graph-based neural network built on VOID Theory.

Xenakis Terretektorh: musicians scattered in space, structure from interaction.

Architecture:
  - N neurons in abstract space (no layers)
  - Each neuron connects to K nearest neighbors
  - Feature subsets per neuron (specialization)
  - Signal propagates T ticks
  - Graph backprop: error flows backward through neighbor connections
  - Topology self-organizes: neurons move based on contribution
  - Checkpointing: save best weights during training

All integer arithmetic. Zero floats in core.
"""

import random
import copy
from dataclasses import dataclass, field
from typing import List, Tuple, Optional

# ============================================================
# Constants
# ============================================================
W_DENOM = 128
S_DENOM = 64
POS_SCALE = 1000

FOR_THRESH_N = (S_DENOM * 9) // 16    # 36
AG_THRESH_N = (S_DENOM * 7) // 16     # 28


@dataclass
class CloudNeuron:
    nid: int
    pos_x: int = 0
    pos_y: int = 0
    pos_z: int = 0
    input_weights: List[int] = field(default_factory=list)
    input_mask: List[int] = field(default_factory=list)
    neighbor_weights: List[int] = field(default_factory=list)
    neighbor_ids: List[int] = field(default_factory=list)
    bias: int = 0
    state: int = S_DENOM // 2
    prev_state: int = S_DENOM // 2
    amplitude_n: int = 500
    amplitude_d: int = 1000
    budget: int = 10_000_000
    correct_count: int = 0
    wrong_count: int = 0
    is_output: bool = False


def cloud_distance(a, b):
    return abs(a.pos_x - b.pos_x) + abs(a.pos_y - b.pos_y) + abs(a.pos_z - b.pos_z)


def init_cloud(n_features, n_neurons, k_neighbors, feature_frac=0.6):
    neurons = []
    n_subset = min(n_features, max(3, int(n_features * feature_frac)))

    for nid in range(n_neurons):
        px = random.randint(0, POS_SCALE)
        py = random.randint(0, POS_SCALE)
        pz = random.randint(0, POS_SCALE)
        is_out = (nid == n_neurons - 1)

        # Output neuron sees all features; others see random subset
        if is_out:
            mask = list(range(n_features))
        else:
            mask = sorted(random.sample(range(n_features), n_subset))

        n_vis = len(mask)
        sqrt_n = max(1, int(n_vis ** 0.5))
        w_range = max(2, W_DENOM // sqrt_n)
        input_w = [random.randint(-w_range, w_range) for _ in range(n_vis)]
        bias = random.randint(-w_range // 4, w_range // 4)

        neurons.append(CloudNeuron(
            nid=nid, pos_x=px, pos_y=py, pos_z=pz,
            input_weights=input_w, input_mask=mask,
            bias=bias, is_output=is_out,
        ))

    _connect_neighbors(neurons, k_neighbors)
    return neurons


def _connect_neighbors(neurons, k, preserve_weights=False):
    for neuron in neurons:
        old_w = {}
        if preserve_weights:
            for j, nid in enumerate(neuron.neighbor_ids):
                if j < len(neuron.neighbor_weights):
                    old_w[nid] = neuron.neighbor_weights[j]

        dists = sorted(
            [(cloud_distance(neuron, o), o.nid) for o in neurons if o.nid != neuron.nid]
        )
        neighbors = [nid for _, nid in dists[:k]]
        neuron.neighbor_ids = neighbors

        sqrt_k = max(1, int(k ** 0.5))
        w_range = max(2, W_DENOM // sqrt_k)
        neuron.neighbor_weights = [
            old_w.get(nid, random.randint(-w_range, w_range))
            for nid in neighbors
        ]


def activate(weighted_sum, n_inputs):
    sqrt_n = max(1, int(n_inputs ** 0.5))
    scale = max(1, sqrt_n * W_DENOM)
    return max(0, min(S_DENOM, S_DENOM // 2 + weighted_sum // scale))


def cloud_forward(neurons, inputs, n_ticks):
    n = len(neurons)
    nid_to_idx = {neuron.nid: i for i, neuron in enumerate(neurons)}

    for neuron in neurons:
        neuron.prev_state = S_DENOM // 2
        neuron.state = S_DENOM // 2

    tick_history = [[S_DENOM // 2] * n]

    for tick in range(n_ticks):
        new_states = []
        for neuron in neurons:
            # Input (masked features)
            ws = 0
            for wi, fi in enumerate(neuron.input_mask):
                if wi < len(neuron.input_weights) and fi < len(inputs):
                    ws += neuron.input_weights[wi] * inputs[fi]

            # Neighbor contribution
            for j, nid in enumerate(neuron.neighbor_ids):
                if j < len(neuron.neighbor_weights) and nid in nid_to_idx:
                    ws += neuron.neighbor_weights[j] * neurons[nid_to_idx[nid]].prev_state

            ws += neuron.bias * S_DENOM
            n_inp = len(neuron.input_weights) + len(neuron.neighbor_weights)
            new_states.append(activate(ws, n_inp))
            neuron.budget -= 1

        for i, neuron in enumerate(neurons):
            neuron.prev_state = neuron.state
            neuron.state = new_states[i]

        tick_history.append(list(new_states))

    return neurons[-1].state, tick_history, nid_to_idx


def verdict(output_state):
    if output_state > FOR_THRESH_N:
        return True, output_state
    elif output_state < AG_THRESH_N:
        return False, S_DENOM - output_state
    else:
        return None, abs(2 * output_state - S_DENOM)


# ============================================================
# Training — graph backprop + gradient clipping
# ============================================================
def train_step(neurons, inputs, truth, n_ticks, learning_rate=5):
    n = len(neurons)
    output_state, tick_history, nid_to_idx = cloud_forward(neurons, inputs, n_ticks)
    decision, confidence = verdict(output_state)

    target = (S_DENOM * 3) // 4 if truth else S_DENOM // 4
    error = target - output_state
    if error == 0:
        return decision

    # Graph backprop: propagate error backward through T ticks
    curr_errors = [0] * n
    curr_errors[n - 1] = error
    accum_errors = [0] * n

    for back_tick in range(n_ticks):
        accum_errors = [accum_errors[i] + curr_errors[i] for i in range(n)]
        next_errors = [0] * n

        for i, neuron in enumerate(neurons):
            if curr_errors[i] == 0:
                continue
            # Propagate to neighbors (whose states influenced me)
            for j, nid in enumerate(neuron.neighbor_ids):
                if j < len(neuron.neighbor_weights) and nid in nid_to_idx:
                    prop = (curr_errors[i] * neuron.neighbor_weights[j]) // W_DENOM
                    next_errors[nid_to_idx[nid]] += prop

        curr_errors = next_errors

    accum_errors = [accum_errors[i] + curr_errors[i] for i in range(n)]

    # Clip errors to prevent oscillation
    MAX_ERR = S_DENOM
    accum_errors = [max(-MAX_ERR, min(MAX_ERR, e)) for e in accum_errors]

    # Weight updates
    for i, neuron in enumerate(neurons):
        local_err = accum_errors[i]
        if local_err == 0:
            continue
        err_sign = 1 if local_err > 0 else -1

        # Input weights
        n_inp = len(neuron.input_weights)
        sqrt_n = max(1, int(n_inp ** 0.5))
        for wi, fi in enumerate(neuron.input_mask):
            if wi >= n_inp or fi >= len(inputs):
                break
            step = (learning_rate * local_err * inputs[fi]) // (sqrt_n * S_DENOM)
            if step == 0:
                step = err_sign
            neuron.input_weights[wi] = max(-W_DENOM, min(W_DENOM,
                                            neuron.input_weights[wi] + step))

        # Neighbor weights
        n_nbr = len(neuron.neighbor_weights)
        sqrt_k = max(1, int(n_nbr ** 0.5))
        for j, nid in enumerate(neuron.neighbor_ids):
            if j < n_nbr and nid in nid_to_idx:
                nbr_state = tick_history[-1][nid_to_idx[nid]]
                step = (learning_rate * local_err * nbr_state) // (sqrt_k * S_DENOM)
                if step == 0:
                    step = err_sign
                neuron.neighbor_weights[j] = max(-W_DENOM, min(W_DENOM,
                                                  neuron.neighbor_weights[j] + step))

        # Bias
        bias_step = (learning_rate * local_err) // (sqrt_n * S_DENOM)
        if bias_step == 0:
            bias_step = err_sign
        neuron.bias = max(-W_DENOM, min(W_DENOM, neuron.bias + bias_step))

        # Amplitude
        if decision is not None:
            if decision == truth:
                neuron.correct_count += 1
                neuron.amplitude_n = min(neuron.amplitude_d - 1, neuron.amplitude_n + 2)
            else:
                neuron.wrong_count += 1
                neuron.amplitude_n = max(1, neuron.amplitude_n - 3)

    # Topology movement: attract toward output if helpful, repel if not
    # BUT also repel from nearby neurons to prevent collapse to single point
    MIN_DIST = POS_SCALE // 8  # minimum distance between neurons (~125)

    output_neuron = neurons[-1]
    for i, neuron in enumerate(neurons):
        if neuron.is_output or decision is None:
            continue
        local_err = accum_errors[i]
        if local_err == 0:
            continue
        activity = neuron.state - S_DENOM // 2
        if activity == 0:
            continue
        act_sign = 1 if activity > 0 else -1
        err_sign = 1 if local_err > 0 else -1

        helpful = (decision == truth) if (act_sign == err_sign) else (decision != truth)
        move = 2 if helpful else -1

        # Move toward/away from output
        dx = output_neuron.pos_x - neuron.pos_x
        dy = output_neuron.pos_y - neuron.pos_y
        dz = output_neuron.pos_z - neuron.pos_z
        dist = max(1, abs(dx) + abs(dy) + abs(dz))
        neuron.pos_x += (move * dx) // dist
        neuron.pos_y += (move * dy) // dist
        neuron.pos_z += (move * dz) // dist

        # Repulsion from nearby neurons (prevent collapse)
        for j, other in enumerate(neurons):
            if i == j or other.is_output:
                continue
            rx = neuron.pos_x - other.pos_x
            ry = neuron.pos_y - other.pos_y
            rz = neuron.pos_z - other.pos_z
            rdist = abs(rx) + abs(ry) + abs(rz)
            if rdist < MIN_DIST and rdist > 0:
                # Push apart
                push = 3
                neuron.pos_x += (push * rx) // max(1, rdist)
                neuron.pos_y += (push * ry) // max(1, rdist)
                neuron.pos_z += (push * rz) // max(1, rdist)

        neuron.pos_x = max(0, min(POS_SCALE, neuron.pos_x))
        neuron.pos_y = max(0, min(POS_SCALE, neuron.pos_y))
        neuron.pos_z = max(0, min(POS_SCALE, neuron.pos_z))

    return decision


def encode_features(X_row, feature_mins, feature_maxs):
    signals = []
    for i, val in enumerate(X_row):
        rng = feature_maxs[i] - feature_mins[i]
        if rng == 0:
            signals.append(S_DENOM // 2)
        else:
            normalized = (val - feature_mins[i]) / rng
            signals.append(max(0, min(S_DENOM, int(normalized * S_DENOM))))
    return signals


def train_cloud(X, y, n_neurons=64, k_neighbors=8, n_ticks=3,
                n_epochs=80, lr=5, rewire_every=10):
    random.seed(42)
    feature_mins = X.min(axis=0)
    feature_maxs = X.max(axis=0)
    n_features = X.shape[1]

    neurons = init_cloud(n_features, n_neurons, k_neighbors)

    best_neurons = copy.deepcopy(neurons)
    best_score = -999999

    for epoch in range(n_epochs):
        correct, wrong, unknown = 0, 0, 0

        indices = list(range(len(X)))
        random.shuffle(indices)

        for idx in indices:
            signals = encode_features(X[idx], feature_mins, feature_maxs)
            truth = bool(y[idx])
            decision = train_step(neurons, signals, truth, n_ticks, lr)

            if decision is None:
                unknown += 1
            elif decision == truth:
                correct += 1
            else:
                wrong += 1

        total = len(X)
        # Score: maximize correct, heavily penalize wrong
        score = correct * 10 - wrong * 30
        is_best = False
        if score > best_score:
            best_score = score
            best_neurons = copy.deepcopy(neurons)
            is_best = True

        if epoch % 10 == 0 or epoch == n_epochs - 1 or is_best:
            tag = " *" if is_best else ""
            print(f"  Ep {epoch:3d}: {correct}/{total} w={wrong} u={unknown}{tag}")

        if epoch % rewire_every == 0 and epoch >= 20:
            _connect_neighbors(neurons, k_neighbors, preserve_weights=True)

    return best_neurons, feature_mins, feature_maxs


def predict_cloud(neurons, X, feature_mins, feature_maxs, n_ticks=3):
    results = []
    for idx in range(len(X)):
        signals = encode_features(X[idx], feature_mins, feature_maxs)
        output_state, _, _ = cloud_forward(neurons, signals, n_ticks)
        results.append(verdict(output_state))
    return results


if __name__ == "__main__":
    from sklearn.datasets import load_breast_cancer

    data = load_breast_cancer()
    X, y = data.data, data.target
    n = len(X)

    print("=" * 70)
    print("  VOID CLOUD v3 — Graph Backprop + Feature Masks + Checkpointing")
    print("=" * 70)
    print(f"Dataset: Wisconsin BC ({n} samples, {X.shape[1]} features)\n")

    # (n_neurons, k, ticks, epochs, lr, rw, label)
    configs = [
        (32,  6, 3, 80,  5, 10, "32n k=6"),
        (64,  8, 3, 80,  5, 10, "64n k=8"),
        (128, 8, 3, 80,  5, 10, "128n k=8"),
        (128, 12,3, 80,  5, 10, "128n k=12"),
        (128, 8, 3, 100, 8, 15, "128n k=8 lr=8 100ep"),
    ]

    print(f"{'Config':<25s} {'Correct':>8s} {'Wrong':>6s} {'Unk':>5s} {'Cov%':>6s} {'CondAcc':>8s}")
    print("-" * 62)

    for n_neurons, k, ticks, epochs, lr, rw, label in configs:
        print(f"\n>>> {label}")
        neurons, fmins, fmaxs = train_cloud(X, y, n_neurons, k, ticks, epochs, lr, rw)
        preds = predict_cloud(neurons, X, fmins, fmaxs, ticks)

        correct = sum(1 for i, (d, _) in enumerate(preds) if d == bool(y[i]))
        wrong = sum(1 for i, (d, _) in enumerate(preds) if d is not None and d != bool(y[i]))
        unknown = sum(1 for d, _ in preds if d is None)
        answered = correct + wrong
        cov = (answered * 100) // n
        ca = (correct * 1000) // answered if answered > 0 else 0
        print(f"  >> {label:<23s} {correct:>8d} {wrong:>6d} {unknown:>5d} {cov:>5d}% {ca:>7d}\u2030")
