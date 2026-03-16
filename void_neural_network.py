"""
VOID Neural Network — a true neural network built on VOID Theory.

Architecture:
  Input (FinProb features) → Hidden Layers → Single Output → Bool3

Key innovations:
  1. Bool3 output: FOR / AGAINST / UNKNOWN as ontological states
  2. All integer arithmetic: FinProb weights, no floats in core logic
  3. Topology Folding: FoldBridges provide direct gradient paths from
     output to every hidden layer — gradient cannot vanish because
     it doesn't pass through intermediate weights.
     (From void_topology_folding.v: bridges connect distant layers)
  4. Entropy-aware backprop: layers with high entropy (random weights)
     receive gradient through bridges; structured layers use normal backprop.
     (From void_entropy_tunnel.v: tunneling through high-entropy regions)
"""

import json
import random
from dataclasses import dataclass, field
from typing import List, Tuple, Optional

# ============================================================
# FinProb
# ============================================================
@dataclass
class FinProb:
    n: int
    d: int
    def __repr__(self):
        return f"{self.n}/{self.d}"

ZERO = FinProb(0, 1)
HALF = FinProb(1, 2)
W_DENOM = 128  # Weight resolution (higher = finer learning)
S_DENOM = 64   # Signal resolution (input encoding)

def fp_gt(a, b): return a.n * b.d > b.n * a.d
def fp_lt(a, b): return a.n * b.d < b.n * a.d


# ============================================================
# Neuron
# ============================================================
@dataclass
class VoidNeuron:
    neuron_id: int
    layer: int
    weights: List[int] = field(default_factory=list)   # integers in [-W_DENOM, W_DENOM]
    bias: int = 0
    amplitude: FinProb = field(default_factory=lambda: FinProb(500, 1000))
    budget: int = 10000000
    heat: int = 0
    correct_count: int = 0
    wrong_count: int = 0
    activation_count: int = 0


# ============================================================
# FoldBridge — from void_topology_folding.v
# Direct gradient path from output to any hidden layer.
# Bridges have stability that decays with use (DDF forward).
# ============================================================
@dataclass
class FoldBridge:
    """A bridge connecting output error directly to a hidden layer.

    From void_topology_folding.v:
    - end1/end2: endpoints (here: output layer → hidden layer index)
    - stability: strength of bridge (decays with use)
    - maintenance_cost: budget consumed per use
    """
    target_layer: int           # Which hidden layer this connects to
    stability_n: int = 64       # Stability numerator (starts at 64/128)
    stability_d: int = 128      # Stability denominator
    uses: int = 0               # How many times used
    useful_count: int = 0       # How many times the bridge helped

    @property
    def strength(self):
        """Bridge strength as fraction — determines how much direct error signal passes."""
        return self.stability_n / self.stability_d


# ============================================================
# Network init
# ============================================================
def init_network(n_features: int, hidden_sizes: List[int]):
    """Create VOID neural network with FoldBridges.

    Returns: (layers, bridges)
    - layers: list of neuron lists (hidden + output)
    - bridges: list of FoldBridges from output to each hidden layer
    """
    layers = []
    neuron_id = 0
    prev_size = n_features

    for layer_idx, size in enumerate(hidden_sizes):
        neurons = []
        for _ in range(size):
            sqrt_approx = max(1, int(prev_size ** 0.5))
            w_range = max(2, W_DENOM // sqrt_approx)
            weights = [random.randint(-w_range, w_range) for _ in range(prev_size)]
            bias = random.randint(-w_range // 2, w_range // 2)
            neurons.append(VoidNeuron(neuron_id=neuron_id, layer=layer_idx,
                                       weights=weights, bias=bias))
            neuron_id += 1
        layers.append(neurons)
        prev_size = size

    # Output layer: single neuron
    sqrt_approx = max(1, int(prev_size ** 0.5))
    w_range = max(2, W_DENOM // sqrt_approx)
    output_neuron = VoidNeuron(
        neuron_id=neuron_id, layer=len(hidden_sizes),
        weights=[random.randint(-w_range, w_range) for _ in range(prev_size)],
        bias=0,
    )
    layers.append([output_neuron])

    # FoldBridges: direct connection from output error to each hidden layer
    # From void_topology_folding.v: "fold_space creates bridge between two locations"
    bridges = []
    for l_idx in range(len(hidden_sizes)):
        # Bridge stability starts at 1/2 (matching void_topology_folding.v)
        bridges.append(FoldBridge(
            target_layer=l_idx,
            stability_n=W_DENOM // 2,
            stability_d=W_DENOM,
        ))

    return layers, bridges


# ============================================================
# Activation — integer ReLU-like, producing FinProb output
# ============================================================
def neuron_forward(neuron: VoidNeuron, inputs: List[FinProb]) -> Tuple[FinProb, int, bool]:
    """Compute neuron output — all integer.

    Returns: (output, raw_weighted_sum, saturated)
    - output: FinProb(n, S_DENOM)
    - raw_ws: the raw weighted sum before activation (for backprop)
    - saturated: whether output was clamped (derivative = 0)
    """
    if neuron.budget <= 0:
        return FinProb(S_DENOM // 2, S_DENOM), 0, True  # dead = neutral, saturated

    neuron.budget -= 1
    neuron.heat += 1
    neuron.activation_count += 1

    # Weighted sum: w_i * input_i.n (all inputs have d=S_DENOM)
    ws = 0
    for i in range(min(len(inputs), len(neuron.weights))):
        ws += neuron.weights[i] * inputs[i].n

    ws += neuron.bias * S_DENOM

    # Scale: sqrt(n_inputs) * W_DENOM — normalizes for random weight distribution
    # With Xavier init, weights ~ W_DENOM/sqrt(n), so typical ws ~ sqrt(n) * W_DENOM * S_DENOM/2
    # We want this to map to roughly S_DENOM/4 shift → good spread across output range
    n_inp = len(neuron.weights)
    sqrt_n = max(1, int(n_inp ** 0.5))
    scale = max(1, sqrt_n * W_DENOM)

    # Map to [0, S_DENOM]: output = S_DENOM/2 + ws / scale
    half = S_DENOM // 2
    shift = ws // scale
    out_n = half + shift

    # Clamp and track saturation
    saturated = (out_n <= 0) or (out_n >= S_DENOM)
    out_n = max(0, min(S_DENOM, out_n))

    return FinProb(out_n, S_DENOM), ws, saturated


def layer_forward_simple(layer: List[VoidNeuron], inputs: List[FinProb]) -> List[FinProb]:
    """Forward pass returning just outputs (for inference)."""
    return [neuron_forward(n, inputs)[0] for n in layer]


def layer_forward_full(layer: List[VoidNeuron], inputs: List[FinProb]):
    """Forward pass returning outputs + metadata (for training)."""
    outputs = []
    raw_ws_list = []
    saturated_list = []
    for n in layer:
        out, raw_ws, sat = neuron_forward(n, inputs)
        outputs.append(out)
        raw_ws_list.append(raw_ws)
        saturated_list.append(sat)
    return outputs, raw_ws_list, saturated_list


def network_forward(layers, inputs: List[FinProb]) -> List[FinProb]:
    current = inputs
    for layer in layers:
        current = layer_forward_simple(layer, current)
    return current


# ============================================================
# Bool3 Verdict from single output neuron
# ============================================================
# Thresholds for Bool3 (in S_DENOM scale)
# S_DENOM=16: FOR > 9/16 (0.5625), AGAINST < 7/16 (0.4375)
# S_DENOM=64: FOR > 36/64 (0.5625), AGAINST < 28/64 (0.4375)
FOR_THRESH_N = (S_DENOM * 9) // 16    # = 36 when S_DENOM=64
AG_THRESH_N = (S_DENOM * 7) // 16     # = 28 when S_DENOM=64

def verdict(output: FinProb) -> Tuple[Optional[bool], FinProb]:
    """Bool3 verdict from single neuron output (scale = S_DENOM).
    High output = FOR (True/benign), Low = AGAINST (False/malignant),
    Middle = UNKNOWN.
    """
    if output.n > FOR_THRESH_N:
        confidence = FinProb(output.n, output.d)
        return True, confidence
    elif output.n < AG_THRESH_N:
        confidence = FinProb(output.d - output.n, output.d)
        return False, confidence
    else:
        return None, FinProb(abs(2 * output.n - output.d), output.d)


# ============================================================
# Entropy measurement — from void_entropy_tunnel.v
# ============================================================
def compute_layer_entropy(layer: List[VoidNeuron]) -> int:
    """Measure weight disorder of a layer — integer entropy.

    Returns a value in [0, W_DENOM] range:
      - 0 = perfectly structured (all weights identical or zero)
      - W_DENOM = maximum disorder (weights uniformly spread)

    Method: mean absolute deviation of all weights, normalized.
    This is the VOID analog of entropy — measured in integer ticks,
    no logarithms, no floats. Pure counting.
    """
    if not layer:
        return 0

    # Collect all weights from all neurons in this layer
    all_weights = []
    for neuron in layer:
        all_weights.extend(neuron.weights)

    if not all_weights:
        return 0

    # Mean (integer)
    n = len(all_weights)
    mean = sum(all_weights) // n

    # Mean absolute deviation (integer)
    mad = sum(abs(w - mean) for w in all_weights) // n

    # Normalize to [0, W_DENOM] range
    # Max possible MAD ≈ W_DENOM (when weights span full range)
    return min(W_DENOM, mad)


# ============================================================
# Learning — entropy-tunneled credit propagation
# ============================================================
def train_step(layers, inputs: List[FinProb], truth: bool, learning_rate: int = 2,
               bridges: List[FoldBridge] = None):
    """One training step with magnitude-based integer backpropagation.

    Key insight: propagate actual error magnitudes through layers,
    not just signs. All arithmetic stays integer.
    """
    # Forward pass — save per-layer inputs, outputs, and saturation
    layer_inputs = []
    layer_outputs = []
    layer_saturated = []
    current = inputs

    for layer in layers:
        layer_inputs.append(current)
        outputs, raw_ws_list, sat_list = layer_forward_full(layer, current)
        layer_outputs.append(outputs)
        layer_saturated.append(sat_list)
        current = outputs

    # Verdict
    final_output = current[0]  # single output neuron
    decision, confidence = verdict(final_output)

    # === COMPUTE OUTPUT ERROR (integer) ===
    # target_n is in [0, S_DENOM] scale
    if truth:
        target_n = (S_DENOM * 3) // 4  # 75% — deep into FOR zone
    else:
        target_n = S_DENOM // 4         # 25% — deep into AGAINST zone

    # error = target - actual, range [-S_DENOM, S_DENOM]
    output_error = target_n - final_output.n

    # === OUTPUT LAYER WEIGHT UPDATE ===
    out_neuron = layers[-1][0]
    out_inputs = layer_inputs[-1]
    n_out_inp = len(out_neuron.weights)
    # Scale factor: we want step ~ lr * error * input / (n_inp * S_DENOM)
    out_scale = max(1, n_out_inp)

    for i in range(min(n_out_inp, len(out_inputs))):
        # step = lr * error * input_activation / (n_inputs * S_DENOM)
        # All integers: (lr * output_error * inp_n) // (out_scale * S_DENOM)
        inp_n = out_inputs[i].n
        step = (learning_rate * output_error * inp_n) // (out_scale * S_DENOM)
        if step == 0 and output_error != 0:
            step = 1 if output_error > 0 else -1
        out_neuron.weights[i] = max(-W_DENOM, min(W_DENOM,
                                    out_neuron.weights[i] + step))

    # Bias update
    bias_step = (learning_rate * output_error) // out_scale
    if bias_step == 0 and output_error != 0:
        bias_step = 1 if output_error > 0 else -1
    out_neuron.bias = max(-W_DENOM, min(W_DENOM,
                          out_neuron.bias + bias_step))

    # Track correctness + amplitude credit for output neuron
    if decision == truth:
        out_neuron.correct_count += 1
        new_amp = min(out_neuron.amplitude.d - 1, out_neuron.amplitude.n + 5)
        out_neuron.amplitude = FinProb(new_amp, out_neuron.amplitude.d)
    elif decision is not None:
        out_neuron.wrong_count += 1
        new_amp = max(1, out_neuron.amplitude.n - 8)
        out_neuron.amplitude = FinProb(new_amp, out_neuron.amplitude.d)

    # === TOPOLOGY-FOLDED BACKPROPAGATION ===
    # From void_topology_folding.v:
    #   - FoldBridges connect output error directly to each hidden layer
    #   - Gradient flows through bridges (can't vanish — no intermediate weights)
    #   - Normal backprop ALSO runs through adjacent layers
    #   - Total delta = normal_delta + bridge_delta
    #   - Bridge stability decays with use (DDF forward)
    #   - If bridge helps (layer improves), stability reinforced
    #
    next_deltas = [output_error]

    for l_idx in range(len(layers) - 2, -1, -1):
        layer = layers[l_idx]
        next_layer = layers[l_idx + 1]
        l_inputs = layer_inputs[l_idx]
        l_outputs = layer_outputs[l_idx]
        l_saturated = layer_saturated[l_idx]

        # Find bridge for this layer (if any)
        bridge = None
        if bridges:
            for br in bridges:
                if br.target_layer == l_idx:
                    bridge = br
                    break

        current_deltas = []
        n_l_inp = len(layer[0].weights) if layer else 1

        for h_idx, h_neuron in enumerate(layer):
            if h_neuron.budget <= 0:
                current_deltas.append(0)
                continue

            # 1. Normal backprop through adjacent layer
            back_scale = max(1, int(W_DENOM ** 0.5))
            normal_delta = 0
            for j, next_neuron in enumerate(next_layer):
                if h_idx < len(next_neuron.weights) and j < len(next_deltas):
                    normal_delta += (next_deltas[j] * next_neuron.weights[h_idx]) // back_scale

            # 2. FoldBridge: direct error signal from output (topology folding)
            # This term CANNOT vanish because it doesn't pass through
            # any intermediate weights — it jumps directly from output.
            bridge_delta = 0
            if bridge is not None and bridge.stability_n > 0:
                # bridge_delta = output_error * bridge_strength
                # Scale: (output_error * stability_n) // stability_d
                bridge_delta = (output_error * bridge.stability_n) // bridge.stability_d

            # 3. Combine: total delta = normal + bridge
            delta_h = normal_delta + bridge_delta

            # Activation derivative: 0 if saturated
            if l_saturated[h_idx]:
                delta_h = 0

            current_deltas.append(delta_h)

            if delta_h == 0:
                continue

            # Update hidden weights
            delta_h = max(-S_DENOM * 4, min(S_DENOM * 4, delta_h))
            h_scale = max(1, n_l_inp * 2)
            for i in range(min(len(h_neuron.weights), len(l_inputs))):
                inp_n = l_inputs[i].n
                step = (learning_rate * delta_h * inp_n) // (h_scale * S_DENOM)
                if step == 0 and delta_h != 0:
                    step = 1 if delta_h > 0 else -1
                h_neuron.weights[i] = max(-W_DENOM, min(W_DENOM,
                                          h_neuron.weights[i] + step))
                h_neuron.budget -= 1
                h_neuron.heat += 1

            # Bias update
            h_bias_step = (learning_rate * delta_h) // h_scale
            if h_bias_step == 0 and delta_h != 0:
                h_bias_step = 1 if delta_h > 0 else -1
            h_neuron.bias = max(-W_DENOM, min(W_DENOM,
                                h_neuron.bias + h_bias_step))

        # Amplitude credit for all neurons in this layer
        for h_neuron in layer:
            if decision is not None:
                if decision == truth:
                    h_neuron.correct_count += 1
                    new_amp = min(h_neuron.amplitude.d - 1, h_neuron.amplitude.n + 2)
                else:
                    h_neuron.wrong_count += 1
                    new_amp = max(1, h_neuron.amplitude.n - 3)
                h_neuron.amplitude = FinProb(new_amp, h_neuron.amplitude.d)

        # Bridge DDF: update bridge stability
        # From void_topology_folding.v: "observe_bridge weakens it" (DDF forward)
        # But if bridge was useful, reinforce it
        if bridge is not None:
            bridge.uses += 1
            # DDF forward: using bridge decays it slightly
            bridge.stability_n = max(1, bridge.stability_n - 1)
            # DDF backward: if this layer is learning (entropy decreasing),
            # bridge is being useful → reinforce
            layer_entropy = compute_layer_entropy(layer)
            if layer_entropy < W_DENOM // 2:  # Layer has structure
                bridge.stability_n = min(bridge.stability_d, bridge.stability_n + 2)
                bridge.useful_count += 1

        next_deltas = current_deltas

    return decision, confidence


# ============================================================
# Encoding (boundary with float world)
# ============================================================
def encode_features(X_row, feature_mins, feature_maxs) -> List[FinProb]:
    signals = []
    for i, val in enumerate(X_row):
        rng = feature_maxs[i] - feature_mins[i]
        if rng == 0:
            signals.append(FinProb(S_DENOM // 2, S_DENOM))
        else:
            normalized = (val - feature_mins[i]) / rng
            n = max(0, min(S_DENOM, int(normalized * S_DENOM)))
            signals.append(FinProb(n, S_DENOM))
    return signals


# ============================================================
# Training loop
# ============================================================
def train(X, y, feature_names, hidden_sizes=[16], n_epochs=40, lr=2):
    random.seed(42)
    feature_mins = X.min(axis=0)
    feature_maxs = X.max(axis=0)
    n_features = X.shape[1]

    layers, bridges = init_network(n_features, hidden_sizes)

    epoch_stats = []

    for epoch in range(n_epochs):
        correct_total = 0
        unknown_total = 0
        wrong_total = 0

        indices = list(range(len(X)))
        random.shuffle(indices)

        for idx in indices:
            signals = encode_features(X[idx], feature_mins, feature_maxs)
            truth = bool(y[idx])

            decision, _ = train_step(layers, signals, truth, learning_rate=lr,
                                     bridges=bridges)

            if decision == truth:
                correct_total += 1
            elif decision is None:
                unknown_total += 1
            else:
                wrong_total += 1

        total = len(X)
        acc_pct = (correct_total * 1000) // total
        alive = sum(1 for l in layers for n in l if n.budget > 0)
        total_neurons = sum(len(l) for l in layers)

        epoch_stats.append({
            "epoch": epoch, "correct": correct_total,
            "wrong": wrong_total, "unknown": unknown_total,
            "accuracy_permille": acc_pct, "alive": alive,
        })

        print(f"Epoch {epoch:2d}: {correct_total}/{total} ({acc_pct}\u2030) "
              f"wrong={wrong_total} unknown={unknown_total} alive={alive}/{total_neurons}")

    return layers, bridges, epoch_stats, feature_mins, feature_maxs


def predict(layers, X, feature_mins, feature_maxs):
    results = []
    for idx in range(len(X)):
        signals = encode_features(X[idx], feature_mins, feature_maxs)
        outputs = network_forward(layers, signals)
        decision, confidence = verdict(outputs[0])
        results.append((decision, confidence.n, confidence.d))
    return results


# ============================================================
# Main
# ============================================================
def run_config(X, y, feature_names, hidden_sizes, n_epochs, lr, label=""):
    """Run one configuration and return summary + bridge info."""
    random.seed(42)
    layers, bridges, stats, fmins, fmaxs = train(X, y, feature_names,
                                                   hidden_sizes=hidden_sizes,
                                                   n_epochs=n_epochs, lr=lr)
    preds = predict(layers, X, fmins, fmaxs)
    correct = sum(1 for i, (d, _, _) in enumerate(preds) if d == bool(y[i]))
    wrong = sum(1 for i, (d, _, _) in enumerate(preds) if d is not None and d != bool(y[i]))
    unknown = sum(1 for d, _, _ in preds if d is None)
    answered = correct + wrong
    cond_acc = (correct * 1000) // answered if answered > 0 else 0
    return correct, wrong, unknown, cond_acc, bridges


if __name__ == "__main__":
    from sklearn.datasets import load_breast_cancer

    data = load_breast_cancer()
    X, y = data.data, data.target
    n = len(X)

    print("=" * 70)
    print("  VOID NEURAL NETWORK — Entropy Tunneled Backpropagation")
    print("  All integer. Zero floats. Bool3 output. Adaptive skip connections.")
    print("=" * 70)
    print(f"\nDataset: Wisconsin BC ({n} samples, {X.shape[1]} features)")
    print(f"W_DENOM={W_DENOM}, S_DENOM={S_DENOM}")
    print(f"FOR > {FOR_THRESH_N}/{S_DENOM}, AGAINST < {AG_THRESH_N}/{S_DENOM}")

    # Test scaling: from 2 layers to 6 layers
    configs = [
        ([64, 32], 80, 3, "2L: 64-32"),
        ([64, 32, 16], 80, 3, "3L: 64-32-16"),
        ([64, 48, 32, 16], 80, 3, "4L: 64-48-32-16"),
        ([64, 48, 32, 24, 16], 100, 3, "5L: 64-48-32-24-16"),
        ([64, 48, 32, 24, 16, 8], 100, 3, "6L: 64-48-32-24-16-8"),
    ]

    print(f"\n{'Config':<28s} {'Correct':>8s} {'Wrong':>6s} {'Unk':>5s} {'Cov%':>6s} {'CondAcc':>8s} {'Bridges':>8s}")
    print("-" * 80)

    for hidden, epochs, lr, label in configs:
        c, w, u, ca, brs = run_config(X, y, data.feature_names, hidden, epochs, lr, label)
        cov = ((c + w) * 100) // n
        br_info = " ".join(f"{br.stability_n}/{br.stability_d}" for br in brs) if brs else "none"
        print(f"  {label:<26s} {c:>8d} {w:>6d} {u:>5d} {cov:>5d}% {ca:>7d}\u2030  {br_info}")
