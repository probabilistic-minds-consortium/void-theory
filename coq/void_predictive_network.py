"""
void_predictive_network.py — VOID predictive processing network.

TWO CORRECTIONS:
  a) NO FRACTIONS. Weight = Fin n. Accumulator = Fin. Compare = le_fin_b3.
     FinProb is gone. Everything is structural finite type operations.

  b) PREDICTIVE PROCESSING (Friston/Clark):
     - Cell maintains a PREDICTION (what it expects)
     - Signal arrives → prediction error = surprise
     - Low surprise = cell predicted well = conserve budget (free energy)
     - High surprise = cell predicted poorly = spend budget
     - Budget IS free energy. Prediction error consumes it.
     - Good predictors survive. Bad predictors die.

     The brain doesn't learn from signals. It learns from ERRORS.
     What propagates is not the signal — it's the mismatch.

Dataset: Wisconsin Breast Cancer (569 real patients)
"""

import random
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from sklearn.datasets import load_breast_cancer
from sklearn.model_selection import train_test_split
from sklearn.feature_selection import mutual_info_classif
from dataclasses import dataclass, field
from enum import Enum
from typing import List, Tuple
from copy import deepcopy

# ============================================================================
# BOOL3 + FIN OPS — no fractions anywhere
# ============================================================================

class Bool3(Enum):
    BTrue = "T"
    BFalse = "F"
    BUnknown = "?"
    def __repr__(self): return self.value

def add_fin(a, b, budget):
    """Add two Fin values. Each step costs 1 tick."""
    result, heat = a, 0
    for _ in range(b):
        if budget <= 0: return (result, 0, heat)
        budget -= 1; heat += 1; result += 1
    return (result, budget, heat)

def le_fin_b3(n, m, budget):
    """n <= m? Structural countdown. Returns Bool3."""
    heat = 0
    while True:
        if budget <= 0: return (Bool3.BUnknown, 0, heat)
        budget -= 1; heat += 1
        if n == 0: return (Bool3.BTrue, budget, heat)
        if m == 0: return (Bool3.BFalse, budget, heat)
        n -= 1; m -= 1

def eq_fin_b3(n, m, budget):
    """n == m? Structural."""
    heat = 0
    while True:
        if budget <= 0: return (Bool3.BUnknown, 0, heat)
        budget -= 1; heat += 1
        if n == 0 and m == 0: return (Bool3.BTrue, budget, heat)
        if n == 0 or m == 0: return (Bool3.BFalse, budget, heat)
        n -= 1; m -= 1

# ============================================================================
# PREDICTIVE CELL — Friston/Clark model
#
# Each cell is a tiny generative model:
#   - It has weights (Fin values) per input
#   - It PREDICTS: accumulates evidence for/against, compares
#   - Prediction error = |predicted - actual truth|
#   - Budget = free energy, consumed by surprise
#
# Three prediction error levels:
#   - MATCH:    cell predicted correctly → minimal cost (just computation)
#   - MISMATCH: cell predicted wrong → surprise penalty
#   - UNKNOWN:  cell couldn't predict → no penalty, no reward (honest)
# ============================================================================

@dataclass
class PredictiveCell:
    """A cell that predicts, not reacts."""
    weights_for: List[int]      # Fin weights: how much BTrue evidence counts
    weights_against: List[int]  # Fin weights: how much BFalse evidence counts
    budget: int                 # free energy
    heat: int                   # dissipated energy (irreversible)
    initial_budget: int
    prior: Bool3 = Bool3.BUnknown  # cell's standing prediction (updated by history)
    correct_count: int = 0     # tracks prediction success
    wrong_count: int = 0       # tracks prediction failure

def accumulate_fin(inputs_active, weights, budget):
    """Sum weights where input is active. Pure Fin addition.
    Cost: 1 tick per active input (fixed), not proportional to weight."""
    acc = 0
    for active, w in zip(inputs_active, weights):
        if active:
            if budget <= 0: return (acc, 0)
            budget -= 1  # fixed cost per input, not per weight unit
            acc += w     # structural: Fin value, no loop needed for same-den
    return (acc, budget)

def predict(cell, inputs):
    """
    Cell makes a prediction based on current inputs.
    Accumulates evidence FOR (BTrue inputs) and AGAINST (BFalse inputs).
    Compares the two Fin accumulators.
    BUnknown inputs: skip both (no evidence).
    """
    budget = cell.budget

    # Collect evidence
    true_mask = [i == Bool3.BTrue for i in inputs]
    false_mask = [i == Bool3.BFalse for i in inputs]

    evidence_for, budget = accumulate_fin(true_mask, cell.weights_for, budget)
    evidence_against, budget = accumulate_fin(false_mask, cell.weights_against, budget)

    # No evidence at all?
    if evidence_for == 0 and evidence_against == 0:
        cost = cell.budget - budget
        return (Bool3.BUnknown, cost)

    # Only one side has evidence
    if evidence_for == 0:
        cost = cell.budget - budget
        return (Bool3.BFalse, cost)
    if evidence_against == 0:
        cost = cell.budget - budget
        return (Bool3.BTrue, cost)

    # Both sides → compare (le_fin_b3 twice to detect tie)
    r1, budget, _ = le_fin_b3(evidence_against, evidence_for, budget)
    r2, budget, _ = le_fin_b3(evidence_for, evidence_against, budget)

    cost = cell.budget - budget

    if r1 == Bool3.BTrue and r2 == Bool3.BTrue:
        return (Bool3.BUnknown, cost)  # tie → honest uncertainty
    elif r1 == Bool3.BTrue:
        return (Bool3.BTrue, cost)     # for > against
    elif r2 == Bool3.BTrue:
        return (Bool3.BFalse, cost)    # against > for
    else:
        return (Bool3.BUnknown, cost)  # budget ran out

def update_cell(cell, prediction, truth, computation_cost):
    """
    Predictive processing update:
    - Prediction matched truth → low surprise → pay only computation cost
    - Prediction was wrong → HIGH surprise → pay computation + penalty
    - Prediction was Unknown → no surprise signal → pay computation only
    """
    SURPRISE_COST = 150  # prediction error penalty

    new_budget = cell.budget - computation_cost
    new_heat = cell.heat + computation_cost

    if prediction == Bool3.BUnknown or truth == Bool3.BUnknown:
        # Can't compute prediction error → no update
        return PredictiveCell(
            cell.weights_for, cell.weights_against,
            new_budget, new_heat, cell.initial_budget,
            cell.prior, cell.correct_count, cell.wrong_count)

    if prediction == truth:
        # LOW SURPRISE — prediction matched reality
        # Reward: small budget recovery (precision weighting)
        PRECISION_GAIN = 40  # successful prediction = free energy gain
        return PredictiveCell(
            cell.weights_for, cell.weights_against,
            new_budget + PRECISION_GAIN, new_heat, cell.initial_budget,
            prediction, cell.correct_count + 1, cell.wrong_count)
    else:
        # HIGH SURPRISE — prediction error!
        # This is the key Friston insight: surprise costs free energy
        return PredictiveCell(
            cell.weights_for, cell.weights_against,
            new_budget - SURPRISE_COST, new_heat + SURPRISE_COST, cell.initial_budget,
            prediction, cell.correct_count, cell.wrong_count + 1)

# ============================================================================
# NETWORK — ensemble of predictive cells
# ============================================================================

@dataclass
class PredictiveNetwork:
    cells: List[PredictiveCell]
    history: list = field(default_factory=list)

    def forward(self, inputs):
        """Each cell predicts. Tally alive cells. Return consensus."""
        predictions = []
        costs = []
        for cell in self.cells:
            pred, cost = predict(cell, inputs)
            predictions.append(pred)
            costs.append(cost)

        # Tally only alive cells
        alive_preds = [p for p, c in zip(predictions, self.cells) if c.budget > 0]
        if not alive_preds:
            alive_preds = predictions  # fallback: use all

        t = sum(1 for p in alive_preds if p == Bool3.BTrue)
        f = sum(1 for p in alive_preds if p == Bool3.BFalse)
        u = sum(1 for p in alive_preds if p == Bool3.BUnknown)

        if u >= t + f:
            verdict = Bool3.BUnknown
        elif t > f:
            verdict = Bool3.BTrue
        elif f > t:
            verdict = Bool3.BFalse
        else:
            verdict = Bool3.BUnknown

        return predictions, costs, verdict, t, f, u

    def train_step(self, inputs, truth):
        predictions, costs, verdict, vt, vf, vu = self.forward(inputs)

        # Update each cell based on its prediction error
        new_cells = []
        for cell, pred, cost in zip(self.cells, predictions, costs):
            new_cells.append(update_cell(cell, pred, truth, cost))
        self.cells = new_cells

        alive = sum(1 for c in self.cells if c.budget > 0)
        self.history.append({
            'correct': verdict == truth,
            'verdict': verdict.value,
            'truth': truth.value,
            'budgets': [c.budget for c in self.cells],
            'heats': [c.heat for c in self.cells],
            'alive': [c.budget > 0 for c in self.cells],
            'alive_count': alive,
            'votes': (vt, vf, vu),
        })
        return verdict

# ============================================================================
# LOAD DATA
# ============================================================================

print("=" * 60)
print("VOID Predictive Processing Network")
print("Friston/Clark: prediction error = free energy cost")
print("No fractions. Only Fin. Only le_fin_b3.")
print("=" * 60)
print()

data = load_breast_cancer()
X, y = data.data, data.target
feature_names = list(data.feature_names)

# 8 diverse-quality features
mi = mutual_info_classif(X, y, random_state=42)
diverse_idx = [22, 20, 26, 10, 28, 15, 9, 11]
X_selected = X[:, diverse_idx]
n_features = 8
medians = np.median(X_selected, axis=0)

print("Features: 8 diverse quality (best → noise)")
for i, idx in enumerate(diverse_idx):
    q = 'BEST' if mi[idx] > 0.4 else 'GOOD' if mi[idx] > 0.2 else 'WEAK' if mi[idx] > 0.05 else 'NOISE'
    print(f"  x{i}: {feature_names[idx]} (MI={mi[idx]:.3f}) [{q}]")
print()

def to_bool3(row, medians):
    return [Bool3.BTrue if row[i] > medians[i] else Bool3.BFalse for i in range(len(medians))]

def label_to_bool3(label):
    return Bool3.BFalse if label == 1 else Bool3.BTrue  # malignant=BTrue

X_train, X_test, y_train, y_test = train_test_split(
    X_selected, y, test_size=0.2, random_state=42, stratify=y)
print(f"Train: {len(y_train)} ({sum(y_train==0)} malignant, {sum(y_train==1)} benign)")
print(f"Test:  {len(y_test)} ({sum(y_test==0)} malignant, {sum(y_test==1)} benign)")
print()

# ============================================================================
# BUILD NETWORK — weights are plain Fin values, not fractions
# ============================================================================

def make_network():
    random.seed(42)

    # x0=w.perim(BEST) x1=w.radius(BEST) x2=w.concav(GOOD) x3=rad.err(GOOD)
    # x4=w.symm(WEAK)  x5=comp.err(WEAK) x6=m.fractal(NOISE) x7=tex.err(NOISE)

    configs = [
        # BEST focused (should predict well → survive)
        ([5,5,1,1,1,1,1,1], [5,5,1,1,1,1,1,1]),
        ([5,5,1,1,1,1,1,1], [5,5,1,1,1,1,1,1]),
        # GOOD focused
        ([1,1,5,5,1,1,1,1], [1,1,5,5,1,1,1,1]),
        ([1,1,5,5,1,1,1,1], [1,1,5,5,1,1,1,1]),
        # WEAK focused (marginal predictors)
        ([1,1,1,1,5,5,1,1], [1,1,1,1,5,5,1,1]),
        ([1,1,1,1,5,5,1,1], [1,1,1,1,5,5,1,1]),
        # NOISE focused (should die — can't predict from noise)
        ([1,1,1,1,1,1,5,5], [1,1,1,1,1,1,5,5]),
        ([1,1,1,1,1,1,5,5], [1,1,1,1,1,1,5,5]),
        # BALANCED
        ([1,1,1,1,1,1,1,1], [1,1,1,1,1,1,1,1]),
        ([1,1,1,1,1,1,1,1], [1,1,1,1,1,1,1,1]),
        # BEST+GOOD broad model
        ([3,3,3,3,1,1,1,1], [3,3,3,3,1,1,1,1]),
        # Quality-aligned
        ([5,4,3,2,1,1,1,1], [5,4,3,2,1,1,1,1]),
        # ANTI-QUALITY (trusts noise over signal — should die fast)
        ([1,1,1,1,2,3,4,5], [1,1,1,1,2,3,4,5]),
        # Asymmetric: BEST predicts FOR, NOISE predicts AGAINST
        ([5,5,1,1,1,1,1,1], [1,1,1,1,1,1,5,5]),
        # Inverted: NOISE predicts FOR, BEST predicts AGAINST
        ([1,1,1,1,1,1,5,5], [5,5,1,1,1,1,1,1]),
        # Cross: BEST+GOOD FOR, WEAK+NOISE AGAINST
        ([4,4,3,3,1,1,1,1], [1,1,1,1,3,3,4,4]),
    ]

    cells = []
    for w_for, w_against in configs:
        cells.append(PredictiveCell(
            weights_for=w_for,
            weights_against=w_against,
            budget=30000,
            heat=0,
            initial_budget=30000))
    return PredictiveNetwork(cells)

strategy_labels = [
    'BEST-1', 'BEST-2', 'GOOD-1', 'GOOD-2',
    'WEAK-1', 'WEAK-2', 'NOISE-1', 'NOISE-2',
    'bal-1', 'bal-2', 'broad', 'decline',
    'anti-q', 'best+/n-', 'noise+/b-', 'cross',
]

# ============================================================================
# TRAIN
# ============================================================================

net = make_network()
n_cells = len(net.cells)
print(f"Network: {n_cells} predictive cells, {n_features} inputs each")
print(f"Budget (free energy): {net.cells[0].budget} ticks per cell")
print(f"Surprise cost: 150 | Precision gain: 40")
print()

# Debug: firing cost
test_inp = to_bool3(X_train[0], medians)
test_c = deepcopy(net.cells[0])
_, cost0 = predict(test_c, test_inp)
print(f"[debug] computation cost per prediction: {cost0} ticks")
print(f"[debug] 25 epochs × {len(y_train)} = {25*len(y_train)} predictions")
print()

print("--- TRAINING (25 epochs) ---")
random.seed(42)
train_idx = list(range(len(y_train)))
for epoch in range(25):
    random.shuffle(train_idx)
    for idx in train_idx:
        inputs = to_bool3(X_train[idx], medians)
        truth = label_to_bool3(y_train[idx])
        net.train_step(inputs, truth)
    alive = sum(1 for c in net.cells if c.budget > 0)
    if (epoch + 1) % 5 == 0:
        c_ok = sum(1 for h in net.history[-len(y_train):] if h['correct'])
        print(f"  Epoch {epoch+1}: {alive}/{n_cells} alive, acc={100*c_ok/len(y_train):.1f}%")

print(f"\nTotal: {len(net.history)} training steps.")
print()

# ============================================================================
# EVALUATE
# ============================================================================

def evaluate(net, X_eval, y_eval, medians):
    correct, wrong, unknown = 0, 0, 0
    details = []
    eval_net = deepcopy(net)
    for i in range(len(y_eval)):
        inputs = to_bool3(X_eval[i], medians)
        truth = label_to_bool3(y_eval[i])
        preds, costs, verdict, vt, vf, vu = eval_net.forward(inputs)
        if verdict == truth: correct += 1
        elif verdict == Bool3.BUnknown: unknown += 1
        else: wrong += 1
        details.append({
            'truth': truth.value, 'verdict': verdict.value,
            'correct': verdict == truth, 'votes': (vt, vf, vu),
        })
    return correct, wrong, unknown, details

print("--- TRAIN SET ---")
tr_c, tr_w, tr_u, _ = evaluate(net, X_train, y_train, medians)
print(f"Correct: {tr_c}/{len(y_train)} ({100*tr_c/len(y_train):.1f}%)")
print(f"Wrong: {tr_w}, Unknown: {tr_u}")
print()

print("--- TEST SET (unseen) ---")
te_c, te_w, te_u, test_details = evaluate(net, X_test, y_test, medians)
print(f"Correct: {te_c}/{len(y_test)} ({100*te_c/len(y_test):.1f}%)")
print(f"Wrong: {te_w}")
print(f"Unknown: {te_u} (honest 'need more tests')")
print()

# Cell analysis
alive_cells = [(i, c) for i, c in enumerate(net.cells) if c.budget > 0]
dead_cells = [(i, c) for i, c in enumerate(net.cells) if c.budget <= 0]
print(f"--- CELL FATE ---")
print(f"Alive: {len(alive_cells)}/{n_cells}")
for i, c in alive_cells:
    ratio = f"{c.correct_count}/{c.correct_count+c.wrong_count}" if c.correct_count+c.wrong_count > 0 else "0/0"
    print(f"  [{i:2d}] {strategy_labels[i]:12s}: budget={c.budget:8d}  correct={ratio}")
print(f"Dead: {len(dead_cells)}/{n_cells}")
for i, c in dead_cells:
    ratio = f"{c.correct_count}/{c.correct_count+c.wrong_count}" if c.correct_count+c.wrong_count > 0 else "0/0"
    print(f"  [{i:2d}] {strategy_labels[i]:12s}: heat={c.heat:8d}  correct={ratio} ☠")
print()

# Errors
print("--- TEST ERRORS (first 15) ---")
ec = 0
for j, d in enumerate(test_details):
    if not d['correct']:
        actual = 'malignant' if d['truth'] == 'T' else 'benign'
        pred = {'T': 'malignant', 'F': 'benign', '?': 'UNKNOWN'}[d['verdict']]
        mark = '??' if d['verdict'] == '?' else 'WRONG'
        print(f"  Patient {j}: actual={actual} pred={pred} votes={d['votes']} [{mark}]")
        ec += 1
        if ec >= 15: break

# ============================================================================
# VISUALIZATION
# ============================================================================

fig = plt.figure(figsize=(22, 28), facecolor='#08080e')
gs = gridspec.GridSpec(4, 2, hspace=0.35, wspace=0.3,
                       left=0.07, right=0.96, top=0.95, bottom=0.04)

clrs = ['#ff6b6b', '#ff8a8a', '#6bcb77', '#8dde88',
        '#ffd93d', '#ffe066', '#4d96ff', '#7ab3ff',
        '#e879f9', '#f0a0ff', '#59c1bd', '#f97316',
        '#94a3b8', '#ff8fb1', '#a66cff', '#34d399']
bg = '#08080e'
gc = '#151525'
tc = '#d0d0d0'
plt.rcParams.update({'text.color': tc, 'axes.labelcolor': tc,
                     'xtick.color': '#888', 'ytick.color': '#888', 'axes.edgecolor': '#333'})

fig.suptitle('VOID Predictive Processing — Friston/Clark — No Fractions — Pure Fin',
             fontsize=16, color='#ffffff', fontweight='bold', y=0.98)

h = net.history
steps = list(range(len(h)))

# 1. FREE ENERGY (budget)
ax1 = fig.add_subplot(gs[0, 0])
ax1.set_facecolor(bg)
for i in range(n_cells):
    b = [s['budgets'][i] for s in h]
    ax1.plot(steps, b, color=clrs[i], alpha=0.75, linewidth=1.1, label=strategy_labels[i])
ax1.axhline(y=0, color='#ff0000', linestyle='-', alpha=0.5, linewidth=2)
ax1.set_title('FREE ENERGY (budget) — good predictors survive', color='#fff', fontsize=12, pad=8)
ax1.set_xlabel('training step'); ax1.set_ylabel('free energy')
ax1.legend(fontsize=5.5, ncol=4, loc='upper left', facecolor='#111', edgecolor='#333')
ax1.grid(True, color=gc, alpha=0.5)

# 2. ACCURACY
ax2 = fig.add_subplot(gs[0, 1])
ax2.set_facecolor(bg)
window = 50
r_acc = [sum(1 if s['correct'] else 0 for s in h[max(0,i-window+1):i+1]) / min(i+1, window) for i in range(len(h))]
r_unk = [sum(1 if s['verdict']=='?' else 0 for s in h[max(0,i-window+1):i+1]) / min(i+1, window) for i in range(len(h))]
r_wrg = [sum(1 if (not s['correct'] and s['verdict']!='?') else 0 for s in h[max(0,i-window+1):i+1]) / min(i+1, window) for i in range(len(h))]
ax2.fill_between(steps, r_acc, color='#6bcb77', alpha=0.12)
ax2.plot(steps, r_acc, color='#6bcb77', linewidth=2, label='Correct')
ax2.plot(steps, r_unk, color='#ffd93d', linewidth=2, label='Unknown (honest)')
ax2.plot(steps, r_wrg, color='#ff6b6b', linewidth=2, label='Wrong')
ax2.set_title(f'PREDICTION ACCURACY — rolling {window}', color='#fff', fontsize=12, pad=8)
ax2.legend(fontsize=9, facecolor='#111', edgecolor='#333')
ax2.set_ylim(-0.05, 1.05); ax2.grid(True, color=gc, alpha=0.5)

# 3. ALIVE
ax3 = fig.add_subplot(gs[1, 0])
ax3.set_facecolor(bg)
ac = [s['alive_count'] for s in h]
ax3.fill_between(steps, ac, color='#6bcb77', alpha=0.15)
ax3.plot(steps, ac, color='#6bcb77', linewidth=2)
ax3.set_title('SURVIVING MODELS — natural selection by prediction', color='#fff', fontsize=12, pad=8)
ax3.set_ylim(0, n_cells + 1)
ax3.text(0, n_cells + 0.3, f'started: {n_cells}', fontsize=8, color='#888')
ax3.text(len(steps)*0.7, max(1, ac[-1]) + 0.3, f'survived: {ac[-1]}', fontsize=9,
         color='#6bcb77', fontweight='bold')
ax3.grid(True, color=gc, alpha=0.5)

# 4. VOTES
ax4 = fig.add_subplot(gs[1, 1])
ax4.set_facecolor(bg)
vt = [s['votes'][0] for s in h]; vf = [s['votes'][1] for s in h]; vu = [s['votes'][2] for s in h]
ax4.stackplot(steps, vt, vf, vu, colors=['#6bcb77', '#ff6b6b', '#555577'],
              labels=['BTrue (malig)', 'BFalse (benign)', 'BUnknown'], alpha=0.65)
ax4.set_title('PREDICTIONS — three-valued per patient', color='#fff', fontsize=12, pad=8)
ax4.legend(fontsize=8, loc='upper right', facecolor='#111', edgecolor='#333')
ax4.grid(True, color=gc, alpha=0.3)

# 5. CELL FATE bar chart
ax5 = fig.add_subplot(gs[2, 0])
ax5.set_facecolor(bg)
fb = [c.budget for c in net.cells]
fh = [c.heat for c in net.cells]
x = range(n_cells)
ax5.bar(x, fb, 0.4, color=[clrs[i] if fb[i] > 0 else '#333' for i in range(n_cells)], alpha=0.8, label='budget (free energy)')
ax5.bar([i+0.4 for i in x], fh, 0.4, color=['#553333']*n_cells, alpha=0.5, label='heat (entropy)')
ax5.set_title('CELL FATE — free energy vs entropy', color='#fff', fontsize=12, pad=8)
ax5.set_xticks(range(n_cells))
ax5.set_xticklabels([strategy_labels[i] for i in range(n_cells)], fontsize=5.5, rotation=45, ha='right')
ax5.legend(fontsize=8, facecolor='#111', edgecolor='#333')
ax5.grid(True, color=gc, alpha=0.3, axis='y')

# 6. SUMMARY
ax6 = fig.add_subplot(gs[2, 1])
ax6.set_facecolor(bg); ax6.axis('off')
summary = "PREDICTIVE PROCESSING RESULTS\n"
summary += "=" * 44 + "\n\n"
summary += "MODEL (Friston/Clark)\n"
summary += "  Each cell PREDICTS, doesn't react\n"
summary += "  Evidence FOR (BTrue) + AGAINST (BFalse)\n"
summary += "  Prediction error = surprise = cost\n"
summary += "  Budget = free energy\n"
summary += "  Good predictors survive\n\n"
summary += "NO FRACTIONS\n"
summary += "  Weights = Fin values (integers)\n"
summary += "  Compare = le_fin_b3 (structural)\n"
summary += "  No num/den, no cross-multiply\n\n"
summary += f"TRAIN ({len(y_train)} patients)\n"
summary += f"  Correct: {tr_c} ({100*tr_c/len(y_train):.1f}%)\n"
summary += f"  Wrong: {tr_w}, Unknown: {tr_u}\n\n"
summary += f"TEST ({len(y_test)} unseen)\n"
summary += f"  Correct: {te_c} ({100*te_c/len(y_test):.1f}%)\n"
summary += f"  Wrong: {te_w}, Unknown: {te_u}\n\n"
summary += f"SELECTION\n"
summary += f"  Started: {n_cells} | Alive: {len(alive_cells)} | Dead: {len(dead_cells)}\n"
ax6.text(0.03, 0.97, summary, transform=ax6.transAxes, fontsize=9.5, fontfamily='monospace',
         color=tc, verticalalignment='top',
         bbox=dict(boxstyle='round,pad=0.6', facecolor='#0e0e1a', edgecolor='#2a2a4a'))

# 7. HEAT (entropy)
ax7 = fig.add_subplot(gs[3, 0])
ax7.set_facecolor(bg)
for i in range(n_cells):
    hs = [s['heats'][i] for s in h]
    ax7.plot(steps, hs, color=clrs[i], alpha=0.7, linewidth=1)
ax7.set_title('ENTROPY — irreversible prediction cost', color='#fff', fontsize=12, pad=8)
ax7.grid(True, color=gc, alpha=0.5)

# 8. PREDICTION QUALITY per strategy
ax8 = fig.add_subplot(gs[3, 1])
ax8.set_facecolor(bg)
ratios = []
for c in net.cells:
    total = c.correct_count + c.wrong_count
    ratios.append(c.correct_count / total if total > 0 else 0)
bars = ax8.bar(range(n_cells), ratios, color=[clrs[i] for i in range(n_cells)], alpha=0.8)
ax8.axhline(y=0.5, color='#ff6b6b', linestyle='--', alpha=0.5, label='chance')
ax8.set_title('PREDICTION QUALITY — correct / total per cell', color='#fff', fontsize=12, pad=8)
ax8.set_xticks(range(n_cells))
ax8.set_xticklabels([strategy_labels[i] for i in range(n_cells)], fontsize=5.5, rotation=45, ha='right')
ax8.set_ylim(0, 1.05)
ax8.legend(fontsize=8, facecolor='#111', edgecolor='#333')
ax8.grid(True, color=gc, alpha=0.3, axis='y')

plt.savefig('/mnt/user-data/outputs/void_predictive_network.png', dpi=150, facecolor=bg)
plt.close()
print("\nSaved: /mnt/user-data/outputs/void_predictive_network.png")
