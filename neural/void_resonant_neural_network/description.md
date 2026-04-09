
```markdown
# VOID Resonant Ensemble — Detailed Design

---

## 1. WHAT THIS NETWORK IS FOR

Binary classification: **pattern recognition in tabular data**.

This is not a convolutional network (for images) or a recurrent one (for sequences). It is an **ensemble of pattern detectors**, each responding to a different "type" of input data. Detectors that consistently identify patterns correctly survive. Detectors that are wrong die.

Applications:
- Medical diagnostics (Breast Cancer, Heart Disease, Diabetes)
- Anomaly detection (fraud detection, intrusion detection)
- Any problem where **subtypes** exist within the data (different tumor types, different fraud schemes)

Resonance is crucial precisely for problems involving subtypes: different cells specialize in recognizing different subtypes, rather than relying on a single model for everything.

---

## 2. DATASET

**Wisconsin Breast Cancer** (sklearn) — 569 samples, 30 features, 2 classes.

Why this one:
- Previous attempts achieved ~65% → a clear benchmark to beat
- The data contains natural subtypes (different types of malignant tumors)
- 30 features of varying quality (MI from 0.01 to 0.7) — ideal for testing selective activation
- Known baselines: Random Forest ~96%, Logistic Regression ~97%

Realistic target with frozen weights and thermodynamic selection: **80-90%**.

Why not 95%+: frozen weights impose a limitation. However, VOID does not claim to replace gradients — it claims to provide **honest epistemology** where uncertainty is explicit.

---

## 3. ARCHITECTURE — ResonantCell

```python
@dataclass
class ResonantCell:
    # === FROZEN (epistemology — never change) ===
    w_for:      List[FinProb]   # weights for the "yes" hypothesis (len = n_features)
    w_against:  List[FinProb]   # weights for the "no" hypothesis (len = n_features)
    frequency:  FinProb         # characteristic frequency

    # === VARIABLE (thermodynamics — change every cycle) ===
    amplitude:  FinProb         # current resonance strength (REPUTATION)
    budget:     int             # Fin — remaining budget
    heat:       int             # Fin — accumulated heat

```

### What is frozen and what is not:

| Field | Type | Frozen? | Role |
| --- | --- | --- | --- |
| w_for | List[FinProb] | **YES** | "who am I" — what patterns I recognize |
| w_against | List[FinProb] | **YES** | "what I fear" — what patterns I reject |
| frequency | FinProb | **YES** | "what I respond to" — input filter |
| amplitude | FinProb | **NO** | "how much I am believed" — REPUTATION |
| budget | Fin | **NO** | "how much I have left" — survivability |
| heat | Fin | **NO** | "how much I have done" — past |

**Key observation**: weights (w_for, w_against, frequency) are FROZEN. But **amplitude** is not a weight — it is the **cell's reputation**, emergent from the history of interactions. Amplitude changes through:

* Constructive resonance (increase)
* Destructive resonance (decrease)
* Universal damping (entropic decay)
* Credit propagation (reward for accuracy)

This does not violate the "frozen weights" axiom because amplitude is not a parameter of a generative model — it is a measure of **thermodynamic success**.

---

## 4. CELL INITIALIZATION

### 4.1 Weights (frozen forever)

```python
def init_cell(cell_id, n_features, weight_denominator=16):
    # Random weights from FinProb in (0,1)
    w_for = [(random(1, d-1), d) for _ in range(n_features)]
    w_against = [(random(1, d-1), d) for _ in range(n_features)]
    ...

```

But NOT purely random. Population diversity is critical:

**"Committee of Experts" Strategy:**

```
Cells  0-7:   strong weights on features with highest MI (BEST)
Cells  8-15:  strong weights on average MI features (GOOD)
Cells 16-23:  strong weights on weak features (WEAK)
Cells 24-31:  even weights (BALANCED)
Cells 32-39:  asymmetrical w_for ≠ w_against (CROSS)
Cells 40-47:  inverted — noise for, signal against (CONTRARIAN)
Cells 48-55:  random
Cells 56-63:  random with a different seed

```

64 cells. None is "better" at the start — selection will decide.

### 4.2 Frequency (frozen)

Cell frequency = **summary of its weight profile**:

```python
def compute_frequency(w_for, w_against):
    # Frequency = "center of gravity" of weights in the feature space
    # Cell with strong weights on features 0-5 → low frequency
    # Cell with strong weights on features 25-29 → high frequency
    weighted_sum = 0
    total_weight = 0
    for i, (wf, wa) in enumerate(zip(w_for, w_against)):
        w = finprob_to_approx(wf) + finprob_to_approx(wa)
        weighted_sum += i * w
        total_weight += w
    # Normalize to (0,1)
    center = weighted_sum / (total_weight * n_features) if total_weight > 0 else 0.5
    return to_finprob(center)  # (num, den) in (0,1)

```

Cell focused on low-index features → low frequency.
Cell focused on high-index features → high frequency.
Evenly balanced cell → frequency ≈ 0.5.

### 4.3 Amplitude (initial)

All cells start with an amplitude of `half = (1, 2)`.
Tabula rasa — none has a reputation at the start.

### 4.4 Budget

All cells start with an identical budget, e.g., 100000 ticks.
Enough for ~25 epochs × 455 samples × ~50 ticks/activation.

---

## 5. INPUT FREQUENCY

Each input has its own "frequency" — a summary of WHICH features are active:

```python
def input_frequency(signals: List[FinProb]):
    # Signals are FinProb[30] — encoded features
    # Input frequency = weighted average of active feature positions
    weighted_sum = 0
    total_weight = 0
    for i, s in enumerate(signals):
        w = finprob_to_approx(s)  # feature strength
        weighted_sum += i * w
        total_weight += w
    center = weighted_sum / (total_weight * len(signals)) if total_weight > 0 else 0.5
    return to_finprob(center)

```

Patient with dominant "worst" features (indices 20-29) → high frequency.
Patient with dominant "mean" features (indices 0-9) → low frequency.

---

## 6. RESONANCE — who activates

```python
def is_resonant(cell, input_freq, threshold=(1, 4)):
    # cell.frequency ≈ input_freq ?
    dist = finprob_dist(cell.frequency, input_freq, budget)
    return finprob_le(dist, threshold, budget)
    # Cost: ~3 ticks (dist + compare)

```

Resonance threshold `threshold = 1/4` means: the cell activates if its frequency is within ±0.25 of the input frequency.

Effect: **for each input, ~30-50% of cells activate** (those whose weight profile matches the profile of active features). The rest remain silent — saving budget.

This is a natural **attention mechanism**: the network automatically focuses resources on cells that "understand" this type of input.

---

## 7. FORWARD PASS — activating resonant cells

```python
def activate_cell(cell, signals: List[FinProb], budget):
    """Cell activation — dual accumulator."""
    acc_for = ZERO_PROB      # (0, 1)
    acc_against = ZERO_PROB  # (0, 1)
    heat = 0

    for i, s in enumerate(signals):
        if budget <= 0:
            break

        # Signal categorization at the 1/2 boundary
        cmp, budget, h = prob_le_b3(HALF, s, budget)
        heat += h

        if cmp == BTrue:
            # s > 1/2 → evidence FOR → accumulate w_for[i]
            acc_for, budget, h = add_prob_heat(acc_for, cell.w_for[i], budget)
            heat += h
        elif cmp == BFalse:
            # s < 1/2 → evidence AGAINST → accumulate w_against[i]
            acc_against, budget, h = add_prob_heat(acc_against, cell.w_against[i], budget)
            heat += h
        # BUnknown → skip (lack of information)

    # Decision: compare accumulators
    if acc_for == ZERO_PROB and acc_against == ZERO_PROB:
        return HALF, budget, heat  # neutral — no evidence

    cmp, budget, h = prob_le_b3(acc_against, acc_for, budget)
    heat += h

    if cmp == BTrue:
        # acc_for >= acc_against → positive signal
        # output = acc_for / (acc_for + acc_against)
        total, budget, h = add_prob_heat(acc_for, acc_against, budget)
        heat += h
        output = (fst(acc_for) * snd(total), fst(total) * snd(acc_for))
        # Simplification: output closer to 1.0
        return output, budget, heat
    else:
        # acc_against > acc_for → negative signal
        total, budget, h = add_prob_heat(acc_for, acc_against, budget)
        heat += h
        output = (fst(acc_against) * snd(total), fst(total) * snd(acc_against))
        # Invert: output closer to 0.0
        complement = (fst(total) - fst(output), snd(total))
        return complement, budget, heat

```

Result: **FinProb** in (0,1).

* Close to 1.0 = cell says "YES" (malignant)
* Close to 0.0 = cell says "NO" (benign)
* Close to 0.5 = cell does not know

---

## 8. RESONANCE CASCADE — the heart of the architecture

After cell activation, their signals **interfere with each other**:

```python
def resonance_cascade(active_cells, signals, max_rounds=5, budget):
    """Cascade: resonating cells mutually amplify/dampen each other."""

    # Step 1: activate all resonating cells
    outputs = {}
    for cell in active_cells:
        out, budget, heat = activate_cell(cell, signals, budget)
        outputs[cell.id] = out
        cell.budget -= heat  # WRITE: activation cost
        cell.heat += heat

    # Step 2: interference cascade (max_rounds)
    for round in range(max_rounds):
        if budget <= 0:
            break  # budget exhaustion stops the cascade

        changes = 0
        for i, cell_a in enumerate(active_cells):
            for j, cell_b in enumerate(active_cells):
                if i >= j:
                    continue
                if budget <= 0:
                    break

                out_a = outputs[cell_a.id]
                out_b = outputs[cell_b.id]

                # Do both cells agree?
                a_says_yes = finprob_gt(out_a, HALF)
                b_says_yes = finprob_gt(out_b, HALF)

                budget -= 1  # comparison cost
                heat += 1

                if a_says_yes == b_says_yes:
                    # === AGREEMENT → CONSTRUCTIVE RESONANCE ===
                    # Both amplitudes increase (FinProb: numerator += 1)
                    cell_a.amplitude = boost_amplitude(cell_a.amplitude, budget)
                    cell_b.amplitude = boost_amplitude(cell_b.amplitude, budget)
                    budget -= 2; heat += 2  # cost of two WRITEs
                    changes += 1
                else:
                    # === DISAGREEMENT → DESTRUCTIVE RESONANCE ===
                    # Both amplitudes decrease (FinProb: numerator -= 1)
                    cell_a.amplitude = decay_amplitude(cell_a.amplitude)
                    cell_b.amplitude = decay_amplitude(cell_b.amplitude)
                    changes += 1

        if changes == 0:
            break  # convergence — nothing changed

    return outputs, budget

```

### What the cascade does:

**Round 1**: Cells A and B agree → both amplified. C and D disagree → both dampened.
**Round 2**: A and B (now stronger) still agree → even stronger. C and D (dampened) exert less influence.
**Round 3**: Convergence — strong cells dominate, weak ones are suppressed.

This is **consensus through physics**, not a voting algorithm.

### Cascade limitations:

1. `max_rounds` — parameter (e.g., 5), not infinity
2. Budget — if exhausted, the cascade stops
3. Convergence — if nothing changes, it ends

---

## 9. VERDICT — network decision

```python
def verdict(active_cells, outputs, budget):
    """Amplitude-weighted voting."""

    # Only cells with amplitude > minimal_threshold vote
    voters = [(c, outputs[c.id]) for c in active_cells
              if finprob_gt(c.amplitude, MINIMAL_AMP)]

    if not voters:
        return BUnknown, ZERO_PROB  # nobody knows

    # Votes weighted by amplitude
    weight_for = ZERO_PROB     # sum of amplitudes of cells saying "yes"
    weight_against = ZERO_PROB # sum of amplitudes of cells saying "no"
    weight_unknown = ZERO_PROB

    for cell, out in voters:
        if finprob_gt(out, HALF_PLUS):     # > 0.55 → "yes"
            weight_for = add_prob(weight_for, cell.amplitude, budget)
        elif finprob_lt(out, HALF_MINUS):  # < 0.45 → "no"
            weight_against = add_prob(weight_against, cell.amplitude, budget)
        else:
            weight_unknown = add_prob(weight_unknown, cell.amplitude, budget)

    # VOID Rules (from void_neural_theory.v):
    total_known = add_prob(weight_for, weight_against, budget)
    if finprob_le(total_known, weight_unknown):
        return BUnknown, ZERO_PROB  # majority doesn't know

    if finprob_gt(weight_for, weight_against):
        confidence = weight_for / (weight_for + weight_against)  # FinProb
        return BTrue, confidence
    elif finprob_gt(weight_against, weight_for):
        confidence = weight_against / (weight_for + weight_against)
        return BFalse, confidence
    else:
        return BUnknown, ZERO_PROB  # tie → we don't know, NO coin tossing

```

### Key difference from a feedforward (pancake) network:

In a feedforward network: each cell votes with a weight of 1.
In resonance: each cell votes with a weight = **amplitude**.

Amplitude is learned through the history of interactions.
A cell that is consistently wrong → low amplitude → its vote doesn't count.
A cell that is consistently right → high amplitude → dominates the verdict.

**THIS IS LEARNING.**

---

## 10. LEARNING — FULL MECHANISM

### The problem with previous attempts:

Previous implementations used:

* Erode/constrict on threshold → BUT there is no threshold field
* Backprop-like weight modification → BUT weights are frozen
* Only budget refund/drain → too weak (65% accuracy)

### Solution in the Resonant Ensemble:

Learning occurs through **THREE** independent mechanisms:

#### Mechanism A: CREDIT PROPAGATION (budgetary)

```python
def credit_propagation(cell, cell_output, truth, budget):
    """Standard void credit: refund for accuracy."""
    REFUND_AMOUNT = 3   # ticks of refund for correct prediction

    cell_says_yes = finprob_gt(cell_output, HALF)
    truth_is_yes = (truth == BTrue)

    if is_neutral(cell_output):
        return cell  # honest ignorance → no penalty, no reward

    if cell_says_yes == truth_is_yes:
        # CORRECT PREDICTION → budget refund
        cell.budget += REFUND_AMOUNT
        return cell
    else:
        # WRONG PREDICTION → no refund
        # Drain is PASSIVE — budget has already been spent on activation
        return cell

```

This mechanism alone is too weak. But it works IN TANDEM with the next two.

#### Mechanism B: RESONANT AMPLITUDE MODULATION

This is NEW and specific to the resonant ensemble:

```python
def amplitude_credit(cell, cell_output, truth, cascade_result):
    """Amplitude changes based on accuracy + cascade."""
    BOOST = (1, 8)    # +1/8 for correct prediction
    PENALTY = None    # no explicit penalty — damping is sufficient

    cell_says_yes = finprob_gt(cell_output, HALF)
    truth_is_yes = (truth == BTrue)

    if is_neutral(cell_output):
        return cell  # neutral → amplitude unchanged

    if cell_says_yes == truth_is_yes:
        # CORRECT → boost amplitude
        cell.amplitude = add_prob(cell.amplitude, BOOST, cell.budget)
        cell.budget -= 1  # WRITE costs
        cell.heat += 1
    # WRONG → NO EXPLICIT PENALTY
    # The penalty is implicit:
    #   1. Destructive cascade has already weakened amplitude (Step 8)
    #   2. Damping will lower it further (Step 10c)
    #   3. No budgetary refund (Step 10a)
    # Three simultaneous pressures are sufficient

    return cell

```

#### Mechanism C: UNIVERSAL DAMPING (entropy)

```python
def universal_damping(cells):
    """AFTER EVERY EPOCH: all amplitudes decay."""
    for cell in cells:
        if cell.budget > 0:
            cell.amplitude = decay_amplitude(cell.amplitude)
            # decay: (fs (fs n), d) → (fs n, d)
            # i.e., numerator -= 1 (one step closer to zero)
            cell.budget -= 1  # damping costs
            cell.heat += 1

```

Damping is **unconditional**. Every cell loses amplitude every epoch.
Only cells regularly boosted by constructive resonance + credit maintain amplitude.

### The three selection pressures COMBINED:

```
After each training example:

1. CREDIT (budgetary):
   Correct → +3 budget       | Wrong → +0 budget (passive drain)

2. AMPLITUDE (resonant):
   Correct → +1/8 amplitude  | Wrong → +0 (cascade already lowered it)

3. DAMPING (entropic) — per epoch:
   All → amplitude -= 1 tick

A cell survives if ALL three pressures balance positively:
   budget > 0 AND amplitude > minimal_threshold

```

### Why this works better than refund/drain alone:

| Mechanism | Previously | Now |
| --- | --- | --- |
| Budget | The only learning signal | One of three |
| Amplitude | Did not exist | Cell reputation — weighted vote |
| Cascade | Did not exist | Physical consensus — boosts correct, suppresses wrong |
| Damping | Did not exist | Automatic forgetting — forces relevance |
| Resonance | Did not exist | Attention — cells activate selectively |

Previously: 1 selection mechanism.
Now: 5 interacting mechanisms, each consistent with VOID.

---

## 11. FULL TRAINING CYCLE

```python
for epoch in range(N_EPOCHS):
    for (signals, truth) in training_data:

        # 1. Compute input frequency
        freq = input_frequency(signals)

        # 2. Find resonating cells
        active = [c for c in cells if is_resonant(c, freq) and c.budget > 0]

        if not active:
            continue  # no cell resonates → skip (budget savings!)

        # 3. Forward pass (only active cells)
        outputs = {}
        for cell in active:
            out, budget, heat = activate_cell(cell, signals, cell.budget)
            outputs[cell.id] = out
            cell.budget = budget
            cell.heat += heat

        # 4. Resonance cascade (physical consensus)
        resonance_cascade(active, outputs, max_rounds=3, global_budget)

        # 5. Verdict (amplitude-weighted voting)
        decision, confidence = verdict(active, outputs, global_budget)

        # 6. Credit propagation (budget + amplitude)
        for cell in active:
            credit_propagation(cell, outputs[cell.id], truth)
            amplitude_credit(cell, outputs[cell.id], truth)

    # 7. Damping at the end of the epoch
    universal_damping(cells)

    # 8. Diagnostics
    alive = sum(1 for c in cells if c.budget > 0)
    high_amp = sum(1 for c in cells if finprob_gt(c.amplitude, (1, 4)))
    print(f"Epoch {epoch}: {alive} alive, {high_amp} high-amplitude")

```

---

## 12. WHY AMPLITUDE ≠ WEIGHT MODIFICATION

Weights (w_for, w_against) define **WHAT the cell recognizes** — its epistemological identity.
Frozen → the cell never changes what it "believes" in.

Amplitude defines **HOW MUCH the cell weighs in voting** — its thermodynamic status.
Variable → the cell can gain or lose influence.

Biological analogy:

* Weights = Neuron's DNA (does not change)
* Amplitude = Synaptic strength (changes through use)
* Budget = Metabolic resources (deplete)
* Damping = Natural aging

In VOID theory:

* Weights ∈ FinProb — epistemology (mathematical content)
* Amplitude ∈ FinProb — thermodynamics (maintained pattern)
* Maintaining amplitude COSTS budget (every boost is a WRITE)
* Amplitude decays without sustenance (damping = entropy)
* Pattern = active distinction maintained at the cost of resources

Amplitude is a **pattern** in the sense of void_pattern.v: maintained activity that costs and decays without sustenance.

---

## 13. AXIOM VERIFICATION

For EVERY operation in the network:

| Operation | Type | Cost | Conservation |
| --- | --- | --- | --- |
| Read frequency | READ | 0 | B = B |
| Read amplitude | READ | 0 | B = B |
| Compare freq (resonance) | WRITE | 3 ticks | B = B' + 3 |
| Activation (forward pass) | WRITE | ~30-60 | B = B' + h |
| Compare in cascade | WRITE | 1 tick | B = B' + 1 |
| Boost amplitude | WRITE | 1 tick | B = B' + 1 |
| Decay amplitude (damping) | WRITE | 1 tick | B = B' + 1 |
| Refund budget | ADMIN | 0 | B_cell += refund |
| Verdict | WRITE | ~10 | B = B' + h |

Assertion after every operation: `budget_before == budget_after + heat_generated`

---

## 14. TUNING PARAMETERS

| Parameter | Initial Value | Role |
| --- | --- | --- |
| n_cells | 64 | population size |
| initial_budget | 100000 | starting resources |
| weight_denominator | 16 | FinProb weight precision |
| resonance_threshold | 1/4 | resonance bandwidth |
| max_cascade_rounds | 3 | cascade depth |
| refund_amount | 3 | reward for accuracy (Fin) |
| amplitude_boost | 1/8 | amplitude reward (FinProb) |
| n_epochs | 25 | number of epochs |
| HALF_PLUS | 11/20 | "yes" threshold (0.55) |
| HALF_MINUS | 9/20 | "no" threshold (0.45) |
| MINIMAL_AMP | 1/8 | minimum amplitude to vote |

All parameters are Fin or FinProb. No floats. No infinity.

```

```