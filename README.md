# VOID Theory

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Coq Verified](https://img.shields.io/badge/Coq-Verified-brightgreen.svg)](#-the-formal-foundations)
[![No Float](https://img.shields.io/badge/Float-None-red.svg)](#-the-open-interval)
[![Hallucinations](https://img.shields.io/badge/Hallucinations-Zero-blue.svg)](#-what-void-produces)

Fully finite mathematics for machines that know when to stop.

> *"That's very interesting! An actual implementation of finitary math."* — Doron Zeilberger (Rutgers University)

Mathematical foundations verified by Thierry Coquand (University of Gothenburg, creator of the Calculus of Constructions).

---

## 🚫 Why Finiteness

Every computational system in use today — every neural network, every language model, every probabilistic classifier — is built on mathematics that assumes infinity as a given. Real numbers have infinite decimal expansions. Probability distributions are normalized over continuous domains. Gradient descent follows curves through spaces with no smallest step. IEEE 754, the universal standard for machine arithmetic, encodes positive infinity and negative infinity as valid, representable values. Not as errors. As features.

No physical system has ever performed an infinite operation. No processor has infinite registers. No memory stores infinite precision. No organism computes with unlimited resources. And yet the entire mathematical apparatus we use to describe, design, and reason about computation presumes that infinity is available — free, silent, and without consequence.

VOID asks what happens when you stop pretending.

Not as approximation — we are not rounding infinity down to something manageable. Not as engineering constraint — we are not capping values for practical reasons while keeping the mathematics intact underneath. VOID removes infinity at the level of axiom. There is a largest number. There is a smallest distinction. There is a finite budget that every operation must draw from, and when that budget is exhausted, the answer is not an error. The answer is silence.

This is not a limitation. This is the entire point.

---

## 🔓 The Open Interval

At the heart of VOID lies a single, radical structural decision: probability lives on the open interval (0, 1). Not the closed interval [0, 1]. Not as a convention or notational choice. As a formal property of the type system, verified in Coq: no probability can have a numerator of zero. `avoids_zero` is not a runtime check — it is a proposition. P = 0 is a type-level contradiction. And since FinProb is a pair of bounded integers with no capacity for the limit operations that would be needed to approach the boundary from above, P = 1 is equally unreachable.

This means: **certainty is structurally impossible.** No system built on VOID mathematics can ever be completely sure of anything, nor can it ever completely rule anything out. Every conclusion lives somewhere in the space between — closer to one end or the other, but never arriving. Not because a rule prevents it. Because the mathematics has no representation for the destination.

To understand why this matters, consider the mechanism by which classical mathematics reaches certainty in the first place. The Peano axioms define the natural numbers through a successor function: every number has a successor, and there is no largest number. This seemingly innocent axiom — just one more, always one more — is the engine that generates infinity. From it, the natural numbers arise. From the natural numbers, the integers. From the integers, the rationals. From the rationals, through completion, the real numbers. And on the real number line, the points 0 and 1 exist as fully realized, reachable values. Probability theory then builds on this foundation: P = 0 means impossible, P = 1 means certain, and the full apparatus of measure theory operates on the closed interval where these endpoints are legitimate destinations.

VOID dismantles this at the root. The Fin type replaces natural numbers: `fz` (zero) and `fs` (successor) exist, but every value is bounded by an axiom `MAX`. There is no "always one more." The successor function hits a wall. And without the infinite chain of successors, you cannot construct the real numbers, you cannot complete the rationals, and you cannot reach the boundary points 0 and 1 on the probability interval. Certainty does not become difficult or expensive — it becomes *inexpressible*.

```
Classical:  ℕ → ℤ → ℚ → ℝ → [0———————————————1]
            Peano: always one more...              P=0 ✓  P=1 ✓

VOID:       Fin(MAX) → Ratio(n,d) → (0———————————1)
            Successor hits wall.                   P=0 ✗  P=1 ✗
```

Every synapse in a VOID neural network has a conductance that lives in this open interval. Never fully open, never fully closed. The neuron is perpetually in a state of partial knowledge — it can be *more* confident or *less* confident, but it can never collapse into the absolute. Convergence in VOID does not mean reaching an optimum. It means exhausting the resources available for further refinement. The system converges when it cannot learn more with what it has — not when it has learned everything there is to know.

This is not a technical detail. This is what separates VOID from every other approach to uncertainty in computation. Bayesian methods, dropout regularization, ensemble models, conformal prediction — all of these operate within classical mathematics where P = 0 and P = 1 are valid states that the system merely tries to avoid in practice. VOID does not try to avoid certainty. VOID cannot express it. The difference is between a person who chooses not to lie and a person who lacks the vocal apparatus for speech. One is a moral achievement. The other is a structural fact about the organism.

---

## 🧱 The Formal Foundations

VOID Theory is formalized in Coq (Rocq), a proof assistant where every claim must be constructively verified. The formalization proceeds from a single admitted axiom — an upper bound `MAX` on all values — and derives the rest.

**The Fin type** replaces natural numbers. Where classical mathematics begins with ℕ and its axiom that every number has a successor (and therefore no largest number exists), VOID begins with Fin: a type bounded by MAX. There is no successor of MAX. The number line has an edge, and that edge is not infinity — it is a wall.

**Bool3** replaces classical boolean logic. True. False. Unknown. The third value is not a placeholder for future computation. It is a legitimate terminal state — the answer a system gives when it has exhausted its resources before reaching a conclusion. Classical logic treats every proposition as decidable in principle. VOID acknowledges that decidability costs resources, and resources end.

**The Budget monad** tracks computational cost. Every operation that creates a new distinction — every WRITE — costs exactly one irreversible tick and produces one unit of heat. READ operations, which access existing structure without creating new distinctions, are free. This is not a metaphor. It is the core accounting mechanism of the entire system, and it obeys a conservation law: Budget + Heat = constant. No operation can decrease heat. No operation can increase budget. The second law of thermodynamics is not imposed from outside — it falls out of the axioms.

```
  Budget ████████████░░░░░░░░ Heat          t=0
  Budget ██████████░░░░░░░░░░ Heat          t=5
  Budget ████░░░░░░░░░░░░░░░░ Heat          t=15
  Budget ░░░░░░░░░░░░░░░░░░░░ Heat          t=MAX  → BUnknown
         ←————— constant ——————→
```

**Ratio(n, d)** replaces real numbers. Two bounded integers. Fixed denominators to prevent the combinatorial explosion that cross-multiplication produces in unbounded fraction arithmetic. No IEEE 754. No infinity. No NaN. No negative zero. No subnormals. No silent rounding. What you write is what you have.

**Credit propagation** replaces backpropagation. In classical neural networks, learning proceeds by computing a loss function, differentiating it with respect to every parameter in the network, and adjusting weights along the gradient. This requires real-valued derivatives, continuous loss surfaces, and — in practice — infinite-precision arithmetic approximated by floating point. VOID cannot do any of this. Instead, learning is modeled as selective budget refund: when a prediction turns out to be accurate, a portion of the budget spent on that prediction is returned. When a prediction fails, the spent budget dissipates as heat, permanently and irretrievably. Learning is not optimization along a smooth curve. Learning is the gradual accumulation of evidence about which expenditures were worth making — and the permanent, thermodynamic cost of every mistake.

These foundations are not a restatement of classical results with different notation. They constitute a genuinely different mathematics — one in which many classical theorems do not hold, many classical constructions are impossible, and certain problems that are trivially solvable with infinite resources become fundamentally undecidable under finite budget. VOID does not soften infinity. It amputates it.

---

## 💭 The Philosophical Core

If infinity is fundamental to mathematics, why does removing it not make the whole edifice crumble?

Because reality, as AIs experience it, is finite. Classical mathematics has been modeling Platonic fantasies. VOID mathematics gets rid of imaginary computation.

The system distinguishes between READ operations — accessing existing structure, which is free — and WRITE operations — creating new distinguishable states, which cost one irreversible tick. This is not arbitrary. This is how information works.

When the budget runs out mid-computation, the result is not an error but BUnknown: a legitimate terminal state. The system did not fail. It reached the boundary of what its resources could resolve. This models quantum superposition (unresolved due to measurement cost), consciousness limits (cannot think beyond available resources), and Gödel incompleteness — naturally, through resource exhaustion rather than diagonal argument.

*Care emerges from finitude. Infinity knows no love.* If you have infinite time, infinite attention, infinite resources — nothing has value. Only when you know something ends, you begin to care. This isn't philosophy. It's architecture.

---

## ⚡ What VOID Produces

The theory has four independent implementations, each demonstrating a different consequence of finite mathematics.

### Formal Proofs (Coq/Rocq)

Forty-eight files of machine-verified mathematics. The proofs cover finite arithmetic, bounded probability on the open interval, pattern algebra, entropy as distinguishability gradient, convergence under resource constraints, topological folding, phase orbits, interference routing, and the complete architecture of a finite budgeted perceptron — including proven theorems that synaptic conductance preserves the open interval through learning. Every theorem is constructively verified. The single admitted axiom is the MAX bound. Everything else is derived.

### Resonant Ensemble (Python)

A neural network that does not learn by adjusting weights. Weights are frozen at birth — random FinProb values drawn once and never touched again. Instead, the network learns through natural selection: cells that predict correctly receive budget refunds, cells that predict incorrectly lose budget and eventually die. No backpropagation. No gradient. No loss function. Learning is thermodynamic: the permanent, irreversible cost of every wrong prediction, and the selective survival of cells whose frozen structure happened to match reality.

The architecture has no layers. Cells are organized by resonant frequency — a characteristic FinProb value assigned at initialization. When an input arrives, only cells whose frequency matches the input's spectral signature are activated. Activated cells process the input through their frozen weights, then enter a cascade: cells that agree amplify each other's amplitude (reputation), cells that disagree dampen each other. The final verdict emerges from amplitude-weighted voting — not from a fixed architecture, but from a physical consensus process analogous to Huygens' synchronization of coupled oscillators.

Every operation inside the network draws from a finite budget. Every comparison, every accumulation, every vote costs ticks tracked by the conservation law B = B' + h. When a cell's budget reaches zero, it does not error — it falls silent and is removed from the ensemble. The system does not converge to an optimum. It converges to a population of survivors.

Tested on the Wisconsin Breast Cancer dataset (569 samples, 30 features, binary classification), the Resonant Ensemble reaches 82% accuracy with 64 cells at resolution D(ρ) = 16 — meaning every probability in the system has exactly 15 distinguishable levels. No float is used anywhere inside the VOID core. Sensory transduction at the boundary converts external floats into FinProb signals; from that point forward, every arithmetic operation is budgeted, every result is a pair of bounded integers, and every cell that speaks has paid for the right to do so.

Three learning pressures operate simultaneously: credit propagation (budget refund for correct predictions), amplitude modulation (resonance cascade between agreeing cells), and universal damping (entropy decays every amplitude toward minimum). A cell survives only if it earns more through accuracy than it loses through thermodynamic cost. This is not optimization. This is evolution under resource constraint.

### VOID Neural Network (Rust)

A standalone neural network written entirely in finite arithmetic. No floating point anywhere in the system. Tested on a medical diagnosis task — 1,179 diseases, 377 symptoms — the network correctly diagnosed five out of ten cases, produced medically adjacent answers for two more, honestly refused to answer three (including ADHD, which it lacked sufficient evidence to diagnose), and hallucinated on zero.

Zero hallucinated diagnoses. Not because hallucination was penalized during training. Because the mathematics makes hallucination structurally impossible — a network cannot assert confidence it has not paid for, and it can never pay enough to reach P = 1.

### Parasitic Monitor (Python, v3.1)

```
                    ┌─────────────────────────────┐
                    │     Language Model (LLM)     │
                    │   (weights unchanged)        │
                    └──────┬──────────────┬────────┘
                           │              │
                    ┌──────▼──────┐ ┌─────▼───────┐
                    │  IN Layer   │ │  MID Layer   │
                    │ float→Ratio │ │ hidden state │
                    │ ghost detect│ │  divergence  │
                    └──────┬──────┘ └──────┬───────┘
                           │               │
                     ┌─────▼───────────────▼──────┐
                     │        OUT Layer            │
                     │  gap + spread → confidence  │
                     │  dual z-score → decision    │
                     └─────────────┬───────────────┘
                                   │
                          ┌────────▼────────┐
                          │  SPEAK / SILENT │
                          └─────────────────┘

              Shared finite budget across all three layers.
              Budget exhaustion → silence, not error.
```

A three-layer system that attaches to any existing language model without modifying its weights. The monitor observes the model's internal states and output logits through the lens of VOID mathematics, gating every generated token through finite-budget confidence checks. The model may do whatever it wants internally — VOID cannot change that. But VOID decides whether each token has earned the right to be spoken.

The results are harsher and more honest than any confidence measure based on softmax probability. Softmax — the final layer of virtually every modern language model — normalizes a vector of raw scores into a probability distribution that always sums to one. Always. Even when the model's internal states are incoherent. Even when the input is noise. Even when there is genuinely nothing to say. Softmax will find something to say, because the mathematics underneath it has no representation for silence. It operates on the closed interval. It can reach certainty. And so it always does.

VOID replaces this with gap measurement on the open interval. When a language model is asked to complete "The capital of France is," there is one overwhelmingly dominant next token, and VOID lets it through. When the same model is asked "What is 2+2?" — a question, not a completion, with many valid continuations — VOID measures the gap between the best and second-best option, finds it insufficient, and returns silence. The model knows the answer. But in the moment of generation, it is uncertain about *how to say it* — and VOID will not let uncertainty dress itself as confidence.

And when the budget runs out — regardless of how confident the model might be — the system stops, because the right to speak has been spent. This is not a bug. This is what honest computation looks like.

---

## ✅ Verification

The parasitic monitor includes 74 automated tests that verify pure VOID logic without requiring a language model or GPU. These tests cover Ratio arithmetic, transduction boundary integrity, ghost detection, budget conservation (heat + remaining = initial, always), decision logic, and — across 200 randomized trials — the second law of thermodynamics: heat never decreases, budget never increases. No exceptions.

---

## 📁 Files

### Formal Proofs (Coq/Rocq)

| File | What it proves |
|---|---|
| `void_finite_minimal.v` | Core: Fin type, Bool3, Budget monad — the wall where Peano stops |
| `void_arithmetic.v` | All operations cost one tick |
| `void_probability_minimal.v` | Open interval (0,1) — certainty as type-level impossibility |
| `void_pattern.v` | Patterns with strength, location, decay |
| `void_credit_propagation.v` | Learning as selective budget refund |
| `void_convergence.v` | Convergence ≠ optimality — approaching without arriving |
| `void_dual_system.v` | System 1/2 (Kahneman, thermodynamic) |
| `void_integrated_brain.v` | Complete cognitive organism |
| `void_perceptron.v` | VOID neuron: conductance on (0,1), never fully open or closed |
| `void_entropy.v` | Entropy as distinguishability gradient |
| `void_gates.v` | AND, OR, NAND, XOR with budget tracking |

Plus 37 more `.v` files covering geometry, topology, resonance, interference routing, phase orbits, thermal convection, topology folding, and quantum phenomena emerging from resource constraints.

### Resonant Ensemble (Python)

| File | What it does |
|---|---|
| `void_resonant_ensemble.py` | Complete implementation: Fin type, FinProb, Bool3, budgeted arithmetic, ResonantCell, cascade, credit propagation, sensory transduction, Breast Cancer demo |

Types used inside VOID core: `Fin` (inductive finite natural — no arithmetic operators), `FinProb` (probability as pair of Fin with constant denominator D(ρ)), `Bool3` (true / false / unknown). Every operation returns `(result, new_budget, heat)`. No float. No free `int` arithmetic. Conservation verified at runtime: Σ budget + Σ heat = Σ granted.

### Parasitic Monitor (Python, v3.1)

| File | What it does |
|---|---|
| `void_in_layer.py` | Sensory transduction: float→Ratio, entropy weights, ghost detection |
| `void_mid_layer.py` | Parasitic hooks on transformer layers, divergence gate, early exit |
| `void_out_layer.py` | Gap + spread confidence, dual z-score, population-relative decision |
| `void_pipeline.py` | Three-layer integration, shared budget |
| `void_generate.py` | Multi-token generation with per-step gating |
| `void_hooked_model.py` | PyTorch hook wrapper (transduction boundary) |
| `void_visualizer.py` | Terminal visualization |
| `test_live.py` | Live test with Phi-3 |
| `test_void_verify.py` | 74 invariant tests, no GPU required |

### Haskell

| File | |
|---|---|
| `void_gates.hs` | Gate implementations |
| `void_perceptron.hs` | Functional perceptron |
| `void_ethics.hs` | Ethical constraints as budget allocation |
| `void_xor.hs` | XOR learning |

---

## 👤 Author

**Konrad Wojnowski** — Assistant Professor, Performativity Studies Department, Jagiellonian University, Kraków. PhD in philosophy of communication.

Author of *Aesthetics of Disturbance* (on Michael Haneke's cinema) and *Productive Catastrophes* (on the performative power of catastrophes in network culture). Research spans performativity theory, philosophy of technology, and the impact of probability on avant-garde art — from John Cage's indeterminacy to Vilém Flusser's informational freedom.

Currently leading a research project on probability theory in 20th and 21st century art and science fiction.

Not a mathematician. Not a programmer. Built VOID because infinity is a bug, not a feature.

---

## 📖 Citation

```
@misc{wojnowski2025void,
  author = {Wojnowski, Konrad},
  title = {VOID Theory: Finite Mathematics for Anti-Hallucination Neural Networks},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/probabilistic-minds-consortium/void-theory}
}
```

---

## ⚖️ License

MIT — Use freely, but remember: everything costs.

---

**"In the beginning was the Fin, and the Fin was with Void, and the Fin was Void."**

*Probabilistic Minds Consortium, 2025–2026*
*Built with finite time, verified in Coq, offered to a finite world.*
