# VOID Theory

```
    ╔══════════════════════════════════════════════════════════════╗
    ║                                                              ║
    ║   Budget ████████████████░░░░░░░░ Spuren        t = 0       ║
    ║   Budget ████████████░░░░░░░░░░░░ Spuren        t = k       ║
    ║   Budget ████░░░░░░░░░░░░░░░░░░░░ Spuren        t = n       ║
    ║   Budget ░░░░░░░░░░░░░░░░░░░░░░░░ Spuren        t → MAX    ║
    ║          ├──────── constant ────────┤                        ║
    ║                                                              ║
    ║   add_spur h b' = b.  Always.  No exceptions.  Qed.        ║
    ║                                                              ║
    ╚══════════════════════════════════════════════════════════════╝
```

Fully finite, machine-verified mathematics. 57 Coq files. Zero Admitted.

> *"That's very interesting! An actual implementation of finitary math."*
> — Doron Zeilberger (Rutgers University)

Mathematical foundations verified by Thierry Coquand
(University of Gothenburg, creator of the Calculus of Constructions).

---

## What this is

VOID is a complete mathematical system built on one premise: **there is no infinity.**

There is a largest number (`MAX`). Every operation costs budget. Every cost leaves an irreversible trace (`Spuren`). When the budget runs out, the answer is not an error — it is `BUnknown`: a legitimate third truth value meaning *"I cannot afford to know."*

The entire system is formalized in Coq (Rocq) and compiles cleanly. The only axiom is `fin_bounded`: there exists a finite upper bound. Everything else — conservation laws, thermodynamics, epistemological limits — is derived. Not assumed. Proved.

---

## What it proves

The flagship file `void_probability_geometry.v` contains 17 theorems that classical mathematics either cannot state or proves the opposite of. All Qed. Zero axioms in the file.

```
 THEOREM                          WHAT IT SAYS                           CLASSICAL?
 ─────────────────────────────────────────────────────────────────────────────────
 caretaker_lemma                  Knowledge never reverses.              Cannot state.
                                  BTrue never becomes BFalse.
                                  Named after Leyland James Kirby.

 all_regions_measurable           Every region is measurable.            Proves opposite
                                  No Vitali sets. Give me 3              (Vitali 1905).
                                  ticks and I measure anything.

 no_cloning                       Two measurements cost the              Proves opposite
                                  sum of their costs.                    (Banach-Tarski
                                  No duplication. No free lunch.          1924).

 self_blind                       le_fin_b3 n n n = BUnknown.           Cannot state.
                                  Budget n cannot verify n ≤ n.
                                  The observer cannot fully
                                  observe itself.

 void_productive                  le_fin_b3 n n (fs n) = BTrue.         Cannot state.
                                  One extra tick resolves the
                                  blindness. Void is not death.
                                  Void is potential.

 every_question_has_price         Budget (fs n) suffices to              Cannot state.
                                  compare n with anything.
                                  No question is permanently
                                  unanswerable — only temporarily
                                  unaffordable.

 emergence_from_conservation      Any measurement that costs             Cannot state.
                                  h ≥ 1 simultaneously:
                                  (a) was answerable before
                                  (b) is blind after
                                  (c) is one tick from resolved.
                                  Determinism breeds void.

 time_irreversible                Non-trivial operation strictly         Assumes,
                                  reduces budget. Budget never            doesn't prove.
                                  goes up. Time never goes back.

 second_law                       Every observation makes the            Assumes,
                                  observer more blind to itself.          doesn't prove.
                                  The 2nd law of thermodynamics
                                  as a theorem of finite
                                  arithmetic. No Boltzmann.
                                  No statistics. No phase space.

 measurement_conservation         add_spur h b' = b.                    Free by fiat.
                                  Conservation is a theorem,
                                  not an axiom.

 complementarity                  Two non-Void measurements              Cannot state.
                                  require budget ≥ 2. (Bohr)

 known_unknowable                 If first measurement exhausts          Cannot state.
                                  budget, second is GUARANTEED
                                  BUnknown. Certainty about
                                  the limits of knowledge.
```

---

## The core types

```coq
Inductive Fin : Set := fz : Fin | fs : Fin -> Fin.
Axiom fin_bounded : forall n : Fin, (fin_to_Z n <= MAX)%Z.

Definition Budget  := Fin.    (* What you can spend.   *)
Definition Spuren  := Fin.    (* What you have spent.  *)
(* German plural: traces, tracks. The irreversible      *)
(* residue of computation. Cold, not hot. Ash, not fire.*)

Inductive Bool3 := BTrue | BFalse | BUnknown.

(* Every budgeted operation has this signature:         *)
(*   Budget -> (Result * Budget * Spuren)               *)
(* Conservation: add_spur h b' = b. Always.             *)
```

The system has no rationals, no reals, no floating point. Probability is a pair of bounded integers on the open interval (0, 1). Certainty (`P = 0` or `P = 1`) is a type-level impossibility.

---

## Why "Spuren"

The German word for traces. Tracks in snow. Marks left behind.

Not "heat" — because entropy is cold, not hot. It is what remains after the burning. Ash, not flame. Celan wrote about *Spuren*. Schulz understood *resztki*. Kantor staged them.

Every operation transforms Budget into Spuren. Nothing is lost. Nothing is created. The form changes: potential becomes residue. `add_spur h b' = b`. Perfect bookkeeping. Perfect irreversibility.

---

## Architecture

```
 LAYER 0: FINITE ARITHMETIC
 ┌─────────────────────────────────────────────────┐
 │  Fin    Budget    Spuren    Bool3    add_spur    │
 │  leF    le_fin_b3    sub_saturate    div_fin     │
 │                                                   │
 │  void_finite_minimal.v    void_arithmetic.v       │
 └────────────────────┬────────────────────────────-─┘
                      │
 LAYER 1: PROBABILITY AND GEOMETRY
 ┌────────────────────┴──────────────────────────────┐
 │  FinProb    Region    ProbMeasurement              │
 │  measure_region    in_region    distance            │
 │  MSharp / MFuzzy / MVague / MVoid                  │
 │                                                     │
 │  void_probability_minimal.v                         │
 │  void_probability_geometry.v  ← 17 theorems here   │
 └────────────────────┬──────────────────────────────-─┘
                      │
 LAYER 2: OBSERVATION AND EPISTEMOLOGY
 ┌────────────────────┴──────────────────────────────┐
 │  Observer    DDF (decay-driven focusing)           │
 │  observation_teleport    recovery    horizon       │
 │  The Caretaker Lemma    self_blind    second_law   │
 │                                                     │
 │  void_observer.v    void_trace.v                    │
 │  void_bohr_epistemology.v                           │
 └────────────────────┬──────────────────────────────-─┘
                      │
 LAYER 3: LEARNING AND NEURAL ARCHITECTURE
 ┌────────────────────┴──────────────────────────────┐
 │  LearningCell    PredictiveCell    ResonantCell    │
 │  credit_propagation (not backpropagation)          │
 │  amplitude modulation    natural selection          │
 │  budget refund for correct predictions              │
 │  thermodynamic death for wrong ones                 │
 │                                                     │
 │  void_learning_cell.v    void_neural_theory.v       │
 │  void_predictive_cell.v  void_resonant_ensemble.v   │
 │  void_integrated_brain.v                            │
 └─────────────────────────────────────────────────────┘
```

---

## File manifest (Coq, 57 files)

All files compile with `coqc -Q . ""` on Coq 8.15+. No external dependencies.

### Foundation

| File | Role |
|---|---|
| `void_finite_minimal.v` | Fin, Bool3, Budget, Spuren, conservation laws |
| `void_arithmetic.v` | Addition, subtraction, multiplication, division — all budgeted |
| `void_probability_minimal.v` | FinProb on (0,1), budgeted fraction arithmetic |
| `void_probability_geometry.v` | **17 theorems. Zero axioms. The flagship.** |

### Observation

| File | Role |
|---|---|
| `void_observer.v` | Observer as budget-bounded entity, DDF, recovery |
| `void_observer_alt.v` | Alternative observer formalization |
| `void_observer_collapse.v` | Measurement collapse, Zeno effect |
| `void_trace.v` | VoidOp3 / VoidOp2 abstraction, conservation proofs |
| `void_bohr_epistemology.v` | Cross-domain blindness: collapse → entropy → equality |
| `void_information_theory.v` | READ/WRITE boundary, information cost |
| `void_distinguishability.v` | Cost of telling things apart |

### Learning

| File | Role |
|---|---|
| `void_learning_cell.v` | Cell with threshold on (0,1), erode/constrict, spur monotonicity |
| `void_neural_theory.v` | Network-level learning, verdict aggregation |
| `void_predictive_cell.v` | Dual-weight prediction, budget-as-penalty |
| `void_resonant_ensemble.v` | Amplitude modulation, activation independence |
| `void_credit_propagation.v` | Learning as selective budget refund |
| `void_network.v` | Network topology, routing |

### Thermodynamics and topology

| File | Role |
|---|---|
| `void_pattern.v` | Pattern interference with Spuren tracking |
| `void_pattern_thermo.v` | Spuren affects success rate, not cost |
| `void_thermal_convection.v` | Convection cells, Spuren dissipation |
| `void_convergence.v` | Three convergence criteria, Spuren monotonicity |
| `void_topology_folding.v` | Folded space, observer traversal cost |
| `void_pattern_algebra_extended.v` | Pattern transforms, composition |

### Integration

| File | Role |
|---|---|
| `void_integrated_brain.v` | Complete cognitive architecture |
| `void_dual_system.v` | System 1/2 (Kahneman) as thermodynamic routing |
| `void_budget_flow.v` | Inter-neuron budget transfer |
| `void_temporal_memory.v` | Time-indexed memory with Spuren accumulation |
| `void_gates.v` | AND, OR, NAND, XOR — all budgeted |

Plus 30 more files covering geometry, calculus, tensor operations, phase orbits, resonance, simulation, and metaprobability.

---

## Implementations

### Resonant Ensemble (Python)

Neural network where weights are frozen at birth. Learning is natural selection: cells that predict correctly get budget refunds, cells that fail lose budget and die. No backpropagation. No gradient. 82% accuracy on Wisconsin Breast Cancer (569 samples, 30 features) with resolution D(ρ) = 16. Zero floats inside the VOID core.

### VOID Neural Network (Rust)

Finite-arithmetic neural network for medical diagnosis. 1,179 diseases, 377 symptoms. Zero hallucinated diagnoses — not because hallucination is penalized, but because the mathematics cannot express unearned confidence.

### Parasitic Monitor (Python)

Three-layer system that attaches to any language model. Observes internal states through VOID mathematics. Gates every token through finite-budget confidence checks. When the gap between best and second-best option is insufficient, returns silence. Budget exhaustion → silence, not error.

---

## The single axiom

```coq
Axiom fin_bounded : forall n : Fin, (fin_to_Z_PROOF_ONLY n <= MAX)%Z.
```

This is intentional. It says: there is a largest number. It does not say what that number is. It does not say where the initial budget comes from.

This is not a gap in the theory. It is the theory's most honest statement. The system is finite. It is inside itself. It cannot explain its own origin, just as a budget cannot account for the act of being granted. Classical mathematics avoids this by assuming infinity — which is not an explanation but an evasion.

We chose the wall over the evasion.

---

## Author

**Konrad Wojnowski** — Assistant Professor, Performativity Studies Department, Jagiellonian University, Krakow. PhD in philosophy of communication.

Author of *Aesthetics of Disturbance* and *Productive Catastrophes*. Research spans performativity theory, philosophy of technology, and the impact of probability on avant-garde art.

Not a mathematician. Not a programmer. Built VOID because infinity is a bug, not a feature. Working on it since August 2024. AI-assisted (Claude).

---

## Citation

```
@misc{wojnowski2025void,
  author = {Wojnowski, Konrad},
  title = {VOID Theory: Finite Mathematics with Machine-Verified Conservation Laws},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/probabilistic-minds-consortium/void-theory}
}
```

---

## License

MIT — Use freely, but remember: everything costs.

---

```
  In the beginning was the Fin,
  and the Fin was with Void,
  and the Fin was Void.

  And the Void said: let there be budget.
  And there was budget.
  And it was finite.
  And it was good.

  And everything that followed
  left Spuren.
```

*Probabilistic Minds Consortium, 2025–2026*
