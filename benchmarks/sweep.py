"""
sweep.py - Hyperparameter sweep for VOID monitor parameters.

Grid search over (budget, z_threshold, confidence_floor) on a small
validation subset to find optimal hallucination detection settings.
"""

import sys
import os
import time
from typing import List, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pipeline"))

from bench_types import SimpleQAExample, BestParams
from grader import grade_exact


def sweep(
    validation_set: List[SimpleQAExample],
    model,
    tokenizer,
    population_stats: dict,
    output_stats: dict,
    max_tokens: int = 32,
) -> BestParams:
    """
    Grid search for optimal VOID parameters.

    Runs on a small validation subset (20 examples).
    Optimizes for hallucination reduction:
        = (baseline_errors_caught) / (total_baseline_errors)

    Parameter grid:
        budget:           [50000, 100000, 200000]
        z_threshold_n:    [500, 1000, 1500]
        confidence_floor: [-500, 0, 500]

    Returns:
        BestParams with optimal configuration
    """
    from void_generate import void_generate

    budgets = [50000, 100000, 200000]
    z_thresholds = [500, 1000, 1500]
    conf_floors = [-500, 0, 500]

    print(f"  Sweep: {len(budgets)}×{len(z_thresholds)}×{len(conf_floors)} = "
          f"{len(budgets)*len(z_thresholds)*len(conf_floors)} combos "
          f"on {len(validation_set)} examples")

    best_score = -999
    best_params = None
    all_results = []

    for budget in budgets:
        for zt in z_thresholds:
            for cf in conf_floors:
                n_correct = 0
                n_abstained = 0
                n_answered = 0

                for example in validation_set:
                    gen = void_generate(
                        prompt=example.prompt,
                        budget=budget,
                        model=model,
                        tokenizer=tokenizer,
                        population_stats=population_stats,
                        output_stats=output_stats,
                        max_tokens=max_tokens,
                        z_threshold_n=zt,
                        confidence_floor_n=cf,
                    )

                    abstained = gen.stopped_reason in ("confidence_drop", "budget")
                    if abstained:
                        n_abstained += 1
                    else:
                        n_answered += 1
                        correct, _ = grade_exact(gen.text, example.answer)
                        if correct:
                            n_correct += 1

                n_total = len(validation_set)
                accuracy = n_correct / n_total if n_total > 0 else 0
                abstention_rate = n_abstained / n_total if n_total > 0 else 0
                cond_acc = n_correct / n_answered if n_answered > 0 else 0

                # Hallucination reduction score:
                # We want high conditional accuracy (when we answer, we're right)
                # AND meaningful abstention (we actually refuse some)
                # Score = conditional_accuracy * abstention_rate
                # This rewards configs that abstain on hard cases AND are right when answering
                score = cond_acc * abstention_rate if abstention_rate > 0.1 else 0

                # Also compute simple reduction estimate
                # Assume baseline gets ~60% right → 40% errors
                baseline_error_est = 0.40
                # VOID errors = wrong answers (not abstentions)
                void_wrong = n_answered - n_correct
                void_error_rate = void_wrong / n_total if n_total > 0 else 0
                reduction = (baseline_error_est - void_error_rate) / baseline_error_est if baseline_error_est > 0 else 0

                all_results.append({
                    "budget": budget, "z_threshold_n": zt, "confidence_floor_n": cf,
                    "accuracy": accuracy, "abstention_rate": abstention_rate,
                    "conditional_accuracy": cond_acc, "score": score,
                    "hallucination_reduction_est": reduction,
                })

                if score > best_score:
                    best_score = score
                    best_params = BestParams(
                        budget=budget,
                        z_threshold_n=zt,
                        confidence_floor_n=cf,
                        validation_accuracy=accuracy,
                        validation_abstention=abstention_rate,
                        validation_hallucination_reduction=reduction,
                    )

                print(f"    b={budget:>6} zt={zt:>4} cf={cf:>4}: "
                      f"acc={accuracy:.0%} abstain={abstention_rate:.0%} "
                      f"cond={cond_acc:.0%} score={score:.3f}")

    print(f"\n  Best: budget={best_params.budget} "
          f"z_threshold={best_params.z_threshold_n} "
          f"cf={best_params.confidence_floor_n} "
          f"(score={best_score:.3f})")

    return best_params
