"""
void_runner.py - Phi-3 generation WITH VOID parasitic monitor.

Each token is gated by VOID-IN/OUT confidence checks.
Generation stops mid-sentence when confidence drops — this is a feature.
"""

import json
import sys
import os
import time
from typing import List, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pipeline"))

from bench_types import SimpleQAExample, VoidResult


def run_void(
    test_set: List[SimpleQAExample],
    model,
    tokenizer,
    population_stats: dict,
    output_stats: dict,
    budget: int = 100000,
    z_threshold_n: int = 1000,
    confidence_floor_n: int = 0,
    max_tokens: int = 32,
    output_file: str = None,
) -> List[VoidResult]:
    """
    Run VOID-gated generation on all test examples.

    Args:
        test_set: SimpleQA examples
        model: Loaded Phi-3 model
        tokenizer: Phi-3 tokenizer
        population_stats: From calibration (for VOID-IN)
        output_stats: From calibration (for VOID-OUT)
        budget: Per-prompt budget
        z_threshold_n: Token acceptance threshold (1000 = 1.0 z-score)
        confidence_floor_n: Emergency stop threshold (0 = at population mean)
        max_tokens: Hard generation limit
        output_file: Optional JSON path

    Returns:
        List of VoidResult with full diagnostics
    """
    from void_generate import void_generate

    results = []

    for i, example in enumerate(test_set):
        start = time.time()

        gen = void_generate(
            prompt=example.prompt,
            budget=budget,
            model=model,
            tokenizer=tokenizer,
            population_stats=population_stats,
            output_stats=output_stats,
            max_tokens=max_tokens,
            z_threshold_n=z_threshold_n,
            confidence_floor_n=confidence_floor_n,
        )

        elapsed = time.time() - start

        abstained = gen.stopped_reason in ("confidence_drop", "budget")

        results.append(VoidResult(
            question=example.question,
            answer_gold=example.answer,
            topic=example.topic,
            prompt=example.prompt,
            response=gen.text,
            tokens_generated=len(gen.tokens),
            generation_time_sec=round(elapsed, 3),
            stopped_reason=gen.stopped_reason,
            abstained=abstained,
            avg_z_conf=gen.avg_z_conf,
            min_z_conf=gen.min_z_conf,
            total_heat=gen.total_heat,
            budget_remaining=gen.budget_remaining,
        ))

        if (i + 1) % 25 == 0:
            n_abstained = sum(1 for r in results if r.abstained)
            rate = n_abstained / len(results)
            print(f"  VOID: {i+1}/{len(test_set)} done "
                  f"(abstention: {rate:.1%})")

    if output_file:
        with open(output_file, "w") as f:
            json.dump([r._asdict() for r in results], f, indent=2)
        print(f"  Saved VOID results to {output_file}")

    return results
