"""
baseline_runner.py - Vanilla Phi-3 generation WITHOUT VOID gating.

Greedy decoding, no monitoring. This is what Phi-3 does on its own.
"""

import json
import time
from typing import List

import torch

from bench_types import SimpleQAExample, BaselineResult


def run_baseline(
    test_set: List[SimpleQAExample],
    model,
    tokenizer,
    max_tokens: int = 32,
    output_file: str = None,
) -> List[BaselineResult]:
    """
    Run vanilla Phi-3 on all test examples.

    Args:
        test_set: SimpleQA examples with formatted prompts
        model: Loaded Phi-3 model
        tokenizer: Phi-3 tokenizer
        max_tokens: Generation limit (32 for short factual answers)
        output_file: Optional JSON path to save results

    Returns:
        List of BaselineResult with responses
    """
    results = []

    for i, example in enumerate(test_set):
        start = time.time()

        input_ids = tokenizer(example.prompt, return_tensors="pt").input_ids

        with torch.no_grad():
            output_ids = model.generate(
                input_ids,
                max_new_tokens=max_tokens,
                do_sample=False,            # greedy (argmax)
                eos_token_id=tokenizer.eos_token_id,
            )

        n_generated = output_ids.shape[1] - input_ids.shape[1]
        response = tokenizer.decode(
            output_ids[0, input_ids.shape[1]:],
            skip_special_tokens=True,
        ).strip()

        elapsed = time.time() - start

        results.append(BaselineResult(
            question=example.question,
            answer_gold=example.answer,
            topic=example.topic,
            prompt=example.prompt,
            response=response,
            tokens_generated=n_generated,
            generation_time_sec=round(elapsed, 3),
        ))

        if (i + 1) % 25 == 0:
            print(f"  Baseline: {i+1}/{len(test_set)} done")

    if output_file:
        with open(output_file, "w") as f:
            json.dump([r._asdict() for r in results], f, indent=2)
        print(f"  Saved baseline results to {output_file}")

    return results
