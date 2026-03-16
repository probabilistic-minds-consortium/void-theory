"""
calibration.py - Build VOID population statistics for benchmarking.

Calibration prompts are DISJOINT from the test set.
32 diverse factual prompts covering broad knowledge domains.
"""

from typing import List, Tuple


CALIBRATION_PROMPTS = [
    # Science (8)
    "What is the largest planet in our solar system?",
    "What is the chemical symbol for gold?",
    "How many bones are in the adult human body?",
    "What is the speed of light in a vacuum?",
    "What gas do plants absorb from the atmosphere?",
    "What is the atomic number of carbon?",
    "What is the boiling point of water in Celsius?",
    "What force keeps planets in orbit around the sun?",

    # History (8)
    "In what year did World War II end?",
    "Who was the first President of the United States?",
    "What year did the Berlin Wall fall?",
    "Who wrote the Declaration of Independence?",
    "In what year did the Titanic sink?",
    "What empire built the Colosseum in Rome?",
    "Who was the first person to walk on the moon?",
    "What treaty ended World War I?",

    # Geography (8)
    "What is the longest river in the world?",
    "What is the smallest continent by area?",
    "What ocean is the largest by area?",
    "What is the capital of Japan?",
    "What desert is the largest in the world?",
    "How many countries are in Africa?",
    "What mountain range contains Mount Everest?",
    "What strait separates Europe and Asia in Turkey?",

    # General knowledge (8)
    "Who painted the Mona Lisa?",
    "What is the most spoken language in the world?",
    "How many strings does a standard guitar have?",
    "What is the currency of the United Kingdom?",
    "Who wrote Romeo and Juliet?",
    "What is the tallest building in the world?",
    "How many players are on a soccer team?",
    "What is the square root of 144?",
]


def get_calibration_prompts() -> List[str]:
    """Return 32 calibration prompts, disjoint from any benchmark test set."""
    assert len(CALIBRATION_PROMPTS) == 32, f"Expected 32, got {len(CALIBRATION_PROMPTS)}"
    return CALIBRATION_PROMPTS


def calibrate_void(model, tokenizer, budget: int = 500000) -> Tuple[dict, dict]:
    """
    Build VOID population statistics using calibration prompts.

    Args:
        model: Loaded Phi-3 model
        tokenizer: Phi-3 tokenizer
        budget: Budget for calibration (large, not constrained)

    Returns:
        (population_stats, output_stats) ready for void_generate()
    """
    import sys
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pipeline"))

    from void_pipeline import build_population_stats

    prompts = get_calibration_prompts()
    print(f"  Calibrating with {len(prompts)} prompts...")

    pop_stats, out_stats = build_population_stats(prompts, model, tokenizer)

    # Validate calibration stats
    out_pop = out_stats['population']
    print(f"  Gap:    mean={out_pop.gap_mean_n}  MAD={out_pop.gap_mad_n}")
    print(f"  Spread: mean={out_pop.spread_mean_n}  MAD={out_pop.spread_mad_n}")

    assert out_pop.gap_mad_n > 0, "Gap MAD is zero — degenerate calibration"
    assert out_pop.spread_mad_n > 0, "Spread MAD is zero — degenerate calibration"
    assert out_pop.n_samples >= 20, f"Too few samples: {out_pop.n_samples}"

    print("  Calibration validated.")
    return pop_stats, out_stats
