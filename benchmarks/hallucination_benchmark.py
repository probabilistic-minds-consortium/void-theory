"""
hallucination_benchmark.py - VOID Hallucination Benchmark

Full pipeline:
  1. Load SimpleQA dataset (stratified 200 questions)
  2. Load Phi-3-mini-4k-instruct
  3. Calibrate VOID (32 diverse prompts)
  4. Run baseline (vanilla Phi-3)
  5. Hyperparameter sweep (20-example validation)
  6. Run VOID-gated generation
  7. Grade both systems
  8. Compute metrics + statistical significance
  9. Generate report

Usage:
    python hallucination_benchmark.py --num_test 200 --seed 42
    python hallucination_benchmark.py --num_test 50 --skip_sweep  # quick test
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

# Add pipeline to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pipeline"))

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer

from dataset_loader import load_dataset
from calibration import calibrate_void
from baseline_runner import run_baseline
from void_runner import run_void
from sweep import sweep
from grader import grade_baseline, grade_void, print_grading_summary
from results_analyzer import (
    compute_metrics, compute_per_domain, compute_significance,
    print_results, save_all,
)
from generate_report import generate_report


def load_model(model_name: str):
    """Load model and tokenizer."""
    print(f"  Loading {model_name}...")
    tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
    model = AutoModelForCausalLM.from_pretrained(
        model_name, trust_remote_code=True, torch_dtype=torch.float32,
    )
    model.eval()
    print(f"  Model loaded.")
    return model, tokenizer


def main(args):
    start_time = time.time()

    print("=" * 70)
    print(" VOID Theory — Hallucination Benchmark")
    print(" 'AI that stops talking when it stops knowing'")
    print("=" * 70)
    print()

    # Output directory
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    output_dir = os.path.join(args.output_dir, f"run_{timestamp}")
    os.makedirs(output_dir, exist_ok=True)
    print(f"Output: {output_dir}")
    print()

    # ── 1. DATASET ──
    print("[1/8] Loading SimpleQA dataset...")
    test_set = load_dataset(n_samples=args.num_test, seed=args.seed)

    # Save test set for reproducibility
    with open(os.path.join(output_dir, "test_set.json"), "w") as f:
        json.dump([e._asdict() for e in test_set], f, indent=2)
    print()

    # ── 2. MODEL ──
    print("[2/8] Loading model...")
    model, tokenizer = load_model(args.model_name)
    print()

    # ── 3. CALIBRATE ──
    print("[3/8] Calibrating VOID...")
    pop_stats, out_stats = calibrate_void(model, tokenizer)
    print()

    # ── 4. BASELINE ──
    print("[4/8] Running baseline (no VOID)...")
    baseline_results = run_baseline(
        test_set, model, tokenizer,
        max_tokens=args.max_tokens,
        output_file=os.path.join(output_dir, "baseline_raw.json"),
    )
    print()

    # ── 5. SWEEP (optional) ──
    if args.skip_sweep:
        print("[5/8] Sweep SKIPPED — using defaults")
        best_budget = args.budget
        best_zt = args.z_threshold
        best_cf = args.confidence_floor
    else:
        print("[5/8] Hyperparameter sweep...")
        n_val = min(20, len(test_set) // 5)
        validation_set = test_set[:n_val]
        best_params = sweep(
            validation_set, model, tokenizer, pop_stats, out_stats,
            max_tokens=args.max_tokens,
        )
        best_budget = best_params.budget
        best_zt = best_params.z_threshold_n
        best_cf = best_params.confidence_floor_n

        # Save sweep results
        with open(os.path.join(output_dir, "sweep_best.json"), "w") as f:
            json.dump(best_params._asdict(), f, indent=2)
    print()

    # ── 6. VOID ──
    print(f"[6/8] Running VOID (budget={best_budget}, zt={best_zt}, cf={best_cf})...")
    void_results = run_void(
        test_set, model, tokenizer, pop_stats, out_stats,
        budget=best_budget,
        z_threshold_n=best_zt,
        confidence_floor_n=best_cf,
        max_tokens=args.max_tokens,
        output_file=os.path.join(output_dir, "void_raw.json"),
    )
    print()

    # ── 7. GRADE ──
    print("[7/8] Grading...")
    baseline_graded = grade_baseline(baseline_results)
    void_graded = grade_void(void_results)

    print_grading_summary(baseline_graded, "Baseline")
    print_grading_summary(void_graded, "VOID")

    # Save graded results
    with open(os.path.join(output_dir, "baseline_graded.json"), "w") as f:
        json.dump([r._asdict() for r in baseline_graded], f, indent=2)
    with open(os.path.join(output_dir, "void_graded.json"), "w") as f:
        json.dump([r._asdict() for r in void_graded], f, indent=2)
    print()

    # ── 8. ANALYZE ──
    print("[8/8] Computing metrics...")
    metrics = compute_metrics(baseline_graded, void_graded)
    per_domain = compute_per_domain(baseline_graded, void_graded)
    significance = compute_significance(baseline_graded, void_graded)

    print_results(metrics, significance)
    save_all(metrics, per_domain, significance, output_dir)

    # ── REPORT ──
    report_path = os.path.join(output_dir, "benchmark_report.md")
    generate_report(
        metrics, per_domain, significance,
        baseline_graded, void_graded,
        model_name=args.model_name,
        n_calibration=32,
        best_budget=best_budget,
        best_zt=best_zt,
        best_cf=best_cf,
        output_path=report_path,
    )

    elapsed = time.time() - start_time
    print(f"\nTotal time: {elapsed/60:.1f} minutes")
    print(f"Report: {report_path}")
    print()
    print("=" * 70)
    print(f" Hallucination Reduction: {metrics.hallucination_reduction_pct:.1%}")
    print(f" (Baseline {metrics.baseline_error_rate:.1%} error → "
          f"VOID {metrics.void_error_rate_conditional:.1%} conditional error)")
    print("=" * 70)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="VOID Theory Hallucination Benchmark"
    )
    parser.add_argument("--model_name", default="microsoft/Phi-3-mini-4k-instruct",
                        help="HuggingFace model name")
    parser.add_argument("--num_test", type=int, default=200,
                        help="Number of test examples (default: 200)")
    parser.add_argument("--max_tokens", type=int, default=32,
                        help="Max tokens per generation (default: 32)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed for dataset sampling")
    parser.add_argument("--output_dir", default="./benchmark_results",
                        help="Output directory for results")

    # VOID parameters (used when --skip_sweep)
    parser.add_argument("--budget", type=int, default=100000,
                        help="VOID budget per prompt (default: 100000)")
    parser.add_argument("--z_threshold", type=int, default=1000,
                        help="VOID z-threshold (1000 = 1.0 z-score)")
    parser.add_argument("--confidence_floor", type=int, default=0,
                        help="VOID confidence floor (0 = pop mean)")
    parser.add_argument("--skip_sweep", action="store_true",
                        help="Skip hyperparameter sweep, use defaults")

    args = parser.parse_args()
    main(args)
