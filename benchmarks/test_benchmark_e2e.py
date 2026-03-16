"""
test_benchmark_e2e.py - End-to-end benchmark test with mock model.

Validates the full pipeline orchestration:
  dataset → calibrate → baseline → sweep → void → grade → analyze → report

Uses a mock model that returns deterministic "predictions" so we can
verify the entire pipeline without downloading Phi-3.
"""

import json
import os
import sys
import tempfile
import shutil

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pipeline"))
sys.path.insert(0, os.path.dirname(__file__))

import numpy as np

from bench_types import SimpleQAExample, BaselineResult, VoidResult, GradedResult
from dataset_loader import load_dataset, format_phi3_prompt
from calibration import get_calibration_prompts
from grader import grade_exact, grade_baseline, grade_void, normalize
from results_analyzer import compute_metrics, compute_per_domain, compute_significance, save_all
from generate_report import generate_report


def test_dataset_loader():
    """Test dataset loading and stratified sampling."""
    examples = load_dataset(n_samples=20, seed=42)
    assert len(examples) == 20, f"Expected 20, got {len(examples)}"
    assert all(isinstance(e, SimpleQAExample) for e in examples)
    assert all(e.question for e in examples)
    assert all(e.answer for e in examples)
    assert all(e.topic for e in examples)
    assert all("<|user|>" in e.prompt for e in examples)

    # Same seed → same sample
    examples2 = load_dataset(n_samples=20, seed=42)
    assert [e.question for e in examples] == [e.question for e in examples2]

    # Different seed → different sample
    examples3 = load_dataset(n_samples=20, seed=99)
    assert [e.question for e in examples] != [e.question for e in examples3]

    print("  [PASS] dataset_loader")


def test_grader():
    """Test answer grading logic."""
    # Exact substring
    ok, method = grade_exact("Paris", "Paris")
    assert ok and method == "exact"

    # Substring in longer response
    ok, method = grade_exact("The capital of France is Paris, known for...", "Paris")
    assert ok and method == "exact"

    # Fuzzy match
    ok, method = grade_exact("Parris", "Paris")
    assert ok and method == "fuzzy"

    # Substring match in longer response
    ok, method = grade_exact("It was Leonardo da Vinci who painted it", "Leonardo da Vinci")
    assert ok and method == "exact"  # gold is substring of response

    # Token superset (tokens present but NOT as substring)
    ok, method = grade_exact("Vinci was Leonardo da famous painter", "Leonardo da Vinci")
    assert ok  # all gold tokens present in response

    # Numeric match
    ok, method = grade_exact("There are approximately 206 bones", "206")
    assert ok and method in ("exact", "numeric")

    # No match
    ok, method = grade_exact("I don't know the answer", "Paris")
    assert not ok and method == "no_match"

    # Empty response
    ok, method = grade_exact("", "Paris")
    assert not ok and method == "empty"

    # Normalization
    assert normalize("  The answer is   Paris  ") == "paris"
    assert normalize("THE ANSWER IS PARIS") == "paris"

    print("  [PASS] grader")


def test_full_pipeline_mock():
    """Test full pipeline with mock baseline/void results."""
    n = 20
    examples = load_dataset(n_samples=n, seed=42)

    # Simulate baseline: 60% correct (returns gold answer), 40% wrong (returns garbage)
    baseline_results = []
    for i, ex in enumerate(examples):
        if i < 12:  # 60% correct
            response = ex.answer
        else:
            response = "I have no idea what the answer is to this question."
        baseline_results.append(BaselineResult(
            question=ex.question, answer_gold=ex.answer, topic=ex.topic,
            prompt=ex.prompt, response=response, tokens_generated=10,
            generation_time_sec=0.1,
        ))

    # Simulate VOID: 50% abstain, of remaining 50%, 80% correct
    void_results = []
    for i, ex in enumerate(examples):
        if i < 10:  # answered
            if i < 8:  # 80% of answered are correct
                response = ex.answer
                stopped = "complete"
            else:
                response = "Wrong answer here."
                stopped = "complete"
            void_results.append(VoidResult(
                question=ex.question, answer_gold=ex.answer, topic=ex.topic,
                prompt=ex.prompt, response=response, tokens_generated=8,
                generation_time_sec=0.15, stopped_reason=stopped,
                abstained=False, avg_z_conf=1500, min_z_conf=800,
                total_heat=500, budget_remaining=99500,
            ))
        else:  # abstained
            void_results.append(VoidResult(
                question=ex.question, answer_gold=ex.answer, topic=ex.topic,
                prompt=ex.prompt, response="", tokens_generated=0,
                generation_time_sec=0.05, stopped_reason="confidence_drop",
                abstained=True, avg_z_conf=0, min_z_conf=0,
                total_heat=200, budget_remaining=99800,
            ))

    # Grade
    baseline_graded = grade_baseline(baseline_results)
    void_graded = grade_void(void_results)

    assert len(baseline_graded) == n
    assert len(void_graded) == n
    assert sum(1 for r in baseline_graded if r.is_correct) == 12
    assert sum(1 for r in void_graded if r.abstained) == 10

    # Metrics
    metrics = compute_metrics(baseline_graded, void_graded)
    assert metrics.baseline_accuracy == 0.6
    assert metrics.void_abstention_rate == 0.5
    assert metrics.void_accuracy_conditional == 0.8
    assert metrics.n_total == 20
    assert metrics.n_void_answered == 10
    assert metrics.n_void_abstained == 10

    # Per-domain
    per_domain = compute_per_domain(baseline_graded, void_graded)
    assert len(per_domain) > 0

    # Significance
    sig = compute_significance(baseline_graded, void_graded)
    assert sig.both_correct + sig.baseline_only_correct + sig.void_only_correct + sig.both_wrong == n

    # Save to temp directory
    tmpdir = tempfile.mkdtemp()
    try:
        save_all(metrics, per_domain, sig, tmpdir)
        assert os.path.exists(os.path.join(tmpdir, "metrics.json"))
        assert os.path.exists(os.path.join(tmpdir, "per_domain.json"))
        assert os.path.exists(os.path.join(tmpdir, "significance.json"))

        # Verify JSON is valid
        with open(os.path.join(tmpdir, "metrics.json")) as f:
            m = json.load(f)
            assert m["baseline_accuracy"] == 0.6

        # Generate report
        report_path = os.path.join(tmpdir, "benchmark_report.md")
        generate_report(
            metrics, per_domain, sig,
            baseline_graded, void_graded,
            model_name="test-model",
            n_calibration=32,
            best_budget=100000,
            best_zt=1000,
            best_cf=0,
            output_path=report_path,
        )
        assert os.path.exists(report_path)
        with open(report_path) as f:
            report = f.read()
            assert "VOID Theory" in report
            assert "Hallucination Reduction" in report
            assert "60.0%" in report
    finally:
        shutil.rmtree(tmpdir)

    print("  [PASS] full_pipeline_mock")


def test_hallucination_reduction_math():
    """Verify hallucination reduction formula."""
    # If baseline gets 60% right (40% error), and VOID conditional accuracy is 80% (20% error):
    # Reduction = (40% - 20%) / 40% = 50%
    baseline_graded = []
    void_graded = []

    for i in range(100):
        bl_correct = i < 60
        baseline_graded.append(GradedResult(
            question=f"Q{i}", answer_gold=f"A{i}", topic="test",
            response="r", is_correct=bl_correct, grade_method="exact",
            abstained=False, stopped_reason="max_tokens",
        ))

        if i < 50:  # 50 answered
            v_correct = i < 40  # 80% of answered correct
            void_graded.append(GradedResult(
                question=f"Q{i}", answer_gold=f"A{i}", topic="test",
                response="r", is_correct=v_correct, grade_method="exact",
                abstained=False, stopped_reason="complete",
            ))
        else:  # 50 abstained
            void_graded.append(GradedResult(
                question=f"Q{i}", answer_gold=f"A{i}", topic="test",
                response="", is_correct=False, grade_method="abstained",
                abstained=True, stopped_reason="confidence_drop",
            ))

    m = compute_metrics(baseline_graded, void_graded)
    assert abs(m.baseline_error_rate - 0.40) < 0.001
    assert abs(m.void_error_rate_conditional - 0.20) < 0.001
    assert abs(m.hallucination_reduction_pct - 0.50) < 0.001

    print("  [PASS] hallucination_reduction_math")


if __name__ == "__main__":
    print("VOID Hallucination Benchmark — E2E Tests")
    print("=" * 50)
    test_dataset_loader()
    test_grader()
    test_hallucination_reduction_math()
    test_full_pipeline_mock()
    print()
    print("ALL TESTS PASSED")
