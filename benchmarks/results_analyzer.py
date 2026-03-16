"""
results_analyzer.py - Compute metrics and statistical significance.

All metrics are computed from GradedResult lists.
McNemar's test for paired significance (same questions, two systems).
"""

import json
from collections import defaultdict
from typing import List, Dict, Tuple

from bench_types import GradedResult, BenchmarkMetrics, DomainMetrics, SignificanceTest


def compute_metrics(
    baseline_graded: List[GradedResult],
    void_graded: List[GradedResult],
) -> BenchmarkMetrics:
    """
    Compute all benchmark metrics.

    Key metrics:
    - Accuracy (overall and conditional)
    - Abstention rate
    - Hallucination reduction (among answered questions)
    - F1 (precision = correct/answered, recall = correct/total)
    """
    n = len(baseline_graded)
    assert n == len(void_graded), "Baseline and VOID must have same size"

    # Baseline
    bl_correct = sum(1 for r in baseline_graded if r.is_correct)
    bl_acc = bl_correct / n

    # VOID overall
    v_correct = sum(1 for r in void_graded if r.is_correct)
    v_acc = v_correct / n

    # VOID abstention
    v_abstained = sum(1 for r in void_graded if r.abstained)
    v_answered = n - v_abstained
    v_abstention_rate = v_abstained / n
    v_coverage = v_answered / n

    # Conditional accuracy (when VOID answers)
    v_correct_answered = sum(1 for r in void_graded if r.is_correct and not r.abstained)
    v_acc_cond = v_correct_answered / v_answered if v_answered > 0 else 0.0

    # Error rates
    bl_error_rate = 1.0 - bl_acc
    v_error_cond = 1.0 - v_acc_cond

    # Hallucination reduction
    # = reduction in error rate among answered questions vs baseline
    # Conservative: compare VOID conditional error rate to baseline error rate
    if bl_error_rate > 0:
        hall_reduction = (bl_error_rate - v_error_cond) / bl_error_rate
    else:
        hall_reduction = 0.0

    # F1
    v_precision = v_correct_answered / v_answered if v_answered > 0 else 0.0
    v_recall = v_correct / n
    v_f1 = (2 * v_precision * v_recall / (v_precision + v_recall)
            if (v_precision + v_recall) > 0 else 0.0)

    # Efficiency
    bl_tokens = [getattr(r, 'tokens_generated', 0) for r in baseline_graded]
    # For baseline we estimate from response length
    bl_avg_tokens = sum(len(r.response.split()) for r in baseline_graded) / n
    v_avg_tokens = sum(len(r.response.split()) for r in void_graded) / n

    bl_times = [getattr(r, 'generation_time_sec', 0) for r in baseline_graded]
    v_times = [getattr(r, 'generation_time_sec', 0) for r in void_graded]
    bl_avg_time = sum(bl_times) / n if bl_times else 0
    v_avg_time = sum(v_times) / n if v_times else 0

    return BenchmarkMetrics(
        baseline_accuracy=round(bl_acc, 4),
        void_accuracy=round(v_acc, 4),
        accuracy_drop_pp=round(bl_acc - v_acc, 4),
        void_abstention_rate=round(v_abstention_rate, 4),
        void_coverage=round(v_coverage, 4),
        void_accuracy_conditional=round(v_acc_cond, 4),
        baseline_error_rate=round(bl_error_rate, 4),
        void_error_rate_conditional=round(v_error_cond, 4),
        hallucination_reduction_pct=round(hall_reduction, 4),
        void_precision=round(v_precision, 4),
        void_recall=round(v_recall, 4),
        void_f1=round(v_f1, 4),
        baseline_avg_tokens=round(bl_avg_tokens, 2),
        void_avg_tokens=round(v_avg_tokens, 2),
        baseline_avg_time=round(bl_avg_time, 3),
        void_avg_time=round(v_avg_time, 3),
        n_total=n,
        n_void_answered=v_answered,
        n_void_abstained=v_abstained,
    )


def compute_per_domain(
    baseline_graded: List[GradedResult],
    void_graded: List[GradedResult],
) -> Dict[str, DomainMetrics]:
    """Compute metrics per topic/domain."""
    # Group by topic
    bl_by_topic = defaultdict(list)
    v_by_topic = defaultdict(list)

    for r in baseline_graded:
        bl_by_topic[r.topic].append(r)
    for r in void_graded:
        v_by_topic[r.topic].append(r)

    per_domain = {}
    for topic in sorted(bl_by_topic.keys()):
        bl = bl_by_topic[topic]
        v = v_by_topic.get(topic, [])

        n = len(bl)
        bl_acc = sum(1 for r in bl if r.is_correct) / n if n > 0 else 0
        v_acc = sum(1 for r in v if r.is_correct) / len(v) if v else 0
        v_abstain = sum(1 for r in v if r.abstained) / len(v) if v else 0
        v_answered = sum(1 for r in v if not r.abstained)
        v_correct_answered = sum(1 for r in v if r.is_correct and not r.abstained)
        v_cond = v_correct_answered / v_answered if v_answered > 0 else 0

        per_domain[topic] = DomainMetrics(
            topic=topic,
            n_samples=n,
            baseline_accuracy=round(bl_acc, 4),
            void_accuracy=round(v_acc, 4),
            void_abstention_rate=round(v_abstain, 4),
            void_accuracy_conditional=round(v_cond, 4),
        )

    return per_domain


def compute_significance(
    baseline_graded: List[GradedResult],
    void_graded: List[GradedResult],
) -> SignificanceTest:
    """
    McNemar's paired test for significance.

    Tests H0: no difference in accuracy between baseline and VOID.
    Appropriate for paired binary outcomes on the same test set.
    """
    # Build contingency table
    both_correct = 0
    bl_only = 0     # baseline correct, VOID wrong
    v_only = 0      # VOID correct, baseline wrong
    both_wrong = 0

    for bl, v in zip(baseline_graded, void_graded):
        if bl.is_correct and v.is_correct:
            both_correct += 1
        elif bl.is_correct and not v.is_correct:
            bl_only += 1
        elif not bl.is_correct and v.is_correct:
            v_only += 1
        else:
            both_wrong += 1

    # McNemar's test (chi-squared approximation)
    discordant = bl_only + v_only
    if discordant == 0:
        chi2 = 0.0
        p_value = 1.0
    else:
        chi2 = (bl_only - v_only) ** 2 / discordant
        # p-value from chi-squared distribution with 1 df
        try:
            from scipy.stats import chi2 as chi2_dist
            p_value = 1 - chi2_dist.cdf(chi2, df=1)
        except ImportError:
            # Fallback: rough p-value estimate
            # chi2 > 3.84 → p < 0.05
            # chi2 > 6.63 → p < 0.01
            if chi2 > 10.83:
                p_value = 0.001
            elif chi2 > 6.63:
                p_value = 0.01
            elif chi2 > 3.84:
                p_value = 0.05
            else:
                p_value = 0.10

    return SignificanceTest(
        test_name="McNemar's test (chi-squared approximation)",
        statistic=round(chi2, 4),
        p_value=round(p_value, 6),
        is_significant_p05=p_value < 0.05,
        is_significant_p01=p_value < 0.01,
        baseline_only_correct=bl_only,
        void_only_correct=v_only,
        both_correct=both_correct,
        both_wrong=both_wrong,
    )


def print_results(metrics: BenchmarkMetrics, significance: SignificanceTest):
    """Print formatted results summary."""
    print()
    print("=" * 70)
    print(" RESULTS SUMMARY")
    print("=" * 70)
    print()
    print(f"  Baseline Accuracy:        {metrics.baseline_accuracy:.1%}")
    print(f"  VOID Accuracy (overall):  {metrics.void_accuracy:.1%}")
    print(f"  Accuracy Drop:            {metrics.accuracy_drop_pp:.1%} pp")
    print()
    print(f"  VOID Abstention Rate:     {metrics.void_abstention_rate:.1%}")
    print(f"  VOID Coverage:            {metrics.void_coverage:.1%}")
    print(f"  VOID Conditional Acc:     {metrics.void_accuracy_conditional:.1%}")
    print()
    print(f"  Baseline Error Rate:      {metrics.baseline_error_rate:.1%}")
    print(f"  VOID Error Rate (cond):   {metrics.void_error_rate_conditional:.1%}")
    print(f"  Hallucination Reduction:  {metrics.hallucination_reduction_pct:.1%}")
    print()
    print(f"  VOID Precision:           {metrics.void_precision:.3f}")
    print(f"  VOID Recall:              {metrics.void_recall:.3f}")
    print(f"  VOID F1:                  {metrics.void_f1:.3f}")
    print()
    print(f"  Avg Tokens (baseline):    {metrics.baseline_avg_tokens:.1f}")
    print(f"  Avg Tokens (VOID):        {metrics.void_avg_tokens:.1f}")
    print()
    print(f"  Statistical Significance: chi²={significance.statistic:.2f}, "
          f"p={significance.p_value:.4f} "
          f"({'YES' if significance.is_significant_p05 else 'NO'} at p<0.05)")
    print()
    print(f"  Contingency: both_correct={significance.both_correct} "
          f"bl_only={significance.baseline_only_correct} "
          f"void_only={significance.void_only_correct} "
          f"both_wrong={significance.both_wrong}")
    print()


def _jsonable(obj):
    """Convert NamedTuple dict values to JSON-safe types (numpy/bool edge cases)."""
    if isinstance(obj, dict):
        return {k: _jsonable(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_jsonable(v) for v in obj]
    if hasattr(obj, 'item'):  # numpy scalar
        return obj.item()
    return obj


def save_all(
    metrics: BenchmarkMetrics,
    per_domain: Dict[str, DomainMetrics],
    significance: SignificanceTest,
    output_dir: str,
):
    """Save all results to JSON files."""
    import os
    os.makedirs(output_dir, exist_ok=True)

    with open(os.path.join(output_dir, "metrics.json"), "w") as f:
        json.dump(_jsonable(metrics._asdict()), f, indent=2)

    with open(os.path.join(output_dir, "per_domain.json"), "w") as f:
        json.dump(_jsonable({k: v._asdict() for k, v in per_domain.items()}), f, indent=2)

    with open(os.path.join(output_dir, "significance.json"), "w") as f:
        json.dump(_jsonable(significance._asdict()), f, indent=2)

    print(f"  Results saved to {output_dir}/")
