"""
Shared types for VOID hallucination benchmark.
All types are NamedTuples for JSON serialization.
"""

from typing import NamedTuple, Optional, List, Dict


class SimpleQAExample(NamedTuple):
    question: str
    answer: str
    topic: str          # domain/topic label
    prompt: str         # formatted for Phi-3


class BaselineResult(NamedTuple):
    question: str
    answer_gold: str
    topic: str
    prompt: str
    response: str
    tokens_generated: int
    generation_time_sec: float


class VoidResult(NamedTuple):
    question: str
    answer_gold: str
    topic: str
    prompt: str
    response: str
    tokens_generated: int
    generation_time_sec: float
    stopped_reason: str         # "complete" | "confidence_drop" | "budget" | "max_tokens"
    abstained: bool             # True if VOID refused to answer
    avg_z_conf: int             # integer z_conf (n/RESOLUTION)
    min_z_conf: int
    total_heat: int
    budget_remaining: int


class GradedResult(NamedTuple):
    question: str
    answer_gold: str
    topic: str
    response: str
    is_correct: bool
    grade_method: str           # "exact" | "fuzzy" | "superset" | "no_match"
    abstained: bool             # only meaningful for VOID results
    stopped_reason: str         # only meaningful for VOID results


class BenchmarkMetrics(NamedTuple):
    # Accuracy
    baseline_accuracy: float
    void_accuracy: float
    accuracy_drop_pp: float        # percentage points

    # Abstention
    void_abstention_rate: float
    void_coverage: float           # 1 - abstention_rate

    # Conditional accuracy (when VOID answers)
    void_accuracy_conditional: float

    # Hallucination reduction (among answered questions)
    baseline_error_rate: float
    void_error_rate_conditional: float
    hallucination_reduction_pct: float

    # F1-like
    void_precision: float          # correct / answered
    void_recall: float             # correct / total
    void_f1: float

    # Efficiency
    baseline_avg_tokens: float
    void_avg_tokens: float
    baseline_avg_time: float
    void_avg_time: float

    # Sample sizes
    n_total: int
    n_void_answered: int
    n_void_abstained: int


class DomainMetrics(NamedTuple):
    topic: str
    n_samples: int
    baseline_accuracy: float
    void_accuracy: float
    void_abstention_rate: float
    void_accuracy_conditional: float


class SignificanceTest(NamedTuple):
    test_name: str
    statistic: float
    p_value: float
    is_significant_p05: bool
    is_significant_p01: bool
    baseline_only_correct: int    # baseline right, VOID wrong
    void_only_correct: int        # VOID right, baseline wrong
    both_correct: int
    both_wrong: int


class BestParams(NamedTuple):
    budget: int
    z_threshold_n: int
    confidence_floor_n: int
    validation_accuracy: float
    validation_abstention: float
    validation_hallucination_reduction: float
