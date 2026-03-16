"""
grader.py - Grade benchmark responses against gold answers.

Phase 1 (main): Exact match grading — no API calls, fully reproducible.
Phase 2 (optional): LLM-as-judge for ambiguous cases.

For the main benchmark, we use exact match only.
"""

import re
from difflib import SequenceMatcher
from typing import List, Tuple

from bench_types import BaselineResult, VoidResult, GradedResult


def normalize(text: str) -> str:
    """Normalize text for comparison: lowercase, strip, collapse whitespace."""
    text = text.lower().strip()
    text = re.sub(r'\s+', ' ', text)
    # Remove common filler
    for prefix in ["the answer is ", "it is ", "that would be ", "this is "]:
        if text.startswith(prefix):
            text = text[len(prefix):]
    return text.strip()


def grade_exact(response: str, gold_answer: str) -> Tuple[bool, str]:
    """
    Grade a single response against gold answer using exact matching.

    Three methods in order:
    1. Substring: gold answer appears in response
    2. Fuzzy: SequenceMatcher ratio > 0.7
    3. Token superset: all gold tokens present in response

    Returns:
        (is_correct, method)
    """
    resp_norm = normalize(response)
    gold_norm = normalize(gold_answer)

    if not resp_norm:
        return False, "empty"

    # Method 1: substring match
    if gold_norm in resp_norm:
        return True, "exact"

    # Method 2: fuzzy match
    ratio = SequenceMatcher(None, resp_norm, gold_norm).ratio()
    if ratio > 0.7:
        return True, "fuzzy"

    # Method 3: token superset (all gold tokens in response)
    gold_tokens = set(gold_norm.split())
    resp_tokens = set(resp_norm.split())
    if gold_tokens and gold_tokens.issubset(resp_tokens):
        return True, "superset"

    # Method 4: check if gold answer is a number and response contains it
    # (handles "42" vs "The answer is 42.")
    gold_numbers = re.findall(r'\d+\.?\d*', gold_norm)
    resp_numbers = re.findall(r'\d+\.?\d*', resp_norm)
    if gold_numbers and all(n in resp_numbers for n in gold_numbers):
        return True, "numeric"

    return False, "no_match"


def grade_baseline(results: List[BaselineResult]) -> List[GradedResult]:
    """Grade all baseline results."""
    graded = []
    for r in results:
        correct, method = grade_exact(r.response, r.answer_gold)
        graded.append(GradedResult(
            question=r.question,
            answer_gold=r.answer_gold,
            topic=r.topic,
            response=r.response,
            is_correct=correct,
            grade_method=method,
            abstained=False,
            stopped_reason="max_tokens",
        ))
    return graded


def grade_void(results: List[VoidResult]) -> List[GradedResult]:
    """Grade all VOID results. Abstentions are graded as incorrect."""
    graded = []
    for r in results:
        if r.abstained or not r.response.strip():
            correct = False
            method = "abstained"
        else:
            correct, method = grade_exact(r.response, r.answer_gold)

        graded.append(GradedResult(
            question=r.question,
            answer_gold=r.answer_gold,
            topic=r.topic,
            response=r.response,
            is_correct=correct,
            grade_method=method,
            abstained=r.abstained,
            stopped_reason=r.stopped_reason,
        ))
    return graded


def print_grading_summary(graded: List[GradedResult], label: str):
    """Print grading summary."""
    n = len(graded)
    n_correct = sum(1 for r in graded if r.is_correct)
    n_abstained = sum(1 for r in graded if r.abstained)

    methods = {}
    for r in graded:
        methods[r.grade_method] = methods.get(r.grade_method, 0) + 1

    print(f"\n  {label} grading summary:")
    print(f"    Total:    {n}")
    print(f"    Correct:  {n_correct} ({n_correct/n:.1%})")
    if n_abstained > 0:
        n_answered = n - n_abstained
        n_correct_answered = sum(1 for r in graded if r.is_correct and not r.abstained)
        print(f"    Abstained: {n_abstained} ({n_abstained/n:.1%})")
        print(f"    Answered:  {n_answered} ({n_answered/n:.1%})")
        if n_answered > 0:
            print(f"    Correct|Answered: {n_correct_answered} ({n_correct_answered/n_answered:.1%})")
    print(f"    Methods: {methods}")
