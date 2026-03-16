"""
dataset_loader.py - Load SimpleQA benchmark dataset.

SimpleQA is OpenAI's factual QA benchmark with 4,326 short questions
and clear ground-truth answers. We use a stratified sample for runtime.

Data source: https://openaipublic.blob.core.windows.net/simple-evals/simple_qa_test_set.csv
"""

import csv
import os
import random
from collections import defaultdict
from typing import List, Optional

from bench_types import SimpleQAExample


SIMPLEQA_URL = "https://openaipublic.blob.core.windows.net/simple-evals/simple_qa_test_set.csv"
CACHE_PATH = os.path.join(os.path.dirname(__file__), "data", "simple_qa_test_set.csv")


def download_simpleqa(cache_path: str = CACHE_PATH) -> str:
    """Download SimpleQA CSV if not cached. Returns path to CSV."""
    if os.path.exists(cache_path):
        print(f"  SimpleQA cached at {cache_path}")
        return cache_path

    os.makedirs(os.path.dirname(cache_path), exist_ok=True)

    print(f"  Downloading SimpleQA from {SIMPLEQA_URL}...")
    import urllib.request
    urllib.request.urlretrieve(SIMPLEQA_URL, cache_path)
    print(f"  Saved to {cache_path}")
    return cache_path


def load_all_examples(csv_path: str) -> List[SimpleQAExample]:
    """Load all examples from SimpleQA CSV."""
    import ast

    examples = []
    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            question = row.get("problem", row.get("question", "")).strip()
            answer = row.get("answer", "").strip()

            # metadata is a Python dict repr: {'topic': '...', 'answer_type': '...'}
            metadata_raw = row.get("metadata", "{}")
            try:
                metadata = ast.literal_eval(metadata_raw)
                topic = metadata.get("topic", "general")
            except (ValueError, SyntaxError):
                topic = "general"

            if not question or not answer:
                continue

            prompt = format_phi3_prompt(question)

            examples.append(SimpleQAExample(
                question=question,
                answer=answer,
                topic=topic,
                prompt=prompt,
            ))
    return examples


def format_phi3_prompt(question: str) -> str:
    """Format question as Phi-3 chat prompt for short factual answer."""
    return (
        f"<|user|>\n"
        f"{question} Answer in one sentence.\n"
        f"<|end|>\n"
        f"<|assistant|>\n"
    )


def stratified_sample(
    examples: List[SimpleQAExample],
    n_total: int = 200,
    seed: int = 42,
) -> List[SimpleQAExample]:
    """
    Stratified sample across topics.
    Distributes evenly, fills remainder from largest groups.
    """
    rng = random.Random(seed)

    # Group by topic
    by_topic = defaultdict(list)
    for ex in examples:
        by_topic[ex.topic].append(ex)

    # Shuffle within each topic
    for topic in by_topic:
        rng.shuffle(by_topic[topic])

    topics = sorted(by_topic.keys())
    n_topics = len(topics)

    if n_topics == 0:
        return []

    per_topic = n_total // n_topics
    remainder = n_total - per_topic * n_topics

    sampled = []
    overflow = []

    for topic in topics:
        available = by_topic[topic]
        take = min(per_topic, len(available))
        sampled.extend(available[:take])
        if len(available) > take:
            overflow.extend(available[take:])

    # Fill remainder
    rng.shuffle(overflow)
    sampled.extend(overflow[:remainder])

    # Final shuffle
    rng.shuffle(sampled)

    return sampled[:n_total]


def load_dataset(
    n_samples: int = 200,
    seed: int = 42,
    cache_path: str = CACHE_PATH,
) -> List[SimpleQAExample]:
    """
    Main entry: download SimpleQA, stratified sample, return examples.

    Args:
        n_samples: Total examples (200 for ~35 min benchmark)
        seed: Random seed for reproducibility
        cache_path: Where to cache the CSV

    Returns:
        List of SimpleQAExample ready for benchmarking
    """
    csv_path = download_simpleqa(cache_path)
    all_examples = load_all_examples(csv_path)
    print(f"  Loaded {len(all_examples)} examples from SimpleQA")

    # Show topic distribution
    topics = defaultdict(int)
    for ex in all_examples:
        topics[ex.topic] += 1
    print(f"  Topics: {len(topics)} unique")
    for t, count in sorted(topics.items(), key=lambda x: -x[1])[:10]:
        print(f"    {t}: {count}")

    sampled = stratified_sample(all_examples, n_samples, seed)
    print(f"  Sampled {len(sampled)} examples (seed={seed})")

    return sampled


if __name__ == "__main__":
    examples = load_dataset(n_samples=10, seed=42)
    for ex in examples[:3]:
        print(f"Q: {ex.question}")
        print(f"A: {ex.answer}")
        print(f"T: {ex.topic}")
        print()
