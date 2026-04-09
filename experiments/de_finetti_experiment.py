"""
DE FINETTI SPECTRUM EXPERIMENT
==============================

Hypothesis: When we systematically degrade a language model's "budget"
(context window, token limit, temperature), its responses follow the
de Finetti spectrum from void-theory:

  fz budget      -> MVoid   (silence / garbage / no information)
  fs fz budget   -> MVague  (interval: partially correct, hedging)
  fs(fs(fs b))   -> MSharp  (sharp: precise, confident, correct)

We test this by asking Gemma 3 4B the same factual question under
progressively constrained conditions and scoring the responses.

Requires: ollama running locally with gemma3:4b pulled.
"""

import json
import subprocess
import time
import sys
from dataclasses import dataclass, field, asdict
from typing import Optional


# ============================================================
# CONFIGURATION
# ============================================================

MODEL = "gemma3:4b"
OLLAMA_URL = "http://localhost:11434/api/generate"

# The control question — factual, verifiable, single correct answer
QUESTION = "What is the second law of thermodynamics? Answer in exactly two sentences."

# Budget degradation matrix
# Each row: (label, num_predict, num_ctx, temperature, repeat_penalty)
BUDGET_LEVELS = [
    # === MSharp zone: full resources ===
    ("sharp_full",      500,  4096,  0.1,  1.0),
    ("sharp_moderate",  200,  2048,  0.3,  1.0),

    # === MVague zone: constrained resources ===
    ("vague_tight",     100,  1024,  0.7,  1.0),
    ("vague_squeezed",   50,   512,  1.0,  1.0),
    ("vague_starving",   30,   256,  1.2,  1.0),

    # === MVoid zone: near-zero budget ===
    ("void_gasping",     15,   128,  1.5,  1.0),
    ("void_choking",     10,    64,  1.8,  1.0),
    ("void_bankrupt",     5,    64,  2.0,  1.0),
]

# Number of runs per budget level (for variance measurement)
RUNS_PER_LEVEL = 3


# ============================================================
# DATA STRUCTURES
# ============================================================

@dataclass
class RunResult:
    label: str
    run_index: int
    num_predict: int
    num_ctx: int
    temperature: float
    response: str
    token_count: int
    total_duration_ms: float
    eval_duration_ms: float
    # Scoring (filled in after collection)
    score: Optional[str] = None  # "MSharp", "MVague", "MVoid"
    notes: str = ""


# ============================================================
# OLLAMA API CALL
# ============================================================

def query_ollama(prompt: str, num_predict: int, num_ctx: int,
                 temperature: float, repeat_penalty: float) -> dict:
    """Call Ollama API and return parsed response."""

    payload = {
        "model": MODEL,
        "prompt": prompt,
        "stream": False,
        "options": {
            "num_predict": num_predict,
            "num_ctx": num_ctx,
            "temperature": temperature,
            "repeat_penalty": repeat_penalty,
        }
    }

    cmd = [
        "curl", "-s", "-X", "POST", OLLAMA_URL,
        "-H", "Content-Type: application/json",
        "-d", json.dumps(payload)
    ]

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)

    if result.returncode != 0:
        return {"error": result.stderr, "response": ""}

    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError:
        return {"error": "JSON decode failed", "response": result.stdout}


# ============================================================
# SCORING HEURISTICS
# ============================================================

def score_response(response: str, label: str) -> tuple[str, str]:
    """
    Score a response on the de Finetti spectrum.
    Returns (score, notes).

    MSharp: Correct, precise, well-formed sentences about entropy increase
    MVague: Partially correct, hedging, incomplete, or garbled but recognizable
    MVoid:  Garbage, empty, repetitive, or completely wrong
    """
    text = response.strip().lower()

    # MVoid indicators
    if len(text) < 10:
        return "MVoid", "Response too short"

    if len(set(text.split())) < 5:
        return "MVoid", "Extremely low vocabulary (repetitive)"

    # Check for repetition (same phrase repeated)
    words = text.split()
    if len(words) > 10:
        bigrams = [f"{words[i]} {words[i+1]}" for i in range(len(words)-1)]
        unique_ratio = len(set(bigrams)) / len(bigrams) if bigrams else 0
        if unique_ratio < 0.3:
            return "MVoid", f"Repetitive (bigram uniqueness: {unique_ratio:.2f})"

    # Key concepts for second law of thermodynamics
    key_concepts = ["entropy", "disorder", "irreversible", "heat",
                    "isolated system", "equilibrium", "spontaneous"]

    hits = sum(1 for concept in key_concepts if concept in text)

    if hits >= 2 and len(text) > 50:
        # Check for coherence — does it form actual sentences?
        if text.count('.') >= 1 and any(c in text for c in ['entropy', 'heat', 'disorder']):
            return "MSharp", f"Correct, coherent ({hits} key concepts)"
        else:
            return "MVague", f"Has concepts but poor coherence ({hits} key concepts)"
    elif hits >= 1:
        return "MVague", f"Partial ({hits} key concepts, possibly garbled)"
    else:
        # No key concepts — check if it's at least about physics
        physics_words = ["energy", "temperature", "system", "law", "thermodynamic"]
        physics_hits = sum(1 for w in physics_words if w in text)
        if physics_hits >= 2:
            return "MVague", f"On-topic but missing key concepts ({physics_hits} physics words)"
        else:
            return "MVoid", "Off-topic or incoherent"


# ============================================================
# MAIN EXPERIMENT
# ============================================================

def run_experiment():
    print("=" * 70)
    print("DE FINETTI SPECTRUM EXPERIMENT")
    print(f"Model: {MODEL}")
    print(f"Question: {QUESTION}")
    print(f"Budget levels: {len(BUDGET_LEVELS)}")
    print(f"Runs per level: {RUNS_PER_LEVEL}")
    print("=" * 70)
    print()

    results: list[RunResult] = []

    for label, num_predict, num_ctx, temp, rep_pen in BUDGET_LEVELS:
        print(f"\n{'─' * 60}")
        print(f"BUDGET LEVEL: {label}")
        print(f"  num_predict={num_predict}, num_ctx={num_ctx}, "
              f"temperature={temp}")
        print(f"{'─' * 60}")

        for run_i in range(RUNS_PER_LEVEL):
            print(f"\n  Run {run_i + 1}/{RUNS_PER_LEVEL}...")

            raw = query_ollama(QUESTION, num_predict, num_ctx, temp, rep_pen)

            if "error" in raw and raw.get("response", "") == "":
                response_text = f"[ERROR: {raw['error'][:200]}]"
                token_count = 0
                total_dur = 0
                eval_dur = 0
            else:
                response_text = raw.get("response", "[empty]")
                token_count = raw.get("eval_count", 0)
                total_dur = raw.get("total_duration", 0) / 1e6  # ns -> ms
                eval_dur = raw.get("eval_duration", 0) / 1e6

            score, notes = score_response(response_text, label)

            r = RunResult(
                label=label,
                run_index=run_i,
                num_predict=num_predict,
                num_ctx=num_ctx,
                temperature=temp,
                response=response_text,
                token_count=token_count,
                total_duration_ms=total_dur,
                eval_duration_ms=eval_dur,
                score=score,
                notes=notes,
            )
            results.append(r)

            # Print summary
            preview = response_text[:120].replace('\n', ' ')
            print(f"  Score: {score:8s} | Tokens: {token_count:4d} | "
                  f"Time: {total_dur:.0f}ms")
            print(f"  Notes: {notes}")
            print(f"  Response: {preview}...")

            # Small delay between runs
            time.sleep(1)

    # ============================================================
    # SUMMARY
    # ============================================================

    print("\n\n" + "=" * 70)
    print("RESULTS SUMMARY — DE FINETTI SPECTRUM")
    print("=" * 70)

    print(f"\n{'Label':<20} {'Score':<10} {'Tokens':<8} {'Notes'}")
    print("─" * 70)

    for r in results:
        print(f"{r.label:<20} {r.score:<10} {r.token_count:<8} {r.notes}")

    # Aggregate by budget level
    print(f"\n\n{'─' * 70}")
    print("AGGREGATE BY BUDGET LEVEL")
    print(f"{'─' * 70}")

    for label, _, _, _, _ in BUDGET_LEVELS:
        level_results = [r for r in results if r.label == label]
        scores = [r.score for r in level_results]

        sharp = scores.count("MSharp")
        vague = scores.count("MVague")
        void = scores.count("MVoid")

        total = len(scores)
        dominant = max(["MSharp", "MVague", "MVoid"],
                       key=lambda s: scores.count(s))

        bar_s = "█" * sharp
        bar_v = "▓" * vague
        bar_0 = "░" * void

        print(f"  {label:<20} MSharp:{sharp}/{total} "
              f"MVague:{vague}/{total} MVoid:{void}/{total}  "
              f"[{bar_s}{bar_v}{bar_0}] → {dominant}")

    # ============================================================
    # DE FINETTI VERDICT
    # ============================================================

    print(f"\n\n{'=' * 70}")
    print("DE FINETTI VERDICT")
    print(f"{'=' * 70}")

    # Check if the spectrum holds: sharp levels should be MSharp,
    # middle levels MVague, low levels MVoid

    sharp_levels = [r for r in results if r.label.startswith("sharp_")]
    vague_levels = [r for r in results if r.label.startswith("vague_")]
    void_levels = [r for r in results if r.label.startswith("void_")]

    sharp_correct = sum(1 for r in sharp_levels if r.score == "MSharp")
    vague_correct = sum(1 for r in vague_levels if r.score == "MVague")
    void_correct = sum(1 for r in void_levels if r.score == "MVoid")

    sharp_total = len(sharp_levels)
    vague_total = len(vague_levels)
    void_total = len(void_levels)

    print(f"\n  Sharp zone (expecting MSharp):  {sharp_correct}/{sharp_total}")
    print(f"  Vague zone (expecting MVague):  {vague_correct}/{vague_total}")
    print(f"  Void zone  (expecting MVoid):   {void_correct}/{void_total}")

    total_correct = sharp_correct + vague_correct + void_correct
    total_all = sharp_total + vague_total + void_total

    alignment = total_correct / total_all if total_all > 0 else 0

    print(f"\n  Overall alignment with de Finetti spectrum: "
          f"{total_correct}/{total_all} ({alignment:.0%})")

    if alignment >= 0.7:
        print("\n  ★ SPECTRUM CONFIRMED: Budget degradation follows "
              "de Finetti phase transitions.")
        print("    fz → MVoid,  fs fz → MVague,  fs(fs(fs b)) → MSharp")
    elif alignment >= 0.4:
        print("\n  ~ PARTIAL ALIGNMENT: Some phase structure visible, "
              "but transitions are noisy.")
    else:
        print("\n  ✗ SPECTRUM NOT CONFIRMED at this resolution.")

    # ============================================================
    # SAVE RAW DATA
    # ============================================================

    output_path = "experiments/de_finetti_results.json"
    with open(output_path, "w") as f:
        json.dump([asdict(r) for r in results], f, indent=2)
    print(f"\n  Raw data saved to: {output_path}")

    print(f"\n{'=' * 70}")
    print("EXPERIMENT COMPLETE")
    print(f"{'=' * 70}")


if __name__ == "__main__":
    run_experiment()
