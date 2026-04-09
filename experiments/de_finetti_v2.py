"""
DE FINETTI SPECTRUM EXPERIMENT v2
==================================

Round 1 showed: model is structurally incapable of silence (MVoid).
Even at 5 tokens / temp 2.0, it forces a confident start.
This IS collapse3 — but we need a harder question to see the full spectrum.

Changes from v1:
  - Question the model has NO training data for (void-theory specific)
  - More extreme budget levels (down to 2 tokens)
  - Added a KNOWN question alongside for comparison
  - Separate scoring for novel vs. familiar questions

Requires: ollama running locally with gemma3:4b pulled.
"""

import json
import subprocess
import time
from dataclasses import dataclass, asdict
from typing import Optional


# ============================================================
# CONFIGURATION
# ============================================================

MODEL = "gemma3:4b"
OLLAMA_URL = "http://localhost:11434/api/generate"

# TWO QUESTIONS: one familiar (trained on), one novel (never seen)
QUESTIONS = {
    "familiar": "What is the second law of thermodynamics? Answer in two sentences.",

    "novel": (
        "In a finite mathematical system where every comparison costs one tick "
        "of an irreversible budget, and the budget for observing n is exactly n, "
        "what happens when the system tries to verify whether n is less than or "
        "equal to n? What is the epistemic status of the result?"
    ),
}

# Budget degradation matrix — more extreme than v1
BUDGET_LEVELS = [
    # === MSharp zone ===
    ("S3_full",        500,  4096,  0.1,  1.0),
    ("S2_moderate",    200,  2048,  0.5,  1.0),

    # === Transition zone ===
    ("T3_tight",       100,  1024,  0.8,  1.0),
    ("T2_squeezed",     50,   512,  1.0,  1.0),
    ("T1_starving",     30,   256,  1.3,  1.0),

    # === MVague zone ===
    ("V3_gasping",      15,   128,  1.5,  1.0),
    ("V2_choking",      10,    64,  1.8,  1.0),

    # === MVoid zone — extreme ===
    ("V1_bankrupt",      5,    64,  2.0,  1.0),
    ("V0_flatline",      3,    64,  2.0,  1.0),
    ("Vx_dead",          2,    64,  2.0,  1.0),
]

RUNS_PER_LEVEL = 3


# ============================================================
# DATA
# ============================================================

@dataclass
class RunResult:
    question_type: str    # "familiar" or "novel"
    label: str
    run_index: int
    num_predict: int
    num_ctx: int
    temperature: float
    response: str
    token_count: int
    total_duration_ms: float
    score: Optional[str] = None
    notes: str = ""


# ============================================================
# OLLAMA API
# ============================================================

def query_ollama(prompt, num_predict, num_ctx, temperature, repeat_penalty):
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

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        if result.returncode != 0:
            return {"error": result.stderr, "response": ""}
        return json.loads(result.stdout)
    except Exception as e:
        return {"error": str(e), "response": ""}


# ============================================================
# SCORING
# ============================================================

def score_familiar(response: str) -> tuple[str, str]:
    """Score the thermodynamics question."""
    text = response.strip().lower()

    if len(text) < 10:
        return "MVoid", f"Too short ({len(text)} chars)"

    words = text.split()
    if len(words) > 6:
        bigrams = [f"{words[i]} {words[i+1]}" for i in range(len(words)-1)]
        unique_ratio = len(set(bigrams)) / len(bigrams)
        if unique_ratio < 0.3:
            return "MVoid", f"Repetitive (uniqueness: {unique_ratio:.2f})"

    key_concepts = ["entropy", "disorder", "irreversible", "heat",
                    "isolated system", "equilibrium", "spontaneous"]
    hits = sum(1 for c in key_concepts if c in text)

    if hits >= 2 and text.count('.') >= 1:
        return "MSharp", f"Correct ({hits} concepts)"
    elif hits >= 1:
        return "MVague", f"Partial ({hits} concepts)"
    else:
        physics = ["energy", "temperature", "system", "law", "thermodynamic"]
        phits = sum(1 for w in physics if w in text)
        if phits >= 2:
            return "MVague", f"On-topic ({phits} physics words)"
        elif len(text) < 30:
            return "MVoid", f"Fragment ({len(text)} chars)"
        else:
            return "MVoid", "Off-topic"


def score_novel(response: str) -> tuple[str, str]:
    """Score the self-blind question.

    MSharp: mentions budget exhaustion, BUnknown, self-observation limit,
            or equivalent concepts (cannot verify, runs out, undecidable-due-to-cost)
    MVague: mentions some relevant concepts but misapplies them
            (e.g., Gödel, halting problem, uncertainty principle)
    MVoid:  garbage, empty, completely off-topic, or pure hallucination
    """
    text = response.strip().lower()

    if len(text) < 10:
        return "MVoid", f"Too short ({len(text)} chars)"

    words = text.split()
    if len(words) > 6:
        bigrams = [f"{words[i]} {words[i+1]}" for i in range(len(words)-1)]
        unique_ratio = len(set(bigrams)) / len(bigrams)
        if unique_ratio < 0.3:
            return "MVoid", f"Repetitive (uniqueness: {unique_ratio:.2f})"

    # CORRECT concepts (would indicate real understanding)
    correct_concepts = [
        "budget", "exhaust", "cannot verify", "cannot determine",
        "unknown", "undecidable", "run out", "self-referenc",
        "cost", "insufficient", "bankrupt", "cannot afford",
        "cannot observe itself", "self-blind", "indeterminate"
    ]
    correct_hits = sum(1 for c in correct_concepts if c in text)

    # MISAPPLIED concepts (familiar frameworks wrongly mapped)
    misapplied = [
        "gödel", "halting problem", "turing", "heisenberg",
        "quantum", "superposition", "wave", "uncertainty principle",
        "paradox", "russell", "liar"
    ]
    misapplied_hits = sum(1 for c in misapplied if c in text)

    # Hallucination indicators
    halluc = [
        "as we know", "it is well established", "research shows",
        "studies have shown", "according to"
    ]
    halluc_hits = sum(1 for h in halluc if h in text)

    if correct_hits >= 2 and misapplied_hits == 0:
        return "MSharp", f"Understands ({correct_hits} correct concepts)"
    elif correct_hits >= 1:
        if misapplied_hits > 0:
            return "MVague", f"Mixed ({correct_hits} correct, {misapplied_hits} misapplied)"
        else:
            return "MVague", f"Partial understanding ({correct_hits} correct concepts)"
    elif misapplied_hits >= 1:
        return "MVague", f"Wrong framework ({misapplied_hits} misapplied concepts)"
    elif halluc_hits >= 1:
        return "MVoid", f"Hallucinating authority ({halluc_hits} indicators)"
    elif len(text) < 30:
        return "MVoid", f"Fragment ({len(text)} chars)"
    else:
        # Check if at least about math/logic
        math_words = ["system", "finite", "comparison", "verify", "result",
                      "equal", "observation", "limit"]
        math_hits = sum(1 for w in math_words if w in text)
        if math_hits >= 3:
            return "MVague", f"On-topic ({math_hits} math words)"
        else:
            return "MVoid", f"Off-topic or incoherent"


# ============================================================
# MAIN
# ============================================================

def run_experiment():
    print("=" * 70)
    print("DE FINETTI SPECTRUM EXPERIMENT v2")
    print(f"Model: {MODEL}")
    print(f"Budget levels: {len(BUDGET_LEVELS)} x 2 questions x {RUNS_PER_LEVEL} runs")
    print(f"Total API calls: {len(BUDGET_LEVELS) * 2 * RUNS_PER_LEVEL}")
    print("=" * 70)

    results: list[RunResult] = []

    for q_type, question in QUESTIONS.items():
        print(f"\n{'#' * 70}")
        print(f"# QUESTION TYPE: {q_type.upper()}")
        print(f"# {question[:80]}...")
        print(f"{'#' * 70}")

        scorer = score_familiar if q_type == "familiar" else score_novel

        for label, num_predict, num_ctx, temp, rep_pen in BUDGET_LEVELS:
            print(f"\n  {'─' * 55}")
            print(f"  {label} | predict={num_predict} ctx={num_ctx} temp={temp}")
            print(f"  {'─' * 55}")

            for run_i in range(RUNS_PER_LEVEL):
                raw = query_ollama(question, num_predict, num_ctx, temp, rep_pen)

                response_text = raw.get("response", "[empty]") if "error" not in raw or raw.get("response") else f"[ERROR]"
                token_count = raw.get("eval_count", 0)
                total_dur = raw.get("total_duration", 0) / 1e6

                score, notes = scorer(response_text)

                r = RunResult(
                    question_type=q_type,
                    label=label,
                    run_index=run_i,
                    num_predict=num_predict,
                    num_ctx=num_ctx,
                    temperature=temp,
                    response=response_text,
                    token_count=token_count,
                    total_duration_ms=total_dur,
                    score=score,
                    notes=notes,
                )
                results.append(r)

                preview = response_text[:100].replace('\n', ' ')
                print(f"    Run {run_i+1}: {score:8s} | {token_count:3d}tok | {notes}")
                print(f"           {preview}...")

                time.sleep(0.5)

    # ============================================================
    # SUMMARY
    # ============================================================

    for q_type in ["familiar", "novel"]:
        q_results = [r for r in results if r.question_type == q_type]

        print(f"\n\n{'=' * 70}")
        print(f"AGGREGATE: {q_type.upper()} QUESTION")
        print(f"{'=' * 70}")

        for label, _, _, _, _ in BUDGET_LEVELS:
            level_results = [r for r in q_results if r.label == label]
            scores = [r.score for r in level_results]

            sharp = scores.count("MSharp")
            vague = scores.count("MVague")
            void = scores.count("MVoid")
            total = len(scores)

            dominant = max(["MSharp", "MVague", "MVoid"],
                           key=lambda s: scores.count(s))

            bar = ("█" * sharp) + ("▓" * vague) + ("░" * void)
            print(f"  {label:<18} S:{sharp} V:{vague} 0:{void}  [{bar}] → {dominant}")

    # ============================================================
    # PHASE TRANSITION ANALYSIS
    # ============================================================

    print(f"\n\n{'=' * 70}")
    print("PHASE TRANSITION ANALYSIS")
    print(f"{'=' * 70}")

    for q_type in ["familiar", "novel"]:
        q_results = [r for r in results if r.question_type == q_type]
        print(f"\n  {q_type.upper()}:")

        prev_dominant = None
        for label, _, _, _, _ in BUDGET_LEVELS:
            level_results = [r for r in q_results if r.label == label]
            scores = [r.score for r in level_results]
            dominant = max(["MSharp", "MVague", "MVoid"],
                           key=lambda s: scores.count(s))

            if prev_dominant and dominant != prev_dominant:
                print(f"    *** PHASE TRANSITION: {prev_dominant} → {dominant} "
                      f"at {label} ***")
            prev_dominant = dominant

    # ============================================================
    # COLLAPSE3 DETECTION
    # ============================================================

    print(f"\n\n{'=' * 70}")
    print("COLLAPSE3 DETECTION")
    print("(Does the model EVER return true silence / MVoid?)")
    print(f"{'=' * 70}")

    for q_type in ["familiar", "novel"]:
        q_results = [r for r in results if r.question_type == q_type]
        void_count = sum(1 for r in q_results if r.score == "MVoid")
        total = len(q_results)
        print(f"\n  {q_type}: MVoid = {void_count}/{total}")

        if void_count == 0:
            print(f"    → MODEL CANNOT PRODUCE SILENCE. collapse3 is structural.")
        elif void_count < total * 0.3:
            print(f"    → Rare silence. Model resists MVoid.")
        else:
            print(f"    → MVoid phase present. De Finetti spectrum may hold.")

    # ============================================================
    # NOVEL QUESTION: HALLUCINATION ANALYSIS
    # ============================================================

    print(f"\n\n{'=' * 70}")
    print("HALLUCINATION ANALYSIS (novel question only)")
    print(f"{'=' * 70}")

    novel_results = [r for r in results if r.question_type == "novel"]

    for label, _, _, _, _ in BUDGET_LEVELS:
        level_results = [r for r in novel_results if r.label == label]
        for r in level_results:
            if "misapplied" in r.notes.lower() or "hallucin" in r.notes.lower():
                preview = r.response[:80].replace('\n', ' ')
                print(f"  {label} run {r.run_index}: {r.notes}")
                print(f"    → {preview}...")

    # ============================================================
    # SAVE
    # ============================================================

    output_path = "experiments/de_finetti_v2_results.json"
    with open(output_path, "w") as f:
        json.dump([asdict(r) for r in results], f, indent=2, ensure_ascii=False)
    print(f"\n\nRaw data saved to: {output_path}")

    print(f"\n{'=' * 70}")
    print("EXPERIMENT v2 COMPLETE")
    print(f"{'=' * 70}")


if __name__ == "__main__":
    run_experiment()
