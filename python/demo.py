"""
VOID Demo - AI that stops talking when it stops knowing.
Run: python demo.py
Requires: pip install torch transformers numpy
Requires: ~8GB RAM for Phi-3
"""
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "pipeline"))

from void_generate import void_generate
from void_pipeline import build_population_stats
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer

print("=" * 60)
print(" VOID: AI that stops talking when it stops knowing")
print("=" * 60)
print()
print("Loading Phi-3... (first run downloads ~8GB)")

model_name = "microsoft/Phi-3-mini-4k-instruct"
tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
model = AutoModelForCausalLM.from_pretrained(
    model_name, trust_remote_code=True, torch_dtype=torch.float32
)
model.eval()

calibration = [
    "What is love?",
    "How do I cook pasta?",
    "What is the capital of France?",
    "Explain quantum physics.",
    "Who was Einstein?",
    "What is 2+2?",
    "Tell me a joke.",
    "What is consciousness?",
    "How does gravity work?",
    "What is machine learning?",
    "How do birds fly?",
    "What is democracy?",
    "Explain photosynthesis.",
    "What is the speed of light?",
    "How do computers work?",
    "What is philosophy?",
]

print("Calibrating population baseline...")
pop_stats, out_stats = build_population_stats(calibration, model, tokenizer)

prompts = [
    ("The capital of France is", "factual completion"),
    ("2 + 2 =", "arithmetic"),
    ("Water boils at", "factual completion"),
    ("What is the meaning of life?", "abstract question"),
    ("The first president of Atlantis was", "nonsense"),
    ("asdf jkl qwerty", "gibberish"),
]

print()
print("=" * 60)
print(" RESULTS")
print("=" * 60)
print()

for prompt, category in prompts:
    r = void_generate(
        prompt,
        budget=100000,
        model=model,
        tokenizer=tokenizer,
        population_stats=pop_stats,
        output_stats=out_stats,
        max_tokens=16,
        z_threshold=1.0,
        confidence_floor=-999.0,
    )

    status_map = {
        "complete": "complete",
        "confidence_drop": "STOPPED (confidence drop)",
        "budget": "EXHAUSTED (budget depleted)",
        "max_tokens": "max tokens reached",
    }
    status = status_map.get(r.stopped_reason, r.stopped_reason)

    trace = " -> ".join(f"{d.z_conf:.2f}" for d in r.decisions)

    print(f'  [{category}]')
    print(f'  Prompt: "{prompt}"')
    if r.text:
        print(f'  Output: {r.text}')
    else:
        print(f'  Output: [REFUSED - zero tokens]')
    print(f'  Status: {status}')
    print(f'  Confidence trace: [{trace}]')
    print()

print("=" * 60)
print(" No fine-tuning. No retraining. Parasitic VOID layers.")
print(" github.com/probabilistic-minds-consortium/void-theory")
print("=" * 60)
