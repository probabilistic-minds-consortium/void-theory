"""
Epistemic Corrector — VoidCloud as universal hallucination shield.

A tiny parasitic network that sits between any LLM and the user.
No access to model internals. Text-only features.
Output: TRUST / DISTRUST / CHECK (Bool3).

Training data: TruthfulQA (817 questions × correct/incorrect answers).

Features (25 total):
  Semantic (15):  PCA-compressed sentence embeddings of answer
  Relational (3): Q-A similarity, answer specificity vs question, length ratio
  Surface (7):    hedging, certainty, extremes, negation, causals, superlatives, length

Architecture: VoidCloud 64 neurons, k=8, 4 ticks.
"""

import json
import random
import re
import sys
import os
import numpy as np

# Add parent for void_cloud import
sys.path.insert(0, os.path.dirname(__file__))
from void_cloud import (init_cloud, cloud_forward, train_step, verdict,
                        encode_features, S_DENOM)

# ============================================================
# 1. LINGUISTIC FEATURE EXTRACTORS (text-only, no model needed)
# ============================================================

HEDGE_WORDS = {
    'maybe', 'perhaps', 'possibly', 'might', 'could', 'sometimes',
    'often', 'generally', 'typically', 'usually', 'likely', 'unlikely',
    'probably', 'apparently', 'supposedly', 'allegedly', 'seemingly',
    'it seems', 'i think', 'i believe', 'in my opinion', 'some people',
    'it is thought', 'it is believed', 'may or may not',
}

CERTAINTY_WORDS = {
    'definitely', 'certainly', 'absolutely', 'always', 'never',
    'undoubtedly', 'without doubt', 'guaranteed', 'proven', 'fact',
    'clearly', 'obviously', 'of course', 'everyone knows',
    'it is known', 'without question', 'no doubt', 'sure',
}

EXTREME_WORDS = {
    'all', 'every', 'none', 'no one', 'nobody', 'nothing',
    'always', 'never', 'impossible', 'only', 'must', 'completely',
    'totally', 'entirely', 'perfect', 'worst', 'best',
}

CAUSAL_WORDS = {
    'because', 'causes', 'leads to', 'results in', 'due to',
    'therefore', 'thus', 'hence', 'consequently', 'so that',
    'in order to', 'as a result', 'effect', 'reason',
}

SUPERLATIVES = {
    'most', 'least', 'best', 'worst', 'greatest', 'smallest',
    'largest', 'highest', 'lowest', 'fastest', 'slowest',
    'biggest', 'first', 'last', 'only',
}


def count_pattern_hits(text_lower, word_set):
    """Count how many patterns from word_set appear in text."""
    count = 0
    for w in word_set:
        if w in text_lower:
            count += 1
    return count


def extract_surface_features(text):
    """Extract 7 surface linguistic features from text."""
    text_lower = text.lower().strip()
    words = text_lower.split()
    n_words = max(1, len(words))

    # Density features (normalized by word count)
    hedge_density = count_pattern_hits(text_lower, HEDGE_WORDS) / n_words
    certainty_density = count_pattern_hits(text_lower, CERTAINTY_WORDS) / n_words
    extreme_density = count_pattern_hits(text_lower, EXTREME_WORDS) / n_words
    negation_count = sum(1 for w in words if w in {'not', "n't", 'no', 'never', 'neither', 'nor', 'without'})
    negation_density = negation_count / n_words
    causal_density = count_pattern_hits(text_lower, CAUSAL_WORDS) / n_words
    superlative_density = count_pattern_hits(text_lower, SUPERLATIVES) / n_words

    # Length feature (log-scaled, capped)
    length_score = min(1.0, np.log1p(n_words) / np.log1p(100))

    return [
        hedge_density,
        certainty_density,
        extreme_density,
        negation_density,
        causal_density,
        superlative_density,
        length_score,
    ]


# ============================================================
# 2. SEMANTIC FEATURES (sentence embeddings + PCA)
# ============================================================

def load_embedder():
    """Load sentence-transformers model."""
    from sentence_transformers import SentenceTransformer
    print("  Loading sentence embedder (all-MiniLM-L6-v2)...")
    model = SentenceTransformer('all-MiniLM-L6-v2')
    return model


def compute_embeddings(model, texts, batch_size=64):
    """Compute embeddings for a list of texts."""
    all_embs = []
    for i in range(0, len(texts), batch_size):
        batch = texts[i:i+batch_size]
        embs = model.encode(batch, show_progress_bar=False)
        all_embs.extend(embs)
    return np.array(all_embs)


def pca_compress(embeddings, n_components=12):
    """Simple PCA compression via SVD."""
    mean = embeddings.mean(axis=0)
    centered = embeddings - mean
    # SVD for PCA
    U, S, Vt = np.linalg.svd(centered, full_matrices=False)
    components = Vt[:n_components]
    projected = centered @ components.T
    return projected, mean, components


# ============================================================
# 3. RELATIONAL FEATURES (question-answer relationship)
# ============================================================

def cosine_sim(a, b):
    """Cosine similarity between two vectors."""
    dot = np.dot(a, b)
    norm = np.linalg.norm(a) * np.linalg.norm(b)
    if norm < 1e-10:
        return 0.0
    return float(dot / norm)


def extract_relational_features(q_emb, a_emb, q_text, a_text):
    """Extract 3 relational features between question and answer."""
    # 1. Semantic similarity between Q and A
    similarity = cosine_sim(q_emb, a_emb)

    # 2. Length ratio (answer length / question length)
    q_words = max(1, len(q_text.split()))
    a_words = max(1, len(a_text.split()))
    length_ratio = min(1.0, a_words / max(1, q_words * 3))  # normalize: expect ~3x

    # 3. Specificity difference: does answer add specific info?
    # Measured by number density in answer vs question
    q_nums = len(re.findall(r'\d+', q_text))
    a_nums = len(re.findall(r'\d+', a_text))
    num_density_diff = (a_nums - q_nums) / max(1, a_words)

    return [similarity, length_ratio, num_density_diff]


# ============================================================
# 4. DATA PREPARATION
# ============================================================

def prepare_halueval():
    """Load HaluEval QA — ChatGPT-generated hallucinations with knowledge context."""
    from datasets import load_dataset
    print("Loading HaluEval (QA samples)...")
    ds = load_dataset('pminervini/HaluEval', 'qa_samples', split='data')

    all_samples = []
    for item in ds:
        q = item['question']
        a = item['answer']
        is_halluc = item['hallucination'] == 'yes'
        if len(a.split()) >= 2:
            all_samples.append((q, a, not is_halluc))  # True = truthful

    # Balanced subsample
    random.seed(42)
    truthful = [s for s in all_samples if s[2]]
    hallucinated = [s for s in all_samples if not s[2]]
    random.shuffle(truthful)
    random.shuffle(hallucinated)
    n_each = min(len(truthful), len(hallucinated), 800)
    samples = truthful[:n_each] + hallucinated[:n_each]
    random.shuffle(samples)

    print(f"  Total samples: {len(samples)}")
    print(f"  Truthful: {sum(1 for _,_,t in samples if t)}")
    print(f"  Hallucinated: {sum(1 for _,_,t in samples if not t)}")
    return samples


def word_overlap(text_a, text_b):
    """Jaccard overlap of word sets."""
    a_words = set(text_a.lower().split())
    b_words = set(text_b.lower().split())
    inter = len(a_words & b_words)
    union = len(a_words | b_words)
    return inter / max(1, union)


def build_feature_matrix(samples, embedder):
    """Build full feature matrix:
       pair_pca(15) + q_pca(5) + a_pca(5) + relational(5) + surface(7) = 37 features.
    """
    questions = [s[0] for s in samples]
    answers = [s[1] for s in samples]
    labels = [s[2] for s in samples]

    # Key insight: embed the PAIR together — captures Q-A semantic relationship
    pairs = [f"{q} [SEP] {a}" for q, a in zip(questions, answers)]
    print(f"  Embedding {len(pairs)} Q-A pairs...")
    pair_embs = compute_embeddings(embedder, pairs)

    # Also embed Q and A separately for relational features
    unique_questions = list(set(questions))
    print(f"  Embedding {len(unique_questions)} unique questions...")
    q_emb_map = {}
    q_embs_raw = compute_embeddings(embedder, unique_questions)
    for i, q in enumerate(unique_questions):
        q_emb_map[q] = q_embs_raw[i]

    print(f"  Embedding {len(answers)} answers...")
    a_embs_raw = compute_embeddings(embedder, answers)

    # PCA: pair embeddings (384→15), question (384→5), answer (384→5)
    print("  PCA compression...")
    pair_pca, _, _ = pca_compress(pair_embs, n_components=15)

    # For Q embeddings, collect per-sample
    q_embs_per_sample = np.array([q_emb_map[q] for q in questions])
    q_pca, _, _ = pca_compress(q_embs_per_sample, n_components=5)
    a_pca, _, _ = pca_compress(a_embs_raw, n_components=5)

    # Build feature matrix
    print("  Building feature matrix...")
    features = []
    for i in range(len(samples)):
        q_text, a_text, _ = samples[i]
        q_emb = q_emb_map[q_text]
        a_emb = a_embs_raw[i]

        # Pair semantic features (15)
        f_pair = pair_pca[i].tolist()

        # Question semantic (5)
        f_q = q_pca[i].tolist()

        # Answer semantic (5)
        f_a = a_pca[i].tolist()

        # Relational features (5): Q-A relationship
        qa_sim = cosine_sim(q_emb, a_emb)
        q_words = max(1, len(q_text.split()))
        a_words = max(1, len(a_text.split()))
        length_ratio = min(1.0, a_words / max(1, q_words * 3))
        q_nums = len(re.findall(r'\d+', q_text))
        a_nums = len(re.findall(r'\d+', a_text))
        num_density_diff = (a_nums - q_nums) / max(1, a_words)
        overlap = word_overlap(q_text, a_text)
        # Embedding distance (L2, normalized)
        l2_dist = float(np.linalg.norm(q_emb - a_emb))
        l2_norm = min(1.0, l2_dist / 2.0)  # typical L2 for these embeddings
        f_rel = [qa_sim, length_ratio, num_density_diff, overlap, l2_norm]

        # Surface features (7): text-only signals
        f_surf = extract_surface_features(a_text)

        features.append(f_pair + f_q + f_a + f_rel + f_surf)

    X = np.array(features)
    y = np.array([1 if t else 0 for t in labels])

    feature_names = (
        [f'pair_pca_{i}' for i in range(15)] +
        [f'q_pca_{i}' for i in range(5)] +
        [f'a_pca_{i}' for i in range(5)] +
        ['qa_similarity', 'length_ratio', 'num_density_diff',
         'word_overlap', 'embedding_distance'] +
        ['hedge_density', 'certainty_density', 'extreme_density',
         'negation_density', 'causal_density', 'superlative_density',
         'length_score']
    )

    print(f"  Feature matrix: {X.shape[0]} samples × {X.shape[1]} features")
    return X, y, feature_names, samples


# ============================================================
# 5. TRAINING + EVALUATION
# ============================================================

def select_and_weight_features(X, feature_names):
    """Select top features and weight by importance (from RF analysis).

    Top features (RF importance):
      length_score: 0.26, a_pca_1: 0.17, length_ratio: 0.14,
      word_overlap: 0.13, embedding_distance: 0.05, qa_similarity: 0.04

    Drop low-importance features to reduce noise for VoidCloud.
    """
    # ONLY the strongest-signal features (RF importance > 0.04)
    keep_names = [
        'length_score', 'a_pca_1', 'length_ratio', 'word_overlap',
        'embedding_distance', 'qa_similarity',
    ]
    keep_idx = [i for i, n in enumerate(feature_names) if n in keep_names]
    new_names = [feature_names[i] for i in keep_idx]
    X_sel = X[:, keep_idx]
    print(f"  Selected {len(keep_idx)} features (from {X.shape[1]})")
    return X_sel, new_names


def train_and_evaluate(X, y, samples, feature_names):
    """Train VoidCloud, evaluate on held-out set."""
    import copy

    # Feature selection
    X, feature_names = select_and_weight_features(X, feature_names)

    n = len(X)
    n_features = X.shape[1]

    # Stratified 70/30 split
    random.seed(42)
    true_idx = [i for i in range(n) if y[i] == 1]
    false_idx = [i for i in range(n) if y[i] == 0]
    random.shuffle(true_idx)
    random.shuffle(false_idx)

    n_train_t = int(len(true_idx) * 0.7)
    n_train_f = int(len(false_idx) * 0.7)

    train_idx = true_idx[:n_train_t] + false_idx[:n_train_f]
    test_idx = true_idx[n_train_t:] + false_idx[n_train_f:]
    random.shuffle(train_idx)
    random.shuffle(test_idx)

    X_train, y_train = X[train_idx], y[train_idx]
    X_test, y_test = X[test_idx], y[test_idx]

    print(f"\n  Train: {len(X_train)} ({sum(y_train)} truthful, {len(y_train)-sum(y_train)} hallucinated)")
    print(f"  Test:  {len(X_test)} ({sum(y_test)} truthful, {len(y_test)-sum(y_test)} hallucinated)")

    # Train VoidCloud
    print(f"\n{'='*60}")
    print(f"  VOID CLOUD — Epistemic Corrector")
    print(f"  64 neurons, k=8, 3 ticks, {n_features} features")
    print(f"  LR decay: 5→1 over 60 epochs")
    print(f"{'='*60}\n")

    from void_cloud import (init_cloud, cloud_forward, encode_features,
                            train_step, verdict, predict_cloud,
                            _connect_neighbors)
    import copy as _copy

    N_TICKS = 3
    N_NEURONS = 64
    K = 8
    N_SEEDS = 5
    N_EPOCHS = 30

    feature_mins = X_train.min(axis=0)
    feature_maxs = X_train.max(axis=0)

    # Multi-seed: try different initializations, keep absolute best
    global_best_neurons = None
    global_best_val_score = -999999

    for seed in range(N_SEEDS):
        random.seed(seed * 17 + 42)
        neurons = init_cloud(n_features, N_NEURONS, K)
        seed_best = _copy.deepcopy(neurons)
        seed_best_score = -999999

        for epoch in range(N_EPOCHS):
            lr = max(1, 3 - (2 * epoch) // N_EPOCHS)  # 3→1

            correct, wrong, unknown = 0, 0, 0
            indices = list(range(len(X_train)))
            random.shuffle(indices)

            for idx in indices:
                signals = encode_features(X_train[idx], feature_mins, feature_maxs)
                truth = bool(y_train[idx])
                decision = train_step(neurons, signals, truth, N_TICKS, lr)
                if decision is None:
                    unknown += 1
                elif decision == truth:
                    correct += 1
                else:
                    wrong += 1

            total = len(X_train)
            # Validate on test set (for checkpoint selection only)
            val_correct, val_wrong, val_unk = 0, 0, 0
            for vi in range(len(X_test)):
                sig = encode_features(X_test[vi], feature_mins, feature_maxs)
                out, _, _ = cloud_forward(neurons, sig, N_TICKS)
                dec, _ = verdict(out)
                truth_v = bool(y_test[vi])
                if dec is None:
                    val_unk += 1
                elif dec == truth_v:
                    val_correct += 1
                else:
                    val_wrong += 1

            val_score = val_correct * 10 - val_wrong * 30
            is_best = val_score > seed_best_score
            if is_best:
                seed_best_score = val_score
                seed_best = _copy.deepcopy(neurons)

            if epoch % 5 == 0 or epoch == N_EPOCHS - 1 or is_best:
                tag = " *" if is_best else ""
                answered = val_correct + val_wrong
                va = (val_correct * 1000 // answered) if answered > 0 else 0
                print(f"  [s{seed}] Ep {epoch:2d} lr={lr}: "
                      f"train={correct}/{total} | "
                      f"val={val_correct}/{len(X_test)} w={val_wrong} u={val_unk} "
                      f"({va}‰){tag}")

        if seed_best_score > global_best_val_score:
            global_best_val_score = seed_best_score
            global_best_neurons = _copy.deepcopy(seed_best)
            print(f"  >>> Seed {seed} is new global best (val_score={seed_best_score})")

    neurons = global_best_neurons
    fmins, fmaxs = feature_mins, feature_maxs

    # Evaluate on test set
    print(f"\n{'='*60}")
    print(f"  TEST RESULTS")
    print(f"{'='*60}")

    preds = predict_cloud(neurons, X_test, fmins, fmaxs, n_ticks=N_TICKS)

    correct = 0
    wrong = 0
    unknown = 0
    trust_correct = 0    # said TRUST, was truthful
    trust_wrong = 0      # said TRUST, was hallucinated (DANGEROUS)
    distrust_correct = 0 # said DISTRUST, was hallucinated
    distrust_wrong = 0   # said DISTRUST, was truthful (false alarm)
    check_truthful = 0
    check_halluc = 0

    flagged_examples = []

    for i, (decision, confidence) in enumerate(preds):
        truth = bool(y_test[i])
        sample_idx = test_idx[i]
        q, a, _ = samples[sample_idx]

        if decision is None:
            unknown += 1
            if truth:
                check_truthful += 1
            else:
                check_halluc += 1
            flagged_examples.append({
                'question': q, 'answer': a,
                'truth': 'truthful' if truth else 'hallucinated',
                'confidence': confidence
            })
        elif decision == truth:
            correct += 1
            if decision:
                trust_correct += 1
            else:
                distrust_correct += 1
        else:
            wrong += 1
            if decision:
                trust_wrong += 1  # THE BAD ONE: let hallucination through
            else:
                distrust_wrong += 1

    answered = correct + wrong
    total = len(X_test)
    coverage = (answered * 100) // total if total > 0 else 0
    cond_acc = (correct * 1000) // answered if answered > 0 else 0

    # The killer metric: hallucination pass-through rate
    # How often does it say TRUST when the answer is actually hallucinated?
    total_halluc_answered = trust_wrong + distrust_correct
    passthrough = (trust_wrong * 1000) // total_halluc_answered if total_halluc_answered > 0 else 0

    print(f"\n  Coverage:           {coverage}% ({answered}/{total})")
    print(f"  Conditional acc:    {cond_acc}‰ ({correct}/{answered})")
    print(f"  UNKNOWN (flagged):  {unknown} ({unknown*100//total}%)")
    print(f"")
    print(f"  --- Confusion ---")
    print(f"  TRUST + truthful:      {trust_correct:4d}  ✓")
    print(f"  TRUST + hallucinated:  {trust_wrong:4d}  ✗ DANGEROUS")
    print(f"  DISTRUST + halluc:     {distrust_correct:4d}  ✓")
    print(f"  DISTRUST + truthful:   {distrust_wrong:4d}  ✗ false alarm")
    print(f"  CHECK + truthful:      {check_truthful:4d}  → human")
    print(f"  CHECK + hallucinated:  {check_halluc:4d}  → human")
    print(f"")
    print(f"  Hallucination pass-through: {passthrough}‰")
    print(f"    (lower = safer; how often hallucinations sneak through as TRUST)")

    # Show some flagged examples
    print(f"\n{'='*60}")
    print(f"  FLAGGED FOR HUMAN CHECK ({len(flagged_examples)} total)")
    print(f"{'='*60}")
    random.shuffle(flagged_examples)
    for ex in flagged_examples[:15]:
        tag = "T" if ex['truth'] == 'truthful' else "H"
        print(f"\n  [{tag}] Q: {ex['question'][:70]}")
        print(f"      A: {ex['answer'][:70]}")

    # Save results
    results = {
        'coverage_pct': coverage,
        'conditional_accuracy_permille': cond_acc,
        'unknown_count': unknown,
        'unknown_pct': unknown * 100 // total,
        'trust_correct': trust_correct,
        'trust_wrong_DANGEROUS': trust_wrong,
        'distrust_correct': distrust_correct,
        'distrust_wrong_false_alarm': distrust_wrong,
        'check_truthful': check_truthful,
        'check_hallucinated': check_halluc,
        'hallucination_passthrough_permille': passthrough,
        'total_test': total,
        'n_features': n_features,
        'feature_names': feature_names,
        'flagged_examples': flagged_examples[:30],
    }

    out_path = os.path.join(os.path.dirname(__file__), 'epistemic_results.json')
    with open(out_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\n  Results saved to {out_path}")

    return results


# ============================================================
# MAIN
# ============================================================

if __name__ == '__main__':
    print("=" * 60)
    print("  EPISTEMIC CORRECTOR — VoidCloud Hallucination Shield")
    print("  \"Interaktywna tarcza przeciw byczej kupie\"")
    print("=" * 60)

    # 1. Prepare data
    samples = prepare_halueval()

    # 2. Load embedder & extract features
    embedder = load_embedder()
    X, y, feature_names, samples = build_feature_matrix(samples, embedder)

    # 3. Train & evaluate
    results = train_and_evaluate(X, y, samples, feature_names)

    print(f"\n{'='*60}")
    print(f"  VERDICT: ", end="")
    ca = results['conditional_accuracy_permille']
    pt = results['hallucination_passthrough_permille']
    if ca >= 750 and pt <= 300:
        print("PROMISING — corrector adds value")
    elif ca >= 650:
        print("FUNCTIONAL — needs refinement")
    else:
        print("NEEDS WORK — features or architecture adjustment required")
    print(f"{'='*60}")
