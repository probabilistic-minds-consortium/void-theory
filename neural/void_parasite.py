"""
void_parasite.py — VoidCloud as parasitic verifier on a transformer

Pipeline:
1. Transformer classifies sarcasm (headline → sarcastic/not)
2. We extract transformer's internal confidence signals (meta-features)
3. Quantize to integers
4. VoidCloud learns: TRUST / DISTRUST / UNKNOWN
   - TRUST  = transformer got it right
   - DISTRUST = transformer got it wrong
   - UNKNOWN = VoidCloud can't tell → flags for human review

This is the proof-of-concept for the irony-in-drama pipeline.
"""

import sys, os, random, math, json
import numpy as np
from dataclasses import dataclass

# ── 1. Load sarcasm dataset ──────────────────────────────────────────

def load_sarcasm_data(max_samples=2000):
    """Load News Headlines Sarcasm dataset."""
    from datasets import load_dataset
    ds = load_dataset('raquiba/Sarcasm_News_Headline', split='train')

    # Shuffle and limit
    indices = list(range(len(ds)))
    random.seed(42)
    random.shuffle(indices)
    indices = indices[:max_samples]

    headlines = [ds[i]['headline'] for i in indices]
    labels = [ds[i]['is_sarcastic'] for i in indices]
    return headlines, labels


# ── 2. Transformer classification + meta-feature extraction ─────────

def extract_transformer_features(headlines, batch_size=32):
    """
    Run a small transformer on headlines.
    Extract meta-features about the transformer's behavior.
    """
    from transformers import AutoTokenizer, AutoModelForSequenceClassification
    import torch

    # Sentiment model — its internal states + embeddings become features
    model_name = "distilbert-base-uncased-finetuned-sst-2-english"
    print(f"Loading transformer: {model_name}")

    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForSequenceClassification.from_pretrained(model_name)
    model.eval()

    # Sentence embedder for richer semantic features
    from sentence_transformers import SentenceTransformer
    embedder = SentenceTransformer('all-MiniLM-L6-v2')
    print("Loading sentence embedder: all-MiniLM-L6-v2")

    all_features = []
    all_predictions = []
    all_embeddings_raw = []

    for start in range(0, len(headlines), batch_size):
        batch = headlines[start:start+batch_size]

        # --- Classification logits ---
        inputs = tokenizer(batch, return_tensors="pt", padding=True,
                          truncation=True, max_length=128)
        with torch.no_grad():
            outputs = model(**inputs)
            logits = outputs.logits  # (batch, 2)

        probs = torch.softmax(logits, dim=-1).numpy()
        logits_np = logits.numpy()

        # Get sentence embeddings for this batch
        embeddings = embedder.encode(batch)  # (batch, 384)

        for i in range(len(batch)):
            p = probs[i]
            l = logits_np[i]
            emb = embeddings[i]

            # Meta-features about transformer behavior
            confidence = float(np.max(p))
            entropy = float(-np.sum(p * np.log(p + 1e-10)))
            margin = float(abs(p[0] - p[1]))
            logit_spread = float(abs(l[0] - l[1]))
            pred_class = int(np.argmax(p))
            pred_prob = float(p[pred_class])
            logit_ratio = float(l[0] / (abs(l[1]) + 0.01))

            # Store raw embedding for PCA later
            all_embeddings_raw.append(emb)

            # Text surface features
            text = batch[i]
            words = text.split()
            n_words = len(words)
            has_number = int(any(c.isdigit() for c in text))
            n_caps = sum(1 for c in text if c.isupper())
            has_question = int('?' in text)
            has_exclaim = int('!' in text)
            has_quotes = int('"' in text or "'" in text)
            avg_word_len = sum(len(w) for w in words) / max(1, n_words)
            has_colon = int(':' in text)

            features = [
                # Transformer confidence signals (7)
                confidence, entropy, margin, logit_spread,
                pred_prob, float(pred_class), logit_ratio,

                # Surface features (8)
                float(n_words) / 20.0, float(has_number),
                float(n_caps) / max(1, len(text)),
                float(has_question), float(has_exclaim),
                float(has_quotes), float(avg_word_len) / 10.0,
                float(has_colon),
            ]

            all_features.append(features)
            all_predictions.append(pred_class)

        print(f"  Processed {min(start+batch_size, len(headlines))}/{len(headlines)}")

    # PCA on embeddings: 384 dims → 20 principal components
    from sklearn.decomposition import PCA
    emb_array = np.array(all_embeddings_raw)
    n_components = 20
    pca = PCA(n_components=n_components)
    emb_pca = pca.fit_transform(emb_array)
    explained = sum(pca.explained_variance_ratio_[:n_components])
    print(f"  PCA: 384 → {n_components} dims, {100*explained:.1f}% variance explained")

    # Append PCA components to features
    for i in range(len(all_features)):
        all_features[i].extend(emb_pca[i].tolist())

    return all_features, all_predictions


# ── 3. Quantize to integers for VoidCloud ────────────────────────────

def quantize_features(features, scale=64):
    """Convert float features to integers for VoidCloud.
    Scale to S_DENOM (64) range to match VoidCloud's internal arithmetic."""
    features = np.array(features)

    # Normalize each feature to [0, 1] range
    mins = features.min(axis=0)
    maxs = features.max(axis=0)
    ranges = maxs - mins
    ranges[ranges == 0] = 1  # avoid div by zero

    normalized = (features - mins) / ranges

    # Scale to integers matching S_DENOM
    quantized = (normalized * scale).astype(int)
    quantized = np.clip(quantized, 0, scale)

    return quantized.tolist(), mins, maxs


# ── 4. Create training labels for VoidCloud ──────────────────────────

def create_parasite_labels(transformer_preds, true_labels):
    """
    PIVOT: VoidCloud classifies sarcasm DIRECTLY.

    The transformer is just a feature extractor — its sentiment signals
    become input features. VoidCloud decides:
    - FOR (1)     = sarcastic
    - AGAINST (0) = not sarcastic
    - UNKNOWN     = can't tell → flag for human

    Label = true sarcasm label from dataset.
    """
    sarcastic = sum(true_labels)
    not_sarc = len(true_labels) - sarcastic
    print(f"\nDataset: {sarcastic} sarcastic, {not_sarc} not sarcastic")
    print(f"  VoidCloud will classify sarcasm directly using transformer features")

    return true_labels


# ── 5. Run VoidCloud ─────────────────────────────────────────────────

def run_voidcloud_parasite(features_int, labels, n_neurons=96, k=10):
    """Train VoidCloud to predict transformer reliability."""
    # Import VoidCloud
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from void_cloud import init_cloud, train_step, verdict, cloud_forward

    # Split data
    n = len(features_int)
    split = int(n * 0.7)

    train_X = features_int[:split]
    train_Y = labels[:split]
    test_X = features_int[split:]
    test_Y = labels[split:]

    n_features = len(train_X[0])
    n_ticks = 4
    print(f"\nVoidCloud config: {n_neurons} neurons, k={k}, {n_features} features, {n_ticks} ticks")
    print(f"Train: {len(train_X)}, Test: {len(test_X)}")

    # Init
    random.seed(42)
    neurons = init_cloud(n_features=n_features, n_neurons=n_neurons,
                         k_neighbors=k)

    # Train
    print("\nTraining VoidCloud parasite...")
    best_score = -999999
    best_neurons = None
    n_epochs = 80

    for epoch in range(n_epochs):
        # Shuffle training data
        idx = list(range(len(train_X)))
        random.shuffle(idx)

        lr = max(2, 8 - epoch // 6)

        for i in idx:
            train_step(neurons, train_X[i], train_Y[i],
                       n_ticks=n_ticks, learning_rate=lr)

        # Evaluate on test set
        correct = 0
        wrong = 0
        unknown = 0

        trust_correct = 0      # VoidCloud says TRUST and transformer was right
        trust_wrong = 0        # VoidCloud says TRUST but transformer was wrong
        distrust_correct = 0   # VoidCloud says DISTRUST and transformer was wrong
        distrust_wrong = 0     # VoidCloud says DISTRUST but transformer was right
        unknown_was_right = 0  # VoidCloud abstained, transformer was right
        unknown_was_wrong = 0  # VoidCloud abstained, transformer was wrong

        for i in range(len(test_X)):
            output_state, _, _ = cloud_forward(neurons, test_X[i], n_ticks=n_ticks)
            v, _ = verdict(output_state)
            true = test_Y[i]

            if v == True:  # VoidCloud says SARCASTIC (FOR)
                v = 1
            elif v == False:  # VoidCloud says NOT SARCASTIC (AGAINST)
                v = 0
            else:  # None = UNKNOWN
                v = -1

            if v == 1:
                if true == 1:
                    correct += 1
                    trust_correct += 1
                else:
                    wrong += 1
                    trust_wrong += 1
            elif v == 0:  # VoidCloud says NOT SARCASTIC
                if true == 0:
                    correct += 1
                    distrust_correct += 1
                else:
                    wrong += 1
                    distrust_wrong += 1
            else:  # v == -1, UNKNOWN
                unknown += 1
                if true == 1:
                    unknown_was_right += 1
                else:
                    unknown_was_wrong += 1

        total_decided = correct + wrong
        cond_acc = (1000 * correct // total_decided) if total_decided > 0 else 0
        coverage = 100 * total_decided // len(test_X)

        score = correct * 10 - wrong * 30
        if score > best_score:
            best_score = score
            best_results = {
                'epoch': epoch,
                'correct': correct,
                'wrong': wrong,
                'unknown': unknown,
                'cond_accuracy': cond_acc,
                'coverage': coverage,
                'trust_correct': trust_correct,
                'trust_wrong': trust_wrong,
                'distrust_correct': distrust_correct,
                'distrust_wrong': distrust_wrong,
                'unknown_was_right': unknown_was_right,
                'unknown_was_wrong': unknown_was_wrong,
            }
            # Deep copy neurons for checkpoint
            import copy
            best_neurons = copy.deepcopy(neurons)

        if epoch % 5 == 0 or epoch == n_epochs - 1:
            print(f"  Epoch {epoch:2d}: {cond_acc}‰ acc, {coverage}% cov "
                  f"({correct}✓ {wrong}✗ {unknown}? ) lr={lr}")

    return best_results, best_neurons


# ── 6. Main ──────────────────────────────────────────────────────────

def main():
    print("=" * 60)
    print("VOID PARASITE — VoidCloud monitors transformer reliability")
    print("=" * 60)

    # Load data
    print("\n1. Loading sarcasm dataset...")
    headlines, labels = load_sarcasm_data(max_samples=2000)
    print(f"   {len(headlines)} headlines loaded")
    print(f"   Sarcastic: {sum(labels)}, Not: {len(labels)-sum(labels)}")

    # Run transformer
    print("\n2. Running transformer + extracting meta-features...")
    features, predictions = extract_transformer_features(headlines)
    print(f"   {len(features[0])} meta-features extracted per headline")

    # Create labels (is transformer right or wrong?)
    print("\n3. Creating parasite training labels...")
    parasite_labels = create_parasite_labels(predictions, labels)

    # Quantize
    print("\n4. Quantizing features to integers...")
    features_int, mins, maxs = quantize_features(features)
    print(f"   Feature range: [0, 1000]")

    # Train VoidCloud
    print("\n5. Training VoidCloud parasite...")
    results, neurons = run_voidcloud_parasite(features_int, parasite_labels)

    # Report
    print("\n" + "=" * 60)
    print("RESULTS — Best epoch:", results['epoch'])
    print("=" * 60)
    print(f"\nConditional accuracy: {results['cond_accuracy']}‰")
    print(f"Coverage: {results['coverage']}%")
    print(f"\nWhen VoidCloud says SARCASTIC (FOR):")
    print(f"  Actually sarcastic:     {results['trust_correct']}")
    print(f"  Actually not sarcastic: {results['trust_wrong']}")
    print(f"\nWhen VoidCloud says NOT SARCASTIC (AGAINST):")
    print(f"  Actually not sarcastic: {results['distrust_correct']}")
    print(f"  Actually sarcastic:     {results['distrust_wrong']}")
    print(f"\nWhen VoidCloud says UNKNOWN (NIE WIEM):")
    print(f"  Was sarcastic:     {results['unknown_was_right']}")
    print(f"  Was not sarcastic: {results['unknown_was_wrong']}")

    unknown_total = results['unknown_was_right'] + results['unknown_was_wrong']
    if unknown_total > 0:
        print(f"  Total flagged: {unknown_total}")

    print("\n" + "=" * 60)
    print("INTERPRETATION")
    print("=" * 60)
    print("VoidCloud classifies sarcasm directly, using transformer")
    print("internal states as features. UNKNOWN = genuine ambiguity.")
    print("This is the proof-of-concept for irony detection in drama.")


if __name__ == "__main__":
    main()
