"""Multi-seed evaluation of VoidCloud — is 995‰ real or lucky?"""
import sys
sys.path.insert(0, '/sessions/laughing-hopeful-bohr/mnt/void-theory')

import random
from void_cloud import train_cloud, predict_cloud, encode_features
from sklearn.datasets import load_breast_cancer

data = load_breast_cancer()
X, y = data.data, data.target
n = len(X)

print("=" * 65)
print("  VOID CLOUD — Multi-Seed Stability Test (64n, k=8, t=3)")
print("=" * 65)

results = []
for seed in range(10):
    # Patch the seed
    random.seed(seed * 1000 + 42)
    
    # We need to reinitialize with the new seed
    # Manually set seed before train_cloud
    import void_cloud
    old_seed_fn = random.seed
    
    # Override random.seed inside train_cloud
    neurons_result = None
    feature_mins = X.min(axis=0)
    feature_maxs = X.max(axis=0)
    
    random.seed(seed * 1000 + 42)
    neurons = void_cloud.init_cloud(X.shape[1], 64, 8)
    
    import copy
    best_neurons = copy.deepcopy(neurons)
    best_score = -999999
    
    for epoch in range(80):
        correct, wrong, unknown = 0, 0, 0
        indices = list(range(len(X)))
        random.shuffle(indices)
        
        for idx in indices:
            signals = void_cloud.encode_features(X[idx], feature_mins, feature_maxs)
            truth = bool(y[idx])
            decision = void_cloud.train_step(neurons, signals, truth, 3, 5)
            if decision is None: unknown += 1
            elif decision == truth: correct += 1
            else: wrong += 1
        
        score = correct * 10 - wrong * 30
        if score > best_score:
            best_score = score
            best_neurons = copy.deepcopy(neurons)
        
        if epoch % 10 == 0 and epoch >= 20:
            void_cloud._connect_neighbors(neurons, 8, preserve_weights=True)
    
    # Predict with best checkpoint
    preds = void_cloud.predict_cloud(best_neurons, X, feature_mins, feature_maxs, 3)
    
    correct = sum(1 for i, (d, _) in enumerate(preds) if d == bool(y[i]))
    wrong = sum(1 for i, (d, _) in enumerate(preds) if d is not None and d != bool(y[i]))
    unknown = sum(1 for d, _ in preds if d is None)
    answered = correct + wrong
    cov = (answered * 100) // n
    ca = (correct * 1000) // answered if answered > 0 else 0
    
    results.append((correct, wrong, unknown, cov, ca))
    print(f"  Seed {seed}: correct={correct} wrong={wrong} unk={unknown} cov={cov}% ca={ca}‰")

print("\n" + "-" * 65)
avg_correct = sum(r[0] for r in results) // len(results)
avg_wrong = sum(r[1] for r in results) // len(results)
avg_unk = sum(r[2] for r in results) // len(results)
avg_cov = sum(r[3] for r in results) // len(results)
avg_ca = sum(r[4] for r in results) // len(results)
min_ca = min(r[4] for r in results)
max_ca = max(r[4] for r in results)

print(f"  AVERAGE: correct={avg_correct} wrong={avg_wrong} unk={avg_unk} cov={avg_cov}% ca={avg_ca}‰")
print(f"  CA range: {min_ca}‰ — {max_ca}‰")
print(f"  Seeds with ca ≥ 950‰: {sum(1 for r in results if r[4] >= 950)}/10")
print(f"  Seeds with ca ≥ 980‰: {sum(1 for r in results if r[4] >= 980)}/10")
