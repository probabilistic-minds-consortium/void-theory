import os
import re
from collections import defaultdict, deque

# Get all .v files
all_files = set(f[:-2] for f in os.listdir('.') if f.endswith('.v'))

# Extract dependencies for each file
deps = defaultdict(set)
for base_name in all_files:
    with open(f'{base_name}.v', 'r') as f:
        content = f.read()
        # Find all "Require Import void_*" lines
        for match in re.finditer(r'Require Import void_(\w+)', content):
            dep = f"void_{match.group(1)}"
            if dep in all_files:
                deps[f"void_{base_name.split('void_')[1]}"].add(dep)

# Topological sort
in_degree = defaultdict(int)
for file in all_files:
    in_degree[file] = 0

for file in all_files:
    for dep in deps[file]:
        in_degree[file] += 1

queue = deque([f for f in all_files if in_degree[f] == 0])
result = []

while queue:
    node = queue.popleft()
    result.append(node)
    
    # Find files that depend on this one
    for file in all_files:
        if node in deps[file]:
            in_degree[file] -= 1
            if in_degree[file] == 0:
                queue.append(file)

for f in result:
    print(f)
