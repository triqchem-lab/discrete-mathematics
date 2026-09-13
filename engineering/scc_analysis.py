#!/usr/bin/env python3
"""模块级 SCC (Tarjan) + 分层分析: 找出真强连通分量与可独立编译层"""
import os, re
import collections

SRC = 'src/Sovereign'

def parse_imports(path):
    try:
        s = open(path, encoding='utf-8').read()
    except Exception:
        return set()
    return set(m.group(1) for m in re.finditer(
        r'^\s*(?:open\s+)?import\s+(Sovereign\.[\w.]+)', s, re.M))

allfiles = {}
for root, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith('.agda'):
            p = os.path.join(root, f)
            rel = os.path.relpath(p, SRC).replace('/', '.')
            allfiles['Sovereign.' + rel[:-5]] = p

# 排除 All 自身 (它在被拆)
deps = {}
for mod, p in allfiles.items():
    deps[mod] = parse_imports(p) & set(allfiles.keys())

# Tarjan SCC
index = 0
stack = []
onstack = set()
indices = {}
lowlink = {}
sccs = []

def strongconnect(v):
    global index
    indices[v] = index
    lowlink[v] = index
    index += 1
    stack.append(v)
    onstack.add(v)
    for w in deps.get(v, ()):
        if w not in indices:
            strongconnect(w)
            lowlink[v] = min(lowlink[v], lowlink[w])
        elif w in onstack:
            lowlink[v] = min(lowlink[v], indices[w])
    if lowlink[v] == indices[v]:
        comp = []
        while True:
            w = stack.pop()
            onstack.remove(w)
            comp.append(w)
            if w == v:
                break
        sccs.append(comp)

for v in allfiles:
    if v not in indices:
        strongconnect(v)

# 排序: 大 SCC 在前
sccs.sort(key=len, reverse=True)
print(f"模块总数: {len(allfiles)}, SCC 数: {len(sccs)}")
print(f"\n=== 最大 SCC (规模 > 1) ===")
big = [c for c in sccs if len(c) > 1]
for c in big:
    dirs = collections.Counter(m.split('.')[1] if len(m.split('.')) > 1 else '(top)' for m in c)
    print(f"\nSCC 大小 {len(c)}: 目录分布 {dict(dirs)}")
    for m in sorted(c)[:12]:
        print(f"   {m}")

print(f"\n=== 单模块 SCC (无环, 可独立) 共 {len(sccs) - len(big)} 个 ===")
# 把这些无环模块按它们的依赖分层 (Kahn 于压缩图)
single = [c[0] for c in sccs if len(c) == 1]
print("示例:", sorted(single)[:15])
