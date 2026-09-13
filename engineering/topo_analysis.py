#!/usr/bin/env python3
"""模块级拓扑排序 (Kahn) + 分层: 因模块级无环, 可生成真实编译层序"""
import os, re
import collections
from collections import deque

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

deps = {}
for mod, p in allfiles.items():
    deps[mod] = parse_imports(p) & set(allfiles.keys())

# Kahn: 边 mod -> dep (mod 依赖 dep). 拓扑序 = dep 先于 mod.
in_deg = {m: len(deps[m]) for m in allfiles}
rev = collections.defaultdict(list)
for m in allfiles:
    for d in deps[m]:
        rev[d].append(m)  # d 被 m 依赖; 当 d 排序后, m 的 in_deg 减

q = deque([m for m in allfiles if in_deg[m] == 0])
order = []
while q:
    m = q.popleft()
    order.append(m)
    for depender in rev[m]:
        in_deg[depender] -= 1
        if in_deg[depender] == 0:
            q.append(depender)

print(f"模块总数 {len(allfiles)}, 拓扑排序完成 {len(order)}/{len(allfiles)}")
if len(order) == len(allfiles):
    print("模块级完全无环, 可全拓扑排序!")
else:
    cyc = [m for m in allfiles if in_deg[m] > 0]
    print(f"有环: {len(cyc)} 模块")
    for m in cyc[:20]:
        print("  ", m)
    raise SystemExit

# 分层: 每层 = 同时可编译的模块 (BFS 层)
levels = []
remaining = set(allfiles.keys())
in_deg2 = {m: len(deps[m]) for m in allfiles}
rev2 = collections.defaultdict(list)
for m in allfiles:
    for d in deps[m]:
        rev2[d].append(m)

while remaining:
    layer = [m for m in remaining if in_deg2[m] == 0]
    if not layer:
        break
    levels.append(sorted(layer))
    for m in layer:
        remaining.discard(m)
        for depender in rev2[m]:
            if depender in remaining:
                in_deg2[depender] -= 1

print(f"\n共 {len(levels)} 层 (每层模块互不依赖, 可并行编译)")
for i, layer in enumerate(levels):
    dirs = collections.Counter(m.split('.')[1] if len(m.split('.')) > 1 else '(top)' for m in layer)
    top6 = list(dirs.items())[:6]
    print(f"  L{i}: {len(layer):3d} 模块  目录: {top6}")

# 顶层模块 (不被任何模块依赖)
tops = [m for m in allfiles if len(rev.get(m, [])) == 0]
print(f"\n=== 顶层模块 (无被依赖者, {len(tops)} 个, 候选聚合入口) ===")
for m in sorted(tops):
    print("  ", m)
