#!/usr/bin/env python3
"""Sovereign 库依赖图分析: 模块级 + 目录级, 检测环"""
import os, re, collections
from collections import deque

SRC = 'src/Sovereign'

def parse_imports(path):
    try:
        s = open(path, encoding='utf-8').read()
    except Exception:
        return set()
    return set(re.finditer and [m.group(1) for m in re.finditer(
        r'^\s*(?:open\s+)?import\s+(Sovereign\.[\w.]+)', s, re.M)])

allfiles = {}
for root, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith('.agda'):
            p = os.path.join(root, f)
            rel = os.path.relpath(p, SRC).replace('/', '.')
            allfiles['Sovereign.' + rel[:-5]] = p

print("全库模块总数:", len(allfiles))

deps = {}
for mod, p in allfiles.items():
    deps[mod] = parse_imports(p) & set(allfiles.keys())

def topdir(mod):
    parts = mod.split('.')
    return parts[1] if len(parts) > 1 else '(top)'

dirs = collections.OrderedDict()
for mod in allfiles:
    dirs.setdefault(topdir(mod), []).append(mod)

dirdeps = collections.defaultdict(set)
for mod, ims in deps.items():
    for im in ims:
        dt, dm = topdir(mod), topdir(im)
        if dt != dm:
            dirdeps[dt].add(dm)

all_dirs = list(dirs.keys())
print("\n=== 目录依赖 (A→B 表示 A 依赖 B) ===")
for d in sorted(all_dirs):
    ds = sorted(dirdeps[d])
    print(f"  {d:<20} -> {', '.join(ds) if ds else '(无跨目录)'}")

# Kahn 拓扑 + 环检测
g = {d: dirdeps.get(d, set()) for d in all_dirs}
in_deg = {d: 0 for d in all_dirs}
for d in all_dirs:
    for dep in g[d]:
        in_deg[dep] += 1
q = deque([d for d in all_dirs if in_deg[d] == 0])
order = []
while q:
    d = q.popleft()
    order.append(d)
    for dep in g[d]:
        in_deg[dep] -= 1
        if in_deg[dep] == 0:
            q.append(dep)
print("\n拓扑序可全排序:", len(order) == len(all_dirs), f"({len(order)}/{len(all_dirs)})")
if len(order) < len(all_dirs):
    cyc = [d for d in all_dirs if in_deg[d] > 0]
    print("环涉及目录:", cyc)
print("\n建议编译层序 (被依赖者先):", " -> ".join(order))

print("\n\n=== 模块级: 关键目录间双向依赖的具体模块 ===")
key_pairs = [('Algebra', 'Structology'), ('Algebra', 'Physics'), ('Physics', 'Structology'),
             ('HoTT', 'Structology'), ('Format', 'Structology'), ('Analysis', 'Algebra'),
             ('Physics', 'Algebra'), ('Structology', 'Algebra')]
for a, b in key_pairs:
    print(f"\n-- {a} 依赖 {b}:")
    cnt = 0
    for mod in sorted(deps):
        if topdir(mod) == a:
            for im in sorted(deps[mod]):
                if topdir(im) == b:
                    print(f"    {mod} -> {im}")
                    cnt += 1
                    if cnt >= 8:
                        break
            if cnt >= 8:
                break
