#!/usr/bin/env python3
# 阶段 1a：拓扑序（叶子→根）+ 循环检测。用法: topo-sort.py dep-graph.csv
import sys, csv, collections
edges = collections.defaultdict(set)
nodes = set()
for row in csv.DictReader(open(sys.argv[1])):
    s, d = row['src'], row['dst']; nodes.add(s); nodes.add(d)
    if s != d: edges[s].add(d)
indeg = {n: 0 for n in nodes}
for s in nodes:
    for d in edges[s]: indeg[d] = indeg.get(d, 0) + 1
# 叶子 = 无出边（无依赖者先迁）→ 反向 Kahn：先输出无入边者=根；我们要叶子→根，故按出度=0 起
outdeg = {n: len(edges[n]) for n in nodes}
q = collections.deque(sorted(n for n in nodes if outdeg[n] == 0))
order, remaining = [], dict(edges)
while q:
    n = q.popleft(); order.append(n)
    for m in list(remaining):
        if n in remaining[m]:
            remaining[m].discard(n)
            if not remaining[m] and m not in order and m not in q: q.append(m)
cyc = [n for n in nodes if remaining.get(n)]
print("# 拓扑序（叶子 → 根），共 %d 节点；循环/未决 %d" % (len(order), len(cyc)))
print("\n".join(order))
if cyc:
    print("\n# 循环/强连通残余（需人工断开）:", file=sys.stderr)
    print("\n".join(sorted(cyc)[:40]), file=sys.stderr)
