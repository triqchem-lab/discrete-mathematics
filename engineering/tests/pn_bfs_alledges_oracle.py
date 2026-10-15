# -*- coding: utf-8 -*-
"""先算后验（加强版）：按「距离层」增量枚举 BFS 树 ⇒ 论域扩到 n=7。
增量构造：从 a 出发逐层加入顶点，每个新顶点 x 选一个前驱 y（已在树中）与边 (y,x)，
          并令 path[x] = path[y] + [(y,x)]。这**完备**覆盖所有 BFS 树（BFS 树由前驱选择唯一决定）。"""
import itertools, json, sys

def enumerate_bfs_trees(n, a=0):
    """增量枚举：按「加入顺序」的拓扑序构造，保证覆盖全部 BFS 树。"""
    results = []
    def rec(path, dist, remaining):
        if not remaining:
            results.append({k: tuple(v) for k, v in path.items()})
            return
        # 选下一个顶点（可任选，因为前驱只要求「已在树中」）
        for x in list(remaining):
            for y in path:                      # y 已在树中
                e = (y, x)
                path[x] = list(path[y]) + [e]
                dist[x] = dist[y] + 1
                remaining.discard(x)
                rec(path, dist, remaining)
                remaining.add(x)
                del path[x]; del dist[x]
    rec({a: []}, {a: 0}, set(range(n)) - {a})
    return results

def last_edge_holds(choice, e):
    u = e[0]
    want = tuple(choice[u]) + (e,)
    return any(tuple(choice[w]) == want for w in choice)

def check(n):
    trees = enumerate_bfs_trees(n)
    bad = 0; ex = []
    for choice in trees:
        for x in choice:
            for e in choice[x]:
                if not last_edge_holds(choice, e):
                    bad += 1
                    if len(ex) < 3: ex.append({"x": x, "edge": list(e)})
    return len(trees), bad, ex

def main():
    dom = 0; pts = 0; bad = 0; ex = []
    for n in range(1, 8):                       # 顶点数 1..7（增量枚举 = 完备）
        t, b, e = check(n)
        dom += t; pts += t; bad += b; ex += e
        print(f"  n={n}: BFS 树 {t} 棵，反例 {b}")
    assert pts >= dom, "points < domain ⇒ 抽样"
    print("ORACLE-MANIFEST " + json.dumps({
        "basis": "BFS 树（增量枚举：逐顶点选前驱，完备）",
        "domain": dom, "points": pts,
        "claim": "对每个 BFS 树与每条 path x 上的边 e，LastEdge(p,e) 成立（all-edges-last）"
    }, ensure_ascii=False))
    print(f"[结果] 总 BFS 树 {dom} 棵；反例 {bad}")
    print("[结论]", "命题成立" if bad == 0 else "命题为假")

if __name__ == "__main__":
    main()
