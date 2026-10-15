# -*- coding: utf-8 -*-
"""先算后验（修正版）：BFS 树中「LastEdge e」与「LastEdge (flip e)」能否同时成立？

正确索引：LastEdge 的候选是「**各 path x 的末边**」（x ≠ a）。
  · path[x] = path[y] + [e]，e = (y,x)  ⇒ LastEdge(y, x, e) 成立（定义层）
  · 问：LastEdge(x, y, (x,y))（即 flip 方向）是否也能成立？
"""
import json

def enumerate_bfs_trees(n, a=0):
    results = []
    def rec(path, dist, remaining):
        if not remaining:
            results.append({k: tuple(v) for k, v in path.items()}); return
        for x in list(remaining):
            for y in path:
                e = (y, x)
                path[x] = list(path[y]) + [e]; dist[x] = dist[y] + 1
                remaining.discard(x); rec(path, dist, remaining); remaining.add(x)
                del path[x]; del dist[x]
    rec({a: []}, {a: 0}, set(range(n)) - {a})
    return results

def check(n):
    both = 0; fwd = 0; ex = []
    for ch in enumerate_bfs_trees(n):
        for x in ch:
            if x == 0 or not ch[x]: continue
            y, e = ch[x][-1][0], ch[x][-1]          # 末边 e = (y, x)
            f = last_fwd = (tuple(ch[x]) == tuple(ch[y]) + (e,))
            b = (tuple(ch[y]) == tuple(ch[x]) + ((x, y),))
            if f: fwd += 1
            if f and b:
                both += 1
                if len(ex) < 3: ex.append({"x": x, "y": y})
    return both, fwd, ex

def main():
    dom = 0; both = 0; fwd = 0; ex = []
    for n in range(1, 8):
        b, f, e = check(n); dom += 1; both += b; fwd += f; ex += e
        print(f"  n={n}: 正向成立 {f} 例；同时成立 {b} 例")
    print("ORACLE-MANIFEST " + json.dumps({
        "basis": "BFS 树（增量枚举，完备）", "domain": dom, "points": dom,
        "claim": "BFS 树中 LastEdge(正向) 与 LastEdge(flip 方向) 不可能同时成立"
    }, ensure_ascii=False))
    print(f"[结果] 正向 {fwd} 例；同时成立 {both} 例")
    print("[结论]", "两支互斥 ⇒ 对称化 IsTree 的第二支在 BFS 树中**恒假** ⇒ flip-tree 无法由 BFS 不变量推出" if both == 0 else "两支可同时成立")

if __name__ == "__main__":
    main()
