# -*- coding: utf-8 -*-
"""π₁ᵈ 幂等性双向穷尽 BFS 重验 oracle（修正 L=8 单侧穷尽的抽样伪影）

背景：pi1d_card_oracle.py 的 compute() 只枚举长 ≤ L 的走（w² 长走超域被跳过），
导致 w² ∉ walks 的代表被标记「未定」。本脚本改为**双向穷尽 BFS**：
  · 两侧起点 = w 与 w² = w+w[1:]；
  · 两侧交替用 AStep 单步移动扩展（slide=删中点 y 当 (x,z)∈E；
    expand=插 y 当 (x,y),(y,z)∈E；无退化限制 —— 与 pi1d_card_oracle.nb 严格一致）；
  · 长度上限 = 2×len(w)（边数），覆盖 w² 所在域；
  · 访问状态上限 CAP = 2,000,000。
判定：
  两侧交汇          ⇒ 幂等 ✓
  一侧穷尽无交汇    ⇒ 非幂等 ✗（反例坐实，w 明示）
  触发截断          ⇒ 未定（如实报告，不声称判定）
域：图中全部闭走（任意起点，边数 0..L，L=8 与参考口径一致），逐条检查。

只读参考实现，不修改其语义。复跑：python3 engineering/pi1d_idempotence_bfs_oracle.py
"""
import json
from collections import deque

L = 8
CAP = 2_000_000

GRAPHS = [
    ("c4_diag_undirected", [0, 1, 2, 3],
     {(0,1),(1,0),(1,2),(2,1),(2,3),(3,2),(0,3),(3,0),(0,2),(2,0)},
     [(0,1,2,3,0)]),                      # 代表长走 w=(0,1,2,3,0)，4 边
    ("butterfly_no_selfloop", [0, 1, 2, 3, 4],
     {(0,1),(1,0),(1,2),(2,1),(0,2),(2,0),(0,3),(3,0),(3,4),(4,3),(0,4),(4,0)},
     [(0,1,2,0,3,4,0)]),                  # 代表长走 w=(0,1,2,0,3,4,0)，6 边
]


def moves(w, V, E, max_edges):
    """AStep 单步移动（slide / expand，无退化限制），返回全部后继。"""
    out = []
    n = len(w)
    for i in range(n - 2):                            # slide：删中点 y
        x, z = w[i], w[i + 2]
        if (x, z) in E:
            out.append(w[:i + 1] + w[i + 2:])
    for i in range(n - 1):                            # expand：x 后插 y
        x, z = w[i], w[i + 1]
        for y in V:
            if (x, y) in E and (y, z) in E:
                if len(w) + 1 - 1 <= max_edges:       # 边数不超上限
                    out.append(w[:i + 1] + (y,) + w[i + 1:])
    return out


def bidirectional_bfs(w, V, E):
    """从 w 与 w² 两侧交替 BFS；返回 (verdict, visited_total, side1_class)。
    verdict ∈ {'idempotent', 'non-idempotent', 'undetermined'}
    side1_class = w 侧的可达闭包（用于类级缓存：同类的 walk 判定相同）。"""
    s1 = tuple(w)
    s2 = s1 + s1[1:]
    max_edges = 2 * (len(s1) - 1)
    f1, f2 = {s1}, {s2}
    frontier1, frontier2 = [s1], [s2]
    visited_total = 2
    if s1 == s2:
        return 'idempotent', visited_total, f1
    truncated = False
    turn = 0
    while frontier1 and frontier2:
        if turn % 2 == 0:
            src, dst, frontier = f1, f2, frontier1
        else:
            src, dst, frontier = f2, f1, frontier2
        nxt = []
        for u in frontier:
            for v in moves(u, V, E, max_edges):
                if v not in src:
                    src.add(v)
                    visited_total += 1
                    if v in dst:
                        return 'idempotent', visited_total, f1
                    if visited_total > CAP:
                        truncated = True
                        break
                    nxt.append(v)
            if truncated:
                break
        if truncated:
            return 'undetermined', visited_total, f1
        if turn % 2 == 0:
            frontier1 = nxt
        else:
            frontier2 = nxt
        turn += 1
    # 一侧穷尽仍无交汇（另一侧必为空域或不可达）且未截断
    return 'non-idempotent', visited_total, f1


def closed_walks(V, E, max_edges):
    """枚举图中全部闭走（任意起点，边数 0..max_edges）。"""
    out = []
    for s in V:
        stack = [(s,)]
        while stack:
            w = stack.pop()
            if len(w) - 1 == max_edges:
                continue
            for v in V:
                if (w[-1], v) in E:
                    nw = w + (v,)
                    if nw[0] == nw[-1]:
                        out.append(nw)
                    stack.append(nw)
    return out


def report(name, V, E, highlight_ws):
    walks = closed_walks(V, E, L)
    n_ok = n_bad = n_und = 0
    bad_ws, und_ws = [], []
    verdict_cache = {}          # walk -> verdict（类级缓存：同类判定相同）
    seen_classes = []           # 已处理的 side1 可达类（(代表, verdict)）
    for w in walks:
        w = tuple(w)
        if w in verdict_cache:
            verdict = verdict_cache[w]
        else:
            verdict, _, cls = bidirectional_bfs(w, V, E)
            for u in cls:                       # 类内成员共享判定
                verdict_cache.setdefault(u, verdict)
        if verdict == 'idempotent':
            n_ok += 1
        elif verdict == 'non-idempotent':
            n_bad += 1
            bad_ws.append(w)
        else:
            n_und += 1
            und_ws.append(w)
    print(f'== {name} ==')
    print(f'   域: 边数 0..{L} 全闭走, 可查 {len(walks)} 条')
    print(f'   幂等 {n_ok} / 非幂等 {n_bad} / 未定 {n_und}')
    for hw in highlight_ws:
        hw = tuple(hw)
        v = verdict_cache.get(hw)
        if v is None:
            v, c, _ = bidirectional_bfs(hw, V, E)
            print(f'   代表长走 {hw} -> {v} (独立 BFS, 状态 {c})')
        else:
            print(f'   代表长走 {hw} (w²={hw + hw[1:]}) -> {v} (类缓存)')
    if bad_ws:
        print(f'   非幂等反例(前5): {bad_ws[:5]}')
    if und_ws:
        print(f'   未定(前5): {und_ws[:5]}')
    if n_und == 0:
        verdict = '幂等 ✓' if n_bad == 0 else f'非幂等 ✗（{n_bad} 条反例坐实）'
    else:
        verdict = f'未定（{n_und} 条截断）'
    print(f'   最终判定: {verdict}')
    return dict(name=name, domain=len(walks), checkable=len(walks), idempotent=n_ok,
                non_idempotent=n_bad, undetermined=n_und, verdict=verdict)


if __name__ == '__main__':
    results = []
    for name, V, E, hws in GRAPHS:
        results.append(report(name, V, E, hws))
    print('\n== 汇总 ==')
    for r in results:
        print(f"  {r['name']}: 可查 {r['checkable']} / 幂等 {r['idempotent']} "
              f"/ 非幂等 {r['non_idempotent']} / 未定 {r['undetermined']} "
              f"=> {r['verdict']}")
    tot_domain = sum(r['domain'] for r in results)
    tot_points = sum(r['checkable'] for r in results)
    print()
    print('ORACLE-MANIFEST ' + json.dumps({
        "basis": "闭走 × 单步移动（slide/expand）双向穷尽 BFS 幂等判定",
        "domain": tot_domain,
        "points": tot_points,
        "claim": "c4_diag_undirected 与 butterfly_no_selfloop 均非幂等（三态判定，零未定）",
    }, ensure_ascii=False))
