#!/usr/bin/env python3
"""A₄ 闭包核验（精确整数，无浮点）：{shift, flip} 生成的群 = A₄ ⊂ SO(3) 的 3 维表示。

shift = [[0,0,1],[1,0,0],[0,1,0]]   （3-循环）
flip  = diag(-1,-1,1)               （反演型 180° 旋转，det = +1）

判据（全部用 Python 整数精确计算）：
  1. 闭包元素个数 = 12
  2. 每个元素都是「有符号置换矩阵」（每行每列恰一个 ±1）
  3. 每个元素 det = +1（⇒ 落在 SO(3)，正是 A₄ 的 3 维表示）
  4. ord(shift)=3、ord(flip)=2、ord(flip∘shift)=3（展示关系 s³=f²=(fs)³=1）

用法: python3 engineering/verify_a4_closure.py
"""
import itertools
import json
import sys

S = ((0, 0, 1), (1, 0, 0), (0, 1, 0))
F = ((-1, 0, 0), (0, -1, 0), (0, 0, 1))


def mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)) for i in range(3))


def det(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))


def is_signed_perm(A):
    for row in A:
        if sorted(abs(x) for x in row) != [0, 0, 1]:
            return False
    for j in range(3):
        if sorted(abs(A[i][j]) for i in range(3)) != [0, 0, 1]:
            return False
    return True


def order(A):
    M, n = A, 1
    I = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    while M != I and n <= 12:
        M = mul(A, M)
        n += 1
    return n


def main():
    G = {((1, 0, 0), (0, 1, 0), (0, 0, 1))}
    frontier = [((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    while frontier:
        new = []
        for A in frontier:
            for B in (S, F):
                M = mul(B, A)
                if M not in G:
                    G.add(M)
                    new.append(M)
        frontier = new
    mats = sorted(G)
    checks = {
        "closure_order": len(mats),
        "all_signed_permutation": all(is_signed_perm(M) for M in mats),
        "all_det_plus_one": all(det(M) == 1 for M in mats),
        "order_shift": order(S),
        "order_flip": order(F),
        "order_flip_comp_shift": order(mul(F, S)),
    }
    ok = (checks["closure_order"] == 12 and checks["all_signed_permutation"]
          and checks["all_det_plus_one"] and checks["order_shift"] == 3
          and checks["order_flip"] == 2 and checks["order_flip_comp_shift"] == 3)
    print(json.dumps(checks, indent=1))
    print("ORACLE-MANIFEST " + json.dumps({
        "basis": "3x3 integer matrices (exact, no floats)",
        "domain": 12, "points": len(mats),
        "claim": "closure of {shift, flip} = A4 (order 12), all det=+1 signed permutations; orders 3/2/3"}))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
