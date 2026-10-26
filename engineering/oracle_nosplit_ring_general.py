#!/usr/bin/env python3
"""NoSplitJ1Ring 的独立数值核验（先算后验证；全整数 / 精确有理数，无浮点）。

被验命题（`NoSplitJ1Ring.no-split-ring-general` 的独立对照版本）：

  设 R 是无挠交换环，A : 3×3 over R。若 A 与
    S = [[0,0,1],[1,0,0],[0,1,0]]   （3-循环）
    F = diag(-1,-1,1)               （反演型 180° 旋转，det = +1）
  都交换（A·S = S·A 且 A·F = F·A），则 A 的六个非对角元全为 0、三个对角元相等
  （即 A 是标量矩阵）。

判据（四条，互补）：
  ① GF(3)^9 **全空间穷举**：19,683 个矩阵里，与 S、F 都交换的恰好 3 个标量；
  ② **精确消元**（整数 / Fraction，无浮点）：交换子空间（线性方程组的完整解空间）
     在 GF(p)（p = 5, 7, 11, 13, 101）与 ℚ 上维数都是 1 —— 线性系统的解空间由秩
     **完全确定**，这不是抽样；
  ③ **结论不弱**：Agda 主定理的结论（6 个零 + 2 个相等）作为线性方程组，解空间维数
     也是 1 ⇒ 证明了「交换子空间的全部」，不是只证了一部分；
  ④ **无挠性假设不可去**：GF(2) 上 -x = x 恒成立（无挠性要求的 `x ≈ 0` 会迫使环平凡），
     而 A = S 与 S、F 都交换且不是标量 ⇒ 结论在特征 2 上确实失效。

用法: python3 engineering/oracle_nosplit_ring_general.py
"""
import itertools
import json
import sys
from fractions import Fraction

S = ((0, 0, 1), (1, 0, 0), (0, 1, 0))
F = ((-1, 0, 0), (0, -1, 0), (0, 0, 1))
I = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


# ── 3×3 矩阵（元组套元组；整数精确）────────────────────────────────────────

def mm(A, B, mod=None):
    out = []
    for i in range(3):
        row = []
        for j in range(3):
            v = A[i][0] * B[0][j] + A[i][1] * B[1][j] + A[i][2] * B[2][j]
            row.append(v % mod if mod is not None else v)
        out.append(tuple(row))
    return tuple(out)


def flat_to_mat(vals):
    return (tuple(vals[0:3]), tuple(vals[3:6]), tuple(vals[6:9]))


def is_scalar_mod(A, p):
    """A 是否等于 k·I（k ∈ GF(p)）。"""
    for i in range(3):
        for j in range(3):
            want = A[i][j]
            if i != j and want % p != 0:
                return False
    k = A[0][0] % p
    return all(A[i][i] % p == k for i in range(3))


def commutes(A, p):
    return mm(A, S, p) == mm(S, A, p) and mm(A, F, p) == mm(F, A, p)


# ── 线性方程组：把「与 S、F 交换」写成 18×9 的整数系数矩阵 ────────────────

def commuting_system():
    """返回 (M, nvar)：M 的每一行是一条线性方程，未知量是 A 的 9 个元素。"""
    rows = []
    for i in range(3):
        for j in range(3):
            # 与 S 交换： Σ_k A[i][k] S[k][j] − Σ_k S[i][k] A[k][j] = 0
            row = [0] * 9
            for k in range(3):
                row[i * 3 + k] += S[k][j]
                row[k * 3 + j] -= S[i][k]
            rows.append(row)
            # 与 F 交换
            row = [0] * 9
            for k in range(3):
                row[i * 3 + k] += F[k][j]
                row[k * 3 + j] -= F[i][k]
            rows.append(row)
    return rows, 9


def conclusion_system():
    """Agda 主定理结论的 8 条关系（6 个非对角元 = 0，2 个对角元相等）。"""
    rows = []
    for (a, b) in [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]:
        row = [0] * 9
        row[a * 3 + b] = 1
        rows.append(row)
    for (a, b) in [((0, 0), (1, 1)), ((1, 1), (2, 2))]:
        row = [0] * 9
        row[a[0] * 3 + a[1]] = 1
        row[b[0] * 3 + b[1]] = -1
        rows.append(row)
    return rows, 9


def rank_mod(rows, nvar, p):
    """GF(p) 上高斯消元，返回秩。"""
    M = [[x % p for x in r] for r in rows]
    rank = 0
    for col in range(nvar):
        piv = None
        for r in range(rank, len(M)):
            if M[r][col] % p != 0:
                piv = r
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], -1, p)
        M[rank] = [(x * inv) % p for x in M[rank]]
        for r in range(len(M)):
            if r != rank and M[r][col] % p != 0:
                f = M[r][col]
                M[r] = [(M[r][c] - f * M[rank][c]) % p for c in range(nvar)]
        rank += 1
    return rank


def rank_rational(rows, nvar):
    """ℚ 上精确高斯消元（Fraction），返回秩。"""
    M = [[Fraction(x) for x in r] for r in rows]
    rank = 0
    for col in range(nvar):
        piv = None
        for r in range(rank, len(M)):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = Fraction(1) / M[rank][col]
        M[rank] = [x * inv for x in M[rank]]
        for r in range(len(M)):
            if r != rank and M[r][col] != 0:
                f = M[r][col]
                M[r] = [M[r][c] - f * M[rank][c] for c in range(nvar)]
        rank += 1
    return rank


def vec_of(mat):
    return [mat[i][j] for i in range(3) for j in range(3)]


def applies_zero(rows, v):
    return all(sum(r[k] * v[k] for k in range(9)) == 0 for r in rows)


# ── 各检查项 ───────────────────────────────────────────────────────────────

def check_gf3_exhaustive():
    """GF(3)^9 全穷举（19,683 个矩阵）。"""
    total = 0
    commutants = 0
    nonscalar = 0
    for vals in itertools.product(range(3), repeat=9):
        total += 1
        A = flat_to_mat(vals)
        if commutes(A, 3):
            commutants += 1
            if not is_scalar_mod(A, 3):
                nonscalar += 1
    return {
        "domain": total,
        "points": total,
        "commutants": commutants,
        "non_scalar_commutants": nonscalar,
        "ok": total == 3 ** 9 and commutants == 3 and nonscalar == 0,
    }


def check_exact_linear_algebra():
    """交换子空间维数：GF(p)（若干素数）与 ℚ，精确消元。"""
    rows, nvar = commuting_system()
    primes = [5, 7, 11, 13, 101]
    per_prime = {}
    ok = True
    for p in primes:
        nullity = nvar - rank_mod(rows, nvar, p)
        per_prime[str(p)] = {"rank": nvar - nullity, "nullity": nullity}
        ok = ok and nullity == 1
    rank_q = rank_rational(rows, nvar)
    nullity_q = nvar - rank_q
    # 单位矩阵必须是解（否则「标量」这个候选解方向不成立）
    id_is_solution = applies_zero(rows, vec_of(I))
    ok = ok and nullity_q == 1 and id_is_solution
    return {
        "gf_primes": per_prime,
        "rational_rank": rank_q,
        "rational_nullity": nullity_q,
        "identity_is_solution": id_is_solution,
        "ok": ok,
    }


def check_conclusion_not_weaker():
    """Agda 结论的 8 条关系解空间维数 = 1 ⇒ 结论覆盖了整个交换子空间。"""
    rows, nvar = conclusion_system()
    ok = True
    detail = {}
    for p in [3, 5, 7]:
        nullity = nvar - rank_mod(rows, nvar, p)
        detail[str(p)] = {"rank": nvar - nullity, "nullity": nullity}
        ok = ok and nullity == 1
    rank_q = rank_rational(rows, nvar)
    nullity_q = nvar - rank_q
    id_is_solution = applies_zero(rows, vec_of(I))
    ok = ok and nullity_q == 1 and id_is_solution
    return {
        "gf": detail,
        "rational_rank": rank_q,
        "rational_nullity": nullity_q,
        "identity_is_solution": id_is_solution,
        "ok": ok,
    }


def check_char2_counterexample():
    """GF(2)：A = S 与 S、F 都交换但不是标量 ⇒ 无挠性假设不可去。"""
    A = S
    acts_with_S = mm(A, S, 2) == mm(S, A, 2)
    acts_with_F = mm(A, F, 2) == mm(F, A, 2)
    scalar = is_scalar_mod(A, 2)
    # GF(2) 上 F = I，故 F 交换是自动的 —— 这本身就是「无挠性失效」的机制说明
    F_is_identity_mod2 = all(F[i][j] % 2 == (1 if i == j else 0) % 2
                             for i in range(3) for j in range(3))
    return {
        "A_is_S": True,
        "commutes_S": acts_with_S,
        "commutes_F": acts_with_F,
        "is_scalar": scalar,
        "F_equals_identity_mod2": F_is_identity_mod2,
        "ok": acts_with_S and acts_with_F and (not scalar) and F_is_identity_mod2,
    }


def main():
    r1 = check_gf3_exhaustive()
    r2 = check_exact_linear_algebra()
    r3 = check_conclusion_not_weaker()
    r4 = check_char2_counterexample()
    result = {
        "gf3_exhaustive": r1,
        "exact_linear_algebra": r2,
        "conclusion_not_weaker": r3,
        "char2_counterexample": r4,
        "all_ok": all(r["ok"] for r in (r1, r2, r3, r4)),
    }
    print(json.dumps(result, indent=1, ensure_ascii=False))
    try:
        from oracle_kit import manifest
    except Exception:  # 脱离 preset 直接跑时退化为裸打印
        def manifest(basis, domain, points, claim):
            print("ORACLE-MANIFEST " + json.dumps(
                {"basis": basis, "domain": domain, "points": points, "claim": claim},
                ensure_ascii=False))
    manifest(
        basis="GF(3)^9 全空间穷举 19,683 个矩阵（暴力对账）+ GF(p)（p=5,7,11,13,101）与 ℚ 的精确消元（线性系统完整解空间，非抽样）+ GF(2) 显式反例",
        domain=r1["domain"],
        points=r1["points"],
        claim="与 S、F 都交换的 3×3 矩阵必为标量：GF(3)^9 穷举 19,683 个全验；交换子空间维数在 GF(p) 与 ℚ 上精确为 1（完整解）；Agda 结论 8 条关系解空间维数也为 1（结论不弱）；GF(2) 上 A=S 为非标量反例（无挠性不可去）",
    )
    return 0 if result["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
