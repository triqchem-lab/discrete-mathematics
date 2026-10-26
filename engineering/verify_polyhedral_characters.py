#!/usr/bin/env python3
"""多面体群特征标正交性 + Plancherel 熵（精确算术 ℚ(√5)，无浮点）。

核验：
  1. A₅（5 类 / 5 不可约，全实特征标含 √5）：⟨χᵢ,χⱼ⟩ = δᵢⱼ（25 对）
  2. I_h ≅ A₅ × C₂（10 类 / 10 不可约）：同上（100 对）
  3. Σdᵢ² = |G|：A₄(12)、A₅(60)、2A₄(24)、2A₅(120)、I_h(120)
  4. Plancherel 熵 H = −Σ pᵢ log₂ pᵢ，pᵢ = dᵢ²/|G|（log2 只用于输出熵值，不参与判定）

⚠ A₄ 的两个复 1 维表示需要 ω = (−1+i√3)/2（ℚ(ω)），本脚本的实数域装不下，
   故 A₄ 只核验 Σdᵢ² = 12，不做特征标正交性判定（不虚报）。

用法: python3 engineering/verify_polyhedral_characters.py
"""
import json
import math
import sys
from fractions import Fraction as F


class Q5:
    """a + b√5（a, b 为 Fraction），精确运算。"""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, o):
        o = o if isinstance(o, Q5) else Q5(o)
        return Q5(self.a + o.a, self.b + o.b)

    def __mul__(self, o):
        o = o if isinstance(o, Q5) else Q5(o)
        return Q5(self.a * o.a + 5 * self.b * o.b, self.a * o.b + self.b * o.a)

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __eq__(self, o):
        o = o if isinstance(o, Q5) else Q5(o)
        return self.a == o.a and self.b == o.b

    def __repr__(self):
        return f"({self.a}+{self.b}√5)"


PHI = Q5(F(1, 2), F(1, 2))     # (1+√5)/2
PSI = Q5(F(1, 2), F(-1, 2))    # (1−√5)/2

# A₅：类大小 1,15,20,12,12；不可约维数 1,3,3,4,5
A5_ROWS = [
    (1,  [Q5(1), Q5(3), Q5(3), Q5(4), Q5(5)]),
    (15, [Q5(1), Q5(-1), Q5(-1), Q5(0), Q5(1)]),
    (20, [Q5(1), Q5(0), Q5(0), Q5(1), Q5(-1)]),
    (12, [Q5(1), PHI, PSI, Q5(-1), Q5(0)]),
    (12, [Q5(1), PSI, PHI, Q5(-1), Q5(0)]),
]
A5_DIMS = [1, 3, 3, 4, 5]
A5_CLASSES = [1, 15, 20, 12, 12]


def orthogonality(rows, n_irr, order):
    worst = F(0)
    ok = total = 0
    for i in range(n_irr):
        for j in range(n_irr):
            s = Q5(0)
            for size, chars in rows:
                s = s + Q5(size) * chars[i] * chars[j]
            s = Q5(s.a / order, s.b / order)
            target = Q5(1) if i == j else Q5(0)
            total += 1
            if s == target:
                ok += 1
            else:
                dev = abs(float(s.a - target.a)) + abs(float(s.b - target.b))
                worst = max(worst, F(dev))
    return worst, ok, total


def plancherel(dims, order):
    p = [F(d * d, order) for d in dims]
    return -sum(float(x) * math.log2(float(x)) for x in p)


def main():
    out = {}
    worst, ok, total = orthogonality(A5_ROWS, 5, 60)
    out["A5"] = {"orthogonality": f"{ok}/{total}", "max_dev": float(worst),
                 "dim_sum_sq": sum(d * d for d in A5_DIMS), "H_bits": round(plancherel(A5_DIMS, 60), 4)}

    # I_h = A₅ × C₂：类 = (A₅ 类) × {+1,−1}，共 10 类；
    # 表示 = ρ ⊗ ε（5 个 ρ × 2 个 ε），共 10 个。χ_{ρ⊗ε}(c, δ) = χ_ρ(c) · ε · δ? 
    # 取类 (c, +) 与 (c, −)：在 ρ⊗(+1) 上特征标为 χ_ρ(c) 与 −χ_ρ(c)（因为 δ 作用在 C₂ 因子上）。
    # 在 ρ⊗(−1) 上则相反。这样 10×10 表即为下面的 classes 列表。
    # 表示序：前 5 个 = ρ⊗ε₀（ε₀ ≡ 1），后 5 个 = ρ⊗ε₁（ε₁(+1)=1, ε₁(−1)=−1）
    # 类 (c,+1)：χ = χ_ρ(c)（两个 ε 都给 +χ_ρ）
    # 类 (c,−1)：χ = χ_ρ(c)（ε₀）与 −χ_ρ(c)（ε₁）
    classes = []
    for size, chars in A5_ROWS:
        pos = [c for c in chars] + [c for c in chars]
        neg = [c for c in chars] + [-c for c in chars]
        classes.append((size, pos))
        classes.append((size, neg))
    worst2, ok2, total2 = orthogonality(classes, 10, 120)
    ih_dims = A5_DIMS + A5_DIMS
    out["Ih"] = {"orthogonality": f"{ok2}/{total2}", "max_dev": float(worst2),
                 "dim_sum_sq": sum(d * d for d in ih_dims), "H_bits": round(plancherel(ih_dims, 120), 4),
                 "class_sizes": [s for s, _ in classes]}

    out["A4"] = {"dim_sum_sq": 1 + 1 + 1 + 9, "H_bits": round(plancherel([1, 1, 1, 3], 12), 4),
                 "note": "只核验维数平方和；复特征标需 ℚ(ω)，本脚本不做"}
    out["2A4"] = {"dim_sum_sq": sum(d * d for d in [1, 1, 1, 2, 2, 2, 3]),
                  "H_bits": round(plancherel([1, 1, 1, 2, 2, 2, 3], 24), 4)}
    out["2A5"] = {"dim_sum_sq": sum(d * d for d in [1, 2, 2, 3, 3, 4, 4, 5, 6]),
                  "H_bits": round(plancherel([1, 2, 2, 3, 3, 4, 4, 5, 6], 120), 4)}
    print(json.dumps(out, indent=1))

    ok_all = (out["A5"]["orthogonality"] == "25/25" and out["Ih"]["orthogonality"] == "100/100"
              and out["A5"]["dim_sum_sq"] == 60 and out["Ih"]["dim_sum_sq"] == 120
              and out["A4"]["dim_sum_sq"] == 12 and out["2A4"]["dim_sum_sq"] == 24
              and out["2A5"]["dim_sum_sq"] == 120)
    print("ORACLE-MANIFEST " + json.dumps({
        "basis": "Q(sqrt5) exact arithmetic; A5 and Ih=A5xC2 character tables",
        "domain": 125, "points": 25 + 100,
        "claim": "A5 (25/25) and Ih (100/100) character orthogonality exact; dim^2 sums = |G| for A4/A5/2A4/2A5/Ih"}))
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
