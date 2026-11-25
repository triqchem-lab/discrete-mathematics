#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""M13·N0 oracle: Strassen 2×2 七乘方案的 GF(3) 全枚举验证 + 次数账本

先算后验纪律（memory: py-enumerate-before-agda-clauses）:
  · 6561 对 (A,B) 全枚举: Strassen 输出 ≡ 朴素乘法输出 (mod 3)
  · 次数账本: Strassen 7 乘 vs 朴素 8 乘（加/减法门另计）
  · 发射 Agda 全枚举正确性证明（3^8 = 6561 条 refl, 零 meta 形态）
"""
from itertools import product

F3 = (0, 1, 2)

def add(x, y): return (x + y) % 3
def mul(x, y): return (x * y) % 3
def neg(x): return (-x) % 3
def sub(x, y): return (x - y) % 3

def schoolbook(A, B):
    (a, b, c, d), (e, f, g, h) = A, B
    return (add(mul(a, e), add(mul(b, g), 0)) ,  # 占位, 下面完整四项
            )

def schoolbook2(A, B):
    (a, b, c, d), (e, f, g, h) = A, B
    c11 = add(mul(a, e), mul(b, g))
    c12 = add(mul(a, f), mul(b, h))
    c21 = add(mul(c, e), mul(d, g))
    c22 = add(mul(c, f), mul(d, h))
    return (c11, c12, c21, c22)

def strassen(A, B):
    (a, b, c, d), (e, f, g, h) = A, B
    m1 = mul(add(a, d), add(e, h))
    m2 = mul(add(c, d), e)
    m3 = mul(a, sub(f, h))
    m4 = mul(d, sub(g, e))
    m5 = mul(add(a, b), h)
    m6 = mul(sub(c, a), add(e, f))
    m7 = mul(sub(b, d), add(g, h))
    c11 = add(add(m1, m4), add(sub(m5, 0) if False else neg(m5), m7))  # m1+m4−m5+m7
    c11 = add(add(m1, m4), add(neg(m5), m7))
    c12 = add(m3, m5)
    c21 = add(m2, m4)
    c22 = add(add(m1, neg(m2)), add(m3, m6))
    return (c11, c12, c21, c22)

def main():
    mats = list(product(F3, repeat=4))
    fail = 0
    for A in mats:
        for B in mats:
            if strassen(A, B) != schoolbook2(A, B):
                fail += 1
                if fail <= 3:
                    print("FAIL", A, B, strassen(A, B), schoolbook2(A, B))
    print(f"全枚举 81×81 = {81*81} 对: 失败 {fail} {'✓ 方案成立' if fail == 0 else '✗'}")
    print("次数账本: Strassen 7 乘 (m1..m7) + 18 加/减; 朴素 8 乘 + 4 加")
    print("基例表（16 对, E₁₁/E₁₂/E₂₁/E₂₂ × 同）:")
    E = {(0,0,0,0): "E0", (1,0,0,0): "E00", (0,1,0,0): "E01",
         (0,0,1,0): "E10", (0,0,0,1): "E11"}
    for A in [(1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1)]:
        for B in [(1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1)]:
            print(f"  {E[A]}⊗{E[B]}: strassen={strassen(A,B)} school={schoolbook2(A,B)}")

    # ---- emit Agda ----
    TRI = {0: "T₀", 1: "T₁", 2: "T₂"}
    def t(x): return TRI[x]
    def quad(v): return f"(mkMat2 {t(v[0])} {t(v[1])} {t(v[2])} {t(v[3])})"
    L = []
    A = L.append
    A('{-# OPTIONS --rewriting --guardedness #-}')
    A('')
    A('-- | Sovereign.Algebra.LinearAlgebra.StrassenGF3')
    A('-- M13: Strassen 2×2 七乘方案的 GF(3) 全枚举正确性（M13·N0 oracle 冻结）')
    A('--')
    A('-- 数学背景:')
    A('--   · Strassen 1969: 2×2 矩阵乘法 7 次乘法（朴素 8）——ω-型改进的最小完整实例')
    A('--   · 本件: 7 门方案在 GF(3) 上的**全枚举正确性**——3⁸ = 6561 组输入逐组 refl')
    A('--     （先算后验: engineering/oracle_strassen_gf3.py 全枚举核对后逐字发射）')
    A('--   · 次数账本: strassen 的 ⊗ 门恰 7 个（m1..m7 各一）; 朴素 mulMat2 为 8 ⊗')
    A('--     ——离散寄存器对 ω 问题的构造性答案（账本层; 渐近 ω 不在本库边界）')
    A('--')
    A('-- 诚实边界:')
    A('--   · 下界（7 为最小, Hopcroft–Kerr）不作陈述 [边界外]')
    A('--   · 渐近 ω（OpenAI ω ≤ 9/4 等）不在本库边界——见')
    A('--     docs/techniques/OpenAI-omega-9-4-只读审计-2026-11-25.md')
    A('')
    A('module Sovereign.Algebra.LinearAlgebra.StrassenGF3 where')
    A('')
    A('open import Data.Nat using (ℕ)')
    A('open import Relation.Binary.PropositionalEquality using (_≡_; refl)')
    A('open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)')
    A('open import Sovereign.Algebra.LinearAlgebra.Matrix2')
    A('  using (Mat2; mkMat2; mulMat2)')
    A('')
    A('_⊖_ : Trit → Trit → Trit')
    A('x ⊖ y = x ⊕ negate y')
    A('')
    A('-- §1. 七门（每门恰一次 ⊗）')
    A('')
    A('m1 m2 m3 m4 m5 m6 m7 : Mat2 Trit → Mat2 Trit → Trit')
    A('m1 (mkMat2 a _ _ d) (mkMat2 e _ _ h) = (a ⊕ d) ⊗ (e ⊕ h)')
    A('m2 (mkMat2 _ _ c d) (mkMat2 e _ _ _) = (c ⊕ d) ⊗ e')
    A('m3 (mkMat2 a b _ _) (mkMat2 _ f _ h) = a ⊗ (f ⊖ h)')
    A('m4 (mkMat2 _ _ _ d) (mkMat2 e _ g _) = d ⊗ (g ⊖ e)')
    A('m5 (mkMat2 a b _ _) (mkMat2 _ _ _ h) = (a ⊕ b) ⊗ h')
    A('m6 (mkMat2 _ _ c d) (mkMat2 e f _ _) = (c ⊖ a) ⊗ (e ⊕ f)')
    A('m7 (mkMat2 _ b _ d) (mkMat2 _ _ g h) = (b ⊖ d) ⊗ (g ⊕ h)')
    A('')
    A('-- §2. Strassen 输出组合（仅 ⊕/⊖; 无额外 ⊗）')
    A('')
    A('strassen : Mat2 Trit → Mat2 Trit → Mat2 Trit')
    A('strassen A B =')
    A('  mkMat2')
    A('    (((m1 A B ⊕ m4 A B) ⊕ negate (m5 A B)) ⊕ m7 A B)')
    A('    ((m3 A B ⊕ m5 A B))')
    A('    ((m2 A B ⊕ m4 A B))')
    A('    (((m1 A B ⊕ negate (m2 A B)) ⊕ m3 A B) ⊕ m6 A B)')
    A('')
    A('mul₃ : Mat2 Trit → Mat2 Trit → Mat2 Trit')
    A('mul₃ = mulMat2 _⊕_ _⊗_')
    A('')
    A('-- §3. ★ 全枚举正确性（3⁸ = 6561 条 refl; oracle 逐字发射）')
    A('')
    A('strassen-correct :')
    A('  ∀ (a b c d e f g h : Trit) →')
    A('    strassen (mkMat2 a b c d) (mkMat2 e f g h)')
    A('    ≡ mul₃ (mkMat2 a b c d) (mkMat2 e f g h)')
    for v in product(F3, repeat=8):
        a, b, c, d, e, f, g, h = v
        A(f'strassen-correct {t(a)} {t(b)} {t(c)} {t(d)} {t(e)} {t(f)} {t(g)} {t(h)} = refl')
    A('')
    A(f'-- 6561 条全覆盖（oracle strassen 全枚举: 失败 {fail} ✓）')

    open("src/Sovereign/Algebra/LinearAlgebra/StrassenGF3.agda", "w", encoding="utf-8").write("\n".join(L) + "\n")
    print("Agda 模块已发射: src/Sovereign/Algebra/LinearAlgebra/StrassenGF3.agda")

if __name__ == "__main__":
    main()
