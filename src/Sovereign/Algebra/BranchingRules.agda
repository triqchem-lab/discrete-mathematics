{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.BranchingRules
-- SO(3) → A₄ 分支规则: 连续李群表示限制到离散子群的分解表
--
-- 核心结果:
--   SO(3) spin-l 不可约表示 (dim 2l+1) 限制到 A₄ 后分解为:
--
--   l=0: V1                             (dim 1)
--   l=1: V3                             (dim 3)
--   l=2: V3 ⊕ V1' ⊕ V1''               (dim 5)  ← 修正: 非 V3⊕V1⊕V1'
--   l=3: V3 ⊕ V3 ⊕ V1                  (dim 7)
--   l=4: V3 ⊕ V3 ⊕ V1 ⊕ V1' ⊕ V1''    (dim 9)
--   l=5: V3 ⊕ V3 ⊕ V3 ⊕ V1' ⊕ V1''    (dim 11)
--
-- 证明策略: 穷举法 (l=0..5 逐案 refl) + 周期 6 递推 (l≥6)
-- 数学依据: 特征标内积 m_i = (1/12) Σ_C |C| χ_l(C) conj(χ_i(C))
--
-- 宪法合规:
--   - 0 postulate
--   - 禁止浮点数, 特征标值 ∈ Z[ω] (Eisenstein 整数)
--   - 所有验证通过穷举 refl
--
-- 依赖:
--   A4Representations — 共轭类, 不可约表示, 特征标表
--   Eisenstein        — Z[ω] 环

module Sovereign.Algebra.BranchingRules where

open import Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+N_; _*_ to _*N_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.RootMath.Eisenstein
  using (Eisenstein; eis; 0ᵉ; 1ᵉ; ωᵉ; ω²ᵉ; -1ᵉ; 3ᵉ; _+ᵉ_; _*ᵉ_; conjᵉ)

open import Sovereign.Structology.A4Representations
  using ( A4Irrep; V3; V1; V1'; V1''
        ; dim
        ; ConjugacyClass; C1; C2; C3; C4
        ; classSize
        )

--------------------------------------------------------------------------------
-- §1. Eisenstein 整数辅助常数
--------------------------------------------------------------------------------

2ᵉ : Eisenstein
2ᵉ = eis (+ 2) (+ 0)

5ᵉ : Eisenstein
5ᵉ = eis (+ 5) (+ 0)

7ᵉ : Eisenstein
7ᵉ = eis (+ 7) (+ 0)

9ᵉ : Eisenstein
9ᵉ = eis (+ 9) (+ 0)

11ᵉ : Eisenstein
11ᵉ = eis (+ 11) (+ 0)

12ᵉ : Eisenstein
12ᵉ = eis (+ 12) (+ 0)

--------------------------------------------------------------------------------
-- §2. ℕ-Eisenstein 标量乘法
--------------------------------------------------------------------------------
-- 用于 |C| × χ(C) 的计算 (类大小 × 特征标值)

infixl 25 _·e_
_·e_ : ℕ → Eisenstein → Eisenstein
0     ·e x = 0ᵉ
suc n ·e x = x +ᵉ (n ·e x)

--------------------------------------------------------------------------------
-- §3. SO(3) spin-l 特征标在 A₄ 共轭类上的取值
--------------------------------------------------------------------------------
--
-- A₄ 的 4 个共轭类对应 SO(3) 中的旋转:
--   C1 = 恒等 (θ=0)           → χ_l = 2l+1
--   C2 = 顺时针 120° (θ=2π/3) → χ_l 周期 3: {1, 0, -1}
--   C3 = 逆时针 120° (θ=4π/3) → 同 C2 (SO(3) 特征标 θ-偶对称)
--   C4 = 180° (θ=π)           → χ_l = (-1)^l, 周期 2
--
-- 公式: χ_l(θ) = sin((2l+1)θ/2) / sin(θ/2)
-- 在 A₄ 共轭类上取值全为整数 (嵌入 Z[ω])

-- C1: 恒等, χ_l(e) = 2l+1
so3χ-C1 : ℕ → Eisenstein
so3χ-C1 0       = 1ᵉ
so3χ-C1 (suc n) = so3χ-C1 n +ᵉ 2ᵉ

-- C2/C3: 120°/240° 旋转, 周期 3
so3χ-C23 : ℕ → Eisenstein
so3χ-C23 0 = 1ᵉ
so3χ-C23 1 = 0ᵉ
so3χ-C23 2 = -1ᵉ
so3χ-C23 (suc (suc (suc n))) = so3χ-C23 n

-- C4: 180° 旋转, 周期 2
so3χ-C4 : ℕ → Eisenstein
so3χ-C4 0 = 1ᵉ
so3χ-C4 1 = -1ᵉ
so3χ-C4 (suc (suc n)) = so3χ-C4 n

-- 统一特征标函数
so3χ : ℕ → ConjugacyClass → Eisenstein
so3χ l C1 = so3χ-C1 l
so3χ l C2 = so3χ-C23 l
so3χ l C3 = so3χ-C23 l
so3χ l C4 = so3χ-C4 l

-- [分类: 已证引理] SO(3) 特征标值验证 (l=0..5)
so3χ-C1-0 : so3χ-C1 0 ≡ 1ᵉ
so3χ-C1-0 = refl

so3χ-C1-2 : so3χ-C1 2 ≡ 5ᵉ
so3χ-C1-2 = refl

so3χ-C1-5 : so3χ-C1 5 ≡ 11ᵉ
so3χ-C1-5 = refl

so3χ-C23-period : so3χ-C23 3 ≡ 1ᵉ × so3χ-C23 4 ≡ 0ᵉ × so3χ-C23 5 ≡ -1ᵉ
so3χ-C23-period = refl , refl , refl

so3χ-C4-period : so3χ-C4 2 ≡ 1ᵉ × so3χ-C4 3 ≡ -1ᵉ × so3χ-C4 4 ≡ 1ᵉ
so3χ-C4-period = refl , refl , refl

--------------------------------------------------------------------------------
-- §4. A₄ 特征标在共轭类上的取值 (便利包装)
--------------------------------------------------------------------------------
-- 重导出 A4Representations 的特征标表, 以共轭类为索引
-- (A4Representations.character 以 A4 元素为索引, 需先 classify)

a4χ : A4Irrep → ConjugacyClass → Eisenstein
a4χ V1   _  = 1ᵉ
a4χ V1'  C1 = 1ᵉ
a4χ V1'  C2 = ωᵉ
a4χ V1'  C3 = ω²ᵉ
a4χ V1'  C4 = 1ᵉ
a4χ V1'' C1 = 1ᵉ
a4χ V1'' C2 = ω²ᵉ
a4χ V1'' C3 = ωᵉ
a4χ V1'' C4 = 1ᵉ
a4χ V3   C1 = 3ᵉ
a4χ V3   C2 = 0ᵉ
a4χ V3   C3 = 0ᵉ
a4χ V3   C4 = -1ᵉ

--------------------------------------------------------------------------------
-- §5. 分支重数函数 (周期 6 递推)
--------------------------------------------------------------------------------
--
-- branchMult ρ l = SO(3) spin-l 限制到 A₄ 后, 不可约表示 ρ 的重数
--
-- 由特征标内积公式:
--   branchMult ρ l = (1/12) Σ_C |C| · χ_l(C) · conj(χ_ρ(C))
--
-- 递推关系 (l → l+6):
--   branchMult V1   (l+6) = branchMult V1   l + 1
--   branchMult V3   (l+6) = branchMult V3   l + 3
--   branchMult V1'  (l+6) = branchMult V1'  l + 1
--   branchMult V1'' (l+6) = branchMult V1'' l + 1
--
-- 维数增量验证: 1·1 + 3·3 + 1·1 + 1·1 = 12 = 2·6

branchMult : A4Irrep → ℕ → ℕ
-- V1: 基础值 (l=0..5)
branchMult V1   0 = 1
branchMult V1   1 = 0
branchMult V1   2 = 0
branchMult V1   3 = 1
branchMult V1   4 = 1
branchMult V1   5 = 0
-- V3: 基础值
branchMult V3   0 = 0
branchMult V3   1 = 1
branchMult V3   2 = 1
branchMult V3   3 = 2
branchMult V3   4 = 2
branchMult V3   5 = 3
-- V1': 基础值
branchMult V1'  0 = 0
branchMult V1'  1 = 0
branchMult V1'  2 = 1
branchMult V1'  3 = 0
branchMult V1'  4 = 1
branchMult V1'  5 = 1
-- V1'': 基础值 (始终等于 V1', 因为 SO(3) 是实表示)
branchMult V1'' 0 = 0
branchMult V1'' 1 = 0
branchMult V1'' 2 = 1
branchMult V1'' 3 = 0
branchMult V1'' 4 = 1
branchMult V1'' 5 = 1
-- l≥6: 周期 6 递推
branchMult V1   (suc (suc (suc (suc (suc (suc n)))))) = suc (branchMult V1 n)
branchMult V3   (suc (suc (suc (suc (suc (suc n)))))) = suc (suc (suc (branchMult V3 n)))
branchMult V1'  (suc (suc (suc (suc (suc (suc n)))))) = suc (branchMult V1' n)
branchMult V1'' (suc (suc (suc (suc (suc (suc n)))))) = suc (branchMult V1'' n)

--------------------------------------------------------------------------------
-- §6. 维数验证: Σ_ρ mult(ρ,l) · dim(ρ) ≡ 2l+1
--------------------------------------------------------------------------------

dimSum : ℕ → ℕ
dimSum l = branchMult V1 l *N dim V1
     +N branchMult V3 l *N dim V3
     +N branchMult V1' l *N dim V1'
     +N branchMult V1'' l *N dim V1''

-- [分类: 已证引理] 穷举验证 l=0..6
dimSum≡1 : dimSum 0 ≡ 1
dimSum≡1 = refl

dimSum≡3 : dimSum 1 ≡ 3
dimSum≡3 = refl

dimSum≡5 : dimSum 2 ≡ 5
dimSum≡5 = refl

dimSum≡7 : dimSum 3 ≡ 7
dimSum≡7 = refl

dimSum≡9 : dimSum 4 ≡ 9
dimSum≡9 = refl

dimSum≡11 : dimSum 5 ≡ 11
dimSum≡11 = refl

-- l=6: 验证递推正确性 (2·6+1=13)
dimSum≡13 : dimSum 6 ≡ 13
dimSum≡13 = refl

--------------------------------------------------------------------------------
-- §7. l=2 修正证明
--------------------------------------------------------------------------------
--
-- 原模板错误: decomp-l2 = V3 ⊕ V1 ⊕ V1' (5 = 3+1+1)
-- 正确分解:   decomp-l2 = V3 ⊕ V1' ⊕ V1'' (5 = 3+1+1)
--
-- 根因: 特征标内积 m(V1, 2) = 0, 不是 1
--
-- 计算:
--   m(V1, 2) = (1/12)[1·5·1 + 4·(-1)·1 + 4·(-1)·1 + 3·1·1]
--            = (1/12)[5 - 4 - 4 + 3] = 0/12 = 0
--
--   m(V1', 2) = (1/12)[1·5·1 + 4·(-1)·ω² + 4·(-1)·ω + 3·1·1]
--             = (1/12)[8 - 4(ω+ω²)] = (1/12)[8+4] = 1

-- [分类: 已证引理] V1 在 l=2 中重数为 0
l2-V1≡0 : branchMult V1 2 ≡ 0
l2-V1≡0 = refl

-- [分类: 已证引理] V3 在 l=2 中重数为 1
l2-V3≡1 : branchMult V3 2 ≡ 1
l2-V3≡1 = refl

-- [分类: 已证引理] V1' 在 l=2 中重数为 1
l2-V1'≡1 : branchMult V1' 2 ≡ 1
l2-V1'≡1 = refl

-- [分类: 已证引理] V1'' 在 l=2 中重数为 1
l2-V1''≡1 : branchMult V1'' 2 ≡ 1
l2-V1''≡1 = refl

--------------------------------------------------------------------------------
-- §8. 特征标内积验证 (l=2, 全部 4 个不可约表示)
--------------------------------------------------------------------------------
--
-- 内积分子: innerNum ρ l = Σ_C |C| · χ_l(C) · conj(χ_ρ(C))
-- 定理: innerNum ρ l ≡ 12 · branchMult ρ l (作为 Eisenstein 整数)

innerNum : A4Irrep → ℕ → Eisenstein
innerNum ρ l =
    classSize C1 ·e (so3χ l C1 *ᵉ conjᵉ (a4χ ρ C1))
  +ᵉ classSize C2 ·e (so3χ l C2 *ᵉ conjᵉ (a4χ ρ C2))
  +ᵉ classSize C3 ·e (so3χ l C3 *ᵉ conjᵉ (a4χ ρ C3))
  +ᵉ classSize C4 ·e (so3χ l C4 *ᵉ conjᵉ (a4χ ρ C4))

-- [分类: 已证引理] l=2, V1: 分子 = 0 = 12 × 0
-- 1·5·1 + 4·(-1)·1 + 4·(-1)·1 + 3·1·1 = 5-4-4+3 = 0
inner-l2-V1 : innerNum V1 2 ≡ 0ᵉ
inner-l2-V1 = refl

-- [分类: 已证引理] l=2, V3: 分子 = 12 = 12 × 1
-- 1·5·3 + 4·(-1)·0 + 4·(-1)·0 + 3·1·(-1) = 15-3 = 12
inner-l2-V3 : innerNum V3 2 ≡ 12ᵉ
inner-l2-V3 = refl

-- [分类: 已证引理] l=2, V1': 分子 = 12 = 12 × 1
-- 1·5·1 + 4·(-1)·ω² + 4·(-1)·ω + 3·1·1
-- = 5 - 4ω² - 4ω + 3 = 8 - 4(ω+ω²) = 8+4 = 12
inner-l2-V1' : innerNum V1' 2 ≡ 12ᵉ
inner-l2-V1' = refl

-- [分类: 已证引理] l=2, V1'': 分子 = 12 = 12 × 1
-- (与 V1' 对称: ω ↔ ω² 交换, 结果不变)
inner-l2-V1'' : innerNum V1'' 2 ≡ 12ᵉ
inner-l2-V1'' = refl

-- [分类: 已证引理] l=0, V1: 分子 = 12 = 12 × 1 (平凡表示验证)
inner-l0-V1 : innerNum V1 0 ≡ 12ᵉ
inner-l0-V1 = refl

-- [分类: 已证引理] l=1, V3: 分子 = 12 = 12 × 1 (三维表示验证)
inner-l1-V3 : innerNum V3 1 ≡ 12ᵉ
inner-l1-V3 = refl

--------------------------------------------------------------------------------
-- §9. 分解表 (l=0..5, 穷举验证)
--------------------------------------------------------------------------------

-- l=0: V1 (dim 1)
decomp-l0 : branchMult V1 0 ≡ 1 × branchMult V3 0 ≡ 0 × branchMult V1' 0 ≡ 0 × branchMult V1'' 0 ≡ 0
decomp-l0 = refl , refl , refl , refl

-- l=1: V3 (dim 3)
decomp-l1 : branchMult V1 1 ≡ 0 × branchMult V3 1 ≡ 1 × branchMult V1' 1 ≡ 0 × branchMult V1'' 1 ≡ 0
decomp-l1 = refl , refl , refl , refl

-- l=2: V3 ⊕ V1' ⊕ V1'' (dim 5) — 修正: 非 V3⊕V1⊕V1'
decomp-l2 : branchMult V1 2 ≡ 0 × branchMult V3 2 ≡ 1 × branchMult V1' 2 ≡ 1 × branchMult V1'' 2 ≡ 1
decomp-l2 = refl , refl , refl , refl

-- l=3: V3 ⊕ V3 ⊕ V1 (dim 7)
decomp-l3 : branchMult V1 3 ≡ 1 × branchMult V3 3 ≡ 2 × branchMult V1' 3 ≡ 0 × branchMult V1'' 3 ≡ 0
decomp-l3 = refl , refl , refl , refl

-- l=4: V3 ⊕ V3 ⊕ V1 ⊕ V1' ⊕ V1'' (dim 9)
decomp-l4 : branchMult V1 4 ≡ 1 × branchMult V3 4 ≡ 2 × branchMult V1' 4 ≡ 1 × branchMult V1'' 4 ≡ 1
decomp-l4 = refl , refl , refl , refl

-- l=5: V3 ⊕ V3 ⊕ V3 ⊕ V1' ⊕ V1'' (dim 11)
decomp-l5 : branchMult V1 5 ≡ 0 × branchMult V3 5 ≡ 3 × branchMult V1' 5 ≡ 1 × branchMult V1'' 5 ≡ 1
decomp-l5 = refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §10. V1'/V1'' 配对定理
--------------------------------------------------------------------------------
--
-- SO(3) 是实表示, 复共轭不可约表示 V1' 和 V1'' 总是以相同重数出现.
-- 数学原因: SO(3) 特征标在 C2/C3 上取值相同 (θ-偶对称),
-- 而 V1'/V1'' 的特征标在 C2/C3 上互换 (ω ↔ ω²).

-- [分类: 已证引理] V1'/V1'' 重数相等 (l=0..6 穷举 + 递推保持)
pairing-0 : branchMult V1' 0 ≡ branchMult V1'' 0
pairing-0 = refl

pairing-1 : branchMult V1' 1 ≡ branchMult V1'' 1
pairing-1 = refl

pairing-2 : branchMult V1' 2 ≡ branchMult V1'' 2
pairing-2 = refl

pairing-3 : branchMult V1' 3 ≡ branchMult V1'' 3
pairing-3 = refl

pairing-4 : branchMult V1' 4 ≡ branchMult V1'' 4
pairing-4 = refl

pairing-5 : branchMult V1' 5 ≡ branchMult V1'' 5
pairing-5 = refl

-- 一般情形: 递推保持配对
pairing-general : ∀ n → branchMult V1' n ≡ branchMult V1'' n
pairing-general 0 = refl
pairing-general 1 = refl
pairing-general 2 = refl
pairing-general 3 = refl
pairing-general 4 = refl
pairing-general 5 = refl
pairing-general (suc (suc (suc (suc (suc (suc n)))))) =
  cong suc (pairing-general n)
  where open import Relation.Binary.PropositionalEquality using (cong)

--------------------------------------------------------------------------------
-- §11. V3 重数公式
--------------------------------------------------------------------------------
--
-- branchMult V3 l = ⌈l/2⌉ = (2l+1-(-1)^l)/4
--
-- 验证: l=0→0, l=1→1, l=2→1, l=3→2, l=4→2, l=5→3

V3-mult-formula : branchMult V3 0 ≡ 0 × branchMult V3 1 ≡ 1 × branchMult V3 2 ≡ 1 × branchMult V3 3 ≡ 2 × branchMult V3 4 ≡ 2 × branchMult V3 5 ≡ 3
V3-mult-formula = refl , refl , refl , refl , refl , refl
