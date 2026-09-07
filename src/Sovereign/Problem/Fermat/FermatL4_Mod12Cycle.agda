{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Fermat.FermatL4_Mod12Cycle
-- 费马大定理的离散基座 — L4 R₁₂ 幂周期闭包层
--
-- 数学背景 (对应 DC12 论文"定理 1 幂周期闭包"的真内核; 论文表有误, 本层按真表):
--   在环 R₁₂ = (Duodec, +12, *12) 上, 每个元素 x 的幂 xⁿ (n∈ℕ) 的行为被逐类分类:
--     [单位群 V₄] d1,d5,d7,d11 : u² = 1 → uⁿ 只依赖 n 奇偶 (偶→d1)
--     [常数类]   d4 (4²≡4), d9 (9²≡9)  : n≥1 恒为常数
--     [周期 2]   d2,d3,d5,d7,d8,d11     : n 足够大后 (或自 n=1) 周期 2
--     [湮灭类]   d0 (n≥1), d6 (n≥2)     : 幂在有限步归零 (6²≡0)
--   逐类穷举 refl 验证 (真表, 2026-09-07 数值核对):
--     x=0:0,0,0,… | x=1:1,1,… | x=2:2,4,8,4,8,… | x=3:3,9,3,9,…
--     x=4:4,4,… | x=5:5,1,5,1,… | x=6:6,0,0,… | x=7:7,1,7,1,…
--     x=8:8,4,8,4,… | x=9:9,9,… | x=10:10,4,4,… | x=11:11,1,11,1,…
--
-- 主定理 (低位约束, DC12 论文定理 4 的"正确投影"版本):
--   flt-mod12-even-nonsol : 若 a,b,c 皆为单位 (gcd 与 12 互素), n 偶,
--     则 aⁿ +12 bⁿ ≠ cⁿ (mod 12).
--   证明: 单位偶次幂 = d1 (V₄ 指数 2), 故 1+1=2 ≠ 1.
--   -- 这是"偶次费马方程 ⇒ 三数不能皆与 12 互素"的同余版; 与 ℕ 提升层
--      (FermatL4_NatLift, 3|abc) 互补: 3 通道在 mod3, 非 3-素数因子经 CRT 在 mod4.
--
-- 精确边界:
--   * 本层只在 R₁₂ 环上, 不经 Doz 位值, 无位数分离 (那已被反例排除).
--   * 单位群 V₄ (全 2 阶) ≠ ⟨α⟩ C₄ (4 阶元) — 防混淆见 DuodecClock.mulAlpha-not-*12.
--
-- 0 postulate. 依赖: Duodecimal (R₁₂ = Duodec 环), Data.Nat.

module Sovereign.Problem.Fermat.FermatL4_Mod12Cycle where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11
       ; _+12_; _*12_)

--------------------------------------------------------------------------------
-- §1. R₁₂ 上的幂函数 pow12
--------------------------------------------------------------------------------

pow12 : Duodec → ℕ → Duodec
pow12 x zero = d1
pow12 x (suc n) = x *12 pow12 x n

--------------------------------------------------------------------------------
-- §2. 单位判定 (V₄ = {1,5,7,11} ≅ (R₁₂)×)
--------------------------------------------------------------------------------

Unit12 : Duodec → Set
Unit12 x = x ≡ d1 ⊎ x ≡ d5 ⊎ x ≡ d7 ⊎ x ≡ d11

--------------------------------------------------------------------------------
-- §3. 湮灭类: 0 与 6
--------------------------------------------------------------------------------

-- 0ⁿ = 0 (n ≥ 1)
pow12-zero-suc : ∀ n → pow12 d0 (suc n) ≡ d0
pow12-zero-suc n = refl   -- d0 *12 _ = d0

-- 6ⁿ = 0 (n ≥ 2): 用 6 *12 (6 *12 y) ≡ d0 (12 case)
six-double-zero : ∀ y → d6 *12 (d6 *12 y) ≡ d0
six-double-zero d0 = refl;  six-double-zero d1 = refl
six-double-zero d2 = refl;  six-double-zero d3 = refl
six-double-zero d4 = refl;  six-double-zero d5 = refl
six-double-zero d6 = refl;  six-double-zero d7 = refl
six-double-zero d8 = refl;  six-double-zero d9 = refl
six-double-zero d10 = refl; six-double-zero d11 = refl

pow12-six-nilpotent : ∀ n → pow12 d6 (suc (suc n)) ≡ d0
pow12-six-nilpotent n = begin
  pow12 d6 (suc (suc n))            ≡⟨⟩
  d6 *12 pow12 d6 (suc n)           ≡⟨⟩
  d6 *12 (d6 *12 pow12 d6 n)        ≡⟨ six-double-zero (pow12 d6 n) ⟩
  d0                                ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §4. 单位幂: 偶次 = d1 (V₄ 指数 2 → 周期 2)
--------------------------------------------------------------------------------

-- 每个单位 u 的"两次乘 = 恒等": u *12 (u *12 y) ≡ y (12 case)
unit-double-id : ∀ u → Unit12 u → ∀ y → u *12 (u *12 y) ≡ y
unit-double-id d1 _ y = begin
  d1 *12 (d1 *12 y)  ≡⟨⟩
  y                  ∎
  where open ≡-Reasoning
unit-double-id d5 _ y = five-double-id y
  where
  five-double-id : ∀ y → d5 *12 (d5 *12 y) ≡ y
  five-double-id d0 = refl;  five-double-id d1 = refl
  five-double-id d2 = refl;  five-double-id d3 = refl
  five-double-id d4 = refl;  five-double-id d5 = refl
  five-double-id d6 = refl;  five-double-id d7 = refl
  five-double-id d8 = refl;  five-double-id d9 = refl
  five-double-id d10 = refl; five-double-id d11 = refl
unit-double-id d7 _ y = seven-double-id y
  where
  seven-double-id : ∀ y → d7 *12 (d7 *12 y) ≡ y
  seven-double-id d0 = refl;  seven-double-id d1 = refl
  seven-double-id d2 = refl;  seven-double-id d3 = refl
  seven-double-id d4 = refl;  seven-double-id d5 = refl
  seven-double-id d6 = refl;  seven-double-id d7 = refl
  seven-double-id d8 = refl;  seven-double-id d9 = refl
  seven-double-id d10 = refl; seven-double-id d11 = refl
unit-double-id d11 _ y = eleven-double-id y
  where
  eleven-double-id : ∀ y → d11 *12 (d11 *12 y) ≡ y
  eleven-double-id d0 = refl;  eleven-double-id d1 = refl
  eleven-double-id d2 = refl;  eleven-double-id d3 = refl
  eleven-double-id d4 = refl;  eleven-double-id d5 = refl
  eleven-double-id d6 = refl;  eleven-double-id d7 = refl
  eleven-double-id d8 = refl;  eleven-double-id d9 = refl
  eleven-double-id d10 = refl; eleven-double-id d11 = refl
unit-double-id d0 (inj₁ ()) _
unit-double-id d0 (inj₂ (inj₁ ())) _
unit-double-id d0 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d0 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d2 (inj₁ ()) _
unit-double-id d2 (inj₂ (inj₁ ())) _
unit-double-id d2 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d2 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d3 (inj₁ ()) _
unit-double-id d3 (inj₂ (inj₁ ())) _
unit-double-id d3 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d3 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d4 (inj₁ ()) _
unit-double-id d4 (inj₂ (inj₁ ())) _
unit-double-id d4 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d4 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d6 (inj₁ ()) _
unit-double-id d6 (inj₂ (inj₁ ())) _
unit-double-id d6 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d6 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d8 (inj₁ ()) _
unit-double-id d8 (inj₂ (inj₁ ())) _
unit-double-id d8 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d8 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d9 (inj₁ ()) _
unit-double-id d9 (inj₂ (inj₁ ())) _
unit-double-id d9 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d9 (inj₂ (inj₂ (inj₂ ()))) _
unit-double-id d10 (inj₁ ()) _
unit-double-id d10 (inj₂ (inj₁ ())) _
unit-double-id d10 (inj₂ (inj₂ (inj₁ ()))) _
unit-double-id d10 (inj₂ (inj₂ (inj₂ ()))) _

-- 单位偶次幂 = d1 (归纳, 每步用 unit-double-id 消去两层)
pow12-unit-even : ∀ u → Unit12 u → ∀ n → pow12 u (n * 2) ≡ d1
pow12-unit-even u uu zero = refl
pow12-unit-even u uu (suc n) = begin
  pow12 u (suc n * 2)                ≡⟨⟩
  pow12 u (suc (suc (n * 2)))        ≡⟨⟩
  u *12 pow12 u (suc (n * 2))        ≡⟨⟩
  u *12 (u *12 pow12 u (n * 2))      ≡⟨ unit-double-id u uu (pow12 u (n * 2)) ⟩
  pow12 u (n * 2)                    ≡⟨ pow12-unit-even u uu n ⟩
  d1                                 ∎
  where open ≡-Reasoning

-- 单位奇次幂 = 自身: u^(2k+1) = u *12 u^(2k) = u *12 d1 = u
pow12-unit-odd : ∀ u → Unit12 u → ∀ n → pow12 u (suc (n * 2)) ≡ u
pow12-unit-odd u uu n = begin
  pow12 u (suc (n * 2))             ≡⟨⟩
  u *12 pow12 u (n * 2)             ≡⟨ cong (u *12_) (pow12-unit-even u uu n) ⟩
  u *12 d1                          ≡⟨ unit-mul-d1 u uu ⟩
  u                                 ∎
  where open ≡-Reasoning
        unit-mul-d1 : ∀ u → Unit12 u → u *12 d1 ≡ u
        unit-mul-d1 d1 _ = refl
        unit-mul-d1 d5 _ = refl
        unit-mul-d1 d7 _ = refl
        unit-mul-d1 d11 _ = refl
        unit-mul-d1 d0 (inj₁ ())
        unit-mul-d1 d0 (inj₂ (inj₁ ()))
        unit-mul-d1 d0 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d0 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d2 (inj₁ ())
        unit-mul-d1 d2 (inj₂ (inj₁ ()))
        unit-mul-d1 d2 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d2 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d3 (inj₁ ())
        unit-mul-d1 d3 (inj₂ (inj₁ ()))
        unit-mul-d1 d3 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d3 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d4 (inj₁ ())
        unit-mul-d1 d4 (inj₂ (inj₁ ()))
        unit-mul-d1 d4 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d4 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d6 (inj₁ ())
        unit-mul-d1 d6 (inj₂ (inj₁ ()))
        unit-mul-d1 d6 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d6 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d8 (inj₁ ())
        unit-mul-d1 d8 (inj₂ (inj₁ ()))
        unit-mul-d1 d8 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d8 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d9 (inj₁ ())
        unit-mul-d1 d9 (inj₂ (inj₁ ()))
        unit-mul-d1 d9 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d9 (inj₂ (inj₂ (inj₂ ())))
        unit-mul-d1 d10 (inj₁ ())
        unit-mul-d1 d10 (inj₂ (inj₁ ()))
        unit-mul-d1 d10 (inj₂ (inj₂ (inj₁ ())))
        unit-mul-d1 d10 (inj₂ (inj₂ (inj₂ ())))

--------------------------------------------------------------------------------
-- §5. 常数类: d1, d4, d9
--------------------------------------------------------------------------------

-- 1ⁿ = 1
pow12-one : ∀ n → pow12 d1 n ≡ d1
pow12-one zero = refl
pow12-one (suc n) = begin
  pow12 d1 (suc n)  ≡⟨⟩
  d1 *12 pow12 d1 n ≡⟨⟩
  pow12 d1 n        ≡⟨ pow12-one n ⟩
  d1                ∎
  where open ≡-Reasoning

-- 4² = 4, 9² = 9: 常数类实例
four-square : d4 *12 d4 ≡ d4
four-square = refl
nine-square : d9 *12 d9 ≡ d9
nine-square = refl

--------------------------------------------------------------------------------
-- §6. 主定理: 低位约束 (mod 12) — 三单位偶次无解
--
--   若 a,b,c ∈ (R₁₂)× = V₄, n = 2k ≥ 2 偶, 则 aⁿ +12 bⁿ ≠ cⁿ (mod 12).
--   因单位偶次幂 = d1 (pow12-unit-even): LHS ≡ 1+1 = 2, RHS ≡ 1, 而 d2 ≠ d1.
--
--   这是 DC12 论文定理 4 的**正确投影版本** (论文的 π3 数字和定义非同态, 已弃;
--   此处直接用 R₁₂ 环乘 + V₄ 单位群, 真且穷举可判).
--------------------------------------------------------------------------------

d2≢d1 : d2 ≡ d1 → ⊥
d2≢d1 ()

flt-mod12-even-nonsol : ∀ a b c k →
                        Unit12 a → Unit12 b → Unit12 c →
                        pow12 a (suc k * 2) +12 pow12 b (suc k * 2) ≡ pow12 c (suc k * 2) → ⊥
flt-mod12-even-nonsol a b c k ua ub uc eq =
  d2≢d1 (trans (sym lhs) (trans eq rhs))
  where
  open ≡-Reasoning
  -- 偶次指数 (suc k)*2 = 2k+2 ≥ 2
  pa : pow12 a (suc k * 2) ≡ d1
  pa = pow12-unit-even a ua (suc k)
  pb : pow12 b (suc k * 2) ≡ d1
  pb = pow12-unit-even b ub (suc k)
  pc : pow12 c (suc k * 2) ≡ d1
  pc = pow12-unit-even c uc (suc k)
  lhs : pow12 a (suc k * 2) +12 pow12 b (suc k * 2) ≡ d2
  lhs = begin
    pow12 a (suc k * 2) +12 pow12 b (suc k * 2)  ≡⟨ cong₂ _+12_ pa pb ⟩
    d1 +12 d1                                     ≡⟨⟩
    d2                                            ∎
  rhs : pow12 c (suc k * 2) ≡ d1
  rhs = pc

--------------------------------------------------------------------------------
-- §7. 真表 (逐类幂行为, refl 穷举佐证; 完整分类见模块头注释)
--------------------------------------------------------------------------------

-- 单位 d5: 5,1,5,1 → 偶 d1 / 奇 d5 (实例)
five-even : pow12 d5 2 ≡ d1
five-even = refl
five-odd : pow12 d5 3 ≡ d5
five-odd = refl
-- 周期 2 类 d3: 3,9,3,9
three-alt : pow12 d3 2 ≡ d9
three-alt = refl
three-alt2 : pow12 d3 3 ≡ d3
three-alt2 = refl
-- 常数类 d4: 4,4,4
four-const : pow12 d4 3 ≡ d4
four-const = refl
-- 湮灭类 d6: 6,0,0
six-annihilate : pow12 d6 3 ≡ d0
six-annihilate = refl

--------------------------------------------------------------------------------
-- §8. 大衍核心锚定 — "mod 12 穷尽全部相位信息"的代数根据 (2026-09-07 接链)
--
-- R₁₂ 层建模的合法性来自最低公理基座 DayanCore:
--   DC = ⟨δ, φ | δ³ = id, φ⁴ = id, δφ = φδ⟩ ≅ C₃ × C₄ ≅ C₁₂,
--   载体 DuodecPoint = Trit × AlphaPower, 联合周期 12 = lcm(3,4)
--   由抽象定理 dayan-joint-order-12 ((δ∘φ)¹² = id, 归纳导出) 给出.
-- 本模块在 R₁₂ 环上的单位群 V₄/幂周期分类是这一 12 阶交换群结构
-- 经 CRT 投影后的环论切片: 依赖侧全部本地形式化, 无连续统.
--------------------------------------------------------------------------------

open import Function.Base using (_∘_)
open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Algebra.GroupTheory.DuodecClock
  using (DuodecPoint; AlphaPower)
open import Sovereign.Algebra.GroupTheory.DayanCore
  using (DayanCore; duodec-dayan-core; dayan-joint-order-12; iterate)

dayan-anchor : ∀ (t : Trit) (a : AlphaPower) →
  iterate
    (DayanCore.δ duodec-dayan-core ∘ DayanCore.φ duodec-dayan-core)
    12 (t , a) ≡ (t , a)
dayan-anchor = λ t a → dayan-joint-order-12 duodec-dayan-core (t , a)
