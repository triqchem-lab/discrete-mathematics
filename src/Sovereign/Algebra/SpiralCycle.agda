{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.SpiralCycle
-- ⟨2⟩ 六环定理：Christoffel 螺旋 {1,2,4,8,7,5} 的代数闭合
--
-- 数学背景：
--   (ℤ/9ℤ)* = {1,2,4,5,7,8}，|(ℤ/9ℤ)*| = φ(9) = 6。
--   倍频算子 x ↦ 2x mod 9 是单位群上的自同构（2 可逆 mod 9）。
--   轨道 ⟨2⟩ = {1 → 2 → 4 → 8 → 7 → 5 → 1} 恰为全部单位：
--     2¹ ≡ 2, 2² ≡ 4, 2³ ≡ 8, 2⁴ ≡ 16 ≡ 7, 2⁵ ≡ 32 ≡ 5, 2⁶ ≡ 64 ≡ 1 (mod 9)
--   因此 2 生成 (ℤ/9ℤ)*，|⟨2⟩| = 6，轨道六步闭合——"124875" 螺旋。
--
-- 与循环数的联系：1/7 = 0.\overline{142857}，142857 是周期 6 的循环数；
--   2×142857 = 285714、4×142857 = 571428——倍频 = 数字旋转，
--   即 ⟨2⟩₉ ≅ ⟨10⟩₇ ≅ C₆ 的两个投影。
--
-- 0 postulate — 全部 refl 构造性证明（字面量计算归约）

module Sovereign.Algebra.SpiralCycle where

open import Data.Nat using (ℕ; _*_; _%_; _^_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

-- 不等式（本地定义，避免标准库版本差异，同 VortexRoot 惯例）
infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

------------------------------------------------------------------------------
-- §1. 倍频算子与六步轨道
------------------------------------------------------------------------------

-- 倍频算子：x ↦ 2x mod 9（Christoffel 螺旋的步进）
double-mod9 : ℕ → ℕ
double-mod9 n = (2 * n) % 9

-- 六步轨道：1 → 2 → 4 → 8 → 7 → 5 → 1
spiral-step-1 : double-mod9 1 ≡ 2
spiral-step-1 = refl

spiral-step-2 : double-mod9 2 ≡ 4
spiral-step-2 = refl

spiral-step-4 : double-mod9 4 ≡ 8
spiral-step-4 = refl

spiral-step-8 : double-mod9 8 ≡ 7
spiral-step-8 = refl   -- 16 % 9 = 7

spiral-step-7 : double-mod9 7 ≡ 5
spiral-step-7 = refl   -- 14 % 9 = 5

spiral-step-5 : double-mod9 5 ≡ 1
spiral-step-5 = refl   -- 10 % 9 = 1

------------------------------------------------------------------------------
-- §2. 阶恰为 6
------------------------------------------------------------------------------

-- 2⁶ ≡ 1 (mod 9)：64 = 7×9 + 1
spiral-order-6 : (2 ^ 6) % 9 ≡ 1
spiral-order-6 = refl

-- 最小性：k = 1..5 均不归 1（轨道在前五步不闭合）
spiral-minimal-1 : (2 ^ 1) % 9 ≢ 1
spiral-minimal-1 = λ ()   -- 2 ≢ 1

spiral-minimal-2 : (2 ^ 2) % 9 ≢ 1
spiral-minimal-2 = λ ()   -- 4 ≢ 1

spiral-minimal-3 : (2 ^ 3) % 9 ≢ 1
spiral-minimal-3 = λ ()   -- 8 ≢ 1

spiral-minimal-4 : (2 ^ 4) % 9 ≢ 1
spiral-minimal-4 = λ ()   -- 7 ≢ 1

spiral-minimal-5 : (2 ^ 5) % 9 ≢ 1
spiral-minimal-5 = λ ()   -- 5 ≢ 1

-- 迭代闭合：从 1 出发六步后回到 1
six-steps-return :
  double-mod9 (double-mod9 (double-mod9 (double-mod9 (double-mod9 (double-mod9 1))))) ≡ 1
six-steps-return = refl

------------------------------------------------------------------------------
-- §3. 轨道 = 全部单位：(ℤ/9ℤ)* 的每个元素都是 2 的某次幂
------------------------------------------------------------------------------

unit-hit-1 : Σ ℕ (λ k → (2 ^ k) % 9 ≡ 1)
unit-hit-1 = 0 , refl

unit-hit-2 : Σ ℕ (λ k → (2 ^ k) % 9 ≡ 2)
unit-hit-2 = 1 , refl

unit-hit-4 : Σ ℕ (λ k → (2 ^ k) % 9 ≡ 4)
unit-hit-4 = 2 , refl

unit-hit-8 : Σ ℕ (λ k → (2 ^ k) % 9 ≡ 8)
unit-hit-8 = 3 , refl

unit-hit-7 : Σ ℕ (λ k → (2 ^ k) % 9 ≡ 7)
unit-hit-7 = 4 , refl   -- 16 % 9 = 7

unit-hit-5 : Σ ℕ (λ k → (2 ^ k) % 9 ≡ 5)
unit-hit-5 = 5 , refl   -- 32 % 9 = 5

-- 六个轨道点两两互异（15 对）——轨道确有 6 个元素
units-distinct :
  (1 ≢ 2) × (1 ≢ 4) × (1 ≢ 8) × (1 ≢ 7) × (1 ≢ 5) ×
  (2 ≢ 4) × (2 ≢ 8) × (2 ≢ 7) × (2 ≢ 5) ×
  (4 ≢ 8) × (4 ≢ 7) × (4 ≢ 5) ×
  (8 ≢ 7) × (8 ≢ 5) ×
  (7 ≢ 5)
units-distinct = (λ ()) , (λ ()) , (λ ()) , (λ ()) , (λ ()) ,
                 (λ ()) , (λ ()) , (λ ()) , (λ ()) ,
                 (λ ()) , (λ ()) , (λ ()) ,
                 (λ ()) , (λ ()) ,
                 (λ ())

------------------------------------------------------------------------------
-- §4. 循环数连接：1/7 的数字周期 = 倍频轨道的镜像
------------------------------------------------------------------------------

-- 1/7 = 0.\overline{142857}：142857 × 7 = 999999
one-seventh-cycle : 7 * 142857 ≡ 999999
one-seventh-cycle = refl

-- 倍频 = 数字旋转：2× 与 4× 恰好是 ⟨2⟩ 的前两步
cyclic-rotate-2 : 2 * 142857 ≡ 285714
cyclic-rotate-2 = refl

cyclic-rotate-4 : 4 * 142857 ≡ 571428
cyclic-rotate-4 = refl

-- 数字旋转 ⟺ 分数加倍：2/7 = 0.\overline{285714}
fraction-doubling-rotates : 7 * (2 * 142857) ≡ 2 * 999999
fraction-doubling-rotates = refl   -- 1999998 ≡ 1999998
