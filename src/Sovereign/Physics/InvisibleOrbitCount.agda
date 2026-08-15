{-# OPTIONS --rewriting #-}

-- | Sovereign.Physics.InvisibleOrbitCount
-- 不可见自由度的系统计数: 共轭轨道对账 (0 postulate, 无洞)
--
-- 先算后写 — 与知识库"64 分型 = 51 有形 + 13 无形"的对账结论:
--   (a) GF(9) Frobenius 轨道: 不动点 = 实轴 GF(3) (3 个), 共轭对 = 3 对,
--       总轨道 = 6。 9 = 3 + 2×3 — 每个共轭对是同一轨道的两个投影方向
--       (RightHandedNeutrinoTheorem 的推广: σ(α)=−α 只是 3 对之一)。
--   (b) 三个空间坐标 GF(3)³ 在手征共轭 (negation) 下:
--       不动点恰 1 个 (零点), 非零点两两配对, 对数 = (27−1)/2 = 13。
--       13 无形分型的代数对应: 空间三坐标的 13 个 ± 共轭对 —
--       每一对的两个方向中至多一个落在选定可观测投影内。
--   (c) 64 = 51 + 13 是六爻二进制空间 (2⁶) 上的知识库分派 — 51/13 的
--       具体清单是描述层输入, 不由 GF(3) 代数导出 — 不写假定理。
--       "729 = 3⁶ 格点 51/13 划分" 数学上不成立 (729 ≠ 64), 不形式化。
--
-- 诚实边界: 13 的代数对应与卢先生清单的逐项对应是框架层解读;
--   本模块证明的是计数结构本身 (不动点唯一性 + 对合 + 对数算术)。

module Sovereign.Physics.InvisibleOrbitCount where

open import Data.Nat using (ℕ; _/_; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate; negate²)
open import Sovereign.Algebra.GF9 using (GF9; galoisConjugate)

--------------------------------------------------------------------------------
-- §1. GF(9) Frobenius 轨道: 3 不动点 + 3 共轭对 = 6 轨道
--------------------------------------------------------------------------------

-- 不动点恰为实轴: σ(x) = x ⟺ x 的 α 系数为零 (9 case)
sigma-fixed-iff-real : ∀ x → galoisConjugate x ≡ x → proj₂ x ≡ T₀
sigma-fixed-iff-real (a , T₀) p = refl
sigma-fixed-iff-real (a , T₁) ()
sigma-fixed-iff-real (a , T₂) ()

-- 共轭对的两个方向相异 (对合且无二阶不动点于非实轴元素)
conjugatePair-distinct : ∀ x → proj₂ x ≢ T₀ → galoisConjugate x ≢ x
conjugatePair-distinct (a , T₀) p q = ⊥-elim (p refl)
conjugatePair-distinct (a , T₁) p = λ ()
conjugatePair-distinct (a , T₂) p = λ ()

-- 轨道计数算术: 6 = 2×3 (非实轴元素两两配对 → 3 对)
orbitCount6 : 6 ≡ 2 * 3
orbitCount6 = refl

--------------------------------------------------------------------------------
-- §2. 空间三坐标的共轭对: 1 不动点 + 13 对
--------------------------------------------------------------------------------

-- 三个空间坐标 (与 T6FiveDimensionalProjection.Space3 同构, 本地定义)
Space3 : Set
Space3 = Trit × Trit × Trit

-- 手征共轭 (逐坐标取反)
conj3 : Space3 → Space3
conj3 (x , y , z) = (negate x , negate y , negate z)

-- 对合 (逐坐标 negate²)
conj3-involutive : ∀ p → conj3 (conj3 p) ≡ p
conj3-involutive (x , y , z) = begin
  conj3 (conj3 (x , y , z))
    ≡⟨ refl ⟩
  (negate (negate x) , negate (negate y) , negate (negate z))
    ≡⟨ cong (λ a → a , negate (negate y) , negate (negate z)) (negate² x) ⟩
  (x , negate (negate y) , negate (negate z))
    ≡⟨ cong (λ b → x , b , negate (negate z)) (negate² y) ⟩
  (x , y , negate (negate z))
    ≡⟨ cong (λ c → x , y , c) (negate² z) ⟩
  (x , y , z) ∎

-- negate 的不动点恰为 T₀ (3 case)
negate-fixed-only-T₀ : ∀ x → negate x ≡ x → x ≡ T₀
negate-fixed-only-T₀ T₀ p = refl
negate-fixed-only-T₀ T₁ ()
negate-fixed-only-T₀ T₂ ()

-- 共轭的不动点恰为零点: conj3 p ≡ p ⟹ p = (T₀, T₀, T₀)
conj3-fixed-only-zero : ∀ p → conj3 p ≡ p → p ≡ (T₀ , T₀ , T₀)
conj3-fixed-only-zero (x , y , z) p =
  cong₂ _,_
    (negate-fixed-only-T₀ x (cong proj₁ p))
    (cong₂ _,_
      (negate-fixed-only-T₀ y (cong (λ t → proj₁ (proj₂ t)) p))
      (negate-fixed-only-T₀ z (cong (λ t → proj₂ (proj₂ t)) p)))

-- 计数算术: 非零点 26 个, 两两配对 → 13 对
thirteenPairs : 26 / 2 ≡ 13
thirteenPairs = refl

-- 27 = 1 + 2×13 (不动点 1 + 共轭对 13)
invisibleCount27 : 1 + 2 * 13 ≡ 27
invisibleCount27 = refl

-- 0 postulate.
