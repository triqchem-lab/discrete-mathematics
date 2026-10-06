{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LiftCriterion
-- 完备性层 C1：「恰 2 存活」泛型化——GF(3) 提升判据的唯一解定理
--
-- 数学内容：
--   Hensel 三候选判据（mod 3 系数级）：k·(2x) = −q 的 GF(3) 线性方程。
--   核心定理（C1）：a ≠ T₀ ⟹ 方程 k ⊗ a ≡ b 有**唯一解** k = b ⊗ a。
--     存在：(b⊗a)⊗a = b⊗(a⊗a) = b⊗T₁ = b（非零元自逆）
--     唯一：按 a 分 case 消去（T₁ 直读 / T₂ 是 negate 定义性）
--   推论（恰 2 存活）：两基根 x=±1 各给 2x = ±2 ≠ T₀——各恰一解。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LiftCriterion where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate
        ; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊗-identityˡ
        ; ⊗-assoc; ⊗-identityʳ; ⊗-comm)
open import Sovereign.Algebra.ChainHomo using (negate-inv)

--------------------------------------------------------------------------------
-- §1. 非零元自逆——NonZero₃ a ⟹ a ⊗ a ≡ T₁
--------------------------------------------------------------------------------

NonZero₃ : Trit → Set
NonZero₃ T₀ = ⊥
NonZero₃ T₁ = ⊤
NonZero₃ T₂ = ⊤

sq-selfinv : ∀ (a : Trit) → NonZero₃ a → a ⊗ a ≡ T₁
sq-selfinv T₁ tt = refl
sq-selfinv T₂ tt = refl

-- negate 的 ⊗ 交换（9 case——negate a ⊗ b ≡ negate (a ⊗ b)）
neg-⊗ : ∀ (a b : Trit) → negate a ⊗ b ≡ negate (a ⊗ b)
neg-⊗ T₀ T₀ = refl
neg-⊗ T₀ T₁ = refl
neg-⊗ T₀ T₂ = refl
neg-⊗ T₁ T₀ = refl
neg-⊗ T₁ T₁ = refl
neg-⊗ T₁ T₂ = refl
neg-⊗ T₂ T₀ = refl
neg-⊗ T₂ T₁ = refl
neg-⊗ T₂ T₂ = refl
-- 9 case 全 refl：negate a⊗b 与 negate(a⊗b) 的 ⊗/negate 表逐格核对

-- negate 对合
neg-invol : ∀ (a : Trit) → negate (negate a) ≡ a
neg-invol T₀ = refl
neg-invol T₁ = refl
neg-invol T₂ = refl

--------------------------------------------------------------------------------
-- §2. 零因子消去——NonZero₃ a ∧ a⊗x ≡ a⊗y ⟹ x ≡ y
--
--   a = T₁：⊗-identityˡ 直读
--   a = T₂：T₂⊗x = negate x（定义性）→ negate 对合
--------------------------------------------------------------------------------

-- T₂ 乘法即 negate（按 x 3 case——x 变量时 ⊗ 不归约）
T₂neg : ∀ (x : Trit) → T₂ ⊗ x ≡ negate x
T₂neg T₀ = refl
T₂neg T₁ = refl
T₂neg T₂ = refl

-- x ⊗ T₂ 即 negate x（按 x 3 case）
x⊗T₂neg : ∀ (x : Trit) → x ⊗ T₂ ≡ negate x
x⊗T₂neg T₀ = refl
x⊗T₂neg T₁ = refl
x⊗T₂neg T₂ = refl

⊗-cancel : ∀ (x y a : Trit) → NonZero₃ a → x ⊗ a ≡ y ⊗ a → x ≡ y
⊗-cancel x y T₁ tt h = trans (sym (⊗-identityʳ x)) (trans h (⊗-identityʳ y))
⊗-cancel x y T₂ tt h =
  trans (sym (neg-invol x))
  (trans (cong negate (trans (sym (x⊗T₂neg x)) (trans h (x⊗T₂neg y))))
         (neg-invol y))
⊗-cancel x y T₀ () h

-- T₂ 乘法即 negate（按 x 3 case——x 变量时 ⊗ 不归约）

--------------------------------------------------------------------------------
-- §3. C1 核心定理——GF(3) 线性方程唯一解
--
--   NonZero₃ a ⟹ Σ k, k⊗a ≡ b × 唯一性
--------------------------------------------------------------------------------

-- 存在性：解 k = b ⊗ a
lift-solve : ∀ (a b : Trit) → NonZero₃ a → Σ Trit (λ k → k ⊗ a ≡ b)
lift-solve a b nz = (b ⊗ a ,
  trans (⊗-assoc b a a)
  (trans (cong (λ z → b ⊗ z) (sq-selfinv a nz))
         (⊗-identityʳ b)))
  -- (b⊗a)⊗a = b⊗(a⊗a) = b⊗T₁ = b

-- 唯一性：k₁⊗a ≡ k₂⊗a ⟹ k₁ ≡ k₂
lift-unique : ∀ (a k₁ k₂ : Trit) → NonZero₃ a →
              k₁ ⊗ a ≡ k₂ ⊗ a → k₁ ≡ k₂
lift-unique a k₁ k₂ nz h = ⊗-cancel k₁ k₂ a nz h
-- 签名统一为 a 在右（h 直接匹配）

--------------------------------------------------------------------------------
-- §4. C1 推论——「恰 2 存活」的 GF(3) 判据级闭合
--
--   提升判据方程：k ⊗ (2x) ≡ negate q（q = (x²−1)/d 的 GF(3) 系数）。
--   基根 x = ±1 ⟹ 2x = ±2 ≠ T₀ ⟹ NonZero₃ (2x)——唯一解定理适用。
--   两基根 × 每根恰一解 ⟹ 恰 2 存活（G4 泛型定理的核心）。
--------------------------------------------------------------------------------

-- 2x 的非零性：x ≠ T₀ ⟹ NonZero₃ (T₂ ⊗ x)
two-nonzero : ∀ (x : Trit) → NonZero₃ x → NonZero₃ (T₂ ⊗ x)
two-nonzero T₁ tt = tt
two-nonzero T₂ tt = tt
-- T₂⊗T₁ = T₂ ✓、T₂⊗T₂ = T₁ ✓（非零）

-- 判据方程的解（存在+唯一打包）
lift-criterion : ∀ (x q : Trit) → NonZero₃ x →
                 Σ Trit (λ k → k ⊗ (T₂ ⊗ x) ≡ negate q)
                 × (∀ (k₁ k₂ : Trit) →
                    k₁ ⊗ (T₂ ⊗ x) ≡ negate q →
                    k₂ ⊗ (T₂ ⊗ x) ≡ negate q →
                    k₁ ≡ k₂)
lift-criterion x q nz =
  (sol , λ k₁ k₂ h₁ h₂ → lift-unique (T₂ ⊗ x) k₁ k₂ (two-nonzero x nz)
                       (trans h₁ (sym h₂)))
  where
    sol : Σ Trit (λ k → k ⊗ (T₂ ⊗ x) ≡ negate q)
    sol = lift-solve (T₂ ⊗ x) (negate q) (two-nonzero x nz)
  -- 存在：解 k = (negate q)⊗(2x)（lift-solve 直接）
  -- 唯一：两解之差经 ⊗-cancel 消去

--------------------------------------------------------------------------------
-- §5. C1 完成度——完备性层第一块闭合
--
--   ✅ NonZero₃ + sq-selfinv（非零元自逆）
--   ✅ ⊗-cancel（零因子消去，两 case 定义性——比 distrib 桥简一个量级）
--   ✅ lift-solve / lift-unique：GF(3) 线性方程唯一解定理
--   ✅ lift-criterion：提升判据的解存在+唯一打包
--
--   完备性推论：三候选中恰一存活 per 基根（方程唯一解）；
--   两基根 × 恰一 = 恰 2 存活——G4 的泛型定理核心在此闭合
--   （判据级：ℤ 系数 q 到 GF(3) 的映射对账留 roadmap 注记——
--    q = (x²−1)/d 的整除性由 HenselMod* 实例层的 rootWitness 形状承担）。
--------------------------------------------------------------------------------
