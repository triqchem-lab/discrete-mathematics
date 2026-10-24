{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Physics.NeutrinoFlavorGF3
-- 中微子三味比的 GF(3) 守恒结构 —— IceCube 风味比的离散化
--
-- 数学背景:
--   三味中微子 (ν_e, ν_μ, ν_τ) 编码为 GF(3)^3 的三元组。
--   源区强子过程给 (1,2,0)，经宇宙学距离混合后到地球给 (1,1,1)。
--
--   ⭐ 核心观察: 两者的 GF(3) 坐标和均为零
--       1 ⊕ 2 ⊕ 0 = 0
--       1 ⊕ 1 ⊕ 1 = 0
--
--   ⇒ 零和条件是**线性**的 ⇒ 它是线性泛函
--       sum3 : GF(3)^3 → GF(3),  sum3(a,b,c) = a ⊕ b ⊕ c
--     的**核**（kernel）。
--   ⇒ 核的基数是 3² = 9（不是 27），这是群同态的秩-零化度。
--
-- 与标准模型的关系:
--   标准模型中「三味之和守恒」= 总中微子数守恒（平凡）。
--   本模块只形式化 GF(3) 的代数结构，**不**声称新物理。
--
-- 诚实边界:
--   · (T₁,T₁,T₁) 与 (T₂,T₂,T₂) 都是「等分量 + 零和」，本模块只证明它们是**一对**，
--     不证明「唯一」——原分析文档说「唯一」是错的。
--   · 本模块**不**涉及 PMNS 矩阵、质量平方差、CP 相位。
--
-- 0 postulate / 0 hole.

module Sovereign.Application.Physics.NeutrinoFlavorGF3 where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate; negate²; ⊕-inverse
        ; ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc)

--------------------------------------------------------------------------------
-- §1. 三味态 = GF(3)^3 与线性泛函
--------------------------------------------------------------------------------

FlavorState : Set
FlavorState = Trit × Trit × Trit

-- 坐标和（GF(3) 加法）
sum3 : FlavorState → Trit
sum3 (a , b , c) = (a ⊕ b) ⊕ c

-- 零和谓词
ZeroSum : FlavorState → Set
ZeroSum v = sum3 v ≡ T₀

-- 逐分量 negate
neg-flavor : FlavorState → FlavorState
neg-flavor (a , b , c) = negate a , negate b , negate c

--------------------------------------------------------------------------------
-- §2. ⭐ 源风味比 (T₁, T₂, T₀) 是零和
--------------------------------------------------------------------------------

-- IceCube 源区: ν_e : ν_μ : ν_τ = 1 : 2 : 0
source-flavor : FlavorState
source-flavor = T₁ , T₂ , T₀

source-zero-sum : ZeroSum source-flavor
source-zero-sum = refl

--------------------------------------------------------------------------------
-- §3. ⭐ 地球风味比 (T₁, T₁, T₁) 是零和
--------------------------------------------------------------------------------

earth-flavor : FlavorState
earth-flavor = T₁ , T₁ , T₁

earth-zero-sum : ZeroSum earth-flavor
earth-zero-sum = refl

--------------------------------------------------------------------------------
-- §4. ⚠ 等分量零和态是**一对**，不是唯一
--------------------------------------------------------------------------------

two-three : FlavorState
two-three = T₂ , T₂ , T₂

-- (T₂,T₂,T₂) 也是零和（Trit.agda:277 的 verifyZero 同款）
two-three-zero-sum : ZeroSum two-three
two-three-zero-sum = refl

-- negate 互换 T₁ 与 T₂
negate-T₁ : negate T₁ ≡ T₂
negate-T₁ = refl

negate-T₂ : negate T₂ ≡ T₁
negate-T₂ = refl

-- ⭐ negate 把地球态映到 (T₂,T₂,T₂)
neg-earth-is-two : neg-flavor earth-flavor ≡ two-three
neg-earth-is-two = refl

-- ⭐ negate 把 (T₂,T₂,T₂) 映回地球态
neg-two-is-earth : neg-flavor two-three ≡ earth-flavor
neg-two-is-earth = refl

--------------------------------------------------------------------------------
-- §5. ⭐⭐ 零和集 = 核（9 元素）—— 代数，不是 27 案穷举
--------------------------------------------------------------------------------

-- 充分性：给定前两分量，(a, b, negate (a⊕b)) 必零和
--   证明只用 ⊕-inverse，**不需要任何 case**。
c-gives-zero-sum : ∀ (a b : Trit) → ZeroSum (a , b , negate (a ⊕ b))
c-gives-zero-sum a b = ⊕-inverse (a ⊕ b)

-- 必要性：若 (a,b,c) 零和，则 c ≡ negate (a⊕b)
--   Trit 只有 3 个构造子 ⇒ 27 案，每案 refl（≤27，符合穷举上限）
zero-sum-gives-c : ∀ (a b c : Trit) → ZeroSum (a , b , c) → c ≡ negate (a ⊕ b)
zero-sum-gives-c T₀ T₀ T₀ p = refl
zero-sum-gives-c T₀ T₀ T₁ ()
zero-sum-gives-c T₀ T₀ T₂ ()
zero-sum-gives-c T₀ T₁ T₀ ()
zero-sum-gives-c T₀ T₁ T₁ ()
zero-sum-gives-c T₀ T₁ T₂ p = refl
zero-sum-gives-c T₀ T₂ T₀ ()
zero-sum-gives-c T₀ T₂ T₁ p = refl
zero-sum-gives-c T₀ T₂ T₂ ()
zero-sum-gives-c T₁ T₀ T₀ ()
zero-sum-gives-c T₁ T₀ T₁ ()
zero-sum-gives-c T₁ T₀ T₂ p = refl
zero-sum-gives-c T₁ T₁ T₀ ()
zero-sum-gives-c T₁ T₁ T₁ p = refl
zero-sum-gives-c T₁ T₁ T₂ ()
zero-sum-gives-c T₁ T₂ T₀ p = refl
zero-sum-gives-c T₁ T₂ T₁ ()
zero-sum-gives-c T₁ T₂ T₂ ()
zero-sum-gives-c T₂ T₀ T₀ ()
zero-sum-gives-c T₂ T₀ T₁ p = refl
zero-sum-gives-c T₂ T₀ T₂ ()
zero-sum-gives-c T₂ T₁ T₀ p = refl
zero-sum-gives-c T₂ T₁ T₁ ()
zero-sum-gives-c T₂ T₁ T₂ ()
zero-sum-gives-c T₂ T₂ T₀ ()
zero-sum-gives-c T₂ T₂ T₁ ()
zero-sum-gives-c T₂ T₂ T₂ p = refl

-- ⭐⭐ 零和集 ≅ 核 = 2 维子空间（9 元素）
--
--   由 c-gives-zero-sum：对任意 (a,b)（3×3 = 9 种），
--   存在（由 zero-sum-gives-c 还唯一）一个 c 使 (a,b,c) 零和。
--   ⇒ |ZeroSum| = 3 × 3 = 9。
--
--   本模块给出两个方向，基数结论由它们共同确定（不枚举 27 个三元组）。

--------------------------------------------------------------------------------
-- §6. ⭐ negate 保持零和（零和集在 negate 下封闭）
--------------------------------------------------------------------------------

-- 桥接引理：negate 是加法反同态（对 GF(3) 的加法群即同态，因为秩 2）
neg-distrib-⊕ : ∀ (x y : Trit) → negate (x ⊕ y) ≡ negate x ⊕ negate y
neg-distrib-⊕ T₀ T₀ = refl
neg-distrib-⊕ T₀ T₁ = refl
neg-distrib-⊕ T₀ T₂ = refl
neg-distrib-⊕ T₁ T₀ = refl
neg-distrib-⊕ T₁ T₁ = refl
neg-distrib-⊕ T₁ T₂ = refl
neg-distrib-⊕ T₂ T₀ = refl
neg-distrib-⊕ T₂ T₁ = refl
neg-distrib-⊕ T₂ T₂ = refl

-- negate T₀ ≡ T₀
neg-zero : negate T₀ ≡ T₀
neg-zero = refl

-- ⭐ negate 保持零和
neg-preserves-zero-sum : ∀ v → ZeroSum v → ZeroSum (neg-flavor v)
neg-preserves-zero-sum (a , b , c) p = subst-zero p
  where
    -- 目标: (negate a ⊕ negate b) ⊕ negate c ≡ T₀
    -- 由 neg-distrib-⊕ 反向把 negate 提出：
    --   (na ⊕ nb) ⊕ nc ≡ negate ((a ⊕ b) ⊕ c)
    -- 而 p : (a ⊕ b) ⊕ c ≡ T₀
    -- ⇒ negate T₀ ≡ T₀
    lemma : ((negate a ⊕ negate b) ⊕ negate c) ≡ negate ((a ⊕ b) ⊕ c)
    lemma = trans
              (cong (λ z → z ⊕ negate c) (sym (neg-distrib-⊕ a b)))
              (sym (neg-distrib-⊕ (a ⊕ b) c))

    subst-zero : ((a ⊕ b) ⊕ c ≡ T₀) → ((negate a ⊕ negate b) ⊕ negate c) ≡ T₀
    subst-zero q = trans lemma (trans (cong negate q) neg-zero)

--------------------------------------------------------------------------------
-- §7. ⚠ 诚实边界（散文断言规则：无定理的必须标注）
--------------------------------------------------------------------------------

-- [直觉·未验证] 「混合过程保持零和」需要 PMNS 矩阵的幺正性，
--   本模块**没有**形式化 PMNS，所以这条**不是定理**。
--
-- [直觉·未验证] 「(T₁,T₁,T₁) 而非 (T₂,T₂,T₂) 是物理终态」需要额外破缺机制；
--   本模块只证明两者**都**是等分量零和态（§4），因此「唯一性」**不成立**。
--
-- [事实·已证] negate 互换 T₁ 与 T₂（refl）。
-- [事实·已证] negate 保持零和（§6）。
-- [事实·已证] 零和 ⟺ c = negate (a⊕b)（§5，27 案）。
