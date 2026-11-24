{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.FrobF9
-- Frobenius σ 于 GF(9) 的载体层（M6 · B1）
--
-- 数学背景:
--   GF(9) = GF(3)[α]/(α²+1) 的 Frobenius: σ(a + bα) = a + bα³ = a − bα
--   （α³ = α·α² = −α），即**共轭**: σ = f9conj, 且 σ² = id（F₃ 上 Frobenius 恒等）。
--   σ 是环自同（negate 的 ⊕/⊗ 分配性承载, 3³ 全枚举逐格 refl）。
--   曲线方程系数为 F₃-嵌入（σ-不动），故 rhs σ-等变: σ(rhs(x)) = rhs(σx)，
--   ⟹ E(F₉) 的点集 σ-封闭（frob-closed）——σ 作为 E(F₉) 点集上的置换的载体。
--
-- 诚实边界:
--   本件是**点集置换**载体; σ 作为群自同 End(E) 元素（Deuring 正常元 ρ²=−3 的
--   环论意义）需要 E(F₉) 群律——库内 0 命中, 见 A5.2 注记 B5（未排期）。

module Sovereign.Application.Problems.RH.FrobF9 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF9All

--------------------------------------------------------------------------------
-- §1. negate 的分配性（3³ 全枚举, 逐格 refl）
--------------------------------------------------------------------------------

negate2 : ∀ b → negate (negate b) ≡ b
negate2 T₀ = refl
negate2 T₁ = refl
negate2 T₂ = refl

neg-⊕-distr : ∀ u v → negate (u ⊕ v) ≡ negate u ⊕ negate v
neg-⊕-distr T₀ T₀ = refl
neg-⊕-distr T₀ T₁ = refl
neg-⊕-distr T₀ T₂ = refl
neg-⊕-distr T₁ T₀ = refl
neg-⊕-distr T₁ T₁ = refl
neg-⊕-distr T₁ T₂ = refl
neg-⊕-distr T₂ T₀ = refl
neg-⊕-distr T₂ T₁ = refl
neg-⊕-distr T₂ T₂ = refl

neg-⊗-l : ∀ u v → negate (u ⊗ v) ≡ negate u ⊗ v
neg-⊗-l T₀ T₀ = refl
neg-⊗-l T₀ T₁ = refl
neg-⊗-l T₀ T₂ = refl
neg-⊗-l T₁ T₀ = refl
neg-⊗-l T₁ T₁ = refl
neg-⊗-l T₁ T₂ = refl
neg-⊗-l T₂ T₀ = refl
neg-⊗-l T₂ T₁ = refl
neg-⊗-l T₂ T₂ = refl

neg-⊗-r : ∀ u v → negate (u ⊗ v) ≡ u ⊗ negate v
neg-⊗-r T₀ T₀ = refl
neg-⊗-r T₀ T₁ = refl
neg-⊗-r T₀ T₂ = refl
neg-⊗-r T₁ T₀ = refl
neg-⊗-r T₁ T₁ = refl
neg-⊗-r T₁ T₂ = refl
neg-⊗-r T₂ T₀ = refl
neg-⊗-r T₂ T₁ = refl
neg-⊗-r T₂ T₂ = refl

neg-⊗-neg : ∀ u v → negate u ⊗ negate v ≡ u ⊗ v
neg-⊗-neg T₀ T₀ = refl
neg-⊗-neg T₀ T₁ = refl
neg-⊗-neg T₀ T₂ = refl
neg-⊗-neg T₁ T₀ = refl
neg-⊗-neg T₁ T₁ = refl
neg-⊗-neg T₁ T₂ = refl
neg-⊗-neg T₂ T₀ = refl
neg-⊗-neg T₂ T₁ = refl
neg-⊗-neg T₂ T₂ = refl

--------------------------------------------------------------------------------
-- §2. σ = f9conj: 对合 + 环自同
--------------------------------------------------------------------------------

f9conj : F9 → F9
f9conj (mkF9 a b) = mkF9 a (negate b)

f9conj2 : ∀ x → f9conj (f9conj x) ≡ x
f9conj2 (mkF9 a b) = cong (mkF9 a) (negate2 b)

f9add-conj : ∀ x y → f9conj (f9add x y) ≡ f9add (f9conj x) (f9conj y)
f9add-conj (mkF9 a b) (mkF9 c d) =
  cong₂ mkF9 refl (neg-⊕-distr b d)

f9mul-conj : ∀ x y → f9conj (f9mul x y) ≡ f9mul (f9conj x) (f9conj y)
f9mul-conj (mkF9 a b) (mkF9 c d) =
  cong₂ mkF9 first-comp second-comp
  where
  -- 首分量: (a⊗c) ⊕ negate(b⊗d) ≡ (a⊗c) ⊕ negate((neg b)⊗(neg d))
  first-comp : (a ⊗ c) ⊕ negate (b ⊗ d)
             ≡ (a ⊗ c) ⊕ negate (negate b ⊗ negate d)
  first-comp = cong (λ z → (a ⊗ c) ⊕ negate z) (sym (neg-⊗-neg b d))
  -- 次分量: negate((a⊗d) ⊕ (b⊗c)) ≡ (a⊗(neg d)) ⊕ ((neg b)⊗c)
  second-comp : negate ((a ⊗ d) ⊕ (b ⊗ c))
              ≡ (a ⊗ negate d) ⊕ (negate b ⊗ c)
  second-comp =
    trans (neg-⊕-distr (a ⊗ d) (b ⊗ c))
          (cong₂ _⊕_ (neg-⊗-r a d) (neg-⊗-l b c))

--------------------------------------------------------------------------------
-- §3. F₃-嵌入 σ-不动 + rhs σ-等变 + E(F₉) 点封闭
--------------------------------------------------------------------------------

t2f9-conj : ∀ t → f9conj (t2f9 t) ≡ t2f9 t
t2f9-conj T₀ = refl
t2f9-conj T₁ = refl
t2f9-conj T₂ = refl

-- conj 穿透左嵌套 f9add（rhs9 的三层结构用）
conj-add2 : ∀ u v → f9conj (f9add u v)
                 ≡ f9add (f9conj u) (f9conj v)
conj-add2 = f9add-conj

conj-add3 : ∀ u v w → f9conj (f9add (f9add u v) w)
                   ≡ f9add (f9add (f9conj u) (f9conj v)) (f9conj w)
conj-add3 u v w =
  trans (f9add-conj (f9add u v) w)
        (cong (λ z → f9add z (f9conj w)) (f9add-conj u v))

conj-add4 : ∀ u v w z
          → f9conj (f9add (f9add (f9add u v) w) z)
          ≡ f9add (f9add (f9add (f9conj u) (f9conj v)) (f9conj w)) (f9conj z)
conj-add4 u v w z =
  trans (f9add-conj (f9add (f9add u v) w) z)
        (cong (λ A → f9add A (f9conj z)) (conj-add3 u v w))

-- rhs 的 σ-等变（系数 F₃-嵌入 σ-不动; 泛型引理, 对所有曲线/点成立）
rhs9-conj : ∀ (c : CurveF3) (x : F9)
          → f9conj (rhs9 c x) ≡ rhs9 c (f9conj x)
rhs9-conj (mkC a₂ a₄ a₆) x =
  trans (conj-add4 (f9mul (f9mul x x) x)
                   (f9mul (t2f9 a₂) (f9mul x x))
                   (f9mul (t2f9 a₄) x)
                   (t2f9 a₆))
        (cong₄ (λ u w y r → f9add (f9add (f9add u w) y) r)
               L1 L2 L3 (t2f9-conj a₆))
  where
  open ≡-Reasoning
  -- 叶改写: conj(叶) ≡ 叶的 σ-形（目标 rhs9 c (f9conj x) 的对应分量）
  L1 : f9conj (f9mul (f9mul x x) x)
     ≡ f9mul (f9mul (f9conj x) (f9conj x)) (f9conj x)
  L1 = trans (f9mul-conj (f9mul x x) x)
             (cong (λ z → f9mul z (f9conj x)) (f9mul-conj x x))
  L2 : f9conj (f9mul (t2f9 a₂) (f9mul x x))
     ≡ f9mul (t2f9 a₂) (f9mul (f9conj x) (f9conj x))
  L2 = trans (f9mul-conj (t2f9 a₂) (f9mul x x))
             (trans (cong (λ z → f9mul z (f9conj (f9mul x x))) (t2f9-conj a₂))
                    (cong (f9mul (t2f9 a₂)) (f9mul-conj x x)))
  L3 : f9conj (f9mul (t2f9 a₄) x)
     ≡ f9mul (t2f9 a₄) (f9conj x)
  L3 = trans (f9mul-conj (t2f9 a₄) x)
             (cong (λ z → f9mul z (f9conj x)) (t2f9-conj a₄))
  cong₃ : ∀ {A B : Set} (f : A → A → A → B) {u v w x y z : A}
        → u ≡ v → w ≡ x → y ≡ z → f u w y ≡ f v x z
  cong₃ f refl refl refl = refl
  cong₄ : ∀ {A B : Set} (f : A → A → A → A → B)
        {u v w x y z r s : A}
        → u ≡ v → w ≡ x → y ≡ z → r ≡ s
        → f u w y r ≡ f v x z s
  cong₄ f refl refl refl refl = refl

-- 点封闭: y² = rhs(x) ⟹ (σy)² = rhs(σx)（σ 作为 E(F₉) 点集置换的载体）
frob-closed : ∀ (c : CurveF3) (x y : F9)
            → f9mul y y ≡ rhs9 c x
            → f9mul (f9conj y) (f9conj y) ≡ rhs9 c (f9conj x)
frob-closed c x y he =
  trans (sym (f9mul-conj y y))
  (trans (cong f9conj he) (rhs9-conj c x))
