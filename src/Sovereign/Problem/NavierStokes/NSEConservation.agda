{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEConservation
-- 总量守恒主定理: 全环面对差分的求和恒为 T₀ ⇒ `nsStep` 保总量
--
-- 目标（台账 `NSE.conservation.torus-total`）:
--   **主定理** `torusSum-diffF : ∀ i f → torusSum (diffF i f) ≡ T₀`
--   （离散散度定理的 T⁶ 全环面版）;
--   **推论** `total-nsStep : ∀ v → totalF (nsStep v) ≡ totalF v`
--   （`grad` 六分量均为 `diffF`（NSEOnT6:534-536）⇒ 总量不变）。
--   物理读法: 单点可被搬运, **总量不可增减**——O3 的「多步/耦合集中」被总量守恒限制。
--
-- 装配件（已在库/上一批闭合, 本模块只组装）:
--   · `fold1-cong` / `fold1-+` / `fold1-negate` / `fold1-shift`（NSEConservationCore）
--     —— funext 障碍已由 `fold1-cong` 解除（逐点 → 整体, 有限折叠不需要 funext）
--   · `sum3-+` / `negate-⊕` / `_+S_` / `diffF` / `shiftF`（NSEOnT6）
--
-- 结构:
--   §1 逐层部分和 S6…S2 + torusSum（6 层嵌套 fold1）
--   §2 同态性: torusSum-+S（split6…split2 逐层）
--   §3 移位不变: torusSum-shiftF（3 个轴, 逐层 fold1-shift）
--   §4 取负交换: torusSum-negate（negS6…negS2 逐层）
--   §5 **主定理** torusSum-diffF + **推论** totalF 守恒（sum6-cong 一次到位）
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEConservation where

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-identityʳ)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6; mkField;
   sum3; sum6; shift3; shiftAt; shiftF; diffF; _+S_; _+F_; div; grad; nsStep)
open import Sovereign.Problem.NavierStokes.NSEConservationCore using
  (fold1; fold1-cong; fold1-+; fold1-negate; fold1-shift)

--------------------------------------------------------------------------------
-- §1. 逐层部分和（显式命名, 使逐层装配的引理陈述短）
--------------------------------------------------------------------------------

S6 : ScalarField → C3 → C3 → C3 → C3 → C3 → Trit
S6 f x1 x2 x3 x4 x5 = fold1 (λ x6 → f (x1 , x2 , x3 , x4 , x5 , x6))

S5 : ScalarField → C3 → C3 → C3 → C3 → Trit
S5 f x1 x2 x3 x4 = fold1 (λ x5 → S6 f x1 x2 x3 x4 x5)

S4 : ScalarField → C3 → C3 → C3 → Trit
S4 f x1 x2 x3 = fold1 (λ x4 → S5 f x1 x2 x3 x4)

S3 : ScalarField → C3 → C3 → Trit
S3 f x1 x2 = fold1 (λ x3 → S4 f x1 x2 x3)

S2 : ScalarField → C3 → Trit
S2 f x1 = fold1 (λ x2 → S3 f x1 x2)

-- 全环面求和（729 点）
torusSum : ScalarField → Trit
torusSum f = fold1 (λ x1 → S2 f x1)

negateF : ScalarField → ScalarField
negateF f x = negate (f x)

--------------------------------------------------------------------------------
-- §2. 同态性: torusSum (f +S g) ≡ torusSum f ⊕ torusSum g（逐层 split）
--------------------------------------------------------------------------------

split6 : ∀ f g x1 x2 x3 x4 x5 →
  S6 (f +S g) x1 x2 x3 x4 x5 ≡ S6 f x1 x2 x3 x4 x5 ⊕ S6 g x1 x2 x3 x4 x5
split6 f g x1 x2 x3 x4 x5 =
  fold1-+ (λ x6 → f (x1 , x2 , x3 , x4 , x5 , x6))
          (λ x6 → g (x1 , x2 , x3 , x4 , x5 , x6))

split5 : ∀ f g x1 x2 x3 x4 →
  S5 (f +S g) x1 x2 x3 x4 ≡ S5 f x1 x2 x3 x4 ⊕ S5 g x1 x2 x3 x4
split5 f g x1 x2 x3 x4 =
  trans (fold1-cong (λ x5 → split6 f g x1 x2 x3 x4 x5))
        (fold1-+ (λ x5 → S6 f x1 x2 x3 x4 x5) (λ x5 → S6 g x1 x2 x3 x4 x5))

split4 : ∀ f g x1 x2 x3 →
  S4 (f +S g) x1 x2 x3 ≡ S4 f x1 x2 x3 ⊕ S4 g x1 x2 x3
split4 f g x1 x2 x3 =
  trans (fold1-cong (λ x4 → split5 f g x1 x2 x3 x4))
        (fold1-+ (λ x4 → S5 f x1 x2 x3 x4) (λ x4 → S5 g x1 x2 x3 x4))

split3 : ∀ f g x1 x2 →
  S3 (f +S g) x1 x2 ≡ S3 f x1 x2 ⊕ S3 g x1 x2
split3 f g x1 x2 =
  trans (fold1-cong (λ x3 → split4 f g x1 x2 x3))
        (fold1-+ (λ x3 → S4 f x1 x2 x3) (λ x3 → S4 g x1 x2 x3))

split2 : ∀ f g x1 →
  S2 (f +S g) x1 ≡ S2 f x1 ⊕ S2 g x1
split2 f g x1 =
  trans (fold1-cong (λ x2 → split3 f g x1 x2))
        (fold1-+ (λ x2 → S3 f x1 x2) (λ x2 → S3 g x1 x2))

torusSum-+S : ∀ f g → torusSum (f +S g) ≡ torusSum f ⊕ torusSum g
torusSum-+S f g =
  trans (fold1-cong (λ x1 → split2 f g x1))
        (fold1-+ (λ x1 → S2 f x1) (λ x1 → S2 g x1))

--------------------------------------------------------------------------------
-- §3. 移位不变: torusSum (shiftF i f) ≡ torusSum f
--
-- NSEOnT6 的 shiftAt 只作用于前三个坐标（x1/x2/x3）, 逐层对应 S2/S3/S4 的绑定位。
-- 各层的 Sₖ 恒等式在定义上成立（shift3 的展开）, 故只需 fold1-shift/fold1-cong。
--------------------------------------------------------------------------------

torusSum-shiftF : ∀ (i : C3) (f : ScalarField) →
  torusSum (shiftF i f) ≡ torusSum f
torusSum-shiftF zero f = fold1-shift (S2 f)
torusSum-shiftF (suc zero) f = fold1-cong (λ x1 → fold1-shift (S3 f x1))
torusSum-shiftF (suc (suc zero)) f =
  fold1-cong (λ x1 → fold1-cong (λ x2 → fold1-shift (S4 f x1 x2)))

--------------------------------------------------------------------------------
-- §4. 取负交换: torusSum (negateF f) ≡ negate (torusSum f)（逐层 negS）
--------------------------------------------------------------------------------

negS6 : ∀ f x1 x2 x3 x4 x5 →
  S6 (negateF f) x1 x2 x3 x4 x5 ≡ negate (S6 f x1 x2 x3 x4 x5)
negS6 f x1 x2 x3 x4 x5 =
  fold1-negate (λ x6 → f (x1 , x2 , x3 , x4 , x5 , x6))

negS5 : ∀ f x1 x2 x3 x4 →
  S5 (negateF f) x1 x2 x3 x4 ≡ negate (S5 f x1 x2 x3 x4)
negS5 f x1 x2 x3 x4 =
  trans (fold1-cong (λ x5 → negS6 f x1 x2 x3 x4 x5))
        (fold1-negate (λ x5 → S6 f x1 x2 x3 x4 x5))

negS4 : ∀ f x1 x2 x3 →
  S4 (negateF f) x1 x2 x3 ≡ negate (S4 f x1 x2 x3)
negS4 f x1 x2 x3 =
  trans (fold1-cong (λ x4 → negS5 f x1 x2 x3 x4))
        (fold1-negate (λ x4 → S5 f x1 x2 x3 x4))

negS3 : ∀ f x1 x2 →
  S3 (negateF f) x1 x2 ≡ negate (S3 f x1 x2)
negS3 f x1 x2 =
  trans (fold1-cong (λ x3 → negS4 f x1 x2 x3))
        (fold1-negate (λ x3 → S4 f x1 x2 x3))

negS2 : ∀ f x1 →
  S2 (negateF f) x1 ≡ negate (S2 f x1)
negS2 f x1 =
  trans (fold1-cong (λ x2 → negS3 f x1 x2))
        (fold1-negate (λ x2 → S3 f x1 x2))

torusSum-negate : ∀ f → torusSum (negateF f) ≡ negate (torusSum f)
torusSum-negate f =
  trans (fold1-cong (λ x1 → negS2 f x1))
        (fold1-negate (λ x1 → S2 f x1))

--------------------------------------------------------------------------------
-- §5. 主定理与推论
--------------------------------------------------------------------------------

-- GF(3) 逆元律（3 case; 库内表归约即证）
plus-negate-zero : ∀ (a : Trit) → a ⊕ negate a ≡ T₀
plus-negate-zero T₀ = refl
plus-negate-zero T₁ = refl
plus-negate-zero T₂ = refl

-- **主定理**（离散散度定理 T⁶ 版）: 全环面对差分的求和恒为 T₀
torusSum-diffF : ∀ (i : C3) (f : ScalarField) → torusSum (diffF i f) ≡ T₀
torusSum-diffF i f =
  trans (torusSum-+S (shiftF i f) (negateF f))
  (trans (cong₂ _⊕_ (torusSum-shiftF i f) (torusSum-negate f))
         (plus-negate-zero (torusSum f)))

-- 六分量总量
totalF : Field → Trit
totalF v = sum6 (torusSum (v1 v)) (torusSum (v2 v)) (torusSum (v3 v))
               (torusSum (v4 v)) (torusSum (v5 v)) (torusSum (v6 v))

-- sum6 的六点同余（由 J/模式匹配一次给出, 免去深层 cong 括号链）
sum6-cong : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : Trit} →
  a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ →
  sum6 a₁ b₁ c₁ d₁ e₁ f₁ ≡ sum6 a₂ b₂ c₂ d₂ e₂ f₂
sum6-cong refl refl refl refl refl refl = refl

-- 单分量守恒: torusSum (f +S diffF i s) ≡ torusSum f
comp-conserved : ∀ (f s : ScalarField) (i : C3) →
  torusSum (f +S diffF i s) ≡ torusSum f
comp-conserved f s i =
  trans (torusSum-+S f (diffF i s))
        (trans (cong (torusSum f ⊕_) (torusSum-diffF i s))
               (⊕-identityʳ (torusSum f)))

-- **推论**: `nsStep` 保总量（grad 六分量均为 diffF, NSEOnT6:534-536）
total-nsStep : ∀ (v : Field) → totalF (nsStep v) ≡ totalF v
total-nsStep v =
  sum6-cong
    (comp-conserved (v1 v) (div v) zero)
    (comp-conserved (v2 v) (div v) (suc zero))
    (comp-conserved (v3 v) (div v) (suc (suc zero)))
    (comp-conserved (v4 v) (div v) zero)
    (comp-conserved (v5 v) (div v) (suc zero))
    (comp-conserved (v6 v) (div v) (suc (suc zero)))

--------------------------------------------------------------------------------
-- §6. 诚实边界
--
-- ✓ 已证: torusSum-+S / torusSum-shiftF / torusSum-negate / **torusSum-diffF** /
--   **total-nsStep**（全部构造性, 无 postulate）。
-- ✗ 不声称:
--   ① 这不是连续统的守恒律（能量/动量）——只是本离散基座上的**总量不变**;
--   ② 「总量守恒 ⇒ 无集中」**不成立**（总量不变仍允许再分布）——
--      O3 的多步集中问题**部分**受限（总量通道被封）, 完全闭合仍需支撑集/集中度定理;
--   ③ `Incompressible` 保持性（NSEOnT6:615）的前提 `laplacian ≡ T₀` 已被 T1 否证
--      ——那条定理是**条件式**, 本模块不引用。
--------------------------------------------------------------------------------
