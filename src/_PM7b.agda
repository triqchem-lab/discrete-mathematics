{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PM7b
-- Hₖ 群律：transport-of-structure（M7a 立界件）
--
-- 数学背景：Hₖ = Cₖ/HR 是 HIT 商（_PM7a HomologyQuotient）。Cₖ 的 FAb 群律
--   经 HR 同余搬入商层——「群律 transport-of-structure」：商层群律 =
--   C 层群律 + HR 同余（add-resp/neg-resp）+ 商泛性质（elim/elimProp 族）。
-- 核心原则：
-- 1. 复用优先：HomologyQuotient/HRWells（_PM7a）零重证；H₀ 先例的 elim 三参形
-- 2. 群律五件（assoc / 单位双侧 / 逆双侧）+ 交换律 bonus
-- 3. HR 同余为显式参数（条件形——任务书「HRWells 实例化若卡则条件形交付」）
-- 4. 零洞零 postulate（参数前提范式——关系入定义纪律）
-- 包含：HkGroupLaws（泛型群律——transport 主定理）· K3GroupLaws（FAb3 半实例）
--       · 核对层 · 立界注记

module _PM7b where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; elim)
open import Cubical.HITs.SetQuotients.Properties using (elimProp; elimProp2)
open import Cubical.Foundations.HLevels using (isSetΠ; isPropΠ; isPropΠ2)
import _PM7a
open import Sovereign.Algebra.FreeAb using (FAb; _+ᶠ_; negᶠ)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₀; C₁; C₂; ∂₁; ∂₂)

--------------------------------------------------------------------------------
-- §0 逐点 Trit 律（策略 A ≤27 case——transport 源的最底层）
--------------------------------------------------------------------------------

⊕-assoc-pt : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc-pt T₀ T₀ T₀ = refl
⊕-assoc-pt T₀ T₀ T₁ = refl
⊕-assoc-pt T₀ T₀ T₂ = refl
⊕-assoc-pt T₀ T₁ T₀ = refl
⊕-assoc-pt T₀ T₁ T₁ = refl
⊕-assoc-pt T₀ T₁ T₂ = refl
⊕-assoc-pt T₀ T₂ T₀ = refl
⊕-assoc-pt T₀ T₂ T₁ = refl
⊕-assoc-pt T₀ T₂ T₂ = refl
⊕-assoc-pt T₁ T₀ T₀ = refl
⊕-assoc-pt T₁ T₀ T₁ = refl
⊕-assoc-pt T₁ T₀ T₂ = refl
⊕-assoc-pt T₁ T₁ T₀ = refl
⊕-assoc-pt T₁ T₁ T₁ = refl
⊕-assoc-pt T₁ T₁ T₂ = refl
⊕-assoc-pt T₁ T₂ T₀ = refl
⊕-assoc-pt T₁ T₂ T₁ = refl
⊕-assoc-pt T₁ T₂ T₂ = refl
⊕-assoc-pt T₂ T₀ T₀ = refl
⊕-assoc-pt T₂ T₀ T₁ = refl
⊕-assoc-pt T₂ T₀ T₂ = refl
⊕-assoc-pt T₂ T₁ T₀ = refl
⊕-assoc-pt T₂ T₁ T₁ = refl
⊕-assoc-pt T₂ T₁ T₂ = refl
⊕-assoc-pt T₂ T₂ T₀ = refl
⊕-assoc-pt T₂ T₂ T₁ = refl
⊕-assoc-pt T₂ T₂ T₂ = refl

⊕-comm-pt : ∀ a b → a ⊕ b ≡ b ⊕ a
⊕-comm-pt T₀ T₀ = refl
⊕-comm-pt T₀ T₁ = refl
⊕-comm-pt T₀ T₂ = refl
⊕-comm-pt T₁ T₀ = refl
⊕-comm-pt T₁ T₁ = refl
⊕-comm-pt T₁ T₂ = refl
⊕-comm-pt T₂ T₀ = refl
⊕-comm-pt T₂ T₁ = refl
⊕-comm-pt T₂ T₂ = refl

negSelf : ∀ a → a ⊕ negate a ≡ T₀
negSelf T₀ = refl
negSelf T₁ = refl
negSelf T₂ = refl

negSelfˡ : ∀ a → negate a ⊕ a ≡ T₀
negSelfˡ T₀ = refl
negSelfˡ T₁ = refl
negSelfˡ T₂ = refl

zerSelfˡ : ∀ a → T₀ ⊕ a ≡ a
zerSelfˡ T₀ = refl
zerSelfˡ T₁ = refl
zerSelfˡ T₂ = refl

zerSelfʳ : ∀ a → a ⊕ T₀ ≡ a
zerSelfʳ T₀ = refl
zerSelfʳ T₁ = refl
zerSelfʳ T₂ = refl

sub₃ : C₁ → C₁ → C₁
sub₃ x y = λ i → x i ⊕ negate (y i)

zero₃ : C₁
zero₃ = λ _ → T₀

--------------------------------------------------------------------------------
-- §1 泛型群律（transport-of-structure 主定理）
--------------------------------------------------------------------------------

module HkGroupLaws
  (Cₖ Cₖ₋₁ Cₖ₊₁ : Set)
  (sub : Cₖ → Cₖ → Cₖ)
  (∂k : Cₖ → Cₖ₋₁) (zero₁ : Cₖ₋₁)
  (∂kp1 : Cₖ₊₁ → Cₖ)
  (comp0 : (c : Cₖ₊₁) → ∂k (∂kp1 c) ≡ zero₁)
  where

  open _PM7a.HomologyQuotient Cₖ Cₖ₋₁ Cₖ₊₁ sub ∂k zero₁ ∂kp1 comp0
    using (KerSub; ImElem; im⊂ker; HR; Hk; HRWells)

  module Laws
    (add : Cₖ → Cₖ → Cₖ) (zer : Cₖ) (neg : Cₖ → Cₖ)
    (add-assoc : ∀ x y z → add (add x y) z ≡ add x (add y z))
    (add-zerˡ : ∀ x → add zer x ≡ x)
    (add-zerʳ : ∀ x → add x zer ≡ x)
    (add-negˡ : ∀ x → add (neg x) x ≡ zer)
    (add-negʳ : ∀ x → add x (neg x) ≡ zer)
    (add-comm : ∀ x y → add x y ≡ add y x)
    (wells : HRWells)
    (add-resp : ∀ x x' y y' → HR x x' → HR y y' → HR (add x y) (add x' y'))
    (neg-resp : ∀ x x' → HR x x' → HR (neg x) (neg x'))
    where

    open HRWells wells using (hr-refl; hr-sym; hr-trans; hr-resp)

    -- 商层运算（双 elim——H₀ 先例的 elim 三参形）
    +ₕL : Cₖ → Hk → Hk
    +ₕL x = elim {P = λ _ → Hk} (λ _ → squash/) (λ y → [ add x y ])
                (λ y y' r → eq/ _ _ (add-resp x x y y' (hr-refl x) r))

    +ₕL-resp : ∀ x x' (q : Hk) → HR x x' → +ₕL x q ≡ +ₕL x' q
    +ₕL-resp x x' q r =
      elimProp {P = λ q → +ₕL x q ≡ +ₕL x' q} (λ _ → squash/ _ _)
               (λ y → eq/ _ _ (add-resp x x' y y r (hr-refl y))) q

    _+ₕ_ : Hk → Hk → Hk
    _+ₕ_ = elim {P = λ _ → Hk → Hk} (λ _ → isSetΠ (λ _ → squash/)) (λ x → +ₕL x)
                (λ x x' r → funExt (λ q → +ₕL-resp x x' q r))

    zerₕ : Hk
    zerₕ = [ zer ]

    negₕ : Hk → Hk
    negₕ = elim {P = λ _ → Hk} (λ _ → squash/) (λ x → [ neg x ])
                (λ x x' r → eq/ _ _ (neg-resp x x' r))

    -- 群律五件 + 交换律（transport：C 层律经 cong [_] 抬升 + elimProp 泛化）
    assocₕ : ∀ a b c → (a +ₕ b) +ₕ c ≡ a +ₕ (b +ₕ c)
    assocₕ = elimProp {P = λ a → ∀ b c → (a +ₕ b) +ₕ c ≡ a +ₕ (b +ₕ c)}
             (λ _ → isPropΠ2 (λ _ _ → squash/ _ _))
             (λ x → elimProp2 {P = λ y z → ([ x ] +ₕ y) +ₕ z ≡ [ x ] +ₕ (y +ₕ z)}
                              (λ _ _ → squash/ _ _)
                              (λ y z → cong [_] (add-assoc x y z)))

    zerˡₕ : ∀ a → zerₕ +ₕ a ≡ a
    zerˡₕ = elimProp {P = λ a → zerₕ +ₕ a ≡ a} (λ _ → squash/ _ _) (λ x → cong [_] (add-zerˡ x))

    zerʳₕ : ∀ a → a +ₕ zerₕ ≡ a
    zerʳₕ = elimProp {P = λ a → a +ₕ zerₕ ≡ a} (λ _ → squash/ _ _) (λ x → cong [_] (add-zerʳ x))

    negˡₕ : ∀ a → negₕ a +ₕ a ≡ zerₕ
    negˡₕ = elimProp {P = λ a → negₕ a +ₕ a ≡ zerₕ} (λ _ → squash/ _ _) (λ x → cong [_] (add-negˡ x))

    negʳₕ : ∀ a → a +ₕ negₕ a ≡ zerₕ
    negʳₕ = elimProp {P = λ a → a +ₕ negₕ a ≡ zerₕ} (λ _ → squash/ _ _) (λ x → cong [_] (add-negʳ x))

    commₕ : ∀ a b → a +ₕ b ≡ b +ₕ a
    commₕ = elimProp2 {P = λ a b → a +ₕ b ≡ b +ₕ a} (λ _ _ → squash/ _ _) (λ x y → cong [_] (add-comm x y))

--------------------------------------------------------------------------------
-- §2 K₃ 半实例（FAb3：C 层群律全真 + HR 面参数——条件形）
--------------------------------------------------------------------------------

module K3GroupLaws
  (comp0-k3 : (c : C₂) → ∂₁ (∂₂ c) ≡ zero₃)
  where

  open _PM7a.HomologyQuotient C₁ C₀ C₂ sub₃ ∂₁ zero₃ ∂₂ comp0-k3
    using (HR; Hk; HRWells)

  -- C 层群律（transport 源——全真证明）
  addᶠ-assoc : ∀ (x y z : C₁) → (_+ᶠ_ {3} (_+ᶠ_ {3} x y) z) ≡ (_+ᶠ_ {3} x (_+ᶠ_ {3} y z))
  addᶠ-assoc x y z = funExt (λ i → ⊕-assoc-pt (x i) (y i) (z i))

  addᶠ-zerˡ : ∀ (x : C₁) → (_+ᶠ_ {3} zero₃ x) ≡ x
  addᶠ-zerˡ x = funExt (λ i → zerSelfˡ (x i))

  addᶠ-zerʳ : ∀ (x : C₁) → (_+ᶠ_ {3} x zero₃) ≡ x
  addᶠ-zerʳ x = funExt (λ i → zerSelfʳ (x i))

  addᶠ-negˡ : ∀ (x : C₁) → (_+ᶠ_ {3} (negᶠ {3} x) x) ≡ zero₃
  addᶠ-negˡ x = funExt (λ i → negSelfˡ (x i))

  addᶠ-negʳ : ∀ (x : C₁) → (_+ᶠ_ {3} x (negᶠ {3} x)) ≡ zero₃
  addᶠ-negʳ x = funExt (λ i → negSelf (x i))

  addᶠ-comm : ∀ (x y : C₁) → (_+ᶠ_ {3} x y) ≡ (_+ᶠ_ {3} y x)
  addᶠ-comm x y = funExt (λ i → ⊕-comm-pt (x i) (y i))

  -- 半实例组装：HR 面参数（立界 §3）→ 群律全形
  module Inst
    (wells-k3 : HRWells)
    (add-resp-k3 : ∀ x x' y y' → HR x x' → HR y y' → HR ((_+ᶠ_ {3}) x y) ((_+ᶠ_ {3}) x' y'))
    (neg-resp-k3 : ∀ x x' → HR x x' → HR ((negᶠ {3}) x) ((negᶠ {3}) x'))
    where

    open HkGroupLaws.Laws C₁ C₀ C₂ sub₃ ∂₁ zero₃ ∂₂ comp0-k3
      (_+ᶠ_ {3}) zero₃ (negᶠ {3})
      addᶠ-assoc addᶠ-zerˡ addᶠ-zerʳ addᶠ-negˡ addᶠ-negʳ addᶠ-comm
      wells-k3 add-resp-k3 neg-resp-k3
      public

--------------------------------------------------------------------------------
-- §3 核对层（defeq/小例 refl 级）
--------------------------------------------------------------------------------

-- 代表元层零元案核对（defeq 通道）
check-assoc-zeros : (_+ᶠ_ {3} (_+ᶠ_ {3} zero₃ zero₃) zero₃) ≡ (_+ᶠ_ {3} zero₃ (_+ᶠ_ {3} zero₃ zero₃))
check-assoc-zeros = refl

check-neg-t1 : (_+ᶠ_ {3} (λ i → T₁) (negᶠ {3} (λ i → T₁))) ≡ zero₃
check-neg-t1 = refl

-- 逐点样本（assoc）
check-assoc-pt-t1t1t2 : (T₁ ⊕ T₁) ⊕ T₂ ≡ T₁ ⊕ (T₁ ⊕ T₂)
check-assoc-pt-t1t1t2 = refl

--------------------------------------------------------------------------------
-- §4 立界注记（诚实边界）
--------------------------------------------------------------------------------
-- (i) HRWells 的 K₃ 实例化（等价三律 + hr-resp——K3Slice 的 ∂₁-hom 面同源件）~30-50 行
-- (ii) add-resp-k3：FAb 四项重排（sub₃ (x +ᶠ y) (x' +ᶠ y') ~ sub₃ x x' +ᶠ sub₃ y y'）
--     需 negate 分配 + ⊕-swap-mid 族（四项 81-case 超穷举边界——须 rearrange 代数链）~15-25 行
-- (iii) neg-resp-k3：negate 分配律 9-case ~10 行
-- (iv) 一般 X 的 Hₖ 商面 rec/elim 定理族（PT-4/PM7a 立界同源）
