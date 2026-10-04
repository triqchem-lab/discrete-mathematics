{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Algebra.FreeAbQuotient
-- 任务书第二层·2.5 泛型化（GAP-M7a-泛型）：FAb 上的 **cubical HIT 商群**
--
-- 数学背景：M7a 实例层（FreeAbHomologyGroup，setoid 形态）的泛型化——
--   复用 cubical-0.9 库件 SetQuotients（非自造 HIT）：
--     H₀ = C₀ / R₀（R₀ x y := aug x ≡ aug y）⟹ H₀ ≅ GF(3)
--     H₁ = C₁ / R₁（R₁ x y := ∂₁x ≡₁ ∂₁y 逐点）⟹ 循环类归零
--     H₂ = C₂ / R₂（R₂ x y := ∂₂x ≡∂₂y 逐点）⟹ 循环类归零
--
--   本模块全 cubical ≡（Path）自持：aug/h₀-bwd/h₀-fwd-bwd 局部重定义
--   （⊕ 表使 h₀-fwd-bwd 逐分支 refl——无 PropEq 桥接需求）。
--   同构只用 elim + eq/（注入性由 eq/ 直接构造，无需 effective）。
--   HIT + 文件级 --rewriting 共存实测（本模块 = 顶配测试床）。
--   群律以 transport-of-structure 形态闭合（沿 f₀ 同构拉回 Trit 群结构）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.FreeAbQuotient where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Empty.Base using (⊥)
open import Data.Unit using (⊤; tt)
open import Cubical.Relation.Nullary using (Discrete; Dec; yes; no; ¬_)
open import Cubical.Foundations.Prelude
  using (isSet; isProp; _≡_; refl; transport; sym; _∙_; cong; cong₂)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.SetQuotients.Properties using (elim; elimProp2)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; ⊕-comm)
open import Sovereign.Problem.Hodge.FreeAbBoundary
  using (C₀; C₁; C₂; ∂₁; ∂₂)

--------------------------------------------------------------------------------
-- §1. Trit 的 Discrete ⟹ isSet（Discrete→isSet 复用 + transport 惯用法）
--------------------------------------------------------------------------------

is₀ is₁ is₂ : Trit → Set
is₀ T₀ = ⊤
is₀ _ = ⊥
is₁ T₁ = ⊤
is₁ _ = ⊥
is₂ T₂ = ⊤
is₂ _ = ⊥

decEqTrit : Discrete Trit
decEqTrit T₀ T₀ = yes refl
decEqTrit T₀ T₁ = no (λ p → transport (λ i → is₀ (p i)) tt)
decEqTrit T₀ T₂ = no (λ p → transport (λ i → is₀ (p i)) tt)
decEqTrit T₁ T₀ = no (λ p → transport (λ i → is₁ (p i)) tt)
decEqTrit T₁ T₁ = yes refl
decEqTrit T₁ T₂ = no (λ p → transport (λ i → is₁ (p i)) tt)
decEqTrit T₂ T₀ = no (λ p → transport (λ i → is₂ (p i)) tt)
decEqTrit T₂ T₁ = no (λ p → transport (λ i → is₂ (p i)) tt)
decEqTrit T₂ T₂ = yes refl

isSetTrit : isSet Trit
isSetTrit = Discrete→isSet decEqTrit

--------------------------------------------------------------------------------
-- §2. 局部 cubical 自持定义（aug / h₀-bwd / h₀-fwd-bwd——全 refl）
--   ⊕ 表使 x ⊕ T₀ = x 定义性成立 ⟹ h₀-fwd-bwd 逐分支 refl。
--------------------------------------------------------------------------------

aug : C₀ → Trit
aug x = (x fzero ⊕ x (fsuc fzero)) ⊕ x (fsuc (fsuc fzero))

h₀-bwd : Trit → C₀
h₀-bwd c fzero = c
h₀-bwd c (fsuc _) = T₀

h₀-fwd-bwd : ∀ c → aug (h₀-bwd c) ≡ c
h₀-fwd-bwd T₀ = refl
h₀-fwd-bwd T₁ = refl
h₀-fwd-bwd T₂ = refl

--------------------------------------------------------------------------------
-- §3. 三个商关系（Prop 值，cubical ≡）
--------------------------------------------------------------------------------

R₀ : C₀ → C₀ → Set
R₀ x y = aug x ≡ aug y

R₁ : C₁ → C₁ → Set
R₁ x y = ∀ i → ∂₁ x i ≡ ∂₁ y i

R₂ : C₂ → C₂ → Set
R₂ x y = ∀ i → ∂₂ x i ≡ ∂₂ y i

--------------------------------------------------------------------------------
-- §4. 三个 HIT 商类型
--------------------------------------------------------------------------------

H₀ H₁ H₂ : Set
H₀ = C₀ / R₀
H₁ = C₁ / R₁
H₂ = C₂ / R₂

zeroᶠ-C₀ : C₀
zeroᶠ-C₀ = λ _ → T₀

zeroᶠ-C₁ : C₁
zeroᶠ-C₁ = λ _ → T₀

zeroᶠ-C₂ : C₂
zeroᶠ-C₂ = λ _ → T₀

--------------------------------------------------------------------------------
-- §5. H₀ ≅ GF(3)：fwd = aug（elim 构造，coherence = r 本身）+ 群律转移
--------------------------------------------------------------------------------

f₀ : H₀ → Trit
f₀ = elim (λ _ → isSetTrit) aug (λ a b r → r)



-- 注入性：f₀ [x] ≡ f₀ [y] 的判据即 R₀ x y（eq/ 直接构造——无需 effective）
h₀-inj : ∀ x y → f₀ [ x ] ≡ f₀ [ y ] → [ x ] ≡ [ y ]
h₀-inj x y h = eq/ {R = R₀} x y h

-- 满射性：任意 c 由 [h₀-bwd c] 承载
h₀-surj : ∀ c → f₀ [ h₀-bwd c ] ≡ c
h₀-surj c = h₀-fwd-bwd c

-- 群律迁移（transport-of-structure）：+H₀ 经同构 f₀ 拉回 Trit 群结构
--   （沿双射迁结构——无需 aug-linear AC 链；良定义性由 f₀ 常值性直给）
+H₀ : H₀ → H₀ → H₀
+H₀ q₁ q₂ = [ h₀-bwd (f₀ q₁ ⊕ f₀ q₂) ]

-- 良定义性：f₀ (+H₀ [x] [y]) ≡ f₀ x ⊕ f₀ y（h₀-fwd-bwd）——对代表元选取不敏感
+H₀-respect : ∀ x x' y y' → f₀ [ x ] ≡ f₀ [ x' ] → f₀ [ y ] ≡ f₀ [ y' ] →
              f₀ (+H₀ [ x ] [ y ]) ≡ f₀ (+H₀ [ x' ] [ y' ])
+H₀-respect x x' y y' hx hy =
  h₀-fwd-bwd (f₀ [ x ] ⊕ f₀ [ y ])
  ∙ (cong₂ _⊕_ hx hy)
  ∙ sym (h₀-fwd-bwd (f₀ [ x' ] ⊕ f₀ [ y' ]))

-- 交换律的 f₀ 层形态（⊕-comm 直给；+H₀-comm 经 h₀-injQ 迁移——elimProp 版下一原子件）
-- cubical ≡ 版交换律（9-case——模块级 ≡ 为 cubical Path，⊕-comm 是 PropEq 不混用）
⊕-comm-cub : ∀ a b → a ⊕ b ≡ b ⊕ a
⊕-comm-cub T₀ T₀ = refl
⊕-comm-cub T₀ T₁ = refl
⊕-comm-cub T₀ T₂ = refl
⊕-comm-cub T₁ T₀ = refl
⊕-comm-cub T₁ T₁ = refl
⊕-comm-cub T₁ T₂ = refl
⊕-comm-cub T₂ T₀ = refl
⊕-comm-cub T₂ T₁ = refl
⊕-comm-cub T₂ T₂ = refl

-- 商层单射性（elimProp2——isPropΠ + squash/ 定义性组合）
h₀-injQ : ∀ q₁ q₂ → f₀ q₁ ≡ f₀ q₂ → q₁ ≡ q₂
h₀-injQ = elimProp2 prop (λ x y h → eq/ {R = R₀} x y h)
  where
    prop : ∀ q₁ q₂ → isProp ((f₀ q₁ ≡ f₀ q₂) → q₁ ≡ q₂)
    prop q₁ q₂ = isPropΠ (λ h → squash/ q₁ q₂)

f₀-comm : ∀ q₁ q₂ → f₀ q₁ ⊕ f₀ q₂ ≡ f₀ q₂ ⊕ f₀ q₁
f₀-comm q₁ q₂ = ⊕-comm-cub (f₀ q₁) (f₀ q₂)

-- 单位元：[h₀-bwd T₀]（f₀ 零类）
+H₀-unit : H₀
+H₀-unit = [ h₀-bwd T₀ ]

h₀-unit-f : f₀ +H₀-unit ≡ T₀
h₀-unit-f = refl

-- H₀ 非平凡：T₁ 类与 0 类在 f₀ 下分离
h₀-zero-f : f₀ [ zeroᶠ-C₀ ] ≡ T₀
h₀-zero-f = refl

h₀-T₁-distinct : ¬ (f₀ [ h₀-bwd T₁ ] ≡ f₀ [ zeroᶠ-C₀ ])
h₀-T₁-distinct h = triv (sym (h₀-fwd-bwd T₁) ∙ h ∙ h₀-zero-f)
  where
    triv : T₁ ≡ T₀ → ⊥
    triv p = transport (λ i → is₁ (p i)) tt

--------------------------------------------------------------------------------
-- §6. H₁ = 0：任意循环的类 = [0]（eq/ 直接构造——R₁ 判据即循环假设）
--------------------------------------------------------------------------------

∂₁-zeroᶠ : ∀ i → ∂₁ zeroᶠ-C₁ i ≡ T₀
∂₁-zeroᶠ fzero = refl
∂₁-zeroᶠ (fsuc fzero) = refl
∂₁-zeroᶠ (fsuc (fsuc fzero)) = refl

∂₂-zeroᶠ : ∀ i → ∂₂ zeroᶠ-C₂ i ≡ T₀
∂₂-zeroᶠ fzero = refl
∂₂-zeroᶠ (fsuc fzero) = refl
∂₂-zeroᶠ (fsuc (fsuc fzero)) = refl

h₁-zero-HIT : ∀ (x : C₁) → (∀ i → ∂₁ x i ≡ T₀) → [ x ] ≡ [ zeroᶠ-C₁ ]
h₁-zero-HIT x hx = eq/ {R = R₁} x zeroᶠ-C₁
  (λ i → hx i ∙ sym (∂₁-zeroᶠ i))

--------------------------------------------------------------------------------
-- §7. H₂ = 0：循环类归零（生成元零判据）
--------------------------------------------------------------------------------

h₂-zero-HIT : ∀ (c : C₂) → (∂₂ c fzero ≡ T₀) → [ c ] ≡ [ zeroᶠ-C₂ ]
h₂-zero-HIT c h = eq/ {R = R₂} c zeroᶠ-C₂ helper
  where
    -- ∂₂ 表：三分量同为 c fzero ⟹ 逐分支归 h（c fzero ≡ T₀）
    helper : ∀ i → ∂₂ c i ≡ ∂₂ zeroᶠ-C₂ i
    helper fzero = h
    helper (fsuc fzero) = h
    helper (fsuc (fsuc fzero)) = h


--------------------------------------------------------------------------------
-- §7. +H₀ 群律完成件：结合律 + 单位元（f₀ 迁移模式——同 +H₀-comm）
--------------------------------------------------------------------------------

-- 辅助：f₀ (+H₀ q₁ q₂) = f₀ q₁ ⊕ f₀ q₂（h₀-fwd-bwd 一步）
h₀-fwd+H₀ : ∀ q₁ q₂ → f₀ (+H₀ q₁ q₂) ≡ f₀ q₁ ⊕ f₀ q₂
h₀-fwd+H₀ q₁ q₂ = h₀-fwd-bwd (f₀ q₁ ⊕ f₀ q₂)

-- cubical 版结合/单位（模块级 ≡ 为 cubical Path——本地 27/3-case）
⊕-assoc-cub : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc-cub T₀ T₀ T₀ = refl
⊕-assoc-cub T₀ T₀ T₁ = refl
⊕-assoc-cub T₀ T₀ T₂ = refl
⊕-assoc-cub T₀ T₁ T₀ = refl
⊕-assoc-cub T₀ T₁ T₁ = refl
⊕-assoc-cub T₀ T₁ T₂ = refl
⊕-assoc-cub T₀ T₂ T₀ = refl
⊕-assoc-cub T₀ T₂ T₁ = refl
⊕-assoc-cub T₀ T₂ T₂ = refl
⊕-assoc-cub T₁ T₀ T₀ = refl
⊕-assoc-cub T₁ T₀ T₁ = refl
⊕-assoc-cub T₁ T₀ T₂ = refl
⊕-assoc-cub T₁ T₁ T₀ = refl
⊕-assoc-cub T₁ T₁ T₁ = refl
⊕-assoc-cub T₁ T₁ T₂ = refl
⊕-assoc-cub T₁ T₂ T₀ = refl
⊕-assoc-cub T₁ T₂ T₁ = refl
⊕-assoc-cub T₁ T₂ T₂ = refl
⊕-assoc-cub T₂ T₀ T₀ = refl
⊕-assoc-cub T₂ T₀ T₁ = refl
⊕-assoc-cub T₂ T₀ T₂ = refl
⊕-assoc-cub T₂ T₁ T₀ = refl
⊕-assoc-cub T₂ T₁ T₁ = refl
⊕-assoc-cub T₂ T₁ T₂ = refl
⊕-assoc-cub T₂ T₂ T₀ = refl
⊕-assoc-cub T₂ T₂ T₁ = refl
⊕-assoc-cub T₂ T₂ T₂ = refl

⊕-identityʳ-cub : ∀ a → a ⊕ T₀ ≡ a
⊕-identityʳ-cub T₀ = refl
⊕-identityʳ-cub T₁ = refl
⊕-identityʳ-cub T₂ = refl

-- ⊕-identityˡ cubical 版
⊕-identityˡ-cub : ∀ a → T₀ ⊕ a ≡ a
⊕-identityˡ-cub T₀ = refl
⊕-identityˡ-cub T₁ = refl
⊕-identityˡ-cub T₂ = refl

-- f₀ 层结合律（类型锚定终态 f₀ (+H₀ q₁ (+H₀ q₂ q₃))）
f₀-assoc : ∀ q₁ q₂ q₃ →
           f₀ (+H₀ (+H₀ q₁ q₂) q₃) ≡ f₀ (+H₀ q₁ (+H₀ q₂ q₃))
f₀-assoc q₁ q₂ q₃ =
  h₀-fwd+H₀ (+H₀ q₁ q₂) q₃
  ∙ cong (_⊕ f₀ q₃) (h₀-fwd+H₀ q₁ q₂)
  ∙ ⊕-assoc-cub (f₀ q₁) (f₀ q₂) (f₀ q₃)
  ∙ cong (f₀ q₁ ⊕_) (sym (h₀-fwd+H₀ q₂ q₃))
  ∙ sym (h₀-fwd+H₀ q₁ (+H₀ q₂ q₃))

-- 结合律（h₀-injQ 迁移）
+H₀-assoc : ∀ q₁ q₂ q₃ →
            +H₀ (+H₀ q₁ q₂) q₃ ≡ +H₀ q₁ (+H₀ q₂ q₃)
+H₀-assoc q₁ q₂ q₃ =
  h₀-injQ (+H₀ (+H₀ q₁ q₂) q₃) (+H₀ q₁ (+H₀ q₂ q₃))
         (f₀-assoc q₁ q₂ q₃)

-- 单位元律（左/右）
+H₀-unit-l : ∀ q → +H₀ +H₀-unit q ≡ q
+H₀-unit-l q =
  h₀-injQ (+H₀ +H₀-unit q) q
         (h₀-fwd+H₀ +H₀-unit q ∙ ⊕-identityˡ-cub (f₀ q))

+H₀-unit-r : ∀ q → +H₀ q +H₀-unit ≡ q
+H₀-unit-r q =
  h₀-injQ (+H₀ q +H₀-unit) q
         (h₀-fwd+H₀ q +H₀-unit ∙ ⊕-identityʳ-cub (f₀ q))
