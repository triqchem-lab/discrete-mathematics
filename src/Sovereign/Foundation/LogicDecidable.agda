{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.LogicDecidable
-- 可判定命题的组合器族——Dec P =「P 或 ¬P 的可计算证据」的结构性组合
--
-- 数学背景：构造性逻辑中，可判定性不是元语言假设而是数据——Dec P 携带
-- 判定结果与相应证据。组合器族（×-dec/⊎-dec/¬-dec/mapDec）把原子判定
-- 装配为复合命题判定，对应 Coq 的 Decidable 族与 Agda stdlib
-- Relation.Nullary 家族；stdlib 为信任基座直用，本模块补**映射表层**。
--
-- 核心原则：
-- 1. stdlib 直用（Dec/yes/no/¬_ 为信任基座）；本模块只加组合器与核对层
-- 2. 0 postulate / 0 hole——组合器全为构造性定义
-- 3. 命名反映数学内容（mapDec/×-dec/⊎-dec/¬-dec——不缩写）
-- 4. 核对层用数据形 refl 与 Bool 通道（免函数外延）
--
-- 包含：mapDec · ×-dec · ⊎-dec · ¬-dec · isYes · dec⊤/dec⊥ · 核对层

module Sovereign.Foundation.LogicDecidable where

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- ③ 基础件层：组合器族
--------------------------------------------------------------------------------

-- 同构于的两个判定互相搬运（逻辑等价下的判定传递）
mapDec : ∀ {P Q : Set} → (P → Q) → (Q → P) → Dec P → Dec Q
mapDec f g (yes p) = yes (f p)
mapDec f g (no ¬p) = no (λ q → ¬p (g q))

-- 合取判定（∧→Dec 映射）：两侧判定合成积判定
×-dec : ∀ {P Q : Set} → Dec P → Dec Q → Dec (P × Q)
×-dec (yes p) (yes q) = yes (p , q)
×-dec (yes p) (no ¬q) = no (λ { (_ , q′) → ¬q q′ })
×-dec (no ¬p) _       = no (λ { (p′ , _) → ¬p p′ })

-- 析取判定（∨→Dec 映射）
⊎-dec : ∀ {P Q : Set} → Dec P → Dec Q → Dec (P ⊎ Q)
⊎-dec (yes p) _       = yes (inj₁ p)
⊎-dec (no ¬p) (yes q) = yes (inj₂ q)
⊎-dec (no ¬p) (no ¬q) = no (λ { (inj₁ p) → ¬p p ; (inj₂ q) → ¬q q })

-- 否定判定：¬P 可判定当且仅当 P 可判定（证据互换）
¬-dec : ∀ {P : Set} → Dec P → Dec (¬ P)
¬-dec (yes p)  = no (λ ¬p → ¬p p)
¬-dec (no ¬p)  = yes ¬p

--------------------------------------------------------------------------------
-- ④ 附加件：Bool 投影（判定的计算面）
--------------------------------------------------------------------------------

isYes : ∀ {P : Set} → Dec P → Bool
isYes (yes _) = true
isYes (no _)  = false

-- 两个平凡判定（常真/常假命题的判定本体）
dec⊤ : Dec ⊤
dec⊤ = yes tt

dec⊥ : Dec ⊥
dec⊥ = no (λ ())

--------------------------------------------------------------------------------
-- ⑥ 核对层：数据形 refl 交叉 + Bool 通道
--------------------------------------------------------------------------------

-- 数据形核对（无函数值——defeq 直接收口）
check-× : ×-dec (yes tt) (yes tt) ≡ yes (tt , tt)
check-× = refl

check-⊎₁ : ⊎-dec (yes tt) (no (λ ())) ≡ yes (inj₁ tt)
check-⊎₁ = refl

check-⊎₂ : ⊎-dec (no (λ ())) (yes tt) ≡ yes (inj₂ tt)
check-⊎₂ = refl

-- Bool 通道核对（免函数外延——isYes 抹去证据形）
check-isYes-⊤ : isYes dec⊤ ≡ true
check-isYes-⊤ = refl

check-isYes-⊥ : isYes dec⊥ ≡ false
check-isYes-⊥ = refl

check-neg-⊥ : isYes (¬-dec dec⊥) ≡ true
check-neg-⊥ = refl

check-×-mixed : isYes (×-dec dec⊤ dec⊥) ≡ false
check-×-mixed = refl
