{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4c —— (d) v2-1：Gskel two-chain 上 AStep 完全为空（分离路线基石）
--
-- 数学背景（v2 路线第 1 段）：
--   Gskel P 的边 = KEdge P x y ⊎ KEdge P y x（两端严格相异——KEdge = Strict = ⊑ × ≢）。
--   AStep 的 slide/expand 生成元需要三点 x→y→z + 捷径 x→z——三条边各自携带 ≢ 分量
--   ⇒ 三点两两相异 ⇒ Fin 2 上不可能（两点集 8 组合）⇒ **AStep 为空**。
--   推论 ah-diag-sk：Gskel 上 AHomotopy = 逐点相等（gen 案消解）——
--   「Gskel π₁ 类 = walk 本身」的分离路线基石。
--
-- 核心原则：
-- 1. 双 ≡ 世界显式钉（KEdge/Strict 的 ≢ 是 Builtin ≡——reflᴱ 模式直消；
--    walk 等式在 Cubical 世界——ah-diag 输出 Cubical ≡）
-- 2. K 禁用：消解全走构造子头冲突型空模式（zero vs suc——#51 安全面）与模式细化
-- 3. 零洞零 postulate
--
-- 包含：edgeGskel-neq（边→端点相异）｜tri-dist-impossible（Fin 2 三点消解）｜
--       AStep-sk-empty（主件）｜ah-diag-sk（AHomotopy = 对角）
module _PPI4c where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; AStep; AHomotopy; slide; expand; refl'; symm; trans'; gen)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)

private
  module DG = DiGraph

--------------------------------------------------------------------------------
-- §1 边端点相异（Gskel 边携带 KEdge 的 ≢ 分量——Builtin 世界直取）
--------------------------------------------------------------------------------

-- Builtin ≡ 对称（顶层命名件——模式 λ 项位局限教训：命名件模式匹配可靠）
symEq : ∀ {a b : Fin 2} → a ≡ᴱ b → b ≡ᴱ a
symEq reflᴱ = reflᴱ

edgeGskel-neq : ∀ (x y : Fin 2) → DG.edge (Gskel two-chain) x y → (x ≡ᴱ y → ⊥)
edgeGskel-neq x y (inj₁ (_ , x≢y)) = x≢y
edgeGskel-neq x y (inj₂ (_ , y≢x)) = λ eq → y≢x (symEq eq)

--------------------------------------------------------------------------------
-- §2 Fin 2 三点两两相异消解（8 组合——构造子头冲突型消解）
--------------------------------------------------------------------------------

tri-dist-impossible : ∀ (x y z : Fin 2)
  → (x ≡ᴱ y → ⊥) → (y ≡ᴱ z → ⊥) → (x ≡ᴱ z → ⊥) → ⊥
tri-dist-impossible fzero fzero z x≢y _ _ = x≢y reflᴱ
tri-dist-impossible fzero (fsuc fzero) fzero _ _ x≢z = x≢z reflᴱ
tri-dist-impossible fzero (fsuc fzero) (fsuc fzero) _ y≢z _ = y≢z reflᴱ
tri-dist-impossible (fsuc fzero) fzero fzero _ y≢z _ = y≢z reflᴱ
tri-dist-impossible (fsuc fzero) fzero (fsuc fzero) _ _ x≢z = x≢z reflᴱ
tri-dist-impossible (fsuc fzero) (fsuc fzero) z x≢y _ _ = x≢y reflᴱ

--------------------------------------------------------------------------------
-- §3 主件：AStep 完全为空（slide/expand 同证——三点消解）
--------------------------------------------------------------------------------

AStep-sk-empty : ∀ {u v} {w1 w2 : Walk (Gskel two-chain) u v}
  → AStep (Gskel two-chain) w1 w2 → ⊥
AStep-sk-empty (slide {x = x} {y} {z} _ _ e1 e2 e3) =
  tri-dist-impossible x y z
    (edgeGskel-neq x y e1) (edgeGskel-neq y z e2) (edgeGskel-neq x z e3)
AStep-sk-empty (expand {x = x} {y} {z} _ _ e1 e2 e3) =
  tri-dist-impossible x y z
    (edgeGskel-neq x y e1) (edgeGskel-neq y z e2) (edgeGskel-neq x z e3)

--------------------------------------------------------------------------------
-- §4 推论：AHomotopy = 对角（gen 案消解 ⇒ 只剩相等闭包）
--------------------------------------------------------------------------------

ah-diag-sk : ∀ {u v} {w w' : Walk (Gskel two-chain) u v}
  → AHomotopy (Gskel two-chain) w w' → w ≡ w'
ah-diag-sk (refl' w) = refl
ah-diag-sk (symm h) = sym (ah-diag-sk h)
ah-diag-sk (trans' h1 h2) = ah-diag-sk h1 ∙ ah-diag-sk h2
ah-diag-sk (gen s) = ⊥-elim (AStep-sk-empty s)
