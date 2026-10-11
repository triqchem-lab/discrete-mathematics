{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI4m
-- Gskel 收官：首回返引理 + decomp-unique 一般形 + MonoidIso 第二独立证
--
-- 数学背景：excursion 分解唯一性的收口。_PPI4l §4 立界「首回返引理」为唯一缺件。
--   构造携带路线（#56 路线②）：cutZ 即首回返分割器——e 是 excursion ⟹
--   cutZ (e ++w t) 首段恰为 e（首回返位由 walk 本身决定）。规范形主件
--   canonical : proj₁ (cutZ (concatL es)) ≡ es ⟹ decomp-unique 一行收口
--   （sym canonical ∙ cong ∙ canonical），免双 cons-inj（泵引理为另一路线——_PPI4l §1）。
--   MonoidIso 第二证：to = excursion 计数（length ∘ proj₁ ∘ cutZ），与 gskel-classify
--   （rounds 计数）经 to≡roundsQ 对账锚收口。
--
-- 核心原则：
-- 1. K-free（#56）：同索引 loop 只匹配 cons（三槽位无反射等式）；nil 情形经
--    cons-view / nil-or-ne 一般指标视图转出（Link 先例）；eqV 载荷 Builtin ≡ᴱ 分名。
-- 2. canonical 路线免双 cons-inj；3. 零洞零 postulate；核对层 refl 级。
--
-- 包含：nil-or-ne/cons-view/noX-tail/noX-junction′｜cutZAcc-exc｜cutZ-exc-head
--       ｜AllExc/canonical/decomp-unique｜length-rep/to-w/cutZ-loopK/to-w≡rounds
--       ｜toQ/to≡roundsQ｜gskel-classify-2｜核对层

module _PPI4m where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.HITs.SetQuotients using ([_])
open import Cubical.HITs.SetQuotients.Properties using (elimProp)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import Sovereign.Topology.McCordPi0 using (two-chain)
open import _PPI using (Loop)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; π₁ᵈ-rec)
open import _PPI4 using (Gskel; MonoidIso)
open import _PPI4c using (ah-diag-sk)
open import _PPI4d using (e01; e10; w2)
open import _PPI4g
  using (loopK; rounds; unloop; loopK-+; rounds-loopK; gskel-classify; _+ℕ_)
open import _PPI4j
  using (module Cut; NoX; Nonempty; IsExc;
         ++w-assocᴱ; ++w-nilᴱ; NoX-ext; check-exc-w2a; check-exc-w2b)
open import _PPI4k using (module LoopRes)

private
  module DG = DiGraph

module FirstRet {G : DiGraph} (eqV : (a b : DG.V G) → Dec (a ≡ᴱ b)) where
  open Cut {G = G} eqV
  open LoopRes {G = G} eqV

  -- §1 视图件（一般指标匹配——同索引 nil 墙的出口）

  nil-or-ne : ∀ {u v} (w : Walk G u v) → (w ≡ᴱ nil v) ⊎ Nonempty w
  nil-or-ne (nil v) = inj₁ reflᴱ
  nil-or-ne (cons e w) = inj₂ tt

  cons-view : ∀ {u v} (w : Walk G u v) → Nonempty w
            → Σ (DG.V G) (λ m →
              Σ (DG.edge G u m) (λ e →
              Σ (Walk G m v) (λ p → w ≡ᴱ cons e p)))
  cons-view (nil v) ()
  cons-view (cons {v = m} e p) _ = m , e , p , reflᴱ

  noX-tail : ∀ {x u v w'} (e : DG.edge G u v) (w : Walk G v w')
           → NoX x (cons e w) → NoX x w
  noX-tail e (nil v) n = tt
  noX-tail e (cons e' b) n = proj₂ n

  -- 连接点引理（_PPI4l noX-junction 同义——含 nil 尾 ⊤ 形覆盖）
  noX-junction′ : ∀ {u w} (p₁ : Walk G u a') → Nonempty p₁
                → (q : Walk G a' w) → Nonempty q
                → NoX a' (p₁ ++w q) → ⊥
    where a' = _
  noX-junction′ (nil v) () _ _ _
  noX-junction′ (cons e (nil v)) _ (nil _) () _
  noX-junction′ (cons e (nil v)) _ (cons e' q') _ n = proj₁ n reflᴱ
  noX-junction′ (cons e (cons e' b)) _ q nq n =
    noX-junction′ (cons e' b) tt q nq (proj₂ n)
