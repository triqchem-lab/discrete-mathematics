{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.SetoidFreeGroupUniversal
-- **自由群的 setoid 版泛性质**：在 `SetoidGroupData` 上给出 `eval` / `eval-gen` /
-- `eval-++w` / `uniqueness`——与 `_PN15` 的**严格版**（`GroupData`）逐条对应。
--
-- 为什么需要这一件：
--   `_PN15` 的泛性质参数化在严格 `GroupData X` 上。而 SL(2,F₃) 这类载体必然带
--   证明字段（`det M ≡ 1`），严格相等证不出结合律（见 `SL2SetoidGroup` 的取舍说明），
--   只能用 setoid 群。所以泛性质也需要一条 setoid 版，否则桥断在最后一步。
--
-- 数学内容（与严格版完全平行，只是 `≡` 换成载体的 `≈`，
-- `cong` 换成 `⋆-cong`，`refl/sym/trans` 换成 `refl≈/sym≈/trans≈`）：
--   给定 setoid 群 `sg` 与生成元指派 `f : A → Carrier`，
--   存在映射 `eval : Walk B(A) → Carrier`，满足
--     (i)   在生成元上等于 `f`            —— eval-gen
--     (ii)  是乘法同态（至 `≈`）          —— eval-++w
--     (iii) 任何满足同样三条的 `φ` 都与 `eval` 逐点 `≈`  —— uniqueness
--
-- 注：定义域是**原始走**（未做消去商）；因 `eval` 值落在群里，`fwd a` 后接 `bwd a`
--   自然算出 `f a ⋆ ι (f a) ≈ e₀`，无需在语法层先商掉。
--
-- 策略：结构递归 + setoid 替换（每项 ≤3 步）
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.SetoidFreeGroupUniversal where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- 生成元图与走（语法层）
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_)
-- setoid 群 record + B(A) 的边
open import _PN15 using (SetoidGroupData; BEdge; fwd; bwd; BA)

module SetoidUniversal
  {A : Set} (sg : SetoidGroupData) (f : A → SetoidGroupData.Carrier sg) where

  open SetoidGroupData sg

  eval : Walk (BA A) tt tt → Carrier
  eval (nil _)             = e₀
  eval (cons (fwd a) p)    = f a ⋆ eval p
  eval (cons (bwd a) p)    = ι (f a) ⋆ eval p

  -- (i) 在生成元上就是 f
  eval-gen : (a : A) → eval (cons (fwd a) (nil tt)) ≈ f a
  eval-gen a = unitʳ (f a)

  eval-nil : eval (nil tt) ≈ e₀
  eval-nil = refl≈

  -- (ii) 乘法同态（至 ≈）
  eval-++w : (p q : Walk (BA A) tt tt) → eval (p ++w q) ≈ eval p ⋆ eval q
  eval-++w (nil _) q = sym≈ (unitˡ (eval q))
  eval-++w (cons (fwd a) p) q =
    trans≈ (⋆-cong refl≈ (eval-++w p q))
           (sym≈ (assoc (f a) (eval p) (eval q)))
  eval-++w (cons (bwd a) p) q =
    trans≈ (⋆-cong refl≈ (eval-++w p q))
           (sym≈ (assoc (ι (f a)) (eval p) (eval q)))

  -- (iii) 唯一性：任何满足同样三条约束的 φ 与 eval 逐点 ≈
  uniqueness : (φ : Walk (BA A) tt tt → Carrier)
             → φ (nil tt) ≈ e₀
             → (∀ a → φ (cons (fwd a) (nil tt)) ≈ f a)
             → (∀ a → φ (cons (bwd a) (nil tt)) ≈ ι (f a))
             → (∀ p q → φ (p ++w q) ≈ φ p ⋆ φ q)
             → (p : Walk (BA A) tt tt) → φ p ≈ eval p
  uniqueness φ hn hf hb hc (nil _) = hn
  uniqueness φ hn hf hb hc (cons (fwd a) p) =
    trans≈ (hc (cons (fwd a) (nil tt)) p)
      (trans≈ (⋆-cong (hf a) refl≈)
              (⋆-cong refl≈ (uniqueness φ hn hf hb hc p)))
  uniqueness φ hn hf hb hc (cons (bwd a) p) =
    trans≈ (hc (cons (bwd a) (nil tt)) p)
      (trans≈ (⋆-cong (hb a) refl≈)
              (⋆-cong refl≈ (uniqueness φ hn hf hb hc p)))
