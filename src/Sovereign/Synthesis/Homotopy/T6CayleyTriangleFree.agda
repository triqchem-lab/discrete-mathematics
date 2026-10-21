{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyTriangleFree
--
-- **对所有 `n`：`Tⁿ = (Z/3)ⁿ` 的 Cayley 图无有向三角形**（覆盖裁决里的 `T⁶`，n = 6）
--
-- ## 对上一批的推广
--
-- `T6CayleyNoCollapse` 证的是 `T6CayleyVec 1`（**n = 1**）无三角形。
-- 本模块在裁决的**原始载体** `T6Vert n = Fin n → Fin 3` 上证**任意 n** ✓
--
-- ## 论证（四情形）
--
-- 「三角形」= `x →j y →k z` 且 `x →l z`，即
-- `stepGen k (stepGen j x) ≡ stepGen l x`。分四种情形取矛盾：
--
-- | 情形 | 取的坐标 | 矛盾 |
-- |---|---|---|
-- | `k ≢ j`、`l ≢ j` | `j` | `succF3 (x j) ≡ x j` |
-- | `k ≡ j`、`l ≡ j` | `j` | `succF3²(x j) ≡ succF3 (x j)` |
-- | `k ≢ j`、`l ≡ j` | `k` | `succF3 (x k) ≡ x k` |
-- | `k ≡ j`、`l ≢ j` | `j` | `succF3²(x j) ≡ x j` |
--
-- 每个情形都只用到「加生成元在某坐标上是否推进」这一局部信息 ⇒ **不需要 funext** ✓
--
-- ## 推论
--
-- `NoCollapse (T6Cayley n)`：该图上 A-同伦退化为命题相等
-- ⇒ 走层不塌缩（对 `T⁶` 亦然）⇒ 裁决 2 第 3 步的 `π₁ᵈ ≅ C₃` 在任意 n 都不成立。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Pi1dCardinality` 的一般图判据（裁决 2 步 4），不重证

module Sovereign.Synthesis.Homotopy.T6CayleyTriangleFree where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyGraph
  using (T6Vert; succF3; stepGen; T6Cayley)
open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (succF3≢id)
open import Sovereign.Synthesis.Homotopy.Pi1dCardinality
  using (TriangleFree; NoCollapse; no-collapse-iff-triangle-free)

--------------------------------------------------------------------------------
-- §1. 局部工具
--------------------------------------------------------------------------------

succF3²≢id : ∀ (a : Fin 3) → succF3 (succF3 a) ≡ a → ⊥
succF3²≢id Fin.zero                     ()
succF3²≢id (Fin.suc Fin.zero)           ()
succF3²≢id (Fin.suc (Fin.suc Fin.zero)) ()

succF3²≢s : ∀ (a : Fin 3) → succF3 (succF3 a) ≡ succF3 a → ⊥
succF3²≢s Fin.zero                     ()
succF3²≢s (Fin.suc Fin.zero)           ()
succF3²≢s (Fin.suc (Fin.suc Fin.zero)) ()

--------------------------------------------------------------------------------
-- §2. 加生成元的展开律（双向）
--------------------------------------------------------------------------------

stepGen-yes : ∀ {n : ℕ} (j : Fin n) (x : T6Vert n) (i : Fin n)
            → i ≡ j → stepGen j x i ≡ succF3 (x i)
stepGen-yes j x i p with i Fin.≟ j
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

stepGen-no : ∀ {n : ℕ} (j : Fin n) (x : T6Vert n) (i : Fin n)
           → i ≢ j → stepGen j x i ≡ x i
stepGen-no j x i ¬p with i Fin.≟ j
... | yes p = ⊥-elim (¬p p)
... | no  _ = refl

--------------------------------------------------------------------------------
-- §3. ★ 四情形：`stepGen k ∘ stepGen j` 与 `stepGen l` 不可能相等
--------------------------------------------------------------------------------

stepGen-triangle : ∀ {n : ℕ} (j k l : Fin n) (x : T6Vert n)
                 → stepGen k (stepGen j x) ≢ stepGen l x
stepGen-triangle j k l x e with k Fin.≟ j | l Fin.≟ j

-- 情形 1：都不在 j 上推进 ⇒ 取坐标 j
... | no ¬kj | no ¬lj =
      succF3≢id (x j)
        (trans (sym (stepGen-yes j x j refl))
        (trans (sym (stepGen-no k (stepGen j x) j (λ p → ¬kj (sym p))))
        (trans (cong (λ f → f j) e)
               (stepGen-no l x j (λ p → ¬lj (sym p))))))

-- 情形 2：都在 j 上推进 ⇒ 取坐标 j（+2 对 +1）
... | yes kj | yes lj =
      succF3²≢s (x j)
        (trans (cong succF3 (sym (stepGen-yes j x j refl)))
        (trans (sym (stepGen-yes k (stepGen j x) j (sym kj)))
        (trans (cong (λ f → f j) e)
               (stepGen-yes l x j (sym lj)))))

-- 情形 3：k 不推进、l 在 j 上推进 ⇒ 取坐标 k
... | no ¬kj | yes lj =
      succF3≢id (x k)
        (trans (cong succF3 (sym (stepGen-no j x k ¬kj)))
        (trans (sym (stepGen-yes k (stepGen j x) k refl))
        (trans (cong (λ f → f k) e)
               (stepGen-no l x k (λ p → ¬kj (trans p lj))))))

-- 情形 4：k 在 j 上推进、l 不推进 ⇒ 取坐标 j（+2 对 +0）
... | yes kj | no ¬lj =
      succF3²≢id (x j)
        (trans (cong succF3 (sym (stepGen-yes j x j refl)))
        (trans (sym (stepGen-yes k (stepGen j x) j (sym kj)))
        (trans (cong (λ f → f j) e)
               (stepGen-no l x j (λ p → ¬lj (sym p))))))

--------------------------------------------------------------------------------
-- §4. ★★ 主定理：任意 n 的 Cayley 图无有向三角形
--------------------------------------------------------------------------------

tfN : ∀ (n : ℕ) → TriangleFree (T6Cayley n)
tfN n {x} (j , e1) (k , e2) (l , e3) =
  stepGen-triangle j k l x
    (trans (cong (stepGen k) (sym e1)) (trans (sym e2) e3))

--------------------------------------------------------------------------------
-- §5. 推论：A-同伦退化为命题相等（走层不塌缩）
--------------------------------------------------------------------------------

no-collapse-N : ∀ (n : ℕ) → NoCollapse (T6Cayley n)
no-collapse-N n =
  proj₂ (no-collapse-iff-triangle-free {G = T6Cayley n}) (tfN n)
