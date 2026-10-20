{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Fiber
-- ★ 纤维等大：线性映射的每个纤维都与核等势（T4 的秩-零化度最后一步，2026-10-20）
--
-- 数学背景
--   设 `T : CoeffN n → CoeffN m` 是**线性**映射（点态加法/取负），`x` 是任一元素，
--   `y = T x`。则「纤维」`{z : T z = y}` 与「核」`{k : T k = 0}` 之间存在**双射**：
--
--     正向：`z ↦ z + (−x)`      （因为 `T(z − x) = T z − T x = y − y = 0`）
--     反向：`k ↦ x + k`          （因为 `T(x + k) = T x + 0 = y`）
--
--   ⇒ **所有纤维等大** = 秩-零化度的乘法侧（`|V| = |ker| · |im|`）。
--
-- 设计
--   本库无 funext ⇒ 加法/取负/群律全部**点态**；线性性作为**假设**（`Linear` record）。
--   `CoeffN n` 的加法就是 GF(3) 的逐点 `⊕` ✓。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Fiber where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Sovereign.Base.Trit using
  ( Trit; T₀; _⊕_; negate
  ; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse; negate² )
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF3BlockSplit using (CoeffN)

--------------------------------------------------------------------------------
-- §0. `CoeffN` 的加法群（点态）
--------------------------------------------------------------------------------

_+C_ : ∀ {n} → CoeffN n → CoeffN n → CoeffN n
(p +C q) x = p x ⊕ q x

negC : ∀ {n} → CoeffN n → CoeffN n
negC p x = negate (p x)

zeroC : ∀ {n} → CoeffN n
zeroC _ = T₀

-- 群律（点态陈述，逐点由 Trit 的律给出）
+C-assoc : ∀ {n} (p q r : CoeffN n) (x : Torus n) →
  ((p +C q) +C r) x ≡ (p +C (q +C r)) x
+C-assoc p q r x = ⊕-assoc (p x) (q x) (r x)

+C-identityˡ : ∀ {n} (p : CoeffN n) (x : Torus n) → (zeroC +C p) x ≡ p x
+C-identityˡ p x = ⊕-identityˡ (p x)

+C-inverse : ∀ {n} (p : CoeffN n) (x : Torus n) → (p +C negC p) x ≡ T₀
+C-inverse p x = ⊕-inverse (p x)

+C-comm : ∀ {n} (p q : CoeffN n) (x : Torus n) → (p +C q) x ≡ (q +C p) x
+C-comm p q x = ⊕-comm (p x) (q x)

--------------------------------------------------------------------------------
-- §1. 线性性（假设）
--------------------------------------------------------------------------------

record Linear {n m} (T : CoeffN n → CoeffN m) : Set where
  field
    add : ∀ (p q : CoeffN n) (x : Torus m) → T (p +C q) x ≡ (T p +C T q) x
    neg : ∀ (p : CoeffN n) (x : Torus m) → T (negC p) x ≡ negC (T p) x

--------------------------------------------------------------------------------
-- §2. 纤维与核
--------------------------------------------------------------------------------

Fiber : ∀ {n m} → (T : CoeffN n → CoeffN m) → CoeffN m → CoeffN n → Set
Fiber T y z = ∀ x → T z x ≡ y x

Kernel : ∀ {n m} → (T : CoeffN n → CoeffN m) → CoeffN n → Set
Kernel T k = ∀ x → T k x ≡ T₀

--------------------------------------------------------------------------------
-- §3. ★★ 纤维等大（双射的两方向，全点态）
--------------------------------------------------------------------------------

-- 正向：`z ↦ z + (−x)` 把纤维 `T⁻¹(y)` 送到核
fiber→kernel : ∀ {n m} {T : CoeffN n → CoeffN m} (L : Linear T)
  (x : CoeffN n) (y : CoeffN m) →
  Fiber T y x →                                    -- T x = y
  ∀ (z : CoeffN n) → Fiber T y z → Kernel T (z +C negC x)
fiber→kernel L x y Tx z Tz w =
  trans (Linear.add L z (negC x) w)
        (trans (cong₂ _⊕_ (Tz w) (Linear.neg L x w))
               (trans (cong (λ u → y w ⊕ negate u) (Tx w))
                      (⊕-inverse (y w))))

-- 反向：`k ↦ x + k` 把核送回纤维
kernel→fiber : ∀ {n m} {T : CoeffN n → CoeffN m} (L : Linear T)
  (x : CoeffN n) (y : CoeffN m) →
  Fiber T y x →
  ∀ (k : CoeffN n) → Kernel T k → Fiber T y (x +C k)
kernel→fiber L x y Tx k Tk w =
  trans (Linear.add L x k w)
        (trans (cong₂ _⊕_ (Tx w) (Tk w))
               (⊕-identityʳ (y w)))

--------------------------------------------------------------------------------
-- §4. ★ 两个方向互逆（点态）
--------------------------------------------------------------------------------

-- `(x + (z + (−x)))` 回到 `z`（点态）
kernel-fiber-round : ∀ {n} (x z : CoeffN n) (w : Torus n) →
  (x +C (z +C negC x)) w ≡ z w
kernel-fiber-round x z w =
  trans (sym (⊕-assoc (x w) (z w) (negate (x w))))
        (trans (cong (λ u → u ⊕ negate (x w)) (⊕-comm (x w) (z w)))
               (trans (⊕-assoc (z w) (x w) (negate (x w)))
                      (trans (cong (λ u → z w ⊕ u) (⊕-inverse (x w)))
                             (⊕-identityʳ (z w)))))
