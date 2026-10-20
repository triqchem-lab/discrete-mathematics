{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3BasisCount
-- ★ `V` 有基 ⇒ `V ≅ (Fin d → Trit) ≅ Fin (3^d)`（T4 的秩-零化度计数侧，2026-10-20）
--
-- 数学背景
--   `GF3Dim` 给了「基判据」（张成 + 分离 ⇒ 系数唯一），`GF3Count` 给了
--   base-3 编码 `(Fin d → Trit) ≅ Fin (3^d)`。本模块把两者接起来：
--
--     **Basis V  ⇒  V 与 `Fin (3^(dim V))` 之间存在双射** —— 即 `|V| = 3^(dim V)`。
--
--   这正是「维数 ↔ 基数」的桥，是秩-零化度的**计数侧**。
--
-- 设计
--   本库无 funext ⇒ 双射的往返只在**点态**陈述（`∀ x → ...`）。
--   「基」判据必须含 **闭性**（`∀ c → V (Comb v c)`）：否则反向映射落不进 `V`。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3BasisCount where

open import Data.Nat using (ℕ; zero; suc; _^_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF3BlockSplit using (CoeffN)
open import Sovereign.Algebra.LinearAlgebra.GF3Dim using
  (Comb; Span; Separated; comb-inj)
open import Sovereign.Algebra.LinearAlgebra.GF3Count using
  (fromFun; toFun; fromFun-toFun; toFun-fromFun; hd; tl; cons)
open import Data.Fin using (remQuot; combine)
open import Sovereign.Algebra.LinearAlgebra.GF3Count using (trit→fin3)

--------------------------------------------------------------------------------
-- §0. `fromFun` 的逐点同余（无 funext ⇒ 函数参数改写必须走这条）
--------------------------------------------------------------------------------

fromFun-cong : ∀ d (f g : Fin d → Trit) →
  (∀ i → f i ≡ g i) → fromFun d f ≡ fromFun d g
fromFun-cong zero f g e = refl
fromFun-cong (suc d) f g e =
  cong₂ combine (cong trit→fin3 (e fzero))
                (fromFun-cong d (tl f) (tl g) (λ i → e (fsuc i)))

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §0b. `Comb` 的逐点同余（系数改写）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin-cong)

Comb-cong : ∀ {n d} (v : Fin d → CoeffN n) (c c' : Fin d → Trit) →
  (∀ i → c i ≡ c' i) → ∀ x → Comb v c x ≡ Comb v c' x
Comb-cong v c c' e x =
  sumFin-cong {n = _} (λ i → cong (λ z → z ⊗' v i x) (e i))
  where
    open import Sovereign.Base.Trit using (_⊗_)
    _⊗'_ : Trit → Trit → Trit
    a ⊗' b = a ⊗ b

--------------------------------------------------------------------------------
-- §1. 基（含闭性 —— 这是「V 恰是张成空间」的精确表述）
--------------------------------------------------------------------------------

record Basis {n} (V : CoeffN n → Set) : Set where
  field
    dim    : ℕ
    vecs   : Fin dim → CoeffN n
    closed : ∀ (c : Fin dim → Trit) → V (Comb vecs c)      -- 张成空间 ⊆ V
    covers : ∀ (p : CoeffN n) → V p → Span dim vecs p      -- V ⊆ 张成空间
    sep    : Separated vecs                                 -- 系数唯一

--------------------------------------------------------------------------------
-- §2. V 与系数空间的双射（点态往返）
--------------------------------------------------------------------------------

-- 正向：V 的元素 ↦ 它的系数
toCoeff : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (p : CoeffN n) → V p → (Fin (Basis.dim b) → Trit)
toCoeff b p Vp = proj₁ (Basis.covers b p Vp)

-- 反向：系数 ↦ 组合（落在 V 里，由闭性给出）
fromCoeff : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (c : Fin (Basis.dim b) → Trit) → CoeffN n
fromCoeff b c = Comb (Basis.vecs b) c

fromCoeff-closed : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (c : Fin (Basis.dim b) → Trit) → V (fromCoeff b c)
fromCoeff-closed b = Basis.closed b

-- 往返 ①：`fromCoeff (toCoeff p) ≡ p`（**点态**，因为无 funext）
round1 : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (p : CoeffN n) (Vp : V p) (x : Torus n) →
  fromCoeff b (toCoeff b p Vp) x ≡ p x
round1 b p Vp x = sym (proj₂ (Basis.covers b p Vp) x)

-- 往返 ②：`toCoeff (fromCoeff c) ≡ c`
round2 : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (c : Fin (Basis.dim b) → Trit) (i : Fin (Basis.dim b)) →
  toCoeff b (fromCoeff b c) (fromCoeff-closed b c) i ≡ c i
round2 b c i =
  comb-inj (Basis.vecs b) (Basis.sep b)
           (toCoeff b (fromCoeff b c) (fromCoeff-closed b c)) c
           (λ x → sym (proj₂ (Basis.covers b (fromCoeff b c) (fromCoeff-closed b c)) x))
           i

--------------------------------------------------------------------------------
-- §3. ★★ 主定理：V 与 `Fin (3^dim)` 双射
--------------------------------------------------------------------------------

-- 正向：V 的元素 ↦ 它的 base-3 编码
V-to-Fin : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (p : CoeffN n) → V p → Fin (3 ^ Basis.dim b)
V-to-Fin b p Vp = fromFun (Basis.dim b) (toCoeff b p Vp)

-- 反向：base-3 编码 ↦ 组合
V-from-Fin : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (k : Fin (3 ^ Basis.dim b)) → CoeffN n
V-from-Fin b k = fromCoeff b (toFun (Basis.dim b) k)

-- 反向落在 V 里
V-from-Fin-closed : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (k : Fin (3 ^ Basis.dim b)) → V (V-from-Fin b k)
V-from-Fin-closed b k = fromCoeff-closed b (toFun (Basis.dim b) k)

-- ★ 往返 ③：`V-to-Fin (V-from-Fin k) ≡ k`
V-round-from : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (k : Fin (3 ^ Basis.dim b)) →
  V-to-Fin b (V-from-Fin b k) (V-from-Fin-closed b k) ≡ k
V-round-from b k =
  trans (fromFun-cong (Basis.dim b) _ _
                      (λ i → round2 b (toFun (Basis.dim b) k) i))
        (fromFun-toFun (Basis.dim b) k)

-- ★ 往返 ④：`V-from-Fin (V-to-Fin p) ≡ p`（点态）
V-round-to : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (p : CoeffN n) (Vp : V p) (x : Torus n) →
  V-from-Fin b (V-to-Fin b p Vp) x ≡ p x
V-round-to b p Vp x =
  trans (Comb-cong (Basis.vecs b) _ _
                   (λ i → toFun-fromFun (Basis.dim b) (toCoeff b p Vp) i) x)
        (round1 b p Vp x)
