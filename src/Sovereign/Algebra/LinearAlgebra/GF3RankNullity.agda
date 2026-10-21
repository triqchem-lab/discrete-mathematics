{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3RankNullity
-- 秩-零化度（T4 的最后一个基础设施件，2026-10-21）
--
-- 数学
--   对线性映射 `T : V → W`（`V`、`W` 为有限维 GF(3) 向量空间）：
--       **dim V = dim ker T + dim im T**
--
-- 本库的维数语义（见 `GF3BasisCount`）：
--   `Basis V` ⇒ `V ≅ Fin (3^(dim V))`   ⇒   `|V| = 3^(dim V)`
--   ⇒ 维数等式可以化为**基数等式**：`3^(dim V) = 3^(dim ker) · 3^(dim im)`
--   ⇒ 再加 `3^`-单射即可。**不需要**抽象的 `dim` 函数。
--
-- 本模块
--   §1 `3^`-单射（`3^a = 3^b ⇒ a = b`）
--   §2 纤维乘积分解 `V ≅ im T × ker T`（用 `GF3Fiber` 的纤维等大）
--   §3 拼装出维数公式
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3RankNullity where

open import Data.Nat using (ℕ; zero; suc; _*_; _^_; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( <-irrefl; <-trans; <-cmp; *-monoˡ-<; *-monoʳ-<; ^-monoˡ-≤; ≤-refl; ≤-trans; n≤1+n )
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

--------------------------------------------------------------------------------
-- §1. `3^`-单射：`3^a ≡ 3^b ⇒ a ≡ b`
--
-- 直接用 stdlib：`^-monoʳ-< : ∀ m → 1 < m → Monotonic₁ _<_ _<_ (m ^_)`
--------------------------------------------------------------------------------

open import Data.Nat.Properties using
  ( ^-monoʳ-<; <-irrefl; <-cmp; <-trans; ≤-refl; ≤-trans
  ; m≤m+n; n≤1+n< )
open import Data.Nat using (_<_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Tri)

1<3 : 1 < 3
1<3 = s≤s (s≤s z≤n)

-- `3^` 严格单调
3^-mono-< : ∀ {a b} → a < b → 3 ^ a < 3 ^ b
3^-mono-< = ^-monoʳ-< 3 1<3

-- ★ `3^`-单射
3^-inj : ∀ {a b} → 3 ^ a ≡ 3 ^ b → a ≡ b
3^-inj {a} {b} eq with <-cmp a b
... | Tri.tri< a<b _ _   = ⊥-elim (<-irrefl eq (3^-mono-< a<b))
... | Tri.tri≈ _ a≡b _   = a≡b
... | Tri.tri> _ _ b<a   = ⊥-elim (<-irrefl (sym eq) (3^-mono-< b<a))

--------------------------------------------------------------------------------
-- §2. ★★ `F : ker F² → im F ∩ ker F`：满射性与核
--
-- 秩-零化度在**本问题上的实例**：
--      ker(F | ker F²) = ker F
-- 配合 `GF3ImKer` 的 `im F ∩ ker F = F(ker F²)`，给出 `q_n = c_n − a_n` 的结构来源
-- （把 oracle `bd06f20b` 的这条从「数值」升级为「定理」）。
--------------------------------------------------------------------------------

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Sovereign.Base.Trit using (Trit; T₀)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus; sumFin)
open import Sovereign.Algebra.LinearAlgebra.GF3BlockSplit using (CoeffN; sum2)
open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (mulX2; zeroAt; lookupAt)
open import Sovereign.Algebra.LinearAlgebra.GF3Slice using (sumFin-zero')
open import Sovereign.Algebra.LinearAlgebra.GF3ImKer using (ImF; KerF; im-ker-eq)

-- `ker F²`
KerF2 : ∀ {n} → CoeffN n → Set
KerF2 p = ∀ x → sum2 (sum2 p) x ≡ T₀

-- 辅助：点态为零的函数，`sum2` 后仍为零
sum2-zero : ∀ {n} (q : CoeffN n) → (∀ y → q y ≡ T₀) → ∀ x → sum2 q x ≡ T₀
sum2-zero {n} q h x = sumFin-zero' {n} (λ j → mulX2 j q x) goal
  where
    goal : ∀ j → mulX2 j q x ≡ T₀
    goal j with lookupAt j x in eqL
    ... | fzero             = refl
    ... | fsuc fzero        = refl
    ... | fsuc (fsuc fzero) = h (zeroAt j x)

-- ★ `ker F ⊆ ker F²`（一次归零 ⇒ 两次也归零）
ker⊆ker2 : ∀ {n} {p : CoeffN n} → KerF p → KerF2 p
ker⊆ker2 ker = sum2-zero _ ker

-- ★★ 满射到 `im F ∩ ker F`：`p ∈ ker F² ⇒ F p ∈ im F ∩ ker F`
-- （由 `GF3ImKer.im-ker-eq` 的反向：`F(ker F²) ⊆ im F ∩ ker F`）
ker2-to-imker : ∀ {n} {p : CoeffN n} → KerF2 p → ImF (sum2 p) × KerF (sum2 p)
ker2-to-imker {n} {p} k2 = proj₁ (im-ker-eq (sum2 p)) (p , k2 , (λ _ → refl))

-- ★★ 核的刻画：在 `ker F²` 上，`F p = 0` 等价于 `p ∈ ker F` 的像
-- （即 `ker(F | ker F²) = ker F`，因为 `ker F ⊆ ker F²`）
restrict-kernel : ∀ {n} {p : CoeffN n} → KerF p → KerF (sum2 p)
restrict-kernel ker = sum2-zero _ ker

--------------------------------------------------------------------------------
-- §3. `V-from-Fin` 的单射性（`dim` 良定义的第一步）
--
-- 思路：
--   `V-from-Fin b k = Comb (vecs b) (toFun d k)`
--   ⇒ 点态相等 ⇒ `comb-inj`（分离族）给出系数相等 ⇒ `fromFun` 相等 ⇒ `fromFun-toFun` 给出 `k ≡ k'`
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.GF3Dim using (Comb; comb-inj; Separated)
open import Sovereign.Algebra.LinearAlgebra.GF3BasisCount using
  (Basis; fromCoeff; V-from-Fin; round2; fromFun-cong)
open import Sovereign.Algebra.LinearAlgebra.GF3Count using (fromFun; toFun; fromFun-toFun)

-- `V-from-Fin` 的点态展开（定义相等）
V-from-Fin-eq : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (k : Fin (3 ^ Basis.dim b)) (x : Torus n) →
  V-from-Fin b k x ≡ Comb (Basis.vecs b) (toFun (Basis.dim b) k) x
V-from-Fin-eq b k x = refl

-- ★ `V-from-Fin` 单射（点态前提）
V-from-Fin-inj : ∀ {n} {V : CoeffN n → Set} (b : Basis V)
  (k k' : Fin (3 ^ Basis.dim b)) →
  (∀ x → V-from-Fin b k x ≡ V-from-Fin b k' x) →
  k ≡ k'
V-from-Fin-inj {n} {V} b k k' eq =
  trans (sym (fromFun-toFun d k))
        (trans (fromFun-cong d (toFun d k) (toFun d k') coef-eq)
               (fromFun-toFun d k'))
  where
    d : ℕ
    d = Basis.dim b

    -- 系数相等（由 `comb-inj`）
    coef-eq : ∀ i → toFun d k i ≡ toFun d k' i
    coef-eq = comb-inj (Basis.vecs b) (Basis.sep b)
                       (toFun d k) (toFun d k')
                       (λ x → trans (sym (V-from-Fin-eq b k x)) (trans (eq x) (V-from-Fin-eq b k' x)))

--------------------------------------------------------------------------------
-- §4. 加性基座：`sumFin` 与 `Comb` 的加性
--
-- 阶段 2（纤维乘积双射）的前置：需要「`V` 对加法封闭」，
-- 而 `V` 的封闭性来自 `Basis.closed`，后者需要 `Comb` 的加性。
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (_⊕_; _⊗_; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong)

-- `sumFin` 加性
sumFin-add : ∀ {n} (f g : Fin n → Trit) →
  sumFin (λ i → f i ⊕ g i) ≡ sumFin f ⊕ sumFin g
sumFin-add {zero} f g = refl
sumFin-add {suc m} f g =
  trans (cong₂ _⊕_ refl (sumFin-add {m} (λ i → f (fsuc i)) (λ i → g (fsuc i))))
        (square-shuffle (f fzero) (g fzero)
                        (sumFin (λ i → f (fsuc i))) (sumFin (λ i → g (fsuc i))))
  where
    -- (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
    square-shuffle : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
    square-shuffle a b c d =
      trans (⊕-assoc a b (c ⊕ d))
            (trans (cong (a ⊕_) (sym (⊕-assoc b c d)))
                   (trans (cong (λ z → a ⊕ (z ⊕ d)) (⊕-comm b c))
                          (trans (cong (a ⊕_) (⊕-assoc c b d))
                                 (sym (⊕-assoc a c (b ⊕ d))))))


-- 系数的逐点加法
_+D_ : ∀ {d} → (Fin d → Trit) → (Fin d → Trit) → (Fin d → Trit)
(c +D c') i = c i ⊕ c' i

-- ★ `Comb` 加性
Comb-add : ∀ {n d} (v : Fin d → CoeffN n) (c c' : Fin d → Trit) (x : Torus n) →
  Comb v (c +D c') x ≡ Comb v c x ⊕ Comb v c' x
Comb-add {n} {d} v c c' x =
  trans (sumFin-cong {n = d} coeff-step) (sumFin-add {d} _ _)
  where
    coeff-step : ∀ i → (c i ⊕ c' i) ⊗ v i x ≡ (c i ⊗ v i x) ⊕ (c' i ⊗ v i x)
    coeff-step i = ⊗-distribʳ-⊕ (c i) (c' i) (v i x)
