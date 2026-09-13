{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.CosetAuto
--
-- 陪集映射的**自动构造**：把 Lagrange 定理的手工假设（q / repr / section / q-coset）
-- 全部从 G、H 自动产出，调用点从「4 个假设」降到「一行」。
--
-- 数学背景：
--   Lagrange 的证明（Lagrange.fiber-count）只需要一个「纤维化」数据：
--       q : Fin n → Fin m（陪集标号）、repr : Fin m → Fin n（代表元）、
--       section : q ∘ repr ≡ id、q-coset : q x ≡ q y ⇔ x⁻¹ ⊙ y ∈ H。
--   这些不是数学输入，而是**构造** —— 本模块用 B.q-iff 的 q-raw（等价类最小元）
--   把它们造出来，m 则是「代表元子类型」的元素个数。
--
-- 核心构件（SubEnum）：把 Fin n 的**可判定子类型**枚举成 Fin m，带 toFin / index
--   双向往返。纯结构归纳（n = 0 / 命中 zero / 未命中 zero），不需要 searchFin、
--   list filter 或良基递归。
--
-- 关键原则：
--   1. m 是**算出来的**（对具体 G、H 归一化到具体数字，见 §5 对抗验证）
--   2. section / q-coset 由 SubEnum 的双往返 + q-iff 直接给出，不重新搜最小性
--   3. 无 funExt：全部结论写成等式形式
--   4. 0 postulate / 0 hole
--
-- 包含：SubEnum / enum / enum-lift / enum-skip / index-cong
--       q-raw-idem / coset-data / lagrange-auto

module Sovereign.Algebra.GroupTheory.CosetAuto where

open import Data.Nat using (ℕ; zero; suc; _≤_; _*_)
open import Data.Nat.Properties using (≤-antisym)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; toℕ-injective; suc-injective)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Function.Definitions using (Injective)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup; Subgroup; lagrange)
open import Sovereign.Algebra.GroupTheory.CosetConstruction using
  (q-raw; q-raw-eq; q-raw-min; isEq; isEq-refl; isEq-sym; isEq-trans; q-iff)

--------------------------------------------------------------------------------
-- §1. 有限子类型枚举（通用构件）
--
-- Fin n 的可判定子类型 P 与某个 Fin m 双射。m / toFin / index 三者一起产出：
--   · toFin : Fin m → Fin n        （枚举代表元）
--   · index : (i : Fin n) → P i → Fin m （元素的子类型内下标）
--   · index-ok / toFin-inj        （双往返）
--------------------------------------------------------------------------------

record SubEnum (n : ℕ) (P : Fin n → Set) : Set where
  field
    size      : ℕ
    toFin     : Fin size → Fin n
    toFin-P   : ∀ r → P (toFin r)
    toFin-inj : Injective _≡_ _≡_ toFin
    index     : (i : Fin n) → P i → Fin size
    index-ok  : ∀ i p → toFin (index i p) ≡ i

-- 命中 fzero：把 fzero 排在首位，其余整体 suc 上移
enum-lift : ∀ {n} {P : Fin (suc n) → Set} → P fzero → SubEnum n (λ i → P (fsuc i))
          → SubEnum (suc n) P
enum-lift {n} {P} p0 e' = record
  { size      = suc (SubEnum.size e')
  ; toFin     = toFin
  ; toFin-P   = toFin-P
  ; toFin-inj = toFin-inj
  ; index     = index
  ; index-ok  = index-ok
  }
  where
    toFin : Fin (suc (SubEnum.size e')) → Fin (suc n)
    toFin fzero    = fzero
    toFin (fsuc r) = fsuc (SubEnum.toFin e' r)

    toFin-P : ∀ r → P (toFin r)
    toFin-P fzero    = p0
    toFin-P (fsuc r) = SubEnum.toFin-P e' r

    toFin-inj : Injective _≡_ _≡_ toFin
    toFin-inj {fzero}  {fzero}  _  = refl
    toFin-inj {fzero}  {fsuc r} ()
    toFin-inj {fsuc r} {fzero}  ()
    toFin-inj {fsuc r} {fsuc s} eq = cong fsuc (SubEnum.toFin-inj e' (suc-injective eq))

    index : (i : Fin (suc n)) → P i → Fin (suc (SubEnum.size e'))
    index fzero    _ = fzero
    index (fsuc i) p = fsuc (SubEnum.index e' i p)

    index-ok : ∀ i p → toFin (index i p) ≡ i
    index-ok fzero    p = refl
    index-ok (fsuc i) p = cong fsuc (SubEnum.index-ok e' i p)

-- 未命中 fzero：整个子枚举 suc 上移，fzero 处空
enum-skip : ∀ {n} {P : Fin (suc n) → Set} → ¬ P fzero → SubEnum n (λ i → P (fsuc i))
          → SubEnum (suc n) P
enum-skip {n} {P} ¬p0 e' = record
  { size      = SubEnum.size e'
  ; toFin     = toFin
  ; toFin-P   = toFin-P
  ; toFin-inj = toFin-inj
  ; index     = index
  ; index-ok  = index-ok
  }
  where
    toFin : Fin (SubEnum.size e') → Fin (suc n)
    toFin r = fsuc (SubEnum.toFin e' r)

    toFin-P : ∀ r → P (toFin r)
    toFin-P r = SubEnum.toFin-P e' r

    toFin-inj : Injective _≡_ _≡_ toFin
    toFin-inj eq = SubEnum.toFin-inj e' (suc-injective eq)

    index : (i : Fin (suc n)) → P i → Fin (SubEnum.size e')
    index fzero    p = ⊥-elim (¬p0 p)
    index (fsuc i) p = SubEnum.index e' i p

    index-ok : ∀ i p → toFin (index i p) ≡ i
    index-ok fzero    p = ⊥-elim (¬p0 p)
    index-ok (fsuc i) p = cong fsuc (SubEnum.index-ok e' i p)

-- 主构件：对 n 的结构归纳
enum : ∀ {n} (P : Fin n → Set) (dec : ∀ i → Dec (P i)) → SubEnum n P
enum {zero}  P dec = record
  { size      = zero
  ; toFin     = λ ()
  ; toFin-P   = λ ()
  ; toFin-inj = λ { {()} }
  ; index     = λ ()
  ; index-ok  = λ ()
  }
enum {suc n} P dec with dec fzero
... | yes p0 = enum-lift p0 (enum (λ i → P (fsuc i)) (λ i → dec (fsuc i)))
... | no ¬p0 = enum-skip ¬p0 (enum (λ i → P (fsuc i)) (λ i → dec (fsuc i)))

-- index 对下标相等做同余（两次 index-ok + toFin-inj）
index-cong : ∀ {n} {P : Fin n → Set} (E : SubEnum n P) {i j : Fin n}
             (p : P i) (q : P j) → i ≡ j
           → SubEnum.index E i p ≡ SubEnum.index E j q
index-cong E {i} {j} p q eq =
  SubEnum.toFin-inj E
    (trans (SubEnum.index-ok E i p) (trans eq (sym (SubEnum.index-ok E j q))))

--------------------------------------------------------------------------------
-- §2. q-raw 的幂等性（代表元判据）
--------------------------------------------------------------------------------

-- q-raw 幂等：等价类的最小元也是自身的类的最小元
q-raw-idem : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n)
           → q-raw G H (q-raw G H x) ≡ q-raw G H x
q-raw-idem G H x = toℕ-injective (≤-antisym lo hi)
  where
    lo : toℕ (q-raw G H (q-raw G H x)) ≤ toℕ (q-raw G H x)
    lo = q-raw-min G H (q-raw G H x) (q-raw G H x) (isEq-refl G H (q-raw G H x))
    hi : toℕ (q-raw G H x) ≤ toℕ (q-raw G H (q-raw G H x))
    hi = q-raw-min G H x (q-raw G H (q-raw G H x))
           (isEq-trans G H (q-raw-eq G H (q-raw G H x)) (q-raw-eq G H x))

--------------------------------------------------------------------------------
-- §3. 自动构造陪集数据
--------------------------------------------------------------------------------

isRep : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) → Fin n → Set
isRep G H i = q-raw G H i ≡ i

isRep-dec : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (i : Fin n)
          → Dec (isRep G H i)
isRep-dec G H i = q-raw G H i ≟ i

-- 自动的纤维化数据：m（陪集个数）、repr、q、section、q-coset
coset-data : ∀ {n k} (G : FinGroup n) (H : Subgroup G k)
           → Σ ℕ (λ m → Σ (Fin m → Fin n) (λ repr →
               Σ (Fin n → Fin m) (λ q →
                 (∀ r → q (repr r) ≡ r)
               × (∀ x y → (q x ≡ q y) ⇔ isEq G H x y))))
coset-data G H = SubEnum.size E , (repr , (q , (section , q-coset)))
  where
    E : SubEnum _ (isRep G H)
    E = enum (isRep G H) (isRep-dec G H)

    repr : Fin (SubEnum.size E) → _
    repr = SubEnum.toFin E

    q : _ → Fin (SubEnum.size E)
    q x = SubEnum.index E (q-raw G H x) (q-raw-idem G H x)

    -- q x 由 q-raw x 决定（证明项不影响）
    q-cong : ∀ x y → q-raw G H x ≡ q-raw G H y → q x ≡ q y
    q-cong x y eq = index-cong E (q-raw-idem G H x) (q-raw-idem G H y) eq

    -- toFin (q x) ≡ q-raw x
    q-ok : ∀ x → repr (q x) ≡ q-raw G H x
    q-ok x = SubEnum.index-ok E (q-raw G H x) (q-raw-idem G H x)

    section : ∀ r → q (repr r) ≡ r
    section r =
      trans (index-cong E (q-raw-idem G H (repr r))
                         (SubEnum.toFin-P E r) (SubEnum.toFin-P E r))
            (SubEnum.toFin-inj E (SubEnum.index-ok E (repr r) (SubEnum.toFin-P E r)))

    to-dir : ∀ x y → q x ≡ q y → isEq G H x y
    to-dir x y eq = Equivalence.to (q-iff G H x y)
                      (trans (sym (q-ok x)) (trans (cong repr eq) (q-ok y)))

    from-dir : ∀ x y → isEq G H x y → q x ≡ q y
    from-dir x y p = q-cong x y (Equivalence.from (q-iff G H x y) p)

    q-coset : ∀ x y → (q x ≡ q y) ⇔ isEq G H x y
    q-coset x y = mk⇔ (to-dir x y) (from-dir x y)

--------------------------------------------------------------------------------
-- §4. 一行 Lagrange
--------------------------------------------------------------------------------

lagrange-auto : ∀ {n k} (G : FinGroup n) (H : Subgroup G k)
              → Σ ℕ (λ m → n ≡ k * m)
lagrange-auto G H with coset-data G H
... | m , (repr , (q , (section , q-coset))) =
      m , lagrange G H q repr section q-coset
