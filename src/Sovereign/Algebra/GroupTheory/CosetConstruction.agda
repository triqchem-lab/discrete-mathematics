{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.CosetConstruction
--
-- 陪集映射的**自动构造**（B 档「自动构造」的第一块）。
--
-- 数学背景：
--   给定有限群 G : FinGroup n 与子群 H : Subgroup G k，定义等价关系
--       x ~ y  ⟺  x⁻¹ ⊙ y ∈ H
--   陪集映射 q : Fin n → Fin n 取「与 x 等价的最小元素」（searchFin 枚举）。
--
-- 核心原则：
--   1. **用 searchFin 枚举**而非手工构造（原料：Data.Fin._≟_ + searchFin）
--   2. 子群成员关系 mem 可判定（由 hAt 的枚举 + Fin._≟_）
--   3. **无 funExt**：全部结论写成逐点/等式形式
--   4. 0 postulate / 0 hole
--
-- 包含：
--   §1 mem-dec
--   §2 isEq / isEq-dec / isEq-refl / isEq-sym / isEq-trans（等价关系）
--   §3 firstIn（结构性最小值搜索）+ q-raw / q-raw-eq / q-raw-min
--   §4 q-raw-eq-of-eq + q-iff（同代表元 ⟺ 等价）
--
-- 关键路线（2026-09-10 闭合）：**不用 searchFin 的返回结构证最小性**。
--   searchMin 的两个「不可能分支」在 toℕ 不归约的空目标上卡死
--   （prover_limits: agda-empty-goal-ton-stuck）；改为 firstIn 对**界**结构递归，
--   从 0 起逐点判定、由「已知见证仍在界内」保证终止，最小性由归纳直接得到。

module Sovereign.Algebra.GroupTheory.CosetConstruction where

open import Data.Nat using (ℕ; _<_; _≤_; z≤n; s≤s; suc; zero)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; toℕ-injective; toℕ<n; toℕ-fromℕ<)
open import Data.Nat.Properties using (n<1+n; <-trans; <-irrefl; ≤-refl; ≤-trans; ≤-antisym; m≤n⇒m≤1+n; ≤-total; _<?_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; module ≡-Reasoning)
open import Function.Bundles using (_⇔_; mk⇔)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation.Core using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup; Subgroup)
open import Sovereign.Algebra.Holographic.4320DClosure using (searchFin)

--------------------------------------------------------------------------------
-- §1. 子群成员关系可判定
--------------------------------------------------------------------------------

mem-dec : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) → (x : Fin n) → Dec (Subgroup.mem H x)
mem-dec G H x = searchFin (λ t → Subgroup.hAt H t ≡ x) (λ t → Subgroup.hAt H t ≟ x)

--------------------------------------------------------------------------------
-- §2. 等价关系 x ~ y ⟺ x⁻¹ ⊙ y ∈ H
--------------------------------------------------------------------------------

isEq : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) → Fin n → Fin n → Set
isEq G H x y = Subgroup.mem H (FinGroup._⊙_ G (FinGroup.inv G x) y)

isEq-dec : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) → (x y : Fin n) → Dec (isEq G H x y)
isEq-dec G H x y = mem-dec G H (FinGroup._⊙_ G (FinGroup.inv G x) y)

isEq-refl : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n) → isEq G H x x
isEq-refl G H x = subst (Subgroup.mem H) (sym (FinGroup.inverseˡ G x)) (Subgroup.mem-ε H)

-- 对称性：x ~ y ⇒ y ~ x，因 y⁻¹ ⊙ x = (x⁻¹ ⊙ y)⁻¹ ∈ H
isEq-sym : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) {x y : Fin n}
         → isEq G H x y → isEq G H y x
isEq-sym G H {x} {y} p =
  subst (Subgroup.mem H) step (Subgroup.mem-inv H p)
  where
    open FinGroup G
    step : inv (inv x ⊙ y) ≡ inv y ⊙ x
    step = trans (inv-⊙ (inv x) y) (cong (inv y ⊙_) (inv-inv x))

-- 传递性：x ~ y ⇒ y ~ z ⇒ x ~ z，因 x⁻¹ ⊙ z = (x⁻¹ ⊙ y) ⊙ (y⁻¹ ⊙ z) ∈ H
isEq-trans : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) {x y z : Fin n}
           → isEq G H x y → isEq G H y z → isEq G H x z
isEq-trans G H {x} {y} {z} p q =
  subst (Subgroup.mem H) step (Subgroup.mem-⊙ H p q)
  where
    open FinGroup G
    open ≡-Reasoning
    step : (inv x ⊙ y) ⊙ (inv y ⊙ z) ≡ inv x ⊙ z
    step = begin
      (inv x ⊙ y) ⊙ (inv y ⊙ z)   ≡⟨ assoc (inv x) y (inv y ⊙ z) ⟩
      inv x ⊙ (y ⊙ (inv y ⊙ z))   ≡⟨ cong (inv x ⊙_) (sym (assoc y (inv y) z)) ⟩
      inv x ⊙ ((y ⊙ inv y) ⊙ z)   ≡⟨ cong (λ w → inv x ⊙ (w ⊙ z)) (inverseʳ y) ⟩
      inv x ⊙ (ε ⊙ z)             ≡⟨ cong (inv x ⊙_) (identityˡ z) ⟩
      inv x ⊙ z                   ∎

--------------------------------------------------------------------------------
-- §3. 最小值搜索（结构性；不用 searchFin 的返回结构）
--
-- 根因（prover_limits: agda-empty-goal-ton-stuck）：用 searchFin 的返回结构证最小性时，
-- 「dec fzero 命中却返回 fsuc i」的分支目标是 toℕ (fsuc i) ≤ 0，把 ⊥ 用上去需要
--   subst (λ w → toℕ (fsuc i) ≤ w) (toℕ-fzero' …) p
-- —— toℕ fzero 在 subst 的期望类型里不归约，隐式参数推不出。
--
-- 改法：「界内首个命中」搜索，返回值**区分命中与界内无命中**：
--   命中 ⇒ 不做任何 toℕ 上的 subst；无命中 ⇒ 顶部元素的判定直接给结论。
-- 全部是对界 bound 的结构归纳，既不需要见证输入，也不需要良基递归。
--------------------------------------------------------------------------------

-- m ≤ suc n 的二分
≤-suc-split : ∀ {m n : ℕ} → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
≤-suc-split {zero}  z≤n       = inj₁ z≤n
≤-suc-split {suc m} {zero}  (s≤s z≤n) = inj₂ refl
≤-suc-split {suc m} {suc n} (s≤s m≤sn) with ≤-suc-split {m} {n} m≤sn
... | inj₁ m≤n  = inj₁ (s≤s m≤n)
... | inj₂ refl = inj₂ refl

-- 界为 0 时唯一元素是 0
none-zero : ∀ (P : ℕ → Set) → ¬ P zero → ∀ m → m ≤ zero → ¬ P m
none-zero P ¬p0 zero    z≤n = ¬p0
none-zero P ¬p0 (suc _) ()

-- 命中分支：界内最小 ⇒ 对 suc b 内的元素也最小
lift-first : ∀ (P : ℕ → Set) {k b m : ℕ}
           → k ≤ b → (m ≤ b → P m → k ≤ m) → (m ≤ b) ⊎ (m ≡ suc b) → P m → k ≤ m
lift-first P k≤b h (inj₁ m≤b)  pm = h m≤b pm
lift-first P k≤b h (inj₂ refl) pm = m≤n⇒m≤1+n k≤b

-- 本界顶部命中：对界内任意满足者都 ≤（下方满足者与假设矛盾）
top-min : ∀ (P : ℕ → Set) {b m : ℕ}
        → (m ≤ b → ¬ P m) → (m ≤ b) ⊎ (m ≡ suc b) → P m → suc b ≤ m
top-min P h (inj₁ m≤b)  pm = ⊥-elim (h m≤b pm)
top-min P h (inj₂ refl) pm = ≤-refl

-- 全界无命中
no-hit : ∀ (P : ℕ → Set) {b m : ℕ}
       → (m ≤ b → ¬ P m) → ¬ P (suc b) → (m ≤ b) ⊎ (m ≡ suc b) → P m → ⊥
no-hit P h ¬psb (inj₁ m≤b)  pm = h m≤b pm
no-hit P h ¬psb (inj₂ refl) pm = ¬psb pm

-- 下半界无命中时，判定本界顶部
firstIn-tail : ∀ (P : ℕ → Set) (b : ℕ) → (∀ m → m ≤ b → ¬ P m) → Dec (P (suc b))
             → Σ ℕ (λ k → k ≤ suc b × P k × (∀ m → m ≤ suc b → P m → k ≤ m))
             ⊎ (∀ m → m ≤ suc b → ¬ P m)
firstIn-tail P b noneb (yes psb) =
  inj₁ (suc b , (≤-refl , (psb , λ m m≤sb pm → top-min P (noneb m) (≤-suc-split m≤sb) pm)))
firstIn-tail P b noneb (no ¬psb) =
  inj₂ (λ m m≤sb pm → no-hit P (noneb m) ¬psb (≤-suc-split m≤sb) pm)

-- [0, bound] 内的首个命中
firstIn : (P : ℕ → Set) (dec : ∀ m → Dec (P m)) (bound : ℕ)
        → Σ ℕ (λ k → k ≤ bound × P k × (∀ m → m ≤ bound → P m → k ≤ m))
        ⊎ (∀ m → m ≤ bound → ¬ P m)
firstIn P dec zero with dec zero
... | yes p0 = inj₁ (zero , (z≤n , (p0 , λ m _ _ → z≤n)))
... | no ¬p0 = inj₂ (none-zero P ¬p0)
firstIn P dec (suc b) with firstIn P dec b
... | inj₁ (k , (k≤b , (pk , minb))) =
      inj₁ (k , (m≤n⇒m≤1+n k≤b ,
                 (pk , λ m m≤sb pm → lift-first P k≤b (minb m) (≤-suc-split m≤sb) pm)))
... | inj₂ noneb = firstIn-tail P b noneb (dec (suc b))

--------------------------------------------------------------------------------
-- §3b. Fin n 上的最小等价元
--------------------------------------------------------------------------------

-- ℕ 索引 i（< n）对应的群元素与 x 等价
memIdx : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n) → ℕ → Set
memIdx {n} G H x i = Σ (i < n) (λ i<n → isEq G H (fromℕ< {i} {n} i<n) x)

memIdx-dec : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n) (i : ℕ)
           → Dec (memIdx G H x i)
memIdx-dec {n} G H x i with i <? n
... | yes i<n = fromEq (isEq-dec G H (fromℕ< {i} {n} i<n) x)
  where
    fromEq : Dec (isEq G H (fromℕ< {i} {n} i<n) x) → Dec (memIdx G H x i)
    fromEq (yes p) = yes (i<n , p)
    fromEq (no ¬p) = no (λ (_ , p) → ¬p p)
... | no ¬i<n = no (λ (i<n , _) → ¬i<n i<n)

-- x 自身是界 toℕ x 处的见证
witness-x : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n)
          → memIdx G H x (toℕ x)
witness-x G H x =
  toℕ<n x , subst (λ j → isEq G H j x)
                   (sym (toℕ-injective (toℕ-fromℕ< (toℕ<n x))))
                   (isEq-refl G H x)

-- 等价类的最小元（界内最小 + 界自带的见证）
q-raw-core : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n)
           → Σ ℕ (λ k → k ≤ toℕ x × memIdx G H x k
                        × (∀ m → m ≤ toℕ x → memIdx G H x m → k ≤ m))
q-raw-core G H x with firstIn (memIdx G H x) (memIdx-dec G H x) (toℕ x)
... | inj₁ (k , (k≤t , (pk , min))) = k , (k≤t , (pk , min))
... | inj₂ none = ⊥-elim (none (toℕ x) ≤-refl (witness-x G H x))

q-raw : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) → Fin n → Fin n
q-raw {n} G H x with q-raw-core G H x
... | k , (_ , ((k<n , _) , _)) = fromℕ< {k} {n} k<n

-- q-raw x 与 x 等价
q-raw-eq : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n)
         → isEq G H (q-raw G H x) x
q-raw-eq G H x with q-raw-core G H x
... | k , (_ , ((k<n , p) , _)) = p

-- 全局最小性：界内最小 + 见证恰在界上 ⇒ 对界外的满足者同样 ≤
q-min-global : ∀ (P : ℕ → Set) {k t i : ℕ}
             → k ≤ t → (∀ m → m ≤ t → P m → k ≤ m) → (i ≤ t) ⊎ (t ≤ i) → P i → k ≤ i
q-min-global P {i = i} k≤t min (inj₁ i≤t) qi = min i i≤t qi
q-min-global P k≤t min (inj₂ t≤i) qi = ≤-trans k≤t t≤i

q-raw-min : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x : Fin n) (i : Fin n)
          → isEq G H i x → toℕ (q-raw G H x) ≤ toℕ i
q-raw-min {n} G H x i p with q-raw-core G H x
... | k , (k≤t , (_ , min)) =
      subst (λ z → z ≤ toℕ i)
            (sym (toℕ-fromℕ< {m = k} {n = n} _))
            (q-min-global (memIdx G H x) k≤t min (≤-total (toℕ i) (toℕ x))
                          (toℕ<n i , subst (λ j → isEq G H j x)
                                           (sym (toℕ-injective (toℕ-fromℕ< (toℕ<n i)))) p))

--------------------------------------------------------------------------------
-- §4. 等价元素有相同的最小代表元 ⇒ q-iff
--------------------------------------------------------------------------------

q-raw-eq-of-eq : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) {x y : Fin n}
               → isEq G H x y → q-raw G H x ≡ q-raw G H y
q-raw-eq-of-eq G H {x} {y} p =
  sym (toℕ-injective (≤-antisym
    (q-raw-min G H y (q-raw G H x) (isEq-trans G H (q-raw-eq G H x) p))
    (q-raw-min G H x (q-raw G H y) (isEq-trans G H (q-raw-eq G H y) (isEq-sym G H p)))))

-- 陪集映射的核心性质：代表元相同 ⟺ 等价
q-iff : ∀ {n k} (G : FinGroup n) (H : Subgroup G k) (x y : Fin n)
      → (q-raw G H x ≡ q-raw G H y) ⇔ isEq G H x y
q-iff G H x y = mk⇔ fwd (q-raw-eq-of-eq G H)
  where
    fwd : q-raw G H x ≡ q-raw G H y → isEq G H x y
    fwd e = isEq-trans G H
              (subst (λ z → isEq G H x z) e (isEq-sym G H (q-raw-eq G H x)))
              (q-raw-eq G H y)
