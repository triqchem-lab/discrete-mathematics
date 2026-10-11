{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Combinatorics.Multisets
-- 多重集（重数函数形）与星棒计数对应
--
-- 数学背景：n 类型上的有限多重集 = 重数函数 `Multi n = Fin n → ℕ`；
--   大小 k 的多重集个数 = 星棒系数 `multiset n k = C(n+k−1,k)`（Counting 件）。
--   星棒对应三形：大小 k 多重集 ↔ 弱组合（Σᵢ mᵢ = k）↔ 星位选择 C(n+k−1,k)。
--
-- 核心原则：
-- 1. 重数函数形定义；大小约束进 WeakComp record（关系入定义）
-- 2. 运算点态化（并集 = 逐点 ⊕）；size 同态性构造性证明（rearr 四项重排链）
-- 3. 计数面复用 Counting.multiset 零重证；星棒小例双射全形（≤27 case 边界内）
-- 4. 一般双射（Multi ↔ 星位形）立界 §5——不设空壳签名
--
-- 包含：Multi/size/_∪m_/size-union · zeros-size/wc-head · WeakComp
--       · 星棒计数衔接核对 · pair-class-2（n=2,k=2 三分类）· 核对层

module Sovereign.Algebra.Combinatorics.Multisets where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; suc-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Sovereign.Algebra.Combinatorics.Counting
  using (binom; multiset; multiset-0; multiset-1)

------------------------------------------------------------------------
-- §1 定义层：多重集（重数函数形）
------------------------------------------------------------------------

-- n 个类型上的有限多重集：每个类型的重数
Multi : ℕ → Set
Multi n = Fin n → ℕ

-- 大小（重数总和）——对类数 n 归纳
size : ∀ {n} → Multi n → ℕ
size {zero}  m = 0
size {suc n} m = m fzero + size (λ i → m (fsuc i))

-- 并集（逐点加法）
_∪m_ : ∀ {n} → Multi n → Multi n → Multi n
(a ∪m b) i = a i + b i

------------------------------------------------------------------------
-- §2 主引理层：size 同态性（并集大小 = 大小之和）
------------------------------------------------------------------------

-- 四项重排：(x+y)+(z+w) ≡ (x+z)+(y+w)——assoc/comm 五步链
rearr : ∀ x y z w → (x + y) + (z + w) ≡ (x + z) + (y + w)
rearr x y z w =
  -- (x+y)+(z+w) = x+(y+(z+w)) [assoc]
  trans (+-assoc x y (z + w))
  --   = x+((y+z)+w) [assoc 反向于 y]
    (trans (cong (x +_) (sym (+-assoc y z w)))
  --   = x+((z+y)+w) [中段交换 y z]
      (trans (cong (x +_) (cong (_+ w) (+-comm y z)))
  --   = x+(z+(y+w)) [assoc]
        (trans (cong (x +_) (+-assoc z y w))
  --   = (x+z)+(y+w) [assoc 反向]
          (sym (+-assoc x z (y + w))))))

-- 并集大小可加：size (a ∪m b) ≡ size a + size b
size-union : ∀ {n} (a b : Multi n) → size (a ∪m b) ≡ size a + size b
size-union {zero}  a b = refl
size-union {suc n} a b =
  -- LHS = (a₀+b₀) + size(a' ∪m b') → IH 搬运 → 四项重排
  trans (cong ((a fzero + b fzero) +_)
              (size-union (λ i → a (fsuc i)) (λ i → b (fsuc i))))
        (rearr (a fzero) (b fzero)
               (size (λ i → a (fsuc i))) (size (λ i → b (fsuc i))))

-- 零多重集大小恒零
zeros-size : ∀ {n} → size {n} (λ _ → 0) ≡ 0
zeros-size {zero}  = refl
zeros-size {suc n} = trans (cong (0 +_) (zeros-size {n})) refl

------------------------------------------------------------------------
-- §3 基础件层（续）：弱组合（星棒的数字形）
------------------------------------------------------------------------

-- 弱组合：n 个非负整数之和恰为 k（大小约束进 record——关系入定义）
record WeakComp (n k : ℕ) : Set where
  field
    mult  : Multi n
    size≡ : size mult ≡ k

-- 规范形：全部投入首类
wc-head : ∀ {n} (k : ℕ) → WeakComp (suc n) k
WeakComp.mult  (wc-head {n} k) fzero    = k
WeakComp.mult  (wc-head {n} k) (fsuc i) = 0
WeakComp.size≡ (wc-head {n} k) =
  -- size = k + zeros ≡ k + 0 ≡ k [zeros-size → +identityʳ]
  trans (cong (k +_) (zeros-size {n})) (+-identityʳ k)

------------------------------------------------------------------------
-- §4 计数衔接与小例双射（星棒内容的构造面）
------------------------------------------------------------------------

-- 计数面衔接（复用零重证）：大小 k 的 n 类多重集个数 = multiset n k
-- （一般双射 Multi ↔ 星位形立界 §5；小值核对 = Pascal 通道独立归约）
check-ms-2-2 : multiset 2 2 ≡ 3
check-ms-2-2 = refl

check-ms-3-2 : multiset 3 2 ≡ 6
check-ms-3-2 = refl

check-ms-2-0 : multiset 2 0 ≡ 1
check-ms-2-0 = refl

check-ms-2-1 : multiset 2 1 ≡ 2
check-ms-2-1 = refl

-- 弱组合分类（星棒 k=2 全形——穷举边界内）：a+b ≡ 2 ⟹ (a,b) ∈ 三分类
pair-class-2 : ∀ a b → a + b ≡ 2 →
  (a ≡ 2 × b ≡ 0) ⊎ (a ≡ 1 × b ≡ 1) ⊎ (a ≡ 0 × b ≡ 2)
pair-class-2 zero b eq = inj₂ (inj₂ (refl , eq))
  -- 0+b = b ≡ 2 [定义相等]
pair-class-2 (suc zero) b eq = inj₂ (inj₁ (refl , suc-inj-b))
  -- 1+b = suc b ≡ suc (suc zero) ⟹ b ≡ suc zero
  where
  suc-inj-b : b ≡ suc zero
  suc-inj-b = suc-injective eq
pair-class-2 (suc (suc zero)) b eq = inj₁ (refl , suc-inj-b2)
  -- 2+b = suc (suc b) ≡ suc (suc zero) ⟹ b ≡ zero
  where
  suc-inj-b2 : b ≡ zero
  suc-inj-b2 = suc-injective (suc-injective eq)
pair-class-2 (suc (suc (suc a))) b eq = ⊥-elim (suc≢zero contra)
  -- 3+a+b = suc(suc(suc(a+b))) ≡ 2 ⟹ suc(a+b) ≡ zero [矛盾]
  where
  contra : suc (a + b) ≡ zero
  contra = suc-injective (suc-injective eq)
  suc≢zero : ∀ {x} → suc x ≡ zero → ⊥
  suc≢zero ()

-- 三分类的具体弱组合（n=2,k=2 全体——与分类定理逐案对齐）
wc22-a : WeakComp 2 2
WeakComp.mult  wc22-a fzero        = 2
WeakComp.mult  wc22-a (fsuc fzero) = 0
WeakComp.size≡ wc22-a = refl

wc22-b : WeakComp 2 2
WeakComp.mult  wc22-b fzero        = 1
WeakComp.mult  wc22-b (fsuc fzero) = 1
WeakComp.size≡ wc22-b = refl

wc22-c : WeakComp 2 2
WeakComp.mult  wc22-c fzero        = 0
WeakComp.mult  wc22-c (fsuc fzero) = 2
WeakComp.size≡ wc22-c = refl

------------------------------------------------------------------------
-- §5 立界注记（诚实边界——不设空壳签名）
-- (i) 星棒一般双射：Multi n k ↔ 星位形（Binom (n+k∸1) k 的 k-子集）——
--     需 Multi 的函数外延（funext）面或商形（Multi 模重排）；小例面即 §4；
-- (ii) 一般 k 的 pair-class 归纳形（k+2 分类链 ~40 行——本件 k=2 全形）；
-- (iii) 多重集/分拆语义锚：Partitions.toMulti 衔接（分拆 = 部值多重集 + 降序约束）；
-- (iv) 计数语义完备性（多重集枚举 = multiset n k 值）——双射 (i) 的推论。
------------------------------------------------------------------------
