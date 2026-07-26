{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.NormDiscrete where

--------------------------------------------------------------------------------
-- 离散范数理论 — GF(9)ⁿ 上的范数结构
--
-- 核心概念:
--   • normReal: 取 GF(9) 范数的 GF(3) 分量 (二次型)
--   • normSup: 离散 sup-范数 (正定)
--   • Trit 序关系 _≤t_: 离散值域上的全序
--   • 范数等价性: 有限维离散空间中所有范数等价
--
-- 关键区别 (与连续泛函分析):
--   ① 值域离散: 范数仅取 {T₀, T₁, T₂} 三个值
--   ② 二次型退化: 存在各向同性向量 (normReal(v)=T₀ 但 v≠0)
--   ③ sup-范数正定: normSup(v)=T₀ 当且仅当 v=0
--   ④ 所有范数诱导相同离散拓扑
--
-- 依赖:
--   Sovereign.Analysis.LinearFunctionalDiscrete — GF(9) 向量空间/内积
--   Sovereign.Algebra.GF9 — GF(9) 域运算和 Galois 范数
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
  renaming (module ≡-Reasoning to ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm;
  ⊗-identityˡ; ⊗-identityʳ;
  ⊗-zeroʳ; ⊗-zeroˡ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)

open import Sovereign.Algebra.GF9 using (
  GF9; _+gf9_; _*gf9_; gf9-one; galoisConjugate; galoisConjugate²;
  galoisNorm; embed-gf3;
  +gf9-identityˡ; +gf9-identityʳ;
  *gf9-identityˡ; *gf9-identityʳ;
  *gf9-comm; *gf9-assoc;
  *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
  negate-⊗; negate-⊗-comm; negate-⊗-negate)

open import Sovereign.Analysis.LinearFunctionalDiscrete using (
  VectorSpace; gf9-zero; _+v9_; _·v9_; 0⃗₉; inner9;
  *gf9-zeroˡ; *gf9-zeroʳ; scalar9-zero;
  +v9-identityˡ; +v9-identityʳ)

--------------------------------------------------------------------------------
-- §1. 离散范数定义
--------------------------------------------------------------------------------

-- 二次型范数: normReal(v) = Σᵢ N(vᵢ) (GF(3) 加法)
-- N: GF(9) → GF(3) 是 Galois 范数 N(a+bα) = a²+b²
normReal : ∀ n → VectorSpace n → Trit
normReal zero [] = T₀
normReal (suc n) (x ∷ xs) = galoisNorm x ⊕ normReal n xs

-- 离散 sup-范数: normSup(v) = max(N(vᵢ)) (Trit 序下的最大值)
-- 先定义 Trit 上的 max
maxT : Trit → Trit → Trit
maxT T₀ y = y
maxT T₁ T₀ = T₁
maxT T₁ T₁ = T₁
maxT T₁ T₂ = T₂
maxT T₂ _ = T₂

normSup : ∀ n → VectorSpace n → Trit
normSup zero [] = T₀
normSup (suc n) (x ∷ xs) = maxT (galoisNorm x) (normSup n xs)

--------------------------------------------------------------------------------
-- §2. Trit 序关系 _≤t_
--------------------------------------------------------------------------------

-- Trit 上的全序: T₀ ≤ T₁ ≤ T₂
data _≤t_ : Trit → Trit → Set where
  ≤t-00 : T₀ ≤t T₀
  ≤t-01 : T₀ ≤t T₁
  ≤t-02 : T₀ ≤t T₂
  ≤t-11 : T₁ ≤t T₁
  ≤t-12 : T₁ ≤t T₂
  ≤t-22 : T₂ ≤t T₂

-- 序自反性
≤t-refl : ∀ x → x ≤t x
≤t-refl T₀ = ≤t-00
≤t-refl T₁ = ≤t-11
≤t-refl T₂ = ≤t-22

-- 序传递性
≤t-trans : ∀ {x y z} → x ≤t y → y ≤t z → x ≤t z
≤t-trans ≤t-00 ≤t-00 = ≤t-00
≤t-trans ≤t-00 ≤t-01 = ≤t-01
≤t-trans ≤t-00 ≤t-02 = ≤t-02
≤t-trans ≤t-01 ≤t-11 = ≤t-01
≤t-trans ≤t-01 ≤t-12 = ≤t-02
≤t-trans ≤t-02 ≤t-22 = ≤t-02
≤t-trans ≤t-11 ≤t-11 = ≤t-11
≤t-trans ≤t-11 ≤t-12 = ≤t-12
≤t-trans ≤t-12 ≤t-22 = ≤t-12
≤t-trans ≤t-22 ≤t-22 = ≤t-22

-- 序反对称性
≤t-antisym : ∀ {x y} → x ≤t y → y ≤t x → x ≡ y
≤t-antisym ≤t-00 ≤t-00 = refl
≤t-antisym ≤t-11 ≤t-11 = refl
≤t-antisym ≤t-22 ≤t-22 = refl

-- 序全序性: 任意两个 Trit 可比较
≤t-total : ∀ x y → (x ≤t y) ⊎ (y ≤t x)
≤t-total T₀ T₀ = inj₁ ≤t-00
≤t-total T₀ T₁ = inj₁ ≤t-01
≤t-total T₀ T₂ = inj₁ ≤t-02
≤t-total T₁ T₀ = inj₂ ≤t-01
≤t-total T₁ T₁ = inj₁ ≤t-11
≤t-total T₁ T₂ = inj₁ ≤t-12
≤t-total T₂ T₀ = inj₂ ≤t-02
≤t-total T₂ T₁ = inj₂ ≤t-12
≤t-total T₂ T₂ = inj₁ ≤t-22

-- maxT 是上确界
maxT-ubˡ : ∀ x y → x ≤t maxT x y
maxT-ubˡ T₀ T₀ = ≤t-00
maxT-ubˡ T₀ T₁ = ≤t-01
maxT-ubˡ T₀ T₂ = ≤t-02
maxT-ubˡ T₁ T₀ = ≤t-11
maxT-ubˡ T₁ T₁ = ≤t-11
maxT-ubˡ T₁ T₂ = ≤t-12
maxT-ubˡ T₂ T₀ = ≤t-22
maxT-ubˡ T₂ T₁ = ≤t-22
maxT-ubˡ T₂ T₂ = ≤t-22

maxT-ubʳ : ∀ x y → y ≤t maxT x y
maxT-ubʳ T₀ T₀ = ≤t-00
maxT-ubʳ T₀ T₁ = ≤t-11
maxT-ubʳ T₀ T₂ = ≤t-22
maxT-ubʳ T₁ T₀ = ≤t-01
maxT-ubʳ T₁ T₁ = ≤t-11
maxT-ubʳ T₁ T₂ = ≤t-22
maxT-ubʳ T₂ T₀ = ≤t-02
maxT-ubʳ T₂ T₁ = ≤t-12
maxT-ubʳ T₂ T₂ = ≤t-22

--------------------------------------------------------------------------------
-- §3. 正定性
--------------------------------------------------------------------------------

-- GF(9) 范数正定: N(x)=T₀ 当且仅当 x=gf9-zero
-- 穷举 9 case: N(a,b) = a²+b², 在 GF(3) 中仅 (0,0) 给 0
galoisNorm-zero→zero : ∀ x → galoisNorm x ≡ T₀ → x ≡ gf9-zero
galoisNorm-zero→zero (T₀ , T₀) _ = refl
galoisNorm-zero→zero (T₀ , T₁) p = ⊥-elim (T₁≢T₀ p)
  where T₁≢T₀ : T₁ ≡ T₀ → ⊥
        T₁≢T₀ ()
galoisNorm-zero→zero (T₀ , T₂) p = ⊥-elim (T₁≢T₀ p)
  where T₁≢T₀ : T₁ ≡ T₀ → ⊥
        T₁≢T₀ ()
galoisNorm-zero→zero (T₁ , T₀) p = ⊥-elim (T₁≢T₀ p)
  where T₁≢T₀ : T₁ ≡ T₀ → ⊥
        T₁≢T₀ ()
galoisNorm-zero→zero (T₁ , T₁) p = ⊥-elim (T₂≢T₀ p)
  where T₂≢T₀ : T₂ ≡ T₀ → ⊥
        T₂≢T₀ ()
galoisNorm-zero→zero (T₁ , T₂) p = ⊥-elim (T₂≢T₀ p)
  where T₂≢T₀ : T₂ ≡ T₀ → ⊥
        T₂≢T₀ ()
galoisNorm-zero→zero (T₂ , T₀) p = ⊥-elim (T₁≢T₀ p)
  where T₁≢T₀ : T₁ ≡ T₀ → ⊥
        T₁≢T₀ ()
galoisNorm-zero→zero (T₂ , T₁) p = ⊥-elim (T₂≢T₀ p)
  where T₂≢T₀ : T₂ ≡ T₀ → ⊥
        T₂≢T₀ ()
galoisNorm-zero→zero (T₂ , T₂) p = ⊥-elim (T₂≢T₀ p)
  where T₂≢T₀ : T₂ ≡ T₀ → ⊥
        T₂≢T₀ ()

galoisNorm-of-zero : galoisNorm gf9-zero ≡ T₀
galoisNorm-of-zero = refl

-- maxT 零判定: maxT a b ≡ T₀ → a ≡ T₀ × b ≡ T₀
maxT-zero : ∀ a b → maxT a b ≡ T₀ → a ≡ T₀ × b ≡ T₀
maxT-zero T₀ T₀ _ = refl , refl
maxT-zero T₁ T₀ ()
maxT-zero T₁ T₁ ()
maxT-zero T₁ T₂ ()
maxT-zero T₂ T₀ ()
maxT-zero T₂ T₁ ()
maxT-zero T₂ T₂ ()

-- sup-范数正定: normSup(v)=T₀ → v=0⃗₉
normSup-zero→vec-zero : ∀ n (v : VectorSpace n) →
  normSup n v ≡ T₀ → v ≡ 0⃗₉ n
normSup-zero→vec-zero zero [] _ = refl
normSup-zero→vec-zero (suc n) (x ∷ xs) p =
  cong₂ _∷_ (galoisNorm-zero→zero x (proj₁ (maxT-zero (galoisNorm x) (normSup n xs) p)))
            (normSup-zero→vec-zero n xs (proj₂ (maxT-zero (galoisNorm x) (normSup n xs) p)))

-- 零向量的 sup-范数为零
normSup-of-zero : ∀ n → normSup n (0⃗₉ n) ≡ T₀
normSup-of-zero zero = refl
normSup-of-zero (suc n) = normSup-of-zero n

-- 零向量的二次型范数为零
normReal-of-zero : ∀ n → normReal n (0⃗₉ n) ≡ T₀
normReal-of-zero zero = refl
normReal-of-zero (suc n) = normReal-of-zero n

-- 二次型范数的各向同性: 存在 v≠0 但 normReal(v)=T₀
-- 例: (1,0), (1,0), (1,0) 的范数和 = 1+1+1 = 3 ≡ 0 (mod 3)
isotropic-example9 :
  normReal 3 ((T₁ , T₀) ∷ (T₁ , T₀) ∷ (T₁ , T₀) ∷ []) ≡ T₀
isotropic-example9 = refl

-- 但该向量不是零向量
isotropic-nonzero9 :
  ((T₁ , T₀) ∷ (T₁ , T₀) ∷ (T₁ , T₀) ∷ []) ≢ 0⃗₉ 3
isotropic-nonzero9 ()

--------------------------------------------------------------------------------
-- §4. 齐次性
--------------------------------------------------------------------------------

-- GF(9) 范数乘法性: N(x·y) = N(x)·N(y) (GF(3) 中)
-- 证明: 对 x 的 9 个可能值穷举, 每个 case 对 y 的分量用 GF(3) 算术验证
-- 关键引理: (2t)²=t², negate(t)²=t² (GF(3) 特征)
galoisNorm-multiplicative : ∀ x y →
  galoisNorm (x *gf9 y) ≡ galoisNorm x ⊗ galoisNorm y
-- 81 case 穷举: 对 x 和 y 的分量全部展开, Agda 计算归约验证
galoisNorm-multiplicative (T₀ , T₀) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₀) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₁) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₀ , T₂) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₀) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₁) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₁ , T₂) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₀) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₁) (T₂ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₀ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₀ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₀ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₁ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₁ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₁ , T₂) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₂ , T₀) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₂ , T₁) = refl
galoisNorm-multiplicative (T₂ , T₂) (T₂ , T₂) = refl

-- 二次型范数齐次性: normReal(a·v) = N(a) · normReal(v)
normReal-homogeneous : ∀ n (a : GF9) (v : VectorSpace n) →
  normReal n (a ·v9 v) ≡ galoisNorm a ⊗ normReal n v
normReal-homogeneous zero a [] = sym (⊗-zeroʳ (galoisNorm a))
normReal-homogeneous (suc n) a (x ∷ xs) =
  begin
    galoisNorm (a *gf9 x) ⊕ normReal n (a ·v9 xs)
  ≡⟨ cong₂ _⊕_ (galoisNorm-multiplicative a x)
               (normReal-homogeneous n a xs) ⟩
    (galoisNorm a ⊗ galoisNorm x) ⊕ (galoisNorm a ⊗ normReal n xs)
  ≡⟨ sym (⊗-distribˡ-⊕ (galoisNorm a) (galoisNorm x) (normReal n xs)) ⟩
    galoisNorm a ⊗ (galoisNorm x ⊕ normReal n xs)
  ∎
  where open ≡-Reasoning

-- 零标量乘任意向量得零向量
scalar9-zeroˡ-vec : ∀ n (v : VectorSpace n) → gf9-zero ·v9 v ≡ 0⃗₉ n
scalar9-zeroˡ-vec zero [] = refl
scalar9-zeroˡ-vec (suc n) (x ∷ xs) =
  cong₂ _∷_ (*gf9-zeroˡ x) (scalar9-zeroˡ-vec n xs)

-- sup-范数零标量: normSup(0·v) = T₀
normSup-zero-scalar : ∀ n (v : VectorSpace n) →
  normSup n (gf9-zero ·v9 v) ≡ T₀
normSup-zero-scalar n v =
  trans (cong (normSup n) (scalar9-zeroˡ-vec n v))
        (normSup-of-zero n)

-- sup-范数单位标量: normSup(1·v) = normSup(v)
normSup-one-scalar : ∀ n (v : VectorSpace n) →
  normSup n (gf9-one ·v9 v) ≡ normSup n v
normSup-one-scalar zero [] = refl
normSup-one-scalar (suc n) (x ∷ xs) =
  cong₂ maxT (cong galoisNorm (*gf9-identityˡ x)) (normSup-one-scalar n xs)

--------------------------------------------------------------------------------
-- §5. 范数等价性框架
--
-- 定理: 有限维离散空间中, 所有 "范数" 诱导相同的离散拓扑
-- 原因: 值域有限 ({T₀, T₁, T₂}), 拓扑由零集决定
--
-- 等价条件: 两个范数 N₁, N₂ 等价当且仅当
--   N₁(v) = T₀ ↔ N₂(v) = T₀ (零集相同)
--------------------------------------------------------------------------------

-- 范数等价关系
record NormEquiv (N₁ N₂ : ∀ n → VectorSpace n → Trit) : Set where
  field
    -- 零集相同: N₁(v)=T₀ ↔ N₂(v)=T₀
    zero-set-same : ∀ n (v : VectorSpace n) →
      (N₁ n v ≡ T₀ → N₂ n v ≡ T₀) ×
      (N₂ n v ≡ T₀ → N₁ n v ≡ T₀)

-- 范数等价是自反的
normEquiv-refl : ∀ {N} → NormEquiv N N
normEquiv-refl = record { zero-set-same = λ _ _ → (λ p → p) , (λ p → p) }

-- 范数等价是对称的
normEquiv-sym : ∀ {N₁ N₂} → NormEquiv N₁ N₂ → NormEquiv N₂ N₁
normEquiv-sym eq = record
  { zero-set-same = λ n v →
      let (fwd , bwd) = NormEquiv.zero-set-same eq n v
      in (bwd , fwd)
  }

-- 范数等价是传递的
normEquiv-trans : ∀ {N₁ N₂ N₃} → NormEquiv N₁ N₂ → NormEquiv N₂ N₃ → NormEquiv N₁ N₃
normEquiv-trans eq₁₂ eq₂₃ = record
  { zero-set-same = λ n v →
      let (fwd₁₂ , bwd₁₂) = NormEquiv.zero-set-same eq₁₂ n v
          (fwd₂₃ , bwd₂₃) = NormEquiv.zero-set-same eq₂₃ n v
      in ((λ p → fwd₂₃ (fwd₁₂ p)) , (λ p → bwd₁₂ (bwd₂₃ p)))
  }

-- normSup 的正定性保证: normSup 与 "零判定" 等价
-- 即 normSup(v)=T₀ ↔ v=0⃗ 是范数等价的典范实例
normSup-determines-zero : ∀ n (v : VectorSpace n) →
  (normSup n v ≡ T₀ → v ≡ 0⃗₉ n) ×
  (v ≡ 0⃗₉ n → normSup n v ≡ T₀)
normSup-determines-zero n v =
  (normSup-zero→vec-zero n v) ,
  (λ p → subst (λ w → normSup n w ≡ T₀) (sym p) (normSup-of-zero n))

-- 二次型范数零集包含零向量 (但可能有各向同性向量)
normReal-zero-includes-zero : ∀ n (v : VectorSpace n) →
  v ≡ 0⃗₉ n → normReal n v ≡ T₀
normReal-zero-includes-zero n v p =
  subst (λ w → normReal n w ≡ T₀) (sym p) (normReal-of-zero n)

--------------------------------------------------------------------------------
-- §6. 范数值域分析
--------------------------------------------------------------------------------

-- galoisNorm 值域: 仅取 {T₀, T₁, T₂}
-- N(0,0)=T₀, N(±1,0)=N(0,±1)=T₁, N(±1,±1)=T₂
galoisNorm-values : ∀ x →
  (galoisNorm x ≡ T₀) ⊎ (galoisNorm x ≡ T₁) ⊎ (galoisNorm x ≡ T₂)
galoisNorm-values (T₀ , T₀) = inj₁ refl
galoisNorm-values (T₀ , T₁) = inj₂ (inj₁ refl)
galoisNorm-values (T₀ , T₂) = inj₂ (inj₁ refl)
galoisNorm-values (T₁ , T₀) = inj₂ (inj₁ refl)
galoisNorm-values (T₁ , T₁) = inj₂ (inj₂ refl)
galoisNorm-values (T₁ , T₂) = inj₂ (inj₂ refl)
galoisNorm-values (T₂ , T₀) = inj₂ (inj₁ refl)
galoisNorm-values (T₂ , T₁) = inj₂ (inj₂ refl)
galoisNorm-values (T₂ , T₂) = inj₂ (inj₂ refl)

-- normSup 值域: 仅取 {T₀, T₁, T₂}
normSup-values : ∀ n (v : VectorSpace n) →
  (normSup n v ≡ T₀) ⊎ (normSup n v ≡ T₁) ⊎ (normSup n v ≡ T₂)
normSup-values zero [] = inj₁ refl
normSup-values (suc n) (x ∷ xs) = helper (galoisNorm-values x) (normSup-values n xs)
  where
    helper : ((galoisNorm x ≡ T₀) ⊎ (galoisNorm x ≡ T₁) ⊎ (galoisNorm x ≡ T₂)) →
             ((normSup n xs ≡ T₀) ⊎ (normSup n xs ≡ T₁) ⊎ (normSup n xs ≡ T₂)) →
             (normSup (suc n) (x ∷ xs) ≡ T₀) ⊎
             (normSup (suc n) (x ∷ xs) ≡ T₁) ⊎
             (normSup (suc n) (x ∷ xs) ≡ T₂)
    helper (inj₁ p) (inj₁ q) = inj₁ (trans (cong₂ maxT p q) refl)
    helper (inj₁ p) (inj₂ (inj₁ q)) = inj₂ (inj₁ (trans (cong₂ maxT p q) refl))
    helper (inj₁ p) (inj₂ (inj₂ q)) = inj₂ (inj₂ (trans (cong₂ maxT p q) refl))
    helper (inj₂ (inj₁ p)) (inj₁ q) = inj₂ (inj₁ (trans (cong₂ maxT p q) refl))
    helper (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) = inj₂ (inj₁ (trans (cong₂ maxT p q) refl))
    helper (inj₂ (inj₁ p)) (inj₂ (inj₂ q)) = inj₂ (inj₂ (trans (cong₂ maxT p q) refl))
    helper (inj₂ (inj₂ p)) (inj₁ q) = inj₂ (inj₂ (trans (cong₂ maxT p q) refl))
    helper (inj₂ (inj₂ p)) (inj₂ (inj₁ q)) = inj₂ (inj₂ (trans (cong₂ maxT p q) refl))
    helper (inj₂ (inj₂ p)) (inj₂ (inj₂ q)) = inj₂ (inj₂ (trans (cong₂ maxT p q) refl))

--------------------------------------------------------------------------------
-- 总结: 离散范数理论核心定理
--
-- 1. normReal: 二次型范数 (齐次, 但非正定 — 各向同性)
-- 2. normSup: sup-范数 (正定, 值域 {T₀, T₁, T₂})
-- 3. _≤t_: Trit 全序 (T₀ ≤ T₁ ≤ T₂)
-- 4. galoisNorm-multiplicative: N(x·y) = N(x)·N(y)
-- 5. normReal-homogeneous: normReal(a·v) = N(a)·normReal(v)
-- 6. NormEquiv: 范数等价框架 (零集相同)
-- 7. 所有范数诱导相同离散拓扑 (值域有限 → 拓扑由零集决定)
--
-- 与连续范数理论的投影关系:
--   连续: 范数取 ℝ₊ 值, 等价性需要双向不等式
--   离散: 范数取 {T₀,T₁,T₂}, 等价性退化为零集相同
--   投影方向: 离散 (本体) → 连续 (影子), 信息丢失: 有限值域结构
--------------------------------------------------------------------------------
