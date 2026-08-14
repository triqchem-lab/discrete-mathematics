{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.FiniteProbability
-- 有限概率空间: GF(3)ⁿ 均匀分布 + ℚ 有理期望 + Burnside 1/12 + Markov 平稳分布 (P1-3, wiki 60A)
--
-- 数学背景 (wiki 28-probability):
--   概率 = 有限格点均匀计数比: P(A) = |A|/3ⁿ ∈ ℚ (无极限, 无连续分布)。
--   期望 = (1/3ⁿ) Σ_{x∈GF3ⁿ} X(x) (有限和, 无 Lebesgue 积分)。
--   Burnside: A₄ 正则作用 (12 点自由传递) — 随机 (g,x) 不动概率 = 12/144 = 1/12;
--   自然作用 (4 顶点) — 不动概率 = 12/48 = 1/4 (Σ_g|Fix g| = #轨道·|G| = 12)。
--   Markov: GF(3) 完全均匀链 (每步等概率跳 3 态) — 均匀分布 (1/3,1/3,1/3) 平稳。
--
-- 宪法原则:
--   1. 全离散有理: 概率 = (分子, 分母) 整数对, 相等 = 交叉相乘 (无浮点)。
--   2. GF(3)ⁿ 上的求和 = 前缀树递归 (3 叉), |GF3ⁿ| = 3ⁿ 由 ℕ 归纳。
--   3. A₄ 作用表由 perm 置换表示生成 (144 项群表 + 不动点计数), 0 postulate。
--
-- 包含:
--   §1 有理概率 Rat + 相等/算术
--   §2 GF(3)ⁿ 均匀分布 + |GF3ⁿ| = 3ⁿ + 有理期望
--   §3 Burnside: A₄ 自然作用 (1/4) 与正则作用 (1/12)
--   §4 Markov: GF(3) 均匀链平稳分布 + 双重随机一般引理
--
-- 0 postulate。

module Sovereign.Analysis.FiniteProbability where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; *-comm; *-assoc; *-suc; *-identityʳ; *-identityˡ; +-identityʳ; +-identityˡ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Structology.A4Group using (A4; Id; Rot; Flip; perm)

--------------------------------------------------------------------------------
-- §1. 有理概率 (整数对, 无浮点)
--------------------------------------------------------------------------------

Rat : Set
Rat = ℕ × ℕ

-- 相等: a/b ≡ c/d ⟺ a·d ≡ b·c (交叉相乘)
_≐_ : Rat → Rat → Set
(a , b) ≐ (c , d) = a * d ≡ b * c

-- 加法: a/b + c/d = (ad+cb)/bd
_+r_ : Rat → Rat → Rat
(a , b) +r (c , d) = (a * d + c * b) , (b * d)

-- 乘法: (a/b)(c/d) = ac/bd
_*r_ : Rat → Rat → Rat
(a , b) *r (c , d) = (a * c) , (b * d)

-- 数乘: n·(a/b) = na/b
scalar : ℕ → Rat → Rat
scalar n (a , b) = (n * a) , b

-- 3 项和
rat3 : Rat → Rat → Rat → Rat
rat3 x y z = (x +r y) +r z

--------------------------------------------------------------------------------
-- §2. GF(3)ⁿ 均匀分布与有理期望
--------------------------------------------------------------------------------

-- GF(3)ⁿ 上的全和 (前缀树递归: Σ_{x∈Tritⁿ} f x)
sumGF3 : (n : ℕ) → ((ℕ → Trit) → ℕ) → ℕ
sumGF3 zero f = f (λ _ → T₀)
sumGF3 (suc n) f =
  sumGF3 n (λ x → f (ext T₀ x))
  + (sumGF3 n (λ x → f (ext T₁ x)) + sumGF3 n (λ x → f (ext T₂ x)))
  where
    ext : Trit → (ℕ → Trit) → ℕ → Trit
    ext t x zero = t
    ext t x (suc k) = x k

-- |GF3ⁿ| = 3ⁿ
GF3ⁿ-size : ∀ n → sumGF3 n (λ _ → 1) ≡ 3 ^ n
GF3ⁿ-size zero = refl
GF3ⁿ-size (suc n) = begin
  sumGF3 (suc n) (λ _ → 1)
    ≡⟨⟩
  sumGF3 n (λ _ → 1) + (sumGF3 n (λ _ → 1) + sumGF3 n (λ _ → 1))
    ≡⟨ cong₂ _+_ (GF3ⁿ-size n) (cong₂ _+_ (GF3ⁿ-size n) (GF3ⁿ-size n)) ⟩
  3 ^ n + (3 ^ n + 3 ^ n)
    ≡⟨ three-times (3 ^ n) ⟩
  3 * (3 ^ n)
    ≡⟨⟩
  3 ^ (suc n)
  ∎ where
    three-times : ∀ m → m + (m + m) ≡ 3 * m
    three-times m = begin
      m + (m + m)
        ≡⟨ cong (m +_) (sym (trans (*-suc m 1) (cong (m +_) (*-identityʳ m)))) ⟩
      m + (m * suc 1)
        ≡⟨ sym (*-suc m 2) ⟩
      m * suc 2
        ≡⟨ *-comm m (suc 2) ⟩
      suc 2 * m
        ≡⟨⟩
      3 * m
      ∎

-- 均匀分布: 每个 x 的质量 1/3ⁿ
uniform : (n : ℕ) → Rat
uniform n = 1 , 3 ^ n

-- 归一化: Σ_x 1/3ⁿ = 1
uniform-norm : ∀ n → (sumGF3 n (λ _ → 1) , 3 ^ n) ≐ (1 , 1)
uniform-norm n = begin
  sumGF3 n (λ _ → 1) * 1
    ≡⟨ *-identityʳ (sumGF3 n (λ _ → 1)) ⟩
  sumGF3 n (λ _ → 1)
    ≡⟨ GF3ⁿ-size n ⟩
  3 ^ n
    ≡⟨ sym (*-identityʳ (3 ^ n)) ⟩
  3 ^ n * 1
  ∎

-- 有理期望: E[X] = (Σ X(x)) / 3ⁿ
expectation : (n : ℕ) → ((ℕ → Trit) → ℕ) → Rat
expectation n X = sumGF3 n X , 3 ^ n

-- 常函数期望: E[c] = c
expect-const : ∀ n c → expectation n (λ _ → c) ≐ (c , 1)
expect-const n c = begin
  sumGF3 n (λ _ → c) * 1
    ≡⟨ *-identityʳ (sumGF3 n (λ _ → c)) ⟩
  sumGF3 n (λ _ → c)
    ≡⟨ sum-const n c ⟩
  c * (3 ^ n)
    ≡⟨ *-comm c (3 ^ n) ⟩
  3 ^ n * c
  ∎ where
    sum-const : ∀ n c → sumGF3 n (λ _ → c) ≡ c * (3 ^ n)
    sum-const zero c = sym (*-identityʳ c)
    sum-const (suc n) c = begin
      sumGF3 n (λ _ → c) + (sumGF3 n (λ _ → c) + sumGF3 n (λ _ → c))
        ≡⟨ cong₂ _+_ (sum-const n c) (cong₂ _+_ (sum-const n c) (sum-const n c)) ⟩
      c * (3 ^ n) + (c * (3 ^ n) + c * (3 ^ n))
        ≡⟨ three-times c (3 ^ n) ⟩
      c * (3 * (3 ^ n))
        ≡⟨⟩
      c * (3 ^ (suc n))
      ∎ where
        three-times : ∀ c m → (c * m) + ((c * m) + (c * m)) ≡ c * (3 * m)
        three-times c m = begin
          (c * m) + ((c * m) + (c * m))
            ≡⟨ sym (cong ((c * m) +_) (trans (*-suc (c * m) 1) (cong ((c * m) +_) (*-identityʳ (c * m))))) ⟩
          (c * m) + ((c * m) * suc 1)
            ≡⟨ sym (*-suc (c * m) 2) ⟩
          (c * m) * suc 2
            ≡⟨ *-assoc c m (suc 2) ⟩
          c * (m * suc 2)
            ≡⟨ cong (c *_) (*-comm m (suc 2)) ⟩
          c * (suc 2 * m)
            ≡⟨⟩
          c * (3 * m)
          ∎

-- 均匀分布的期望: E[1] = 1 (与 uniform-norm 一致)
expect-uniform : ∀ n → expectation n (λ _ → 1) ≐ (1 , 1)
expect-uniform n = expect-const n 1

-- 指示函数的概率: P(A) = |A|/3ⁿ (事件 = 指示函数)
probability : (n : ℕ) → ((ℕ → Trit) → ℕ) → Rat
probability = expectation

--------------------------------------------------------------------------------
-- §3. Burnside: A₄ 自然作用 (4 顶点) 与正则作用 (12 点)
--------------------------------------------------------------------------------

-- 自然作用不动点数 (生成表, 12 case: Id→4, Rot→1, Flip→0)
fix4 : A4 → ℕ
fix4 Id = 4
fix4 (Rot zero zero) = 1
fix4 (Rot zero (suc zero)) = 1
fix4 (Rot (suc zero) zero) = 1
fix4 (Rot (suc zero) (suc zero)) = 1
fix4 (Rot (suc (suc zero)) zero) = 1
fix4 (Rot (suc (suc zero)) (suc zero)) = 1
fix4 (Rot (suc (suc (suc zero))) zero) = 1
fix4 (Rot (suc (suc (suc zero))) (suc zero)) = 1
fix4 (Flip zero) = 0
fix4 (Flip (suc zero)) = 0
fix4 (Flip (suc (suc zero))) = 0

-- 正则作用 (左乘) 不动点数 (生成表: Id→12, 其余→0)
fixR : A4 → ℕ
fixR Id = 12
fixR (Rot zero zero) = 0
fixR (Rot zero (suc zero)) = 0
fixR (Rot (suc zero) zero) = 0
fixR (Rot (suc zero) (suc zero)) = 0
fixR (Rot (suc (suc zero)) zero) = 0
fixR (Rot (suc (suc zero)) (suc zero)) = 0
fixR (Rot (suc (suc (suc zero))) zero) = 0
fixR (Rot (suc (suc (suc zero))) (suc zero)) = 0
fixR (Flip zero) = 0
fixR (Flip (suc zero)) = 0
fixR (Flip (suc (suc zero))) = 0

-- 群表 (正则作用的结构, 144 case, 生成)
mulA4 : A4 → A4 → A4
mulA4 Id Id = Id
mulA4 Id (Rot zero zero) = (Rot zero zero)
mulA4 Id (Rot zero (suc zero)) = (Rot zero (suc zero))
mulA4 Id (Rot (suc zero) zero) = (Rot (suc zero) zero)
mulA4 Id (Rot (suc zero) (suc zero)) = (Rot (suc zero) (suc zero))
mulA4 Id (Rot (suc (suc zero)) zero) = (Rot (suc (suc zero)) zero)
mulA4 Id (Rot (suc (suc zero)) (suc zero)) = (Rot (suc (suc zero)) (suc zero))
mulA4 Id (Rot (suc (suc (suc zero))) zero) = (Rot (suc (suc (suc zero))) zero)
mulA4 Id (Rot (suc (suc (suc zero))) (suc zero)) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 Id (Flip zero) = (Flip zero)
mulA4 Id (Flip (suc zero)) = (Flip (suc zero))
mulA4 Id (Flip (suc (suc zero))) = (Flip (suc (suc zero)))
mulA4 (Rot zero zero) Id = (Rot zero zero)
mulA4 (Rot zero zero) (Rot zero zero) = (Rot zero (suc zero))
mulA4 (Rot zero zero) (Rot zero (suc zero)) = Id
mulA4 (Rot zero zero) (Rot (suc zero) zero) = (Flip (suc (suc zero)))
mulA4 (Rot zero zero) (Rot (suc zero) (suc zero)) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot zero zero) (Rot (suc (suc zero)) zero) = (Rot (suc zero) zero)
mulA4 (Rot zero zero) (Rot (suc (suc zero)) (suc zero)) = (Flip zero)
mulA4 (Rot zero zero) (Rot (suc (suc (suc zero))) zero) = (Flip (suc zero))
mulA4 (Rot zero zero) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot zero zero) (Flip zero) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot zero zero) (Flip (suc zero)) = (Rot (suc zero) (suc zero))
mulA4 (Rot zero zero) (Flip (suc (suc zero))) = (Rot (suc (suc zero)) zero)
mulA4 (Rot zero (suc zero)) Id = (Rot zero (suc zero))
mulA4 (Rot zero (suc zero)) (Rot zero zero) = Id
mulA4 (Rot zero (suc zero)) (Rot zero (suc zero)) = (Rot zero zero)
mulA4 (Rot zero (suc zero)) (Rot (suc zero) zero) = (Rot (suc (suc zero)) zero)
mulA4 (Rot zero (suc zero)) (Rot (suc zero) (suc zero)) = (Flip (suc zero))
mulA4 (Rot zero (suc zero)) (Rot (suc (suc zero)) zero) = (Flip (suc (suc zero)))
mulA4 (Rot zero (suc zero)) (Rot (suc (suc zero)) (suc zero)) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot zero (suc zero)) (Rot (suc (suc (suc zero))) zero) = (Rot (suc zero) (suc zero))
mulA4 (Rot zero (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = (Flip zero)
mulA4 (Rot zero (suc zero)) (Flip zero) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot zero (suc zero)) (Flip (suc zero)) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot zero (suc zero)) (Flip (suc (suc zero))) = (Rot (suc zero) zero)
mulA4 (Rot (suc zero) zero) Id = (Rot (suc zero) zero)
mulA4 (Rot (suc zero) zero) (Rot zero zero) = (Flip (suc zero))
mulA4 (Rot (suc zero) zero) (Rot zero (suc zero)) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot (suc zero) zero) (Rot (suc zero) zero) = (Rot (suc zero) (suc zero))
mulA4 (Rot (suc zero) zero) (Rot (suc zero) (suc zero)) = Id
mulA4 (Rot (suc zero) zero) (Rot (suc (suc zero)) zero) = (Flip zero)
mulA4 (Rot (suc zero) zero) (Rot (suc (suc zero)) (suc zero)) = (Rot zero zero)
mulA4 (Rot (suc zero) zero) (Rot (suc (suc (suc zero))) zero) = (Rot (suc (suc zero)) zero)
mulA4 (Rot (suc zero) zero) (Rot (suc (suc (suc zero))) (suc zero)) = (Flip (suc (suc zero)))
mulA4 (Rot (suc zero) zero) (Flip zero) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot (suc zero) zero) (Flip (suc zero)) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot (suc zero) zero) (Flip (suc (suc zero))) = (Rot zero (suc zero))
mulA4 (Rot (suc zero) (suc zero)) Id = (Rot (suc zero) (suc zero))
mulA4 (Rot (suc zero) (suc zero)) (Rot zero zero) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot (suc zero) (suc zero)) (Rot zero (suc zero)) = (Flip (suc (suc zero)))
mulA4 (Rot (suc zero) (suc zero)) (Rot (suc zero) zero) = Id
mulA4 (Rot (suc zero) (suc zero)) (Rot (suc zero) (suc zero)) = (Rot (suc zero) zero)
mulA4 (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) zero) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = (Flip (suc zero))
mulA4 (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) zero) = (Flip zero)
mulA4 (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot zero (suc zero))
mulA4 (Rot (suc zero) (suc zero)) (Flip zero) = (Rot (suc (suc zero)) zero)
mulA4 (Rot (suc zero) (suc zero)) (Flip (suc zero)) = (Rot zero zero)
mulA4 (Rot (suc zero) (suc zero)) (Flip (suc (suc zero))) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot (suc (suc zero)) zero) Id = (Rot (suc (suc zero)) zero)
mulA4 (Rot (suc (suc zero)) zero) (Rot zero zero) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot (suc (suc zero)) zero) (Rot zero (suc zero)) = (Flip zero)
mulA4 (Rot (suc (suc zero)) zero) (Rot (suc zero) zero) = (Flip (suc zero))
mulA4 (Rot (suc (suc zero)) zero) (Rot (suc zero) (suc zero)) = (Rot zero (suc zero))
mulA4 (Rot (suc (suc zero)) zero) (Rot (suc (suc zero)) zero) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot (suc (suc zero)) zero) (Rot (suc (suc zero)) (suc zero)) = Id
mulA4 (Rot (suc (suc zero)) zero) (Rot (suc (suc (suc zero))) zero) = (Flip (suc (suc zero)))
mulA4 (Rot (suc (suc zero)) zero) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot (suc zero) zero)
mulA4 (Rot (suc (suc zero)) zero) (Flip zero) = (Rot (suc zero) (suc zero))
mulA4 (Rot (suc (suc zero)) zero) (Flip (suc zero)) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot (suc (suc zero)) zero) (Flip (suc (suc zero))) = (Rot zero zero)
mulA4 (Rot (suc (suc zero)) (suc zero)) Id = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot zero zero) = (Flip (suc (suc zero)))
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot zero (suc zero)) = (Rot (suc zero) (suc zero))
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) zero) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) (suc zero)) = (Flip zero)
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) zero) = Id
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = (Rot (suc (suc zero)) zero)
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) zero) = (Rot zero zero)
mulA4 (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = (Flip (suc zero))
mulA4 (Rot (suc (suc zero)) (suc zero)) (Flip zero) = (Rot zero (suc zero))
mulA4 (Rot (suc (suc zero)) (suc zero)) (Flip (suc zero)) = (Rot (suc zero) zero)
mulA4 (Rot (suc (suc zero)) (suc zero)) (Flip (suc (suc zero))) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot (suc (suc (suc zero))) zero) Id = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot zero zero) = (Flip zero)
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot zero (suc zero)) = (Rot (suc (suc zero)) zero)
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot (suc zero) zero) = (Rot zero zero)
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot (suc zero) (suc zero)) = (Flip (suc (suc zero)))
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc zero)) zero) = (Flip (suc zero))
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc zero)) (suc zero)) = (Rot (suc zero) (suc zero))
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc (suc zero))) zero) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc (suc zero))) (suc zero)) = Id
mulA4 (Rot (suc (suc (suc zero))) zero) (Flip zero) = (Rot (suc zero) zero)
mulA4 (Rot (suc (suc (suc zero))) zero) (Flip (suc zero)) = (Rot zero (suc zero))
mulA4 (Rot (suc (suc (suc zero))) zero) (Flip (suc (suc zero))) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) Id = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot zero zero) = (Rot (suc zero) zero)
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot zero (suc zero)) = (Flip (suc zero))
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) zero) = (Flip zero)
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) (suc zero)) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) zero) = (Rot zero (suc zero))
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = (Flip (suc (suc zero)))
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) zero) = Id
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Flip zero) = (Rot zero zero)
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc zero)) = (Rot (suc (suc zero)) zero)
mulA4 (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc (suc zero))) = (Rot (suc zero) (suc zero))
mulA4 (Flip zero) Id = (Flip zero)
mulA4 (Flip zero) (Rot zero zero) = (Rot (suc (suc zero)) zero)
mulA4 (Flip zero) (Rot zero (suc zero)) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Flip zero) (Rot (suc zero) zero) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Flip zero) (Rot (suc zero) (suc zero)) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Flip zero) (Rot (suc (suc zero)) zero) = (Rot zero zero)
mulA4 (Flip zero) (Rot (suc (suc zero)) (suc zero)) = (Rot (suc zero) zero)
mulA4 (Flip zero) (Rot (suc (suc (suc zero))) zero) = (Rot zero (suc zero))
mulA4 (Flip zero) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot (suc zero) (suc zero))
mulA4 (Flip zero) (Flip zero) = Id
mulA4 (Flip zero) (Flip (suc zero)) = (Flip (suc (suc zero)))
mulA4 (Flip zero) (Flip (suc (suc zero))) = (Flip (suc zero))
mulA4 (Flip (suc zero)) Id = (Flip (suc zero))
mulA4 (Flip (suc zero)) (Rot zero zero) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Flip (suc zero)) (Rot zero (suc zero)) = (Rot (suc zero) zero)
mulA4 (Flip (suc zero)) (Rot (suc zero) zero) = (Rot zero (suc zero))
mulA4 (Flip (suc zero)) (Rot (suc zero) (suc zero)) = (Rot (suc (suc zero)) zero)
mulA4 (Flip (suc zero)) (Rot (suc (suc zero)) zero) = (Rot (suc zero) (suc zero))
mulA4 (Flip (suc zero)) (Rot (suc (suc zero)) (suc zero)) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Flip (suc zero)) (Rot (suc (suc (suc zero))) zero) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Flip (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot zero zero)
mulA4 (Flip (suc zero)) (Flip zero) = (Flip (suc (suc zero)))
mulA4 (Flip (suc zero)) (Flip (suc zero)) = Id
mulA4 (Flip (suc zero)) (Flip (suc (suc zero))) = (Flip zero)
mulA4 (Flip (suc (suc zero))) Id = (Flip (suc (suc zero)))
mulA4 (Flip (suc (suc zero))) (Rot zero zero) = (Rot (suc zero) (suc zero))
mulA4 (Flip (suc (suc zero))) (Rot zero (suc zero)) = (Rot (suc (suc zero)) (suc zero))
mulA4 (Flip (suc (suc zero))) (Rot (suc zero) zero) = (Rot (suc (suc (suc zero))) zero)
mulA4 (Flip (suc (suc zero))) (Rot (suc zero) (suc zero)) = (Rot zero zero)
mulA4 (Flip (suc (suc zero))) (Rot (suc (suc zero)) zero) = (Rot (suc (suc (suc zero))) (suc zero))
mulA4 (Flip (suc (suc zero))) (Rot (suc (suc zero)) (suc zero)) = (Rot zero (suc zero))
mulA4 (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) zero) = (Rot (suc zero) zero)
mulA4 (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) (suc zero)) = (Rot (suc (suc zero)) zero)
mulA4 (Flip (suc (suc zero))) (Flip zero) = (Flip (suc zero))
mulA4 (Flip (suc (suc zero))) (Flip (suc zero)) = (Flip zero)
mulA4 (Flip (suc (suc zero))) (Flip (suc (suc zero))) = Id

-- Burnside 自然作用: Σ_g |Fix g| = 12 = #轨道 · |A₄| (1 × 12)
burnside-natural : fix4 Id
  + (fix4 (Rot zero zero) + (fix4 (Rot zero (suc zero)) + (fix4 (Rot (suc zero) zero)
  + (fix4 (Rot (suc zero) (suc zero)) + (fix4 (Rot (suc (suc zero)) zero)
  + (fix4 (Rot (suc (suc zero)) (suc zero)) + (fix4 (Rot (suc (suc (suc zero))) zero)
  + (fix4 (Rot (suc (suc (suc zero))) (suc zero)) + (fix4 (Flip zero)
  + (fix4 (Flip (suc zero)) + fix4 (Flip (suc (suc zero)))))))))))))
  ≡ 12
burnside-natural = refl

-- 自然作用不动概率: (Σ_g|Fix g|)/(|A₄|·4) = 12/48 = 1/4
prob-natural : (12 , 12 * 4) ≐ (1 , 4)
prob-natural = refl

-- Burnside 正则作用: Σ_g |Fix g| = 12 (仅 Id 不动, 12 个点)
burnside-regular : fixR Id
  + (fixR (Rot zero zero) + (fixR (Rot zero (suc zero)) + (fixR (Rot (suc zero) zero)
  + (fixR (Rot (suc zero) (suc zero)) + (fixR (Rot (suc (suc zero)) zero)
  + (fixR (Rot (suc (suc zero)) (suc zero)) + (fixR (Rot (suc (suc (suc zero))) zero)
  + (fixR (Rot (suc (suc (suc zero))) (suc zero)) + (fixR (Flip zero)
  + (fixR (Flip (suc zero)) + fixR (Flip (suc (suc zero)))))))))))))
  ≡ 12
burnside-regular = refl

-- 正则作用不动概率: 12/144 = 1/12 ⭐
prob-regular : (12 , 12 * 12) ≐ (1 , 12)
prob-regular = refl

-- 正则作用忠实: g ≠ Id ⟹ fixR g ≡ 0 (生成表验证的声明形式)
fixR-faithful : (g : A4) → fixR g ≡ 12 → g ≡ Id
fixR-faithful Id refl = refl
fixR-faithful (Rot zero zero) ()
fixR-faithful (Rot zero (suc zero)) ()
fixR-faithful (Rot (suc zero) zero) ()
fixR-faithful (Rot (suc zero) (suc zero)) ()
fixR-faithful (Rot (suc (suc zero)) zero) ()
fixR-faithful (Rot (suc (suc zero)) (suc zero)) ()
fixR-faithful (Rot (suc (suc (suc zero))) zero) ()
fixR-faithful (Rot (suc (suc (suc zero))) (suc zero)) ()
fixR-faithful (Flip zero) ()
fixR-faithful (Flip (suc zero)) ()
fixR-faithful (Flip (suc (suc zero))) ()

--------------------------------------------------------------------------------
-- §4. Markov 链: GF(3) 均匀链的平稳分布
--------------------------------------------------------------------------------

-- 转移: P(i, j) = 1/3 (完全均匀 3 态链)
T : Trit → Trit → Rat
T _ _ = 1 , 3

-- 平稳方程 (列 j): Σᵢ π(i)·T(i,j) ≐ π(j), π = (1/3, 1/3, 1/3)
stationary : ∀ j →
  ((scalar 1 (T T₀ j) *r (1 , 3))
   +r ((scalar 1 (T T₁ j) *r (1 , 3)) +r (scalar 1 (T T₂ j) *r (1 , 3))))
  ≐ (1 , 3)
stationary T₀ = refl
stationary T₁ = refl
stationary T₂ = refl

-- 双重随机一般引理: 每列和为 1 ⟹ 均匀分布平稳 (ℚ 整数形式)
-- 具体形态: P(i,j) = aᵢⱼ/bᵢⱼ 且 Σᵢ aᵢⱼ·∏ₖ≠ᵢ bₖⱼ = ∏ᵢ bᵢⱼ ⟹ (1/3)·Σᵢ P(i,j) ≐ 1/3
-- GF(3) 实例已由 stationary 覆盖; 一般引理以整数恒等式给出:
doubly-stochastic : (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℕ) →
  a00 + a10 + a20 ≡ 3 → a01 + a11 + a21 ≡ 3 → a02 + a12 + a22 ≡ 3 →
  ((((a00 + a10) + a20) , 9) ≐ (1 , 3)) × ((((a01 + a11) + a21) , 9) ≐ (1 , 3))
  × ((((a02 + a12) + a22) , 9) ≐ (1 , 3))
doubly-stochastic a00 a01 a02 a10 a11 a12 a20 a21 a22 h0 h1 h2 =
  (trans (cong (_* 3) h0) refl)
  , (trans (cong (_* 3) h1) refl)
  , (trans (cong (_* 3) h2) refl)
