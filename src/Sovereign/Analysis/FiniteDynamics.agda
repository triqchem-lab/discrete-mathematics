{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Analysis.FiniteDynamics
-- 有限动力系统：轨道、周期性、鸽巢原理、GF(9) Frobenius 动力学
module Sovereign.Analysis.FiniteDynamics where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-suc; <⇒≤; ≤-trans; ≤-pred; m+[n∸m]≡n; m∸n≤m; n<1+n; <-irrefl)
open import Data.Fin using (Fin; toℕ; fromℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ<n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

-- ⚠ 重构归位（2026-09-11）: 本模块是**通用**有限动力系统机制，
-- 原先夹带的 GF9 专用物（Frobenius 轨道、不动点刻画、GF9↔Fin9 编码、
-- 周期上界）已全部归位到 `Sovereign.Algebra.FrobeniusOrbit`。
-- 因此这里不再 import `Sovereign.Base.Trit` / `Sovereign.Algebra.GF9` ——
-- 通用模块不承载具体域，依赖方向变纯粹。

--------------------------------------------------------------------------------
-- §1. 轨道定义
--------------------------------------------------------------------------------

-- 离散轨道: 从 x0 出发, 反复应用 f
orbit : {A : Set} → (A → A) → A → ℕ → A
orbit f x0 zero    = x0
orbit f x0 (suc n) = f (orbit f x0 n)

-- 轨道步进: orbit f x0 (suc n) ≡ f (orbit f x0 n)
orbit-step : {A : Set} (f : A → A) (x0 : A) (n : ℕ) → orbit f x0 (suc n) ≡ f (orbit f x0 n)
orbit-step f x0 n = refl

-- 轨道确定性: 若 x ≡ y, 则 f^n(x) ≡ f^n(y)
orbit-cong : {A : Set} (f : A → A) (x y : A) (n : ℕ) → x ≡ y → orbit f x n ≡ orbit f y n
orbit-cong f x y zero    eq = eq
orbit-cong f x y (suc n) eq = cong f (orbit-cong f x y n eq)

--------------------------------------------------------------------------------
-- §2. 最终周期性
--------------------------------------------------------------------------------

record EventuallyPeriodic {A : Set} (seq : ℕ → A) : Set where
  field
    start    : ℕ
    period   : ℕ
    periodic : ∀ k → seq (start + k + period) ≡ seq (start + k)

--------------------------------------------------------------------------------
-- §3. 鸽巢原理（构造性）
--
-- 标准库 Data.Fin.Properties.pigeonhole 的包装:
-- 对任意 f : Fin (suc n) → Fin n, 存在 i < j 使得 f i ≡ f j。
-- 标准库证明为对 n 的归纳 (使用 any? + punchOut), 完全构造性。
--------------------------------------------------------------------------------

pigeonhole-fin : ∀ n → (f : Fin (suc n) → Fin n) →
  Σ (Fin (suc n)) (λ i → Σ (Fin (suc n)) (λ j → toℕ i < toℕ j × f i ≡ f j))
pigeonhole-fin n f = pigeonhole (n<1+n n) f
  -- n<1+n n : n < suc n, 即 Fin (suc n) 比 Fin n 多一个元素

-- 鸽巢原理的碰撞推论: i < j 蕴含 i ≢ j
pigeonhole-collision : ∀ n → (f : Fin (suc n) → Fin n) →
  Σ (Fin (suc n)) (λ i → Σ (Fin (suc n)) (λ j → i ≢ j × f i ≡ f j))
pigeonhole-collision n f =
  let (i , (j , (i<j , fi≡fj))) = pigeonhole-fin n f
  in  (i , (j , (≢-from-< i<j , fi≡fj)))
  where
    ≢-from-< : {i j : Fin (suc n)} → toℕ i < toℕ j → i ≢ j
    ≢-from-< i<j eq rewrite eq = <-irrefl refl i<j

--------------------------------------------------------------------------------
-- §4. 轨道周期定理
--
-- 定理: 对任意 f : Fin N → Fin N 和 x0 : Fin N,
--       orbit f x0 最终周期, 且 period ≤ N。
--
-- 证明思路:
--   1. 取前 N+1 个轨道元素: orbit f x0 0, ..., orbit f x0 N
--   2. 由鸽巢原理, 存在 i < j ≤ N 使得 orbit f x0 i ≡ orbit f x0 j
--   3. 因为 f 是确定性的, orbit f x0 (i+k) ≡ orbit f x0 (j+k) 对所有 k
--   4. 所以 start = i, period = j - i
--------------------------------------------------------------------------------

-- 辅助: 轨道碰撞后的等式传播
-- 若 orbit f x0 i ≡ orbit f x0 j, 则 orbit f x0 (i+k) ≡ orbit f x0 (j+k)
orbit-collision-propagates : {A : Set} (f : A → A) (x0 : A) (i j : ℕ) →
  orbit f x0 i ≡ orbit f x0 j →
  ∀ k → orbit f x0 (i + k) ≡ orbit f x0 (j + k)
orbit-collision-propagates f x0 i j eq zero rewrite +-identityʳ i | +-identityʳ j = eq
orbit-collision-propagates f x0 i j eq (suc k) rewrite +-suc i k | +-suc j k =
  cong f (orbit-collision-propagates f x0 i j eq k)

-- 算术辅助: i + k + (j ∸ i) ≡ j + k (当 i ≤ j)
arith-rearrange : ∀ i j k → i ≤ j → i + k + (j ∸ i) ≡ j + k
arith-rearrange i j k i≤j = trans
  (trans (cong (_+ (j ∸ i)) (+-comm i k))
         (+-assoc k i (j ∸ i)))
  (trans (cong (k +_) (m+[n∸m]≡n i≤j))
         (+-comm k j))

-- 主定理: Fin N 上任意函数的轨道最终周期
orbit-eventually-periodic : ∀ N → (f : Fin N → Fin N) → (x0 : Fin N) →
  EventuallyPeriodic (λ n → orbit f x0 n)
orbit-eventually-periodic zero    f ()
orbit-eventually-periodic (suc N) f x0 = record
  { start    = toℕ (proj₁ ph)
  ; period   = toℕ (proj₁ (proj₂ ph)) ∸ toℕ (proj₁ ph)
  ; periodic = λ k →
    trans (cong (λ n → orbit f x0 n)
              (arith-rearrange (toℕ (proj₁ ph)) (toℕ (proj₁ (proj₂ ph))) k
                (<⇒≤ (proj₁ (proj₂ (proj₂ ph))))))
          (sym (orbit-collision-propagates f x0 (toℕ (proj₁ ph)) (toℕ (proj₁ (proj₂ ph)))
            (proj₂ (proj₂ (proj₂ ph))) k))
  }
  where
    -- 鸽巢原理: suc N 个状态中取 suc (suc N) 个轨道元素, 必有碰撞
    ph : Σ (Fin (suc (suc N))) (λ i → Σ (Fin (suc (suc N))) (λ j →
           toℕ i < toℕ j × orbit f x0 (toℕ i) ≡ orbit f x0 (toℕ j)))
    ph = pigeonhole-fin (suc N) (λ idx → orbit f x0 (toℕ idx))

-- 周期上界: 对 Fin (suc N) 上的函数, 轨道周期 ≤ suc N
orbit-period-bound : ∀ N → (f : Fin (suc N) → Fin (suc N)) → (x0 : Fin (suc N)) →
  Σ ℕ (λ p → p ≤ suc N ×
    Σ ℕ (λ s → ∀ k → orbit f x0 (s + k + p) ≡ orbit f x0 (s + k)))
orbit-period-bound N f x0 =
  let ph = pigeonhole-fin (suc N) (λ idx → orbit f x0 (toℕ idx))
      i = proj₁ ph
      j = proj₁ (proj₂ ph)
      i<j = proj₁ (proj₂ (proj₂ ph))
      fi≡fj = proj₂ (proj₂ (proj₂ ph))
      p = toℕ j ∸ toℕ i
  in  (p , (≤-trans (m∸n≤m (toℕ j) (toℕ i)) (≤-pred (toℕ<n j)) ,
       (toℕ i , λ k → trans
         (cong (λ n → orbit f x0 n) (arith-rearrange (toℕ i) (toℕ j) k (<⇒≤ i<j)))
         (sym (orbit-collision-propagates f x0 (toℕ i) (toℕ j) fi≡fj k)))))

--------------------------------------------------------------------------------
-- §4a'. 逐点碰撞传播（用于无 funExt 的函数值状态空间）
--
-- 若 at (orbit f x0 i) ≡ at (orbit f x0 j)，且 at 对 f 的迭代保持相等
-- （即 at (f s) ≡ at (f t) 当 at s ≡ at t），则后续迭代的观察值也相等。
--------------------------------------------------------------------------------

orbit-collision-pw : ∀ {A B : Set} (f : A → A) (at : A → B) (x0 : A) (i j : ℕ)
  → (∀ s t → at s ≡ at t → at (f s) ≡ at (f t))
  → at (orbit f x0 i) ≡ at (orbit f x0 j)
  → ∀ k → at (orbit f x0 (i + k)) ≡ at (orbit f x0 (j + k))
orbit-collision-pw f at x0 i j step-eq eq zero rewrite +-identityʳ i | +-identityʳ j = eq
orbit-collision-pw f at x0 i j step-eq eq (suc k) rewrite +-suc i k | +-suc j k =
  step-eq (orbit f x0 (i + k)) (orbit f x0 (j + k))
          (orbit-collision-pw f at x0 i j step-eq eq k)
