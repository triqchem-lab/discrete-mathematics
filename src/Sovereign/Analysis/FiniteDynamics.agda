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

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate; negate²)
open import Sovereign.Algebra.GF9 using (
  GF9; galoisConjugate; galoisConjugate²; embed-gf3; gf9-one; alpha)

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
-- §5. GF(9) 上的 Frobenius 动力系统
--
-- f = galoisConjugate = σ: a+bα ↦ a-bα
-- σ² = id (由 galoisConjugate² 证明)
-- 所有轨道周期 ≤ 2
-- 不动点 = GF(3) 元素 (b = T₀)
-- 2-周期轨道 = 非 GF(3) 元素 (b ≠ T₀)
--------------------------------------------------------------------------------

-- Frobenius 轨道: σ 的迭代
frobenius-orbit : GF9 → ℕ → GF9
frobenius-orbit = orbit galoisConjugate

-- 核心定理: σ² = id → 所有轨道周期 ≤ 2
frobenius-orbit-period : ∀ (x : GF9) → orbit galoisConjugate x 2 ≡ x
frobenius-orbit-period x = galoisConjugate² x

-- 推论: σ 的轨道以 2 为周期 (从第 0 步开始)
frobenius-eventually-periodic : ∀ (x : GF9) →
  EventuallyPeriodic (orbit galoisConjugate x)
frobenius-eventually-periodic x = record
  { start    = 0
  ; period   = 2
  ; periodic = λ k → frobenius-periodic-k x k
  }
  where
    -- 对所有 k, σ^(k+2)(x) ≡ σ^k(x)
    frobenius-periodic-k : ∀ x k → orbit galoisConjugate x (0 + k + 2) ≡ orbit galoisConjugate x (0 + k)
    frobenius-periodic-k x zero    = galoisConjugate² x
    frobenius-periodic-k x (suc k) = cong galoisConjugate (frobenius-periodic-k x k)

-- 不动点刻画: σ(x) ≡ x 当且仅当 x 是 GF(3) 嵌入 (b = T₀)
frobenius-fixed-point : ∀ (a : Trit) → galoisConjugate (embed-gf3 a) ≡ embed-gf3 a
frobenius-fixed-point a = refl

-- 不动点逆: 若 σ(x) ≡ x, 则 x 的虚部为 T₀
frobenius-fixed-iff : ∀ x → galoisConjugate x ≡ x →
  Σ Trit (λ a → x ≡ embed-gf3 a)
frobenius-fixed-iff (a , T₀) eq = a , refl
frobenius-fixed-iff (a , T₁) eq = ⊥-elim (T₂≢T₁ (cong proj₂ eq))
  where T₂≢T₁ : T₂ ≡ T₁ → ⊥
        T₂≢T₁ ()
frobenius-fixed-iff (a , T₂) eq = ⊥-elim (T₁≢T₂ (cong proj₂ eq))
  where T₁≢T₂ : T₁ ≡ T₂ → ⊥
        T₁≢T₂ ()

-- 2-周期轨道: 非 GF(3) 元素的轨道恰好周期为 2
-- 即 σ(x) ≢ x (虚部非零)
frobenius-nontrivial-orbit : ∀ (a b : Trit) → b ≢ T₀ →
  galoisConjugate (a , b) ≢ (a , b)
frobenius-nontrivial-orbit a T₀ b≢T₀ = ⊥-elim (b≢T₀ refl)
frobenius-nontrivial-orbit a T₁ b≢T₀ eq = T₂≢T₁ (cong proj₂ eq)
  where T₂≢T₁ : T₂ ≡ T₁ → ⊥
        T₂≢T₁ ()
frobenius-nontrivial-orbit a T₂ b≢T₀ eq = T₁≢T₂ (cong proj₂ eq)
  where T₁≢T₂ : T₁ ≡ T₂ → ⊥
        T₁≢T₂ ()

--------------------------------------------------------------------------------
-- §6. GF(9) 上的周期上界
--
-- GF(9) 有 9 个元素, 由鸽巢原理, 任意 f : GF9 → GF9 的轨道周期 ≤ 9。
-- 对 Frobenius σ, 周期精确为 ≤ 2 (由 σ² = id)。
--------------------------------------------------------------------------------

-- GF9 与 Fin 9 之间的编码
gf9-to-fin9 : GF9 → Fin 9
gf9-to-fin9 (T₀ , T₀) = fzero
gf9-to-fin9 (T₀ , T₁) = fsuc fzero
gf9-to-fin9 (T₀ , T₂) = fsuc (fsuc fzero)
gf9-to-fin9 (T₁ , T₀) = fsuc (fsuc (fsuc fzero))
gf9-to-fin9 (T₁ , T₁) = fsuc (fsuc (fsuc (fsuc fzero)))
gf9-to-fin9 (T₁ , T₂) = fsuc (fsuc (fsuc (fsuc (fsuc fzero))))
gf9-to-fin9 (T₂ , T₀) = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
gf9-to-fin9 (T₂ , T₁) = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
gf9-to-fin9 (T₂ , T₂) = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))

fin9-to-gf9 : Fin 9 → GF9
fin9-to-gf9 fzero                                        = T₀ , T₀
fin9-to-gf9 (fsuc fzero)                                 = T₀ , T₁
fin9-to-gf9 (fsuc (fsuc fzero))                          = T₀ , T₂
fin9-to-gf9 (fsuc (fsuc (fsuc fzero)))                   = T₁ , T₀
fin9-to-gf9 (fsuc (fsuc (fsuc (fsuc fzero))))            = T₁ , T₁
fin9-to-gf9 (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))     = T₁ , T₂
fin9-to-gf9 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = T₂ , T₀
fin9-to-gf9 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = T₂ , T₁
fin9-to-gf9 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = T₂ , T₂

-- 编码往返: fin9-to-gf9 ∘ gf9-to-fin9 = id (9 case refl)
gf9-fin9-roundtrip : ∀ x → fin9-to-gf9 (gf9-to-fin9 x) ≡ x
gf9-fin9-roundtrip (T₀ , T₀) = refl
gf9-fin9-roundtrip (T₀ , T₁) = refl
gf9-fin9-roundtrip (T₀ , T₂) = refl
gf9-fin9-roundtrip (T₁ , T₀) = refl
gf9-fin9-roundtrip (T₁ , T₁) = refl
gf9-fin9-roundtrip (T₁ , T₂) = refl
gf9-fin9-roundtrip (T₂ , T₀) = refl
gf9-fin9-roundtrip (T₂ , T₁) = refl
gf9-fin9-roundtrip (T₂ , T₂) = refl

-- GF9 上任意函数的轨道周期 ≤ 9 (鸽巢原理的直接推论)
gf9-orbit-period-bound : ∀ (f : GF9 → GF9) (x0 : GF9) →
  Σ ℕ (λ p → p ≤ 9 ×
    Σ ℕ (λ s → ∀ k → orbit f x0 (s + k + p) ≡ orbit f x0 (s + k)))
gf9-orbit-period-bound f x0 =
  let -- 将轨道编码为 Fin 9 序列, 取前 10 个元素
      seq-fin : Fin 10 → Fin 9
      seq-fin idx = gf9-to-fin9 (orbit f x0 (toℕ idx))
      ph = pigeonhole-fin 9 seq-fin
      i = proj₁ ph
      j = proj₁ (proj₂ ph)
      i<j = proj₁ (proj₂ (proj₂ ph))
      fi≡fj = proj₂ (proj₂ (proj₂ ph))
      p = toℕ j ∸ toℕ i
      -- 从 Fin 9 碰撞恢复 GF9 等式
      gf9-eq : orbit f x0 (toℕ i) ≡ orbit f x0 (toℕ j)
      gf9-eq = trans (sym (gf9-fin9-roundtrip (orbit f x0 (toℕ i))))
               (trans (cong fin9-to-gf9 fi≡fj)
                      (gf9-fin9-roundtrip (orbit f x0 (toℕ j))))
  in  (p , (≤-trans (m∸n≤m (toℕ j) (toℕ i)) (≤-pred (toℕ<n j)) ,
       (toℕ i , λ k → trans
         (cong (λ n → orbit f x0 n) (arith-rearrange (toℕ i) (toℕ j) k (<⇒≤ i<j)))
         (sym (orbit-collision-propagates f x0 (toℕ i) (toℕ j) gf9-eq k)))))

-- Frobenius 的精确周期上界: ≤ 2 (远优于鸽巢给出的 ≤ 9)
frobenius-period-tight : ∀ x → orbit galoisConjugate x 2 ≡ x
frobenius-period-tight = frobenius-orbit-period
