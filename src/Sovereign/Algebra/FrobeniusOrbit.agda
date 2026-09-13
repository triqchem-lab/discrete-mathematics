{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FrobeniusOrbit
--
-- GF(9) 的 Frobenius 自同构 σ 的轨道结构（展示群实例层）。
--
-- 定位（与 Sovereign.Analysis.FiniteDynamics 的分工）:
--   Analysis.FiniteDynamics = **通用**生成机制: orbit / 鸽巢碰撞 / collision-pw
--   本模块                  = **具体展示群实例**: σ acting on GF(9)
--
-- ⚠ 归位说明（重构落点）: 这些 GF9 专用内容原先住在通用模块
--   `Analysis.FiniteDynamics` 里（该模块头还写着「GF9 Frobenius 动力学」），
--   属层级错位——通用机制不应承载具体域。本模块即该重构的归位落点：
--   通用件留在 Analysis，具体域实例归 Algebra。依赖方向 Algebra → Analysis
--   与库内既有先例一致（`Algebra.IterationTheory` 亦如此）。
--
-- 展示群八要素（本模块实例）:
--   载体   : GF(9) = GF(3)[α]/(α²+1)，9 个元素 a + bα
--   生成元 : σ = galoisConjugate（Frobenius x ↦ x³）: a + bα ↦ a − bα
--   关系   : σ² = id（galoisConjugate²）
--   相位   : α 的幂给出 C₄ 相位（AlphaPower），σ 翻转其第二分量
--   时钟   : frobenius-orbit = orbit σ —— **迭代过程**，不是静态标签
--   归零   : σ-轨道周期 = 2 ⇒ σ² 归零；GF(9) 上任意函数周期 ≤ 9（鸽巢）
--   刚性   : Gal(GF(9)/GF(3)) ≅ C₂，σ 是唯一非平凡自同构
--   核对   : refl 只确认定义自洽，不产生结构
--
-- 核心结论:
--   · 所有 σ-轨道周期 ≤ 2（σ² = id），远优于鸽巢给出的 ≤ 9
--   · 不动点恰是 GF(3) 嵌入像（第二分量 b = T₀）: frobenius-fixed-iff
--   · 非 GF(3) 元素恰落在 2-周期轨道上: frobenius-nontrivial-orbit
--
-- 零 postulate、零 hole。
module Sovereign.Algebra.FrobeniusOrbit where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; +-suc; <⇒≤; ≤-trans; ≤-pred; m∸n≤m)
open import Data.Fin using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using (GF9; galoisConjugate; galoisConjugate²; embed-gf3)
open import Sovereign.Analysis.FiniteDynamics using
  (orbit; EventuallyPeriodic; pigeonhole-fin; orbit-collision-propagates; arith-rearrange)

--------------------------------------------------------------------------------
-- §1. σ 的轨道（时钟过程）
--
-- f = galoisConjugate = σ: a+bα ↦ a-bα
-- σ² = id（由 galoisConjugate² 证明）
-- 所有轨道周期 ≤ 2
-- 不动点 = GF(3) 元素（b = T₀）
-- 2-周期轨道 = 非 GF(3) 元素（b ≠ T₀）
--------------------------------------------------------------------------------

-- Frobenius 轨道: σ 的迭代
frobenius-orbit : GF9 → ℕ → GF9
frobenius-orbit = orbit galoisConjugate

-- |核心定理：σ² = id ⇒ 所有轨道周期 ≤ 2
frobenius-orbit-period : ∀ (x : GF9) → orbit galoisConjugate x 2 ≡ x
frobenius-orbit-period x = galoisConjugate² x

-- |推论：σ 的轨道以 2 为周期（从第 0 步开始）
frobenius-eventually-periodic : ∀ (x : GF9) →
  EventuallyPeriodic (orbit galoisConjugate x)
frobenius-eventually-periodic x = record
  { start    = 0
  ; period   = 2
  ; periodic = λ k → frobenius-periodic-k x k
  }
  where
    -- 对所有 k，σ^(k+2)(x) ≡ σ^k(x)
    frobenius-periodic-k : ∀ x k → orbit galoisConjugate x (0 + k + 2) ≡ orbit galoisConjugate x (0 + k)
    frobenius-periodic-k x zero    = galoisConjugate² x
    frobenius-periodic-k x (suc k) = cong galoisConjugate (frobenius-periodic-k x k)

--------------------------------------------------------------------------------
-- §2. 刚性：不动点刻画
--------------------------------------------------------------------------------

-- |正向：GF(3) 嵌入元素都是不动点
frobenius-fixed-point : ∀ (a : Trit) → galoisConjugate (embed-gf3 a) ≡ embed-gf3 a
frobenius-fixed-point a = refl

-- |逆向：若 σ(x) ≡ x，则 x 的虚部为 T₀（即 x 落在 GF(3) 嵌入像内）
frobenius-fixed-iff : ∀ x → galoisConjugate x ≡ x →
  Σ Trit (λ a → x ≡ embed-gf3 a)
frobenius-fixed-iff (a , T₀) eq = a , refl
frobenius-fixed-iff (a , T₁) eq = ⊥-elim (T₂≢T₁ (cong proj₂ eq))
  where T₂≢T₁ : T₂ ≡ T₁ → ⊥
        T₂≢T₁ ()
frobenius-fixed-iff (a , T₂) eq = ⊥-elim (T₁≢T₂ (cong proj₂ eq))
  where T₁≢T₂ : T₁ ≡ T₂ → ⊥
        T₁≢T₂ ()

-- |2-周期轨道：非 GF(3) 元素满足 σ(x) ≢ x（虚部非零）
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
-- §3. GF(9) 上的周期上界（鸽巢）
--
-- GF(9) 有 9 个元素，由鸽巢原理，任意 f : GF9 → GF9 的轨道周期 ≤ 9。
-- 对 Frobenius σ，周期精确为 ≤ 2（由 σ² = id），见 §4。
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

-- |编码往返：fin9-to-gf9 ∘ gf9-to-fin9 = id（9 case refl ⇒ 有限穷举完备）
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

-- |GF9 上任意函数的轨道周期 ≤ 9（鸽巢原理的直接推论）
gf9-orbit-period-bound : ∀ (f : GF9 → GF9) (x0 : GF9) →
  Σ ℕ (λ p → p ≤ 9 ×
    Σ ℕ (λ s → ∀ k → orbit f x0 (s + k + p) ≡ orbit f x0 (s + k)))
gf9-orbit-period-bound f x0 =
  let -- 将轨道编码为 Fin 9 序列，取前 10 个元素
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

--------------------------------------------------------------------------------
-- §4. 刚性的精确上界
--------------------------------------------------------------------------------

-- |Frobenius 的精确周期上界：≤ 2（远优于鸽巢给出的 ≤ 9）
frobenius-period-tight : ∀ x → orbit galoisConjugate x 2 ≡ x
frobenius-period-tight = frobenius-orbit-period
