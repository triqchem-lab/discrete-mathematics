{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.FiniteOrbitObs
-- 通用有限动力学引理的**观察值版**（NSEFinalClosure §4 的形态泛化）
--
-- 泛化点: `NSEFinalClosure.finite-orbit-pw` 处理 `D → B` 形状态（逐点 = 对定义域点）。
--   本模块把状态抽象为任意 `S`，逐点性换成**观察族** `obs : S → Idx → Obs`
--   （如 6 分量场的 `comp k v x`、或任意可观察值），得:
--
--   `finite-orbit-obs`：
--     给定 ① 注入编码 `enc : S → Fin N`（逐点形态: 编码相等 ⇒ 各观察值相等）；
--          ② step 的观察逐点性（观察值相等经 step 保持），
--     则任意初态的轨道**观察值序列最终周期**：
--       ∃ s p, ∀ k i → obs (orbit step ψ₀ (s + k + p)) i ≡ obs (orbit step ψ₀ (s + k)) i
--
-- 为何这样陈述（诚实边界, 承 NSEFinalClosure §4 的教训）: 本库无 funExt,
--   「状态相等」在函数值状态空间上不可达；**观察值层的最终周期是唯一可行形态**。
--   另注: 从逐点相等推进轨道还需要 step 的观察逐点性（缺之则命题在 MLTT 下不可证）。
--
-- 复用件（全部已证）: `FiniteDynamics.{orbit, arith-rearrange, pigeonhole-fin}`。
-- 0 postulate / 0 hole。

module Sovereign.Analysis.FiniteOrbitObs where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_)
open import Data.Nat.Properties using (<⇒≤; +-identityʳ; +-suc)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)

open import Sovereign.Analysis.FiniteDynamics using (orbit; arith-rearrange; pigeonhole-fin)

finite-orbit-obs :
  ∀ {S Idx Obs : Set} (N : ℕ) (enc : S → Fin N) (obs : S → Idx → Obs)
  → (∀ {s t : S} → enc s ≡ enc t → ∀ i → obs s i ≡ obs t i)
  → (step : S → S)
  → (∀ {s t : S} → (∀ i → obs s i ≡ obs t i) → ∀ i → obs (step s) i ≡ obs (step t) i)
  → (ψ₀ : S)
  → Σ ℕ (λ s → Σ ℕ (λ p → ∀ k i →
        obs (orbit step ψ₀ (s + k + p)) i ≡ obs (orbit step ψ₀ (s + k)) i))
finite-orbit-obs {S} {Idx} {Obs} N enc obs enc-inj step step-pw ψ₀ =
  (toℕ i , (toℕ j ∸ toℕ i , periodic))
  where
    -- 鸽巢：Fin (suc N) 个轨道编码（前 N+1 项）落入 Fin N，必有碰撞
    pigeon : Σ (Fin (suc N)) (λ a → Σ (Fin (suc N)) (λ b →
           toℕ a < toℕ b × enc (orbit step ψ₀ (toℕ a)) ≡ enc (orbit step ψ₀ (toℕ b))))
    pigeon = pigeonhole-fin N (λ idx → enc (orbit step ψ₀ (toℕ idx)))

    i : Fin (suc N)
    i = proj₁ pigeon
    j : Fin (suc N)
    j = proj₁ (proj₂ pigeon)
    i<j : toℕ i < toℕ j
    i<j = proj₁ (proj₂ (proj₂ pigeon))
    code-eq : enc (orbit step ψ₀ (toℕ i)) ≡ enc (orbit step ψ₀ (toℕ j))
    code-eq = proj₂ (proj₂ (proj₂ pigeon))

    eq₀ : ∀ q → obs (orbit step ψ₀ (toℕ i)) q ≡ obs (orbit step ψ₀ (toℕ j)) q
    eq₀ = enc-inj code-eq

    -- 观察值碰撞沿轨道传播（经 step 的观察逐点性）
    propagate : ∀ k q →
      obs (orbit step ψ₀ (toℕ i + k)) q ≡ obs (orbit step ψ₀ (toℕ j + k)) q
    propagate zero q rewrite +-identityʳ (toℕ i) | +-identityʳ (toℕ j) = eq₀ q
    propagate (suc k) q rewrite +-suc (toℕ i) k | +-suc (toℕ j) k =
      step-pw (propagate k) q

    periodic : ∀ k q →
      obs (orbit step ψ₀ (toℕ i + k + (toℕ j ∸ toℕ i))) q
      ≡ obs (orbit step ψ₀ (toℕ i + k)) q
    periodic k q =
      trans (cong (λ n → obs (orbit step ψ₀ n) q)
                  (arith-rearrange (toℕ i) (toℕ j) k (<⇒≤ i<j)))
            (sym (propagate k q))

--------------------------------------------------------------------------------
-- 诚实边界
--
-- ✓ 已证: `finite-orbit-obs`（通用观察值版最终周期；证明为 NSEFinalClosure §4 的
--   形态泛化, 同一鸽巢 + 传播结构）。
-- ✗ 不在此模块:
--   ① 具体状态空间的编码注入（如 NSEOnT6 的 6 分量 `Field`：需 4374 = 6×729 槽位的
--      混合基数编码 + `Fin 4374 ↔ Fin 6 × Torus6` 索引管道 + `Fin 3 ↪ Fin 12/19` 数字嵌入）
--      —— 零件大多已证（`FinMixedRadix.enc-inj-pointwise`、`PairEnc`、`decodePt/encodePt`），
--      缺的只是索引管道（下一段的第一件事）;
--   ② supportCount 轨道的无条件最终周期（由 ① + `NSESupportFixedInv.supportCount-ext`
--      一步给出）;
--   ③ 任何 funExt 依赖的结论（本库无 funExt，观察值层是唯一可行形态）。
--------------------------------------------------------------------------------
