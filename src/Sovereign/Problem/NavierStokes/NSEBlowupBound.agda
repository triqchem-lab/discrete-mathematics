{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEBlowupBound
-- 离散意义下的「无爆聚」：定义 + 定理 (闭合 NSEPhaseField 的 O3 第二半)
--
-- 背景: NSEPhaseField.agda:396-401 与 :541-549 把 O3 记为**立场而非定理**,
--   理由是「需要先定义『爆聚』在 729 格点上是什么」。本模块补上这个定义。
--
-- 定义 (离散爆聚的判据):
--   设状态空间为 S, 且 S 经 `enc : S → Fin N` **有限编码**
--   (库内 NS 已有: `NSEFinalClosure.stateEnc`)。称一个 ℕ-值可观察量
--   `h ∘ enc` **爆聚**, 若它在状态空间上**无界**:
--        爆聚(h)  ⇔  ¬ Σ ℕ (λ B → ∀ s → h (enc s) ≤ B)
--
-- 定理 (本模块):
--   **不存在**这样的可观察量 —— 任何 ℕ-值可观察量都有界。
--   理由是纯有限性: `Fin N` 只有 N 个元素, 逐个取最大即得界。
--   这与本框架的一贯立场一致: 离散基座上「无界增长」没有容身之处
--   (与 `NSE.T13.eventual-periodicity`「有限状态空间 ⇒ 最终周期」同源)。
--
-- 结构:
--   §1 有限有界引理 fin-bounded  (对 Fin n 归纳, 界 = 首元 + 其余界)
--   §2 主定理 no-discrete-blowup (经有限编码分解的可观察量有界)
--   §3 具体实例 phase-observable-bounded (单格点相位层 = C₄ 上 4 个取值, 直接举证)
--   §4 诚实边界 (本模块**不**声称什么)
--
-- ⚠ 诚实边界 (必读):
--   这是**离散类比**, 不是对连续统 Navier–Stokes 正则性问题的解答。
--   在连续统里「无界」可以由 ε→0 的无限细分产生, 而离散基座**没有**这个自由度
--   —— 这正是元诊断「连续统病态 / 离散自愈」的实例, 但它是**框架立场**,
--   不是本模块证明的数学命题。
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEBlowupBound where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m)

open import Sovereign.Algebra.GroupTheory.DuodecClock using (AlphaPower; a0; a1; a2; a3)

--------------------------------------------------------------------------------
-- §1. 有限有界引理
--
-- 对 `Fin n` 归纳: n = 0 时无元素(空模式); n = suc n 时把界取作
--   h 首元 + (其余 n 个元素的界)
-- 两个分支分别用 `m≤m+n` (首元) 与 `m≤n+m` (其余) 完成。
--------------------------------------------------------------------------------

fin-bounded : ∀ {n : ℕ} (h : Fin n → ℕ) → Σ ℕ (λ B → ∀ i → h i ≤ B)
fin-bounded {zero}  h = zero , (λ ())
fin-bounded {suc n} h = h fzero + B , body
  where
    ih : Σ ℕ (λ B → ∀ i → h (fsuc i) ≤ B)
    ih = fin-bounded {n} (λ i → h (fsuc i))

    B : ℕ
    B = proj₁ ih

    hb : ∀ i → h (fsuc i) ≤ B
    hb = proj₂ ih

    body : ∀ i → h i ≤ h fzero + B
    body fzero    = m≤m+n (h fzero) B
    body (fsuc i) = ≤-trans (hb i) (m≤n+m B (h fzero))

--------------------------------------------------------------------------------
-- §2. 主定理: 离散无爆聚
--
-- 任何「经有限状态编码分解」的可观察量都有界 —— 故按 §0 的定义,
-- 它**不是**爆聚。编码 `enc` 在库内 NS 侧已有实例 (`stateEnc : PresField → Fin N`)。
--------------------------------------------------------------------------------

no-discrete-blowup : ∀ {N : ℕ} {S : Set} (enc : S → Fin N) (h : Fin N → ℕ) →
  Σ ℕ (λ B → ∀ s → h (enc s) ≤ B)
no-discrete-blowup enc h = proj₁ (fin-bounded h) , (λ s → proj₂ (fin-bounded h) (enc s))

--------------------------------------------------------------------------------
-- §3. 具体实例: 单格点相位层 (C₄) 上的任意可观察量有界
--
-- 相位层只有 4 个取值, 故界可以**显式写出** (四元之和), 不需要 Fin 归纳。
-- 这是 NS 现场最贴近的义务: 相位值在其 4 档内, 不存在「相位爆聚」。
--------------------------------------------------------------------------------

phase-observable-bounded : ∀ (f : AlphaPower → ℕ) →
  Σ ℕ (λ B → ∀ a → f a ≤ B)
phase-observable-bounded f = f a0 + S₁ , body
  where
    -- 右嵌套, 与结论类型逐字对齐 (避免 + 的结合性不是定义性相等)
    S₁ : ℕ
    S₁ = f a1 + (f a2 + f a3)

    S₂ : ℕ
    S₂ = f a2 + f a3

    -- 链式比较: f a0 ≤ f a0 + S₁ ; f a1 ≤ S₁ ≤ f a0 + S₁ ;
    --           f a2 ≤ S₂ ≤ S₁ ≤ f a0 + S₁ ; f a3 ≤ S₂ ≤ S₁ ≤ f a0 + S₁
    body : ∀ a → f a ≤ f a0 + S₁
    body a0 = m≤m+n (f a0) S₁
    body a1 = ≤-trans (m≤m+n (f a1) S₂) (m≤n+m S₁ (f a0))
    body a2 = ≤-trans (≤-trans (m≤m+n (f a2) (f a3)) (m≤n+m S₂ (f a1)))
                      (m≤n+m S₁ (f a0))
    body a3 = ≤-trans (≤-trans (m≤n+m (f a3) (f a2)) (m≤n+m S₂ (f a1)))
                      (m≤n+m S₁ (f a0))

--------------------------------------------------------------------------------
-- §4. 诚实边界 (本模块不声称什么)
--
-- ✓ 已证 (构造性, 0 postulate / 0 hole):
--     fin-bounded               : Fin n 上任意 ℕ-值函数有界
--     no-discrete-blowup        : 经有限编码分解的可观察量有界 (⇒ 离散无爆聚)
--     phase-observable-bounded  : C₄ 相位层上任意 ℕ-值可观察量有界
--
-- ✗ 不声称:
--     ① 连续统 Navier–Stokes 的全局正则性 —— 本模块与它无关;
--     ② 「所以真实流体不爆聚」—— 从离散基座到连续统没有已建立的桥
--        (本框架明确不声称连续极限, 见 NSEPhaseField:420 的 O4);
--     ③ 本定理**不是** O3 的完整闭合: O3 要求的是「**给定的离散演化**下
--        不出现爆聚」, 本模块给的是「**任何**可观察量在任何演化下都有界」
--        —— 后者更强(因而更平凡), 它排除了「无界」这一形式, 但
--        没有刻画「物理意义的爆聚」(如局部密度峰值集中在演化中加剧)。
--        故 O3 仍**部分开放**: 剩余的是「爆聚」的**物理**判据, 而非有界性。
--------------------------------------------------------------------------------
