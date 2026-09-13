{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEFinalClosure
--
-- 离散 NSE 的**最终周期性闭合**：从展示群状态编码到有限动力学鸽巢引理。
--
-- 数学背景：
--   状态空间 PresField = Torus6 → DuodecPoint 是有限的（|Torus6| = 729,
--   |DuodecPoint| = 12）。故任何确定性演化 step : PresField → PresField
--   的轨道最终周期 —— 离散意义下的「无有限时间爆聚」。
--
-- 证明 DAG（评估报告 §3.3.2）：
--   阶段一 展示群分量编码（NSEPresentation §14/§15）：
--          compEnc + decodePt-encodePt : decodePt (encodePt x) ≡ x
--   阶段二 混合基数编码注入（Sovereign.Analysis.FinMixedRadix §3）：
--          enc12-inj-pointwise（基 12，递归界 N12）
--   阶段三 鸽巢 + 逐点传播（本模块 §3）
--
-- 陈述形式（诚实边界）：本库无 funExt（非 cubical），故周期性写成**逐点**形式
--   ∀ k x, orbit step ψ₀ (s+k+p) x ≡ orbit step ψ₀ (s+k) x
--   这是 EventuallyPeriodic 在函数值状态空间上唯一可行的形式。
--
-- 0 postulate / 0 hole。

module Sovereign.Problem.NavierStokes.NSEFinalClosure where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≤; n<1+n; m+[n∸m]≡n; +-comm; +-assoc; +-identityʳ; +-suc)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ-fromℕ<)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst)

open import Sovereign.Analysis.FiniteDynamics using (orbit; arith-rearrange; pigeonhole-fin)
open import Sovereign.Analysis.FinMixedRadix using (N12; enc12; enc12-inj-pointwise; suc≤12)
open import Sovereign.Analysis.PairEnc using (pairEnc; pairEnc-injective)
open import Sovereign.Problem.NavierStokes.NSEPresentation using
  (PresField; Torus6; Axis6; shiftAt; amp; ph; ext; compEnc; compEnc-injective;
   decodePt; encodePt; decodePt-encodePt)

--------------------------------------------------------------------------------
-- §1. 状态编码与逐点注入性
--------------------------------------------------------------------------------

stateCode : PresField → (Fin 729 → Fin 12)
stateCode ψ i = pairEnc (compEnc ψ (decodePt i))

stateCode-injective :
  ∀ {ψ φ : PresField} → (∀ i → stateCode ψ i ≡ stateCode φ i) → ∀ x → ψ x ≡ φ x
stateCode-injective {ψ} {φ} eq =
  compEnc-injective (λ x → pairEnc-injective (compEnc ψ x) (compEnc φ x) (key x))
  where
    key : ∀ x → pairEnc (compEnc ψ x) ≡ pairEnc (compEnc φ x)
    key x = trans (cong (λ z → pairEnc (compEnc ψ z)) (sym (decodePt-encodePt x)))
                  (trans (eq (encodePt x))
                         (cong (λ z → pairEnc (compEnc φ z)) (decodePt-encodePt x)))

-- 完整编码（自然数，避免 Fin 证明项卡住）
observe : PresField → ℕ
observe ψ = enc12 729 (stateCode ψ)

--------------------------------------------------------------------------------
-- §2. 状态空间大小
--------------------------------------------------------------------------------

STATE_DIM : ℕ
STATE_DIM = N12 729

--------------------------------------------------------------------------------
-- §3. 完整状态编码 → Fin N729 与逐点注入性
--
-- 用 C1 的严格界（FinMixedRadix.suc≤12 : suc (enc12 k f) ≤ 12 ^ k）直接构造
-- Fin 值，绕开「Fin (suc (N12 729)) 的证明项随函数变化」的对齐问题。
--
-- **界的抽象化（承重）**：界若写成字面量 12 ^ 729，鸽巢证明里的 any? 会对
-- Fin (12^729) 做枚举 —— 实测 346s 后 heap exhausted（exit 251, 8GB）；
-- 把界封成 abstract 常量后成为中性项、不归约，鸽巢只做符号推理（实测 2.8s, exit 0）。
-- 块内 refl 证 N729 ≡ 12 ^ 729，供块外用 subst 跨过不透明性。
--------------------------------------------------------------------------------

-- **双层抽象（承重）**：块内 refl 证 N729 ≡ 12 ^ 729；再把编码**连同其体**一起封装。
-- 体里含 `enc12 729` / `suc≤12 729`，一旦被展开就是 729 层展开
-- （实测：stateEnc 未封装 → P3 探针 >75s 超时；封装后与 postulate 编码同速）。
--------------------------------------------------------------------------------

abstract
  N729 : ℕ
  N729 = 12 ^ 729

  N729≡12^729 : N729 ≡ 12 ^ 729
  N729≡12^729 = refl

  stateEnc : PresField → Fin N729
  stateEnc ψ = fromℕ< {observe ψ} {12 ^ 729} (suc≤12 729 (stateCode ψ))

  toℕ-stateEnc : ∀ ψ → toℕ (stateEnc ψ) ≡ observe ψ
  toℕ-stateEnc ψ = toℕ-fromℕ< _

  stateEnc-injective-pw :
    ∀ {ψ φ : PresField} → stateEnc ψ ≡ stateEnc φ → ∀ x → ψ x ≡ φ x
  stateEnc-injective-pw {ψ} {φ} eq =
    stateCode-injective
      (enc12-inj-pointwise 729 (stateCode ψ) (stateCode φ)
        (trans (sym (toℕ-stateEnc ψ)) (trans (cong toℕ eq) (toℕ-stateEnc φ))))

--------------------------------------------------------------------------------
-- §4. 通用有限动力学引理（逐点形式，界 N 符号化）
--
-- **陈述修正（诚实边界）**：本库无 funExt，故
--   (a) 「编码注入」只能是逐点形式 enc s ≡ enc t → ∀ x, s x ≡ t x；
--   (b) 由此推进轨道还需要 step 的**逐点性**：
--       ∀ x, s x ≡ t x → ∀ x, step s x ≡ step t x。
--   缺 (b) 时命题在 MLTT 下不可证 —— 从逐点相等推出 step s ≡ step t 正是 funExt。
--   对具体的离散算子（逐点作用于邻域）(b) 可由 cong 直接给出，故这是
--   **陈述层的必要假设**，不是证明技巧。原注释版陈述（任意 step）为假命题候选。
--
-- **计算性边界**：N 符号化时证明项正常；实例化到 N = 12 ^ 729 后若强行归一化
--   鸽巢见证会枚举 12 ^ 729 个元素（不可行）。本定理是**存在性证明**，不是算法。
--------------------------------------------------------------------------------

finite-orbit-pw :
  ∀ {D B : Set} (N : ℕ) (enc : (D → B) → Fin N)
  → (∀ {s t : D → B} → enc s ≡ enc t → ∀ x → s x ≡ t x)
  → (step : (D → B) → D → B)
  → (∀ {s t : D → B} → (∀ x → s x ≡ t x) → ∀ x → step s x ≡ step t x)
  → (ψ₀ : D → B)
  → Σ ℕ (λ s → Σ ℕ (λ p → ∀ k x →
        orbit step ψ₀ (s + k + p) x ≡ orbit step ψ₀ (s + k) x))
finite-orbit-pw {D} {B} N enc enc-inj step step-pw ψ₀ =
  (toℕ i , (toℕ j ∸ toℕ i , periodic))
  where
    -- 鸽巢：Fin (suc N) 个轨道编码（即前 N+1 项）落入 Fin N，必有碰撞
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

    eq₀ : ∀ x → orbit step ψ₀ (toℕ i) x ≡ orbit step ψ₀ (toℕ j) x
    eq₀ = enc-inj code-eq

    -- 逐点碰撞传播：eq₀ 经 step 的逐点性沿轨道保持
    propagate : ∀ k x → orbit step ψ₀ (toℕ i + k) x ≡ orbit step ψ₀ (toℕ j + k) x
    propagate zero x rewrite +-identityʳ (toℕ i) | +-identityʳ (toℕ j) = eq₀ x
    propagate (suc k) x rewrite +-suc (toℕ i) k | +-suc (toℕ j) k =
      step-pw (propagate k) x

    periodic : ∀ k x →
      orbit step ψ₀ (toℕ i + k + (toℕ j ∸ toℕ i)) x ≡ orbit step ψ₀ (toℕ i + k) x
    periodic k x =
      trans (cong (λ n → orbit step ψ₀ n x)
                  (arith-rearrange (toℕ i) (toℕ j) k (<⇒≤ i<j)))
            (sym (propagate k x))

--------------------------------------------------------------------------------
-- §5. 最终定理：离散 NSE 状态空间的最终周期性（离散意义下的「无有限时间爆聚」）
--
-- 状态空间 PresField = Torus6 → DuodecPoint 有限（12 ^ 729），
-- 任意确定性演化 step 的轨道最终周期。
--------------------------------------------------------------------------------

nse-eventual-periodicity :
  (step : PresField → PresField)
  → (∀ {s t : PresField} → (∀ x → s x ≡ t x) → ∀ x → step s x ≡ step t x)
  → (ψ₀ : PresField)
  → Σ ℕ (λ s → Σ ℕ (λ p → ∀ k x →
        orbit step ψ₀ (s + k + p) x ≡ orbit step ψ₀ (s + k) x))
nse-eventual-periodicity step step-pw ψ₀ =
  finite-orbit-pw N729 stateEnc stateEnc-injective-pw step step-pw ψ₀

--------------------------------------------------------------------------------
-- §6. 具体实例：沿单轴的离散平移算子
--
-- 主定理是**条件式**的（需要 step 逐点）。若全库没有具体 step，定理就只是空转的
-- schema —— 本节补一个非平凡实例：沿第 0 轴的平移算子，其逐点性由
-- 「作用在邻域点上」直接给出（cong 都不需要）。
--------------------------------------------------------------------------------

axis0 : Axis6
axis0 = fzero

stepShift : PresField → PresField
stepShift ψ x = ψ (shiftAt axis0 x)

stepShift-pw : ∀ {s t : PresField} → (∀ x → s x ≡ t x) → ∀ x → stepShift s x ≡ stepShift t x
stepShift-pw eq x = eq (shiftAt axis0 x)

-- 具体实例：平移动力学的轨道最终周期
nse-shift-instance :
  (ψ₀ : PresField) → Σ ℕ (λ s → Σ ℕ (λ p → ∀ k x →
      orbit stepShift ψ₀ (s + k + p) x ≡ orbit stepShift ψ₀ (s + k) x))
nse-shift-instance = nse-eventual-periodicity stepShift stepShift-pw
