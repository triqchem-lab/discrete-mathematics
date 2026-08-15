{-# OPTIONS --rewriting #-}

-- | Sovereign.Physics.RightHandedNeutrinoTheorem
-- 右旋中微子定理 (0 postulate, 无洞)
--
-- 定理内容 (代数层, 全部 refl):
--   νL = α, νR = −α (GF(9) 中的共轭对), σ = Frobenius/伽罗瓦共轭 z ↦ z³
--   1. rightNeutrino-invisible   obs νR ≡ false — 右旋在可观测投影下不可见
--   2. leftNeutrino-visible      obs νL ≡ true  — 左旋可见
--   3. frobenius-swaps           σ(νL) ≡ νR    — Frobenius 交换左右旋
--   4. realOf-nuR-zero           Re(νR) ≡ 0    — 右旋实部为零 (纯虚)
--   5. conjugate-involutive-nuL  σ²(νL) ≡ νL   — 共轭对合
--   6. conjugate-orbit-single    σ(νL) ≡ νR 且 νL ≢ νR — 同一条伽罗瓦轨道的
--                                两个不同投影方向 (共轭对 ≠ 两个独立实体)
--   7. projection-complementary  两方向恰好一内一外 (可观测投影只取其一)
--
-- 诚实边界:
--   (a) 一切假设、理论、概念并存 — 无恒对理论。本模块不裁决任何物理理论
--       的正误; "νR 是可观测物理态还是投影幻象" 属于框架层解读, 与标准
--       模型 (跷跷板机制等) 构成互补描述而非替代关系。本模块证明的只是
--       代数内核: 共轭对由 Frobenius 原生给出 (无外源实体), 且选定的
--       可观测投影结构性地只看到其中一个方向。
--   (b) obs 通道的选择 (哪个方向"可见") 是物理输入 (知识库的"地球局域
--       投影"对应), 不是本模块的定理 — 定理在给定投影下全部刚性成立。
--   (c) 知识库的"13 个无形分型"、跷跷板机制的互补解读等为描述层对应,
--       记录于注释, 不以 postulate 占位。
--
-- 依赖: Algebra.GF9 (α² = −1, Gal(GF(9)/GF(3)) ≅ C₂, σ(α) = −α)。

module Sovereign.Physics.RightHandedNeutrinoTheorem where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using (GF9; alpha; galoisConjugate)

--------------------------------------------------------------------------------
-- §1. 左右旋态: 同一条伽罗瓦轨道上的两个投影方向
--------------------------------------------------------------------------------

-- 右旋基元 −α = 0 − 1·α (σ(α), 由 GF9.sigma-alpha 锁定)
neg-alpha : GF9
neg-alpha = (T₀ , T₂)

-- 左旋中微子态 (α 系数 = 1 的投影方向)
nuL : GF9
nuL = alpha

-- 右旋中微子候选态 (α 系数 = −1 ≡ 2 的投影方向)
nuR : GF9
nuR = neg-alpha

--------------------------------------------------------------------------------
-- §2. 可观测投影: 地球局域通道 (只对 α 系数 = 1 的"往外翻"方向敏感)
--------------------------------------------------------------------------------

-- Trit 等式检验 (0 postulate, 4 clause 穷举)
trit-eqᵇ : Trit → Trit → Bool
trit-eqᵇ T₀ T₀ = true
trit-eqᵇ T₁ T₁ = true
trit-eqᵇ T₂ T₂ = true
trit-eqᵇ _ _ = false

-- 可观测投影: α 系数是否为 1 (局域投影通道)
obs : GF9 → Bool
obs (a , b) = trit-eqᵇ b T₁

-- 实部投影 (实部观测通道)
realOf : GF9 → Trit
realOf (a , b) = a

--------------------------------------------------------------------------------
-- §3. 定理
--------------------------------------------------------------------------------

-- 定理 1: 右旋中微子在可观测投影下不可见
rightNeutrino-invisible : obs nuR ≡ false
rightNeutrino-invisible = refl

-- 定理 2: 左旋中微子在可观测投影下可见
leftNeutrino-visible : obs nuL ≡ true
leftNeutrino-visible = refl

-- 定理 3: Frobenius 共轭交换左右旋 (σ(α) = −α)
frobenius-swaps : galoisConjugate nuL ≡ nuR
frobenius-swaps = refl

-- 定理 4: 右旋候选态实部为零 (纯虚, 实部通道不可见)
realOf-nuR-zero : realOf nuR ≡ T₀
realOf-nuR-zero = refl

-- 定理 5: 共轭对合 (σ²(νL) = νL)
conjugate-involutive-nuL : galoisConjugate (galoisConjugate nuL) ≡ nuL
conjugate-involutive-nuL = refl

-- 定理 6: 共轭对是同一条伽罗瓦轨道的两个不同投影方向
-- (σ 交换两者 且 两者相异 — 共轭对不是两个独立实体)
conjugate-orbit-single : (galoisConjugate nuL ≡ nuR) × (nuL ≢ nuR)
conjugate-orbit-single = refl , λ ()

-- 定理 7: 两个投影方向恰好一内一外 (可观测投影只取其一)
projection-complementary : (obs nuL ≡ true) × (obs nuR ≡ false)
projection-complementary = refl , refl

-- 0 postulate.
