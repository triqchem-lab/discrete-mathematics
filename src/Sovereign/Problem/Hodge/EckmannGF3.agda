{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.EckmannGF3
-- 任务书第四层·4.2：Eckmann 离散 Hodge 定理（1944/45）的 GF(3) 退化核对
--
-- 数学背景：Eckmann, "Harmonische Funktionen und Randwertaufgaben in einem
--   Komplex"（Comment. Math. Helv. 17 (1944/45), 240–255）在有限复形上证明
--   Hodge 分解 C^k = im ∂ ⊕ im δ ⊕ ker L——但该分解**依赖正定内积**
--   （x·x = 0 ⟹ x = 0）。GF(3) 上内积失正定：存在 x ≢ 0 且 x·x = 0
--   （各向同性向量），正交直和分解的直和性随之失效。
--
-- 本模块把任务书 §4.2 的 ⚠ 修正（「⊕ 应为子空间和，不是直和」的根据）
-- 从注释级升为**类型级见证**：
--   ① 各向同性见证 isotropic = (1,1,1)：向量非零，self 内积 = 0（mod 3）；
--   ② 对照具体点：单位向量 self 内积非零（内积机制在工作，见证非定义空转）；
--   ③ 失正定的直接推论：inner x x = 0 不蕴含 x = 0（零化不判零）。
--
-- ⚠ 诚实边界：
--   1. 完整 Eckmann 分解 / 不分裂定理（im ∂₁ ∩ ker δ₀ ≠ 0 的链复形见证）
--      需要 ∂/δ 矩阵机件 —— 接 jac_Topology 边界矩阵，是 roadmap。
--   2. inner 的对称性是一般向量间的函数等式 —— 无 funext 不陈述（NSE.T15 纪律）；
--      具体点的对称性由 §3 的 refl 实例侧证。
--   3. 系数域锁定 GF(3)（Base/Trit 本源），不涉连续统内积。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.EckmannGF3 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; _⊕_; _⊗_)

--------------------------------------------------------------------------------
-- §1. GF(3) 3 维向量与内积
--------------------------------------------------------------------------------

V3 : Set
V3 = Fin 3 → Trit

zeroV : V3
zeroV _ = T₀

-- 标准内积：逐点 ⊗ 后 ⊕ 求和（GF(3) 加法）
inner : V3 → V3 → Trit
inner u v =
  (u fzero ⊗ v fzero) ⊕
  ((u (fsuc fzero) ⊗ v (fsuc fzero)) ⊕
   (u (fsuc (fsuc fzero)) ⊗ v (fsuc (fsuc fzero))))

-- 向量非零：某分量非零（逐点判零，无 funext 不做整体 ≢ 函数等式）
NonZero : V3 → Set
NonZero u =
  (u fzero ≢ T₀) ⊎
  ((u (fsuc fzero) ≢ T₀) ⊎ (u (fsuc (fsuc fzero)) ≢ T₀))

--------------------------------------------------------------------------------
-- §2. 主见证：GF(3) 内积失正定（Eckmann 修正的类型级根据）
--
-- isotropic = (1,1,1)：每分量 = 1 ≠ 0（向量非零），而 self 内积
--   1·1 ⊕ (1·1 ⊕ 1·1) = 1 ⊕ (1 ⊕ 1) = 1 ⊕ 2 = 0 (mod 3)。
-- 在正定内积下 x ≢ 0 ⟹ x·x ≠ 0 —— 此见证击穿之。
--------------------------------------------------------------------------------

isotropic : V3
isotropic _ = T₁

isotropic-nonzero : NonZero isotropic
isotropic-nonzero = inj₁ (λ ())

isotropic-null : inner isotropic isotropic ≡ T₀
isotropic-null = refl

-- 失正定的直接推论：self 内积为零不判零（反方向正是正定性的定义）
null-not-zero : Σ V3 (λ u → NonZero u × (inner u u ≡ T₀))
null-not-zero = isotropic , (isotropic-nonzero , isotropic-null)

--------------------------------------------------------------------------------
-- §3. 具体点对抗（对抗验证协议 §6）：内积机制在工作
--
-- 单位向量 self 内积 = T₁（非零）——证明见证不是「内积恒零」的定义空转；
-- 不同基向量内积 = T₀（正交特例）。
--------------------------------------------------------------------------------

e1 : V3
e1 fzero = T₁
e1 (fsuc _) = T₀

e2 : V3
e2 fzero = T₀
e2 (fsuc fzero) = T₁
e2 (fsuc (fsuc _)) = T₀

-- 非零具体点：inner e1 e1 = 1·1 ⊕ (0 ⊕ 0) = T₁
inner-e1-e1 : inner e1 e1 ≡ T₁
inner-e1-e1 = refl

-- 正交具体点：inner e1 e2 = 1·0 ⊕ (0·1 ⊕ 0·0) = T₀
inner-e1-e2 : inner e1 e2 ≡ T₀
inner-e1-e2 = refl

-- 非零性对照：e1 确实非零（见证不是拿零向量充数）
e1-nonzero : NonZero e1
e1-nonzero = inj₁ (λ ())

-- 对照定理：内积不恒零（存在取值 T₁ 的实例，与 §2 的 T₀ 实例并存）
inner-takes-nonzero : Σ V3 (λ u → inner u u ≡ T₁)
inner-takes-nonzero = e1 , inner-e1-e1
