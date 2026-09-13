{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.DCSigmaAut
-- σ_DC 是 DC 展示群的群自同构 — Frobenius 诱导的相位取逆保持乘性/单位/逆元
--
-- 数学背景:
--   GF(9) 的 Frobenius 自同构 σ(x) = x³ 在乘法子群 ⟨α⟩ ≅ C₄ 上诱导
--     σ(α) = α³ = α⁻¹   （因 α⁴ = 1，故 α³ = α⁻¹）
--   DC = Trit × AlphaPower 是加乘联合时钟（加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩）。
--   σ_DC(t, αᵏ) = (t, α⁻ᵏ) 保留幅度分量、仅在相位分量取逆，构成 DC 的**群自同构**:
--     · sigmaDC-homo: σ_DC(x·y) ≡ σ_DC(x)·σ_DC(y)    （乘性）
--     · sigmaDC-e   : σ_DC(e)   ≡ e                    （单位保持）
--     · sigmaDC-inv : σ_DC(x⁻¹) ≡ σ_DC(x)⁻¹            （逆元保持）
--   与 DCGroup 已有的 sigmaDC-involution（σ² = id）合起来即 σ_DC ∈ Aut(DC)。
--   Aut 的基数 4 有库内投影层锚点: DuodecClockProperties §8「Aut(DuodecClock) ≅ V₄」
--   （经 toDuodec 落到 Z/12 抽象层，φ(12) = 4）；σ_DC 是其中只翻相位、不动幅度的那个。
--
-- 核心原则:
--   1. 复用优先（侦察纪律）: 相位分量的乘性就是 DuodecClock.rho-alphaInv-homo
--      （16 case 已证），**一行复用**；不重证 144 case 的 DC 全表。
--   2. 幅度分量因 σ_DC 不动 t 而**定义相等**，直接 refl 闭合（定义相等 ≠ 命题相等）。
--   3. 相位不可约: σ_DC 只作用于相位 C₄，禁止约化为 {±1}（C₄→C₂ 非忠实）。
--   4. 未来态锚定: 直接锁定 RHS = mixedOp (sigmaDC p) (sigmaDC q) 的分量形式，
--      不从 LHS 逐项剥离。
--   5. 0 postulate / 0 hole / 0 sorry。
--
-- 包含: sigmaDC 的群同态性（乘性 / 单位 / 逆元）+ 具体点对抗验证

module Sovereign.Algebra.GroupTheory.DCSigmaAut where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Sovereign.Base.Trit using (T₀; T₁; T₂)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (mixedOp; duodec-e; duodec-inv; a1; a3; rho-alphaInv-homo)
open import Sovereign.Algebra.GroupTheory.DCGroup using (sigmaDC)

--------------------------------------------------------------------------------
-- §1. σ_DC 保持乘性
--------------------------------------------------------------------------------

-- σ_DC (p · q) ≡ σ_DC p · σ_DC q
-- 分量分解: 幅度分量 p₁ ⊕ q₁ 两侧定义相同（σ_DC 不动 t）→ refl；
--           相位分量即 rho-alphaInv-homo（alphaInv 保持 mulAlpha）。
sigmaDC-homo : ∀ p q →
  sigmaDC (mixedOp p q) ≡ mixedOp (sigmaDC p) (sigmaDC q)
sigmaDC-homo (x , a) (y , b) = cong₂ _,_ refl (rho-alphaInv-homo a b)

--------------------------------------------------------------------------------
-- §2. σ_DC 保持单位元
--------------------------------------------------------------------------------

-- σ_DC e ≡ e，因 e = (T₀, a0) 且 alphaInv a0 = a0（定义相等）
sigmaDC-e : sigmaDC duodec-e ≡ duodec-e
sigmaDC-e = refl

--------------------------------------------------------------------------------
-- §3. σ_DC 保持逆元
--------------------------------------------------------------------------------

-- σ_DC (p⁻¹) ≡ (σ_DC p)⁻¹
-- 两侧皆归约为 (negate x, alphaInv (alphaInv a))（定义相等）
sigmaDC-inv : ∀ p →
  sigmaDC (duodec-inv p) ≡ duodec-inv (sigmaDC p)
sigmaDC-inv (x , a) = refl

--------------------------------------------------------------------------------
-- §4. 对抗验证（具体点独立 refl 计算，不引用上面的定理）
--     发现论证空洞的唯一可靠手段: 具体实例与定理实例必须逐点一致。
--------------------------------------------------------------------------------

-- 混合点: p = (T₁, a1) = (1, α), q = (T₂, a3) = (2, α³)
-- LHS: σ((1,α)·(2,α³)) = σ(T₀, a0) = (T₀, a0)
-- RHS: (1,α⁻¹)·(2,α⁻³) = (1,a3)·(2,a1) = (T₀, a0)  ✓
sigmaDC-homo-check-mixed :
  sigmaDC (mixedOp (T₁ , a1) (T₂ , a3)) ≡
  mixedOp (sigmaDC (T₁ , a1)) (sigmaDC (T₂ , a3))
sigmaDC-homo-check-mixed = refl

-- 逆元点: p = (T₂, a1) = (2, α)
-- LHS: σ((2,α)⁻¹) = σ(T₁, a3) = (T₁, a1)
-- RHS: (σ(2,α))⁻¹ = (2, a3)⁻¹ = (T₁, a1)  ✓
sigmaDC-inv-check :
  sigmaDC (duodec-inv (T₂ , a1)) ≡ duodec-inv (sigmaDC (T₂ , a1))
sigmaDC-inv-check = refl

-- 单位点: σ(e) = σ(T₀, a0) = (T₀, a0) = e  ✓
sigmaDC-e-check : sigmaDC duodec-e ≡ duodec-e
sigmaDC-e-check = refl
