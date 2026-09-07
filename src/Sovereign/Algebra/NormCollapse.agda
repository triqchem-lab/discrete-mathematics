{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.NormCollapse
-- 范数坍缩代数 — 共轭积坍缩 (相位乘法信息丢失)
--
-- 语料锚 (仅直觉映射, 非定理):
--   "1²+i²=0²" → GF(9) 出生证明 (不可约式 x²+1=0, 域内加法: 1²+α²=0)
--   "3²+4²=5²" → ℤ/ℝ 整数勾股 (连续统侧, 本库不判定其成立与否)
-- 核心定理内容:
--   范数 N(x) = x·σ(x) 把共轭对投射到 GF(3), 是乘法同态 GF(9)^× → GF(3)^×
--   核 ker N = ⟨α⟩ ≅ C₄: 相位子群 {1,α,α²,α³} 坍缩到范数值 T₁ — 相位信息 4→1 丢失
--
-- 零幂族 (Zero Power Family):
--   0² 不是"零的平方", 而是"零的二次幂 = 零"。
--   零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
--   出生证明 1²+α²=0² 中的 0² 是零幂族语义。
--
-- 本模块汇聚 GF9.agda 中已证的范数定理，并精确标注坍缩语义。
-- 不重复证明，只做结构化汇聚。
--
-- 0 postulate.

module Sovereign.Algebra.NormCollapse where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.GF9
  using ( GF9; gf9-zero; gf9-one; alpha; _*gf9_; _+gf9_
        ; galoisConjugate; galoisNorm; embed-gf3
        ; norm-conj-mul; galoisNorm-conjugate
        ; norm-mul
        )

--------------------------------------------------------------------------------
-- §1. 范数坍缩核心: N(x) = x·σ(x)
--------------------------------------------------------------------------------

-- 范数定义: N(a+bα) = a²+b² ∈ GF(3)
norm-formula : GF9 → Trit
norm-formula = galoisNorm

-- 坍缩恒等式: embed(N(x)) = x * σ(x)
-- 即: 共轭积坍缩到 GF(3) 基座
norm-collapse : ∀ x → embed-gf3 (galoisNorm x) ≡ x *gf9 galoisConjugate x
norm-collapse = norm-conj-mul

-- 范数保乘: N(xy) = N(x)·N(y)
norm-multiplicative : ∀ x y → galoisNorm (x *gf9 y) ≡ galoisNorm x ⊗ galoisNorm y
norm-multiplicative = norm-mul

-- 范数共轭不变: N(σ(x)) = N(x)
norm-conjugate-invariant : ∀ x → galoisNorm (galoisConjugate x) ≡ galoisNorm x
norm-conjugate-invariant = galoisNorm-conjugate

--------------------------------------------------------------------------------
-- §2. 勾股投影: N(a+bα) = a²+b²
--------------------------------------------------------------------------------

-- 数学定位 (精确):
--   galoisNorm : GF9 → GF3, N(a+bα) = a²⊕b². 作为加法群映射值域 = {0,1,2} = GF(3).
--   ★ 范数坍缩 = 相位乘法信息丢失, 而非否定 ℤ 整数等式:
--     作为乘法群同态 N : GF(9)^× → GF(3)^×, 核 ker N = ⟨α⟩ ≅ C₄.
--     四个相位元 {1, α, α², α³} 同像到 T₁ (norm-is-one) — 4→1 相位信息坍缩.
--     故"勾股关系"若在 GF(9)^× 相位结构内表述 (a,b,c ∈ 乘法群, 关系 = 范数相等),
--     在相位信息下不成立 — 这是范数坍缩的内容.
--   ⚠️ 不是: "整数 9+16=25 为假" (那是 ℤ 连续统侧事实, 与本模块无关, 见下).

-- 具体实例 (全部 refl):
norm-1-0 : galoisNorm (T₁ , T₀) ≡ T₁  -- N(1) = 1²+0² = 1
norm-1-0 = refl

norm-0-1 : galoisNorm (T₀ , T₁) ≡ T₁  -- N(α) = 0²+1² = 1
norm-0-1 = refl

norm-1-1 : galoisNorm (T₁ , T₁) ≡ T₂  -- N(1+α) = 1²+1² = 2
norm-1-1 = refl

norm-1-2 : galoisNorm (T₁ , T₂) ≡ T₂  -- N(φ) = 1²+2² = 1+1 = 2 (mod 3)
norm-1-2 = refl

-- 语料锚对应 (仅作直觉映射, 不是定理):
-- "1²+i²=0²" → alpha-squared : α² = -1 (GF9 出生, 域内加法)
-- "3²+4²=5²" → ℤ/ℝ 整数勾股, 是 N(3+4i)=25 的实数投影 — 属连续统, 本库不形式化其成立与否
--   本库形式化的是: 范数坍缩 N : GF(9)^× → GF(3)^× 的核 = ⟨α⟩, 相位信息 4→1 丢失

--------------------------------------------------------------------------------
-- §3. 出生证明: 1²+α²=0
--------------------------------------------------------------------------------

-- 在 GF(9) 中: 1²+α² = 1+(-1) = 0
-- 这是范数坍缩的特殊情况: N(1+α) = 1²+1² = 2, 但 1²+α² = 0 (域内加法)
-- 语料 "1²+i²=0²" 的精确形式化

-- α² = -1 (已证, 这里仅汇聚引用)
alpha-squared-is-neg-one : alpha *gf9 alpha ≡ (T₂ , T₀)
alpha-squared-is-neg-one = refl

-- 1² + α² = 0² (在 GF(9) 中: 三个都是平方!)
-- ⚠️ 语料原文用复数 i, 我们用 α (GF(9) 生成元, 不是复数 i)
-- 这是 GF(9) 的出生证明: 不可约式 x²+1=0 无根 → 扩张为域
-- 不是勾股定理! 3²+4²=5² 才是范数坍缩 (下方 §2)
-- 0² 是零幂族: 零的二次幂 = 零 (零吸收一切幂次, 零是唯一能跨维度的元素)
-- 结构性声明: 乘法单位元的平方 + 生成元的平方 = 零的平方
birth-proof : (gf9-one *gf9 gf9-one) +gf9 (alpha *gf9 alpha) ≡ gf9-zero *gf9 gf9-zero
birth-proof = refl

-- 0 postulate.
