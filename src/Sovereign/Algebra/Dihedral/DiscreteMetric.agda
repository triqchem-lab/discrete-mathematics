{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Dihedral.DiscreteMetric
-- 【重建 2026-09-07】原草稿含假定理 (frobeniusNorm-zero 的 ↔ 反向不成立:
--   frobeniusNorm (T₀,aₖ) 恒 = T₀ 但 (T₀,aₖ≠0) 非单位元; frobeniusNorm-multiplicative
--   对 (T₀,T₁) 等反例不成立), 且 Cayley 度量部分与 CayleyMetric 模块重叠。
--   本版重建为全真定理的聚焦模块: DC 的损益投影平方 ν(t,a)=t⊗t 的精确性质。
--   数学内容 (穷举核对):
--     · GF(3) 平方: 0²=0, 1²=1, 2²=4≡1 → ν 值域 ⊂ {T₀,T₁}
--     · ν(x)=T₀ ⟺ proj₁ x = T₀ (损益分量零)
--     · ν 不依赖相位分量 (纯损益投影)
--     · DC 上无 Frobenius 乘性 (与 GF9 域范数本质不同) — 见 §3
--
-- 核心原则:
--   1. DC = Trit × AlphaPower: 范数投影到损益分量平方, 相位分量不参与
--   2. ν 是"零检测": 值域 {T₀,T₁}, 无损分量 = 中性
--   3. 这与 GF9 的 galoisNorm (乘法群同态, 核=⟨α⟩) 是不同结构:
--      DC 是加法群, 无域乘法, 故无"相位坍缩到核"的乘性范数
--
-- 0 postulate, 0 hole. 全部定理逐 case 穷举 refl/构造。

module Sovereign.Algebra.Dihedral.DiscreteMetric where

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; mixedOp; duodec-e; duodec-inv; mulAlpha)

-- 逻辑等价 (本地, 双向蕴含)
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

--------------------------------------------------------------------------------
-- §1. 损益投影平方 (代数层)
--------------------------------------------------------------------------------

-- 定义: ν(t, αᵏ) = t² ∈ GF(3)   (纯损益投影, 相位不参与)
frobeniusNorm : DuodecPoint → Trit
frobeniusNorm (t , a) = t ⊗ t

-- GF(3) 平方值域: 0²=0, 1²=1, 2²=1 → ν ∈ {T₀, T₁}
-- 引理: t⊗t = T₀ ⟺ t = T₀ (逐 3 case)
trit-sq-zero : ∀ t → (t ⊗ t ≡ T₀) ↔ (t ≡ T₀)
trit-sq-zero T₀ = (λ _ → refl) , (λ _ → refl)
trit-sq-zero T₁ = (λ ()) , (λ ())
trit-sq-zero T₂ = (λ ()) , (λ ())

-- ν 值域 ⊂ {T₀,T₁}: 任何点的范数不是 T₀ 就是 T₁ (永非 T₂)
frobeniusNorm-range-2 : ∀ x → frobeniusNorm x ≡ T₀ ⊎ frobeniusNorm x ≡ T₁
frobeniusNorm-range-2 (T₀ , a) = inj₁ refl
frobeniusNorm-range-2 (T₁ , a) = inj₂ refl   -- 1⊗1 = T₁
frobeniusNorm-range-2 (T₂ , a) = inj₂ refl   -- 2⊗2 = 4 ≡ 1 (mod 3) = T₁

-- 范数值域存在 (对任意点, 有值)
frobeniusNorm-range : ∀ x → Σ Trit (λ t → frobeniusNorm x ≡ t)
frobeniusNorm-range x = frobeniusNorm x , refl

-- 零集特征: ν(x) = T₀ ⟺ 损益分量 = T₀ (中性)
-- 注意: 这不是"x ≡ duodec-e"! (T₀, a₁) 等纯相位点也 ν=0.
-- 原草稿的 frobeniusNorm-zero (声称 ⟺ x ≡ duodec-e) 是假定理, 本版修正.
frobeniusNorm-zero-char : ∀ x → (frobeniusNorm x ≡ T₀) ↔ (proj₁ x ≡ T₀)
frobeniusNorm-zero-char (t , a) = trit-sq-zero t

-- 相位无关: ν 只依赖损益分量, 不依赖相位
frobeniusNorm-phase-free : ∀ t a b → frobeniusNorm (t , a) ≡ frobeniusNorm (t , b)
frobeniusNorm-phase-free t a b = refl

-- 与单位元: ν(e) = T₀ (中性点范数零)
frobeniusNorm-unit : frobeniusNorm duodec-e ≡ T₀
frobeniusNorm-unit = refl

-- 纯相位点 (损益零) 全为范数零: (T₀,aₖ) 4 个点
frobeniusNorm-phase-points : ∀ a → frobeniusNorm (T₀ , a) ≡ T₀
frobeniusNorm-phase-points a = refl

--------------------------------------------------------------------------------
-- §2. 逆与范数: ν(x⁻¹) = ν(x)  (逐 12 case)
--------------------------------------------------------------------------------

-- 损益投影平方在取逆下不变 (因 negate t 的平方 = t 的平方: GF3 (-1)²=1,(-2)²=1)
frobeniusNorm-inv : ∀ x → frobeniusNorm (duodec-inv x) ≡ frobeniusNorm x
frobeniusNorm-inv (T₀ , a) = refl
frobeniusNorm-inv (T₁ , a) = refl   -- negate T₁ = T₂, T₂⊗T₂ = T₁ = T₁⊗T₁
frobeniusNorm-inv (T₂ , a) = refl

--------------------------------------------------------------------------------
-- §3. 与 GF9 范数的本质区别 (无乘性)
--------------------------------------------------------------------------------

-- DC 是加法群 (C₁₂), 无域乘法. 因此 frobeniusNorm 对 mixedOp 不乘性:
--   ν(x·y) = (t₁⊕t₂)² 而 ν(x)·ν(y) = t₁²·t₂², 一般不等 (例: x=(T₀,a1), y=(T₁,a0):
--   ν(x·y)=ν(T₁,a1)=(T₁)²=T₁, 但 ν(x)·ν(y)=T₀·T₁=T₀).
-- 这与 GF9 的 galoisNorm (乘法群同态 GF9^×→GF3^×, 核=⟨α⟩≅C₄) 是不同结构:
--   GF9 有域乘法才有"范数坍缩/相位信息 4→1 丢失"; DC 是加法群, 该结构不存在.
-- 本模块只承载 DC 的损益投影, 相位通道 (AlphaPower) 的坍缩分析属 GF9 层.

-- 无乘性的反例 (构造性): 存在 x y 使 ν(x·y) ≠ ν(x)·ν(y)
-- (用具体 x=(T₀,a1), y=(T₁,a0))
non-multiplicative-witness :
  Σ (DuodecPoint × DuodecPoint) (λ (x , y) →
    frobeniusNorm (mixedOp x y) ≢ frobeniusNorm x ⊗ frobeniusNorm y)
non-multiplicative-witness = ((T₀ , a1) , (T₁ , a0)) , (λ ())

--------------------------------------------------------------------------------
-- §4. 总结
--------------------------------------------------------------------------------

-- DC 的损益投影平方 ν(t,a) = t⊗t 是"零检测" (值域 {T₀,T₁}):
--   · ν(x)=T₀ ⟺ 损益分量中性
--   · 相位无关, 逆不变
--   · 无乘性 (DC 无域乘法, 与 GF9 galoisNorm 本质不同)
-- 离散字度量 (对称/三角) 属 CayleyMetric 模块, 本模块不做.
