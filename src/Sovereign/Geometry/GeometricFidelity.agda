{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Geometry.GeometricFidelity
-- QUAD.T2 几何极保真度判定：指名投影逐条量保真度（24 号文档 :97 任务）
--
-- 数学背景:
--   24-four-poles-vs-presentation-group.md:97 的 T2 任务:
--     「∥_∥₂ 截断后是否保留相位区分（同轨道、相位不同的路径 α vs α³
--       是否被识别为同一证明）；若不能保留 ⇒ 改用已存在的 set quotient
--       （T6.agda:960）；并须处理它与 φ-respects（:976-977 postulate）的关系」
--   判据第②层（非忠实商截断）: memory/crt-wave-physics-not-modular-arithmetic.md
--   范数坍缩: docs/duodecimal/10 —— N : GF(9)× → GF(3)× 的核 = ⟨α⟩ ≅ C₄
--
-- 判定（先算后验证: oracle 全域 9/9, norm(α)=norm(α³)=1 且 α≠α³）:
--   范数型读法（galoisNorm）**不保相位** —— 否定档: 不存在保单位单射（无损往返）。
--   逻辑强度按 24 号 :83 分档:
--     正档（存在性无损）= 本源层 alphaPowerToGF9 单射（展示层相位保真）;
--     否定档（不存在单射）= 本模块 norm-not-injective。
--   落地建议（24 号指示）: 「识别」职责改用已存在的 set quotient
--     T6╱A4（T6.agda:960）; 其与 φ-respects（T6:976-977 postulate）的
--     相容性 = 商等价生成元与截断见证的相容, 留待人类裁决（journal 已记）。
module Sovereign.Geometry.GeometricFidelity where

open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using (GF9; galoisNorm)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (AlphaPower; alphaPowerToGF9; alphaPowerToGF9-injective)

-- 相位对（GF9 二元组形, 具名钉类型）: α 与 α³ = -α
αg : GF9
αg = (T₀ , T₁)

α3g : GF9
α3g = (T₀ , T₂)

phase-pair-distinct : αg ≢ α3g
phase-pair-distinct ()

-- 范数坍缩见证: 异相位、同范数
norm-collapse : galoisNorm αg ≡ galoisNorm α3g
norm-collapse = refl

-- T2 判定 · 否定档: 范数型投影不存在保单位单射（无损往返）
norm-not-injective : ¬ (∀ x y → galoisNorm x ≡ galoisNorm y → x ≡ y)
norm-not-injective inj = phase-pair-distinct (inj αg α3g norm-collapse)

-- T2 判定 · 构造性见证: 同范数、异相位的点对
t2-phase-collapse :
  Σ GF9 (λ x → Σ GF9 (λ y → (x ≢ y) × (galoisNorm x ≡ galoisNorm y)))
t2-phase-collapse = αg , (α3g , (phase-pair-distinct , norm-collapse))

-- T2 判定 · 正档对照: 本源层（展示层）相位保真
--   相位区分活在 C₄ 纤维（α 的 90° 旋转）, 经 alphaPowerToGF9 嵌入无损
presentation-phase-faithful : ∀ a b → alphaPowerToGF9 a ≡ alphaPowerToGF9 b → a ≡ b
presentation-phase-faithful = alphaPowerToGF9-injective

-- 结论:
--   ① 范数型读法（galoisNorm/∥·∥₂ 范数）: 相位维保真度 = 0（否定档 + 见证）;
--   ② 本源层 C₄ 纤维: 相位保真（正档, 无损往返）;
--   ③ 「识别同轨道不同相位」的职责 ⇒ 改用 set quotient T6╱A4（T6:960）,
--      其与 φ-respects（T6:976-977 postulate）的相容性待人类裁决。
