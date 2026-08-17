{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.BinaryTetrahedralIrreducibility
-- 2·A₄ = SL(2,3) 推导特征标不可约性重证: ⟨χ,χ⟩ = 1 (item 5, 0 postulate)
--
-- 核心原则:
--   ① 离散形式: ⟨χ,χ⟩ = (1/|G|) Σ_c |c|·χ(c)·χ̄(c) 不用有理数/浮点,
--      证明层锁其整数恒等式 ⟨χ,χ⟩·|G| = Σ ≡ 24 = |G| (⟨χ,χ⟩=1 ⟺ Σ=|G|·1)
--   ② 对象是「推导特征标」: χ₂ 由阶数导出 (DefiningRep),
--      χ₂′ = χ₂⊗χ₁′, χ₂″ = χ₂⊗χ₁″ 由张量积导出 (TwoDimTensors.chi2'-tensor)
--   ③ 全 refl 归约穷举 (7 类 × 3 特征标), Zω 算术闭值归约
--   ④ 命名层: 除法 24/24=1 的表述留在注释, 不进证明链
--
-- 包含: scaleZω/term/inner-num 定义, classSizes-sum (Σ|c|=24),
--       chi2-irreducible / chi2'-irreducible / chi2''-irreducible
--
-- 数值预验证: sov-math/sov-validation/src/chi_inner.rs (cargo test 通过)

module Sovereign.Structology.BinaryTetrahedralIrreducibility where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Representation
  using (Zω; mkZω; zeroZω; addZω; mulZω; conjZω)
open import Sovereign.Structology.BinaryTetrahedralRepresentation
  using (ConjClass2A4; classSize2A4; chi2-2A4; chi2'-2A4; chi2''-2A4)

--------------------------------------------------------------------------------
-- §1. 群阶: Σ_c |c| = 24
--------------------------------------------------------------------------------

classSizes-sum : 1 + 1 + 4 + 4 + 4 + 4 + 6 ≡ 24
classSizes-sum = refl

--------------------------------------------------------------------------------
-- §2. 内积分子: ⟨χ,χ⟩·|G| = Σ_c |c| · χ(c) · χ̄(c)
--------------------------------------------------------------------------------

-- 自然数标量倍 (重复加法)
scaleZω : ℕ → Zω → Zω
scaleZω Data.Nat.zero z = zeroZω
scaleZω (Data.Nat.suc n) z = addZω z (scaleZω n z)

-- 单个共轭类的贡献: |c| · χ(c) · χ̄(c)
term : (ConjClass2A4 → Zω) → ConjClass2A4 → Zω
term χ c = scaleZω (classSize2A4 c) (mulZω (χ c) (conjZω (χ c)))

-- 7 个共轭类求和 (ConjClass2A4 = Fin 7 逐 case 展开)
inner-num : (ConjClass2A4 → Zω) → Zω
inner-num χ = addZω (term χ zero)
            (addZω (term χ (suc zero))
            (addZω (term χ (suc (suc zero)))
            (addZω (term χ (suc (suc (suc zero))))
            (addZω (term χ (suc (suc (suc (suc zero)))))
            (addZω (term χ (suc (suc (suc (suc (suc zero))))))
                   (term χ (suc (suc (suc (suc (suc (suc zero))))))))))))

-- |G| 的 ℤ 嵌入
group-order : ℤ
group-order = + 24

--------------------------------------------------------------------------------
-- §3. 不可约性: ⟨χ,χ⟩ = 1 ⟺ 内积分子 ≡ |G|
--------------------------------------------------------------------------------

-- χ₂ (由阶数/特征值结构导出): [2,-2,-1,-1,1,1,0]
-- Σ = 1·4 + 1·4 + 4·1 + 4·1 + 4·1 + 4·1 + 6·0 = 24
chi2-irreducible : inner-num chi2-2A4 ≡ mkZω group-order (+ 0)
chi2-irreducible = refl

-- χ₂′ = χ₂⊗χ₁′ (张量积导出): [2,-2,-ω,-ω²,ω,ω²,0]
-- |χ|² = [4,4,1,1,1,1,0] (ω·ω̄ = ω·ω² = ω³ = 1), Σ = 24
chi2'-irreducible : inner-num chi2'-2A4 ≡ mkZω group-order (+ 0)
chi2'-irreducible = refl

-- χ₂″ = χ₂⊗χ₁″ (张量积导出): [2,-2,-ω²,-ω,ω²,ω,0], Σ = 24
chi2''-irreducible : inner-num chi2''-2A4 ≡ mkZω group-order (+ 0)
chi2''-irreducible = refl

-- 0 postulate.
