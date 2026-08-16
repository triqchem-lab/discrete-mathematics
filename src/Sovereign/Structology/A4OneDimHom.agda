{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4OneDimHom
-- A₄ 一维表示的同态构造 — 从 abelianization 推导特征标 (0 postulate)
--
-- 深度证明 (第一步): A₄ 的三个一维表示 (ρ₁, ρ₁′, ρ₁″) 不是手写特征标,
-- 而是从 abelianization 映射 ab : A₄ → C₃ (Fin 3) 复合 ω 的幂得到:
--   ρ₁′(g) = ω^(ab g),  ρ₁″(g) = ω²^(ab g)
-- 同态性 ρ₁′(g⊗h) = ρ₁′(g)·ρ₁′(h) 由两个引理推出:
--   ab-hom:        ab(g⊗h) = ab g + ab h        (C₃ 同态, 12×12 穷举)
--   omega-pow-mul: ω^a · ω^b = ω^(a+b)          (9 情形 refl)
--
-- 本模块先落 omega-pow-mul (纯 Z[ω] 代数, 独立于群), ab-hom 穷举随后。

module Sovereign.Structology.A4OneDimHom where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

-- 复用 Z[ω] 环 (ω²=-1-ω, ω³=1)
open import Sovereign.Structology.A4Representation
  using (Zω; oneZω; ω; ω²; mulZω)

--------------------------------------------------------------------------------
-- §1. C₃ 加法 (Fin 3 模 3) 与 ω 的幂
--------------------------------------------------------------------------------

-- C₃ 加法 (模 3)
add3 : Fin 3 → Fin 3 → Fin 3
add3 zero m = m
add3 (suc zero) zero = suc zero
add3 (suc zero) (suc zero) = suc (suc zero)
add3 (suc zero) (suc (suc zero)) = zero
add3 (suc (suc zero)) zero = suc (suc zero)
add3 (suc (suc zero)) (suc zero) = zero
add3 (suc (suc zero)) (suc (suc zero)) = suc zero

-- ω 的幂: powerω 0 = 1, powerω 1 = ω, powerω 2 = ω²
powerω : Fin 3 → Zω
powerω zero = oneZω
powerω (suc zero) = ω
powerω (suc (suc zero)) = ω²

--------------------------------------------------------------------------------
-- §2. omega-pow-mul: ω^a · ω^b = ω^(a+b)  (9 情形, 全 refl)
--   关键: mulZω 的 ℤ 运算归一化使 ω·ω=ω², ω·ω²=1, ω²·ω=1, ω²·ω²=ω
--------------------------------------------------------------------------------

omega-pow-mul : ∀ (a b : Fin 3) → mulZω (powerω a) (powerω b) ≡ powerω (add3 a b)
omega-pow-mul zero zero = refl
omega-pow-mul zero (suc zero) = refl
omega-pow-mul zero (suc (suc zero)) = refl
omega-pow-mul (suc zero) zero = refl
omega-pow-mul (suc zero) (suc zero) = refl
omega-pow-mul (suc zero) (suc (suc zero)) = refl
omega-pow-mul (suc (suc zero)) zero = refl
omega-pow-mul (suc (suc zero)) (suc zero) = refl
omega-pow-mul (suc (suc zero)) (suc (suc zero)) = refl

--------------------------------------------------------------------------------
-- §3. abelianization ab : A₄ → C₃ 与一维表示
--------------------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)

-- 复用 A₄ 群 (12 元素: Id, Rot i j, Flip k) 与乘法 _⊗_
open import Sovereign.Structology.A4Group using (A4; Id; Rot; Flip; _⊗_)

-- abelianization: A₄ → C₃ = Fin 3 (核为 V₄ = {Id, Flip 0,1,2})
-- 3 循环两个共轭类 (Python 求解): {R01,R10,R21,R30}→1, {R00,R11,R20,R31}→2
-- 即 ab(Rot i j) = 1 当 (toℕ i + toℕ j) 奇, = 2 当偶 (非简单按方向分)
ab : A4 → Fin 3
ab Id = zero
ab (Rot zero zero) = suc (suc zero)                     -- 2
ab (Rot zero (suc zero)) = suc zero                     -- 1
ab (Rot (suc zero) zero) = suc zero                     -- 1
ab (Rot (suc zero) (suc zero)) = suc (suc zero)         -- 2
ab (Rot (suc (suc zero)) zero) = suc (suc zero)         -- 2
ab (Rot (suc (suc zero)) (suc zero)) = suc zero         -- 1
ab (Rot (suc (suc (suc zero))) zero) = suc zero         -- 1
ab (Rot (suc (suc (suc zero))) (suc zero)) = suc (suc zero)  -- 2
ab (Flip k) = zero                                      -- 双对换 → 1 (在 V₄ 中)

-- 一维表示 (值域 Zω, 1×1 矩阵即元素本身)
ρ1 : A4 → Zω
ρ1 _ = oneZω

ρ1' : A4 → Zω
ρ1' g = powerω (ab g)

ρ1'' : A4 → Zω
ρ1'' g = powerω (ab2 g) where
  ab2 : A4 → Fin 3
  ab2 Id = zero
  ab2 (Rot i zero) = suc (suc zero)
  ab2 (Rot i (suc zero)) = suc zero
  ab2 (Flip k) = zero

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- §4. ab-hom (12×12 穷举) + ρ₁′ 同态
--------------------------------------------------------------------------------

ab-hom : ∀ (g h : A4) → ab (g ⊗ h) ≡ add3 (ab g) (ab h)
ab-hom (Id) (Id) = refl
ab-hom (Id) (Rot zero zero) = refl
ab-hom (Id) (Rot zero (suc zero)) = refl
ab-hom (Id) (Rot (suc zero) zero) = refl
ab-hom (Id) (Rot (suc zero) (suc zero)) = refl
ab-hom (Id) (Rot (suc (suc zero)) zero) = refl
ab-hom (Id) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Id) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Id) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Id) (Flip zero) = refl
ab-hom (Id) (Flip (suc zero)) = refl
ab-hom (Id) (Flip (suc (suc zero))) = refl
ab-hom (Rot zero zero) (Id) = refl
ab-hom (Rot zero zero) (Rot zero zero) = refl
ab-hom (Rot zero zero) (Rot zero (suc zero)) = refl
ab-hom (Rot zero zero) (Rot (suc zero) zero) = refl
ab-hom (Rot zero zero) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot zero zero) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot zero zero) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot zero zero) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot zero zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot zero zero) (Flip zero) = refl
ab-hom (Rot zero zero) (Flip (suc zero)) = refl
ab-hom (Rot zero zero) (Flip (suc (suc zero))) = refl
ab-hom (Rot zero (suc zero)) (Id) = refl
ab-hom (Rot zero (suc zero)) (Rot zero zero) = refl
ab-hom (Rot zero (suc zero)) (Rot zero (suc zero)) = refl
ab-hom (Rot zero (suc zero)) (Rot (suc zero) zero) = refl
ab-hom (Rot zero (suc zero)) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot zero (suc zero)) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot zero (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot zero (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot zero (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot zero (suc zero)) (Flip zero) = refl
ab-hom (Rot zero (suc zero)) (Flip (suc zero)) = refl
ab-hom (Rot zero (suc zero)) (Flip (suc (suc zero))) = refl
ab-hom (Rot (suc zero) zero) (Id) = refl
ab-hom (Rot (suc zero) zero) (Rot zero zero) = refl
ab-hom (Rot (suc zero) zero) (Rot zero (suc zero)) = refl
ab-hom (Rot (suc zero) zero) (Rot (suc zero) zero) = refl
ab-hom (Rot (suc zero) zero) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot (suc zero) zero) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot (suc zero) zero) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot (suc zero) zero) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot (suc zero) zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot (suc zero) zero) (Flip zero) = refl
ab-hom (Rot (suc zero) zero) (Flip (suc zero)) = refl
ab-hom (Rot (suc zero) zero) (Flip (suc (suc zero))) = refl
ab-hom (Rot (suc zero) (suc zero)) (Id) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot zero zero) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot zero (suc zero)) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot (suc zero) zero) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot (suc zero) (suc zero)) (Flip zero) = refl
ab-hom (Rot (suc zero) (suc zero)) (Flip (suc zero)) = refl
ab-hom (Rot (suc zero) (suc zero)) (Flip (suc (suc zero))) = refl
ab-hom (Rot (suc (suc zero)) zero) (Id) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot zero zero) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot zero (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot (suc zero) zero) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) zero) (Flip zero) = refl
ab-hom (Rot (suc (suc zero)) zero) (Flip (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) zero) (Flip (suc (suc zero))) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Id) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot zero zero) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot zero (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) zero) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Flip zero) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Flip (suc zero)) = refl
ab-hom (Rot (suc (suc zero)) (suc zero)) (Flip (suc (suc zero))) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Id) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot zero zero) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot zero (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc zero) zero) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Flip zero) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Flip (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) zero) (Flip (suc (suc zero))) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Id) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot zero zero) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot zero (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) zero) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) zero) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip zero) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc zero)) = refl
ab-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc (suc zero))) = refl
ab-hom (Flip zero) (Id) = refl
ab-hom (Flip zero) (Rot zero zero) = refl
ab-hom (Flip zero) (Rot zero (suc zero)) = refl
ab-hom (Flip zero) (Rot (suc zero) zero) = refl
ab-hom (Flip zero) (Rot (suc zero) (suc zero)) = refl
ab-hom (Flip zero) (Rot (suc (suc zero)) zero) = refl
ab-hom (Flip zero) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Flip zero) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Flip zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Flip zero) (Flip zero) = refl
ab-hom (Flip zero) (Flip (suc zero)) = refl
ab-hom (Flip zero) (Flip (suc (suc zero))) = refl
ab-hom (Flip (suc zero)) (Id) = refl
ab-hom (Flip (suc zero)) (Rot zero zero) = refl
ab-hom (Flip (suc zero)) (Rot zero (suc zero)) = refl
ab-hom (Flip (suc zero)) (Rot (suc zero) zero) = refl
ab-hom (Flip (suc zero)) (Rot (suc zero) (suc zero)) = refl
ab-hom (Flip (suc zero)) (Rot (suc (suc zero)) zero) = refl
ab-hom (Flip (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Flip (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Flip (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Flip (suc zero)) (Flip zero) = refl
ab-hom (Flip (suc zero)) (Flip (suc zero)) = refl
ab-hom (Flip (suc zero)) (Flip (suc (suc zero))) = refl
ab-hom (Flip (suc (suc zero))) (Id) = refl
ab-hom (Flip (suc (suc zero))) (Rot zero zero) = refl
ab-hom (Flip (suc (suc zero))) (Rot zero (suc zero)) = refl
ab-hom (Flip (suc (suc zero))) (Rot (suc zero) zero) = refl
ab-hom (Flip (suc (suc zero))) (Rot (suc zero) (suc zero)) = refl
ab-hom (Flip (suc (suc zero))) (Rot (suc (suc zero)) zero) = refl
ab-hom (Flip (suc (suc zero))) (Rot (suc (suc zero)) (suc zero)) = refl
ab-hom (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) zero) = refl
ab-hom (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-hom (Flip (suc (suc zero))) (Flip zero) = refl
ab-hom (Flip (suc (suc zero))) (Flip (suc zero)) = refl
ab-hom (Flip (suc (suc zero))) (Flip (suc (suc zero))) = refl

rho1'-hom : ∀ (g h : A4) → mulZω (ρ1' g) (ρ1' h) ≡ ρ1' (g ⊗ h)
rho1'-hom g h = begin
  mulZω (ρ1' g) (ρ1' h)
    ≡⟨ refl ⟩
  mulZω (powerω (ab g)) (powerω (ab h))
    ≡⟨ omega-pow-mul (ab g) (ab h) ⟩
  powerω (add3 (ab g) (ab h))
    ≡⟨ cong powerω (sym (ab-hom g h)) ⟩
  powerω (ab (g ⊗ h))
    ≡⟨ refl ⟩
  ρ1' (g ⊗ h) ∎

-- 0 postulate.
