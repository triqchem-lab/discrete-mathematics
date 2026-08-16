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
ab : A4 → Fin 3
ab Id = zero
ab (Rot i zero) = suc zero            -- 正向 3 循环 → ω
ab (Rot i (suc zero)) = suc (suc zero)  -- 反向 3 循环 → ω²
ab (Flip k) = zero                    -- 双对换 → 1 (在 V₄ 交换子群中)

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
-- §4. ab-hom 与 ρ₁′ 同态 (下一轮: ab-hom 12×12 穷举 + rho1'-hom 结构证明)
--   声明留待 fill:
--   ab-hom : ∀ g h → ab (g ⊗ h) ≡ add3 (ab g) (ab h)
--   rho1'-hom : ∀ g h → mulZω (ρ1' g) (ρ1' h) ≡ ρ1' (g ⊗ h)
--     = omega-pow-mul (ab g) (ab h) ∘ cong powerω (sym (ab-hom g h))

-- 0 postulate.
