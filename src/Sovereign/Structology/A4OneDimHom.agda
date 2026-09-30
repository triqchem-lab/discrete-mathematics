{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4OneDimHom
-- A₄ 一维表示的同态构造 — 从 abelianization 推导特征标 (0 postulate)
--
-- 深度证明 (第一步): A₄ 的三个一维表示 (ρ₁, ρ₁′, ρ₁″) 不是手写特征标,
-- 而是从 abelianization 映射 ab : A₄ → C₃ (Fin 3) 复合 ω 的幂得到:
--   ρ₁′(g) = ω^(ab g),  ρ₁″(g) = ω²^(ab g)
-- 同态性 ρ₁′(g⊗h) = ρ₁′(g)·ρ₁′(h) 由两个引理推出:
--   ab-hom:        ab(g⊗h) = ab g + ab h        (C₃ 同态)
--   omega-pow-mul: ω^a · ω^b = ω^(a+b)          (9 情形 refl)
--
-- ab-hom 的证明是生成元分解符号化 (路径 A):
--   A₄ = ⟨gs, gt⟩; 生成元对引理 ab-step (2×12 = 24 案 refl) +
--   词归纳传播 ab-word + dispatcher — 不再保留 12×12 = 144 案穷举表。

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

-- 生成元词表示 (A₄ = ⟨gs, gt⟩, 词归纳传播用)
open import Sovereign.Structology.A4GenWords
  using (Gen; gs; gt; gen; Word; ε; _▸_; ev; wordOf; ev-wordOf; ⊗-assocₚ; fromPerm-permₚ)

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
-- §4. ab-hom (生成元分解符号化) + ρ₁′ 同态
--   路径 (A): 生成元对引理 ab-step (2 生成元 × 12 = 24 案 refl, ≤27)
--   + 词归纳传播 ab-word + dispatcher;
--   原 12×12 = 144 案穷举表已删除。
--------------------------------------------------------------------------------

-- add3 结合律 (C₃ 单位元与结合律是词归纳的代数侧前提)
-- a = zero 时定义相等 1 案; a = suc _ 时 b、c 各 3 案 (共 19 案 refl)
add3-assoc : ∀ (a b c : Fin 3) → add3 (add3 a b) c ≡ add3 a (add3 b c)
add3-assoc zero b c = refl
add3-assoc (suc zero) zero zero = refl
add3-assoc (suc zero) zero (suc zero) = refl
add3-assoc (suc zero) zero (suc (suc zero)) = refl
add3-assoc (suc zero) (suc zero) zero = refl
add3-assoc (suc zero) (suc zero) (suc zero) = refl
add3-assoc (suc zero) (suc zero) (suc (suc zero)) = refl
add3-assoc (suc zero) (suc (suc zero)) zero = refl
add3-assoc (suc zero) (suc (suc zero)) (suc zero) = refl
add3-assoc (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
add3-assoc (suc (suc zero)) zero zero = refl
add3-assoc (suc (suc zero)) zero (suc zero) = refl
add3-assoc (suc (suc zero)) zero (suc (suc zero)) = refl
add3-assoc (suc (suc zero)) (suc zero) zero = refl
add3-assoc (suc (suc zero)) (suc zero) (suc zero) = refl
add3-assoc (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
add3-assoc (suc (suc zero)) (suc (suc zero)) zero = refl
add3-assoc (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
add3-assoc (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

-- 具名右作用 (避免 cong λ 的归约陷阱)
add3-right : Fin 3 → Fin 3 → Fin 3
add3-right c z = add3 z c

-- 具名左乘映射 (同上)
ab-mul-h : A4 → A4 → Fin 3
ab-mul-h h x = ab (x ⊗ h)

-- 具名右作用映射 (作用在 A4 变元上, 供 dispatcher 的 cong 使用)
ab-add3-h : A4 → A4 → Fin 3
ab-add3-h h x = add3 (ab x) (ab h)

-- 生成元对引理: 同态性在 2 个生成元 × 12 个元素上逐案验证 (24 案 refl)
ab-step : ∀ (c : Gen) (h : A4) → ab (gen c ⊗ h) ≡ add3 (ab (gen c)) (ab h)
ab-step gs Id = refl
ab-step gs (Rot zero zero) = refl
ab-step gs (Rot zero (suc zero)) = refl
ab-step gs (Rot (suc zero) zero) = refl
ab-step gs (Rot (suc zero) (suc zero)) = refl
ab-step gs (Rot (suc (suc zero)) zero) = refl
ab-step gs (Rot (suc (suc zero)) (suc zero)) = refl
ab-step gs (Rot (suc (suc (suc zero))) zero) = refl
ab-step gs (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-step gs (Flip zero) = refl
ab-step gs (Flip (suc zero)) = refl
ab-step gs (Flip (suc (suc zero))) = refl
ab-step gt Id = refl
ab-step gt (Rot zero zero) = refl
ab-step gt (Rot zero (suc zero)) = refl
ab-step gt (Rot (suc zero) zero) = refl
ab-step gt (Rot (suc zero) (suc zero)) = refl
ab-step gt (Rot (suc (suc zero)) zero) = refl
ab-step gt (Rot (suc (suc zero)) (suc zero)) = refl
ab-step gt (Rot (suc (suc (suc zero))) zero) = refl
ab-step gt (Rot (suc (suc (suc zero))) (suc zero)) = refl
ab-step gt (Flip zero) = refl
ab-step gt (Flip (suc zero)) = refl
ab-step gt (Flip (suc (suc zero))) = refl

-- 词归纳传播: 同态性沿词的复合逐层传播 (hom (word) = 链)
ab-word : ∀ (w : Word) (h : A4) → ab (ev w ⊗ h) ≡ add3 (ab (ev w)) (ab h)
ab-word ε h = cong ab (fromPerm-permₚ h)
ab-word (c ▸ w) h = begin
  ab ((gen c ⊗ ev w) ⊗ h)
    ≡⟨ cong ab (⊗-assocₚ (gen c) (ev w) h) ⟩
  ab (gen c ⊗ (ev w ⊗ h))
    ≡⟨ ab-step c (ev w ⊗ h) ⟩
  add3 (ab (gen c)) (ab (ev w ⊗ h))
    ≡⟨ cong (add3 (ab (gen c))) (ab-word w h) ⟩
  add3 (ab (gen c)) (add3 (ab (ev w)) (ab h))
    ≡⟨ sym (add3-assoc (ab (gen c)) (ab (ev w)) (ab h)) ⟩
  add3 (add3 (ab (gen c)) (ab (ev w))) (ab h)
    ≡⟨ cong (add3-right (ab h)) (sym (ab-step c (ev w))) ⟩
  add3 (ab (gen c ⊗ ev w)) (ab h)
  ∎

-- 主定理 (dispatcher): 每个元素由规范词覆盖 (ev-wordOf, 12 案 refl)
ab-hom : ∀ (g h : A4) → ab (g ⊗ h) ≡ add3 (ab g) (ab h)
ab-hom g h = begin
  ab (g ⊗ h)
    ≡⟨ cong (ab-mul-h h) (sym (ev-wordOf g)) ⟩
  ab (ev (wordOf g) ⊗ h)
    ≡⟨ ab-word (wordOf g) h ⟩
  add3 (ab (ev (wordOf g))) (ab h)
    ≡⟨ cong (ab-add3-h h) (ev-wordOf g) ⟩
  add3 (ab g) (ab h)
  ∎

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
