{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.EntropySpinVerification
-- 渠玉芝量子熵理论的库内验证 (0 postulate, 无洞)
--
-- 依据已完成的库, 对熵旋定律的结构断言逐条验证:
--   V1 ρ_S^{μν} 反对称        — rho-antisym 应用于 S 场 (复用, §1)
--   V2 m=∮S·dA 旋度项消失     — massIntegral-curl-zero (复用, §1)
--   V3 ∇·S=0 熵旋守恒        — 本模块新证: divℚ (curlℚ Ψ) ≡ 0 (§2),
--                              与 divS-identity: divℚ S ≡ −∂z(κ·ℋ²·1) (§3)
--      ⇒ 修正公理文档的"无条件 ∇·S=0": 守恒 ⟺ ∂z(κ·ℋ²·1) = 0
--        (如 ℋ² 沿 z 常值)。divS-zero-condition 落链该条件形式。
--   V4 量子化 ∮S·dA = C·m₀  — 未验证: 已证 m ≡ −Σ[(κ·ℋ²)·1], 与
--      C·m₀ 的匹配需要额外假设 (m₀ 定义/陈数量子化), 诚实边界。
--
-- 验证方式: (Fin 3)³ 环面 + ℚ 系数, 全部符号证明; 无 funext
-- (构造子实例化 + 环律链, 与 EntropySpinLaw 同法)。

module Sovereign.Physics.EntropySpinVerification where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Integer using (ℤ; +_; -[1+_]; +0; +[1+_])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; -_; 0ℚ; 1ℚ)
open import Data.Rational.Base using (mkℚ)
open import Data.Rational.Properties
  using (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseʳ;
         neg-distrib-+; *-zeroʳ)
open import Sovereign.Physics.DiscreteEMField3D using (Point3D; next)
open import Sovereign.Physics.EntropySpinLaw

-- ℚ 双负 (stdlib 2.4 未导出; mkℚ 三情形 refl)
negneg : ∀ p → - (- p) ≡ p
negneg (mkℚ +0 d prf) = refl
negneg (mkℚ +[1+ n ] d prf) = refl
negneg (mkℚ -[1+ n ] d prf) = refl

--------------------------------------------------------------------------------
-- §1. V1/V2: 复用已证部分
--------------------------------------------------------------------------------

-- V1: 熵旋密度张量反对称, 对 S 场逐点成立 (直接引用)
v-rho-antisym : ∀ Ψ H p →
  rhoXY (entropySpinLaw Ψ H) p + rhoYX (entropySpinLaw Ψ H) p ≡ 0ℚ
v-rho-antisym Ψ H p = rho-antisym (entropySpinLaw Ψ H) p

-- V2: 质量积分旋度项消失 (引用) — m 只余 ℋ² 项
v-stokes : ∀ Ψ → massIntegral (curlℚ Ψ) ≡ 0ℚ
v-stokes Ψ = massIntegral-curl-zero Ψ

--------------------------------------------------------------------------------
-- §2. ℚ 场代数: 差分可加/负号/交换 + divℚ∘curlℚ = 0 (V3 前半)
--------------------------------------------------------------------------------

-- 差分可加性 (三坐标, 7 步 ℚ 环律链)
dxℚ-add : ∀ f g p → dxℚ (λ q → f q + g q) p ≡ dxℚ f p + dxℚ g p
dxℚ-add f g (i , j , k) = begin
  dxℚ (λ q → f q + g q) (i , j , k)
    ≡⟨ refl ⟩
  (f₊ + g₊) - (f₀ + g₀)
    ≡⟨ cong (λ t → (f₊ + g₊) + t) (neg-distrib-+ f₀ g₀) ⟩
  (f₊ + g₊) + ((- f₀) + (- g₀))
    ≡⟨ sym (+-assoc (f₊ + g₊) (- f₀) (- g₀)) ⟩
  ((f₊ + g₊) - f₀) - g₀
    ≡⟨ cong (λ t → t - g₀) (+-assoc f₊ g₊ (- f₀)) ⟩
  (f₊ + (g₊ - f₀)) - g₀
    ≡⟨ cong (λ t → (f₊ + t) - g₀) (+-comm g₊ (- f₀)) ⟩
  (f₊ + ((- f₀) + g₊)) - g₀
    ≡⟨ cong (λ t → t - g₀) (sym (+-assoc f₊ (- f₀) g₊)) ⟩
  ((f₊ - f₀) + g₊) - g₀
    ≡⟨ +-assoc (f₊ - f₀) g₊ (- g₀) ⟩
  (f₊ - f₀) + (g₊ - g₀)
    ≡⟨ refl ⟩
  dxℚ f (i , j , k) + dxℚ g (i , j , k) ∎
  where
  f₊ = f (next i , j , k)
  f₀ = f (i , j , k)
  g₊ = g (next i , j , k)
  g₀ = g (i , j , k)

dyℚ-add : ∀ f g p → dyℚ (λ q → f q + g q) p ≡ dyℚ f p + dyℚ g p
dyℚ-add f g (i , j , k) = begin
  dyℚ (λ q → f q + g q) (i , j , k)
    ≡⟨ refl ⟩
  (f₊ + g₊) - (f₀ + g₀)
    ≡⟨ cong (λ t → (f₊ + g₊) + t) (neg-distrib-+ f₀ g₀) ⟩
  (f₊ + g₊) + ((- f₀) + (- g₀))
    ≡⟨ sym (+-assoc (f₊ + g₊) (- f₀) (- g₀)) ⟩
  ((f₊ + g₊) - f₀) - g₀
    ≡⟨ cong (λ t → t - g₀) (+-assoc f₊ g₊ (- f₀)) ⟩
  (f₊ + (g₊ - f₀)) - g₀
    ≡⟨ cong (λ t → (f₊ + t) - g₀) (+-comm g₊ (- f₀)) ⟩
  (f₊ + ((- f₀) + g₊)) - g₀
    ≡⟨ cong (λ t → t - g₀) (sym (+-assoc f₊ (- f₀) g₊)) ⟩
  ((f₊ - f₀) + g₊) - g₀
    ≡⟨ +-assoc (f₊ - f₀) g₊ (- g₀) ⟩
  (f₊ - f₀) + (g₊ - g₀)
    ≡⟨ refl ⟩
  dyℚ f (i , j , k) + dyℚ g (i , j , k) ∎
  where
  f₊ = f (i , next j , k)
  f₀ = f (i , j , k)
  g₊ = g (i , next j , k)
  g₀ = g (i , j , k)

dzℚ-add : ∀ f g p → dzℚ (λ q → f q + g q) p ≡ dzℚ f p + dzℚ g p
dzℚ-add f g (i , j , k) = begin
  dzℚ (λ q → f q + g q) (i , j , k)
    ≡⟨ refl ⟩
  (f₊ + g₊) - (f₀ + g₀)
    ≡⟨ cong (λ t → (f₊ + g₊) + t) (neg-distrib-+ f₀ g₀) ⟩
  (f₊ + g₊) + ((- f₀) + (- g₀))
    ≡⟨ sym (+-assoc (f₊ + g₊) (- f₀) (- g₀)) ⟩
  ((f₊ + g₊) - f₀) - g₀
    ≡⟨ cong (λ t → t - g₀) (+-assoc f₊ g₊ (- f₀)) ⟩
  (f₊ + (g₊ - f₀)) - g₀
    ≡⟨ cong (λ t → (f₊ + t) - g₀) (+-comm g₊ (- f₀)) ⟩
  (f₊ + ((- f₀) + g₊)) - g₀
    ≡⟨ cong (λ t → t - g₀) (sym (+-assoc f₊ (- f₀) g₊)) ⟩
  ((f₊ - f₀) + g₊) - g₀
    ≡⟨ +-assoc (f₊ - f₀) g₊ (- g₀) ⟩
  (f₊ - f₀) + (g₊ - g₀)
    ≡⟨ refl ⟩
  dzℚ f (i , j , k) + dzℚ g (i , j , k) ∎
  where
  f₊ = f (i , j , next k)
  f₀ = f (i , j , k)
  g₊ = g (i , j , next k)
  g₀ = g (i , j , k)

-- 差分负号穿越 (三坐标, 3 步)
dxℚ-neg : ∀ f p → dxℚ (λ q → - f q) p ≡ - dxℚ f p
dxℚ-neg f (i , j , k) = begin
  dxℚ (λ q → - f q) (i , j , k)
    ≡⟨ refl ⟩
  (- f₊) - (- f (i , j , k))
    ≡⟨ sym (neg-distrib-+ f₊ (- f (i , j , k))) ⟩
  - (f₊ - f (i , j , k))
    ≡⟨ refl ⟩
  - dxℚ f (i , j , k) ∎
  where
  f₊ = f (next i , j , k)

dyℚ-neg : ∀ f p → dyℚ (λ q → - f q) p ≡ - dyℚ f p
dyℚ-neg f (i , j , k) = begin
  dyℚ (λ q → - f q) (i , j , k)
    ≡⟨ refl ⟩
  (- f₊) - (- f (i , j , k))
    ≡⟨ sym (neg-distrib-+ f₊ (- f (i , j , k))) ⟩
  - (f₊ - f (i , j , k))
    ≡⟨ refl ⟩
  - dyℚ f (i , j , k) ∎
  where
  f₊ = f (i , next j , k)

dzℚ-neg : ∀ f p → dzℚ (λ q → - f q) p ≡ - dzℚ f p
dzℚ-neg f (i , j , k) = begin
  dzℚ (λ q → - f q) (i , j , k)
    ≡⟨ refl ⟩
  (- f₊) - (- f (i , j , k))
    ≡⟨ sym (neg-distrib-+ f₊ (- f (i , j , k))) ⟩
  - (f₊ - f (i , j , k))
    ≡⟨ refl ⟩
  - dzℚ f (i , j , k) ∎
  where
  f₊ = f (i , j , next k)

-- 差分分配过减法: d(f − g) ≡ df − dg
dxℚ-sub : ∀ f g p → dxℚ (λ q → f q - g q) p ≡ dxℚ f p - dxℚ g p
dxℚ-sub f g p = trans (dxℚ-add f (λ q → - g q) p)
                       (cong (λ t → dxℚ f p + t) (dxℚ-neg g p))

dyℚ-sub : ∀ f g p → dyℚ (λ q → f q - g q) p ≡ dyℚ f p - dyℚ g p
dyℚ-sub f g p = trans (dyℚ-add f (λ q → - g q) p)
                       (cong (λ t → dyℚ f p + t) (dyℚ-neg g p))

dzℚ-sub : ∀ f g p → dzℚ (λ q → f q - g q) p ≡ dzℚ f p - dzℚ g p
dzℚ-sub f g p = trans (dzℚ-add f (λ q → - g q) p)
                       (cong (λ t → dzℚ f p + t) (dzℚ-neg g p))

-- 混合偏导交换 (三对, 11 步 ℚ 环律链)
dxdy-commℚ : ∀ f p → dxℚ (dyℚ f) p ≡ dyℚ (dxℚ f) p
dxdy-commℚ f (i , j , k) = begin
  dxℚ (dyℚ f) (i , j , k)
    ≡⟨ refl ⟩
  (c - d) - (a - b)
    ≡⟨ cong (λ t → (c - d) + t) (trans (neg-distrib-+ a (- b)) (cong (λ t → (- a) + t) (negneg b))) ⟩
  (c - d) + ((- a) + b)
    ≡⟨ sym (+-assoc (c - d) (- a) b) ⟩
  ((c - d) - a) + b
    ≡⟨ cong (λ t → t + b) (+-assoc c (- d) (- a)) ⟩
  (c + ((- d) - a)) + b
    ≡⟨ cong (λ t → t + b) (cong (λ t → c + t) (+-comm (- d) (- a))) ⟩
  (c + ((- a) - d)) + b
    ≡⟨ cong (λ t → t + b) (sym (+-assoc c (- a) (- d))) ⟩
  ((c - a) - d) + b
    ≡⟨ (+-assoc (c - a) (- d) b) ⟩
  (c - a) + ((- d) + b)
    ≡⟨ cong (λ t → (c - a) + t) (+-comm (- d) b) ⟩
  (c - a) + (b - d)
    ≡⟨ sym (trans (cong (λ t → (c - a) + t) (neg-distrib-+ d (- b)))
                  (trans (cong (λ t → (c - a) + ((- d) + t)) (negneg b))
                         (cong (λ t → (c - a) + t) (+-comm (- d) b)))) ⟩
  (c - a) - (d - b)
    ≡⟨ refl ⟩
  dyℚ (dxℚ f) (i , j , k) ∎
  where
  a = f (i , next j , k)
  b = f (i , j , k)
  c = f (next i , next j , k)
  d = f (next i , j , k)

dydz-commℚ : ∀ f p → dyℚ (dzℚ f) p ≡ dzℚ (dyℚ f) p
dydz-commℚ f (i , j , k) = begin
  dyℚ (dzℚ f) (i , j , k)
    ≡⟨ refl ⟩
  (c - d) - (a - b)
    ≡⟨ cong (λ t → (c - d) + t) (trans (neg-distrib-+ a (- b)) (cong (λ t → (- a) + t) (negneg b))) ⟩
  (c - d) + ((- a) + b)
    ≡⟨ sym (+-assoc (c - d) (- a) b) ⟩
  ((c - d) - a) + b
    ≡⟨ cong (λ t → t + b) (+-assoc c (- d) (- a)) ⟩
  (c + ((- d) - a)) + b
    ≡⟨ cong (λ t → t + b) (cong (λ t → c + t) (+-comm (- d) (- a))) ⟩
  (c + ((- a) - d)) + b
    ≡⟨ cong (λ t → t + b) (sym (+-assoc c (- a) (- d))) ⟩
  ((c - a) - d) + b
    ≡⟨ (+-assoc (c - a) (- d) b) ⟩
  (c - a) + ((- d) + b)
    ≡⟨ cong (λ t → (c - a) + t) (+-comm (- d) b) ⟩
  (c - a) + (b - d)
    ≡⟨ sym (trans (cong (λ t → (c - a) + t) (neg-distrib-+ d (- b)))
                  (trans (cong (λ t → (c - a) + ((- d) + t)) (negneg b))
                         (cong (λ t → (c - a) + t) (+-comm (- d) b)))) ⟩
  (c - a) - (d - b)
    ≡⟨ refl ⟩
  dzℚ (dyℚ f) (i , j , k) ∎
  where
  a = f (i , j , next k)
  b = f (i , j , k)
  c = f (i , next j , next k)
  d = f (i , next j , k)

dzdx-commℚ : ∀ f p → dzℚ (dxℚ f) p ≡ dxℚ (dzℚ f) p
dzdx-commℚ f (i , j , k) = begin
  dzℚ (dxℚ f) (i , j , k)
    ≡⟨ refl ⟩
  (c - d) - (a - b)
    ≡⟨ cong (λ t → (c - d) + t) (trans (neg-distrib-+ a (- b)) (cong (λ t → (- a) + t) (negneg b))) ⟩
  (c - d) + ((- a) + b)
    ≡⟨ sym (+-assoc (c - d) (- a) b) ⟩
  ((c - d) - a) + b
    ≡⟨ cong (λ t → t + b) (+-assoc c (- d) (- a)) ⟩
  (c + ((- d) - a)) + b
    ≡⟨ cong (λ t → t + b) (cong (λ t → c + t) (+-comm (- d) (- a))) ⟩
  (c + ((- a) - d)) + b
    ≡⟨ cong (λ t → t + b) (sym (+-assoc c (- a) (- d))) ⟩
  ((c - a) - d) + b
    ≡⟨ (+-assoc (c - a) (- d) b) ⟩
  (c - a) + ((- d) + b)
    ≡⟨ cong (λ t → (c - a) + t) (+-comm (- d) b) ⟩
  (c - a) + (b - d)
    ≡⟨ sym (trans (cong (λ t → (c - a) + t) (neg-distrib-+ d (- b)))
                  (trans (cong (λ t → (c - a) + ((- d) + t)) (negneg b))
                         (cong (λ t → (c - a) + t) (+-comm (- d) b)))) ⟩
  (c - a) - (d - b)
    ≡⟨ refl ⟩
  dxℚ (dzℚ f) (i , j , k) ∎
  where
  a = f (next i , j , k)
  b = f (i , j , k)
  c = f (next i , j , next k)
  d = f (i , j , next k)

-- 六项重排 (减法形式): (a−b)+((c−d)+(e−f)) ≡ (a−d)+((c−f)+(e−b))
six-rotateℚ : ∀ a b c d e f →
  (a - b) + ((c - d) + (e - f)) ≡ (a - d) + ((c - f) + (e - b))
six-rotateℚ a b c d e f = begin
  (a - b) + ((c - d) + (e - f))
    ≡⟨ cong (λ t → (a - b) + t) (merge4 c d e f) ⟩
  (a - b) + ((c + e) - (d + f))
    ≡⟨ merge4 a b (c + e) (d + f) ⟩
  (a + (c + e)) - (b + (d + f))
    ≡⟨ cong (λ t → t - (b + (d + f))) (sym (+-assoc a c e)) ⟩
  ((a + c) + e) - (b + (d + f))
    ≡⟨ +-assoc (a + c) e (- (b + (d + f))) ⟩
  (a + c) + (e + (- (b + (d + f))))
    ≡⟨ cong (λ t → (a + c) + t) (cong (λ t → e + t) (neg-distrib-+ b (d + f))) ⟩
  (a + c) + (e + ((- b) + (- (d + f))))
    ≡⟨ cong (λ t → (a + c) + t) (sym (+-assoc e (- b) (- (d + f)))) ⟩
  (a + c) + ((e - b) + (- (d + f)))
    ≡⟨ sym (+-assoc (a + c) (e - b) (- (d + f))) ⟩
  ((a + c) + (e - b)) + (- (d + f))
    ≡⟨ cong (λ t → t + (- (d + f))) (+-comm (a + c) (e - b)) ⟩
  ((e - b) + (a + c)) + (- (d + f))
    ≡⟨ +-assoc (e - b) (a + c) (- (d + f)) ⟩
  (e - b) + ((a + c) + (- (d + f)))
    ≡⟨ +-comm (e - b) ((a + c) + (- (d + f))) ⟩
  ((a + c) + (- (d + f))) + (e - b)
    ≡⟨ sym (cong (λ t → t + (e - b)) (merge4 a d c f)) ⟩
  ((a - d) + (c - f)) + (e - b)
    ≡⟨ +-assoc (a - d) (c - f) (e - b) ⟩
  (a - d) + ((c - f) + (e - b)) ∎

-- 成对抵消 (三对, 混合偏导交换 + 逆元)
pair-cancel-1ℚ : ∀ f p → dxℚ (dyℚ f) p - dyℚ (dxℚ f) p ≡ 0ℚ
pair-cancel-1ℚ f p = begin
  dxℚ (dyℚ f) p - dyℚ (dxℚ f) p
    ≡⟨ cong (λ t → t - dyℚ (dxℚ f) p) (dxdy-commℚ f p) ⟩
  dyℚ (dxℚ f) p - dyℚ (dxℚ f) p
    ≡⟨ +-inverseʳ (dyℚ (dxℚ f) p) ⟩
  0ℚ ∎

pair-cancel-2ℚ : ∀ f p → dyℚ (dzℚ f) p - dzℚ (dyℚ f) p ≡ 0ℚ
pair-cancel-2ℚ f p = begin
  dyℚ (dzℚ f) p - dzℚ (dyℚ f) p
    ≡⟨ cong (λ t → t - dzℚ (dyℚ f) p) (dydz-commℚ f p) ⟩
  dzℚ (dyℚ f) p - dzℚ (dyℚ f) p
    ≡⟨ +-inverseʳ (dzℚ (dyℚ f) p) ⟩
  0ℚ ∎

pair-cancel-3ℚ : ∀ f p → dzℚ (dxℚ f) p - dxℚ (dzℚ f) p ≡ 0ℚ
pair-cancel-3ℚ f p = begin
  dzℚ (dxℚ f) p - dxℚ (dzℚ f) p
    ≡⟨ cong (λ t → t - dxℚ (dzℚ f) p) (dzdx-commℚ f p) ⟩
  dxℚ (dzℚ f) p - dxℚ (dzℚ f) p
    ≡⟨ +-inverseʳ (dxℚ (dzℚ f) p) ⟩
  0ℚ ∎

-- 六项展开式归零 (six-rotateℚ + 三 pair-cancel)
six-zero' : ∀ Ψ p →
  (dxℚ (dyℚ (qz Ψ)) p - dxℚ (dzℚ (qy Ψ)) p)
    + ((dyℚ (dzℚ (qx Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
       + (dzℚ (dxℚ (qy Ψ)) p - dzℚ (dyℚ (qx Ψ)) p))
    ≡ 0ℚ
six-zero' Ψ p = begin
  (dxℚ (dyℚ (qz Ψ)) p - dxℚ (dzℚ (qy Ψ)) p)
    + ((dyℚ (dzℚ (qx Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
       + (dzℚ (dxℚ (qy Ψ)) p - dzℚ (dyℚ (qx Ψ)) p))
    ≡⟨ six-rotateℚ (dxℚ (dyℚ (qz Ψ)) p) (dxℚ (dzℚ (qy Ψ)) p)
                   (dyℚ (dzℚ (qx Ψ)) p) (dyℚ (dxℚ (qz Ψ)) p)
                   (dzℚ (dxℚ (qy Ψ)) p) (dzℚ (dyℚ (qx Ψ)) p) ⟩
  (dxℚ (dyℚ (qz Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
    + ((dyℚ (dzℚ (qx Ψ)) p - dzℚ (dyℚ (qx Ψ)) p)
       + (dzℚ (dxℚ (qy Ψ)) p - dxℚ (dzℚ (qy Ψ)) p))
    ≡⟨ cong₂ _+_
         (pair-cancel-1ℚ (qz Ψ) p)
         (cong₂ _+_ (pair-cancel-2ℚ (qx Ψ) p) (pair-cancel-3ℚ (qy Ψ) p)) ⟩
  0ℚ + (0ℚ + 0ℚ)
    ≡⟨ +-identityˡ 0ℚ ⟩
  0ℚ + 0ℚ
    ≡⟨ +-identityˡ 0ℚ ⟩
  0ℚ ∎

-- 原始 λ 形式六项归零 (三 sub 展开后引用 six-zero')
six-zero : ∀ Ψ p →
  dxℚ (λ q → dyℚ (qz Ψ) q - dzℚ (qy Ψ) q) p
    + (dyℚ (λ q → dzℚ (qx Ψ) q - dxℚ (qz Ψ) q) p
       + dzℚ (λ q → dxℚ (qy Ψ) q - dyℚ (qx Ψ) q) p)
    ≡ 0ℚ
six-zero Ψ p = begin
  dxℚ (λ q → dyℚ (qz Ψ) q - dzℚ (qy Ψ) q) p
    + (dyℚ (λ q → dzℚ (qx Ψ) q - dxℚ (qz Ψ) q) p
       + dzℚ (λ q → dxℚ (qy Ψ) q - dyℚ (qx Ψ) q) p)
    ≡⟨ cong₂ _+_
         (dxℚ-sub (dyℚ (qz Ψ)) (dzℚ (qy Ψ)) p)
         (cong₂ _+_
           (dyℚ-sub (dzℚ (qx Ψ)) (dxℚ (qz Ψ)) p)
           (dzℚ-sub (dxℚ (qy Ψ)) (dyℚ (qx Ψ)) p)) ⟩
  (dxℚ (dyℚ (qz Ψ)) p - dxℚ (dzℚ (qy Ψ)) p)
    + ((dyℚ (dzℚ (qx Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
       + (dzℚ (dxℚ (qy Ψ)) p - dzℚ (dyℚ (qx Ψ)) p))
    ≡⟨ six-zero' Ψ p ⟩
  0ℚ ∎

-- divℚ 与旋度核: divℚ (curlℚ A) ≡ 0 (熵旋守恒的旋度部分)
divℚ : QVector → QScalar
divℚ A p = dxℚ (qx A) p + (dyℚ (qy A) p + dzℚ (qz A) p)

divℚ-curl-zero : ∀ A p → divℚ (curlℚ A) p ≡ 0ℚ
divℚ-curl-zero A p = begin
  divℚ (curlℚ A) p
    ≡⟨ refl ⟩
  dxℚ (λ q → dyℚ (qz A) q - dzℚ (qy A) q) p
    + (dyℚ (λ q → dzℚ (qx A) q - dxℚ (qz A) q) p
       + dzℚ (λ q → dxℚ (qy A) q - dyℚ (qx A) q) p)
    ≡⟨ six-zero A p ⟩
  0ℚ ∎

--------------------------------------------------------------------------------
-- §3. V3 主定理: divℚ S ≡ −∂z(κ·ℋ²·1) — 守恒条件的修正形式
--------------------------------------------------------------------------------

-- S 场 (定律的显式分量形式, n̂=(0,0,1) 展开):
--   S = (dy qzΨ − dz qyΨ, dz qxΨ − dx qzΨ, dx qyΨ − dy qxΨ − (κ·ℋ²)·1)
S-field : QVector → QScalar → QVector
S-field Ψ H p =
  ( dyℚ (qz Ψ) p - dzℚ (qy Ψ) p
  , dzℚ (qx Ψ) p - dxℚ (qz Ψ) p
  , dxℚ (qy Ψ) p - dyℚ (qx Ψ) p - (kappaQ * (H p * H p)) * 1ℚ )

-- 与 entropySpinLaw 的逐点等价 (vscale 的 x/y 分量 s*0ℚ ≡ 0ℚ)
law-eq : ∀ Ψ H p → entropySpinLaw Ψ H p ≡ S-field Ψ H p
law-eq Ψ H p =
  cong₂ _,_
    (trans (cong (λ t → x - t) (*-zeroʳ s)) (+-identityʳ x))
    (cong₂ _,_
      (trans (cong (λ t → y - t) (*-zeroʳ s)) (+-identityʳ y))
      refl)
  where
  s = kappaQ * (H p * H p)
  x = dyℚ (qz Ψ) p - dzℚ (qy Ψ) p
  y = dzℚ (qx Ψ) p - dxℚ (qz Ψ) p

-- 末项提出: a + (b + (c − d)) ≡ (a + (b + c)) − d
pull-last : ∀ a b c d → a + (b + (c - d)) ≡ (a + (b + c)) - d
pull-last a b c d = begin
  a + (b + (c - d))
    ≡⟨ sym (+-assoc a b (c - d)) ⟩
  (a + b) + (c - d)
    ≡⟨ sym (+-assoc (a + b) c (- d)) ⟩
  ((a + b) + c) - d
    ≡⟨ cong (λ t → t - d) (+-assoc a b c) ⟩
  (a + (b + c)) - d ∎

-- V3 主定理: divℚ S = −∂z((κ·ℋ²)·1)
--   修正公理文档"无条件 ∇·S=0": 散度 = 旋度部分(0) − z 向 ℋ² 差分
divS-identity : ∀ Ψ H p →
  divℚ (S-field Ψ H) p ≡ - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p
divS-identity Ψ H p = begin
  divℚ (S-field Ψ H) p
    ≡⟨ refl ⟩
  dxℚ (λ q → dyℚ (qz Ψ) q - dzℚ (qy Ψ) q) p
    + (dyℚ (λ q → dzℚ (qx Ψ) q - dxℚ (qz Ψ) q) p
       + dzℚ (λ q → dxℚ (qy Ψ) q - dyℚ (qx Ψ) q - (kappaQ * (H q * H q)) * 1ℚ) p)
    ≡⟨ cong₂ _+_
         (dxℚ-sub (dyℚ (qz Ψ)) (dzℚ (qy Ψ)) p)
         (cong₂ _+_
           (dyℚ-sub (dzℚ (qx Ψ)) (dxℚ (qz Ψ)) p)
           (trans
             (dzℚ-sub (λ q → dxℚ (qy Ψ) q - dyℚ (qx Ψ) q)
                      (λ q → (kappaQ * (H q * H q)) * 1ℚ) p)
             (cong (λ t → t - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p)
                   (dzℚ-sub (dxℚ (qy Ψ)) (dyℚ (qx Ψ)) p)))) ⟩
  (dxℚ (dyℚ (qz Ψ)) p - dxℚ (dzℚ (qy Ψ)) p)
    + ((dyℚ (dzℚ (qx Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
       + ((dzℚ (dxℚ (qy Ψ)) p - dzℚ (dyℚ (qx Ψ)) p) - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p))
    ≡⟨ pull-last (dxℚ (dyℚ (qz Ψ)) p - dxℚ (dzℚ (qy Ψ)) p)
                 (dyℚ (dzℚ (qx Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
                 (dzℚ (dxℚ (qy Ψ)) p - dzℚ (dyℚ (qx Ψ)) p)
                 (dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p) ⟩
  ((dxℚ (dyℚ (qz Ψ)) p - dxℚ (dzℚ (qy Ψ)) p)
    + ((dyℚ (dzℚ (qx Ψ)) p - dyℚ (dxℚ (qz Ψ)) p)
       + (dzℚ (dxℚ (qy Ψ)) p - dzℚ (dyℚ (qx Ψ)) p)))
    - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p
    ≡⟨ cong (λ t → t - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p) (six-zero' Ψ p) ⟩
  0ℚ - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p
    ≡⟨ +-identityˡ (- dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p) ⟩
  - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p ∎

-- V3 守恒条件形式: ∂z(κ·ℋ²·1) = 0 ⟹ ∇·S = 0
-- (如 ℋ² 沿 z 常值; 公理文档的无条件 ∇·S=0 依此修正)
divS-zero-condition : ∀ Ψ H p →
  dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p ≡ 0ℚ →
  divℚ (S-field Ψ H) p ≡ 0ℚ
divS-zero-condition Ψ H p cond =
  trans (divS-identity Ψ H p) (cong -_ cond)

-- 0 postulate.
