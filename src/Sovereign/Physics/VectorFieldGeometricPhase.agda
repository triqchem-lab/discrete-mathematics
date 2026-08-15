{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.VectorFieldGeometricPhase
-- 矢量场决定几何相位 — Rust 核算的库内固化 (0 postulate, 无洞)
--
-- Rust 核算 (sov-math/sov-chiral/examples/entropy_spin_phase.rs) 的五项数据
-- 在此落为 Agda 定理, 逐项对应:
--   [1] S⃗ 为矢量场       → gradℚ/curlℚ 结构 (QVector)
--   [2] div∘curl = 0     → curl-kernel-source-free
--   [3] curl∘grad = 0    → curlQ-grad-zero (纯标量场不携带几何相位)
--   [4] divS-identity    → entropy-spin-phase-source (相位源仅沿 n̂)
--   [5] 质量 = −κ·N      → curl-flux-vanishes + vector-quantization
--
-- 三方场型对照 (并存互补, 非裁决, 文档层):
--   主流宏观: 标量物质图像 — 几何相位需外贴 Berry 曲率
--   斯瓦鲁量子场: 矢量场 (驻波谐波方向性) — 相位来自谐波方向结构
--   渠玉芝熵旋: 矢量场 S⃗ = ∇×Ψ⃗ − κℋ²·n̂ — 旋度内核无源 (定理 2),
--     几何相位/质量的全部来源是标量项 κℋ² 沿 n̂ 的梯度 (定理 4),
--     且量子化为 −κ·N (定理 5)。矢量场选择决定了相位的一切。
--
-- 与 GF(3) 层 DiscreteEMField3D.curl-grad-zero (Trit 版) 的 ℚ 层对应。

module Sovereign.Physics.VectorFieldGeometricPhase where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Rational using (ℚ; _-_; -_; _*_; 0ℚ; 1ℚ)
open import Data.Rational.Properties using (+-inverseʳ)
open import Sovereign.Physics.DiscreteEMField3D using (Point3D)
open import Sovereign.Physics.EntropySpinLaw
open import Sovereign.Physics.EntropySpinVerification
  using (S-field; dxdy-commℚ; dydz-commℚ; dzdx-commℚ;
         divℚ; divℚ-curl-zero; divS-identity)
open import Sovereign.Physics.EntropySpinMicro using (zeroΨ)
open import Sovereign.Physics.EntropySpinQuantize
  using (fromBool; countQ9; m₀; quantized-mass-integral)

--------------------------------------------------------------------------------
-- 定理 1: 标量梯度 (标量场经矢量场化的形式)
--------------------------------------------------------------------------------

gradℚ : QScalar → QVector
gradℚ φ p = (dxℚ φ p , dyℚ φ p , dzℚ φ p)

--------------------------------------------------------------------------------
-- 定理 2: 纯标量场不携带几何相位 — curl∘grad = 0 (逐点, 符号)
--   三分量分别由 dydz/dzdx/dxdy 交换律 + x−x=0 消去
--------------------------------------------------------------------------------

curlQ-grad-zero : ∀ φ p → curlℚ (gradℚ φ) p ≡ (0ℚ , 0ℚ , 0ℚ)
curlQ-grad-zero φ p = cong₂ _,_ comp1 (cong₂ _,_ comp2 comp3)
  where
  comp1 = begin
    dyℚ (dzℚ φ) p - dzℚ (dyℚ φ) p
      ≡⟨ cong (λ t → dyℚ (dzℚ φ) p - t) (sym (dydz-commℚ φ p)) ⟩
    dyℚ (dzℚ φ) p - dyℚ (dzℚ φ) p
      ≡⟨ +-inverseʳ (dyℚ (dzℚ φ) p) ⟩
    0ℚ ∎
  comp2 = begin
    dzℚ (dxℚ φ) p - dxℚ (dzℚ φ) p
      ≡⟨ cong (λ t → dzℚ (dxℚ φ) p - t) (sym (dzdx-commℚ φ p)) ⟩
    dzℚ (dxℚ φ) p - dzℚ (dxℚ φ) p
      ≡⟨ +-inverseʳ (dzℚ (dxℚ φ) p) ⟩
    0ℚ ∎
  comp3 = begin
    dxℚ (dyℚ φ) p - dyℚ (dxℚ φ) p
      ≡⟨ cong (λ t → dxℚ (dyℚ φ) p - t) (sym (dxdy-commℚ φ p)) ⟩
    dxℚ (dyℚ φ) p - dxℚ (dyℚ φ) p
      ≡⟨ +-inverseʳ (dxℚ (dyℚ φ) p) ⟩
    0ℚ ∎

--------------------------------------------------------------------------------
-- 定理 3: 旋度内核无源 — div∘curl = 0 (矢量场的相位内核)
--------------------------------------------------------------------------------

curl-kernel-source-free : ∀ Ψ p → divℚ (curlℚ Ψ) p ≡ 0ℚ
curl-kernel-source-free = divℚ-curl-zero

--------------------------------------------------------------------------------
-- 定理 4: 熵旋相位源仅沿 n̂ — divS-identity
--   divℚ S = −∂z(κ·ℋ²·1): 旋度部分沉默, 相位源由标量项沿 n̂ 生成
--------------------------------------------------------------------------------

entropy-spin-phase-source : ∀ Ψ H p →
  divℚ (S-field Ψ H) p ≡ - dzℚ (λ q → (kappaQ * (H q * H q)) * 1ℚ) p
entropy-spin-phase-source = divS-identity

--------------------------------------------------------------------------------
-- 定理 5: 旋度通量望远镜消去 — curl 无净几何相位
--------------------------------------------------------------------------------

curl-flux-vanishes : ∀ Ψ → massIntegral (curlℚ Ψ) ≡ 0ℚ
curl-flux-vanishes = massIntegral-curl-zero

--------------------------------------------------------------------------------
-- 定理 6: 矢量场质量量子化 — 质量 = −κ·N (N 活跃点数)
--------------------------------------------------------------------------------

vector-quantization : ∀ H →
  massIntegral (S-field zeroΨ (λ p → fromBool (H p))) ≡ - (countQ9 H * m₀)
vector-quantization = quantized-mass-integral

-- 0 postulate.
