{-# OPTIONS --rewriting #-}

-- | Sovereign.Problem.Langlands.GL2TestVectors
-- GL₂(GF(9)) 群分类的 HFM 穷举交叉验证测试向量
--
-- HFM 验证 (test/GL2Verify.hs):
--   穷举全部 6561 个 Mat₂(GF(9)) 矩阵, 筛出可逆者 5760 个
--   按判别式 Δ = tr² − 4·det 在 GF(9) 中的性质分类
--
-- 数学原理:
--   GF(9) = GF(3)[i], i² = -1, 共 9 个元素
--   Mat₂(GF(9)) 有 9⁴ = 6561 个矩阵
--   GL₂(GF(9)) 的行列式不为零, 个数 = (9²-1)(9²-9) = 5760
--
--   GL₂(F_q) 的共役类由特征多项式 f(t) = det(t·I − M) 分类:
--   (1) Central (标量矩阵): f(t) = (t−λ)², 极小多项式 = t−λ
--       共 q−1 = 8 类, 类大小 = 1
--   (2) Split regular (可对角化, 特征值相异):
--       f(t) = (t−λ)(t−μ), λ≠μ ∈ GF(9)
--       共 (q−1)(q−2)/2 = 28 类, 类大小 = q(q+1) = 90
--   (3) Anisotropic (不可对角化, 特征值在 GF(81)\GF(9)):
--       f(t) 不可约, Δ 不是 GF(9)* 中的平方
--       共 q(q−1)/2 = 36 类, 类大小 = q(q−1) = 72
--   (4) Unipotent (若当块): f(t) = (t−λ)², 极小多项式 = (t−λ)²
--       共 q−1 = 8 类, 类大小 = q²−1 = 80
--
--   总计: 8 + 28 + 36 + 8 = 80 类
--   Burnside 和: 8×1 + 28×90 + 36×72 + 8×80 = 5760 ✓
--
--   Steinberg 特征标 χ_St (GL₂(F_q) 的尖点表示):
--     χ_St(1) = q = 9 (维数)
--     Central:   χ_St = 9
--     Split:     χ_St = 1
--     Aniso:     χ_St = −1
--     Unip:      χ_St = 0
--
--   ⟨χ_St, 1⟩ = 0, ⟨χ_St, χ_St⟩ = 1 (正交性验证)
--
-- 相关模块: Langlands.agda (群阶公式, 共役类计数)

module Sovereign.Problem.Langlands.GL2TestVectors where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

-- 1. 群阶
-- |GL₂(GF(q))| = (q²-1)(q²-q), q=9 → 80 × 72 = 5760
orderGL2 : ℕ; orderGL2 = 80 * 72

-- |SL₂(GF(9))| = |GL₂| / |GF(9)*| = 5760/8 = 720
orderSL2 : ℕ; orderSL2 = 720

-- |Z(GL₂)| = |GF(9)*| = 8 (标量矩阵 λI, λ∈GF(9)*)
centerSize : ℕ; centerSize = 8

orderGL2-ok : orderGL2 ≡ 5760
orderGL2-ok =
  begin
    orderGL2
  ≡⟨⟩  80 * 72
  ≡⟨⟩  5760
  ∎

orderSL2-ok : orderSL2 ≡ 720
orderSL2-ok =
  begin
    orderSL2
  ≡⟨⟩  720
  ∎

-- 整除验证: |SL₂| × |Z| = |GL₂| (因 GL₂/SL₂ ≅ GF(9)*)
orderSL2-factor-check : orderSL2 * centerSize ≡ orderGL2
orderSL2-factor-check =
  begin
    orderSL2 * centerSize
  ≡⟨⟩  -- 展开
    720 * 8
  ≡⟨⟩  -- 720 × 8 = 5760
    5760
  ≡⟨⟩  -- orderGL2 = 5760
    orderGL2
  ∎

-- 2. 共役类分类
--   四类: Central(8×1) + Split(28×90) + Aniso(36×72) + Unip(8×80)
totalClasses : ℕ; totalClasses = 8 + 28 + 36 + 8
burnsideSum : ℕ; burnsideSum = 8 * 1 + 28 * 90 + 36 * 72 + 8 * 80

totalClasses-ok : totalClasses ≡ 80
totalClasses-ok =
  begin
    totalClasses
  ≡⟨⟩  8 + 28 + 36 + 8
  ≡⟨⟩  -- 8+28=36
    36 + 36 + 8
  ≡⟨⟩  -- 36+36=72
    72 + 8
  ≡⟨⟩  -- 72+8=80
    80
  ∎

burnsideSum-ok : burnsideSum ≡ 5760
burnsideSum-ok =
  begin
    burnsideSum
  ≡⟨⟩  8 * 1 + 28 * 90 + 36 * 72 + 8 * 80
  ≡⟨⟩  -- 8×1=8, 28×90=2520, 36×72=2592, 8×80=640
    8 + 2520 + 2592 + 640
  ≡⟨⟩  -- 8+2520=2528
    2528 + 2592 + 640
  ≡⟨⟩  -- 2528+2592=5120
    5120 + 640
  ≡⟨⟩  -- 5120+640=5760
    5760
  ∎

-- 3. Steinberg 特征标 (ℤ)
open import Data.Integer renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
  using (ℤ; +_; -[1+_])

-- χ_St 在各共役类上的取值
chiSt-dim : ℤ; chiSt-dim = + 9        -- 维数 = q
chiSt-cent : ℤ; chiSt-cent = + 9      -- Central 上 = q
chiSt-split : ℤ; chiSt-split = + 1    -- Split 上 = 1
chiSt-aniso : ℤ; chiSt-aniso = -[1+ 0 ]  -- Aniso 上 = −1
chiSt-unip : ℤ; chiSt-unip = + 0      -- Unip 上 = 0

-- ⟨χ_St, 1⟩ = 0 (正交于平凡表示)
-- Σ|C|·χ_St(C)·1 = 8·1·9 + 28·90·1 + 36·72·(−1) + 8·80·0 = 0
orthTriv : ℤ
orthTriv = (+ 8) *ℤ (+ 1) *ℤ (+ 9)
        +ℤ (+ 28) *ℤ (+ 90) *ℤ (+ 1)
        +ℤ (+ 36) *ℤ (+ 72) *ℤ (-[1+ 0 ])
        +ℤ (+ 8) *ℤ (+ 80) *ℤ (+ 0)

orthTriv-ok : orthTriv ≡ + 0
orthTriv-ok =
  begin
    orthTriv
  ≡⟨⟩  (+ 8) *ℤ (+ 1) *ℤ (+ 9) +ℤ (+ 28) *ℤ (+ 90) *ℤ (+ 1)
         +ℤ (+ 36) *ℤ (+ 72) *ℤ (-[1+ 0 ]) +ℤ (+ 8) *ℤ (+ 80) *ℤ (+ 0)
  ≡⟨⟩  -- 8·1·9=72, 28·90·1=2520, 36·72·(−1)=−2592, 8·80·0=0
    (+ 72) +ℤ (+ 2520) +ℤ (-[1+ 2591 ]) +ℤ (+ 0)
  ≡⟨⟩  -- 72+2520=2592, 2592−2592=0
    (+ 0)
  ∎

-- ⟨χ_St, χ_St⟩ = 1 (自身正交归一)
-- Σ|C|·χ_St(C)² = 8·1·81 + 28·90·1 + 36·72·1 + 8·80·0 = 5760
orthSelf : ℤ
orthSelf = (+ 8) *ℤ (+ 1) *ℤ (+ 9) *ℤ (+ 9)
        +ℤ (+ 28) *ℤ (+ 90) *ℤ (+ 1) *ℤ (+ 1)
        +ℤ (+ 36) *ℤ (+ 72) *ℤ (+ 1) *ℤ (+ 1)
        +ℤ (+ 8) *ℤ (+ 80) *ℤ (+ 0) *ℤ (+ 0)

orthSelf-ok : orthSelf ≡ + 5760
orthSelf-ok =
  begin
    orthSelf
  ≡⟨⟩  (+ 8) *ℤ (+ 1) *ℤ (+ 9) *ℤ (+ 9)
         +ℤ (+ 28) *ℤ (+ 90) *ℤ (+ 1) *ℤ (+ 1)
         +ℤ (+ 36) *ℤ (+ 72) *ℤ (+ 1) *ℤ (+ 1)
         +ℤ (+ 8) *ℤ (+ 80) *ℤ (+ 0) *ℤ (+ 0)
  ≡⟨⟩  -- 8·81=648, 28·90=2520, 36·72=2592, 8·80·0=0
    (+ 648) +ℤ (+ 2520) +ℤ (+ 2592) +ℤ (+ 0)
  ≡⟨⟩  -- 648+2520=3168, 3168+2592=5760
    (+ 5760)
  ∎
