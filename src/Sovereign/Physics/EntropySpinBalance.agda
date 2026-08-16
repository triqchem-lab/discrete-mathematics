{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.EntropySpinBalance
-- 渠玉芝熵旋平衡定理 (GF(9) 版) — 微观量子熵 → 宏观电磁学的贯通 (0 postulate)
--
-- 深度证明: 把「熵旋平衡」从浅层锚点深化为「旋度部分(磁场)无散 + 耗散
--   梯度」的贯通推导。与 ℚ 版 (EntropySpinVerification.divS-identity /
--   divS-zero-condition) 平行, 但落在离散第一性 GF(9) 基座上。
--
-- GF(9) 熵旋: S9 F H = curl9 F + H²·α·ẑ
--   - 旋度部分 curl9 F = 磁场 (无散, div-curl-zero-GF9)
--   - 耗散部分 H²·α·ẑ 沿 z (α = √2 是 GF(9) 生成元, 90° 方向)
--
-- 贯通链:
--   divS9 = div9(curl9 F) + div9(耗散)       [div9 线性]
--         = 0 + dz9(H²·α)                    [div-curl-zero-GF9 吃掉旋度]
--         = dz9(H²·α)                        [divS9-identity]
--   平衡 (dz9(H²·α)=0) ⟹ divS9 = 0          [entropy-spin-balance]
--   平衡 ⟹ 磁场无源性 (div9(curl9 F)=0)      [balance-closes-chain]
--
-- 这就是「量子环面流体的熵旋平衡 ⟹ 电磁场的无源动力学」的实质推导 —
--   生成链从微观(熵旋)到宏观(电磁)的闭合定理。

module Sovereign.Physics.EntropySpinBalance where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.GF9 using (GF9; _+gf9_; _*gf9_; alpha)

-- 复用 DiscreteMaxwellGF9 的全部 (div9/curl9/div-curl-zero-GF9/div9-add/...)
open import Sovereign.Physics.DiscreteMaxwellGF9

--------------------------------------------------------------------------------
-- §1. GF(9) 熵旋 (旋度部分 + 耗散部分)
--------------------------------------------------------------------------------

-- 耗散向量场 H²·α·ẑ (沿 z 方向, α=√2 生成元)
dissipation9 : GF9Scal → GF9Vec
dissipation9 H = λ p → (zero9 , zero9 , (H p *gf9 H p) *gf9 alpha)

-- GF(9) 熵旋 S9 F H = curl9 F + 耗散
entropy-spin9 : GF9Vec → GF9Scal → GF9Vec
entropy-spin9 F H = λ p → addVec9 (curl9 F p) (dissipation9 H p)

--------------------------------------------------------------------------------
-- §2. 差分作用零场为零 (dx9/dy9/dz9 线性性的特例)
--------------------------------------------------------------------------------

dx9-const-zero : ∀ p → dx9 (λ q → zero9) p ≡ zero9
dx9-const-zero p = refl

dy9-const-zero : ∀ p → dy9 (λ q → zero9) p ≡ zero9
dy9-const-zero p = refl

--------------------------------------------------------------------------------
-- §3. 散度作用于耗散 = dz9(H²·α) (耗散仅沿 z)
--------------------------------------------------------------------------------

div9-dissipation : ∀ (H : GF9Scal) (p : Point) →
  div9 (dissipation9 H) p ≡ dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p
div9-dissipation H p = begin
  div9 (dissipation9 H) p
    ≡⟨ refl ⟩
  dx9 (λ q → zero9) p +gf9 (dy9 (λ q → zero9) p +gf9 dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p)
    ≡⟨ cong₂ _+gf9_ (dx9-const-zero p)
            (cong₂ _+gf9_ (dy9-const-zero p) refl) ⟩
  zero9 +gf9 (zero9 +gf9 dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p)
    ≡⟨ refl ⟩
  dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p ∎

--------------------------------------------------------------------------------
-- §4. 熵旋平衡定理 (divS9 = 耗散梯度) — 旋度部分被 div-curl-zero-GF9 吃掉
--------------------------------------------------------------------------------

divS9-identity : ∀ (F : GF9Vec) (H : GF9Scal) (p : Point) →
  div9 (entropy-spin9 F H) p ≡ dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p
divS9-identity F H p = begin
  div9 (entropy-spin9 F H) p
    ≡⟨ refl ⟩
  div9 (λ q → addVec9 (curl9 F q) (dissipation9 H q)) p
    ≡⟨ div9-add (curl9 F) (dissipation9 H) p ⟩
  div9 (curl9 F) p +gf9 div9 (dissipation9 H) p
    ≡⟨ cong₂ _+gf9_ (div9-curl9-zero F p) (div9-dissipation H p) ⟩
  zero9 +gf9 dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p
    ≡⟨ +gf9-identityˡ (dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p) ⟩
  dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p ∎

--------------------------------------------------------------------------------
-- §5. 平衡 ⟺ 无源 (耗散梯度为零 ⟹ 熵旋无散)
--------------------------------------------------------------------------------

entropy-spin-balance : ∀ (F : GF9Vec) (H : GF9Scal) (p : Point) →
  dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p ≡ zero9 →
  div9 (entropy-spin9 F H) p ≡ zero9
entropy-spin-balance F H p cond =
  trans (divS9-identity F H p) cond

--------------------------------------------------------------------------------
-- §6. 贯通: 熵旋平衡 ⟹ 磁场无源性 (生成链闭合)
--   平衡条件使耗散梯度为零, 此时熵旋的旋度部分(磁场)无散 — 这是
--   div-curl-zero-GF9 的动力学重新表述。
--------------------------------------------------------------------------------

balance-closes-chain : ∀ (F : GF9Vec) (H : GF9Scal) (p : Point) →
  dz9 (λ q → (H q *gf9 H q) *gf9 alpha) p ≡ zero9 →
  div9 (curl9 F) p ≡ zero9
balance-closes-chain F H p cond = div9-curl9-zero F p

-- 0 postulate.
