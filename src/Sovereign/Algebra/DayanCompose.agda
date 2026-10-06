{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanCompose
-- G3 多分量合成定理——N ≡ rᵢ (mod 定ᵢ) 的 ℤ 代数证明
--
-- 二分量（two-comp）+ 三分量（three-comp）+ witness 式 mod 定义（无 %）。
-- 0 postulate / 0 hole。
module Sovereign.Algebra.DayanCompose where

open import Data.Integer using (ℤ)
open import Data.Integer renaming (_*_ to _ℤ*_; _+_ to _ℤ+_)
open import Data.Integer.Properties
  using (*-distribˡ-+; *-assoc; *-comm; +-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

--------------------------------------------------------------------------------
-- §1. mod 关系的 ℤ 形式——witness 式（无 %）
--------------------------------------------------------------------------------

ModRel : ℤ → ℤ → ℤ → Set
ModRel b x r = Σ ℤ (λ t → x ≡ r ℤ+ b ℤ* t)

--------------------------------------------------------------------------------
-- §2. 两分量合成定理
--
--   N = r₁·u₁ + r₂·u₂
--   前提①（乘率）：r₁·u₁ ≡ r₁ + 定₁·K₁
--   前提②（含因子）：u₂ ≡ 定₁·t₂
--   ⟹ N ≡ r₁ (mod 定₁)，witness = K₁ + r₂·t₂
--
--   证明四步：h₁ 替换 → h₂ 替换 → assoc/comm 重排 → *-distribˡ 提取公因子
--------------------------------------------------------------------------------

two-comp : ∀ (r₁ r₂ 定₁ K₁ u₁ u₂ t₂ : ℤ) →
  (r₁ ℤ* u₁) ≡ (r₁ ℤ+ 定₁ ℤ* K₁) →
  u₂ ≡ (定₁ ℤ* t₂) →
  ModRel 定₁ ((r₁ ℤ* u₁) ℤ+ (r₂ ℤ* u₂)) r₁
two-comp r₁ r₂ 定₁ K₁ u₁ u₂ t₂ h₁ h₂ =
  (K₁ ℤ+ r₂ ℤ* t₂ ,
   trans step₁ (trans step₂ (trans step₃ step₄)))
  where
    step₁ : (r₁ ℤ* u₁) ℤ+ (r₂ ℤ* u₂) ≡ (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* u₂)
    step₁ = cong (λ z → z ℤ+ (r₂ ℤ* u₂)) h₁

    step₂ : _ ≡ (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* (定₁ ℤ* t₂))
    step₂ = cong (λ z → (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* z)) h₂

    step₃ : _ ≡ (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (定₁ ℤ* (r₂ ℤ* t₂))
    step₃ =
      trans (cong (λ z → (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ z)
                 (trans (sym (*-assoc r₂ 定₁ t₂))
                 (trans (cong (λ z → z ℤ* t₂) (*-comm r₂ 定₁))
                        (*-assoc 定₁ r₂ t₂))))
            refl

    step₄ : (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (定₁ ℤ* (r₂ ℤ* t₂)) ≡ r₁ ℤ+ 定₁ ℤ* (K₁ ℤ+ r₂ ℤ* t₂)
    step₄ = trans (+-assoc r₁ (定₁ ℤ* K₁) (定₁ ℤ* (r₂ ℤ* t₂)))
                  (cong (λ z → r₁ ℤ+ z)
                        (sym (*-distribˡ-+ 定₁ K₁ (r₂ ℤ* t₂))))

--------------------------------------------------------------------------------
-- §3. 三分量合成定理——完整证明（复用 two-comp 输出 + 提取公因子）
--
-- N = r₁u₁ + r₂u₂ + r₃u₃
--   = (r₁u₁ + r₂u₂) + r₃u₃                      [+ℤ assoc]
--   ≡ (r₁ + 定₁·K₁) + r₃·(定₁·t₃)               [two-comp h₁ h₂ + cong h₃]
--   ≡ r₁ + 定₁·(K₁ + r₃·t₃)                     [+-assoc + sym *-distribˡ-+]
--   ⟹ N ≡ r₁ (mod 定₁)
--------------------------------------------------------------------------------

three-comp : ∀ (r₁ r₂ r₃ 定₁ K₁ u₁ u₂ u₃ t₂ t₃ : ℤ) →
  (r₁ ℤ* u₁) ≡ (r₁ ℤ+ 定₁ ℤ* K₁) →
  u₂ ≡ (定₁ ℤ* t₂) →
  u₃ ≡ (定₁ ℤ* t₃) →
  ModRel 定₁ ((r₁ ℤ* u₁) ℤ+ (r₂ ℤ* u₂) ℤ+ (r₃ ℤ* u₃)) r₁
three-comp r₁ r₂ r₃ 定₁ K₁ u₁ u₂ u₃ t₂ t₃ h₁ h₂ h₃ =
  (K₁ ℤ+ r₂ ℤ* t₂ ℤ+ r₃ ℤ* t₃ , proof)
  where
    -- 前两分量由 two-comp 闭合
    -- two-comp 输出：r₁u₁+r₂u₂ ≡ r₁ + 定₁·(K₁+r₂t₂)
    two-comp-proof : r₁ ℤ* u₁ ℤ+ r₂ ℤ* u₂ ≡ r₁ ℤ+ 定₁ ℤ* (K₁ ℤ+ r₂ ℤ* t₂)
    two-comp-proof = proj₂ (two-comp r₁ r₂ 定₁ K₁ u₁ u₂ t₂ h₁ h₂)

    -- 两分量合成的 witness
    K₁₂ = K₁ ℤ+ r₂ ℤ* t₂

    -- 第三分量替换：r₃·u₃ = r₃·(定₁·t₃)
    step₃ : r₃ ℤ* u₃ ≡ r₃ ℤ* (定₁ ℤ* t₃)
    step₃ = cong (λ z → r₃ ℤ* z) h₃

    -- 第三分量重排：r₃·(定₁·t₃) = 定₁·(r₃·t₃)
    step₄ : (r₃ ℤ* (定₁ ℤ* t₃)) ≡ 定₁ ℤ* (r₃ ℤ* t₃)
    step₄ = trans (sym (*-assoc r₃ 定₁ t₃))
                  (trans (cong (λ z → z ℤ* t₃) (*-comm r₃ 定₁))
                         (*-assoc 定₁ r₃ t₃))

    -- 提取公因子
    step₅ : (r₁ ℤ+ 定₁ ℤ* K₁₂) ℤ+ (定₁ ℤ* (r₃ ℤ* t₃)) ≡ r₁ ℤ+ 定₁ ℤ* (K₁₂ ℤ+ r₃ ℤ* t₃)
    step₅ = trans (+-assoc r₁ (定₁ ℤ* K₁₂) (定₁ ℤ* (r₃ ℤ* t₃)))
                  (cong (λ z → r₁ ℤ+ z) (sym (*-distribˡ-+ 定₁ K₁₂ (r₃ ℤ* t₃))))

    -- 证明：(r₁u₁+r₂u₂) + r₃u₃ ≡ r₁ + 定₁·(K₁₂ + r₃t₃)
    proof : (r₁ ℤ* u₁ ℤ+ r₂ ℤ* u₂) ℤ+ r₃ ℤ* u₃ ≡ r₁ ℤ+ 定₁ ℤ* (K₁₂ ℤ+ r₃ ℤ* t₃)
    proof = trans (cong (λ z → z ℤ+ r₃ ℤ* u₃) two-comp-proof)
                  (trans (cong (λ z → (r₁ ℤ+ 定₁ ℤ* K₁₂) ℤ+ z) step₃)
                         (trans (cong (λ z → (r₁ ℤ+ 定₁ ℤ* K₁₂) ℤ+ z) step₄)
                                step₅))

--------------------------------------------------------------------------------
-- §4. 完成度
--
--   ✅ ModRel：mod 关系 ℤ 构造性定义（witness 式，无 %）
--   ✅ two-comp：两分量合成定理（四步链）
--   ✅ three-comp：三分量合成定理（复用 two-comp + 提取公因子）
--   ✅ 数值对账：DayanCRT（N=233、解=23、三同余 ✓）
--
--   G3 泛型 CRT 证据链完整闭环：
--   terminate-correct → two-comp/three-comp → CRT3 → DayanCRT 解=23
--------------------------------------------------------------------------------
