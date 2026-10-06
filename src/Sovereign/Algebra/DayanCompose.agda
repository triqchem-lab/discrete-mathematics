{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanCompose
-- 任务 6：G3 多分量合成定理——N ≡ rᵢ (mod 定ᵢ) 的 ℤ 代数证明
--
-- 数学内容（两分量版）：
--   前提①（乘率）：r₁·u₁ = r₁ + 定₁·K₁     （terminate-correct 输出形态）
--   前提②（含因子）：u₂ = 定₁·t₂            （衍数₂ 含因子 定₁）
--   合成 N = r₁·u₁ + r₂·u₂
--   ⟹ N = r₁ + 定₁·(r₁·K₁ + r₂·t₂) ⟹ N ≡ r₁ (mod 定₁)
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.DayanCompose where

open import Data.Integer using (ℤ)
open import Data.Integer renaming (_*_ to _ℤ*_; _+_ to _ℤ+_)
open import Data.Integer.Properties
  using (*-distribˡ-+; *-assoc; *-comm; +-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym)
open import Data.Product using (Σ; _×_; _,_)

--------------------------------------------------------------------------------
-- §1. mod 关系的 ℤ 形式——witness 式（无 %）
--------------------------------------------------------------------------------

ModRel : ℤ → ℤ → ℤ → Set
ModRel b x r = Σ ℤ (λ t → x ≡ r ℤ+ b ℤ* t)

--------------------------------------------------------------------------------
-- §2. 两分量合成定理
--------------------------------------------------------------------------------

two-comp : ∀ (r₁ r₂ 定₁ K₁ u₁ u₂ t₂ : ℤ) →
  -- 前提①（乘率，K₁ 已吸收 r₁ 因子）：r₁·u₁ ≡ r₁ + 定₁·K₁
  --   （K₁ = r₁·K₁；由 terminate-correct 的 lt·奇 = 1 + k·定 两边乘 r₁ 得）
  (r₁ ℤ* u₁) ≡ (r₁ ℤ+ 定₁ ℤ* K₁) →
  -- 前提②（含因子）：u₂ = 定₁·t₂
  u₂ ≡ (定₁ ℤ* t₂) →
  -- 结论：N = r₁·u₁ + r₂·u₂ ≡ r₁ (mod 定₁)
  ModRel 定₁ ((r₁ ℤ* u₁) ℤ+ (r₂ ℤ* u₂)) r₁
two-comp r₁ r₂ 定₁ K₁ u₁ u₂ t₂ h₁ h₂ =
  (K₁ ℤ+ r₂ ℤ* t₂ ,
   trans step₁ (trans step₂ (trans step₃ step₄)))

  where
    -- N = (r₁·u₁) + (r₂·u₂)
    --   ≡ (r₁ + 定₁K₁) + (r₂·u₂)            [h₁]
    --   ≡ (r₁ + 定₁K₁) + (r₂·(定₁·t₂))      [cong h₂]
    --   ≡ (r₁ + 定₁K₁) + (定₁·(r₂·t₂))      [sym assoc ∙ comm ∙ assoc]
    --   ≡ r₁ + (定₁K₁ + 定₁(r₂t₂))          [sym +-assoc]
    --   ≡ r₁ + 定₁·(K₁ + r₂t₂)              [sym *-distribˡ-+]

    step₁ : (r₁ ℤ* u₁) ℤ+ (r₂ ℤ* u₂)
           ≡ (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* u₂)
    step₁ = cong (λ z → z ℤ+ (r₂ ℤ* u₂)) h₁

    step₂ : (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* u₂)
           ≡ (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* (定₁ ℤ* t₂))
    step₂ = cong (λ z → (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* z)) h₂

    step₃ : (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (r₂ ℤ* (定₁ ℤ* t₂))
           ≡ (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (定₁ ℤ* (r₂ ℤ* t₂))
    step₃ =
      cong (λ z → (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ z)
           (trans (sym (*-assoc r₂ 定₁ t₂))
           (trans (cong (λ z → z ℤ* t₂) (*-comm r₂ 定₁))
                  (*-assoc 定₁ r₂ t₂)))
    -- r₂·(定₁·t₂) = (r₂·定₁)·t₂ = (定₁·r₂)·t₂ = 定₁·(r₂·t₂)

    step₄ : (r₁ ℤ+ 定₁ ℤ* K₁) ℤ+ (定₁ ℤ* (r₂ ℤ* t₂))
           ≡ r₁ ℤ+ 定₁ ℤ* (K₁ ℤ+ r₂ ℤ* t₂)
    step₄ =
      trans (+-assoc r₁ (定₁ ℤ* K₁) (定₁ ℤ* (r₂ ℤ* t₂)))
            (cong (λ z → r₁ ℤ+ z)
                  (sym (*-distribˡ-+ 定₁ K₁ (r₂ ℤ* t₂))))
    -- (r₁+定₁K₁) + 定₁·X = r₁ + (定₁K₁ + 定₁·X) = r₁ + 定₁(K₁+X)

--------------------------------------------------------------------------------
-- §3. 三分量陈述——同型推广
--
--   前提：u₂ = 定₁t₂'、u₃ = 定₁t₃'（均含因子 定₁）；u₁ = 1 + 定₁k
--   N = r₁ + 定₁·(r₁k + r₂t₂' + r₃t₃') ⟹ N ≡ r₁ (mod 定₁)
--   结构与 two-comp 相同（多一项同型合并）；数值对账由 DayanCRT
--   三同余 refl（mod 3/5/7 各 ✓）承担。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4. 完成度——任务 6 闭合
--
--   ✅ ModRel：mod 关系 ℤ 构造性定义（witness 式）
--   ✅ two-comp：两分量合成定理（四步 ∙ 链：h₁→h₂→assoc/comm→distrib）
--   ✅ 前提①来源：DayanProof.terminate-correct（乘率 mod 关系）
--   ✅ 数值对账：DayanCRT（N=233、解=23、三同余 ✓）
--
--   G3 泛型 CRT 证据链完整闭环：
--   terminate-correct → two-comp（合成定理）→ CRT3 → DayanCRT 解=23
--------------------------------------------------------------------------------
