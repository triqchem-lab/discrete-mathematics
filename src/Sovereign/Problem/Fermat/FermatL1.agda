{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Fermat.FermatL1
-- 费马大定理的离散基座 — L1 幂周期层
--
-- 数学背景 (13-flt-analysis.md 验证 1):
--   GF(3)× 的幂坍缩: 非零元 x ∈ {T₁, T₂} 满足 x² = 1, 故 xⁿ 只依赖 n 的奇偶:
--     n 偶 (2k): x^(2k) = 1
--     n 奇 (2k+1): x^(2k+1) = x
--   这是"幂的律"在 GF(3) 上的全部内容 — 指数维度坍缩为奇偶周期.
--   不足以区分 n = 2 (勾股, 有解) 与 n ≥ 3 (FLT 声称无解) —
--   那个区分需要 Archimedes 序 (连续统), 不在本层.
--
-- 本层引理 (全部 0 postulate):
--   nonzero-square : x ≢ 0 → x ⊗ x = 1      (平方坍缩, 第一原理)
--   pow3-step2     : x ≢ 0 → x^(m+2) = x^m   (两步周期)
--   pow3-even      : x ≢ 0 → x^(2k)  = 1
--   pow3-odd       : x ≢ 0 → x^(2k+1) = x
--   pow3-even-channel : ∀ x → x^(2k) ∈ {T₁, T₀}  (定理 C, 含零通道;
--                      对应 13-flt-analysis.md §9.2 计划)
--
-- 依赖: FermatL0 (pow3 定义, 零幂族, 非零分类)

module Sovereign.Problem.Fermat.FermatL1 where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; _⊕_; ⊗-identityˡ; ⊗-identityʳ; ⊗-assoc)

open import Sovereign.Problem.Fermat.FermatL0 using (pow3; _≢₃_; pow3-zero-odd)

--------------------------------------------------------------------------------
-- §1. 平方坍缩: 非零元的平方 = 1 (特征 3 的第一原理)
--------------------------------------------------------------------------------

-- GF(3)× 中 1² = 1, 2² = 4 ≡ 1: 平方映射是常值映射到 {1}
nonzero-square : ∀ x → x ≢₃ T₀ → x ⊗ x ≡ T₁
nonzero-square T₀ neq = ⊥-elim (neq refl)
nonzero-square T₁ _   = refl
nonzero-square T₂ _   = refl

--------------------------------------------------------------------------------
-- §2. 两步周期: x^(m+2) = x^m (对非零 x)
--------------------------------------------------------------------------------

pow3-step2 : ∀ x → x ≢₃ T₀ → ∀ m → pow3 x (suc (suc m)) ≡ pow3 x m
pow3-step2 x xz m = begin
  pow3 x (suc (suc m))      ≡⟨⟩                        -- 展开 pow3 两层
  x ⊗ (x ⊗ pow3 x m)        ≡⟨ sym (⊗-assoc x x (pow3 x m)) ⟩
  (x ⊗ x) ⊗ pow3 x m        ≡⟨ cong (_⊗ pow3 x m) (nonzero-square x xz) ⟩
  T₁ ⊗ pow3 x m             ≡⟨ ⊗-identityˡ (pow3 x m) ⟩
  pow3 x m                  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §3. 偶次幂 = 1: x^(2k) = 1 (非零 x)
--------------------------------------------------------------------------------

-- 用右乘 2: n * 2 (n 次 2 相加). (suc n) * 2 = suc (suc (n * 2)) 为定义归约.
pow3-even : ∀ x → x ≢₃ T₀ → ∀ n → pow3 x (n * 2) ≡ T₁
pow3-even x xz zero = refl                            -- x⁰ = T₁
pow3-even x xz (suc n) = begin
  pow3 x (suc n * 2)          ≡⟨⟩                     -- (n+1)*2 = (n*2)+2 归约
  pow3 x (suc (suc (n * 2)))  ≡⟨ pow3-step2 x xz (n * 2) ⟩
  pow3 x (n * 2)              ≡⟨ pow3-even x xz n ⟩
  T₁                          ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §4. 奇次幂 = x: x^(2k+1) = x (非零 x)
--------------------------------------------------------------------------------

pow3-odd : ∀ x → x ≢₃ T₀ → ∀ n → pow3 x (suc (n * 2)) ≡ x
pow3-odd x xz zero = begin
  pow3 x (suc (zero * 2))  ≡⟨⟩
  pow3 x (suc zero)        ≡⟨⟩
  x ⊗ T₁                   ≡⟨ ⊗-identityʳ x ⟩
  x                        ∎
  where open ≡-Reasoning
pow3-odd x xz (suc n) = begin
  pow3 x (suc (suc n * 2))        ≡⟨⟩                -- (n+1)*2 归约
  pow3 x (suc (suc (suc (n * 2)))) ≡⟨ pow3-step2 x xz (suc (n * 2)) ⟩
  pow3 x (suc (n * 2))            ≡⟨ pow3-odd x xz n ⟩
  x                               ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §4b. 偶次幂的 {T₁, T₀} 通道 (定理 C, 13-flt-analysis.md §9.2)
--
-- 对含零在内的全体 GF(3) 元素: 偶次幂只落在 {T₁, T₀} 两个值 —
--   非零元: x^(2k) = T₁ (pow3-even, 平方坍缩的升幂继承)
--   零元素: 0^(2k) = T₀ (k ≥ 1, 零幂族; k = 0 时 x⁰ = T₁ 约定)
--   (suc n) * 2 按定义展开为 suc (suc (n * 2)), 与 pow3-zero-odd 的形状匹配.
--------------------------------------------------------------------------------

pow3-even-channel : ∀ x n → pow3 x (n * 2) ≡ T₁ ⊎ pow3 x (n * 2) ≡ T₀
pow3-even-channel x zero     = inj₁ refl                       -- x⁰ = T₁
pow3-even-channel T₀ (suc n) = inj₂ (pow3-zero-odd n)          -- 零幂族
pow3-even-channel T₁ (suc n) =
  inj₁ (trans (pow3-step2 T₁ (λ ()) (n * 2)) (pow3-even T₁ (λ ()) n))
pow3-even-channel T₂ (suc n) =
  inj₁ (trans (pow3-step2 T₂ (λ ()) (n * 2)) (pow3-even T₂ (λ ()) n))

--------------------------------------------------------------------------------
-- §5. 周期 2 的语义汇总 (本层主定理)
--------------------------------------------------------------------------------

-- GF(3)× 中 xⁿ 只依赖 n 的奇偶性: 周期 = 2.
-- 对照 13-flt-analysis.md §3.1 验证表:
--   x=1: 1,1,1,1,… ; x=2: 2,1,2,1,… (python 核验 2026-09-05)
pow3-period-2-note : Set
pow3-period-2-note = (∀ x → x ≢₃ T₀ → ∀ n → pow3 x (n * 2) ≡ T₁)
                   × (∀ x → x ≢₃ T₀ → ∀ n → pow3 x (suc (n * 2)) ≡ x)

pow3-period-2 : pow3-period-2-note
pow3-period-2 = pow3-even , pow3-odd
