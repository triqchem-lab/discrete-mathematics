{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Fermat.FermatL2
-- 费马大定理的离散基座 — L2 模 3 方程行为层
--
-- 数学背景 (13-flt-analysis.md 验证 1 的方程层面):
--   把 FLT 方程 aⁿ+bⁿ=cⁿ 约化到 GF(3). 由 L1 的幂周期 2:
--
--   [n 奇] x^(2k+1) = x (非零): 方程退化为一次线性方程 x⊕y = z.
--     非零解存在: (1,1,2) 与 (2,2,1) — 处处有"伪解".
--     ⟹ GF(3) 的幂的律不排斥奇数指数的解: 无解性不在幂自身里.
--
--   [n 偶] x^(2k) = 1 (非零): 非零三元的方程化为 1⊕1 = 1, 即 2 = 1 — 无解.
--     若有解 (含零), 则必须穿过零通道: x≡0 ∨ y≡0 ∨ z≡0.
--     提升到 ℤ: 任何偶次 FLT 反例必须满足 3 | abc (某变量被 3 整除).
--     (ℤ 提升是元论证 — L0+ 外部引用, 本模块只证 GF(3) 层的精确陈述)
--
-- 本层主定理 (全部 0 postulate):
--   flt-odd-linear        : n 奇 ⇒ 方程 = 线性关系 (非零元上)
--   flt-mod3-sol-112/221  : 非零解 (1,1,2)/(2,2,1) 存在 ∀ n
--   flt-even-nonsol       : n 偶 ⇒ 非零三元无解
--   flt-even-zero-channel : n 偶 ⇒ 有解 ⇒ 至少一个变量为 0 (零通道)
--
-- 依赖: FermatL0 (pow3, ≢₃, zero-trit?), FermatL1 (pow3-even/odd)

module Sovereign.Problem.Fermat.FermatL2 where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

open import Sovereign.Problem.Fermat.FermatL0 using (pow3; _≢₃_; zero-trit?)
open import Sovereign.Problem.Fermat.FermatL1 using (pow3-even; pow3-odd)

--------------------------------------------------------------------------------
-- §1. n 奇: 方程退化为线性
--------------------------------------------------------------------------------

-- 若 x⊕y = z (非零元), 则奇次幂版本同样成立: 幂不改变线性关系.
flt-odd-linear : ∀ n x y z → x ≢₃ T₀ → y ≢₃ T₀ → z ≢₃ T₀ →
                 x ⊕ y ≡ z →
                 pow3 x (suc (n * 2)) ⊕ pow3 y (suc (n * 2)) ≡ pow3 z (suc (n * 2))
flt-odd-linear n x y z xz yz zz xy=z = begin
  pow3 x (suc (n * 2)) ⊕ pow3 y (suc (n * 2))
    ≡⟨ cong₂ _⊕_ (pow3-odd x xz n) (pow3-odd y yz n) ⟩
  x ⊕ y
    ≡⟨ xy=z ⟩
  z
    ≡⟨ sym (pow3-odd z zz n) ⟩
  pow3 z (suc (n * 2))
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §2. n 奇: 非零解存在 (1,1,2) 与 (2,2,1)
--------------------------------------------------------------------------------

-- 1 + 1 ≡ 2: 对任意奇指数成立
flt-mod3-sol-112 : ∀ n →
  pow3 T₁ (suc (n * 2)) ⊕ pow3 T₁ (suc (n * 2)) ≡ pow3 T₂ (suc (n * 2))
flt-mod3-sol-112 n = flt-odd-linear n T₁ T₁ T₂ (λ ()) (λ ()) (λ ()) refl
  -- refl : T₁ ⊕ T₁ ≡ T₂ (⊕ 定义); T₁ ≢ T₀, T₂ ≢ T₀ 为 λ()

-- 2 + 2 ≡ 1: 对任意奇指数成立
flt-mod3-sol-221 : ∀ n →
  pow3 T₂ (suc (n * 2)) ⊕ pow3 T₂ (suc (n * 2)) ≡ pow3 T₁ (suc (n * 2))
flt-mod3-sol-221 n = flt-odd-linear n T₂ T₂ T₁ (λ ()) (λ ()) (λ ()) refl
  -- refl : T₂ ⊕ T₂ ≡ T₁ (⊕ 定义: 2+2 = 4 ≡ 1)

--------------------------------------------------------------------------------
-- §3. n 偶: 非零三元无解
--------------------------------------------------------------------------------

-- 若 x,y,z 全非零, 偶次方程 1⊕1 = 1 不成立: 2 ≠ 1.
T2-not-T1 : T₂ ≡ T₁ → ⊥
T2-not-T1 ()

-- 偶次非零元之和的规范值: x^(2k) ⊕ y^(2k) = 1 ⊕ 1 = 2
even-lhs-value : ∀ n x y → x ≢₃ T₀ → y ≢₃ T₀ →
                 pow3 x (n * 2) ⊕ pow3 y (n * 2) ≡ T₂
even-lhs-value n x y xz yz = begin
  pow3 x (n * 2) ⊕ pow3 y (n * 2)
    ≡⟨ cong₂ _⊕_ (pow3-even x xz n) (pow3-even y yz n) ⟩
  T₁ ⊕ T₁
    ≡⟨⟩
  T₂
  ∎
  where open ≡-Reasoning

flt-even-nonsol : ∀ n x y z → x ≢₃ T₀ → y ≢₃ T₀ → z ≢₃ T₀ →
                  (pow3 x (n * 2) ⊕ pow3 y (n * 2)) ≢₃ pow3 z (n * 2)
flt-even-nonsol n x y z xz yz zz eq =
  T2-not-T1 (trans (sym (even-lhs-value n x y xz yz))
                   (trans eq (pow3-even z zz n)))

--------------------------------------------------------------------------------
-- §4. n 偶: 有解 ⇒ 至少一个变量为 0 (零通道)
--------------------------------------------------------------------------------

-- 偶次方程若有 (含零的) 解, 则 x 或 y 或 z 必为 0.
-- 提升到 ℤ 即: 偶次 FLT 反例必须满足 3 | abc — 幂等式穿过零通道
-- (13-flt-analysis.md §3.3: n 偶 ⇒ GF(3)× 无非零解 ⟹ 反例需 3|abc)
flt-even-zero-channel : ∀ n x y z →
                        pow3 x (n * 2) ⊕ pow3 y (n * 2) ≡ pow3 z (n * 2) →
                        x ≡ T₀ ⊎ y ≡ T₀ ⊎ z ≡ T₀
flt-even-zero-channel n x y z eq with zero-trit? x | zero-trit? y | zero-trit? z
flt-even-zero-channel n x y z eq | inj₁ xz | _       | _       = inj₁ xz
flt-even-zero-channel n x y z eq | inj₂ xz | inj₁ yz | _       = inj₂ (inj₁ yz)
flt-even-zero-channel n x y z eq | inj₂ xz | inj₂ yz | inj₁ zz = inj₂ (inj₂ zz)
flt-even-zero-channel n x y z eq | inj₂ xz | inj₂ yz | inj₂ zz =
  ⊥-elim (flt-even-nonsol n x y z xz yz zz eq)
