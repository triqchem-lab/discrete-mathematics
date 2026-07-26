{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.CommunicationDiscrete
-- 应用层：离散通信理论 (信道容量与 CRT 编码)
--
-- 层级: 应用数学 (全息文明投影)
-- GF(3) 合法身份: 模 3 整数算术 + CRT 正交分解
--
-- 定理清单:
--   1. 信道容量 = 4320: 引用 yao-4320
--   2. CRT 编码无损: 引用 crtTheorem
--
-- 0 postulate, 全部构造性证明, 穷举法优先

module Sovereign.Applied.CommunicationDiscrete where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _%_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.BurnsideT6
  using (yao-4320; independent-info-from-yao)
open import Sovereign.Format.CRT
  using (crtTheorem; crtProject; crtReconstruct; POW2; POW3; M)

--------------------------------------------------------------------------------
-- 1. 信道容量 = 4320
-- Shannon 信道容量: C = B·log₂(1+SNR)
-- 离散版本: 4320D 全息独立信息维度
-- 4320 = 729×6 - 54 (裸爻变空间 - 规范群阶)
-- 引用 BurnsideT6.yao-4320: independent-info-from-yao ≡ 4320
--------------------------------------------------------------------------------

-- 信道容量 = 4320 (引用 yao-4320)
channel-capacity-4320 : independent-info-from-yao ≡ 4320
channel-capacity-4320 = yao-4320

-- 数值验证: 729×6 - 54 = 4320
channel-capacity-arithmetic : 729 * 6 ∸ 54 ≡ 4320
channel-capacity-arithmetic = refl

--------------------------------------------------------------------------------
-- 2. CRT 编码无损: 中国剩余定理保证信息不丢失
-- 编码: x → (x mod 2¹⁶, x mod 3¹¹)
-- 解码: (a, b) → (a·T₁ + b·T₂) mod M
-- 定理: 解码(编码(x)) ≡ x mod M (在 M = 2¹⁶×3¹¹ 内无损)
-- 引用 CRT.crtTheorem
--------------------------------------------------------------------------------

-- CRT 编码-解码往返无损 (引用 crtTheorem)
crt-lossless : ∀ (x : ℕ) → crtReconstruct (crtProject x) ≡ x % M
crt-lossless = crtTheorem

-- CRT 模数: M = 2¹⁶ × 3¹¹ = 11609505792
crt-modulus : M ≡ 65536 * 177147
crt-modulus = refl
