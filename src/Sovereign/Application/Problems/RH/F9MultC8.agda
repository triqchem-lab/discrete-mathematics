{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.F9MultC8
-- F₉* ≅ C₈: 原生共轭性的乘法群来源（M8）
--
-- 数学背景（用户 2026-11-25 §六 陈述的**修正版**, oracle c8 模式全枚举核对 ✓）:
--   · F₉* 是循环群: 生成元 g = 1 + α, g⁸ = 1, 8 个幂两两不同（dist-g 28 条）;
--     离散对数 log_g : F₉* → ℤ/8 即**相位**。
--   · Frobenius σ = f9conj 在 C₈ 上作用 = k ↦ 3k (mod 8)（c8-sig 8 条）,
--     σ² = k ↦ 9k ≡ k（2 阶自同构）。
--   · **Norm 修正**: N(g^k) := g^k · σ(g^k) = g^(4k) ∈ F₃* = {±1}（c8-norm 8 条;
--     k 偶 ↦ +1, k 奇 ↦ −1）——「α⁴ = q = 9」不成立（初版陈述被枚举否证）:
--     域元素层 Norm 落在 F₃*; 「α·ᾱ = q」属**曲线 Frobenius 本征值层**
--     （Weil: π·π̄ = q, q=3 于 F₃ / F₉ 视基域则 π²·π̄² = 9）——两层不得混写。
--   · ℤ 对照（§六 修正版）: ℤ 的乘法结构 = 素数分解自由交换幺半群, 非群、
--     非循环、无相位 ⟹ 无原生共轭, 特征 0 须解析注入（与 ABCL1 加乘壁垒
--     no-injective-hom 同源: 加法/乘法两类同构的分离定理）。
--
-- 诚实边界:
--   · 本件是 **F₉* 乘法群层**的相位结构; 曲线 Frobenius 本征值层（Weil q-数）
--     在 WeilRecurrenceAll/E3Tor 承载（数值层）, 两层的桥（π·π̄=q 于 End）
--     属 B5 环论层, 未排期。
--   · 全件独立具名引理形态（nightly 坑#5/#6）; 表格 oracle c8 模式逐字生成。

module Sovereign.Application.Problems.RH.F9MultC8 where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Application.Problems.RH.CountF9All
open import Sovereign.Application.Problems.RH.FrobF9

--------------------------------------------------------------------------------
-- §1. 生成元与幂表（oracle c8 逐字; g = 1 + α, 阶 8）
--------------------------------------------------------------------------------

ggen : F9
ggen = mkF9 T₁ T₁

c8pow : ℕ → F9
c8pow zero = mkF9 T₁ T₀
c8pow (suc zero) = mkF9 T₁ T₁
c8pow (suc (suc zero)) = mkF9 T₀ T₂
c8pow (suc (suc (suc zero))) = mkF9 T₁ T₂
c8pow (suc (suc (suc (suc zero)))) = mkF9 T₂ T₀
c8pow (suc (suc (suc (suc (suc zero))))) = mkF9 T₂ T₂
c8pow (suc (suc (suc (suc (suc (suc zero)))))) = mkF9 T₀ T₁
c8pow (suc (suc (suc (suc (suc (suc (suc zero))))))) = mkF9 T₂ T₁
c8pow (suc (suc (suc (suc (suc (suc (suc (suc _)))))))) = mkF9 T₁ T₀  -- ≡ g⁰（ℤ/8 相位）

--------------------------------------------------------------------------------
-- §2. C₈: 8 个幂两两不同（28 条, () 拦截）
--------------------------------------------------------------------------------

dist-g0-1 : c8pow 0 ≢ c8pow 1
dist-g0-1 ()
dist-g0-2 : c8pow 0 ≢ c8pow 2
dist-g0-2 ()
dist-g0-3 : c8pow 0 ≢ c8pow 3
dist-g0-3 ()
dist-g0-4 : c8pow 0 ≢ c8pow 4
dist-g0-4 ()
dist-g0-5 : c8pow 0 ≢ c8pow 5
dist-g0-5 ()
dist-g0-6 : c8pow 0 ≢ c8pow 6
dist-g0-6 ()
dist-g0-7 : c8pow 0 ≢ c8pow 7
dist-g0-7 ()
dist-g1-2 : c8pow 1 ≢ c8pow 2
dist-g1-2 ()
dist-g1-3 : c8pow 1 ≢ c8pow 3
dist-g1-3 ()
dist-g1-4 : c8pow 1 ≢ c8pow 4
dist-g1-4 ()
dist-g1-5 : c8pow 1 ≢ c8pow 5
dist-g1-5 ()
dist-g1-6 : c8pow 1 ≢ c8pow 6
dist-g1-6 ()
dist-g1-7 : c8pow 1 ≢ c8pow 7
dist-g1-7 ()
dist-g2-3 : c8pow 2 ≢ c8pow 3
dist-g2-3 ()
dist-g2-4 : c8pow 2 ≢ c8pow 4
dist-g2-4 ()
dist-g2-5 : c8pow 2 ≢ c8pow 5
dist-g2-5 ()
dist-g2-6 : c8pow 2 ≢ c8pow 6
dist-g2-6 ()
dist-g2-7 : c8pow 2 ≢ c8pow 7
dist-g2-7 ()
dist-g3-4 : c8pow 3 ≢ c8pow 4
dist-g3-4 ()
dist-g3-5 : c8pow 3 ≢ c8pow 5
dist-g3-5 ()
dist-g3-6 : c8pow 3 ≢ c8pow 6
dist-g3-6 ()
dist-g3-7 : c8pow 3 ≢ c8pow 7
dist-g3-7 ()
dist-g4-5 : c8pow 4 ≢ c8pow 5
dist-g4-5 ()
dist-g4-6 : c8pow 4 ≢ c8pow 6
dist-g4-6 ()
dist-g4-7 : c8pow 4 ≢ c8pow 7
dist-g4-7 ()
dist-g5-6 : c8pow 5 ≢ c8pow 6
dist-g5-6 ()
dist-g5-7 : c8pow 5 ≢ c8pow 7
dist-g5-7 ()
dist-g6-7 : c8pow 6 ≢ c8pow 7
dist-g6-7 ()

--------------------------------------------------------------------------------
-- §3. σ 作用 = k ↦ 3k (mod 8)（c8-sig 8 条）
--------------------------------------------------------------------------------

c8-sig-0 : f9conj (c8pow 0) ≡ c8pow 0
c8-sig-0 = refl
c8-sig-1 : f9conj (c8pow 1) ≡ c8pow 3
c8-sig-1 = refl
c8-sig-2 : f9conj (c8pow 2) ≡ c8pow 6
c8-sig-2 = refl
c8-sig-3 : f9conj (c8pow 3) ≡ c8pow 1
c8-sig-3 = refl
c8-sig-4 : f9conj (c8pow 4) ≡ c8pow 4
c8-sig-4 = refl
c8-sig-5 : f9conj (c8pow 5) ≡ c8pow 7
c8-sig-5 = refl
c8-sig-6 : f9conj (c8pow 6) ≡ c8pow 2
c8-sig-6 = refl
c8-sig-7 : f9conj (c8pow 7) ≡ c8pow 5
c8-sig-7 = refl

--------------------------------------------------------------------------------
-- §4. Norm 落 F₃* = {±1}（c8-norm 8 条; 修正「α⁴=9」——枚举否证）
--------------------------------------------------------------------------------

c8-norm-0 : f9mul (c8pow 0) (f9conj (c8pow 0)) ≡ t2f9 T₁
c8-norm-0 = refl
c8-norm-1 : f9mul (c8pow 1) (f9conj (c8pow 1)) ≡ t2f9 T₂
c8-norm-1 = refl
c8-norm-2 : f9mul (c8pow 2) (f9conj (c8pow 2)) ≡ t2f9 T₁
c8-norm-2 = refl
c8-norm-3 : f9mul (c8pow 3) (f9conj (c8pow 3)) ≡ t2f9 T₂
c8-norm-3 = refl
c8-norm-4 : f9mul (c8pow 4) (f9conj (c8pow 4)) ≡ t2f9 T₁
c8-norm-4 = refl
c8-norm-5 : f9mul (c8pow 5) (f9conj (c8pow 5)) ≡ t2f9 T₂
c8-norm-5 = refl
c8-norm-6 : f9mul (c8pow 6) (f9conj (c8pow 6)) ≡ t2f9 T₁
c8-norm-6 = refl
c8-norm-7 : f9mul (c8pow 7) (f9conj (c8pow 7)) ≡ t2f9 T₂
c8-norm-7 = refl
