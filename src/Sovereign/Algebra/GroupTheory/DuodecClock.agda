{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.DuodecClock
-- 十二进制混合时钟 — 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩（加乘联合，非纯加法直积）
--
-- 核心原则:
--   · 十二进制 = 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩ ⊂ GF(9)*
--   · Z/3 = GF(3) 加法（三进制归零，+1 周期 3）
--   · ⟨α⟩ = GF(9) 乘法子群（90° 旋转，乘 α 四步回位，α² = -1）
--   · 抽象群同构于 Z/12（加法），语义是加乘联合周期，不是模 12 环。
--
-- ⚠️ 概念澄清（红线，不进证明链）:
--   传统 Z/12 环的乘法（模 12，有零因子如 2×6=0）不是本模块的乘法；
--   本模块第二个因子的乘法来自 GF(9) 域乘法（⟨α⟩ 是 GF(9)* 的 4 阶子群）。
--   禁挂「A₄ ≅ Z/12」或「A₄ 是十二进制」：A₄ = V₄⋊C₃，非交换。
--   命名约定 (2026-08-19 定稿): 正式符号 DuodecClock = Z/3_加 ⊕ ⟨α⟩_乘
--   （元素类型 DuodecPoint）。勿用 Doz —— 它与传统二面体群 D₁₂
--   （正六边形对称群，12 阶非交换）混淆；本结构是 12 阶交换联合周期。
--
-- 包含:
--   §1 乘法旋转 ⟨α⟩（AlphaPower + mulAlpha + GF(9) 嵌入）
--   §2 混合时钟点（DuodecPoint = Trit × AlphaPower, mixedOp）
--   §3 混合时钟是群（L2 全称符号证明，经分量公理）
--   §4 与 Z/12 加法同构（CRT 正交分解, 策略 E；混合运算 = +12, 144 case）
--   §5 语义锚点（char 3 归零、α 阶 4、12 = 3×4）
--
-- 数值锚定: /home/yanli/work/math cpp/tests/test_duodec_crt.cpp
--   ① 混合时钟 CRT 同态 144/144 PASS ② CRT 往返 12/12 PASS
--   ③ char-3 归零 / ord(α)=4 / GF(9)* 阶 8 无 12 阶元 / 12=3×4 全部 PASS
--
-- ── TurnBridge: 角度→转→群阶 换算表 ──────────────────────────
-- 语料锚: "克里斯托三步 180/90/45 (根号二规则)" + 感官换算表
-- 度数仅为十进制换算皮，本体是周期分数（转 = 圆周分数）。
--
-- | 群元素 | 转     | 度数    | 阶 | 语料锚           |
-- |--------|--------|---------|----|------------------|
-- | 1      | 0      | 0°     | 1  | 归零             |
-- | α      | 1/4    | 90°    | 4  | 克里斯托90°      |
-- | α²=-1  | 2/4    | 180°   | 2  | σ 对合/反转      |
-- | α³=-α  | 3/4    | 270°   | 4  | 断网态            |
-- | φ      | 1/8    | 45°    | 8  | 意识自转          |
-- | φ²=α   | 2/8    | 90°    | -- | 半步→全步         |
-- | φ⁴=-1  | 4/8    | 180°   | -- | 半圈             |
-- | φ⁶=-α  | 6/8    | 270°   | -- | 断网              |
-- | φ⁸=1   | 8/8    | 360°   | 1  | 全闭合            |
-- | -1     | 1/2    | 180°   | 2  | ⟨-1⟩ 最内层      |
--
-- ⚠️ 勘误: 语料 "触 1/64 转 = 5.5125°" 应为 5.625° (360/64)
-- ───────────────────────────────────────────────────────────────

module Sovereign.Algebra.GroupTheory.DuodecClock where

open import Data.Nat using (ℕ; _*_; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate;
         ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse; ⊕-comm)
open import Sovereign.Algebra.GF9
  using (GF9; gf9-one; gf9-zero; alpha; alpha-squared; alpha-powers-4;
         _+gf9_; _*gf9_; *gf9-assoc)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; π3; π4; crt12; crt12-roundtrip; crt12-inv-π3; crt12-inv-π4;
         _+12_; _*12_; d0; d1; d2; d4; d8)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 乘法旋转 ⟨α⟩ = {1, α, α², α³} — GF(9)* 的 4 阶乘法子群
--------------------------------------------------------------------------------

data AlphaPower : Set where
  a0 : AlphaPower   -- 1
  a1 : AlphaPower   -- α
  a2 : AlphaPower   -- α² = -1
  a3 : AlphaPower   -- α³ = -α

-- 乘法表: α^i · α^j = α^{i+j mod 4}
mulAlpha : AlphaPower → AlphaPower → AlphaPower
mulAlpha a0 x = x
mulAlpha a1 a0 = a1
mulAlpha a1 a1 = a2
mulAlpha a1 a2 = a3
mulAlpha a1 a3 = a0
mulAlpha a2 a0 = a2
mulAlpha a2 a1 = a3
mulAlpha a2 a2 = a0
mulAlpha a2 a3 = a1
mulAlpha a3 a0 = a3
mulAlpha a3 a1 = a0
mulAlpha a3 a2 = a1
mulAlpha a3 a3 = a2

-- 乘法逆元 (α^i)⁻¹ = α^{-i mod 4}
alphaInv : AlphaPower → AlphaPower
alphaInv a0 = a0
alphaInv a1 = a3
alphaInv a2 = a2
alphaInv a3 = a1

-- ⟨α⟩ 嵌入 GF(9): a_i ↦ α^i（乘法旋转的域锚定）
alphaPowerToGF9 : AlphaPower → GF9
alphaPowerToGF9 a0 = gf9-one
alphaPowerToGF9 a1 = alpha
alphaPowerToGF9 a2 = alpha *gf9 alpha
alphaPowerToGF9 a3 = (alpha *gf9 alpha) *gf9 alpha

-- 嵌入保乘法: ⟨α⟩ 的 mulAlpha 就是 GF(9) 域乘法在子群上的限制 (16 case refl)
mulAlpha-hom : ∀ x y → alphaPowerToGF9 (mulAlpha x y) ≡ alphaPowerToGF9 x *gf9 alphaPowerToGF9 y
mulAlpha-hom a0 a0 = refl
mulAlpha-hom a0 a1 = refl
mulAlpha-hom a0 a2 = refl
mulAlpha-hom a0 a3 = refl
mulAlpha-hom a1 a0 = refl
mulAlpha-hom a1 a1 = refl
mulAlpha-hom a1 a2 = refl
mulAlpha-hom a1 a3 = refl
mulAlpha-hom a2 a0 = refl
mulAlpha-hom a2 a1 = refl
mulAlpha-hom a2 a2 = refl
mulAlpha-hom a2 a3 = refl
mulAlpha-hom a3 a0 = refl
mulAlpha-hom a3 a1 = refl
mulAlpha-hom a3 a2 = refl
mulAlpha-hom a3 a3 = refl

-- 嵌入是单射 (16 case; 对角线 refl, 非对角线 λ ())
alphaPowerToGF9-injective : ∀ x y → alphaPowerToGF9 x ≡ alphaPowerToGF9 y → x ≡ y
alphaPowerToGF9-injective a0 a0 p = refl
alphaPowerToGF9-injective a0 a1 ()
alphaPowerToGF9-injective a0 a2 ()
alphaPowerToGF9-injective a0 a3 ()
alphaPowerToGF9-injective a1 a0 ()
alphaPowerToGF9-injective a1 a1 p = refl
alphaPowerToGF9-injective a1 a2 ()
alphaPowerToGF9-injective a1 a3 ()
alphaPowerToGF9-injective a2 a0 ()
alphaPowerToGF9-injective a2 a1 ()
alphaPowerToGF9-injective a2 a2 p = refl
alphaPowerToGF9-injective a2 a3 ()
alphaPowerToGF9-injective a3 a0 ()
alphaPowerToGF9-injective a3 a1 ()
alphaPowerToGF9-injective a3 a2 ()
alphaPowerToGF9-injective a3 a3 p = refl

-- 结合律: 经 GF(9) 域结合律 (*gf9-assoc) 迁移 (策略 B: 代数推导链)
mulAlpha-assoc : ∀ x y z → mulAlpha (mulAlpha x y) z ≡ mulAlpha x (mulAlpha y z)
mulAlpha-assoc x y z = alphaPowerToGF9-injective _ _ (begin
  alphaPowerToGF9 (mulAlpha (mulAlpha x y) z)
    ≡⟨ mulAlpha-hom (mulAlpha x y) z ⟩
  alphaPowerToGF9 (mulAlpha x y) *gf9 alphaPowerToGF9 z
    ≡⟨ cong (_*gf9 alphaPowerToGF9 z) (mulAlpha-hom x y) ⟩
  (alphaPowerToGF9 x *gf9 alphaPowerToGF9 y) *gf9 alphaPowerToGF9 z
    ≡⟨ *gf9-assoc (alphaPowerToGF9 x) (alphaPowerToGF9 y) (alphaPowerToGF9 z) ⟩
  alphaPowerToGF9 x *gf9 (alphaPowerToGF9 y *gf9 alphaPowerToGF9 z)
    ≡⟨ cong (alphaPowerToGF9 x *gf9_) (sym (mulAlpha-hom y z)) ⟩
  alphaPowerToGF9 x *gf9 alphaPowerToGF9 (mulAlpha y z)
    ≡⟨ sym (mulAlpha-hom x (mulAlpha y z)) ⟩
  alphaPowerToGF9 (mulAlpha x (mulAlpha y z))
  ∎)

-- 单位元
mulAlpha-identityˡ : ∀ x → mulAlpha a0 x ≡ x
mulAlpha-identityˡ x = refl

mulAlpha-identityʳ : ∀ x → mulAlpha x a0 ≡ x
mulAlpha-identityʳ a0 = refl
mulAlpha-identityʳ a1 = refl
mulAlpha-identityʳ a2 = refl
mulAlpha-identityʳ a3 = refl

-- 逆元
mulAlpha-inverse : ∀ x → mulAlpha x (alphaInv x) ≡ a0
mulAlpha-inverse a0 = refl
mulAlpha-inverse a1 = refl
mulAlpha-inverse a2 = refl
mulAlpha-inverse a3 = refl

-- 交换律 (循环群, 16 case refl)
mulAlpha-comm : ∀ x y → mulAlpha x y ≡ mulAlpha y x
mulAlpha-comm a0 a0 = refl
mulAlpha-comm a0 a1 = refl
mulAlpha-comm a0 a2 = refl
mulAlpha-comm a0 a3 = refl
mulAlpha-comm a1 a0 = refl
mulAlpha-comm a1 a1 = refl
mulAlpha-comm a1 a2 = refl
mulAlpha-comm a1 a3 = refl
mulAlpha-comm a2 a0 = refl
mulAlpha-comm a2 a1 = refl
mulAlpha-comm a2 a2 = refl
mulAlpha-comm a2 a3 = refl
mulAlpha-comm a3 a0 = refl
mulAlpha-comm a3 a1 = refl
mulAlpha-comm a3 a2 = refl
mulAlpha-comm a3 a3 = refl

--------------------------------------------------------------------------------
-- §2. 混合时钟点 — 加法步进 ⊕ 乘法旋转
--------------------------------------------------------------------------------

DuodecPoint : Set
DuodecPoint = Trit × AlphaPower

-- 混合运算: 第一分量 GF(3) 加法 (⊕), 第二分量 ⟨α⟩ 乘法 (mulAlpha)
mixedOp : DuodecPoint → DuodecPoint → DuodecPoint
mixedOp (x , a) (y , b) = (x ⊕ y , mulAlpha a b)

duodec-e : DuodecPoint
duodec-e = (T₀ , a0)

duodec-inv : DuodecPoint → DuodecPoint
duodec-inv (x , a) = (negate x , alphaInv a)

--------------------------------------------------------------------------------
-- §3. 混合时钟是群 — L2 全称符号证明（经分量公理组合，非穷举）
--------------------------------------------------------------------------------

mixedOp-assoc : ∀ p q r → mixedOp (mixedOp p q) r ≡ mixedOp p (mixedOp q r)
mixedOp-assoc (x , a) (y , b) (z , c) =
  cong₂ _,_ (⊕-assoc x y z) (mulAlpha-assoc a b c)

mixedOp-identityˡ : ∀ p → mixedOp duodec-e p ≡ p
mixedOp-identityˡ (x , a) = cong₂ _,_ (⊕-identityˡ x) (mulAlpha-identityˡ a)

mixedOp-identityʳ : ∀ p → mixedOp p duodec-e ≡ p
mixedOp-identityʳ (x , a) = cong₂ _,_ (⊕-identityʳ x) (mulAlpha-identityʳ a)

mixedOp-inverse : ∀ p → mixedOp p (duodec-inv p) ≡ duodec-e
mixedOp-inverse (x , a) = cong₂ _,_ (⊕-inverse x) (mulAlpha-inverse a)

-- 交换律: 两个分量皆交换 → 混合时钟是交换群（抽象层即 Z/12 加法）
mixedOp-comm : ∀ p q → mixedOp p q ≡ mixedOp q p
mixedOp-comm (x , a) (y , b) = cong₂ _,_ (⊕-comm x y) (mulAlpha-comm a b)

--------------------------------------------------------------------------------
-- §4. 与 Z/12 加法同构 — CRT 正交分解（策略 E: crt12/π3/π4 已证同构）
--------------------------------------------------------------------------------

-- ⟨α⟩ 旋转相位 ↔ Fin 4（CRT 的 mod-4 分量）双射
alphaToFin4 : AlphaPower → Fin 4
alphaToFin4 a0 = zero
alphaToFin4 a1 = suc zero
alphaToFin4 a2 = suc (suc zero)
alphaToFin4 a3 = suc (suc (suc zero))

fin4ToAlpha : Fin 4 → AlphaPower
fin4ToAlpha zero                   = a0
fin4ToAlpha (suc zero)             = a1
fin4ToAlpha (suc (suc zero))       = a2
fin4ToAlpha (suc (suc (suc zero))) = a3

fin4-alpha-roundtrip : ∀ n → alphaToFin4 (fin4ToAlpha n) ≡ n
fin4-alpha-roundtrip zero                   = refl
fin4-alpha-roundtrip (suc zero)             = refl
fin4-alpha-roundtrip (suc (suc zero))       = refl
fin4-alpha-roundtrip (suc (suc (suc zero))) = refl

alpha-fin4-roundtrip : ∀ a → fin4ToAlpha (alphaToFin4 a) ≡ a
alpha-fin4-roundtrip a0 = refl
alpha-fin4-roundtrip a1 = refl
alpha-fin4-roundtrip a2 = refl
alpha-fin4-roundtrip a3 = refl

-- 混合时钟 → Z/12 (CRT 重构: x = (4·z3 + 9·z4) mod 12)
toDuodec : DuodecPoint → Duodec
toDuodec (x , a) = crt12 x (alphaToFin4 a)

-- Z/12 → 混合时钟 (CRT 投影 π3/π4)
fromDuodec : Duodec → DuodecPoint
fromDuodec n = π3 n , fin4ToAlpha (π4 n)

-- 往返恒等 (复用 Duodecim 的 crt12-roundtrip / crt12-inv-π3 / crt12-inv-π4)
duodec-clock-roundtrip : ∀ n → toDuodec (fromDuodec n) ≡ n
duodec-clock-roundtrip n = begin
  crt12 (π3 n) (alphaToFin4 (fin4ToAlpha (π4 n)))
    ≡⟨ cong (λ k → crt12 (π3 n) k) (fin4-alpha-roundtrip (π4 n)) ⟩
  crt12 (π3 n) (π4 n)
    ≡⟨ crt12-roundtrip n ⟩
  n
  ∎

clock-duodec-roundtrip : ∀ p → fromDuodec (toDuodec p) ≡ p
clock-duodec-roundtrip (x , a) = cong₂ _,_
  (crt12-inv-π3 x (alphaToFin4 a))
  (trans (cong fin4ToAlpha (crt12-inv-π4 x (alphaToFin4 a)))
         (alpha-fin4-roundtrip a))

-- 联合时钟同态: 混合运算 (加法⊕乘法) 在抽象层 = Z/12 加法 (144 case refl,
-- 由 /home/yanli/work/math cpp/tests/test_duodec_crt.cpp 生成并验证 144/144)
mixed-to-+12 : ∀ p q → toDuodec (mixedOp p q) ≡ toDuodec p +12 toDuodec q
mixed-to-+12 (T₀ , a0) (T₀ , a0) = refl; mixed-to-+12 (T₀ , a0) (T₀ , a1) = refl; mixed-to-+12 (T₀ , a0) (T₀ , a2) = refl; mixed-to-+12 (T₀ , a0) (T₀ , a3) = refl; mixed-to-+12 (T₀ , a0) (T₁ , a0) = refl; mixed-to-+12 (T₀ , a0) (T₁ , a1) = refl; mixed-to-+12 (T₀ , a0) (T₁ , a2) = refl; mixed-to-+12 (T₀ , a0) (T₁ , a3) = refl; mixed-to-+12 (T₀ , a0) (T₂ , a0) = refl; mixed-to-+12 (T₀ , a0) (T₂ , a1) = refl; mixed-to-+12 (T₀ , a0) (T₂ , a2) = refl; mixed-to-+12 (T₀ , a0) (T₂ , a3) = refl
mixed-to-+12 (T₀ , a1) (T₀ , a0) = refl; mixed-to-+12 (T₀ , a1) (T₀ , a1) = refl; mixed-to-+12 (T₀ , a1) (T₀ , a2) = refl; mixed-to-+12 (T₀ , a1) (T₀ , a3) = refl; mixed-to-+12 (T₀ , a1) (T₁ , a0) = refl; mixed-to-+12 (T₀ , a1) (T₁ , a1) = refl; mixed-to-+12 (T₀ , a1) (T₁ , a2) = refl; mixed-to-+12 (T₀ , a1) (T₁ , a3) = refl; mixed-to-+12 (T₀ , a1) (T₂ , a0) = refl; mixed-to-+12 (T₀ , a1) (T₂ , a1) = refl; mixed-to-+12 (T₀ , a1) (T₂ , a2) = refl; mixed-to-+12 (T₀ , a1) (T₂ , a3) = refl
mixed-to-+12 (T₀ , a2) (T₀ , a0) = refl; mixed-to-+12 (T₀ , a2) (T₀ , a1) = refl; mixed-to-+12 (T₀ , a2) (T₀ , a2) = refl; mixed-to-+12 (T₀ , a2) (T₀ , a3) = refl; mixed-to-+12 (T₀ , a2) (T₁ , a0) = refl; mixed-to-+12 (T₀ , a2) (T₁ , a1) = refl; mixed-to-+12 (T₀ , a2) (T₁ , a2) = refl; mixed-to-+12 (T₀ , a2) (T₁ , a3) = refl; mixed-to-+12 (T₀ , a2) (T₂ , a0) = refl; mixed-to-+12 (T₀ , a2) (T₂ , a1) = refl; mixed-to-+12 (T₀ , a2) (T₂ , a2) = refl; mixed-to-+12 (T₀ , a2) (T₂ , a3) = refl
mixed-to-+12 (T₀ , a3) (T₀ , a0) = refl; mixed-to-+12 (T₀ , a3) (T₀ , a1) = refl; mixed-to-+12 (T₀ , a3) (T₀ , a2) = refl; mixed-to-+12 (T₀ , a3) (T₀ , a3) = refl; mixed-to-+12 (T₀ , a3) (T₁ , a0) = refl; mixed-to-+12 (T₀ , a3) (T₁ , a1) = refl; mixed-to-+12 (T₀ , a3) (T₁ , a2) = refl; mixed-to-+12 (T₀ , a3) (T₁ , a3) = refl; mixed-to-+12 (T₀ , a3) (T₂ , a0) = refl; mixed-to-+12 (T₀ , a3) (T₂ , a1) = refl; mixed-to-+12 (T₀ , a3) (T₂ , a2) = refl; mixed-to-+12 (T₀ , a3) (T₂ , a3) = refl
mixed-to-+12 (T₁ , a0) (T₀ , a0) = refl; mixed-to-+12 (T₁ , a0) (T₀ , a1) = refl; mixed-to-+12 (T₁ , a0) (T₀ , a2) = refl; mixed-to-+12 (T₁ , a0) (T₀ , a3) = refl; mixed-to-+12 (T₁ , a0) (T₁ , a0) = refl; mixed-to-+12 (T₁ , a0) (T₁ , a1) = refl; mixed-to-+12 (T₁ , a0) (T₁ , a2) = refl; mixed-to-+12 (T₁ , a0) (T₁ , a3) = refl; mixed-to-+12 (T₁ , a0) (T₂ , a0) = refl; mixed-to-+12 (T₁ , a0) (T₂ , a1) = refl; mixed-to-+12 (T₁ , a0) (T₂ , a2) = refl; mixed-to-+12 (T₁ , a0) (T₂ , a3) = refl
mixed-to-+12 (T₁ , a1) (T₀ , a0) = refl; mixed-to-+12 (T₁ , a1) (T₀ , a1) = refl; mixed-to-+12 (T₁ , a1) (T₀ , a2) = refl; mixed-to-+12 (T₁ , a1) (T₀ , a3) = refl; mixed-to-+12 (T₁ , a1) (T₁ , a0) = refl; mixed-to-+12 (T₁ , a1) (T₁ , a1) = refl; mixed-to-+12 (T₁ , a1) (T₁ , a2) = refl; mixed-to-+12 (T₁ , a1) (T₁ , a3) = refl; mixed-to-+12 (T₁ , a1) (T₂ , a0) = refl; mixed-to-+12 (T₁ , a1) (T₂ , a1) = refl; mixed-to-+12 (T₁ , a1) (T₂ , a2) = refl; mixed-to-+12 (T₁ , a1) (T₂ , a3) = refl
mixed-to-+12 (T₁ , a2) (T₀ , a0) = refl; mixed-to-+12 (T₁ , a2) (T₀ , a1) = refl; mixed-to-+12 (T₁ , a2) (T₀ , a2) = refl; mixed-to-+12 (T₁ , a2) (T₀ , a3) = refl; mixed-to-+12 (T₁ , a2) (T₁ , a0) = refl; mixed-to-+12 (T₁ , a2) (T₁ , a1) = refl; mixed-to-+12 (T₁ , a2) (T₁ , a2) = refl; mixed-to-+12 (T₁ , a2) (T₁ , a3) = refl; mixed-to-+12 (T₁ , a2) (T₂ , a0) = refl; mixed-to-+12 (T₁ , a2) (T₂ , a1) = refl; mixed-to-+12 (T₁ , a2) (T₂ , a2) = refl; mixed-to-+12 (T₁ , a2) (T₂ , a3) = refl
mixed-to-+12 (T₁ , a3) (T₀ , a0) = refl; mixed-to-+12 (T₁ , a3) (T₀ , a1) = refl; mixed-to-+12 (T₁ , a3) (T₀ , a2) = refl; mixed-to-+12 (T₁ , a3) (T₀ , a3) = refl; mixed-to-+12 (T₁ , a3) (T₁ , a0) = refl; mixed-to-+12 (T₁ , a3) (T₁ , a1) = refl; mixed-to-+12 (T₁ , a3) (T₁ , a2) = refl; mixed-to-+12 (T₁ , a3) (T₁ , a3) = refl; mixed-to-+12 (T₁ , a3) (T₂ , a0) = refl; mixed-to-+12 (T₁ , a3) (T₂ , a1) = refl; mixed-to-+12 (T₁ , a3) (T₂ , a2) = refl; mixed-to-+12 (T₁ , a3) (T₂ , a3) = refl
mixed-to-+12 (T₂ , a0) (T₀ , a0) = refl; mixed-to-+12 (T₂ , a0) (T₀ , a1) = refl; mixed-to-+12 (T₂ , a0) (T₀ , a2) = refl; mixed-to-+12 (T₂ , a0) (T₀ , a3) = refl; mixed-to-+12 (T₂ , a0) (T₁ , a0) = refl; mixed-to-+12 (T₂ , a0) (T₁ , a1) = refl; mixed-to-+12 (T₂ , a0) (T₁ , a2) = refl; mixed-to-+12 (T₂ , a0) (T₁ , a3) = refl; mixed-to-+12 (T₂ , a0) (T₂ , a0) = refl; mixed-to-+12 (T₂ , a0) (T₂ , a1) = refl; mixed-to-+12 (T₂ , a0) (T₂ , a2) = refl; mixed-to-+12 (T₂ , a0) (T₂ , a3) = refl
mixed-to-+12 (T₂ , a1) (T₀ , a0) = refl; mixed-to-+12 (T₂ , a1) (T₀ , a1) = refl; mixed-to-+12 (T₂ , a1) (T₀ , a2) = refl; mixed-to-+12 (T₂ , a1) (T₀ , a3) = refl; mixed-to-+12 (T₂ , a1) (T₁ , a0) = refl; mixed-to-+12 (T₂ , a1) (T₁ , a1) = refl; mixed-to-+12 (T₂ , a1) (T₁ , a2) = refl; mixed-to-+12 (T₂ , a1) (T₁ , a3) = refl; mixed-to-+12 (T₂ , a1) (T₂ , a0) = refl; mixed-to-+12 (T₂ , a1) (T₂ , a1) = refl; mixed-to-+12 (T₂ , a1) (T₂ , a2) = refl; mixed-to-+12 (T₂ , a1) (T₂ , a3) = refl
mixed-to-+12 (T₂ , a2) (T₀ , a0) = refl; mixed-to-+12 (T₂ , a2) (T₀ , a1) = refl; mixed-to-+12 (T₂ , a2) (T₀ , a2) = refl; mixed-to-+12 (T₂ , a2) (T₀ , a3) = refl; mixed-to-+12 (T₂ , a2) (T₁ , a0) = refl; mixed-to-+12 (T₂ , a2) (T₁ , a1) = refl; mixed-to-+12 (T₂ , a2) (T₁ , a2) = refl; mixed-to-+12 (T₂ , a2) (T₁ , a3) = refl; mixed-to-+12 (T₂ , a2) (T₂ , a0) = refl; mixed-to-+12 (T₂ , a2) (T₂ , a1) = refl; mixed-to-+12 (T₂ , a2) (T₂ , a2) = refl; mixed-to-+12 (T₂ , a2) (T₂ , a3) = refl
mixed-to-+12 (T₂ , a3) (T₀ , a0) = refl; mixed-to-+12 (T₂ , a3) (T₀ , a1) = refl; mixed-to-+12 (T₂ , a3) (T₀ , a2) = refl; mixed-to-+12 (T₂ , a3) (T₀ , a3) = refl; mixed-to-+12 (T₂ , a3) (T₁ , a0) = refl; mixed-to-+12 (T₂ , a3) (T₁ , a1) = refl; mixed-to-+12 (T₂ , a3) (T₁ , a2) = refl; mixed-to-+12 (T₂ , a3) (T₁ , a3) = refl; mixed-to-+12 (T₂ , a3) (T₂ , a0) = refl; mixed-to-+12 (T₂ , a3) (T₂ , a1) = refl; mixed-to-+12 (T₂ , a3) (T₂ , a2) = refl; mixed-to-+12 (T₂ , a3) (T₂ , a3) = refl

--------------------------------------------------------------------------------
-- §5. 语义锚点 — char 3 归零与 α 阶 4（联合周期 12 = 3 × 4）
--------------------------------------------------------------------------------

-- GF(9) 的特征 = 3: 1 + 1 + 1 = 0（素域步进的三进制归零）
gf9-char-3 : gf9-one +gf9 (gf9-one +gf9 gf9-one) ≡ gf9-zero
gf9-char-3 = refl

-- α 的旋转阶 = 4: α⁴ = 1（90° 四步回位）
alpha-rotation-order-4 : (alpha *gf9 alpha) *gf9 (alpha *gf9 alpha) ≡ gf9-one
alpha-rotation-order-4 = alpha-powers-4

-- α² = -1 ≡ 2
alpha-squared-is-neg-one : alpha *gf9 alpha ≡ (T₂ , T₀)
alpha-squared-is-neg-one = alpha-squared

-- 联合周期数值: 12 = 3 × 4 = char(GF(9)) × ord(α)
joint-period-12 : 3 * 4 ≡ 12
joint-period-12 = refl

--------------------------------------------------------------------------------
-- 结论:
--   十二进制 = 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩（混合时钟 DuodecPoint）。
--   mixedOp 是群（§3 交换群），经 CRT 同构于 Z/12 加法（§4: 双射往返 +
--   同态 mixed-to-+12 144/144），12 = char(GF(9)) × ord(α) = 3 × 4（§5）。
--   抽象群同构于 Z/12，但语义是加乘联合周期；模 12 环乘法不参与。
--------------------------------------------------------------------------------

-- 0 postulate.

--------------------------------------------------------------------------------
-- §6. P1 证明新增：防混淆 + 零冥族 + 联合周期
--------------------------------------------------------------------------------

-- §6a. 防混淆证明: mulAlpha ≠ *12 (经 toDuodec 投影)
-- 这证明 DuodecClock 的乘法 (mulAlpha) 与 Duodecimal 的环乘法 (*12) 不同。
-- 反例: (T₁, a1) 在 DuodecClock 自乘 = (T₁⊕T₁, mulAlpha a1 a1) = (T₂, a2)
--   但在 Duodecimal 中: toDuodec(T₁,a1) = d1, d1 *12 d1 = d1
--   而 toDuodec(T₂,a2) = d2, d2 ≠ d1 — mulAlpha 与 *12 不同

-- 计算 toDuodec (T₁, a1) = crt12 T₁ (alphaToFin4 a1) = crt12 T₁ (suc zero) = d1
toDuodec-Ta1 : toDuodec (T₁ , a1) ≡ d1
toDuodec-Ta1 = refl

-- 计算 toDuodec (T₂, a2) = crt12 T₂ (suc (suc zero)) = d2
toDuodec-Ta2 : toDuodec (T₂ , a2) ≡ d2
toDuodec-Ta2 = refl

-- 计算 d1 *12 d1 = d1
d1-mul-d1 : d1 *12 d1 ≡ d1
d1-mul-d1 = refl

-- 计算 d2 ≠ d1
d2-not-d1 : d2 ≡ d1 → ⊥
d2-not-d1 ()

-- 防混淆定理: mulAlpha 经 toDuodec 不等于 *12
-- 证据: toDuodec(mixedOp (T₁,a1) (T₁,a1)) = toDuodec (T₂,a2) = d2,
--       但 toDuodec(T₁,a1) *12 toDuodec(T₁,a1) = d1 *12 d1 = d1, 而 d2 ≠ d1
mulAlpha-not-*12 :
  Σ (DuodecPoint × DuodecPoint)
    (λ (p , q) → toDuodec (mixedOp p q) ≢ (toDuodec p) *12 (toDuodec q))
mulAlpha-not-*12 =
  ((T₁ , a1) , (T₁ , a1)) , λ eq → d2-not-d1 (trans lhs (trans eq rhs))
  where
  open ≡-Reasoning
  -- 左端: toDuodec(mixedOp (T₁,a1) (T₁,a1)) = toDuodec (T₂,a2) = d2
  lhs : toDuodec (mixedOp (T₁ , a1) (T₁ , a1)) ≡ d2
  lhs = begin
    toDuodec (mixedOp (T₁ , a1) (T₁ , a1))  ≡⟨ refl ⟩
    toDuodec (T₂ , a2)                      ≡⟨ toDuodec-Ta2 ⟩
    d2                                      ∎
  -- 右端: toDuodec (T₁,a1) *12 toDuodec (T₁,a1) = d1 *12 d1 = d1
  rhs : (toDuodec (T₁ , a1)) *12 (toDuodec (T₁ , a1)) ≡ d1
  rhs = begin
    (toDuodec (T₁ , a1)) *12 (toDuodec (T₁ , a1))  ≡⟨ cong₂ _*12_ toDuodec-Ta1 toDuodec-Ta1 ⟩
    d1 *12 d1                                      ≡⟨ d1-mul-d1 ⟩
    d1                                              ∎

-- §6a′. 迭代记法定义 (缺失定义桥接层)
--   §6b/§6c 的 record 字段与定理使用 mixedOp^12 / mulAlpha^4 记法, 但从未定义.
--   此处补定义为显式迭代, 语义:
--     mulAlpha^4 a = a 沿 α 平移 4 次 (α 阶 4 → 回 a)
--     mixedOp^12 p = p 沿联合生成元 g = (T₁,a1) 平移 12 次 (g 阶 12 → 回 p)
--   g 阶 12 由分量给出: 损益 ⊕¹² = id (12 mod 3 = 0), 相位 mulAlpha¹² = id (α⁴=1).
--   这使 mixedOp-12-cycle : ∀ p → mixedOp^12 p ≡ p 的 12 个 refl case 成立.

-- α 的 4 次迭代 (α 阶 4: a 沿 α 平移 4 次回到 a)
mulAlpha^4 : AlphaPower → AlphaPower
mulAlpha^4 a = mulAlpha a (mulAlpha a (mulAlpha a (mulAlpha a a0)))

-- 联合生成元 12 次平移: mixedOp 是二元, ^12 p = g·(g·(…·(g·p))) (12 个 g 左乘), g = (T₁,a1).
-- 因 mixedOp 交换, 左乘与右乘等价, 结果恒为 p (g 阶 12).
mixedOp^12 : DuodecPoint → DuodecPoint
mixedOp^12 p = mixedOp g (mixedOp g (mixedOp g (mixedOp g (mixedOp g (mixedOp g
             (mixedOp g (mixedOp g (mixedOp g (mixedOp g (mixedOp g
             (mixedOp g p)))))))))))
  where g = (T₁ , a1)

-- §6b. 零冥族 (ZeroOblivion) 形式化
-- 零冥族: 多维相位同时回到单位元的状态

record ZeroOblivion : Set where
  field
    -- 加法零冥: x + 0 = x (零 = duodec-e, 与 DCGroup 的实例一致)
    addZeroR : ∀ x → mixedOp x duodec-e ≡ x
    addZeroL : ∀ x → mixedOp duodec-e x ≡ x
    -- 乘法零冥: α⁴ = 1 ((a1·a1)·a1)·a1 = a0
    mulAlphaCycle : mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0
    -- 损益零冥: x ⊕ x ⊕ x = T₀
    tritCycle : ∀ x → (x ⊕ x) ⊕ x ≡ T₀
    -- 联合零冥: mixedOp^12 = id
    jointCycle : ∀ p → mixedOp^12 p ≡ p

-- §6c. 联合周期证明: mixedOp^12 = id
-- 证明策略: 分量独立
--   损益分量: ⊕³ = id (char 3)
--   相位分量: α⁴ = id (ord 4)
--   联合: LCM(3,4) = 12

-- 损益分量: ⊕³ = id
trit-cubed : ∀ x → (x ⊕ x) ⊕ x ≡ T₀
trit-cubed T₀ = refl
trit-cubed T₁ = refl
trit-cubed T₂ = refl

-- 相位分量: α⁴ = id (已在 alpha-order-4 中证明)

-- 联合周期: mixedOp^12 = id
-- 证明: 分量独立，损益 3 步归零，相位 4 步归零，12 = LCM(3,4)

-- 辅助引理: mixedOp^3 在损益分量上归零
mixedOp-cubed-trit : ∀ (t : Trit) (a : AlphaPower) →
  proj₁ (mixedOp (mixedOp (mixedOp (t , a) (t , a)) (t , a)) (T₀ , a0)) ≡ T₀
mixedOp-cubed-trit T₀ a = refl
mixedOp-cubed-trit T₁ a = refl
mixedOp-cubed-trit T₂ a = refl

-- 辅助引理: mixedOp^4 在相位分量上归零
mixedOp-fourth-alpha : ∀ (t : Trit) (a : AlphaPower) →
  proj₂ (mixedOp (mixedOp (mixedOp (mixedOp (t , a) (T₀ , a1)) (T₀ , a1)) (T₀ , a1)) (T₀ , a1)) ≡ a
mixedOp-fourth-alpha t a0 = refl
mixedOp-fourth-alpha t a1 = refl
mixedOp-fourth-alpha t a2 = refl
mixedOp-fourth-alpha t a3 = refl

-- 联合周期定理 (简化版): 12 步联合运算回到原点
-- 完整证明需要展开 12 步 mixedOp，此处给出结构框架
-- 实际证明通过穷举 12×12 = 144 case 完成（与 mixed-to-+12 类似）

-- 联合周期声明 (待完整证明)
-- 联合周期定理: 12 步联合运算回到原点
-- 策略: 穷举法 (12 case refl) + 代数推导链
-- 原理: 12 mod 3 = 0 (损益归零), 12 mod 4 = 0 (相位归零)

-- 辅助引理: mixedOp^12 在损益分量上归零
mixedOp-12-trit : ∀ (t : Trit) (a : AlphaPower) →
  proj₁ (mixedOp^12 (t , a)) ≡ t
mixedOp-12-trit T₀ a = refl
mixedOp-12-trit T₁ a = refl
mixedOp-12-trit T₂ a = refl

-- 辅助引理: mixedOp^12 在相位分量上归零
mixedOp-12-alpha : ∀ (t : Trit) (a : AlphaPower) →
  proj₂ (mixedOp^12 (t , a)) ≡ a
mixedOp-12-alpha t a0 = refl
mixedOp-12-alpha t a1 = refl
mixedOp-12-alpha t a2 = refl
mixedOp-12-alpha t a3 = refl

-- 完整证明: mixedOp^12 = id (穷举 12 case refl)
mixedOp-12-cycle : ∀ p → mixedOp^12 p ≡ p
mixedOp-12-cycle (T₀ , a0) = refl
mixedOp-12-cycle (T₀ , a1) = refl
mixedOp-12-cycle (T₀ , a2) = refl
mixedOp-12-cycle (T₀ , a3) = refl
mixedOp-12-cycle (T₁ , a0) = refl
mixedOp-12-cycle (T₁ , a1) = refl
mixedOp-12-cycle (T₁ , a2) = refl
mixedOp-12-cycle (T₁ , a3) = refl
mixedOp-12-cycle (T₂ , a0) = refl
mixedOp-12-cycle (T₂ , a1) = refl
mixedOp-12-cycle (T₂ , a2) = refl
mixedOp-12-cycle (T₂ , a3) = refl

-- α 的 4 次自乘 = a0 (供 ZeroOblivion.mulAlphaCycle 填充)
mulAlpha-4-a1 : mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0
mulAlpha-4-a1 = refl

-- 零冥族实例
zero-oblivion-instance : ZeroOblivion
zero-oblivion-instance = record
  { addZeroR = mixedOp-identityʳ
  ; addZeroL = mixedOp-identityˡ
  ; mulAlphaCycle = mulAlpha-4-a1
  ; tritCycle = trit-cubed
  ; jointCycle = mixedOp-12-cycle
  }

-- §6c′. 三反射定义 (缺失定义桥接层)
--   §6d-§6f 引用 lambda/mu/rho 三个反射但从未定义. 由文件注释补定义:
--     lambda (损益反射): (t, a) ↦ (negate t, a)
--     mu     (相位反射): (t, a) ↦ (t, a⁻¹)
--     rho    (联合反射): λ ∘ μ
--   零元 (T₀,a0) 是三者公共不动点 (zero-fixed-* 引理).

lambda : DuodecPoint → DuodecPoint
lambda (t , a) = (negate t , a)

mu : DuodecPoint → DuodecPoint
mu (t , a) = (t , alphaInv a)

rho : DuodecPoint → DuodecPoint
rho p = lambda (mu p)

-- ρ 对合: rho (rho p) = p (lambda 与 mu 均对合且交换, 穷举 refl)
rho-involution : ∀ p → rho (rho p) ≡ p
rho-involution (T₀ , a0) = refl
rho-involution (T₀ , a1) = refl
rho-involution (T₀ , a2) = refl
rho-involution (T₀ , a3) = refl
rho-involution (T₁ , a0) = refl
rho-involution (T₁ , a1) = refl
rho-involution (T₁ , a2) = refl
rho-involution (T₁ , a3) = refl
rho-involution (T₂ , a0) = refl
rho-involution (T₂ , a1) = refl
rho-involution (T₂ , a2) = refl
rho-involution (T₂ , a3) = refl

-- ── ρ 的代数性质层 (rho 属 DC 群论层; 从谱层上提, DihedralD12 等复用) ──

-- 分量自同态: negate 保持 ⊕ (9 case)
rho-neg-homo : ∀ x y → negate (x ⊕ y) ≡ negate x ⊕ negate y
rho-neg-homo T₀ T₀ = refl; rho-neg-homo T₀ T₁ = refl; rho-neg-homo T₀ T₂ = refl
rho-neg-homo T₁ T₀ = refl; rho-neg-homo T₁ T₁ = refl; rho-neg-homo T₁ T₂ = refl
rho-neg-homo T₂ T₀ = refl; rho-neg-homo T₂ T₁ = refl; rho-neg-homo T₂ T₂ = refl

-- 分量自同态: alphaInv 保持 mulAlpha (16 case; C₄ 交换故同/反同态重合)
rho-alphaInv-homo : ∀ a b →
  alphaInv (mulAlpha a b) ≡ mulAlpha (alphaInv a) (alphaInv b)
rho-alphaInv-homo a0 a0 = refl; rho-alphaInv-homo a0 a1 = refl
rho-alphaInv-homo a0 a2 = refl; rho-alphaInv-homo a0 a3 = refl
rho-alphaInv-homo a1 a0 = refl; rho-alphaInv-homo a1 a1 = refl
rho-alphaInv-homo a1 a2 = refl; rho-alphaInv-homo a1 a3 = refl
rho-alphaInv-homo a2 a0 = refl; rho-alphaInv-homo a2 a1 = refl
rho-alphaInv-homo a2 a2 = refl; rho-alphaInv-homo a2 a3 = refl
rho-alphaInv-homo a3 a0 = refl; rho-alphaInv-homo a3 a1 = refl
rho-alphaInv-homo a3 a2 = refl; rho-alphaInv-homo a3 a3 = refl

-- ρ 是 mixedOp 自同态: rho(x·y) = rho(x)·rho(y)
rho-mixedOp : ∀ p q → rho (mixedOp p q) ≡ mixedOp (rho p) (rho q)
rho-mixedOp (x , a) (y , b) =
  cong₂ _,_ (rho-neg-homo x y) (rho-alphaInv-homo a b)

-- ρ = 逆元: rho p ≡ duodec-inv p (两者定义逐字相同: (negate t, alphaInv a), 12 case)
rho-is-inv : ∀ p → rho p ≡ duodec-inv p
rho-is-inv (T₀ , a0) = refl
rho-is-inv (T₀ , a1) = refl
rho-is-inv (T₀ , a2) = refl
rho-is-inv (T₀ , a3) = refl
rho-is-inv (T₁ , a0) = refl
rho-is-inv (T₁ , a1) = refl
rho-is-inv (T₁ , a2) = refl
rho-is-inv (T₁ , a3) = refl
rho-is-inv (T₂ , a0) = refl
rho-is-inv (T₂ , a1) = refl
rho-is-inv (T₂ , a2) = refl
rho-is-inv (T₂ , a3) = refl

-- 逻辑等价 (本地, 双向蕴含): A ↔ B = (A → B) × (B → A)
-- 避免引入 Function.Bundles 的 _↔_ (proof 结构就是双向函数的积)
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

-- §6d. 零冥族与反射不动点
-- 零元 (T₀, a0) 在三个反射下不动

-- 损益反射 λ: (t, a) ↦ (negate t, a)
-- λ(T₀, a0) = (negate T₀, a0) = (T₀, a0)
zero-fixed-lambda : lambda duodec-e ≡ duodec-e
zero-fixed-lambda = refl

-- 相位反射 μ: (t, a) ↦ (t, a⁻¹)
-- μ(T₀, a0) = (T₀, a0) 因为 a0⁻¹ = a0
zero-fixed-mu : mu duodec-e ≡ duodec-e
zero-fixed-mu = refl

-- 联合反射 ρ = λ∘μ
-- ρ(T₀, a0) = (T₀, a0)
zero-fixed-rho : rho duodec-e ≡ duodec-e
zero-fixed-rho = refl

-- 零元在所有三个反射下不动
zero-fixed-all : (lambda duodec-e ≡ duodec-e) ×
                 (mu duodec-e ≡ duodec-e) ×
                 (rho duodec-e ≡ duodec-e)
zero-fixed-all = zero-fixed-lambda , zero-fixed-mu , zero-fixed-rho

-- §6e. 真空态唯一性
-- 零元是唯一的三反射不动点
-- 证明: 展开 12 种情况，只有 (T₀, a0) 满足 λ(x)=x ∧ μ(x)=x ∧ ρ(x)=x

-- 辅助引理: λ(x)=x ↔ t=T₀
lambda-fixed-char : ∀ t a → (lambda (t , a) ≡ (t , a)) ↔ (t ≡ T₀)
lambda-fixed-char T₀ a = (λ _ → refl) , (λ _ → refl)
lambda-fixed-char T₁ a = (λ ()) , (λ ())
lambda-fixed-char T₂ a = (λ ()) , (λ ())

-- 辅助引理: μ(x)=x ↔ a=a0
-- μ 不动点: a ≡ a0 或 a ≡ a2（因为 alphaInv a0 = a0, alphaInv a2 = a2）
mu-fixed-char : ∀ t a → (mu (t , a) ≡ (t , a)) ↔ (a ≡ a0 ⊎ a ≡ a2)
mu-fixed-char T₀ a0 = (λ _ → inj₁ refl) , (λ _ → refl)
mu-fixed-char T₀ a1 = (λ ()) , (λ { (inj₁ ()) ; (inj₂ ()) })
mu-fixed-char T₀ a2 = (λ _ → inj₂ refl) , (λ _ → refl)
mu-fixed-char T₀ a3 = (λ ()) , (λ { (inj₁ ()) ; (inj₂ ()) })
mu-fixed-char T₁ a0 = (λ _ → inj₁ refl) , (λ _ → refl)
mu-fixed-char T₁ a1 = (λ ()) , (λ { (inj₁ ()) ; (inj₂ ()) })
mu-fixed-char T₁ a2 = (λ _ → inj₂ refl) , (λ _ → refl)
mu-fixed-char T₁ a3 = (λ ()) , (λ { (inj₁ ()) ; (inj₂ ()) })
mu-fixed-char T₂ a0 = (λ _ → inj₁ refl) , (λ _ → refl)
mu-fixed-char T₂ a1 = (λ ()) , (λ { (inj₁ ()) ; (inj₂ ()) })
mu-fixed-char T₂ a2 = (λ _ → inj₂ refl) , (λ _ → refl)
mu-fixed-char T₂ a3 = (λ ()) , (λ { (inj₁ ()) ; (inj₂ ()) })

-- 辅助引理: ρ(x)=x ↔ t=T₀ ∧ (a=a0 ∨ a=a2)
-- Fix(ρ) = Fix(λ) ∩ Fix(μ) = {(T₀,a0), (T₀,a2)} (见下注释)
rho-fixed-char : ∀ t a → (rho (t , a) ≡ (t , a)) ↔ (t ≡ T₀ × (a ≡ a0 ⊎ a ≡ a2))
rho-fixed-char T₀ a0 = (λ _ → refl , inj₁ refl) , λ _ → refl
rho-fixed-char T₀ a1 = (λ ()) , λ { (refl , inj₁ ()) ; (refl , inj₂ ()) }
rho-fixed-char T₀ a2 = (λ _ → refl , inj₂ refl) , λ _ → refl
rho-fixed-char T₀ a3 = (λ ()) , λ { (refl , inj₁ ()) ; (refl , inj₂ ()) }
rho-fixed-char T₁ a0 = (λ ()) , λ { (() , _) }
rho-fixed-char T₁ a1 = (λ ()) , λ { (() , _) }
rho-fixed-char T₁ a2 = (λ ()) , λ { (() , _) }
rho-fixed-char T₁ a3 = (λ ()) , λ { (() , _) }
rho-fixed-char T₂ a0 = (λ ()) , λ { (() , _) }
rho-fixed-char T₂ a1 = (λ ()) , λ { (() , _) }
rho-fixed-char T₂ a2 = (λ ()) , λ { (() , _) }
rho-fixed-char T₂ a3 = (λ ()) , λ { (() , _) }

-- 三反射不动点恰好有两个: (T₀, a0) 和 (T₀, a2)
-- Fix(λ) = {(T₀, α^k) : k=0,1,2,3}
-- Fix(μ) = {(t, a0), (t, a2) : t∈F₃}
-- Fix(ρ) = Fix(λ) ∩ Fix(μ) = {(T₀, a0), (T₀, a2)}

vacuum-unique : ∀ x → (lambda x ≡ x) × (mu x ≡ x) × (rho x ≡ x)
  → (x ≡ duodec-e) ⊎ (x ≡ (T₀ , a2))
vacuum-unique (T₀ , a0) _ = inj₁ refl
vacuum-unique (T₀ , a1) (_ , mu-fix , _) with mu-fixed-char T₀ a1 .proj₁ mu-fix
vacuum-unique (T₀ , a1) (_ , mu-fix , _) | inj₁ ()
vacuum-unique (T₀ , a1) (_ , mu-fix , _) | inj₂ ()
vacuum-unique (T₀ , a2) _ = inj₂ refl
vacuum-unique (T₀ , a3) (_ , mu-fix , _) with mu-fixed-char T₀ a3 .proj₁ mu-fix
vacuum-unique (T₀ , a3) (_ , mu-fix , _) | inj₁ ()
vacuum-unique (T₀ , a3) (_ , mu-fix , _) | inj₂ ()
vacuum-unique (T₁ , a0) (lam-fix , _ , _) with lambda-fixed-char T₁ a0 .proj₁ lam-fix
vacuum-unique (T₁ , a0) (lam-fix , _ , _) | ()
vacuum-unique (T₁ , a1) (lam-fix , _ , _) with lambda-fixed-char T₁ a1 .proj₁ lam-fix
vacuum-unique (T₁ , a1) (lam-fix , _ , _) | ()
vacuum-unique (T₁ , a2) (lam-fix , _ , _) with lambda-fixed-char T₁ a2 .proj₁ lam-fix
vacuum-unique (T₁ , a2) (lam-fix , _ , _) | ()
vacuum-unique (T₁ , a3) (lam-fix , _ , _) with lambda-fixed-char T₁ a3 .proj₁ lam-fix
vacuum-unique (T₁ , a3) (lam-fix , _ , _) | ()
vacuum-unique (T₂ , a0) (lam-fix , _ , _) with lambda-fixed-char T₂ a0 .proj₁ lam-fix
vacuum-unique (T₂ , a0) (lam-fix , _ , _) | ()
vacuum-unique (T₂ , a1) (lam-fix , _ , _) with lambda-fixed-char T₂ a1 .proj₁ lam-fix
vacuum-unique (T₂ , a1) (lam-fix , _ , _) | ()
vacuum-unique (T₂ , a2) (lam-fix , _ , _) with lambda-fixed-char T₂ a2 .proj₁ lam-fix
vacuum-unique (T₂ , a2) (lam-fix , _ , _) | ()
vacuum-unique (T₂ , a3) (lam-fix , _ , _) with lambda-fixed-char T₂ a3 .proj₁ lam-fix
vacuum-unique (T₂ , a3) (lam-fix , _ , _) | ()

-- 推论: 若额外要求相位为 a0，则真空唯一
-- a0 ≠ a2 (前置, 供 vacuum-unique-at-phase-a0 使用)
a0≢a2 : a0 ≡ a2 → ⊥
a0≢a2 ()

vacuum-unique-at-phase-a0 : ∀ x → (lambda x ≡ x) × (mu x ≡ x) × (rho x ≡ x)
  → proj₂ x ≡ a0 → x ≡ duodec-e
vacuum-unique-at-phase-a0 x fixes phase≡a0
  with vacuum-unique x fixes
... | inj₁ x≡zero = x≡zero
... | inj₂ x≡T0a2 = ⊥-elim (a0≢a2 (trans (sym phase≡a0) (cong proj₂ x≡T0a2)))

-- §6f. 零冥族与投影的一致性
-- 证明: toDuodec 把零冥族的 zero 映到 d0
zero-oblivion-to-d0 : toDuodec duodec-e ≡ d0
zero-oblivion-to-d0 = refl

-- 证明: toDuodec 把联合周期映到 +1^12-id
zero-oblivion-joint-to-period :
  ∀ n → toDuodec (mixedOp^12 (fromDuodec n)) ≡ n
zero-oblivion-joint-to-period n = begin
  toDuodec (mixedOp^12 (fromDuodec n))  ≡⟨ cong toDuodec (mixedOp-12-cycle (fromDuodec n)) ⟩
  toDuodec (fromDuodec n)               ≡⟨ duodec-clock-roundtrip n ⟩
  n                                     ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §7. 结论更新:
--   十二进制 = 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩（混合时钟 DuodecPoint）。
--   mixedOp 是群（§3 交换群），经 CRT 同构于 Z/12 加法（§4: 双射往返 +
--   同态 mixed-to-+12 144/144），12 = char(GF(9)) × ord(α) = 3 × 4（§5）。
--   mulAlpha ≠ *12（§6a: 反例证明）。
--   零冥族形式化（§6b: ZeroOblivion record）。
--   联合周期 mixedOp^12 = id（§6c: 待完整证明）。
--   抽象群同构于 Z/12，但语义是加乘联合周期；模 12 环乘法不参与。
--------------------------------------------------------------------------------
-- 0 postulate (除 §6c 联合周期待证明外)。
