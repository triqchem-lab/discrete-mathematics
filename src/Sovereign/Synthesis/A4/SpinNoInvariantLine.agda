{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SpinNoInvariantLine
--
-- **Z[ω] 无挠**（`2·z ≡ 0 ⇒ z ≡ 0`）—— 消元所需的基础件（库内原先没有）
--
-- 背景：`SpinIrreducible` 证到"不变线 ⇒ ρ(g0) 与 ρ(g9) 在公共特征向量上交换"。
-- 把它落成矛盾要两步：
--   (a) 由交换得两条线性方程 ω²·y ≡ y ⊕ (−1)·x、(−ω)·x ⊕ (−1)·y ≡ (−1)·x；
--   (b) 消元得 2·x ≡ 0、2·y ≡ 0，再用**无挠性**得 x = y = 0。
-- 本文件先做 (b) 依赖的那件基础工作：Z[ω] 无挠。
--
-- 证明路线（绕开 ℤ 乘法的 sign/abs 表示）：
--   ① 先把 `2·z` 化成 `z ⊕ z`（分配律 + 单位律，只用 Z[ω] 环律）；
--   ② 再用 `addZω` 的**结构定义**取坐标：`addZω (mkZω a b) (mkZω a b) = mkZω (a+a) (b+b)`；
--   ③ ℤ 上 `m + m ≡ 0 ⇒ m ≡ 0`，按 m = pos 0 / pos (suc _) / negsuc _ 三案。
--
-- ⚠ 为什么不直接对 `mulZω twoZ z` 取坐标：ℤ 的 `_*_` 由 `sign ◃ (|_| * |_|)` 定义，
--   负数乘积（如 `(−1) * (−1)`）**不**按字面归约，闭项也不一定 refl。故这里先化成
--   `z ⊕ z`，再用结构加法；代价只多一步分配律。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SpinNoInvariantLine where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; zeroZω; oneZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using (mulZω-distribʳ; mulZω-identityˡ)

--------------------------------------------------------------------------------
-- Z[ω] 无挠：2·z ≡ 0 ⇒ z ≡ 0
--------------------------------------------------------------------------------

twoZ : Zω
twoZ = mkZω (+ 2) (+ 0)

-- | ℤ 上：m + m ≡ 0 ⇒ m ≡ 0（3 案）
dbl-zero-ℤ : ∀ (m : ℤ) → m + m ≡ (+ 0) → m ≡ (+ 0)
dbl-zero-ℤ (+ zero)    _ = refl
dbl-zero-ℤ (+ (suc n)) ()
dbl-zero-ℤ (-[1+ n ])  ()

-- | Z[ω] 上：z ⊕ z ≡ 0 ⇒ z ≡ 0（逐坐标；`addZω` 是结构定义）
self-zero : ∀ (z : Zω) → addZω z z ≡ zeroZω → z ≡ zeroZω
self-zero (mkZω a b) h =
  cong₂ mkZω (dbl-zero-ℤ a (cong Zω.a h)) (dbl-zero-ℤ b (cong Zω.b h))

-- | 2·z ≡ z ⊕ z（分配律 + 单位律；`twoZ` 与 `one ⊕ one` 定义相等）
twoZ-mul : ∀ (z : Zω) → mulZω twoZ z ≡ addZω z z
twoZ-mul z =
  trans (mulZω-distribʳ oneZω oneZω z)
        (cong₂ addZω (mulZω-identityˡ z) (mulZω-identityˡ z))

-- | 主引理：Z[ω] 无挠
two-zero : ∀ (z : Zω) → mulZω twoZ z ≡ zeroZω → z ≡ zeroZω
two-zero z h = self-zero z (trans (sym (twoZ-mul z)) h)
