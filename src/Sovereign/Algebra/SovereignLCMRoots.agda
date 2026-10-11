{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.SovereignLCMRoots
-- 任务书第三层·3.2 SOVEREIGN_LCM 根全景——**结构层 CRT 分解**（oracle 层核对 + 结构声明）
--
-- 数学背景：SOVEREIGN_LCM = 3¹¹ × 2¹⁶ = 177147 × 65536 = 11609505792。
--   x² ≡ 1 (mod N) 的根由 CRT 分解确定：
--     mod 3¹¹ → 2 根 {1, 177146}（HenselMod177147 ✓）
--     mod 2¹⁶ → 4 根 {1, 32767, 32769, 65535}（HenselModPow2 ✓）
--     CRT 合成 → 2 × 4 = **8 根**。
--
--   ⚠ 工具链限制：r²−1 最大达 1.35×10²⁰（r ≈ 1.16×10¹⁰）——
--     Agda 一元 ℕ 展开需 10²⁰ 个构造子，不可行。
--     本模块给出 8 根的符号 CRT 配对声明 + 结构验证；
--     逐根正 witness（n∣m*n 形态）待二进制 ℕ 或 REWRITE 归约 roadmap。
--
-- 0 postulate / 0 hole。
-- 核心原则:
--   1. 结构层 CRT 分解：SOVEREIGN_LCM = 3¹¹×2¹⁶ 的 x²≡1 根 = 2×4 组合全景；
--   2. 各素幂根的逐条证明由 Hensel 模块承担（HenselMod177147/HenselModPow2）——本模块做结构声明与核对；
--   3. 零 postulate；oracle 层核对不代替证明（证明在 Hensel 系）。
--
-- 包含: SOVEREIGN_LCM · root₁..₈-is-root（8 根全景）

module Sovereign.Algebra.SovereignLCMRoots where

open import Data.Nat using (ℕ; _*_; _+_; _<_; _≤_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Divisibility using (_∣_; n∣m*n)
open import Data.Nat.Divisibility.Core using (divides)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. CRT 配对表（8 根 = 2 × 4 合成）
--
--   每个根 r 由 CRT 配对 (mod 177147, mod 65536) 唯一确定：
--     root₁ = (1,     1)     → r = 1
--     root₂ = (177146, 32769) → r = 2829746177
--     root₃ = (1,     65535)  → r = 2975006719
--     root₄ = (177146, 32767) → r = 5804752895
--     root₅ = (1,     32769)  → r = 5804752897
--     root₆ = (177146, 1)     → r = 8634499073
--     root₇ = (1,     32767)  → r = 8779759615
--     root₈ = (177146, 65535) → r = 11609505791
--
--   oracle 验证：全部 8 根满足 r² ≡ 1 (mod 11609505792) ✓
--------------------------------------------------------------------------------

SOVEREIGN_LCM : ℕ
SOVEREIGN_LCM = 177147 * 65536

-- CRT 配对编码
record CRTPair : Set where
  constructor crt
  field
    mod-p3 : ℕ    -- mod 3¹¹ = 177147 的余
    mod-p2 : ℕ    -- mod 2¹⁶ = 65536 的余

-- 8 个 CRT 配对（全部已 oracle 核对）
crt-pair₁ crt-pair₂ crt-pair₃ crt-pair₄ : CRTPair
crt-pair₁ = crt 1 1
crt-pair₂ = crt 177146 32769
crt-pair₃ = crt 1 65535
crt-pair₄ = crt 177146 32767

crt-pair₅ crt-pair₆ crt-pair₇ crt-pair₈ : CRTPair
crt-pair₅ = crt 1 32769
crt-pair₆ = crt 177146 1
crt-pair₇ = crt 1 32767
crt-pair₈ = crt 177146 65535

--------------------------------------------------------------------------------
-- §2. 8 根的数值（oracle 层核对值）
--
--   以下数值为 oracle 计算结果，满足 r² ≡ 1 (mod SOVEREIGN_LCM)。
--   逐根 Agda 正 witness（n∣m*n 形态）因 r²−1 > 10¹⁸ 超出一元 ℕ 可行范围——
--   需二进制 ℕ 或 REWRITE 归约（roadmap）。
--------------------------------------------------------------------------------

root₁ root₂ root₃ root₄ root₅ root₆ root₇ root₈ : ℕ
root₁ = 1
root₂ = 2829746177
root₃ = 2975006719
root₄ = 5804752895
root₅ = 5804752897
root₆ = 8634499073
root₇ = 8779759615
root₈ = 11609505791

-- 根集的确定性：CRT 双射保证 2×4 = 恰 8 根
-- （形式化需 CRT 双射定理 + coprimality 论证——roadmap）

--------------------------------------------------------------------------------
-- §3. 前置模块引用
--------------------------------------------------------------------------------

-- mod 3¹¹ 两根 {1, 177146}: HenselMod177147 ✓（proven）
-- mod 2¹⁶ 四根 {1, 32767, 32769, 65535}: HenselModPow2 ✓（proven）
-- CRT 合成双射: 需泛型 CRT 定理（roadmap）

-- ── G4 数值层：8 根整除定理（每根 r²−1 = q·SOVEREIGN_LCM，商见证闭式）──
root₁-is-root : SOVEREIGN_LCM ∣ (root₁ * root₁ ∸ 1)
root₁-is-root = divides 0 refl
root₂-is-root : SOVEREIGN_LCM ∣ (root₂ * root₂ ∸ 1)
root₂-is-root = divides 689733359 refl
root₃-is-root : SOVEREIGN_LCM ∣ (root₃ * root₃ ∸ 1)
root₃-is-root = divides 762363630 refl
root₄-is-root : SOVEREIGN_LCM ∣ (root₄ * root₄ ∸ 1)
root₄-is-root = divides 2902376447 refl
root₅-is-root : SOVEREIGN_LCM ∣ (root₅ * root₅ ∸ 1)
root₅-is-root = divides 2902376449 refl
root₆-is-root : SOVEREIGN_LCM ∣ (root₆ * root₆ ∸ 1)
root₆-is-root = divides 6421855984 refl
root₇-is-root : SOVEREIGN_LCM ∣ (root₇ * root₇ ∸ 1)
root₇-is-root = divides 6639746797 refl
root₈-is-root : SOVEREIGN_LCM ∣ (root₈ * root₈ ∸ 1)
root₈-is-root = divides 11609505790 refl
