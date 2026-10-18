{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Algebra.Jacobian.HenselLiftMinimal
--
-- 数学背景：
--  任务书第三层·3.2 延伸：Hensel 提升存在性实例（x² ≡ 1，mod 3 → mod 9）
--
--  数学背景：Hensel 引理——f(a) ≡ 0 (mod p) 且 f'(a) ≢ 0 (mod p) 时，
--    根 a 唯一提升为 mod pᵏ 的根。
--    **2026-10-19 升级**：本模块原只有 f(x) = x²、a ∈ {1,2} 的 **mod 3 → mod 9 实例**；
--    现已补上**一般 k 的存在性定理**（见 §4）——对任意 k，`3^k ∸ 1` 是 x² ≡ 1 (mod 3^k)
--    的根（平凡根 1 亦对任意 k 成立）。一般**唯一性**仍留 roadmap。
--
--    mod 3 的根：x ≡ 1, 2（1²-1 = 0, 2²-1 = 3，均被 3 整除）
--    mod 9 的提升：x = 1（1-1 = 0）与 x = 8（64-1 = 63 = 7·9）
--    两个根都从 mod 3 成功提升到 mod 9——存在性显式见证。
--
--  ⚠ 诚实边界：
--    1. 只证**存在性**（提升见证）；唯一性（f'(a) ≢ 0 mod p 的作用）
--       需非整除否证（¬(9 ∣ 15) 类），cubical 下 ℕ 整除否证需要
--       良基归纳或 stdlib 辅助引理，roadmap。
--    2. f'(a) 条件在本实例以非形式注释给出：f'(1) = 2 ≡ 2 mod 3 ≠ 0、
--       f'(2) = 4 ≡ 1 mod 3 ≠ 0——未形式化。
--    3. ℕ ∸ 截断减法：x² ≥ 1 对所有出现的 x 成立，∸ 即精确减法。
--
--  0 postulate / 0 hole。
--
-- 核心原则：
-- 1. x²≡1 的 Hensel 存在性：mod 3 根 1/2 → mod 9 提升 1/8 显式见证
-- 2. 只证存在性——唯一性（f′(a)≢0 作用）留 roadmap（诚实边界）
-- 3. divides 构造子形（整除见证）
--
-- 包含：root-1-mod-3 / root-2-mod-3 / lift-1-mod-9 / lift-8-mod-9 / root-8-mod-3 / quotient-of-63-by-9
module Sovereign.Algebra.Jacobian.HenselLiftMinimal where

open import Data.Nat using (ℕ; _*_; _∸_)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (_+_; _^_; _≤_; suc; zero; s≤s; z≤n)
open import Data.Nat.Properties
  using ( *-suc; *-comm; m≤m*n; *-monoʳ-≤; ≤-refl; ≤-reflexive; ≤-trans )
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

--------------------------------------------------------------------------------
-- §1. 根的 mod 3 层：x = 1 与 x = 2 都是 x² ≡ 1 (mod 3) 的根
--------------------------------------------------------------------------------

-- x = 1：1² - 1 = 0，被 3 整除（商 0）
-- ─── ③ 基础件层（桥引理/字面桥/序件——全部具名）───
root-1-mod-3 : 3 ∣ ((1 * 1) ∸ 1)
root-1-mod-3 = divides 0 refl

-- x = 2：2² - 1 = 3，被 3 整除（商 1）
root-2-mod-3 : 3 ∣ ((2 * 2) ∸ 1)
root-2-mod-3 = divides 1 refl

--------------------------------------------------------------------------------
-- §2. Hensel 提升：两个根都提升为 mod 9 的根
--
-- 提升 x ≡ 1 (mod 3)：候选 x ∈ {1, 4, 7}——x = 1 成功（见 §3 的 4/7 非根
--   留 roadmap，此处给存在见证）。
-- 提升 x ≡ 2 (mod 3)：候选 x ∈ {2, 5, 8}——x = 8 成功。
--------------------------------------------------------------------------------

-- x = 1 的提升见证：1² - 1 = 0，被 9 整除
lift-1-mod-9 : 9 ∣ ((1 * 1) ∸ 1)
lift-1-mod-9 = divides 0 refl

-- x = 8 的提升见证：8² - 1 = 63 = 7·9，被 9 整除
lift-8-mod-9 : 9 ∣ ((8 * 8) ∸ 1)
lift-8-mod-9 = divides 7 refl

-- x = 8 在 mod 3 层仍是根（提升不破坏下层整除性）
root-8-mod-3 : 3 ∣ ((8 * 8) ∸ 1)
root-8-mod-3 = divides 21 refl

--------------------------------------------------------------------------------
-- §3. 提升后的商记录（63 = 7·9 的显式商）
--
-- 63 的 9-补结构：63 ∸ 63 = 0，63 ≡ 7·9 (mod 良基)——refl 直接闭合。
--------------------------------------------------------------------------------

quotient-of-63-by-9 : 63 ≡ 7 * 9
quotient-of-63-by-9 = refl

--------------------------------------------------------------------------------
-- §4. 一般 k 的 Hensel 提升**存在性**（x² ≡ 1，mod 3^k）—— 2026-10-19 补
--
-- 陈述：对**任意** k，`3^k ∸ 1` 是 x² ≡ 1 (mod 3^k) 的根（平凡根 1 亦对任意 k 成立）。
--   为什么这是「一般存在性」：x² ≡ 1 在 mod 3 有两个根 1 与 2（= -1）；
--   提升 1 的是 **1**（平凡）；提升 2 的是 **3^k ∸ 1**（因 3^k ∸ 1 ≡ -1 ≡ 2 mod 3）。
--
-- 核心恒等式：(m ∸ 1)² ∸ 1 = (m ∸ 2) · m   （m ≥ 2）
--
-- 证明路线的两条要点（踩过的坑，留给后来者）：
--   1. **stdlib 的 `_+_`/`_*_` 按第一个参数递归** ⇒ `p + 1`、`p * X` 对变量 p **卡住不归约**。
--      故一律写 `suc p` / `suc (suc p)`——这样 `∸` 与 `*` 才会归约。
--   2. `*-suc` 让 `∸ 1` 直接归约：`suc p * suc p ≡ suc p + suc p * p`，
--      而 `suc p + X` 定义上归约为 `suc (p + X)`，故 `(suc p + X) ∸ 1` **定义上**即 `p + X`
--      ⇒ `∸ 1` 这一步是 `refl`，不需要任何 ∸ 引理。
--
-- 对抗验证（具体点独立核算，Python 精确整数）：k = 0..9 逐一核对
--   `X = (3^k - 1)² - 1 = (3^k - 2)·3^k` 且 `3^k ∣ X`——全部通过。
--------------------------------------------------------------------------------

-- m ∸ 1 ≡ suc (m ∸ 2)      （m ≥ 2，模式匹配）
sub1-eq : ∀ m → 2 ≤ m → m ∸ 1 ≡ suc (m ∸ 2)
sub1-eq (suc (suc q)) (s≤s (s≤s _)) = refl

-- suc (suc (m ∸ 2)) ≡ m    （m ≥ 2，模式匹配）
suc2∸2 : ∀ m → 2 ≤ m → suc (suc (m ∸ 2)) ≡ m
suc2∸2 (suc (suc q)) (s≤s (s≤s _)) = refl

-- 核心恒等式：(suc p)² ∸ 1 ≡ suc (suc p) · p
sq-minus-one : ∀ p → (suc p * suc p) ∸ 1 ≡ suc (suc p) * p
sq-minus-one p = cong (_∸ 1) (*-suc (suc p) p)

-- 1 ≤ 3^j
1≤3^j : ∀ j → 1 ≤ 3 ^ j
1≤3^j zero    = s≤s z≤n
1≤3^j (suc j) =
  ≤-trans (1≤3^j j)
    (≤-trans (m≤m*n (3 ^ j) 3)                  -- 3^j ≤ 3^j * 3
             (≤-reflexive (*-comm (3 ^ j) 3)))  -- ≡ 3 * 3^j

-- 2 ≤ 3^suc k
pow3-≥2 : ∀ k → 2 ≤ 3 ^ suc k
pow3-≥2 k =
  ≤-trans (s≤s (s≤s z≤n))                       -- 2 ≤ 3
    (≤-trans ≤-refl                             -- 3 ≤ 3 * 1（3 * 1 归约为 3）
             (*-monoʳ-≤ 3 (1≤3^j k)))           -- 3 * 1 ≤ 3 * 3^k

-- ★ 一般 Hensel 提升存在性（非平凡根）：3^k ∸ 1 是 x² ≡ 1 (mod 3^k) 的根，商为 3^k ∸ 2
hensel-root-minus-one : ∀ k → 3 ^ k ∣ ((3 ^ k ∸ 1) * (3 ^ k ∸ 1)) ∸ 1
hensel-root-minus-one zero    = divides 0 refl
hensel-root-minus-one (suc j) = divides (m ∸ 2) (trans eq (*-comm m (m ∸ 2)))
  where
    m : ℕ
    m = 3 ^ suc j

    h2 : 2 ≤ m
    h2 = pow3-≥2 j

    eq : ((m ∸ 1) * (m ∸ 1)) ∸ 1 ≡ m * (m ∸ 2)
    eq = trans (cong (λ z → (z * z) ∸ 1) (sub1-eq m h2))
               (trans (sq-minus-one (m ∸ 2))
                      (cong (λ z → z * (m ∸ 2)) (suc2∸2 m h2)))

-- ★ 一般 Hensel 提升存在性（平凡根）：1 是 x² ≡ 1 (mod 3^k) 的根，对任意 k
hensel-root-one : ∀ k → 3 ^ k ∣ ((1 * 1) ∸ 1)
hensel-root-one k = divides 0 refl
