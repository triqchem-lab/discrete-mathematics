{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.FrobFix
-- Frobenius 不动点 = E(F₃)（M6 · B2/B3）
--
-- 数学背景:
--   B1（FrobF9）证得 σ 封闭 + σ²=id + rhs σ-等变; 本件给不动点的**计数定理**:
--   · 嵌入判据（点级）: F₃-嵌入像 ⟺ 虚部 ≡ T₀（f9im）;
--   · **Fix(σ) = #E(F₃)**: fixcnt c ≡ pointsE c（18 条独立引理, oracle B0 18/18 ✓）;
--   · **轨道分解**: #E(F₉) = Fix + 2·pairs（σ²=id ⟹ 非不动点成 2-cycles;
--     18 条, pairs 常量由 oracle emit-frob 逐字冻结）。
--   组合不变量 (Fix, pairs) 与同构类（CurveIsoF3 8 类）逐类一致（oracle iso/frob 交叉）。
--
-- 诚实边界:
--   fixcnt 的 81 点全枚举 = 独立引理形态（nightly 坑#5 防患, 同 CurveIsoF3 决策）;
--   σ 的群论意义（End(E) 元素/Deuring ρ²=−3）需 E(F₉) 群律, 未排期（B5）。

module Sovereign.Application.Problems.RH.FrobFix where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.CountF9All
open import Sovereign.Application.Problems.RH.FrobF9

--------------------------------------------------------------------------------
-- §1. 嵌入判据与逐点定理（免分派）
--------------------------------------------------------------------------------

f9im : F9 → Trit
f9im (mkF9 a b) = b

isE3 : F9 → Bool
isE3 x = tritEq (f9im x) T₀

-- σP ≡ P ⟹ P 虚部 ≡ T₀（⟺ P 是 F₃-嵌入点; 记录场不等 ⇒ ≡ 空, () 通过）
conj-fix-im : ∀ (x : F9) → f9conj x ≡ x → f9im x ≡ T₀
conj-fix-im (mkF9 a T₀) p = refl
conj-fix-im (mkF9 a T₁) ()
conj-fix-im (mkF9 a T₂) ()

--------------------------------------------------------------------------------
-- §2. 计数层（81 点全枚举; 结构同 CountF9All 的 sum9at 范式）
--------------------------------------------------------------------------------

hitFix : CurveF3 → ℕ → ℕ → ℕ
hitFix c xi yi =
  b2n ((tritEq (f9im (f9at xi)) T₀)
       ∧ (tritEq (f9im (f9at yi)) T₀
          ∧ f9eq (f9mul (f9at yi) (f9at yi)) (rhs9 c (f9at xi))))

colFixat : CurveF3 → ℕ → ℕ → ℕ
colFixat c xi zero = hitFix c xi zero + zero
colFixat c xi (suc k) = hitFix c xi (suc k) + colFixat c xi k

colFix : CurveF3 → ℕ → ℕ
colFix c xi = colFixat c xi eight

sumFix : CurveF3 → ℕ → ℕ
sumFix c zero = colFix c zero + zero
sumFix c (suc k) = colFix c (suc k) + sumFix c k

-- + 1 = 无穷远点（σ-不动; B0 oracle 同款口径 —— 漏掉它则 Fix 与 #E 差 1, 实测）
fixcnt : CurveF3 → ℕ
fixcnt c = suc (sumFix c eight)

--------------------------------------------------------------------------------
-- §3. Fix(σ) = #E(F₃) 18 条 + 轨道分解 18 条（oracle emit-frob 逐字）
--------------------------------------------------------------------------------

pairs-c010 : ℕ
pairs-c010 = 6
pairs-c011 : ℕ
pairs-c011 = 6
pairs-c012 : ℕ
pairs-c012 = 6
pairs-c020 : ℕ
pairs-c020 = 6
pairs-c021 : ℕ
pairs-c021 = 0
pairs-c022 : ℕ
pairs-c022 = 3
pairs-c101 : ℕ
pairs-c101 = 3
pairs-c102 : ℕ
pairs-c102 = 6
pairs-c111 : ℕ
pairs-c111 = 3
pairs-c112 : ℕ
pairs-c112 = 6
pairs-c120 : ℕ
pairs-c120 = 3
pairs-c121 : ℕ
pairs-c121 = 6
pairs-c201 : ℕ
pairs-c201 = 5
pairs-c202 : ℕ
pairs-c202 = 5
pairs-c211 : ℕ
pairs-c211 = 5
pairs-c212 : ℕ
pairs-c212 = 5
pairs-c220 : ℕ
pairs-c220 = 5
pairs-c222 : ℕ
pairs-c222 = 5

split-c010 : pointsE9 c010 ≡ fixcnt c010 + 2 * pairs-c010
split-c010 = refl
split-c011 : pointsE9 c011 ≡ fixcnt c011 + 2 * pairs-c011
split-c011 = refl
split-c012 : pointsE9 c012 ≡ fixcnt c012 + 2 * pairs-c012
split-c012 = refl
split-c020 : pointsE9 c020 ≡ fixcnt c020 + 2 * pairs-c020
split-c020 = refl
split-c021 : pointsE9 c021 ≡ fixcnt c021 + 2 * pairs-c021
split-c021 = refl
split-c022 : pointsE9 c022 ≡ fixcnt c022 + 2 * pairs-c022
split-c022 = refl
split-c101 : pointsE9 c101 ≡ fixcnt c101 + 2 * pairs-c101
split-c101 = refl
split-c102 : pointsE9 c102 ≡ fixcnt c102 + 2 * pairs-c102
split-c102 = refl
split-c111 : pointsE9 c111 ≡ fixcnt c111 + 2 * pairs-c111
split-c111 = refl
split-c112 : pointsE9 c112 ≡ fixcnt c112 + 2 * pairs-c112
split-c112 = refl
split-c120 : pointsE9 c120 ≡ fixcnt c120 + 2 * pairs-c120
split-c120 = refl
split-c121 : pointsE9 c121 ≡ fixcnt c121 + 2 * pairs-c121
split-c121 = refl
split-c201 : pointsE9 c201 ≡ fixcnt c201 + 2 * pairs-c201
split-c201 = refl
split-c202 : pointsE9 c202 ≡ fixcnt c202 + 2 * pairs-c202
split-c202 = refl
split-c211 : pointsE9 c211 ≡ fixcnt c211 + 2 * pairs-c211
split-c211 = refl
split-c212 : pointsE9 c212 ≡ fixcnt c212 + 2 * pairs-c212
split-c212 = refl
split-c220 : pointsE9 c220 ≡ fixcnt c220 + 2 * pairs-c220
split-c220 = refl
split-c222 : pointsE9 c222 ≡ fixcnt c222 + 2 * pairs-c222
split-c222 = refl

fe-c010 : fixcnt c010 ≡ pointsE c010
fe-c010 = refl
fe-c011 : fixcnt c011 ≡ pointsE c011
fe-c011 = refl
fe-c012 : fixcnt c012 ≡ pointsE c012
fe-c012 = refl
fe-c020 : fixcnt c020 ≡ pointsE c020
fe-c020 = refl
fe-c021 : fixcnt c021 ≡ pointsE c021
fe-c021 = refl
fe-c022 : fixcnt c022 ≡ pointsE c022
fe-c022 = refl
fe-c101 : fixcnt c101 ≡ pointsE c101
fe-c101 = refl
fe-c102 : fixcnt c102 ≡ pointsE c102
fe-c102 = refl
fe-c111 : fixcnt c111 ≡ pointsE c111
fe-c111 = refl
fe-c112 : fixcnt c112 ≡ pointsE c112
fe-c112 = refl
fe-c120 : fixcnt c120 ≡ pointsE c120
fe-c120 = refl
fe-c121 : fixcnt c121 ≡ pointsE c121
fe-c121 = refl
fe-c201 : fixcnt c201 ≡ pointsE c201
fe-c201 = refl
fe-c202 : fixcnt c202 ≡ pointsE c202
fe-c202 = refl
fe-c211 : fixcnt c211 ≡ pointsE c211
fe-c211 = refl
fe-c212 : fixcnt c212 ≡ pointsE c212
fe-c212 = refl
fe-c220 : fixcnt c220 ≡ pointsE c220
fe-c220 = refl
fe-c222 : fixcnt c222 ≡ pointsE c222
fe-c222 = refl
