{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra.RnPresentation
--
-- ⚠⚠ **2026-10-21 审核撤回**：本模块**不是**合法的八要素实例 ✗
--
-- 违反 `Presentation.agda:79` 的 DC 红线：
--   「时钟必须是**联合运算 step 沿生成元 g** 的周期（DC 里 = lcm(3,4) = 12），
--    **不是** phase 的迭代（那等于把 12 降格为 4 的倍数，丢掉加法分量）」
--
-- 本实例的 `clock = 4 = phase-order` ✗ —— `clock` **就是** `phase` 的迭代 ✗
--
-- **根因**：`R_n = Vec GF9 (3^n)` 上**不存在**联合运算 ✗
--   · 八要素的联合运算 = 加法（C₃）⊕ 相位乘（C₄）
--   · 在 `DuodecPoint = Trit × AlphaPower`（12 元）上 = `mixedOp` ✓
--   · 在 `GF9 = Trit × Trit`（9 元）上**不存在** ✗（GF9* ≅ C₈，不是 C₄）
--   ⇒ `R_n` 不是 DC 展示群 ⇒ **不应**强套八要素 ✗
--
-- ⇒ **合法的八要素实例只有 `Presentation.agda:131` 的 `dc-presentation`** ✓
--
-- 本模块保留仅作「特征 3 + 刚性 + 自同构」的**部分**结构演示 ✓，
-- 但**clock 字段不合法** ✗ —— 请看 `dc-presentation`。

--
-- **T4 正确环 `R_n = Functions((Z/3)^n, GF9)` 的八要素 `Presentation` 实例**。
--
-- ## 数学背景
--
-- T4 的环是 GF(9)-值函数环 `R_n = Functions((Z/3)^n, GF9)`（`3^n` 维 GF(9)-向量空间）。
-- 八要素要求的是**特征 3 + 代数刚性 + 自同构**（2026-10-21 人类裁决），
-- 三者在本对象上全部成立：
--   · **特征 3**：`GF9` 是 char 3 的域 ✓
--   · **代数刚性**：`galoisConjugate`（`σ(x)=x³`）✓
--   · **自同构**：`Gal(GF9/GF3) ≅ C₂`，`σ` 是乘法自同构（`galoisConjugate-mul`）✓
--
-- ## 载体选择（关键）
--
-- ⚠ **不用函数类型** `Torus n → GF9` ✗ —— `Presentation.assoc` 要求**函数相等** ✗
--    ⇒ 必须 `funext` ✗ —— 本项目**无 funext** ✗
-- ⚠ **用 `Vec GF9 (3^n)`** ✓ —— `≡` 是**结构相等** ✓ ⇒ 无需 funext ✓
--    与 `Torus n → GF9` **同构**（均 `3^n` 个 GF9 值）⇒ 数学对象不变 ✓
--
-- ## 八要素对应
--
--   ① 载体      `Vec GF9 (3^n)`
--   ② 生成元    `step = zipWith _*gf9_`（逐点乘，特征 3），`g = replicate alpha`
--   ③ 关系      `assoc` / `zeroˡ` / `zeroʳ`（全部复用 stdlib + GF9 定律 ✓）
--   ④ 相位      `map (_*gf9 alpha)`（C₄，`alpha` 是 GF9 的本原元）
--   ⑤ 时钟      `clock = 4`（α⁴ = 1）
--   ⑥ 归零      `unit = replicate gf9-one`
--   ⑦ 刚性      `rigidity = map galoisConjugate`（Frobenius 自同构 ✓）
--   ⑧ 核对      `check`（复用 `zeroʳ`）
--
-- ## 核心原则
--   · **零重复**：乘法律全部复用 `Data.Vec.Properties` 与 `GF9` ✓
--   · **无 funext**：载体选 `Vec` 而非函数 ✓
--   · 刚性由 `galoisConjugate` 诱导（`Presentation.agda` 硬约束 ✓）

module Sovereign.Algebra.UniversalAlgebra.RnPresentation where

open import Data.Nat using (ℕ; _^_)
open import Data.Vec using (Vec; []; _∷_; replicate; zipWith; map)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Properties using (zipWith-assoc; zipWith-identityˡ; zipWith-identityʳ; map-∘)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Algebra.UniversalAlgebra.Presentation using (Presentation; iterate)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.FieldTower.GF9 using
  ( GF9; _*gf9_; gf9-one; alpha
  ; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ; galoisConjugate )

--------------------------------------------------------------------------------
-- §1. 载体与运算
--------------------------------------------------------------------------------

-- `R n`：`3^n` 个 GF9 值的向量（与 `Torus n → GF9` 同构）
R : ℕ → Set
R n = Vec GF9 (3 ^ n)

stepR : (n : ℕ) → R n → R n → R n
stepR n = zipWith _*gf9_

unitR : (n : ℕ) → R n
unitR n = replicate (3 ^ n) gf9-one

gR : (n : ℕ) → R n
gR n = replicate (3 ^ n) alpha

phaseR : (n : ℕ) → R n → R n
phaseR n = map (_*gf9 alpha)

rigR : (n : ℕ) → R n → R n
rigR n = map galoisConjugate

--------------------------------------------------------------------------------
-- §2. 相位周期：α⁴ = 1（GF9 的 9 个构造子，全部 refl）
--------------------------------------------------------------------------------

α-four : ∀ (a : GF9) → (((a *gf9 alpha) *gf9 alpha) *gf9 alpha) *gf9 alpha ≡ a
α-four (T₀ , T₀) = refl
α-four (T₀ , T₁) = refl
α-four (T₀ , T₂) = refl
α-four (T₁ , T₀) = refl
α-four (T₁ , T₁) = refl
α-four (T₁ , T₂) = refl
α-four (T₂ , T₀) = refl
α-four (T₂ , T₁) = refl
α-four (T₂ , T₂) = refl

-- 相位四步（直接归纳，避开 funext）
phase-cycle-ax : ∀ {n} (xs : Vec GF9 n) → iterate (map (_*gf9 alpha)) 4 xs ≡ xs
phase-cycle-ax []             = refl
phase-cycle-ax (x ∷ xs)       = cong₂ _∷_ (α-four x) (phase-cycle-ax xs)

-- 时钟四步（`zipWith` 右乘 `replicate alpha`，直接归纳）
clock-cycle-ax : ∀ {n} (xs : Vec GF9 n) →
  iterate (λ y → zipWith _*gf9_ y (replicate n alpha)) 4 xs ≡ xs
clock-cycle-ax []       = refl
clock-cycle-ax (x ∷ xs) = cong₂ _∷_ (α-four x) (clock-cycle-ax xs)

--------------------------------------------------------------------------------
-- §3. 实例
--------------------------------------------------------------------------------

RnPresentation : (n : ℕ) → Presentation (R n)
RnPresentation n = record
  { step        = stepR n
  ; g           = gR n
  ; unit        = unitR n
  ; assoc       = zipWith-assoc {n = 3 ^ n} *gf9-assoc
  ; zeroˡ       = zipWith-identityˡ {n = 3 ^ n} *gf9-identityˡ
  ; zeroʳ       = zipWith-identityʳ {n = 3 ^ n} *gf9-identityʳ
  ; phase       = phaseR n
  ; phase-order = 4
  ; phase-cycle = phase-cycle-ax
  ; clock       = 4
  ; clock-cycle = clock-cycle-ax
  ; rigidity    = rigR n
  ; check       = zipWith-identityʳ {n = 3 ^ n} *gf9-identityʳ
  }
