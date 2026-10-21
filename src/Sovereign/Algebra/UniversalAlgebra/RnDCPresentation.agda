{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra.RnDCPresentation
--
-- **`Vec DuodecPoint (3^n)` 的八要素 `Presentation` 实例**（修正 `RnPresentation` 的红线违规）。
--
-- ## 为什么改载体
--
-- `RnPresentation` 用 `Vec GF9 (3^n)` ✗ —— 其 `clock = 4 = phase-order` ✗，
-- 踩了 `Presentation.agda:79` 的红线：
--   「时钟必须是**联合运算** `step` 沿生成元 `g` 的周期，**不是** `phase` 的迭代」
--
-- 根因：`GF9 = Trit × Trit`（9 元）上**不存在**联合运算 ✗（`GF9* ≅ C₈`，不是 C₄）
-- 修正：载体改为 `DuodecPoint = Trit × AlphaPower`（12 元），在它上面
--       `mixedOp`（加法 ⊕ 相位乘）是现成的联合运算 ✓ ⇒ `clock = 12 = lcm(3,4)` ✓
--
-- ## 八要素
--
--   ① 载体      `Vec DuodecPoint (3^n)`
--   ② 生成元    `step = zipWith mixedOp`（逐点联合），`g = replicate (T₁ , a1)`
--   ③ 关系      `assoc` = `zipWith-assoc mixedOp-assoc`（现成 ✓）、`zeroˡ/ʳ`
--   ④ 相位      `map phaseDC`（C₄，`phaseDC (t , a) = (t , mulAlpha a a1)`）
--   ⑤ 时钟      **`clock = 12`**（联合周期 `lcm(3,4)` ✓ —— 不是 phase 的迭代 ✓）
--   ⑥ 归零      `unit = replicate duodec-e`
--   ⑦ 刚性      `map sigmaDC`（由 `GF9.galoisConjugate` 诱导 ✓）
--   ⑧ 核对      `check`（复用 `zeroʳ`）
--
-- ## 核心原则
--   · **零重复**：全部法则复用 `mixedOp-*` 与 `Data.Vec.Properties` ✓
--   · **不踩红线**：`clock = 12 ≠ phase-order = 4` ✓
--   · **无 funext**：载体是 `Vec`（结构相等）✓

module Sovereign.Algebra.UniversalAlgebra.RnDCPresentation where

open import Data.Nat using (ℕ; _^_; _+_; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_; replicate; zipWith; map)
open import Data.Vec.Properties using (zipWith-assoc; zipWith-identityˡ; zipWith-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; ⊕-comm)
open import Sovereign.Algebra.UniversalAlgebra.Presentation using (Presentation; iterate)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  ( DuodecPoint; AlphaPower; mixedOp; mixedOp-assoc
  ; mixedOp-identityˡ; mixedOp-identityʳ; mixedOp-12-cycle
  ; duodec-e; a0; a1; a2; a3; mulAlpha; mulAlpha-comm )
open import Sovereign.Algebra.GroupTheory.DCGroup using (sigmaDC)

--------------------------------------------------------------------------------
-- §1. 载体与运算
--------------------------------------------------------------------------------

RD : ℕ → Set
RD n = Vec DuodecPoint (3 ^ n)

stepD : (n : ℕ) → RD n → RD n → RD n
stepD n = zipWith mixedOp

unitD : (n : ℕ) → RD n
unitD n = replicate (3 ^ n) duodec-e

gD : (n : ℕ) → RD n
gD n = replicate (3 ^ n) (T₁ , a1)

-- 相位：只动相位分量
phaseD : DuodecPoint → DuodecPoint
phaseD (t , a) = (t , mulAlpha a a1)

phaseVec : (n : ℕ) → RD n → RD n
phaseVec n = map phaseD

rigD : (n : ℕ) → RD n → RD n
rigD n = map sigmaDC

--------------------------------------------------------------------------------
-- §2. 相位周期 4（`AlphaPower` 的 4 个构造子）
--------------------------------------------------------------------------------

α-four : ∀ (a : AlphaPower) →
  mulAlpha (mulAlpha (mulAlpha (mulAlpha a a1) a1) a1) a1 ≡ a
α-four a0 = refl
α-four a1 = refl
α-four a2 = refl
α-four a3 = refl

phaseD-4 : ∀ (p : DuodecPoint) → iterate phaseD 4 p ≡ p
phaseD-4 (t , a) = cong (t ,_) (α-four a)

phaseVec-cycle : ∀ {n} (xs : Vec DuodecPoint n) → iterate (map phaseD) 4 xs ≡ xs
phaseVec-cycle []       = refl
phaseVec-cycle (x ∷ xs) = cong₂ _∷_ (phaseD-4 x) (phaseVec-cycle xs)

--------------------------------------------------------------------------------
-- §3. 时钟 12（联合周期 —— 不踩红线）
--------------------------------------------------------------------------------

-- `mixedOp` 交换
mixedOp-comm : ∀ p q → mixedOp p q ≡ mixedOp q p
mixedOp-comm (x , a) (y , b) = cong₂ _,_ (⊕-comm x y) (mulAlpha-comm a b)

-- 左乘迭代
iterL : ℕ → DuodecPoint → DuodecPoint
iterL zero    x = x
iterL (suc n) x = mixedOp (T₁ , a1) (iterL n x)

-- 右乘 ≡ 左乘
right-eq-left : ∀ n p → iterate (λ y → mixedOp y (T₁ , a1)) n p ≡ iterL n p
right-eq-left zero    p = refl
right-eq-left (suc n) p =
  trans (cong (λ z → mixedOp z (T₁ , a1)) (right-eq-left n p))
        (mixedOp-comm (iterL n p) (T₁ , a1))

-- 单点：右乘 12 步回位
mixedOp-left-12 : ∀ p → iterate (λ y → mixedOp y (T₁ , a1)) 12 p ≡ p
mixedOp-left-12 p = trans (right-eq-left 12 p) (mixedOp-12-cycle p)

-- 逐点提升
clockVec-cycle : ∀ {n} (xs : Vec DuodecPoint n) →
  iterate (λ y → zipWith mixedOp y (replicate n (T₁ , a1))) 12 xs ≡ xs
clockVec-cycle []       = refl
clockVec-cycle (x ∷ xs) = cong₂ _∷_ (mixedOp-left-12 x) (clockVec-cycle xs)

--------------------------------------------------------------------------------
-- §4. ★★★ 八要素实例（clock = 12，不踩红线）
--------------------------------------------------------------------------------

RnDCPresentation : (n : ℕ) → Presentation (RD n)
RnDCPresentation n = record
  { step        = stepD n
  ; g           = gD n
  ; unit        = unitD n
  ; assoc       = zipWith-assoc {n = 3 ^ n} mixedOp-assoc
  ; zeroˡ       = zipWith-identityˡ {n = 3 ^ n} mixedOp-identityˡ
  ; zeroʳ       = zipWith-identityʳ {n = 3 ^ n} mixedOp-identityʳ
  ; phase       = phaseVec n
  ; phase-order = 4
  ; phase-cycle = phaseVec-cycle
  ; clock       = 12
  ; clock-cycle = clockVec-cycle
  ; rigidity    = rigD n
  ; check       = zipWith-identityʳ {n = 3 ^ n} mixedOp-identityʳ
  }
