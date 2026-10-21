{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra.DCPresentation
--
-- **全库第一个 `Presentation` 实例**（八要素的具体落地）。
--
-- ## 数学背景
--
-- `DuodecPoint = Trit × AlphaPower`（12 元）承载 **DC 展示群**：
--   · 加法分量 `Trit`（GF(3) 加法，C₃）
--   · 相位分量 `AlphaPower`（⟨α⟩ ⊂ GF(9)*，C₄）
--   · 联合运算 `mixedOp`（**不是直积**：`clock = lcm(3,4) = 12` 是推论）
--
-- ## 八要素对应
--
--   ① 载体      `DuodecPoint`（类型参数）
--   ② 生成元    `step = mixedOp`，`g = (T₁ , a1)`（联合生成元，阶 12）
--   ③ 关系      `assoc` / `zeroˡ` / `zeroʳ`
--   ④ 相位      `phaseDC (t , a) = (t , a·α)`（C₄，阶 4）
--   ⑤ 时钟      `clock = 12`，`clock-cycle` 由 `mixedOp-12-cycle` 桥接
--   ⑥ 归零      `unit = duodec-e = (T₀ , a0)`
--   ⑦ 刚性      `rigidity = sigmaDC`（由 `GF9.galoisConjugate` 诱导 ✓）
--   ⑧ 核对      `check`（refl 层，不产生结构）
--
-- ## 核心原则
--   1. 相位不可约：取 ⟨α⟩（C₄），**不得**约化为 C₂
--   2. 时钟是联合的：12 = lcm(3,4) 来自 `mixedOp`
--   3. 刚性从 GF9 诱导（`sigmaDC (t,a) = (t , alphaInv a)`）
--   4. 核对不产生结构
--
-- ## 包含
--   §1 相位（`phaseDC` / `α-four` / `phaseDC-4`）
--   §2 时钟（`gDC` / `mixedOp-comm` / `iterL` / `right-eq-left` / `clock-bridge`）
--   §3 实例（`DCPresentation`）

module Sovereign.Algebra.UniversalAlgebra.DCPresentation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; _⊕_; ⊕-comm)
open import Sovereign.Algebra.UniversalAlgebra.Presentation using (Presentation; iterate)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  ( DuodecPoint; AlphaPower; mixedOp; mixedOp-assoc
  ; mixedOp-identityˡ; mixedOp-identityʳ; mixedOp-12-cycle
  ; duodec-e; a0; a1; a2; a3; mulAlpha; mulAlpha-assoc
  ; mulAlpha-identityʳ; mulAlpha-comm; mulAlpha-4-a1 )
open import Sovereign.Algebra.GroupTheory.DCGroup using (sigmaDC)

--------------------------------------------------------------------------------
-- §1. 相位：C₄ 旋转（只动相位分量）
--------------------------------------------------------------------------------

phaseDC : DuodecPoint → DuodecPoint
phaseDC (t , a) = (t , mulAlpha a a1)

-- `α⁴ = 1`：`((((a·α)·α)·α)·α) ≡ a`（4 个构造子 ⇒ 4 个 refl ✓）
α-four : ∀ (a : AlphaPower) →
  mulAlpha (mulAlpha (mulAlpha (mulAlpha a a1) a1) a1) a1 ≡ a
α-four a0 = refl
α-four a1 = refl
α-four a2 = refl
α-four a3 = refl

-- ★ 相位顺序 4
phaseDC-4 : ∀ (x : DuodecPoint) → iterate phaseDC 4 x ≡ x
phaseDC-4 (t , a) = cong (t ,_) (α-four a)

--------------------------------------------------------------------------------
-- §2. 时钟：`iterate (λ y → mixedOp y g) 12` ≡ `mixedOp^12`
--------------------------------------------------------------------------------

-- 联合生成元（阶 12）
gDC : DuodecPoint
gDC = (T₁ , a1)

-- `mixedOp` 交换
mixedOp-comm : ∀ p q → mixedOp p q ≡ mixedOp q p
mixedOp-comm (x , a) (y , b) = cong₂ _,_ (⊕-comm x y) (mulAlpha-comm a b)

-- 左乘迭代（与 `mixedOp^12` 的定义形一致：12 层左乘 g）
iterL : ℕ → DuodecPoint → DuodecPoint
iterL zero    x = x
iterL (suc n) x = mixedOp gDC (iterL n x)

-- ★ 右乘 ≡ 左乘（`mixedOp` 交换）
--   证明：归纳。右乘一步 ↔ 左乘一步，由 `mixedOp-comm` 换序。
right-eq-left : ∀ n x → iterate (λ y → mixedOp y gDC) n x ≡ iterL n x
right-eq-left zero    x = refl
right-eq-left (suc n) x =
  trans (cong (λ z → mixedOp z gDC) (right-eq-left n x))
        (mixedOp-comm (iterL n x) gDC)

-- ★★ 时钟周期 12（`iterL 12` 与 `mixedOp^12` 定义等价 ✓ 探针验证）
clock-bridge : ∀ x → iterate (λ y → mixedOp y gDC) 12 x ≡ x
clock-bridge x = trans (right-eq-left 12 x) (mixedOp-12-cycle x)

--------------------------------------------------------------------------------
-- §3. ★★★ 实例：全库第一个 `Presentation`
--------------------------------------------------------------------------------

DCPresentation : Presentation DuodecPoint
DCPresentation = record
  { step        = mixedOp
  ; g           = gDC
  ; unit        = duodec-e
  ; assoc       = mixedOp-assoc
  ; zeroˡ       = mixedOp-identityˡ
  ; zeroʳ       = mixedOp-identityʳ
  ; phase       = phaseDC
  ; phase-order = 4
  ; phase-cycle = phaseDC-4
  ; clock       = 12
  ; clock-cycle = clock-bridge
  ; rigidity    = sigmaDC
  ; check       = mixedOp-identityʳ
  }
