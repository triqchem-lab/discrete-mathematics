{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.ReductionGapObservation — 归一化器行为的**反射级机器强制观察**
--
-- 为什么需要它（缺口形式化的第三层）：缺口涉及 Agda **自己的**归一化器，而 Agda 没有
-- 「定义相等」这一内部类型 ⇒ 无法写成内部命题。但可以在**反射层**把它变成编译期**机器强制**
-- 的事实：
--
--   · `expectNotConvertible t u` —— 编译期要求 `reduce t` 与 `u` **不可合一**（无规约进展）
--
-- 本模块**能编译通过**本身就是机读证据：抽象生成元（模块参数）上的 `δ₀ (δ₀ (δ₀ c₀))`
-- 与 `c₀` 不可合一（`abstract-no-progress`）。把它换成「可合一」判据，编译**必然**失败。
--
-- ⚠ **未解释的观察（不掩盖）**：同一个 `reduce`+`unify` 机制用在**具体** 3-循环
--   `step (step (step p0))` 上时**未通过**（宏报「没有把它算成目标」），而**转换检查**
--   （`refl`）在同一项上通过（见 GapProbe1 与本模块 `concrete-progress`）⇒
--   宏内的 `unify` 与 `refl` 的转换检查在本机内核上**行为不一致**，具体原因**未查明**。
--   因此正向对照改用 `refl` 表达；该不一致已作为观察记入台账（不当作已解释的事实）。
--
-- ⚠ **层级声明（不得当作内部定理）**：这是**反射级观察**；它证明的是「在本机这个 Agda 内核上
--   该项的 `reduce`+`unify` 结果」，不是一般元定理。缺口的一般形式仍只能作为**外部事实**登记
--   （见 `docs/techniques/presentation-reduction-gap/README.md`，以及同目录的
--    `Sovereign.Trust.PresentationGapBoundary` 三层说明）。
--
-- 依赖只用**原语** `Agda.Builtin.Reflection`（不引 stdlib 的 `Reflection`：后者会拖进
-- Text.Printf 等一大坨，编译从 1s 变 60s）。

module Sovereign.Trust.ReductionGapObservation where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Reflection using
  (Term; TC; unify; reduce; catchTC; bindTC; typeError; strErr; ErrorPart)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- `typeError` 要的是 **List ErrorPart**；原语里没有 `return`，故成功分支用 `unify t′ t′`
failWith : String → TC ⊤
failWith s = typeError (strErr s ∷ [])

--------------------------------------------------------------------------------
-- 两个编译期判据
--------------------------------------------------------------------------------

-- 期望：归约后与目标**不可合一**（归一化器没有把组合项算成目标）
--   ⚠ 已知漏洞：若 `reduce` 本身抛异常，`catchTC` 会把成功分支也走掉 ⇒ 本判据**可能假通过**。
--   独立的正向控制见 `concrete-progress`（refl）与 docs/ 的 GapProbe1。
macro
  expectNotConvertible : Term → Term → TC ⊤
  expectNotConvertible t u =
    bindTC (reduce t) λ t′ →
      catchTC (bindTC (unify t′ u) λ _ →
                 failWith "UNEXPECTED: 归一化器把它算成了目标（缺口不成立）")
              (unify t′ t′)

--------------------------------------------------------------------------------
-- 抽象形态：生成元是**模块参数**（展示群的抽象形态；无定义 ⇒ 无 δ-规则）
--------------------------------------------------------------------------------

module _ (Carrier₀ : Set) (δ₀ : Carrier₀ → Carrier₀) (c₀ : Carrier₀) where

  abstract-no-progress : ⊤
  abstract-no-progress = expectNotConvertible (δ₀ (δ₀ (δ₀ c₀))) c₀

--------------------------------------------------------------------------------
-- 具体形态：三点 3-循环（归一化器直接算）
--------------------------------------------------------------------------------

data Three : Set where
  p0 p1 p2 : Three

step : Three → Three
step p0 = p1
step p1 = p2
step p2 = p0

-- 正向对照：具体 3-循环的闭合实例由**转换检查**闭合（`refl` ⟺ 两侧可转换 ⟺ 归一化器算了它）
--   注：同一件事用反射宏（`reduce` + `unify`）去测时**未通过**（见文件头「未解释的观察」）
concrete-progress : step (step (step p0)) ≡ p0
concrete-progress = refl
