{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra.Presentation
-- 八要素统一类型类 —— 类型论展示群的标准接口（L3）
--
-- 正源: docs/duodecimal/11-type-theory-presentation.md §四「律算框架的群论公理」：
--   Group := 载体类型 (record)
--          + 生成元族 (data, 带代数来源标记)
--          + 关系族 (record 字段)
--          + 刚性作用 (Frobenius 从 GF9 诱导)
--          + 结构证明 (refl, 0 postulate)
--
-- 形状规范: docs/maps/八要素统一形状-2026-10-14.md §三（三段式）
-- 判据原文: docs/maps/M8-check-semantics.md:88「八要素齐备才有公理候选资格」
--
-- ═══════════════════════════════════════════════════════════════
-- 八要素对照（本文件即该形状的**类型类**实现）
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      record Presentation (A : Set) 的**类型参数** A（非字段）
--  ② 生成元    field `step`（运算/作用）
--  ③ 关系      field `assoc` / `identityˡ` / `identityʳ`
--  ④ 相位      field `phase` + `phase-order` + `phase-cycle`
--  ⑤ 时钟      field `clock` + `clock-cycle`
--  ⑥ 归零      field `unit` + `zeroˡ` / `zeroʳ`
--  ⑦ 刚性      field `rigidity`（⚠ 约定：**必须从 GF9 的 galoisConjugate 诱导**，
--              不得在本层另立来源 —— 正源 §二 2.4「Frobenius 定义在 GF9 上」）
--  ⑧ 核对      field `check`（refl 层；正源：不产生结构）
--
-- ⚠ 两条硬约束（正源裁决，非本文件新立）：
--   1. 刚性**不得**定义在生成元层，须从 GF9 诱导（§二 2.4）
--   2. 核对是 refl 自洽确认、**不产生结构**（2026-09-08）
--   3. 八要素**不扩充**（2026-09-27）；壁垒/保真度命题不入本 record
--
-- 与既有结构的关系（不替代，只统一）：
--   - `UniversalAlgebra.Group` 等是**经典代数层级**（半群→群→环→域），
--     不含相位/时钟/刚性；本类型类是**展示群专用**，二者不同物（勿混）。
--   - `GroupTheory.ZeroOblivion` / `DayanCore` / `DCCyclicStructure` 是**具体件**的
--     关系 record；本类型类提供跨件统一接口（实例化即可对接）。

module Sovereign.Algebra.UniversalAlgebra.Presentation where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)

--------------------------------------------------------------------------------
-- 迭代算子（相位/时钟的周期语句需要）
--------------------------------------------------------------------------------
iterate : {A : Set} → (A → A) → ℕ → A → A
iterate f zero    x = x
iterate f (suc n) x = f (iterate f n x)

--------------------------------------------------------------------------------
-- 八要素类型类
--------------------------------------------------------------------------------
record Presentation (A : Set) : Set₁ where
  field
    -- ② 生成元（联合运算）
    step : A → A → A
    -- ② 生成元元（"联合"沿它走钟；见 ⑤）
    g : A
    -- ⑥ 归零（单位元）
    unit : A
    -- ③ 关系（结合律 + 单位律）
    assoc     : ∀ x y z → step (step x y) z ≡ step x (step y z)
    zeroˡ     : ∀ x → step unit x ≡ x
    zeroʳ     : ∀ x → step x unit ≡ x
    -- ④ 相位（**某一分量**的旋转算子 + 阶 + 循环语句）
    --
    -- ⚠ 相位是**分量级**的：在 DC 里它是 ⟨α⟩ ⊂ GF(9)* 的 C₄ 旋转（周期 4）。
    phase       : A → A
    phase-order : ℕ
    phase-cycle : ∀ x → iterate phase phase-order x ≡ x
    -- ⑤ 时钟（**联合**运算沿 g 的周期 + 一圈回位语句）
    --
    -- ⚠ 关键区分（DuodecClock 红线）：「十二进制 = 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩
    --   —— **加乘联合**，非纯加法直积、非 C₁₂ 循环群、非 C₃×C₄ 直积」。
    --   故 clock 必须是**联合运算 step 沿生成元 g** 的周期（DC 里 = lcm(3,4) = 12），
    --   **不是** phase 的迭代（那等于把 12 降格为 4 的倍数，丢掉加法分量）。
    clock       : ℕ
    clock-cycle : ∀ x → iterate (λ y → step y g) clock x ≡ x
    -- ⑦ 刚性（约定：必须由 GF9.galoisConjugate 诱导）
    rigidity : A → A
    -- ⑧ 核对（refl 层，仅确认定义自洽；正源：不产生结构）
    check : ∀ x → step x unit ≡ x

open Presentation public

--------------------------------------------------------------------------------
-- 实例：DuodecPoint 上的八要素展示结构（DC = C₃ × C₄）
--
-- 素材全部取自既有件（DuodecClock / DuodecClockProperties），本实例只做**对接**，
-- 不新证任何东西 —— 这正是 L3 的目的：把散在具体件里的八要素接到统一接口上。
--------------------------------------------------------------------------------
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; verifyZero)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3;
   mixedOp; duodec-e; mulAlpha; mixedOp-assoc; mixedOp-12-cycle;
   mixedOp-identityˡ; mixedOp-identityʳ; mu; rho; mulAlpha; mulAlpha-assoc)
open import Sovereign.Algebra.GroupTheory.DuodecClockProperties using (alpha-order-4)

-- 相位算子：只作用相位分量（乘 α），损益分量不动
dc-phase : DuodecPoint → DuodecPoint
dc-phase (t , a) = (t , mulAlpha a1 a)

-- 相位四步回位（α⁴ = a0 ⟹ 乘 a1 四次 = 恒等）
-- AlphaPower 是 4 元素枚举、mulAlpha 为具体乘法表 ⇒ 逐例归一化即 refl
dc-phase-cycle : ∀ x → iterate dc-phase 4 x ≡ x
dc-phase-cycle (t , a0) = refl
dc-phase-cycle (t , a1) = refl
dc-phase-cycle (t , a2) = refl
dc-phase-cycle (t , a3) = refl

-- 时钟：**联合**运算沿生成元 g = (T₁,a1) 走钟 12 步回位
-- ⚠ 不是 phase 的迭代 —— 12 = lcm(3,4) 是「特征 3 加法」与「C₄ 旋转」的联合周期
-- DuodecPoint 是 12 元素枚举、mixedOp 为分量级具体运算 ⇒ 逐例归一化即 refl
dc-clock-cycle : ∀ x → iterate (λ y → mixedOp y (T₁ , a1)) 12 x ≡ x
dc-clock-cycle (T₀ , a0) = refl
dc-clock-cycle (T₀ , a1) = refl
dc-clock-cycle (T₀ , a2) = refl
dc-clock-cycle (T₀ , a3) = refl
dc-clock-cycle (T₁ , a0) = refl
dc-clock-cycle (T₁ , a1) = refl
dc-clock-cycle (T₁ , a2) = refl
dc-clock-cycle (T₁ , a3) = refl
dc-clock-cycle (T₂ , a0) = refl
dc-clock-cycle (T₂ , a1) = refl
dc-clock-cycle (T₂ , a2) = refl
dc-clock-cycle (T₂ , a3) = refl

dc-presentation : Presentation DuodecPoint
dc-presentation = record
  { step        = mixedOp
  ; g           = (T₁ , a1)   -- 联合生成元（特征 3 步进 × C₄ 旋转）
  ; unit        = duodec-e
  ; assoc       = mixedOp-assoc
  ; zeroˡ       = mixedOp-identityˡ
  ; zeroʳ       = mixedOp-identityʳ
  ; phase       = dc-phase    -- 分量级相位（⟨α⟩ 的 C₄ 旋转，周期 4）
  ; phase-order = 4
  ; phase-cycle = dc-phase-cycle
  ; clock       = 12          -- **联合**周期 lcm(3,4)，非相位的倍数
  ; clock-cycle = dc-clock-cycle
  ; rigidity    = mu          -- 约定：由 GF9.galoisConjugate 诱导 —— 恰好等于相位反射 μ
                              -- （2026-10-21 修正：原为 rho = lambda ∘ mu = 群反转 ✗
                              --   见 docs/duodecimal/39-frobenius-vs-group-inversion.md
                              --   σ 是域自同构 ⇒ 固定素域 GF(3) ⇒ 加法分量上 σ = id；
                              --   而 rho 把 t ↦ -t ⇒ rho 不是 Frobenius 的运输 ✗）
  ; check       = mixedOp-identityʳ
  }

--------------------------------------------------------------------------------
-- g3：Presentation 是通用模板还是 DC 特化？—— 结构与实例的双重回答
--
-- 【探结构】曾试图用「从 DayanCore 构造 Presentation」来定位二者差异，**失败且证据确凿**：
--   DayanCore 的字段是 δ/φ : carrier → carrier（**一元作用**）+ δ³/φ⁴/δφ-comm，
--   **没有** step(二元)/unit/assoc/zeroˡ/zeroʳ ⇒ 群式与生成元式**不可互转**。
--   （编译器证据：dayan-joint-order-12 对 DayanCore 是局部模块内定义，不可导出引用。）
--
-- 【形态对照】本库现存四种**并列**的展示结构形态，Presentation 只是其中一种：
--   ┌ Presentation      群式： step(二元) + unit + 群律 + phase + clock + rigidity
--   ├ DayanCore         生成元式：δ/φ(一元) + δ³/φ⁴/δφ-comm        ← 更贴正源
--   ├ DCCyclicStructure 关系式：assoc/comm/period
--   ├ ZeroOblivion      关系式：addZeroR/L + mulAlphaCycle + tritCycle + jointCycle
--   └ AbstractPresentation 极简：carrier + δ(一元) + δ³            （TwoViewPlain/Rewritten）
--
-- 【⚠ 自我反省】正源 11-type-theory-presentation.md §二 明确「**生成元用 data**（归纳类型）」、
--   §四 的 DC 展开写的是 g₃/g₄ **作用**——即**一元作用**形态（如 DayanCore 的 δ/φ）。
--   本 Presentation 却把生成元做成**二元 `step`**，偏离正源；
--   之所以照此设计，是为迁就既有件（DCGroup 的 mixedOp 是二元）。
--   ⇒ 若要与正源严格一致，应改为「一元 `gens : A → A` 族 + 由它生成的联合」。
--
-- 【实例数】完整实例目前**仅 dc-presentation 一个**；候选普查结果：
--   - TwoViewPlain / TwoViewRewritten 的 AbstractPresentation：仅 3 要素，缺 5 项 ⇒ 不可实例化
--   - DayanCore：形态不同，不可实例化（见上）
--   - A4（12 阶）：**红线排除** —— DuodecClock 明写「禁挂 A₄ ≅ Z/12 或 A₄ 是十二进制」，
--     A₄ = V₄⋊C₃ 非交换，与「加乘联合（交换）」不同物
--   - GF(3)/GF(9) 系：无「联合 + 刚性」齐备者
--
-- 【裁定】Presentation 目前是**群式 + GF9 刚性约束的 DC 族特化模板**，尚非通用模板。
--   要成为通用模板，需要（a）按正源改为一元生成元式，且（b）找到第二个
--   天然带 GF9 Galois 刚性的对象。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §DC 额外定理（2026-10-21）：**DC 特有，不写进通用模板** ✗
--
-- ⚠ 这些约束在当前 `Presentation` 模板下**不是普遍成立的** ✗：
--   模板没有任何字段连接 `phase` 与 `step` ⇒ 它们只能是 DC 的额外定理 ✓
--   （若将来把「分量直积」写进模板，它们才成为定理 —— 见 42 号文 §4.2）
--------------------------------------------------------------------------------

-- ★ G3 单边：`phase` 与 `step` 交换（144 对，靠 `mulAlpha-assoc`）
dc-phase-step-comm : ∀ (x y : DuodecPoint) →
  dc-phase (mixedOp x y) ≡ mixedOp (dc-phase x) y
dc-phase-step-comm (t , a) (u , b) =
  cong₂ _,_ refl (sym (mulAlpha-assoc a1 a b))

-- ★ N8：`phase` 与 `step g` 交换
dc-phase-g-comm : ∀ (x : DuodecPoint) →
  dc-phase (mixedOp (T₁ , a1) x) ≡ mixedOp (T₁ , a1) (dc-phase x)
dc-phase-g-comm (t , a) = refl

-- ★ N3b：`phase-order < clock`（4 < 12）
dc-clock-neq-phase : 4 < 12
dc-clock-neq-phase = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

--------------------------------------------------------------------------------
-- §四层归零（2026-10-21）：**两类，不是四个字段** ✓
--
-- 人类的精确回答（2026-10-21）：
--   · **周期归零**（⊕³ / α⁴ / mixedOp¹²）—— 由 `clock-cycle` 与分量群结构**导出** ✓
--   · **代数归零**（1² + i² = 0²）—— **独立约束** ✗，不是周期归零（不是群的阶）✗
--
-- ⚠ 两者都是 **DC 特有**（不写进通用模板 ✗）：
--   周期归零依赖 DC 的分量群结构；代数归零是 GF(9) 的代数恒等式。
--------------------------------------------------------------------------------

-- ① 周期归零：⊕³ = T₀（Trit 的阶 3）—— 分量群结构导出 ✓
dc-oblivion-trit : ∀ (x : Trit) → ((x ⊕ x) ⊕ x) ≡ T₀
dc-oblivion-trit T₀ = refl
dc-oblivion-trit T₁ = refl
dc-oblivion-trit T₂ = refl

-- ② 周期归零：α⁴ = a₀（AlphaPower 的阶 4）—— = phase-cycle 的单点形
dc-oblivion-phase : ∀ (x : DuodecPoint) → iterate dc-phase 4 x ≡ x
dc-oblivion-phase = dc-phase-cycle

-- ③ 周期归零：mixedOp¹² = id（联合周期 lcm(3,4)）—— = clock-cycle 的单点形
dc-oblivion-joint : ∀ (x : DuodecPoint) → iterate (λ y → mixedOp y (T₁ , a1)) 12 x ≡ x
dc-oblivion-joint = dc-clock-cycle

-- ④ ★ 代数归零：1² + i² = 0² —— **独立约束** ✗（不是周期归零）
--
-- 数学位置（人类的精确回答 §2.3）：
--   `1² + i² = 0²` 在 `DuodecPoint` 中对应 **加法分量上 `T₁ ⊕ T₂ = T₀`**
--   （虚实对消灭的投影）✓
--
-- ⚠ `DuodecPoint`（12 元）**不能单射**到 `GF9`（9 元）✗
--   ⇒ 不需要 `embed` ✗ —— 定理直接在 `Trit` 上表达 ✓
dc-oblivion-algebra : T₁ ⊕ T₂ ≡ T₀
dc-oblivion-algebra = verifyZero
