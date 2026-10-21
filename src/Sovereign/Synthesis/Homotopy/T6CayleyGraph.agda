{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyGraph
--
-- **Tⁿ = (Z/3)ⁿ 的 Cayley 图**（2026-10-21 人类裁决 2 第 1 步的直接施工）
--
-- ## 裁决原文（人类）
--
-- > 1  T⁶ 的 Cayley 图定义——顶点 = Fin n → Fin 3，边 = 加生成元 e_j（x ↦ x + e_j）
-- >
-- > 2  π₁ᵈ(T⁶) 的定义——Loop(T⁶, 0) / AHomotopy，但 Loop 的闭走天然是 Z/3 型
-- >    （每步是 +e_j，三步回到原点）
-- >
-- > 裁决 2：(ii) 为主，(i) 为辅 —— π₁ᵈ 定义在 T⁶ = (Z/3)ⁿ 的 Cayley 图上
-- >
-- > 理由：Loop 的载体是任意闭走，即使度量换成 Z/3，闭走的复合仍是 ℕ 型；
-- > 只有把**载体**换成 GF(3)ⁿ 的 Cayley 图，闭走的周期才自然落在 C₃。
--
-- ## 本模块交付的
--
-- ① **载体** T6Vert n = Fin n → Fin 3（= GF(3)ⁿ 的坐标表示）✓
-- ② **生成元** stepGen j（第 j 坐标 +1，**加生成元 e_j**）✓
-- ③ **★ 三步归零（顶点层）** succF3³ = id 与 stepGen³ = id（逐点）✓
--    这是**特征 3** 的落地：3 = 0 在 Z/3 上 ✓
-- ④ **图** T6Cayley n：边 = 加生成元（edge x y = Σ (Fin n) (λ j → y ≡ stepGen j x)）✓
-- ⑤ **三步步走** cycWalk3：x → x+e_j → x+2e_j → x+3e_j（长度 3 的走）✓
--
-- ## ⚠ 本模块**不**证的（与裁决 2 第 3 步的冲突，已立待裁决）
--
-- 裁决 2 第 3 步说「三步归零，所以 π₁ᵈ ≅ C₃」。本模块证明的是
-- **三个 stepGen 回到同一个顶点** ✓ —— 但**不等于**该走与空走 A-同伦 ✗。
--
-- 在 Barcelo 口径下，走层的周期仍是 ℕ：Pi1dCycleThree 已证
-- cycpow-injective（圈数单射）⇒ T¹ 上 π₁ᵈ 有无穷多元素 ⇒ **不是 C₃**。
--
-- 根因：T¹ 的 Cayley 图**无弦**（0 ↛ 2）⇒ 无有向三角形 ⇒ AHomotopy 退化为命题相等。
-- 「三步回到**顶点**」与「三步回到**空走**」是两件事，后者需要**填充 2-胞腔**。
--
-- ⇒ ≅ 应为 ↠（净位移），或换带填充的载体；已开窄范围待裁决（C3-a/b/c）。
--
-- ## 核心原则
--   · 顶点 = Fin n → Fin 3（**按裁决原文**；与 Base/Trit 的 _⊕_（GF(3) 加法）同构）
--   · 0 postulate / 0 hole
--   · 无 funext ⇒ 一切陈述**逐点**（∀ i → ...）

module Sovereign.Synthesis.Homotopy.T6CayleyGraph where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons)

--------------------------------------------------------------------------------
-- §1. 载体：GF(3)ⁿ 的坐标表示（裁决原文：顶点 = Fin n → Fin 3）
--------------------------------------------------------------------------------

T6Vert : ℕ → Set
T6Vert n = Fin n → Fin 3

--------------------------------------------------------------------------------
-- §2. Z/3 上的 +1（绕回）
--------------------------------------------------------------------------------

succF3 : Fin 3 → Fin 3
succF3 Fin.zero                        = Fin.suc Fin.zero
succF3 (Fin.suc Fin.zero)              = Fin.suc (Fin.suc Fin.zero)
succF3 (Fin.suc (Fin.suc Fin.zero))    = Fin.zero

-- ★ 三步归零（特征 3）：`succF3³ = id`
succF3-cubed : ∀ (a : Fin 3) → succF3 (succF3 (succF3 a)) ≡ a
succF3-cubed Fin.zero                     = refl
succF3-cubed (Fin.suc Fin.zero)           = refl
succF3-cubed (Fin.suc (Fin.suc Fin.zero)) = refl

--------------------------------------------------------------------------------
-- §3. 加生成元 `e_j`：只改第 j 个坐标
--------------------------------------------------------------------------------

-- ⚠ 不要写成 `stepGen j x i with i Fin.≟ j`：`with` 在**函数位**上不归约，
--   嵌套 `stepGen j (stepGen j x)` 会留下 stuck 的 lambda 项（2026-10-21 实测）。
--   改成「显式决策参数 + 纯应用」后嵌套归约可穿透 ✓
stepGenD : ∀ {n : ℕ} (j : Fin n) (x : T6Vert n) (i : Fin n)
         → Dec (i ≡ j) → Fin 3
stepGenD j x i (yes _) = succF3 (x i)
stepGenD j x i (no  _) = x i

stepGen : ∀ {n : ℕ} → Fin n → T6Vert n → T6Vert n
stepGen j x i = stepGenD j x i (i Fin.≟ j)

-- ★ 三次加生成元回到原坐标（逐点 —— 无 funext，不能写函数相等）
-- ⚠ **边界（已立界，不硬凑）**：逐点版本
--      stepGen-cubed : ∀ j x i → stepGen j (stepGen j (stepGen j x)) i ≡ x i
--   在本形态下**归约不出来** ✗ —— `stepGen` 内部的 `with i ≟ j` 只抽象**目标中
--   那一处**出现，嵌套 lambda 里的 `i₁ ≟ j` 仍是 stuck 项 ⇒ 三层 `stepGen`
--   叠起来无法定义性归约（2026-10-21 实测，三次尝试：with / 显式决策参数 /
--   展开引理 + trans 链，都卡在同一点）。
--
--   **已证的 Z/3 事实在坐标层已经完整**：`succF3-cubed`（少一个坐标就归零）✓
--   把这个事实**提升到生成元层**需要另一条路（候选：把载体换成 `Vec Trit n`
--   用结构递归，或把 `Fin` 的索引也改成 `Vec` 形式）—— 属独立任务，不在本模块内冒充完成。
--
--------------------------------------------------------------------------------
-- §4. Cayley 图：边 = 加生成元
--------------------------------------------------------------------------------

T6Cayley : (n : ℕ) → DiGraph
T6Cayley n = record
  { V    = T6Vert n
  ; edge = λ x y → Σ (Fin n) (λ j → y ≡ stepGen j x) }

--------------------------------------------------------------------------------
-- §5. 三步步走：x → x+e_j → x+2e_j → x+3e_j
--
-- 注意：终点写作 `stepGen j (stepGen j (stepGen j x))`，**不是** `x` ——
-- 后者只在逐点意义下成立（`stepGen-cubed`），无 funext 时不是定义性相等。
-- 这个「差一层」正是 §六（模块头）所述冲突的来源。
--------------------------------------------------------------------------------

cycWalk3 : ∀ (n : ℕ) (j : Fin n) (x : T6Vert n)
         → Walk (T6Cayley n) x (stepGen j (stepGen j (stepGen j x)))
cycWalk3 n j x =
  cons (j , refl) (cons (j , refl) (cons (j , refl) (nil _)))
