{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyVec
--
-- **`Tⁿ = (Z/3)ⁿ` 的 Cayley 图（向量载体版本）** —— 补上 `T6CayleyGraph` 的边界
--
-- ## 为什么另起一个模块
--
-- `T6CayleyGraph` 用 `Fin n → Fin 3`（函数载体，按裁决原文的字面写法）给出了载体/
-- 生成元/图/三步步走 ✓，但**生成元层的三步归零证不出来** ✗：
-- `stepGen` 内部的 `with i ≟ j` 只抽象目标中那一处出现，嵌套 lambda 里的
-- `i₁ ≟ j` 仍是 stuck 项 ⇒ `stepGen³` 无法定义性归约（已入 prover_limits）。
--
-- 本模块把载体换成 **`Vec (Fin 3) n`**：`upd` 按 **`j` 与向量双归纳**定义（不用 `with`），
-- 于是 `upd³ = id` 可以直接**结构递归**证出 ✓
--
-- ## 本模块交付的
--
-- ① `T6Vec n = Vec (Fin 3) n`（= `GF(3)ⁿ`，与 `T6CayleyGraph.T6Vert n` 同构）
-- ② `updAt j`：第 `j` 个坐标应用 `succF3`（`succF3` 复用 `T6CayleyGraph`）
-- ③ **★★ `updAt-cubed`：三步归零（生成元层）** —— 特征 3 的完整落地 ✓
-- ④ `T6CayleyVec n : DiGraph`（边 = 加生成元）
-- ⑤ **★★ `cycWalk3Vec`：长度 3 的「真闭走」** —— 用 `subst` 沿 `updAt-cubed`
--    把终点搬回起点，得到 `Walk G x x`（不是「差一层」的半闭合形态）✓
--
-- ## ⚠ 与裁决 2 第 3 步的关系（不变）
--
-- `cycWalk3Vec` 存在 ⇒ **三步回到顶点** ✓；但**不等于**它与空走 A-同伦 ✗。
-- `Pi1dCycleThree` 已证 `T¹` 上圈数单射 ⇒ `π₁ᵈ` 无穷 ⇒ 不是 `C₃`。
-- `≅` 应为 `↠`（净位移），或换带填充的载体 —— 已立待裁决（C3-a/b/c），本模块不选边。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `T6CayleyGraph` 的 `succF3` / `succF3-cubed`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleyVec where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (Vec; []; _∷_; head; tail)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons)
open import Sovereign.Synthesis.Homotopy.T6CayleyGraph
  using (succF3; succF3-cubed)

--------------------------------------------------------------------------------
-- §1. 向量载体
--------------------------------------------------------------------------------

T6Vec : ℕ → Set
T6Vec n = Vec (Fin 3) n

--------------------------------------------------------------------------------
-- §2. 加生成元（按 j 与向量双归纳，不用 with）
--------------------------------------------------------------------------------

updAt : ∀ {n : ℕ} → Fin n → T6Vec n → T6Vec n
updAt Fin.zero    (a ∷ v) = succF3 a ∷ v
updAt (Fin.suc j) (a ∷ v) = a ∷ updAt j v

--------------------------------------------------------------------------------
-- §3. ★★ 三步归零（生成元层）—— 特征 3 在 Tⁿ 上的完整落地
--------------------------------------------------------------------------------

updAt-cubed : ∀ {n : ℕ} (j : Fin n) (v : T6Vec n)
            → updAt j (updAt j (updAt j v)) ≡ v
updAt-cubed {n = zero}  () v
updAt-cubed {n = suc m} Fin.zero (a ∷ v) =
  cong (λ z → z ∷ v) (succF3-cubed a)
updAt-cubed {n = suc m} (Fin.suc j) (a ∷ v) =
  cong (a ∷_) (updAt-cubed j v)

--------------------------------------------------------------------------------
-- §4. Cayley 图：边 = 加生成元
--------------------------------------------------------------------------------

T6CayleyVec : (n : ℕ) → DiGraph
T6CayleyVec n = record
  { V    = T6Vec n
  ; edge = λ x y → Σ (Fin n) (λ j → y ≡ updAt j x) }

--------------------------------------------------------------------------------
-- §5. ★★ 长度 3 的**真闭走**（终点用 subst 搬回起点）
--------------------------------------------------------------------------------

-- 先在「三段生成元之后」的位置构造走
cycWalk3-open : ∀ (n : ℕ) (j : Fin n) (x : T6Vec n)
              → Walk (T6CayleyVec n) x (updAt j (updAt j (updAt j x)))
cycWalk3-open n j x =
  cons (j , refl) (cons (j , refl) (cons (j , refl) (nil _)))

-- ★ 再用 `updAt-cubed` 把终点搬回起点 ⇒ 真正的闭走 `Walk G x x` ✓
cycWalk3Vec : ∀ (n : ℕ) (j : Fin n) (x : T6Vec n)
            → Walk (T6CayleyVec n) x x
cycWalk3Vec n j x =
  subst (Walk (T6CayleyVec n) x) (updAt-cubed j x) (cycWalk3-open n j x)

--------------------------------------------------------------------------------
-- §6. `updAt` 没有不动点（一般 n 三角形成立性的基础砖）
--------------------------------------------------------------------------------

-- `succF3` 没有不动点（Fin 3 三 case；复用 §2 的 `succF3-cubed` 所在模块的同一事实）
succF3≢id : ∀ (a : Fin 3) → succF3 a ≡ a → ⊥
succF3≢id Fin.zero                     ()
succF3≢id (Fin.suc Fin.zero)           ()
succF3≢id (Fin.suc (Fin.suc Fin.zero)) ()

updAt-differs : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n) → updAt j x ≢ x
updAt-differs {n = zero}  () x
updAt-differs {n = suc m} Fin.zero (a ∷ v) e =
  succF3≢id a (cong head e)
updAt-differs {n = suc m} (Fin.suc j) (a ∷ v) e =
  updAt-differs j v (cong tail e)
