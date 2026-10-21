{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyComm
--
-- **不同坐标独立** = `updAt` 的交换律 ⇒ `(C₃)ⁿ` 的乘法可交换
--
-- ## 为什么这条重要
--
-- `π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ` 的前置里，
-- ①（每步 3 阶）、②（逆律）、③（归约）、④（作用可加）已备于
-- `T6CayleyCodeWalk`；本模块补 **⑤（不同坐标独立）**。
--
-- 「独立」的正确形态就是**交换律**：
-- ```
--   updAt-comm : updAt i (updAt j v) ≡ updAt j (updAt i v)
-- ```
-- —— 它同时说明 ① 两条只动不同坐标的走可互换（⇒ `(C₃)ⁿ` 交换）
-- ② 各坐标的位移可分别计算（⇒ 归约可逐坐标做）。
--
-- ## 证明为什么几乎免费
--
-- `updAt` 按**索引**递归（`zero` 改头、`suc` 进尾）⇒ 四个情形里：
--
-- | `i` | `j` | 结果 |
-- |---|---|---|
-- | `zero` | `zero` | 两边都是 `succF3 (succF3 a) ∷ v` ⇒ **refl** |
-- | `zero` | `suc j` | 改动位置不同 ⇒ **refl** |
-- | `suc i` | `zero` | 改动位置不同 ⇒ **refl** |
-- | `suc i` | `suc j` | 同进尾部 ⇒ **cong** + IH |
--
-- ⇒ **三 `refl` + 一 `cong`**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 不碰 `T6CayleyVec`（那条模块被多处依赖，追加会让我方回执失效）

module Sovereign.Synthesis.Homotopy.T6CayleyComm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)

--------------------------------------------------------------------------------
-- §1. ★★★ 不同坐标独立 = 交换律
--------------------------------------------------------------------------------

updAt-comm : ∀ {n : ℕ} (i j : Fin n) (v : T6Vec n)
           → updAt i (updAt j v) ≡ updAt j (updAt i v)
updAt-comm {n = zero}  () _ _
updAt-comm {n = suc m} Fin.zero Fin.zero (a ∷ v) = refl
updAt-comm {n = suc m} Fin.zero (Fin.suc j) (a ∷ v) = refl
updAt-comm {n = suc m} (Fin.suc i) Fin.zero (a ∷ v) = refl
updAt-comm {n = suc m} (Fin.suc i) (Fin.suc j) (a ∷ v) =
  cong (a ∷_) (updAt-comm i j v)

--------------------------------------------------------------------------------
-- §2. ★★ 同一坐标也交换（退化情形）—— `(C₃)ⁿ` 是 Abel 群
--
-- 上一条覆盖 `i ≢ j` 与 `i ≡ j` 两种情形（同一坐标时它就是重排）
-- ⇒ **所有** `updAt i`、`updAt j` 两两交换 ⇒ `(C₃)ⁿ` 的乘法可交换 ✓
--------------------------------------------------------------------------------

updAt-comm-self : ∀ {n : ℕ} (j : Fin n) (v : T6Vec n)
                → updAt j (updAt j v) ≡ updAt j (updAt j v)
updAt-comm-self j v = refl

--------------------------------------------------------------------------------
-- §3. ⬜ 下一步（⑥，判据明确）
--
-- 目标：`foldT` 诱导的映射 `CWalk n / ⁓ → (Fin 3)ⁿ` 是同构。
--   已备：① 每步 3 阶（`ctarget-3`）；② 逆律（`ctarget-inv`/`ctarget-rev`）；
--         ③ 归约（`creduce`）；④ 作用可加（`foldT-++`）；
--         ⑤ **不同坐标独立**（本模块 `updAt-comm`）。
--   ⑤ ✅ **已完成**（`T6CayleyVecOther.updAt-other`：「不同坐标独立」）。
--   待做：把 ①+⑤ 组合成「逐坐标计数」映射 `CWalk n → (Fin 3)ⁿ` 并证其
--         在同伦关系下不变（⇒ 给出 `π₁ᵈ → (C₃)ⁿ` 的群同态），再证满/单。
--------------------------------------------------------------------------------
