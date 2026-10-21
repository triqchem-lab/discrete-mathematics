{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyDec
--
-- **证明无分量的可判定性原语** —— 路 (a3) 的第一级台阶
--
-- ## 为什么需要这一件
--
-- 台账 `PN.B4.pi2d-free-group-boundary` 记了一个**真边界**：
-- 「一般图上 `π₂ᵈ⁺` 的分类」在 `--without-K` 下**不可做** ——
-- 因为它要 `DecEq (ASTep)`，而这条链的最后一环 `edge x y` 常是
-- **带相等证明分量的 `Σ`**，比较证明需 `uip`（`--cubical` ⇒ `--without-K` ⇒ 不可用）。
--
-- **出路**：把「判定」放在**无证明分量**的层上。
-- 本模块给这个层的第一级台阶：
--
-- | 原语 | 类型 | 说明 |
-- |---|---|---|
-- | `DecEq-T6Vec` | `(u v : T6Vec n) → Dec (u ≡ v)` | `Vec (Fin 3) n` 的可判定相等（`Fin 3` 可判定 + `Vec` 逐位比较）|
-- | `decAt` | `(j : Fin n) (x y : T6Vec n) → Dec (y ≡ updAt j x)` | ★ **判定「沿方向 `+e_j` 是否有边 `x → y`」** |
-- | `decAt2` | 同上，但方向是 `−e_j`（即 `updAt j (updAt j ·)`）| |
--
-- **关键**：这些都是**判定「陈述」**（`y ≡ updAt j x`），
-- 而**不是**判定「`T6SymEdge` 的两个**元素**是否相等」——
-- 后者才需要比较证明分量 ✗。前者的结果类型是 `Dec (y ≡ updAt j x)`，
-- 其中 `y`、`updAt j x` 都是 `Vec (Fin 3) n`（**无证明分量**）✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 全部复用 stdlib（`Data.Vec.Properties.≡-dec` + `Fin._≟_`）

module Sovereign.Synthesis.Homotopy.T6CayleyDec where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (Vec)
open import Data.Vec.Properties using (≡-dec)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)

--------------------------------------------------------------------------------
-- §1. `T6Vec n = Vec (Fin 3) n` 的可判定相等
--------------------------------------------------------------------------------

DecEq-T6Vec : ∀ {n : ℕ} (u v : T6Vec n) → Dec (u ≡ v)
DecEq-T6Vec = ≡-dec (Fin._≟_)

--------------------------------------------------------------------------------
-- §2. ★ 方向判定原语：沿 `+e_j` / `−e_j` 是否有边
--
-- 这两个是**归约**真正需要的：判断「第 j 个坐标推进后是不是这个顶点」。
-- 注意它们判定的是**语句**，不涉及任何证明分量 ✓
--------------------------------------------------------------------------------

decAt : ∀ {n : ℕ} (j : Fin n) (x y : T6Vec n) → Dec (y ≡ updAt j x)
decAt j x y = DecEq-T6Vec y (updAt j x)

decAt2 : ∀ {n : ℕ} (j : Fin n) (x y : T6Vec n) → Dec (y ≡ updAt j (updAt j x))
decAt2 j x y = DecEq-T6Vec y (updAt j (updAt j x))

--------------------------------------------------------------------------------
-- §3. ⬜ 下一级台阶（未做，判据明确）
--
-- 要用上面两个原语做**归约**，还差：
--
-- ① **邻居表**：`neighbours : T6Vec n → List (T6Vec n)`（显式枚举 `n` 坐标 × `±` 两向）
-- ② **对应定理（两向）**：
--      `T6SymEdge x y → y ∈ neighbours x`
--      `y ∈ neighbours x → T6SymEdge x y`
--    ← 第二步需要「从成员关系找回 `j`」，即 `List` 的索引搜索（stdlib 的
--      `Data.List.Membership` 或自写 `find`）。
-- ③ 在**无证明分量**的 `List (T6Vec n)` 上做 `reduce`（`&&`-链 + `fuel`）。
--
-- ⇒ 这三步都在 `--without-K` 下**可做**（因为 `Vec (Fin 3) n` 相等可判定），
--   而「一般图」的版本**不可做** —— 这就是台账记的那个真边界。
--------------------------------------------------------------------------------
