{-# OPTIONS --guardedness --rewriting #-}

-- | Sovereign.Trust.GuardedVsPresentation — 「展示群 vs 守卫类型论」的**机器判定版**
--
-- 问题（用户 2026-09-14）：依赖类型论展示群是否属于守卫类型论？
-- 本模块只给能实测的那部分，并**纠正一个前提**：
--
-- ① **本机 Agda 没有 `▷` 延迟模态**（实测事实，非文献转述）：
--      · `open import Agda.Builtin.Guardedness` → `[FileNotFound]`
--      · `open import Agda.Builtin.Later`        → `[FileNotFound]`
--      · `open import Agda.Builtin.Coinduction`  → **rc=0**（存在）
--    ⇒ `--guardedness` 启用的**不是**「守卫类型论（▷ + clock quantifier）」，而是
--    **余归纳（`∞`/`♯`/`♭`）与 record-codata 的守卫检查**。`▷` 与时钟量化属于
--    CloTT / MTT 一类研究语言，**不在 Agda 里** ⇒ 那边的前沿建议在本工具链**无法做实验**。
--
-- ② **本库对守卫模态的实际使用量 = 0**：`grep -rl '▷' src/Sovereign` 只命中 1 个模块，
--    而那是 `HoTT/Fibration.agda:131` 自定义的管道算子 `_▷_ : A → (A → B) → B`，**不是模态**。
--    492 个模块带 `--guardedness` 旗标只是全库统一（余归纳/库依赖需要），不是「用了守卫类型论」。
--
-- ③ **守卫余归纳给的是「定义展开」，不是「周期」**（本模块同文件同旗标下对照）：
--      · `def-unfold : head (repeat x) ≡ x` 用 **`refl`** 闭合 ⇒ 展开是**定义相等**；
--      · `clock-3 : clock x [ 3 ] ≡ x` 必须**引用群的定律**（`step-3-law`）⇒ **周期是证明**。
--    ⇒ 即使把时钟写成余归纳流，`混合时钟走一圈` 这类**有限展示关系**仍不会自动成立：
--      守卫类型论补的是「无限结构的产出性」，不是「有限展示的商」。

module Sovereign.Trust.GuardedVsPresentation where

open import Codata.Guarded.Stream using (Stream; head; tail; repeat; _[_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Trust.PresentationGapBoundary using (Three; step; step-3-law)

--------------------------------------------------------------------------------
-- ① 守卫余归纳：展开是**定义相等**（refl 即可）
--------------------------------------------------------------------------------

def-unfold : ∀ {A : Set} (x : A) → head (repeat x) ≡ x
def-unfold x = refl

--------------------------------------------------------------------------------
-- ② 同一个 `--guardedness` 开关下，有限展示关系**仍要证明**
--------------------------------------------------------------------------------

-- 群的定律：`step³ = id`（三点 3-循环）—— 来自展示群一侧的**证明项**
group-law-is-proof : ∀ x → step (step (step x)) ≡ x
group-law-is-proof = step-3-law

--------------------------------------------------------------------------------
-- ③ 把「时钟」写成守卫余归纳流：周期仍需证明
--------------------------------------------------------------------------------

-- 走钟：每步施加生成元（余归纳定义，由守卫检查器接受）
clock : Three → Stream Three
head (clock x) = x
tail (clock x) = clock (step x)

-- 走 3 步回到原处：**不是定义展开**，必须用群的定律
--   （`clock x [ 3 ]` 归约为 `step (step (step x))`，随后由 `step-3-law` 收口）
clock-3 : ∀ x → (clock x [ 3 ]) ≡ x
clock-3 x = step-3-law x

-- 0 postulate / 0 hole。
