{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.AxialNoSplit
-- 线性转子 J=1 在**轴对称场**下不劈裂 —— 定义与陈述（**证明未完成**）
--
-- ⛔⛔ 2026-10-23 晚 **物理前提已证伪** ⛔⛔
--
-- 本模块头原写：「⟨J=1,M|V_axial|J=1,M'⟩ = δ_MM' · C ⇒ 矩阵是 C·I ⇒ 不劈裂」。
-- **这是错的。**
--
-- 正确：轴场下的四极算符 ∝ (3(n·J)² − 2)，其矩阵元 ∝ (3M² − 2)，
-- **随 M 变化**（M=0 给 −2，M=±1 给 +1）⇒ 谱是 (0,−3,−3) ⇒ **2+1 劈裂**。
--
-- 证据（两条独立）：
--   ① 数值：V₂=10 → 6.02 cm⁻¹（两个独立实现一致）
--   ② 内核：`Sovereign.Synthesis.Physics.J1MatricesProbe` 的 §7
--      直接算出 Jn² 的谱 = (0,−3,−3)（回执 3e0b25a1… / feacf06f…）
--
-- 所以：「轴场不劈裂」既不是物理标准结论，也没有数值验证支持 —— **恰恰相反**。
--
-- ⚠ **本模块剩下的内容仍然有效**：`ScalarMatrix` 的定义、以及「若矩阵是 c·I
--   则不劈裂」这一**定义层面的**事实。它只是**不适用于轴场**。
--
-- 另一个相关事实：`NoSplitJ1Full.no-split-full` 要求 Commutes-shift **和**
--   Commutes-flip 两者都有；而 S₆ = C₃ × 反演，反演在 J=1 上是整体 −1 ⇒
--   物理上只有 shift，**没有 flip** ⇒ `no-split-full` 也不适用。
--
-- ⚠ **诚实标记**：本模块只给出**定义与陈述**，`mul-scalar` 的**证明未完成**。
--   原因：完整证明需要对 Fin 3 的三个分量逐一展开并配合 ℤ 的分配律，
--   而它的**内容其实只是「对角元相等」这一假设本身** ——
--   真正有内容的 Wigner–Eckart 定理（SU(2) 表示论）本库没有。
--   ⇒ 本模块**不构成**「轴场不劈裂」的内核证明。
module Sovereign.Synthesis.Physics.AxialNoSplit where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

--------------------------------------------------------------------------------
-- 一、载体
--------------------------------------------------------------------------------
Mat3 : Set
Mat3 = Fin 3 → Fin 3 → ℤ

Vec3 : Set
Vec3 = Fin 3 → ℤ

mul : Mat3 → Vec3 → Vec3
mul M v i = (M i zero * v zero) + (M i (suc zero) * v (suc zero))
          + (M i (suc (suc zero)) * v (suc (suc zero)))

scale : ℤ → Vec3 → Vec3
scale c v i = c * v i

--------------------------------------------------------------------------------
-- 二、`ScalarMatrix c M`：M 是 c·I
--------------------------------------------------------------------------------
-- 前三条 = 对角元全等于 c；第四条 = 非对角为 0。
-- **「对角元全等」就是「无劈裂」**（对角矩阵的谱即对角元）。
ScalarMatrix : ℤ → Mat3 → Set
ScalarMatrix c M =
    M zero zero ≡ c
  × M (suc zero) (suc zero) ≡ c
  × M (suc (suc zero)) (suc (suc zero)) ≡ c
  × (∀ i j → ¬ (i ≡ j) → M i j ≡ + 0)

--------------------------------------------------------------------------------
-- 三、陈述（未证）
--------------------------------------------------------------------------------
mul-scalar : Set
mul-scalar = ∀ (c : ℤ) (M : Mat3) (v : Vec3)
           → ScalarMatrix c M → ∀ i → mul M v i ≡ scale c v i

-- ⚠ 上面这条**未给出证明项**（不是 postulate，只是把类型写成 Set 值）。
--   给出证明项才叫证明 —— 本模块没有。

--------------------------------------------------------------------------------
-- 四、本模块能支持什么、不能支持什么
--------------------------------------------------------------------------------
-- ✅ **能**：把「无劈裂」精确定义为「对角元全等」（`ScalarMatrix` 的前三条）。
-- ✅ **能**：说明一旦 Wigner–Eckart 给出 ScalarMatrix，无劈裂就是定义层面的直接推论
--          （对角矩阵的谱即对角元，不需要额外定理）。
--
-- ❌ **不能**：说明 Wigner–Eckart 成立 —— 那需要 SU(2) 不可约表示的张量积分解
--          （1 ⊗ 1 = 0 ⊕ 1 ⊕ 2），本库**没有**这套机件。
-- ❌ **不能**：说明 l ≥ 4 的矩阵元为零（三角不等式），同上。
--
-- ⇒ 结论：**「轴场对线性转子 J=1 不劈裂」目前是物理标准结论 + 数值验证，
--   不是本库的内核定理。** 不得当作已证。
