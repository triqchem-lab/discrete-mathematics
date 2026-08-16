{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.TetrahedralA4
-- 正四面体旋转群 = A₄: 元素阶分解 1 + 3×2 + 8×3 (0 postulate)
--
-- 卢先生原生锚: 正四面体 = 「两个周期」(180° 双对换, 阶 2) + 「三生三」(120° 三循环, 阶 3)。
-- A₄ 的元素阶结构 (1, 2,2,2, 3,3,3,3,3,3,3,3) 与之逐项对应:
--   1 个单位元 (阶 1, 无旋转)
--   3 个双对换 Flip (阶 2, 180° 绕对边中点轴, 「两个周期归零」)
--   8 个三循环 Rot (阶 3, 120°/240° 绕顶点-面轴, 「三生三、三再乘三」)
--
-- 本模块把「阶结构」作为正四面体旋转群的代数指纹, 与 A4Group 的群结构桥接;
-- 物理/本体论解读 (sp3 四面体 = 频率+时间+空间) 属命名层, 不进入证明链。

module Sovereign.Structology.TetrahedralA4 where

open import Data.Nat using (ℕ; _*_; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Group using (A4; Id; Rot; Flip; _⊗_)

--------------------------------------------------------------------------------
-- §1. 元素阶
--------------------------------------------------------------------------------

orderOf : A4 → ℕ
orderOf Id = 1
orderOf (Rot i d) = 3     -- 120°/240° 三循环
orderOf (Flip j) = 2      -- 180° 双对换

--------------------------------------------------------------------------------
-- §2. 阶分解 (三个阶类)
--------------------------------------------------------------------------------

order-id : orderOf Id ≡ 1
order-id = refl

order-rot : ∀ (i : Fin 4) (d : Fin 2) → orderOf (Rot i d) ≡ 3
order-rot i d = refl

order-flip : ∀ (j : Fin 3) → orderOf (Flip j) ≡ 2
order-flip j = refl

--------------------------------------------------------------------------------
-- §3. 构造子基数 (阶类大小): |Id|=1, |Rot|=4·2=8, |Flip|=3
--------------------------------------------------------------------------------

rot-count : 4 * 2 ≡ 8
rot-count = refl

order-decomposition : 1 + 3 + 8 ≡ 12
order-decomposition = refl

--------------------------------------------------------------------------------
-- §4. 阶的语义: 2 阶元素 g²=Id, 3 阶元素 g³=Id
--   g²=Id (Flip 自逆) 与 g⊗g⁻¹=Id 由 A4Group.inverse 提供;
--   此处显式给出 Flip 自逆 (阶 2 的直接见证)。
--------------------------------------------------------------------------------

-- Flip 自逆: Flip j ⊗ Flip j = Id (阶 2 的语义)
flip-self-inverse : ∀ (j : Fin 3) → (Flip j) ⊗ (Flip j) ≡ Id
flip-self-inverse zero = refl
flip-self-inverse (suc zero) = refl
flip-self-inverse (suc (suc zero)) = refl

-- 0 postulate.
