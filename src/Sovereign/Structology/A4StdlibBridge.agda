{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4StdlibBridge
-- 任务书 B0a 收官：A4Group 的 stdlib 桥（逐点形式 + 路径应用导出）
--
-- 数学背景：A4Group 的 perm-hom 是 cubical Path（perm (x⊗y) ≡ perm x ∘ₚ perm y），
--   B0a 探针定调的路线 (b)——逐点形式桥接——在此兑现：cubical Path 的
--   逐点应用（路径抽象在 z 上）平凡导出逐点等式，无需 funExt 反向、无需公设。
--
-- 复用：Structology/A4Group（A4/perm/⊗/perm-hom 全部已证核心模块）。
--
-- 0 postulate / 0 hole。
module Sovereign.Structology.A4StdlibBridge where

open import Data.Fin using (Fin; zero; suc)
open import Cubical.Foundations.Prelude using (_≡_; refl; cong)
open import Sovereign.Structology.A4Group
  using (A4; perm; _⊗_; perm-hom)

--------------------------------------------------------------------------------
-- §1. 逐点同态（路径抽象在 RHS——cubical 标准习惯）
--------------------------------------------------------------------------------

perm-hom-pointwise : ∀ (x y : A4) (z : Fin 4) →
  perm (x ⊗ y) z ≡ perm x (perm y z)
perm-hom-pointwise x y z = λ i → perm-hom x y i z

--------------------------------------------------------------------------------
-- §2. 同态律的组合形式（别名，语义同 §1——桥接的对外稳定接口）
--------------------------------------------------------------------------------

perm-hom-pointwise' : ∀ (x y : A4) (z : Fin 4) →
  perm (x ⊗ y) z ≡ perm x (perm y z)
perm-hom-pointwise' x y z = perm-hom-pointwise x y z
