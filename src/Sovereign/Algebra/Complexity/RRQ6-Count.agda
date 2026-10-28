{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.RRQ6-Count
-- GF(3) monic 六次不可约精确计数 = 116（PvsNP 路线图批三 RRQ6 计数件）
--
-- 密度证据链四点（渐近密度阶梯, 逐阶落地）:
--   3/9（RRProperty §2）→ 8/27（RRProperty §4）→ 18/81（RRQuartic §4）
--   → 116/729（本件, 主定理 RRQ6-countIrrQ6-116）
-- 每阶 ~1/N 衰减; 3·116 = 348 ≤ 729 仍极小（nonnatural 分类计数侧证据,
-- 分类 record 见 RRQ6-Judge §5）。
--
-- 结构（判定器在 RRQ6-Judge, 本件只做枚举与计数）:
--   §1  九块枚举数据: 固定 (a₅,a₄) 九种, 每块 81 项 (a₃,a₂,a₁,a₀),
--       a₃ 外层 a₀ 最内（与 RRQuartic §4a 同序）; 九块正文同构（差异只在
--       块名——(a₅,a₄) 已固定, 不在元组内）。
--   §2  计数归并引理: RR-countTrue 对 ++ 的分配 + 经 map 的分配包装。
--   §3  每块一条计数引理 RRQ6-cntBᵢⱼ ≡ kᵢⱼ（refl; k 为 Python 按块实测）。
--   §4  主定理: 九块 ++ 链 + 归并 ≡ 116 = (729−27−9+3)/6。
--   §5  密度 (116,729) + 极小性 3·116 = 348 ≤ 729 + Möbius 四项核对
--       6·116 ≡ 696 = 729−27−9+3。
--
-- 数学核对（Python 实证先行, probes/rrq6_count.py 复跑三路一致）:
-- 判定器法 116 = 暴力全分解法 116 = Möbius (729−27−9+3)/6; 九块 k 值
-- 15,11,12,13,13,13,13,13,13（块序 (a₅,a₄) 字典序）与 §3 逐条一致。
--
-- 层向纪律: 同 RRQ6-Judge——Sovereign.Algebra 禁止 import
-- Sovereign.Application; 判定器 import 复用 RRQ6-Judge 的 RRQ6-irrQ6,
-- 计数器复用 RRProperty 的 RR-countTrue（不建第二份）。
-- 定名纪律: 全部新符号加 RRQ6- 前缀（建档前 grep 自检零撞名）。
-- 分级标注约定: 〔结构定义〕〔refl 枚举〕〔立界注记〕同前件。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.RRQ6-Count where

open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (m≤n+m)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

-- 引用边界（同层 Complexity 复用 + Base 层, 层向合规）:
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Complexity.RRProperty using (RR-countTrue)
open import Sovereign.Algebra.Complexity.RRQ6-Judge using (RRQ6-irrQ6)

--------------------------------------------------------------------------------
-- §1 九块枚举数据〔结构定义; 每块 81 项, a₃ 外层 a₀ 最内〕
--
-- 块序 (a₅,a₄) 字典序: B00,B01,B02,B10,B11,B12,B20,B21,B22; 块内 81 项
-- (a₃,a₂,a₁,a₀) 全空间系统枚举（含可约项——计数由 §3 判定器引理完成,
-- 非名单式; 可约性核对在 refl 内逐项进行, 任一项错则该块引理失败）。
-- 九块正文同构: 元组不含已固定的 (a₅,a₄)。
--------------------------------------------------------------------------------

RRQ6-listB00 : List (Trit × Trit × Trit × Trit)
RRQ6-listB00 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB01 : List (Trit × Trit × Trit × Trit)
RRQ6-listB01 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB02 : List (Trit × Trit × Trit × Trit)
RRQ6-listB02 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB10 : List (Trit × Trit × Trit × Trit)
RRQ6-listB10 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB11 : List (Trit × Trit × Trit × Trit)
RRQ6-listB11 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB12 : List (Trit × Trit × Trit × Trit)
RRQ6-listB12 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB20 : List (Trit × Trit × Trit × Trit)
RRQ6-listB20 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB21 : List (Trit × Trit × Trit × Trit)
RRQ6-listB21 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ6-listB22 : List (Trit × Trit × Trit × Trit)
RRQ6-listB22 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

-- 九块 ++ 链（右结合, 与 §4 归并引理的分段一致）:
RRQ6-restB8 : List (Trit × Trit × Trit × Trit)
RRQ6-restB8 = RRQ6-listB22

RRQ6-restB7 : List (Trit × Trit × Trit × Trit)
RRQ6-restB7 = RRQ6-listB21 ++ RRQ6-restB8

RRQ6-restB6 : List (Trit × Trit × Trit × Trit)
RRQ6-restB6 = RRQ6-listB20 ++ RRQ6-restB7

RRQ6-restB5 : List (Trit × Trit × Trit × Trit)
RRQ6-restB5 = RRQ6-listB12 ++ RRQ6-restB6

RRQ6-restB4 : List (Trit × Trit × Trit × Trit)
RRQ6-restB4 = RRQ6-listB11 ++ RRQ6-restB5

RRQ6-restB3 : List (Trit × Trit × Trit × Trit)
RRQ6-restB3 = RRQ6-listB10 ++ RRQ6-restB4

RRQ6-restB2 : List (Trit × Trit × Trit × Trit)
RRQ6-restB2 = RRQ6-listB02 ++ RRQ6-restB3

RRQ6-restB1 : List (Trit × Trit × Trit × Trit)
RRQ6-restB1 = RRQ6-listB01 ++ RRQ6-restB2

RRQ6-listAll : List (Trit × Trit × Trit × Trit)
RRQ6-listAll = RRQ6-listB00 ++ RRQ6-restB1

--------------------------------------------------------------------------------
-- §2 计数归并引理〔结构定义+归纳; RR-countTrue 对 ++ 的分配〕
--
-- RR-countTrue 是 RRProperty 的既有计数器（import 复用, 不建第二份）,
-- 它对 ++ 的分配本件本地补齐（~10 行）——§4 九块归并的唯一引擎
-- （块计数走 §3 flags 形态, 无需再经 map 的分配引理）。
--------------------------------------------------------------------------------

RRQ6-countTrue-++ : ∀ (bs cs : List Bool) →
  RR-countTrue (bs ++ cs) ≡ RR-countTrue bs + RR-countTrue cs
RRQ6-countTrue-++ [] cs = refl
RRQ6-countTrue-++ (true ∷ bs) cs = cong suc (RRQ6-countTrue-++ bs cs)
RRQ6-countTrue-++ (false ∷ bs) cs = RRQ6-countTrue-++ bs cs

--------------------------------------------------------------------------------
-- §3 每块计数引理〔refl 枚举; k 为 Python 按块实测, 块序 (a₅,a₄) 字典序〕
--
-- 形态说明: 块列表存 (a₃,a₂,a₁,a₀) 四元组（(a₅,a₄) 已固定不在元组内）,
-- 判定须经块包装 RRQ6-irrQ6-block 拼回六元组后过三支判定器——与
-- RRQuartic §4b 判定表 + soundness 的 λ 投影形态同构, 此处用具名包装。
-- 每块先经 map 得字面 flags 列表, 计数引理把 81 项逐一与实测 k 比对:
-- 枚举项写错、判定器与实证不符、k 抄错——任一发生 refl 即失败。
-- k 实测（probes/rrq6_count.py 判定器法, 与暴力分解法逐项交叉一致）:
--   B00=15  B01=11  B02=12  B10=13  B11=13  B12=13  B20=13  B21=13  B22=13
--   合计 116 = (729−27−9+3)/6。
--------------------------------------------------------------------------------

-- 〔结构定义〕块判定包装: 块内 (a₃,a₂,a₁,a₀) 拼固定 (a₅,a₄) 过判定器
RRQ6-irrQ6-block : Trit → Trit → Trit × Trit × Trit × Trit → Bool
RRQ6-irrQ6-block a5 a4 (a3 , a2 , a1 , a0) =
  RRQ6-irrQ6 (a5 , a4 , a3 , a2 , a1 , a0)

-- 九块 flags（字面 Bool 列表, 与块枚举同序）
RRQ6-flagsB00 : List Bool
RRQ6-flagsB00 = map (RRQ6-irrQ6-block T₀ T₀) RRQ6-listB00

RRQ6-flagsB01 : List Bool
RRQ6-flagsB01 = map (RRQ6-irrQ6-block T₀ T₁) RRQ6-listB01

RRQ6-flagsB02 : List Bool
RRQ6-flagsB02 = map (RRQ6-irrQ6-block T₀ T₂) RRQ6-listB02

RRQ6-flagsB10 : List Bool
RRQ6-flagsB10 = map (RRQ6-irrQ6-block T₁ T₀) RRQ6-listB10

RRQ6-flagsB11 : List Bool
RRQ6-flagsB11 = map (RRQ6-irrQ6-block T₁ T₁) RRQ6-listB11

RRQ6-flagsB12 : List Bool
RRQ6-flagsB12 = map (RRQ6-irrQ6-block T₁ T₂) RRQ6-listB12

RRQ6-flagsB20 : List Bool
RRQ6-flagsB20 = map (RRQ6-irrQ6-block T₂ T₀) RRQ6-listB20

RRQ6-flagsB21 : List Bool
RRQ6-flagsB21 = map (RRQ6-irrQ6-block T₂ T₁) RRQ6-listB21

RRQ6-flagsB22 : List Bool
RRQ6-flagsB22 = map (RRQ6-irrQ6-block T₂ T₂) RRQ6-listB22

-- 九块 flags 的 ++ 链（右结合, 与块序一致）:
RRQ6-restF8 : List Bool
RRQ6-restF8 = RRQ6-flagsB22

RRQ6-restF7 : List Bool
RRQ6-restF7 = RRQ6-flagsB21 ++ RRQ6-restF8

RRQ6-restF6 : List Bool
RRQ6-restF6 = RRQ6-flagsB20 ++ RRQ6-restF7

RRQ6-restF5 : List Bool
RRQ6-restF5 = RRQ6-flagsB12 ++ RRQ6-restF6

RRQ6-restF4 : List Bool
RRQ6-restF4 = RRQ6-flagsB11 ++ RRQ6-restF5

RRQ6-restF3 : List Bool
RRQ6-restF3 = RRQ6-flagsB10 ++ RRQ6-restF4

RRQ6-restF2 : List Bool
RRQ6-restF2 = RRQ6-flagsB02 ++ RRQ6-restF3

RRQ6-restF1 : List Bool
RRQ6-restF1 = RRQ6-flagsB01 ++ RRQ6-restF2

RRQ6-flagsAll : List Bool
RRQ6-flagsAll = RRQ6-flagsB00 ++ RRQ6-restF1

RRQ6-cntB00 : RR-countTrue RRQ6-flagsB00 ≡ 15
RRQ6-cntB00 = refl

RRQ6-cntB01 : RR-countTrue RRQ6-flagsB01 ≡ 11
RRQ6-cntB01 = refl

RRQ6-cntB02 : RR-countTrue RRQ6-flagsB02 ≡ 12
RRQ6-cntB02 = refl

RRQ6-cntB10 : RR-countTrue RRQ6-flagsB10 ≡ 13
RRQ6-cntB10 = refl

RRQ6-cntB11 : RR-countTrue RRQ6-flagsB11 ≡ 13
RRQ6-cntB11 = refl

RRQ6-cntB12 : RR-countTrue RRQ6-flagsB12 ≡ 13
RRQ6-cntB12 = refl

RRQ6-cntB20 : RR-countTrue RRQ6-flagsB20 ≡ 13
RRQ6-cntB20 = refl

RRQ6-cntB21 : RR-countTrue RRQ6-flagsB21 ≡ 13
RRQ6-cntB21 = refl

RRQ6-cntB22 : RR-countTrue RRQ6-flagsB22 ≡ 13
RRQ6-cntB22 = refl

--------------------------------------------------------------------------------
-- §4 主定理: monic 六次不可约精确计数 = 116 = (729−27−9+3)/6
--
-- 证明形态: 九块 ++ 链经 §2 countTrue-++ 逐级归并, 每块计数引理代入,
-- 尾步 15+11+12+13·6 = 116 数字闭合（定义性, 无附加证明负担）。
-- Möbius 四项: 729−3⁵×?——准确形态 (3⁶−3³−3²+3)/6 = (729−27−9+3)/6,
-- μ(1)=+3⁶, μ(3)=−3³, μ(2)=−3², μ(6)=+3¹（μ(3)、μ(6) 两项不可漏,
-- 同 RRQuartic §5 RRQ-mobius4 注记形态）。
--------------------------------------------------------------------------------

RRQ6-countIrrQ6 : ℕ
RRQ6-countIrrQ6 = RR-countTrue RRQ6-flagsAll

RRQ6-countIrrQ6-116 : RRQ6-countIrrQ6 ≡ 116
RRQ6-countIrrQ6-116 =
  trans (RRQ6-countTrue-++ RRQ6-flagsB00 RRQ6-restF1)
  (cong₂ _+_ RRQ6-cntB00
  (trans (RRQ6-countTrue-++ RRQ6-flagsB01 RRQ6-restF2)
  (cong₂ _+_ RRQ6-cntB01
  (trans (RRQ6-countTrue-++ RRQ6-flagsB02 RRQ6-restF3)
  (cong₂ _+_ RRQ6-cntB02
  (trans (RRQ6-countTrue-++ RRQ6-flagsB10 RRQ6-restF4)
  (cong₂ _+_ RRQ6-cntB10
  (trans (RRQ6-countTrue-++ RRQ6-flagsB11 RRQ6-restF5)
  (cong₂ _+_ RRQ6-cntB11
  (trans (RRQ6-countTrue-++ RRQ6-flagsB12 RRQ6-restF6)
  (cong₂ _+_ RRQ6-cntB12
  (trans (RRQ6-countTrue-++ RRQ6-flagsB20 RRQ6-restF7)
  (cong₂ _+_ RRQ6-cntB20
  (trans (RRQ6-countTrue-++ RRQ6-flagsB21 RRQ6-restF8)
  (cong₂ _+_ RRQ6-cntB21
           RRQ6-cntB22)))))))))))))))

--------------------------------------------------------------------------------
-- §5 密度与 Möbius 核对（N=6 阶; 续接 RRProperty §5/RRQuartic §5）
--
-- 密度证据链第四点 116/729 ≈ 0.159（前三点 3/9 ≈ 0.33、8/27 ≈ 0.30、
-- 18/81 ≈ 0.22——每阶 ~1/N 衰减形态显见）。
--------------------------------------------------------------------------------

-- 密度对 (不可约数, 全空间)〔结构定义; 第一分量定义性归约为 116〕
RRQ6-density6 : ℕ × ℕ
RRQ6-density6 = RRQ6-countIrrQ6 , 729

RRQ6-density6-116-729 : RRQ6-density6 ≡ (116 , 729)
RRQ6-density6-116-729 = refl

-- 极小性实测点: 3·116 = 348 ≤ 729（覆盖份额至多 ~0.48 的常数上界;
-- 渐近趋零的形态证据链 3/9 → 8/27 → 18/81 → 116/729, 一般 N 见尾注立界）
RRQ6-smallQ6 : 3 * RRQ6-countIrrQ6 ≤ 729
RRQ6-smallQ6 = m≤n+m 348 381

-- Möbius 公式 N₆ = (3⁶−3³−3²+3)/6 的库内核对形态: 6·116 ≡ 696
-- = 729−27−9+3（μ(1)·3⁶ − μ(3)·3² 项 27 − μ(2)·3³ 项 9 + μ(6)·3 项 3;
-- μ(3)、μ(6) 两项不可漏, 同 RRQ-mobius4 注记形态; 一般式
-- (1/n)Σ_{d|n} μ(d)·3^{n/d} 的 μ 簿记以注记承载, 见尾注立界）
RRQ6-mobius6 : 6 * RRQ6-countIrrQ6 ≡ 696
RRQ6-mobius6 = refl

--------------------------------------------------------------------------------
-- §6 立界清单（本件边界，不冒充）与结论
--
--   ✅ 九块 81 项全枚举数据（§1, 729 项 = 3⁶ 全空间系统枚举, 非名单式;
--      落盘后经 Python 解析回读核验逐项一致, 见交付报告）
--   ✅ 计数归并引理 RRQ6-countTrue-++（§2, countTrue 对 ++ 的分配）
--   ✅ 九条块计数引理 k = 15,11,12,13,13,13,13,13,13（§3, refl 逐项;
--      块包装 RRQ6-irrQ6-block 拼回六元组过三支判定器）
--   ✅ 主定理 RRQ6-countIrrQ6-116 = (729−27−9+3)/6（§4, 九块归并闭合;
--      一次编译通过, 未触发 flags 回退路线——块计数本身即 flags 形态）
--   ✅ 密度 (116,729) + 极小性 348 ≤ 729 + Möbius 6·116 ≡ 696（§5, 闭合）
--   〔立界〕「9 块覆盖全空间」的机器侧佐证是计数核对本身（729 项逐一
--      过判定器恰得 Möbius 公式值, 写错/漏项/重项必漂离 116）; 块划分
--      的序结构（字典序 + 块内四层字典序）由枚举书写纪律承载, 未设
--      独立排列引理;
--   〔立界〕N 一般化（参数化次数枚举/密度 ~1/N 渐近）与 Möbius 全式
--      Σ_{d|n} μ(d)·3^{n/d}: 需 GF(3^k) 载体与 μ 簿记基础设施（路线图
--      W3）, 本件仅在 N=6 实测点闭合;
--   〔立界〕载体提升（判定器级 ⟹ GF(3)[x] 环分解 witness）与 RR 原定理
--      形式化: 同 RRQ6-Judge §6 / RRQuartic §5 立界, 不重复设签名。
--
--   0 postulate / 0 hole。
--------------------------------------------------------------------------------
