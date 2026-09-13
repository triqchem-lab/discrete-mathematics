{-# OPTIONS --rewriting --guardedness #-}
-- 律算数学 · 内核移植层的**形式化 oracle（查询面）**
--
-- 为什么是「查询面」而不是可执行程序：本库大量模块带 `--rewriting`，而 Agda 的 GHC 后端
-- 不支持它（`agda --compile` 实测不生成 .hs）。所以走 Agda 自己的交互接口：
-- 驱动脚本把这些函数名当表达式发过去（`Cmd_compute_toplevel`），拿回**形式库算出的值**，
-- 再交给内核树的 C 检查器逐例比对。
--
-- 覆盖与**缺口**（诚实清单）：
--   ✅ GF(3) 加/乘/范数      ← Sovereign.Coding.Trit（_⊕_/_⊗_；环公理在 Sovereign.Base.Trit 里穷举 refl）
--   ✅ 宪法常数              ← Sovereign.Base.Invariants
--   ✅ 5-trit 打包 / 解包     ← Sovereign.Coupling.LCM（pack5 / unpack5）
--   ✅ LCM 桥 (acc*3¹¹)/2¹⁶  ← 与 Sovereign.Coupling.Zhonglv 的同式定义
--   ⚠ 30-trit 截面 → 坐标     ← LCM.coordinateToSection / sectionToCoordinate（内核侧还没有对应实现）
--   ❌ **11 位基 3 环（内核 sov_z3r_*）在库里没有形式化对应**：库里的三进制向量是
--      SovereignSection = Vec Trit 30，而内核/C++ 用的是 11 位（3¹¹）。这一层尚未被形式验证
--      （见 lib/sov/README 的缺口清单；待写 Sovereign.Verify.Z3R：同位表示 + 进位 + 与 ℕ mod 3¹¹ 的同态定理）。
--
-- 用法：由 tools/testing/sov/agda-oracle.mjs 驱动，不手工调用。

module Sovereign.Verify.KernelOracle where

open import Data.Nat using (ℕ; zero; suc; _*_; _/_; _+_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.List using (List; _∷_; [])

import Sovereign.Coding.Trit as C
open C using (Trit; T₀; T₁; T₂; toℕ)
import Sovereign.Coupling.LCM as LCM
import Sovereign.Base.Invariants as Inv

--------------------------------------------------------------------------------
-- 宪法常数（直接引用 Invariants 的定义）
--------------------------------------------------------------------------------

sovereignLcm : ℕ
sovereignLcm = Inv.SOVEREIGN_LCM

polarWinding : ℕ
polarWinding = Inv.POLAR_WINDING

toroidalWinding : ℕ
toroidalWinding = Inv.TOROIDAL_WINDING

chernNumber : ℕ
chernNumber = Inv.CHERN_NUMBER

gapNum : ℕ
gapNum = Inv.GAP_NUM

gapDen : ℕ
gapDen = Inv.GAP_DEN

grandPump : ℕ
grandPump = Inv.POLAR_WINDING * Inv.TOROIDAL_WINDING

--------------------------------------------------------------------------------
-- GF(3)（trit 用 ℕ 编码 0/1/2，驱动逐个发查询）
--------------------------------------------------------------------------------

fromCode : ℕ → Trit
fromCode 0 = T₀
fromCode 1 = T₁
fromCode _ = T₂

gf3Add : ℕ → ℕ → ℕ
gf3Add a b = toℕ (C._⊕_ (fromCode a) (fromCode b))

gf3Mul : ℕ → ℕ → ℕ
gf3Mul a b = toℕ (C._⊗_ (fromCode a) (fromCode b))

-- |T₀|²=0；|T₁|²=|T₂|²=1
gf3Norm : ℕ → ℕ
gf3Norm 0 = 0
gf3Norm _ = 1

--------------------------------------------------------------------------------
-- 5-trit 打包 / 解包（形式定义来自 LCM）
--------------------------------------------------------------------------------

packOf : ℕ → ℕ
packOf v = LCM.pack5 (LCM.unpack5 v)

unpackStr : ℕ → String
unpackStr v = digits (LCM.unpack5 v)
  where
    digits : Vec Trit 5 → String
    digits (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
      show (toℕ a) ++ " " ++ show (toℕ b) ++ " " ++ show (toℕ c) ++ " "
      ++ show (toℕ d) ++ " " ++ show (toℕ e)

--------------------------------------------------------------------------------
-- LCM 桥与位权
--------------------------------------------------------------------------------

-- (acc × 3¹¹) / 2¹⁶ —— 与 Zhonglv 的形式化同式
bridgeOf : ℕ → ℕ
bridgeOf acc = (acc * 177147) / 65536

-- 30-trit 截面 → 坐标（内核侧暂无对应实现，作为对照基线保留）
sectionCoord : ℕ → ℕ
sectionCoord n = LCM.sectionToCoordinate (LCM.coordinateToSection n)

-- 3^k（供 C 侧核对 SOV_Z3R_T*）
pow3 : ℕ → ℕ
pow3 zero = 1
pow3 (suc k) = 3 * pow3 k
