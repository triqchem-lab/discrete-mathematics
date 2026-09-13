{-# OPTIONS --rewriting --guardedness #-}
-- 律算数学 · 十二进制层的**形式化 oracle（查询面）**
--
-- 与 `Sovereign.Verify.KernelOracle` 同一定位：本模块本身不是可执行程序，而是**查询面**——
-- 驱动脚本（`tools/testing/sov/agda-oracle.mjs --duodec`）把下面的函数名当表达式发给 Agda
-- 交互接口（`Cmd_compute_toplevel`），拿回**形式库算出的值**，再交给 tritvm 的
-- `--agda-check` 逐例比对。
--
-- ⚠️ 设计纪律：本模块**只做 ℕ 索引的搬运**（把 Agda 的 `Trit` / `AlphaPower` / `Duodec`
-- 归纳类型与 ℕ 互转），**不重新定义任何数学**。所有取值都直接来自：
--   · `Sovereign.Base.Trit`                     （⊕ / negate / tritToℕ）
--   · `Sovereign.Algebra.GroupTheory.DuodecClock`（mulAlpha / alphaInv / mixedOp / duodec-inv / toDuodec）
--   · `Sovereign.Algebra.Duodecimal`             （_+12_ / _*12_ / π3 / π4 / crt12 / toℕ₁₂）
--   · `Sovereign.Format.Doz`                     （十二进制位值制；本次新增）
-- 这样 oracle 与实现之间不会出现「我自己重写一遍再自己校验」的循环。
--
-- 覆盖与缺口：
--   ✅ DC 加法分量 ⊕（dcMixT）           ← Trit._⊕_
--   ✅ ⟨α⟩ 乘法 mulAlpha / 逆 alphaInv    ← DuodecClock
--   ✅ mixedOp 的 DC → C₁₂ 标签像          ← DuodecClock.toDuodec ∘ mixedOp
--   ✅ 走钟 g^k 的分量轨迹与标签            ← DuodecClock.mixedOp / duodec-e
--   ✅ C₁₂ 加法 / R₁₂ 乘法                ← Duodecimal._+12_ / _*12_
--   ✅ π₃ / π₄ 投影                       ← Duodecimal.π3 / π4
--   ✅ Doz 加法/乘法与规范渲染              ← Format.Doz（Positional 的 base=12 实例）
--   ❌ 未覆盖：DC 的**置换表示**（`Action DC`）在本库中尚无实例
--      （见 `memory/direction-2026-09-dc-permutation-representation.md`：R2 仍开）
--   ❌ 未覆盖：Doz 的进位循环精化（见 Format.Positional 头部的诚实边界）
--
-- 用法：由 tools/testing/sov/agda-oracle.mjs 驱动，不手工调用。

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _<_)

module Sovereign.Verify.DuodecOracle where

open import Data.Fin using (Fin; toℕ)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.String using (String)

import Sovereign.Base.Trit as T
import Sovereign.Algebra.GroupTheory.DuodecClock as DC
import Sovereign.Algebra.Duodecimal as Duo
import Sovereign.Format.Doz as Doz

--------------------------------------------------------------------------------
-- 1. ℕ ↔ 归纳类型的搬运（唯一允许的「新代码」，且无任何数学内容）
--------------------------------------------------------------------------------

tritOf : ℕ → T.Trit
tritOf 0 = T.T₀
tritOf 1 = T.T₁
tritOf _ = T.T₂

alphaOf : ℕ → DC.AlphaPower
alphaOf 0 = DC.a0
alphaOf 1 = DC.a1
alphaOf 2 = DC.a2
alphaOf _ = DC.a3

alphaIdx : DC.AlphaPower → ℕ
alphaIdx DC.a0 = 0
alphaIdx DC.a1 = 1
alphaIdx DC.a2 = 2
alphaIdx DC.a3 = 3

duodecOf : ℕ → Duo.Duodec
duodecOf 0  = Duo.d0
duodecOf 1  = Duo.d1
duodecOf 2  = Duo.d2
duodecOf 3  = Duo.d3
duodecOf 4  = Duo.d4
duodecOf 5  = Duo.d5
duodecOf 6  = Duo.d6
duodecOf 7  = Duo.d7
duodecOf 8  = Duo.d8
duodecOf 9  = Duo.d9
duodecOf 10 = Duo.d10
duodecOf 11 = Duo.d11
duodecOf _  = Duo.d0

-- DCLD imm 的编码：t = imm % 3，alpha = imm / 3（与 tritvm 的 DCLD 一致）
dcPointOf : ℕ → DC.DuodecPoint
dcPointOf n = tritOf (n % 3) , alphaOf (n / 3)

--------------------------------------------------------------------------------
-- 2. DC 本源层
--------------------------------------------------------------------------------

-- ⟨α⟩ 乘法（索引形式）
dcMulAlpha : ℕ → ℕ → ℕ
dcMulAlpha i j = alphaIdx (DC.mulAlpha (alphaOf i) (alphaOf j))

-- 加法分量 ⊕（经 mixedOp 取第一分量，确保走的是本源运算）
dcMixT : ℕ → ℕ → ℕ
dcMixT i j = T.tritToℕ (proj₁ (DC.mixedOp (tritOf i , DC.a0) (tritOf j , DC.a0)))

-- duodec-inv 的两个分量
dcInvT : ℕ → ℕ
dcInvT i = T.tritToℕ (proj₁ (DC.duodec-inv (tritOf i , DC.a0)))

dcInvA : ℕ → ℕ
dcInvA i = alphaIdx (proj₂ (DC.duodec-inv (T.T₀ , alphaOf i)))

--------------------------------------------------------------------------------
-- 3. 投影层：DC → C₁₂ 标签（toDuodec ∘ mixedOp）与 π₃/π₄
--------------------------------------------------------------------------------

-- mixedOp 之后取 C₁₂ 标签：这是**有损投影**，用于在机器上暴露红线
dcMixP : ℕ → ℕ → ℕ
dcMixP p q = Duo.toℕ₁₂ (DC.toDuodec (DC.mixedOp (dcPointOf p) (dcPointOf q)))

-- 单个 DC 点的标签（即 (4t + 9a) mod 12）
dcLabel : ℕ → ℕ
dcLabel n = Duo.toℕ₁₂ (DC.toDuodec (dcPointOf n))

dcPi3 : ℕ → ℕ
dcPi3 n = T.tritToℕ (Duo.π3 (duodecOf n))

dcPi4 : ℕ → ℕ
dcPi4 n = toℕ (Duo.π4 (duodecOf n))

--------------------------------------------------------------------------------
-- 4. 走钟：联合生成元 g = (T₁, a₁) 的 k 次幂（本源侧逐步演化）
--------------------------------------------------------------------------------

g : DC.DuodecPoint
g = T.T₁ , DC.a1

gpow : ℕ → DC.DuodecPoint
gpow zero    = DC.duodec-e
gpow (suc k) = DC.mixedOp (gpow k) g

dcTickT : ℕ → ℕ
dcTickT k = T.tritToℕ (proj₁ (gpow k))

dcTickA : ℕ → ℕ
dcTickA k = alphaIdx (proj₂ (gpow k))

dcTickL : ℕ → ℕ
dcTickL k = Duo.toℕ₁₂ (DC.toDuodec (gpow k))

--------------------------------------------------------------------------------
-- 5. C₁₂ 加法投影 / R₁₂ 环投影
--------------------------------------------------------------------------------

c12Add : ℕ → ℕ → ℕ
c12Add a b = Duo.toℕ₁₂ (Duo._+12_ (duodecOf a) (duodecOf b))

r12Mul : ℕ → ℕ → ℕ
r12Mul a b = Duo.toℕ₁₂ (Duo._*12_ (duodecOf a) (duodecOf b))

--------------------------------------------------------------------------------
-- 6. Doz（十二进制位值制）
--------------------------------------------------------------------------------

dozAdd : ℕ → ℕ → ℕ
dozAdd a b = Doz.value (Doz.add (Doz.digits a) (Doz.digits b))

dozMul : ℕ → ℕ → ℕ
dozMul a b = Doz.value (Doz.mul (Doz.digits a) (Doz.digits b))

-- 规范十二进制写法（DOZOUT 的期望字符串）
dozStr : ℕ → String
dozStr = Doz.render
