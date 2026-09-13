{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Format.Doz
-- **Doz —— 十二进制位值制（dozenal positional notation）**
--
-- 本体论位置（严格按 `docs/duodecimal/01-ontology.md` / `08-terminology.md`）：
--
--   | 记号 | 载体 | 地位 |
--   |------|------|------|
--   | **DC**（DuodecClock） | `DuodecPoint = Trit × AlphaPower`（3×4=12 个元素） | **本源**——加法步进 ⊕ 乘法旋转 |
--   | **C₁₂** | `(Duodec, +12)` | DC 的加法投影（12 个元素） |
--   | **R₁₂** | `(Duodec, +12, *12)` | 环投影（有零因子，`2 *12 6 = 0`） |
--   | **Doz** | 位值数字串 | **记数法层**——以 12 为底，可表示任意大的数 |
--
-- ⚠️ **Doz ≠ DC**：DC 是 12 个元素的代数核（有限）；Doz 是以 12 为底的位值记数法，
-- 能表示 12⁹ − 1 这么大的数（本模块取 9 位，见下）。把 Doz 说成「十二进制只有 12 个元素」
-- 是本库已记录的错误（`PROJECT_MEMORY.md` 2026-08-25 21:30 经验教训）。
--
-- 本模块补的是**一直缺失的那一层**：`docs/duodecimal/01-ontology.md` 写着 Doz
-- 「记数法层（尚未系统形式化）」。这里用 `Sovereign.Format.Positional` 的 base = 12 实例
-- 把它形式化，并给出机器位宽（9 位）下的语义定理。
--
-- ── 位宽为什么是 9 ─────────────────────────────────────────────────────
--   · 12⁹ = 5,159,780,352 ≤ 3²⁷ = 7,625,597,484,987 ✅（27-trit 字装得下）
--   · 12¹⁰ = 61,917,364,224 > 3²⁷ ✗
--   · **本模块是「进制层」**（记数法）：只谈基 `b = 12` 的权重 `12^k`、位值 `0..11`、逢 12 进一。
--     它**不谈**这些位值在字里如何被承载——那是**位域（digit field）**，另一个范畴：
--       · 位域层      → `Sovereign.Format.DigitField`（字段状态数、划分、容量）
--       · 位域 ↔ 进制 桥 → `Sovereign.Format.DigitRealization`（双射，不是等号）
--     ⚠️ 禁止把「进制」与「位域」写成同一件事（如「12 进制 = 3 × 2 × 2」）：
--     见 `docs/duodecimal/08-terminology.md` §7.5。
--   · 本模块只规定**位数上限**（`DOZ_DIGITS = 9`）与进位规则；**不规定**一位数位占几个字段 ——
--     那是位域的事（tritvm v1 用「每位 3 个 trit」是它的位域选择，不是进制的性质）。
--     「三进制不适合以 12 为底的记数法」是**错的说法**：按容量口径，27 个三态域与
--     43 个二态域**都装 11 位**十二进制数位
--     （`DigitRealization.doz11-in-27trit` / `doz11-in-43bit`，各配 not-doz12 的 refl）。
--
-- ── 诚实边界 ───────────────────────────────────────────────────────────
-- 1. 语义正确性来自 `Positional`（逐位运算 + 进位归一在模 12⁹ 下保值）。
-- 2. **不证明** C 的进位循环精化成 `Positional.expand`（需要 Frama-C/VST 一类工具）。
-- 3. `render` 只是**编码显示**函数；它的输出等于「规范十二进制写法」这一点，
--    由 `Positional.expand-spec`（值定理）间接支持，而不是逐字符证明。

open import Data.Nat.Base using (ℕ; _<_)

module Sovereign.Format.Doz where

open import Data.Nat using (zero; suc; _+_; _*_; _^_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; reverse)
import Data.List.Relation.Unary.All as All
open import Data.String using (String; _++_)
open import Data.Nat.Show using (show)
open import Data.Nat.Properties using (_<?_; _≟_)
open import Data.Product using (proj₁)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Sovereign.Format.Positional as P

-- base = 12，且 1 < 12
module Pos = P 12 (s≤s (s≤s z≤n))

--------------------------------------------------------------------------------
-- 1. 载体与位宽
--------------------------------------------------------------------------------

-- Doz 数 = 位表（低位在前，原始位可为任意 ℕ；规范位 = 每一位 < 12）
Doz : Set
Doz = Pos.Raw

-- 位数上限：9 位（这是**进制**层的位数；一位占几个字段属**位域**层，见 DigitField）
DOZ_DIGITS : ℕ
DOZ_DIGITS = 9

-- 容量池：12⁹
POOL : ℕ
POOL = 5159780352

POOL≡12^9 : POOL ≡ 12 ^ 9
POOL≡12^9 = refl

--------------------------------------------------------------------------------
-- 2. 值、规范位、加法、乘法（全部复用 Positional 的 base = 12 实例）
--------------------------------------------------------------------------------

value : Doz → ℕ
value = Pos.value

-- 规范位表：v 的 9 位十二进制表示（低位在前），更高位被丢弃（模 12⁹）
digits : ℕ → Doz
digits = Pos.norm DOZ_DIGITS

add : Doz → Doz → Doz
add = Pos.addNorm DOZ_DIGITS

mul : Doz → Doz → Doz
mul = Pos.mulNorm DOZ_DIGITS

-- 机器语义：结果的低 9 位就是真值，丢弃的进位以 12⁹ × carry 显式出现
add-spec : ∀ xs ys →
  value (add xs ys) + 12 ^ 9 * proj₁ (Pos.expand DOZ_DIGITS (value (Pos.addRaw xs ys)))
    ≡ value xs + value ys
add-spec = Pos.add-spec DOZ_DIGITS

mul-spec : ∀ xs ys →
  value (mul xs ys) + 12 ^ 9 * proj₁ (Pos.expand DOZ_DIGITS (value (Pos.conv xs ys)))
    ≡ value xs * value ys
mul-spec = Pos.mul-spec DOZ_DIGITS

-- 归一后的每一位都 < 12：机器上「数字 ≥ 12 → 陷阱」只可能由外部装入的坏编码触发
digits-bound : ∀ v → All.All (_< 12) (digits v)
digits-bound = Pos.norm-bound DOZ_DIGITS

--------------------------------------------------------------------------------
-- 3. 显示（DOZOUT 的期望字符串）
--------------------------------------------------------------------------------

-- 数字 → 字符：0..9 → '0'..'9'，10 → 'A'，11 → 'B'
digitStr : ℕ → String
digitStr d with 9 <? d
... | no _  = show d
... | yes _ with 10 ≟ d
...   | yes _ = "A"
...   | no  _ = "B"

renderFrom : List ℕ → String
renderFrom []       = ""
renderFrom (d ∷ ds) = digitStr d ++ renderFrom ds

-- 去掉高位零，但至少保留一位
dropZeros : List ℕ → List ℕ
dropZeros []             = []
dropZeros (zero    ∷ xs) = dropZeros xs
dropZeros (suc x   ∷ xs) = suc x ∷ xs

-- 规范十二进制写法：高位在前，A/B 表示 10/11；0 打印 "0"
render : ℕ → String
render v with dropZeros (reverse (digits v))
... | [] = "0"
... | ds = renderFrom ds
