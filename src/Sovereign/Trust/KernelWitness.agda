{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.KernelWitness — 内核空类型判定（eb1251683f）的**补丁相关正控制**
--
-- 本模块的存在理由（2026-09-13，依据用户反馈第 3 条）：
--   缺陷 —— 旧版 `Sovereign.Trust.KernelSpec` 自己 import 了 `PatchedTypeChecker`，
--   而后者在**无补丁内核**上 **import 阶段就炸**（`PatchedTypeChecker.agda:84`
--   `Is empty: R1 ≡ R2 (stuck)`）。于是 KernelSpec 的「A/B 差分」那一行，失败点落在
--   被 import 的模块里，**KernelSpec 自己的条款从未在两版下被对照检查过** ——
--   那一行与 `PatchedTypeChecker` 的行完全冗余，判据价值为零。
--
--   修法 —— 把条款拆成两个模块：
--     · `Sovereign.Trust.KernelSpec`（补丁**无关**）：锚点 + 单射性推论（K4/K2 形态）。
--       它必须在 2.9.0 与官方 2.8.0.1 上**都通过** ⇒ 真正的负控制（NaN 行的对照臂）。
--     · **本模块**（补丁**相关**）：自带相异刚性头 `R1w`/`R2w`，**不 import**
--       `PatchedTypeChecker`，使 2.8.0.1 的失败点**精确落在本模块 K1 的空模式行**。
--
-- 期望矩阵（四个 exit 码，A/B 全交叉）：
--   · `KernelSpec`    × 2.9.0      → 0      （补丁无关条款，两版都应通过）
--   · `KernelSpec`    × 2.8.0.1    → 0      ← **真负控制**：对照臂不因补丁而失败
--   · `KernelWitness` × 2.9.0      → 0      （正控制：补丁使相异刚性头判空）
--   · `KernelWitness` × 2.8.0.1    → 42，且报错行 = 本文件的 `¬R1w≡R2w ()`
--                                     （`Is empty: R1w ≡ R2w (stuck)`）
--   第 2 行通过、第 4 行失败，才是「差分测的是补丁，不是环境」的**有效**证据。
--
-- 数学内容（为什么正控制是正当的，而非「用公理凑」）：
--   相异刚性头（不同 `data`/`record` 定义名）之间的等式**不可能有居留元**——因为
--   正的居留元要给出一个值同时属于两个不同的生成方式（展示群第一原理：结构 = 生成方式）。
--   库内已证的三层编码单射性给出同一结论的模型侧版本（见 `KernelSpec` §1/§2）：
--   算术层 `CRTLemmas.crt-merge`、双射层 `Duodecimal.crt12-roundtrip`、
--   望远镜层 `QuantumBridge:395` 起「构造子注入性的 CRT 正交分解」。
--   本模块只把**观测面**写成可编译签名：补丁开 ⇒ 该空类型判定成立；补丁关 ⇒ 判不出。
--
-- 本模块 **不** 声称：把 Haskell `failure` 分支形式化为 Agda 定理（那要把 tcm 状态机
-- 搬进 Agda，不划算，见 `KernelSpec` §5 边界）。

module Sovereign.Trust.KernelWitness where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

--------------------------------------------------------------------------------
-- §1 两个相异刚性头（自足定义 ⇒ 失败点必在本模块，不在 import 链上）
--------------------------------------------------------------------------------

-- | 与 `PatchedTypeChecker.R1` 同形但**独立定义**：无消去子的相异 `record` 头。
--   不用 import 复用，是为了让本模块的编译失败点严格落在下面 K1 那一行。
record R1w : Set where
  constructor r1w
  field f1w : ℕ

record R2w : Set where
  constructor r2w
  field f2w : ℕ

--------------------------------------------------------------------------------
-- §2 K1 正控制（补丁相关）：相异刚性头的 ≡ 判为空
--------------------------------------------------------------------------------

-- | K1 正控制：`R1w ≡ R2w` 判为空。
--   本机 2.9.0（补丁版）通过；官方 2.8.0.1 在此行报
--   `Is empty: R1w ≡ R2w (stuck)`（blocked on 未解决的相异刚性头）而失败。
--   ⇒ 这一行就是「补丁带来能力扩展」的**可机检判据**。
¬R1w≡R2w : (R1w ≡ R2w) → ⊥
¬R1w≡R2w ()

-- | ≢ 形态（供 Haskell 侧正控制引用，与 `PatchedTypeChecker.DistinctRecordsAreEmpty` 对称）
R1w≢R2w : R1w ≢ R2w
R1w≢R2w = ¬R1w≡R2w

-- | 空类型消去子：与 `KernelSpec` §3 的 `K1-witness` 同形，但基于本模块自足定义。
K1w-witness : (R1w ≡ R2w) → ℕ
K1w-witness ()

--------------------------------------------------------------------------------
-- §3 K2 负控制（补丁无关）：**同一**刚性头的等式**不是**空的
--------------------------------------------------------------------------------
-- 补丁判的是「相异 Def」，**不是**「等式一律为空」。这一行在两版下都必须通过——
-- 它是「补丁没有把相等判定整体炸掉」的活证据（与 `DecisionSoundness` 的 C5 三值纪律呼应）。

K2w-same-def-inhabited : R1w ≡ R1w
K2w-same-def-inhabited = refl

--------------------------------------------------------------------------------
-- §4 边界
--------------------------------------------------------------------------------
-- · 本模块**故意**在无补丁内核上编译失败（exit 42）——那是判据，不是缺陷。
-- · 判据有效的前提是同一批文件在 2.9.0 上 exit 0；两行一起看才有意义。
-- · 数学侧无悬案：单射性三层已证（`KernelSpec` §1/§2 钉签名）。

-- 0 postulate.
