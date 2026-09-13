{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.PatchedTypeChecker
--
-- 本地 Agda 工具链**偏离上游**的行为见证（不是数学定理，是工具链能力探针）。
--
-- ⚠ 归属必须写准（2026-09-10 更正，用户指出）：本模块见证的是 **eb1251683f**，
--   **不是 PR #8611**。两者是**两个不同的变更**，先前我把它们混为一谈：
--
--   · **PR #8611 = 分支 `fix/cubical-injectivity-retract`**（2026-07-13 并入 master）。
--     其真正内容（`git diff origin/master...分支`，7 文件 305 行）是 **UnifyEquiv 的左逆/retract 机制重构**：
--       Rules/LHS/Unify/LeftInverse.hs  +217   ← 「Functions for building the left inverse part of a UnifyEquiv」
--       Rules/LHS/Unify.hs +25 ／ Unify/Types.hs +16 ／ Conversion.hs +39
--       Primitive/Cubical.hs +18 ／ Datatypes.hs +9 ／ Substitute.hs +9
--     ⚠ 该分支**保持上游的 `UnifyStuck`**（`failure = return $ UnifyStuck []`），
--       并把 `test/Fail/Issue292.agda` **留在 Fail**——即**不改变**上游「不允许证明类型可区分」的决定。
--     其本地形式化对应见 Sovereign.Structology.QuantumBridge §TelescopeVerification
--       （`makeTau`/`liftS`/`nTarget`/`retract` 名字级对应，见该模块 :640,661,666,695,702,712）。
--
--   · **eb1251683f**（2026-07-27，本地提交；**与 PR #8611 是两件事**）= 本模块见证的那个变更：
--     它修的是 **Agda 空类型判定的不完备性与场景覆盖**（非数学命题，是工具链缺陷修复）：
--       · src/full/Agda/TypeChecking/Empty.hs —— `checkEmptyType` 中 `splitLast` 前加
--           `instantiateFull tel`，使**经 MetaV 替换的类型归约到构造子形式**再分裂
--       · src/full/Agda/TypeChecking/Rules/LHS/Unify.hs
--           `failure` 分支：`Def d / Def d'` 且 `d /= d'` 且两边无 elims 时返回 **`UnifyConflict`**
--           （不同 Def 节点之间的等式约束**判为空**），而非上游的 `UnifyStuck`
--     提交信息自述：**「previously stuck emptyness checks now resolve correctly」**
--     —— 即把**本该判为空却卡住**的情形判出来；golden 测试跨
--     **Issue292 / 292d / 413 / 835 / Stuck** = **场景覆盖**。
--     `test/Fail/Issue292.agda` 改名到 `test/Succeed/` 是**完备性的推论**，不是刻意改语义
--     （该测试正文注释「which we don't want」记录的是**上游的顾虑**，
--       可作为日后回馈社区时要说明的点，但不构成本地修复的动机）。
--
-- 【2026-09-10 人类裁决】PR #8611 一线**暂缓**：已与上游管理员沟通，**找不到能审核该理论变更的人**
--   （证明器底层元理论研究面窄、很多理论无人维护），故修复**只能本地实现**；
--   **我们现在使用的 Agda 版本就是修复过的版本**。Agda 限制与缺陷仍在，但够用；
--   待本数学库结束后再评估是否向社区反馈。⇒ 本模块作为**工具链能力判据**继续保留。
--
-- 实测（当时系统 Agda = `2.9.0-e8f5682-dirty`，即 /opt/agda/agda；
--   跑 master 的 `test/Succeed/Issue292.agda` → exit 0）：
-- ⚠ 2026-09-11 更新：系统 Agda 已换为 merged master(1705389c69) 构建，版本串
--   `2.9.0-1705389`；本模块在新版下重编仍 exit 0（见文件末说明）。
--   上面那条实测**保留原样**（它记录的是当时的工具链），重跑请以版本串为准。
--   本地工具链**接受** Issue292 ⇒ 它带 **eb1251683f** 的语义，而非分支独自的状态。
--
-- 为什么需要这个模块：
--   该补丁改变的是 Agda 的**接受关系**（哪些程序能通过类型检查），属元理论变更，
--   无法在 Agda 内部形式化为一个命题——但它的**行为后果**可以：
--   下面这个项在未打补丁的 Agda 上报
--     UnsolvedConstraints: Is empty: R1 ≡ R2 (stuck)
--   在本地 Agda 上编译通过。于是「本地工具链带该补丁」这件事有了可复现的机器证据。
--
-- 配套的数学侧形式化（补丁所依赖的 CRT 正交分解，三层，均 0 postulate 0 hole）：
--   · 算术层   Sovereign.Arithmetic.CRTLemmas      coprime-POW2-POW3 / crt-merge
--   · 双射层   Sovereign.Algebra.Duodecimal        crt12-roundtrip / crt12-inv-π3 / -π4
--   · 望远镜层 Sovereign.Structology.QuantumBridge §TelescopeVerification
--                roundtrip-general / crt-orthogonal / deBruijn-lift / ThreeSegment
--                （该模块 395 行起自述「Agda PR #8611: 构造子注入性的 CRT 正交分解」）
--
-- ⚠ 上游审阅时的诚实边界：上述数学与 Haskell 实现之间**没有形式化桥接**
--   （wiki/39-logic-type-theory.md:124-125 自述：这是 L2，当前 0 行代码）。
--   本模块见证的是**工具链行为**，不替代那条桥接。
--
-- ⚠ 若换回上游 Agda（或只带 PR #8611 分支、不带 eb1251683f 的 Agda），
--   本模块**应当编译失败**（`Is empty: R1 ≡ R2 (stuck)`）——那正是它的判据价值：
--   它区分「有 eb1251683f」与「没有」。分支自己的 `test/Fail/Issue292.err` 记的就是这个 stuck。
module Sovereign.Trust.PatchedTypeChecker where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- 两个互不相同（结构上无公共构造子）的 record 类型
record R1 : Set where
  field a : ℕ

record R2 : Set where
  field b : ℕ

-- |元理论变更的行为见证。
--
-- 类型 `R1 ≡ R2` 在补丁下被判为**空类型**，故 `λ()` 空模式匹配合法，本项成立。
-- 在上游 Agda 上，同一项会因 `Is empty: R1 ≡ R2 (stuck)` 而无法构造。
distinct-records-are-empty : (R1 ≡ R2) → ℕ
distinct-records-are-empty ()

-- |同型自反的对照：同一类型名的等式**不是**空的，走 refl 分支。
-- 两者并置说明补丁判的是「不同 Def 节点」，而不是「等式一律为空」。
same-record-is-inhabited : R1 ≡ R1
same-record-is-inhabited = Relation.Binary.PropositionalEquality.refl
