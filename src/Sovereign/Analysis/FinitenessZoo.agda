{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.FinitenessZoo
-- 有限性定义动物园 — 任务书第一层索引（头注与依赖聚合，不承载证明体）
--
-- 数学背景：Dedekind (1888) / Dirichlet (1834) / Tarski-Kuratowski (1920–24) 三个
--   经典有限性定义在**型有限**（Finite A = Σ ℕ (A ≃ Fin n)）上的对账：正向可构造
--   证明的做成定理（子模块），需经典逻辑的方向作**缺口声明**（下 §5）。
--
-- 【连续统缺陷对照（docs/群论红灯审查-离散全息修复.md）】经典有限性理论长在连续统
--   基座上（任意集合/幂集/排中律）；本库构造主义、无 Choice、无连续统
--   （memory/lean-libraries-gap-analysis.md :96）。六缺陷框架纪律原话：「焊死的精确
--   范围以上表为准——未焊死的部分如实标注，不以断言代替证明」—— 本动物园照此办理。
--
-- 【依赖类型论展示群对齐（docs/duodecimal/11 号）】本动物园是**定义/定理层**，非
--   展示群本体，八要素（载体/生成元/关系/相位/时钟/归零/刚性/核对）不构成其公理
--   候选（M8 判据 4：定义层不升公理）。载体立场一致：Σ-类型 + Fin n（fzero/fsuc
--   构造生成，「结构 = 生成方式」）；根基 = Base/Trit（GF(3) 及其扩展），Trit ≅ Fin 3
--   （Geometry/TorusGeometry.tritOf/finOf）。相位/时钟/刚性维度在 DC 侧
--   （DuodecClock 8/8 + DayanCore + DCGroup），本层不新增。
--
-- 拆分（2026-10-02，避免单文件堆积；一节一模块，可独立编译）：
--   §1 载体/传输机件  → Analysis/Finiteness/Foundations.agda
--   1.1 型有限⟹Dedekind → Analysis/Finiteness/Dedekind.agda（P0-a）
--   1.2 鸽巢双向等价    → Analysis/Finiteness/Pigeonhole.agda
--   1.3 Tarski 极小元    → Analysis/Finiteness/Tarski.agda
--
-- §5 缺口声明（诚实边界，非证明失败）：
--   `dedekindFinite→finite`（Dedekind 有限⟹型有限）在构造性逻辑下**不成立**
--   （需排中律或 Choice —— 正是连续统装置）；Tarski ⟺ 其余两定义同理。本动物园
--   **不给出证明**，只标注为经典等价。反证法只在 ¬ 前提内消去，不外推完备性。
--
-- 0 postulate / 0 hole。
module Sovereign.Analysis.FinitenessZoo where

open import Sovereign.Analysis.Finiteness.Foundations
open import Sovereign.Analysis.Finiteness.Dedekind
open import Sovereign.Analysis.Finiteness.Pigeonhole
open import Sovereign.Analysis.Finiteness.Tarski
