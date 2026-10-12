{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI4n
-- Gskel 泛形批：四泛形件路线实测报告（否决型定性 + 可达件落地）
--
-- 数学背景：_PPI4m §2/§3 立界四泛形件（cutZAcc-exc/cutZ-exc-head/canonical/
--   decomp-unique）的后批承诺。目标 canonical : AllExc es →
--   proj₁ (cutZ (concatL es)) ≡ es（⟹ decomp-unique 一行收口）；
--   核心缺件 exc-head : IsExc e → proj₁ (cutZ (e ++w t)) ≡ e ∷ proj₁ (cutZ t)。
--
-- 核心原则：诚实分阶段（路线实测即合格）；零洞零 postulate；two-chain 兼容
--   核对 refl 级；#56 三路线逐一实测记录。

module _PPI4n where

open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import Sovereign.Topology.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)
open import _PPI4d using (e01; e10; w2)
open import _PPI4j using (module Cut; NoX; Nonempty; IsExc)
open import _PPI4k using (module LoopRes)

private
  module DG = DiGraph

-- two-chain 闭实例（_PPI4m 同款）
module C  = Cut {G = Gskel two-chain} _≟F_
module TC = LoopRes {Gskel two-chain} _≟F_

-- ════════════════════════════════════════════════════════════════════════
-- §1 可达件：canonical 基案 + two-chain 兼容核对（refl 级）
-- ════════════════════════════════════════════════════════════════════════

-- 基案（零 excursion 序列）：concatL [] = nil；cutZ (nil) = [] —— defeq 闭合
canonical-base : proj₁ (TC.cutZ (C.concatL {fzero} [])) ≡ []
canonical-base = refl

-- two-chain 兼容核对（与 _PPI4m §5 check-canonical-w2w2 同形同项——defeq 一致）
compat-canonical-w2w2 : proj₁ (TC.cutZ (C.concatL (w2 ∷ w2 ∷ []))) ≡ (w2 ∷ w2 ∷ [])
compat-canonical-w2w2 = refl

compat-cutZ-w2 : proj₁ (TC.cutZ w2) ≡ (w2 ∷ [])
compat-cutZ-w2 = refl

-- ════════════════════════════════════════════════════════════════════════
-- §2 路线实测报告（#56 三路线——否决型定性，root cause 钉死）
-- ════════════════════════════════════════════════════════════════════════
--
-- 【墙位精确定位】exc-head/canonical 的 cons 案可配（cons 单边索引合一无碍）；
--   **nil 案即墙**：e : Walk G a a 匹配 (nil v) 产生 v ≟ a 双同索引方程 ⇒
--   SplitError.UnificationStuck（#56 同索引家族）——而 nil 消解句柄
--   （Nonempty (nil v) = ⊥）需先完成该匹配 ⇒ 消解被墙挡住（_PPI4m:88 同判）。
--
-- 【路线① 构造携带形】把 exc-head 作为递归产出物捆绑（cutZHead : OutHead 形，
--   镜像 cutZAcc 递归）——需 ~150-250 行重写（超本批 50-100 预算）；且其输出一致性
--   = decomp-unique 本身（循环依赖需同步设计）⇒ **独立立项**（先陈述 OutHead 类型
--   再施工——本批不取）。
--
-- 【路线② 残段化】canonical 弱化为「长度面 + 逐项面」两段式：长度面可由
--   resZ-len0/concatL-++（_PPI4k §3）承载；逐项面仍需 exc-head ⇒ 墙位不消半分
--   （只削减长度段，逐项段同墙）⇒ 不取。
--
-- 【路线③ 具象索引】fzero 类具体索引可配（#56 ③ 再证）——two-chain 唯一性已由
--   _PPI4l uniq-w2/w2w2 + _PPI4m §4/§5 全证承担（§1 兼容核对确认同项）；
--   泛形 a 不可具象化 ⇒ 泛形面此路不通。
--
-- 【结论】四泛形件本批否决型收口：墙位 = nil 案同索引合一；
--   下批建议：cutZHead 构造携带镜像批（独立立项，OutHead 先陈述后施工，~150-250 行）。
--   two-chain 具象面（真实数学需求面）已全闭——泛形为一般化锦上件非缺口。
