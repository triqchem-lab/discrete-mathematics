{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.OracleCollapse
-- oracle 惰性定理件——PvsNP 程序批二 OCX
--
-- 定理意义：OracleClasses 的 oracle 设计是「oracle 无关正确性」——完备/正确/
-- 代价/查询界对一切 oracle 实例量化（其头注 (b)）。本件把该设计的边界从注释
-- 升为类型层定理：(1) 任何普通 NP 语言免费提升为 NP^A 成员（验证器忽略
-- oracle 槽，查询账记 0）；(2) 任何 P^A 成员免费剥掉 oracle 槽回到 P（取定
-- oracle 实例 λ _ → false 即合法）；(3) 故「强化版 BGS₁ 类前提」（存在 A：
-- A ∈ P 且 P^A = NP^A）蕴含 P = NP——在本库保守设计下「BGS₁ 类存在性」
-- 不弱于 P=NP 本身，当前设计无法表达非平凡相对化。
--
-- 分级标注：〔结构定义〕〔结构证明〕〔立界注记〕（同库惯例）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.OracleCollapse where

open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (Bool; false)
open import Sovereign.Algebra.Complexity.TimeBound
  using (value; steps; Mono; Pos)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass using (TritLang; InP)
open import Sovereign.Algebra.Complexity.NPClass using (InNP)
open import Sovereign.Algebra.Complexity.OracleClasses
  using (OC-CountedQ; oc-cntq; oc-value; oc-steps;
         OC-OracleFam; OC-LangOf; OC-InP; OC-InNP; OC-NoQuery; oc-collapse)

-- ────────────────────────────────────────────────────────────────────
-- §1 OCX-np-lift：InNP → OC-InNP〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 镜像 oc-P⊆NP 的结构：验证器忽略 oracle 槽（A′ 实参弃置），查询账记 0；
-- InNP 的字段在 oracle 无关设计下直接搬入。查询界取常数 1（Pos 排除零界；
-- 真实账目恒 0 ≤ 1）。完备/正确/代价/查询界对一切 A′ 成立，与 A′ 无关继承。

OCX-np-lift : ∀ {mn A L} (np : InNP L) → OC-InNP mn A L
OCX-np-lift np = record
  { ocnp-p        = InNP.np-p np
  ; ocnp-p-mono   = InNP.np-p-mono np
  ; ocnp-p-pos    = InNP.np-p-pos np
  ; ocnp-q        = λ _ → 1
  ; ocnp-q-mono   = λ _ → ≤-refl
  ; ocnp-q-pos    = λ _ → s≤s z≤n
  ; ocnp-witLen   = InNP.np-witLen np
  ; ocnp-w-mono   = InNP.np-w-mono np
  ; ocnp-verifier = λ n x w A′ →
      oc-cntq (value (InNP.np-verifier np n x w))
              (steps (InNP.np-verifier np n x w)) 0
  ; ocnp-complete = λ n x A′ l → InNP.np-complete np n x l
  ; ocnp-sound    = λ n x w A′ v → InNP.np-sound np n x w v
  ; ocnp-cost     = λ n x w A′ → InNP.np-cost np n x w
  ; ocnp-qcount   = λ n x w A′ → z≤n }

-- ────────────────────────────────────────────────────────────────────
-- §2 OCX-inp-strip：OC-InP → InP〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- key insight：oracle 无关性使「剥掉 oracle 槽」免费——完备/正确/代价界对
-- 一切 oracle 实例量化，故取定实例 A₀ = λ _ → false 后各字段照抄即合法；
-- 查询账目弃置（InP 判定器无查询槽）。

OCX-inp-strip : ∀ {mn A L} (dp : OC-InP mn A L) → InP L
OCX-inp-strip dp = record
  { p          = OC-InP.oc-p dp
  ; p-mono     = OC-InP.oc-p-mono dp
  ; p-pos      = OC-InP.oc-p-pos dp
  ; decider    = λ n x →
      let c = OC-InP.oc-decider dp n x (λ _ → false)
      in  mkCnt (oc-value c) (oc-steps c)
  ; p-complete = λ n x l → OC-InP.oc-complete dp n x (λ _ → false) l
  ; p-sound    = λ n x v → OC-InP.oc-sound dp n x (λ _ → false) v
  ; p-cost     = λ n x → OC-InP.oc-cost dp n x (λ _ → false) }

-- ────────────────────────────────────────────────────────────────────
-- §3 OCX-bgs₁-degenerate：强化版 BGS₁ 前提 ⟹ P = NP〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 定理意义：在本库保守 oracle 设计（oracle 无关正确性）下，「BGS₁ 类存在性」
-- 不弱于 P=NP 本身——当前设计无法表达非平凡相对化，此为设计边界的诚实文档。
-- 前提 record 镜像 OC-BGS₁ 陈述形 + 强化分量：
--   ocxs-aInP：A ∈ P（形同 oc-collapse 前提 dA : InP (OC-LangOf A)）；
--   ocxs-mn-mono：查询长调度单调（oc-collapse 另一前提）。
-- 主路线（三件拼合）：InNP →(§1) OC-InNP → ocxs-npa⊆pa → OC-InP →(§2) InP；
-- 辅路线（§4，消费 aInP/mn-mono）：经 oc-collapse 消除，同结论。
record OCX-BGS₁-Strong : Set₁ where
  field
    ocxs-mn      : ℕ → ℕ                        -- 查询串长调度
    ocxs-mn-mono : Mono ocxs-mn                 -- 〔结构证明〕（oc-collapse 前提）
    ocxs-oracle  : OC-OracleFam                 -- oracle 选择（∃ 的见证位）
    ocxs-aInP    : InP (OC-LangOf ocxs-oracle)  -- 强化分量：A ∈ P
    ocxs-npa⊆pa  : ∀ (L : TritLang) →
                   OC-InNP ocxs-mn ocxs-oracle L → OC-InP ocxs-mn ocxs-oracle L
    ocxs-status  : ℕ                            -- 0 = 前提未被任何构造见证
                                                -- （本件正证明其强度 = P=NP 级）

OCX-bgs₁-degenerate : OCX-BGS₁-Strong → ∀ (L : TritLang) → InNP L → InP L
OCX-bgs₁-degenerate pr L ip =
  OCX-inp-strip (OCX-BGS₁-Strong.ocxs-npa⊆pa pr L (OCX-np-lift ip))

-- ────────────────────────────────────────────────────────────────────
-- §4 辅路线：oc-collapse 消除〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

OCX-collapse-route : ∀ (pr : OCX-BGS₁-Strong) (L : TritLang) →
                     OC-InNP (OCX-BGS₁-Strong.ocxs-mn pr)
                             (OCX-BGS₁-Strong.ocxs-oracle pr) L → OC-NoQuery L
OCX-collapse-route pr L ip =
  oc-collapse (OCX-BGS₁-Strong.ocxs-mn-mono pr)
              (OCX-BGS₁-Strong.ocxs-aInP pr)
              (OCX-BGS₁-Strong.ocxs-npa⊆pa pr L ip)

OCX-noq-strip : ∀ {L} (nq : OC-NoQuery L) → InP L
OCX-noq-strip nq = record
  { p          = OC-NoQuery.oc0-p nq
  ; p-mono     = OC-NoQuery.oc0-p-mono nq
  ; p-pos      = OC-NoQuery.oc0-p-pos nq
  ; decider    = λ n x →
      mkCnt (oc-value (OC-NoQuery.oc0-decider nq n x))
            (oc-steps (OC-NoQuery.oc0-decider nq n x))
  ; p-complete = λ n x l → OC-NoQuery.oc0-complete nq n x l
  ; p-sound    = λ n x v → OC-NoQuery.oc0-sound nq n x v
  ; p-cost     = λ n x → OC-NoQuery.oc0-cost nq n x }

-- 辅路线整链（与主路线同结论；两线交叉印证退化定理）
OCX-bgs₁-degenerate-via-collapse :
  OCX-BGS₁-Strong → ∀ (L : TritLang) → InNP L → InP L
OCX-bgs₁-degenerate-via-collapse pr L ip =
  OCX-noq-strip (OCX-collapse-route pr L (OCX-np-lift ip))

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   退化根源 = oracle 无关正确性（OracleClasses 头注 (b)）：完备/正确/
--       代价对一切 oracle 实例量化，故 §2 取定 λ _ → false 即合法；「固定
--       oracle A 的正确性」变体需泛等性（funext，不在本库公理集）或
--       trace-passing——同 OracleClasses 立界 (ii)，本件不闭合。
-- (ii)  变长查询：本件沿用定长查询槽（OracleClasses 立界 (i)）；OC-BGS₁ /
--       OC-BGS₂ 的非平凡化需固定-oracle 语义 + 查询长度成为计算内部量
--       （变长查询），即 OracleClasses 立界 (i)(ii)，本件不闭合。
-- (iii) oc-P⊆NP 已闭合 P^A ⊆ NP^A 方向；ocxs-npa⊆pa 给出逆向；本保守设计下
--       二者同时退化——npa⊆pa 单独（不需 aInP）已足以给出 P = NP，
--       ocxs-aInP / ocxs-mn-mono 仅为辅路线（oc-collapse 消除）所消费。
-- (iv)  OC-BGS₁ / OC-BGS₂ 的构造（PSPACE-complete / 对角化 oracle）= 世界件
--       status = 0；本件定理给出其陈述强度的下界刻画：任何见证
--       OCX-BGS₁-Strong 的构造即闭合 P = NP。
-- (v)   decider / verifier 的 OTM 实现桥——同 PClass §6(i)。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
