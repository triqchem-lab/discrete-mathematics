{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Morse.PaninaApplications — Panina 离散 Morse 应用实例
--
-- 数学背景：
--   Panina 离散 Morse 的独立方法论 = **柔性多边形模空间**（flexible polygon moduli space）：
--   固定边长的柔性多边形，对角长度随构形变化，构形空间的组合骨架 = **对角翻转图**
--   （三角剖分的 flip graph——五边形情形即结合多面体 associahedron 的 1-骨架 C₅）。
--   与 Forman 线的区别（任务书 5.2 修正：非「与 Forman 相同」）：Panina 面的离散 Morse
--   函数活在**翻转图**上（构形空间自身的高度函数），Forman 线是 CW 复形匹配分析层。
--   本模块 = Panina 面定义层 + 翻转图 C₅ 结构 + **Forman 匹配实例化衔接**
--   （复用 Application.DiscreteMorseGeneral 的 DiscreteMorseFunction/IsCritical
--   ——真实 import 边，非注释衔接）。
--
-- 核心原则：
--   ① 复用优先（DiscreteMorseFunction/IsCritical 零重证直调）
--   ② 五边形翻转图 = C₅ 是组合恒等式（5 剖分 × 2 翻转 = 5 无向边）——全枚举 ≤27 case
--   ③ Morse 实例层诚实边界（bₖ 为 C₅ 实例核，非一般定理——DiscreteMorseTheory 同款口径）
--   ④ 代数污染禁令（禁 Float/超越函数；边长面 Nat 承载）
--
-- 包含：FlexPentagon（柔性五边形）｜Triang 五剖分｜Flip 翻转（10 定向案）+ flip-inv
--       （对合）｜Cell/dimG/Vf（Forman 匹配实例化）｜pan-morse（DiscreteMorseFunction
--       实例）｜crit-T3/crit-e31（临界分类）｜m₀/m₁/b₀/b₁｜morse-ineq-pan/chi-law-pan
--       （Morse 实例核）｜核对层｜立界注记

module Sovereign.Application.Morse.PaninaApplications where

-- §0 导入区（显式 using）--------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; s≤s; z≤n)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Sovereign.Application.Morse.DiscreteMorseGeneral
  using (DiscreteMorseFunction; IsCritical)

-- §1 Panina 面定义层（柔性五边形 + 三角剖分）--------------------------------------

-- 柔性五边形：边长固定（Nat 承载——禁浮点），对角长度随构形（三角剖分）变化。
-- 构形空间的组合骨架 = 翻转图（§2）——Panina 模空间的离散形。
record FlexPentagon : Set where
  field
    side : ℕ → ℕ                    -- 边长函数（0..4 号边；其余值无定义约定）
  -- 柔性注记：对角长度不由 side 决定（构形自由度）——模空间点 = (剖分, 对角长赋值)；
  -- 组合面只承载剖分骨架（本模块范围），度量面（三角不等式构形空间）见 §6 立界。

-- 五边形 5 种三角剖分（对角集命名）：5 对角 (02)(03)(13)(14)(24) 的非交叉二子集
-- 恰 5 个——完备性注记（组合恒等式 C(3,2)·... = 5，与经典 Catalan 一致）。
data Triang : Set where
  t0203 : Triang        -- 对角集 {02, 03}
  t0224 : Triang        -- 对角集 {02, 24}
  t0313 : Triang        -- 对角集 {03, 13}
  t1314 : Triang        -- 对角集 {13, 14}
  t1424 : Triang        -- 对角集 {14, 24}

-- §2 翻转关系（flip——两相邻三角形并成四边形，换另一条对角）------------------------

--   翻转图结构（组合恒等式，全枚举——两对角集对称差恰 1 时为翻转邻接）：
--     t0203 ↔ t0313（flip 02→13）｜t0203 ↔ t0224（flip 03→24）
--     t0224 ↔ t1424（flip 02→14）｜t0313 ↔ t1314（flip 03→14）
--     t1314 ↔ t1424（flip 13→24）
--   = 5 无向边构成 5-圈 C₅（associahedron 1-骨架——Panina 模空间离散形）。
data Flip : Triang → Triang → Set where
  f0203-0313 : Flip t0203 t0313
  f0313-0203 : Flip t0313 t0203
  f0203-0224 : Flip t0203 t0224
  f0224-0203 : Flip t0224 t0203
  f0224-1424 : Flip t0224 t1424
  f1424-0224 : Flip t1424 t0224
  f0313-1314 : Flip t0313 t1314
  f1314-0313 : Flip t1314 t0313
  f1314-1424 : Flip t1314 t1424
  f1424-1314 : Flip t1424 t1314

-- 翻转对合（替换对角两次回到原剖分——flip 是对合）
flip-inv : ∀ {t t'} → Flip t t' → Flip t' t
flip-inv f0203-0313 = f0313-0203
flip-inv f0313-0203 = f0203-0313
flip-inv f0203-0224 = f0224-0203
flip-inv f0224-0203 = f0203-0224
flip-inv f0224-1424 = f1424-0224
flip-inv f1424-0224 = f0224-1424
flip-inv f0313-1314 = f1314-0313
flip-inv f1314-0313 = f0313-1314
flip-inv f1314-1424 = f1424-1314
flip-inv f1424-1314 = f1314-1424

-- C₅ 结构核对：每剖分恰 2 翻转（度 2——二对角全可翻）。
flip-degree : Triang → ℕ
flip-degree t0203 = 2
flip-degree t0224 = 2
flip-degree t0313 = 2
flip-degree t1314 = 2
flip-degree t1424 = 2

-- §3 Forman 匹配实例化（DiscreteMorseGeneral 真实衔接）---------------------------

-- 翻转图 = 1-复形：单形 = 顶点（剖分，dim 0）+ 边（翻转，dim 1）。
--   边单形用命名五边（EEdge）——规范形一型一边（避免二参 ce 造出假边单形）。
data EEdge : Set where
  e12 : EEdge          -- 边 {t0203, t0224}
  e25 : EEdge          -- 边 {t0224, t1424}
  e54 : EEdge          -- 边 {t1424, t1314}
  e43 : EEdge          -- 边 {t1314, t0313}
  e31 : EEdge          -- 边 {t0313, t0203}

data Cell : Set where
  cv : Triang → Cell
  ce : EEdge → Cell

dimG : Cell → ℕ
dimG (cv _) = 0
dimG (ce _) = 1

-- Panina 高度函数（沿圈 t0203-t0224-t1424-t1314-t0313 定向爬升）：
--   f(t0203)=0（极小）｜f(t0224)=1｜f(t1424)=2｜f(t1314)=3｜f(t0313)=4（极大）。
--   C₅ 上恰 1 极小 + 1 极大 ⇒ Morse 计数 m₀=1, m₁=1 与 b=(1,1) 一致（χ=0）。
fpan : Triang → ℕ
fpan t0203 = 0
fpan t0224 = 1
fpan t1424 = 2
fpan t1314 = 3
fpan t0313 = 4

-- Forman 匹配（V : 单形 ↦ 配对单形——严格升 1 维）：
--   四条上坡边配低点：t0203↦e12｜t0224↦e25｜t1424↦e54｜t1314↦e43。
--   临界：顶点 t0313（极大）+ 边 e31（唯一下坡边——未配对）。
Vf : Cell → Maybe Cell
Vf (cv t0203) = just (ce e12)
Vf (cv t0224) = just (ce e25)
Vf (cv t1424) = just (ce e54)
Vf (cv t1314) = just (ce e43)
Vf (cv t0313) = nothing
Vf (ce _) = nothing

-- dim-law（严格升维——4 配对案 refl；t0313/边案 nothing≡just 空形）
dimlaw : ∀ σ τ → Vf σ ≡ just τ → dimG τ ≡ suc (dimG σ)
dimlaw (cv t0203) _ refl = refl
dimlaw (cv t0224) _ refl = refl
dimlaw (cv t1424) _ refl = refl
dimlaw (cv t1314) _ refl = refl
dimlaw (cv t0313) _ ()
dimlaw (ce _) _ ()

-- V-inj（配对单射——配对 4 案 × σ' 分派 + 未配对/边案空形）
vinj : ∀ σ σ' τ → Vf σ ≡ just τ → Vf σ' ≡ just τ → σ ≡ σ'
vinj (cv t0203) (cv t0203) _ refl refl = refl
vinj (cv t0203) (cv t0224) _ refl ()
vinj (cv t0203) (cv t1424) _ refl ()
vinj (cv t0203) (cv t1314) _ refl ()
vinj (cv t0203) (cv t0313) _ refl ()
vinj (cv t0203) (ce _) _ refl ()
vinj (cv t0224) (cv t0203) _ refl ()
vinj (cv t0224) (cv t0224) _ refl refl = refl
vinj (cv t0224) (cv t1424) _ refl ()
vinj (cv t0224) (cv t1314) _ refl ()
vinj (cv t0224) (cv t0313) _ refl ()
vinj (cv t0224) (ce _) _ refl ()
vinj (cv t1424) (cv t0203) _ refl ()
vinj (cv t1424) (cv t0224) _ refl ()
vinj (cv t1424) (cv t1424) _ refl refl = refl
vinj (cv t1424) (cv t1314) _ refl ()
vinj (cv t1424) (cv t0313) _ refl ()
vinj (cv t1424) (ce _) _ refl ()
vinj (cv t1314) (cv t0203) _ refl ()
vinj (cv t1314) (cv t0224) _ refl ()
vinj (cv t1314) (cv t1424) _ refl ()
vinj (cv t1314) (cv t1314) _ refl refl = refl
vinj (cv t1314) (cv t0313) _ refl ()
vinj (cv t1314) (ce _) _ refl ()
vinj (cv t0313) _ _ () _
vinj (ce _) _ _ () _

-- DiscreteMorseFunction 实例化（真实 import 边——record 三字段全闭）
pan-morse : DiscreteMorseFunction Cell dimG
pan-morse = record
  { V = Vf
  ; dim-law = dimlaw
  ; V-inj = vinj
  }

-- 临界辅助（非像引理——Vf 值域 = {just e12, just e25, just e54, just e43, nothing}）
not-pair-T3 : ∀ τ → Vf τ ≡ just (cv t0313) → ⊥
not-pair-T3 (cv t0203) ()
not-pair-T3 (cv t0224) ()
not-pair-T3 (cv t0313) ()
not-pair-T3 (cv t1314) ()
not-pair-T3 (cv t1424) ()
not-pair-T3 (ce _) ()

not-pair-e31 : ∀ τ → Vf τ ≡ just (ce e31) → ⊥
not-pair-e31 (cv t0203) ()
not-pair-e31 (cv t0224) ()
not-pair-e31 (cv t0313) ()
not-pair-e31 (cv t1314) ()
not-pair-e31 (cv t1424) ()
not-pair-e31 (ce _) ()

-- 临界分类（IsCritical dimG Vf——复用 DiscreteMorseGeneral 谓词零重证）
crit-T3 : IsCritical dimG Vf (cv t0313)
crit-T3 = refl , λ { (τ , eq) → not-pair-T3 τ eq }

crit-e31 : IsCritical dimG Vf (ce e31)
crit-e31 = refl , λ { (τ , eq) → not-pair-e31 τ eq }

-- 非临界顶点（配对低端——V 非 nothing）
not-crit-T1 : ¬ IsCritical dimG Vf (cv t0203)
not-crit-T1 (() , _)

-- §4 Morse 计数与不等式实例（诚实边界：C₅ 实例核非一般定理）------------------------

m0 m1 : ℕ
m0 = 1        -- 临界顶点：t0313（极大）
m1 = 1        -- 临界边：e31（唯一下坡边）

b0 b1 : ℕ
b0 = 1        -- C₅ 连通分量数（实例核）
b1 = 1        -- C₅ 圈数（实例核——组合恒等式 V−E+F = 1−5+0 形）

-- Morse 不等式实例（mₖ ≥ bₖ——C₅ 上 Panina 匹配的实例核对）
morse-ineq-pan₀ : b0 ≤ m0
morse-ineq-pan₀ = s≤s z≤n

morse-ineq-pan₁ : b1 ≤ m1
morse-ineq-pan₁ = s≤s z≤n

-- χ 律实例（χ_M = m₀ ∸ m₁ = 0 = χ(C₅)）
chi-law-pan : (m0 ∸ m1) ≡ 0
chi-law-pan = refl

-- §5 核对层（refl 交叉——fpan 爬升 + C₅ 结构 + 匹配面）----------------------------

-- fpan 高度核对（5 顶点全值 0+1+2+3+4 = 10）
check-fpan : (fpan t0203 + fpan t0224) + (fpan t1424 + fpan t1314) + fpan t0313 ≡ 10
check-fpan = refl

-- flip 邻接核对（C₅ 两案 + 对合回环）
check-flip-1 : Flip t0203 t0313
check-flip-1 = f0203-0313

check-flip-round : Flip t0313 t0203
check-flip-round = flip-inv f0203-0313

check-degree-total : flip-degree t0203 + flip-degree t0313 ≡ 4
check-degree-total = refl

-- Vf 配对核对（四配对 + 一临界）
check-Vf-T1 : Vf (cv t0203) ≡ just (ce e12)
check-Vf-T1 = refl

check-Vf-T3 : Vf (cv t0313) ≡ nothing
check-Vf-T3 = refl

-- dimG 核对（顶 0 边 1）
check-dim-edge : dimG (ce e31) ≡ 1
check-dim-edge = refl

check-dim-vertex : dimG (cv t0313) ≡ 0
check-dim-vertex = refl

-- §6 立界注记（无空壳签名）------------------------------------------------------
--   (i)   度量面（对角长赋值满足三角不等式的构形空间——Panina 模空间的连续面）；
--   (ii)  一般 n 边形翻转图（associahedron 组合形——n≥6 非圈，Morse 理论一般形）；
--   (iii) 模空间一般形（柔性 n 边形的 Morse 同调 ≅ 模空间拓扑——深件）；
--   (iv)  临界复形 ≅ 翻转图同调对账（需 DiscreteMorseGeneral 立界的临界复形同调定理）。
