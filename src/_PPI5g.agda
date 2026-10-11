{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI5g —— Ω3Step 生成集完备形 + EqRel 装配
--
-- 数学背景：_PPI5f 立界件 (i)(ii) 转工时——Ω3Step 原仅 fill-tri（尾位气泡收缩）一型生成元，
-- S²ᵈ 最小件够用但一般图完备性立界。本件补全生成集：
--   ① whisk3（缘饰/同余——2-腔侧前缀提升）；
--   ② bub3（边界 2-圈收缩——任意位置「s ∘ s⁻¹」气泡消去，fill-tri 的一般形）；
--   ③ 完备形：BubbleMove（气泡移动关系）→ Ω3Walk⁺ 全证 + 经典对齐骨架（立界）；
--   ④ EqRel 装配：Ω3Walk 等价关系包装（EqRel3——供 π0-Ω2-at 的 rec/elim 面）。
--
-- 核心原则：
-- 1. 组合形即终形；生成元补全 = 陈述层完备化，零新公理；
-- 2. EqRel3 = 包装非公理（三律由 refl3/symm3/trans3 构造子承载）；
-- 3. 经典对齐定理（气泡移动生成一切 2-腔同伦）如实立界。
--
-- 包含：_++2_｜bub｜Ω3Step⁺（base3+/whisk3/bub3）｜Ω3Walk⁺｜embed3｜BubbleMove/bubble-complete
--       ｜EqRel3/ω3-equiv｜S²ᵈ 实例核对 ×4

module _PPI5g where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil; cons; AStep; slide; expand; AHomotopy)
open import _PPI5d using (Ω2Walk; nil2; cons2; Ω2ᵈ; s2-adj; s2v0; w3; w3b; omega2-wit; face012-slide; face012-expand; face013-slide)
open import _PPI5f using (invAStep; Ω3Step; fill-tri; Ω3Walk; refl3; symm3; trans3; gen3; π0-Ω2-at; π₂ᵈ)

-- ────────────────────────────────────────────────────────────────────
-- ① 基础件：2-腔拼接 + 气泡形
-- ────────────────────────────────────────────────────────────────────

infixl 20 _++2_

-- 2-腔拼接：Ω2Walk 是 AStep 图上的走——走拼接即 2-腔纵串
_++2_ : {G : DiGraph} {x : DiGraph.V G} {w1 w2 w3 : Walk G x x} →
        Ω2Walk G x w1 w2 → Ω2Walk G x w2 w3 → Ω2Walk G x w1 w3
nil2 _   ++2 c' = c'
cons2 s c ++2 c' = cons2 s (c ++2 c')

-- 气泡（s ∘ s⁻¹ 边界 2-圈）——本件核心组合形
bub : {G : DiGraph} {x : DiGraph.V G} {w w' : Walk G x x} (s : AStep G w w') → Ω2Walk G x w w
bub {G} {x} {w} s = cons2 s (cons2 (invAStep s) (nil2 w))

-- ────────────────────────────────────────────────────────────────────
-- ② 生成集完备形：Ω3Step⁺（fill-tri 嵌入 + 缘饰 + 任意位气泡消去）
-- ────────────────────────────────────────────────────────────────────

data Ω3Step⁺ (G : DiGraph) (x : DiGraph.V G) : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  base3+ : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} →
           Ω3Step G x c c' → Ω3Step⁺ G x c c'
  whisk3 : {w1 wm w2 : Walk G x x} (c₁ : Ω2Walk G x w1 wm) {c c' : Ω2Walk G x wm w2} →
           Ω3Step⁺ G x c c' → Ω3Step⁺ G x (c₁ ++2 c) (c₁ ++2 c')
  bub3   : {w1 wm w2 : Walk G x x} (c₁ : Ω2Walk G x w1 wm) {wm' : Walk G x x}
           (s : AStep G wm wm') (c₂ : Ω2Walk G x wm w2) →
           Ω3Step⁺ G x ((c₁ ++2 bub s) ++2 c₂) (c₁ ++2 c₂)

-- Ω3Walk⁺：扩展生成集的等价闭包（三律构造子形复制）
data Ω3Walk⁺ (G : DiGraph) (x : DiGraph.V G) : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  refl3+  : {w1 w2 : Walk G x x} (c : Ω2Walk G x w1 w2) → Ω3Walk⁺ G x c c
  symm3+  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} → Ω3Walk⁺ G x c c' → Ω3Walk⁺ G x c' c
  trans3+ : {w1 w2 : Walk G x x} {c1 c2 c3 : Ω2Walk G x w1 w2} →
            Ω3Walk⁺ G x c1 c2 → Ω3Walk⁺ G x c2 c3 → Ω3Walk⁺ G x c1 c3
  gen3+   : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} →
            Ω3Step⁺ G x c c' → Ω3Walk⁺ G x c c'

-- 嵌入保闭包：原 Ω3Walk 步入扩展闭包
embed3 : {G : DiGraph} {x : DiGraph.V G} {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} →
         Ω3Walk G x c c' → Ω3Walk⁺ G x c c'
embed3 (refl3 c) = refl3+ c
embed3 (symm3 p) = symm3+ (embed3 p)
embed3 (trans3 p q) = trans3+ (embed3 p) (embed3 q)
embed3 (gen3 s) = gen3+ (base3+ s)

-- ────────────────────────────────────────────────────────────────────
-- ③ 完备形：BubbleMove → Ω3Walk⁺（全证）+ 经典对齐骨架（立界）
-- ────────────────────────────────────────────────────────────────────

data BubbleMove (G : DiGraph) (x : DiGraph.V G) : {w : Walk G x x} → Ω2Walk G x w w → Ω2Walk G x w w → Set where
  id-bm   : {w : Walk G x x} (c : Ω2Walk G x w w) → BubbleMove G x c c
  mid-bm  : {w wm : Walk G x x} (c₁ : Ω2Walk G x w wm) {wm' : Walk G x x}
            (s : AStep G wm wm') (c₂ : Ω2Walk G x wm w) →
            BubbleMove G x ((c₁ ++2 bub s) ++2 c₂) (c₁ ++2 c₂)
  sym-bm  : {w : Walk G x x} {c c' : Ω2Walk G x w w} →
            BubbleMove G x c c' → BubbleMove G x c' c
  trans-bm : {w : Walk G x x} {c c' c'' : Ω2Walk G x w w} →
             BubbleMove G x c c' → BubbleMove G x c' c'' → BubbleMove G x c c''

-- 完备形主件（已证）：气泡移动序列 ⊆ 扩展生成集闭包
bubble-complete : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} {c c' : Ω2Walk G x w w} →
                  BubbleMove G x c c' → Ω3Walk⁺ G x c c'
bubble-complete (id-bm c) = refl3+ c
bubble-complete (mid-bm c₁ s c₂) = gen3+ (bub3 c₁ s c₂)
bubble-complete (sym-bm p) = symm3+ (bubble-complete p)
bubble-complete (trans-bm p q) = trans3+ (bubble-complete p) (bubble-complete q)

-- 经典对齐骨架（立界——_PPI5f (iii) 定理面）：
-- 「2-腔同伦类 = Ω3Walk⁺ 等价类」完全形需 (a) 非退化三角面边界收缩生成元（TriFill 见证形）；
-- (b) 反向包含。BubbleMove 已证侧 = 气泡序列完备性；「气泡移动生成一切 2-腔同伦」为
-- 经典事实的离散对应待证——如实立界。

-- ────────────────────────────────────────────────────────────────────
-- ④ EqRel 装配（Ω3Walk 等价关系包装——π0-Ω2-at 的 rec/elim 面）
-- ────────────────────────────────────────────────────────────────────

record EqRel3 (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) : Set where
  field
    refl-ω  : (c : Ω2Walk G x w w) → Ω3Walk G x c c
    symm-ω  : {c c' : Ω2Walk G x w w} → Ω3Walk G x c c' → Ω3Walk G x c' c
    trans-ω : {c c' c'' : Ω2Walk G x w w} → Ω3Walk G x c c' → Ω3Walk G x c' c'' → Ω3Walk G x c c''

-- 装配主件：三律由 refl3/symm3/trans3 承载——包装零新公理
ω3-equiv : (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) → EqRel3 G x w
ω3-equiv G x w = record { refl-ω = refl3 ; symm-ω = symm3 ; trans-ω = trans3 }

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 核对层（S²ᵈ 新生成元实例 ×4）
-- ────────────────────────────────────────────────────────────────────

-- EqRel 装配实例（w3 处）
chk-eqrel-w3 : EqRel3 s2-adj s2v0 w3
chk-eqrel-w3 = ω3-equiv s2-adj s2v0 w3

-- bub3 于 w3：任意位气泡消去恰回收 omega2-wit（defeq——nil2 ++2 _ 恒等）
chk-bub-wit : Ω3Step⁺ s2-adj s2v0 omega2-wit (nil2 w3)
chk-bub-wit = bub3 (nil2 w3) face012-slide (nil2 w3)

-- bubble-complete 于 w3：BubbleMove 路径 ↔ 扩展闭包
chk-bm-wit : Ω3Walk⁺ s2-adj s2v0 omega2-wit (nil2 w3)
chk-bm-wit = bubble-complete (mid-bm (nil2 w3) face012-slide (nil2 w3))

-- whisk3 缘饰实例：前缀侧提升（face013-slide 前缀下的气泡消去）
chk-whisk3-s2 : Ω3Step⁺ s2-adj s2v0 (bub face012-slide ++2 bub face012-slide) (bub face012-slide)
chk-whisk3-s2 = whisk3 (bub face012-slide) (bub3 (nil2 w3) face012-slide (nil2 w3))

-- embed3 保闭包核对：原 fill-tri 路径入扩展闭包
chk-embed-s2 : Ω3Walk⁺ s2-adj s2v0 omega2-wit (nil2 w3)
chk-embed-s2 = embed3 (gen3 (fill-tri face012-slide))
