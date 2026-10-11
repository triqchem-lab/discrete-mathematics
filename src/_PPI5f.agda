{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI5f
-- πₙ 刻画定理 n≥2 首批：Ω³ 填充理论（3-腔组合形）+ S²ᵈ 的 Ω² 分类最小件 + n=2 刻画骨架。
--
-- 数学背景：设计文档 docs/plan/pi-n-design.md 选项 1（导出刻画）迭代模式——
--   Ω³ᵈ = Walk(Ω2Walk, Ω3Step)(nil2,nil2)：3-腔 = 2-腔之间的同伦生成元链。
-- 本批把 _PPI5d ⑥ 立界件 (i)(ii) 的定义层落地：Ω3Step = 面填充同伦（fill-tri：三角面的
-- slide∘expand 闭合 2-腔 3-可缩）+ Ω3Walk = 其等价闭包（AHomotopy 三律构造子形）。
-- S²ᵈ 分类最小件：omega2-wit（B4 的 Ω² 见证）在 π₂ 商面**平凡**——[omega2-wit] ≡ [nil2 w3]
-- （三角面填充恰是 3-腔本体，故 2-腔见证 3-可缩）。
--
-- 核心原则：
-- 1. 组合形即终形（不碰 ℝⁿ）；迭代模式注记 → 可编译形（Ω3Step/Ω3Walk 落地）；
-- 2. Ω3Walk = 三律构造子形（refl/symm/trans + gen——AHomotopy 范式复制）；
-- 3. π₂ᵈ := π₀(Ω²ᵈ)（选项 1 刻画承载——与 π₁ᵈ := Loop/AHomotopy 同款定义层手法）；
-- 4. 零洞零 postulate；∓ 链 ≤3；免匹配纪律（K 安全）；显式钉参（#52 族）。
--
-- 包含：invAStep｜Ω3Step（fill-tri）｜Ω3Walk（三律+gen）｜Ω3ᵈ｜S²ᵈ Ω² 分类最小件
--       （omega2-wit-triv/witb-triv）｜π₂ᵈ 定义层 + 商面核对｜卡点清单（立界）

module _PPI5f where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil; cons; AStep; slide; expand; AHomotopy)
open import _PPI5d using (Ω2Walk; nil2; cons2; Ω2ᵈ; s2-adj; s2v0; w3; w3b; omega2-wit; face012-slide; face012-expand; face013-slide; s01; s13; s03; s30)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：Ω³ 填充理论（3-腔组合形——迭代模式的具体化）
-- ────────────────────────────────────────────────────────────────────

-- AStep 的逆向生成元（slide ↔ expand 互逆——同一三角数据对）
invAStep : {G : DiGraph} {u v : DiGraph.V G} {w1 w2 : Walk G u v} → AStep G w1 w2 → AStep G w2 w1
invAStep (slide p b e1 e2 e3) = expand p b e1 e2 e3
invAStep (expand p b e1 e2 e3) = slide p b e1 e2 e3

-- Ω3Step：2-腔之间的 3-步生成元（填充同伦）。
-- fill-tri：三角面填充——2-腔「s ∘ s⁻¹」（先滑后展）3-可缩至平凡 2-腔 nil2。
-- 这是 3-腔的本体数据：三角面的「填充」正是 2-圈的 3-消去。
data Ω3Step (G : DiGraph) (x : DiGraph.V G) : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  fill-tri : {w1 w2 : Walk G x x} (s : AStep G w1 w2) →
             Ω3Step G x (cons2 s (cons2 (invAStep s) (nil2 w1))) (nil2 w1)

-- Ω3Walk：3-腔 = Ω3Step 的等价闭包（AHomotopy 三律构造子形逐字复制——B2 正解②同族）
data Ω3Walk (G : DiGraph) (x : DiGraph.V G) : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  refl3  : {w1 w2 : Walk G x x} (c : Ω2Walk G x w1 w2) → Ω3Walk G x c c
  symm3  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} → Ω3Walk G x c c' → Ω3Walk G x c' c
  trans3 : {w1 w2 : Walk G x x} {c1 c2 c3 : Ω2Walk G x w1 w2} → Ω3Walk G x c1 c2 → Ω3Walk G x c2 c3 → Ω3Walk G x c1 c3
  gen3   : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} → Ω3Step G x c c' → Ω3Walk G x c c'

-- Ω³ᵈ：常值基点处的闭 3-走（迭代模式 Ω^{k+1} = 上阶闭走为载体 + 上阶同伦生成元为步关系）
Ω3ᵈ : (G : DiGraph) → DiGraph.V G → Set
Ω3ᵈ G x = Ω3Walk G x (nil2 (nil x)) (nil2 (nil x))

-- ────────────────────────────────────────────────────────────────────
-- ④ 主引理层：S²ᵈ 的 Ω² 分类最小件（omega2-wit 邻域）
-- ────────────────────────────────────────────────────────────────────

-- 面 (0,1,2) 侧：omega2-wit = cons2 slide (cons2 expand (nil2 w3)) 恰为 fill-tri 形
-- ⇒ 3-可缩至平凡 2-腔（三角面填充 = 3-腔本体）
omega2-wit-triv : Ω3Walk s2-adj s2v0 omega2-wit (nil2 w3)
omega2-wit-triv = gen3 (fill-tri face012-slide)

-- 面 (0,1,3) 侧对称件：w3b 的闭 2-腔同样 3-可缩
omega2-witb : Ω2Walk s2-adj s2v0 w3b w3b
omega2-witb = cons2 face013-slide (cons2 (invAStep face013-slide) (nil2 w3b))

omega2-witb-triv : Ω3Walk s2-adj s2v0 omega2-witb (nil2 w3b)
omega2-witb-triv = gen3 (fill-tri face013-slide)

-- invAStep 归约核对（def-eq 通道钉死——invAStep face013-slide 展形）
chk-inv-step : invAStep face013-slide ≡ expand (nil s2v0) (cons s30 (nil s2v0)) s01 s13 s03
chk-inv-step = refl

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 组合层：π₂ᵈ 定义层（选项 1 刻画承载）+ 商面核对
-- ────────────────────────────────────────────────────────────────────

-- π₀(Ω²ᵈ)：某基走处的闭 2-腔按 3-腔商（Ω3Walk = 填充同伦等价闭包）
π0-Ω2-at : (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) → Set
π0-Ω2-at G x w = Ω2Walk G x w w / (λ c c' → Ω3Walk G x c c')

-- π₂ᵈ：选项 1 导出刻画（与 π₁ᵈ := Loop/AHomotopy 同款定义层手法）
π₂ᵈ : (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) → Set
π₂ᵈ G x w = π0-Ω2-at G x w

-- S²ᵈ 商面核对：omega2-wit 在 π₂ 商面**平凡**（三角面填充 = 3-腔 ⇒ 2-圈 3-可缩）
chk-π2-wit-triv : _≡_ {A = π0-Ω2-at s2-adj s2v0 w3} [ omega2-wit ] [ nil2 w3 ]
chk-π2-wit-triv = eq/ omega2-wit (nil2 w3) (gen3 (fill-tri face012-slide))

chk-π2-witb-triv : _≡_ {A = π0-Ω2-at s2-adj s2v0 w3b} [ omega2-witb ] [ nil2 w3b ]
chk-π2-witb-triv = eq/ omega2-witb (nil2 w3b) (gen3 (fill-tri face013-slide))

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 核对层 + 卡点清单（立界注记）
-- ────────────────────────────────────────────────────────────────────

-- Ω³ᵈ 最小核对（常值处 3-腔的平凡元）
chk-Ω3-nil : Ω3ᵈ s2-adj s2v0
chk-Ω3-nil = refl3 (nil2 (nil s2v0))

-- 三律核对（Ω3Walk 闭包自洽——symm3/trans3 复合形）
chk-Ω3-round : Ω3Walk s2-adj s2v0 omega2-wit omega2-wit
chk-Ω3-round = trans3 omega2-wit-triv (symm3 omega2-wit-triv)

-- 卡点清单（n=2 刻画定理全形的精确剩余——不硬拱）：
-- (i) Ω3Walk 的等价关系完备形：fill-tri 之外的 3-步生成元（whisker 缘饰：
--     同侧加 AStep 的 Ω3Step cong 形、边界消去边界形）——2-腔等价的完备生成集待补
--     （当前 gen3 只有面填充一型——S²ᵈ 分类最小件已够，一般图完备性立界）；
-- (ii) 商型良定义：π0-Ω2-at 上的 rec/elim 面（Ω3Walk 需 EqRel 包装——symm3/trans3 已具，
--     refl3 供 refl——EqRel record 装配 ~10 行，随 (i) 一批）；
-- (iii) 「π₂ᵈ 定义 = 经典同伦类定义」对齐定理：需 3-填充完备性（whisker+边界消去
--     生成集下 Ω3Walk 恰为 2-腔同伦类）——1-2 批（设计文档 B4 立界件 (i) 的定理面）；
-- (iv) S²ᵈ 完整 Ω¹ 分类（w3 族/双折返族/长圈）——_PPI4g 计数范式推广，1 批（B4 立界件 (iii)）。
