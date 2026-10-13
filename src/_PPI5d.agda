{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI5d
-- πₙ-B4：Ωⁿ 迭代循环空间的组合形 + S²ᵈ 最小例 + n=1 一致性核对（锚点第四验）。
--
-- 数学背景：设计文档 docs/plan/pi-n-design.md 选项 1（导出刻画）——πₙᵈ(X,x) ≈ π₀(Ωⁿᵈ X)，
-- 其中 Ωᵈ = 闭走空间（Loop 形）、π₀ = 按同伦商。Ω¹ᵈ 恰为既有 Loop；Ω²ᵈ = AStep 图上的
-- 闭走（2-腔 = AStep 链）；迭代模式 = 每阶换「载体 + 步关系」再取 RWalk。
-- n=1 一致性锚点：π₀(Ω¹ᵈ) 与 π₁ᵈ = Loop/AHomotopy **定义相等**（恒等映射双向 + 往返 refl）。
--
-- 核心原则：
-- 1. 组合形即终形（不碰 ℝⁿ——连续统红线）；
-- 2. Ω¹ᵈ := Loop（零新件，定义相等承载一致性）；Ω²ᵈ := AStep 链（关系入定义 B2 正解②同族）；
-- 3. 刻画定理（πₙ ≃ π₀(Ωⁿ) 一般 n）签名级立界，n=1 案由恒等桥证成；
-- 4. 零洞零 postulate；∓ 链 ≤3；免匹配纪律（K 安全）；显式钉参（#52 族）。
--
-- 包含：Ω1ᵈ/Ω2Walk/Ω2ᵈ（定义层）｜S²ᵈ 组合形（s2-adj = K4 骨架）+ 面三角滑动实例
--       ｜π₀-Ω1 恒等桥四件（n=1 锚点第四验）｜刻画定理立界注记

module _PPI5d where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong)
open import Cubical.HITs.SetQuotients using (_/_; [_])
open import Relation.Binary.PropositionalEquality using ()
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; Walk; nil; cons; _++w_; AStep; slide; expand; AHomotopy)
open import _PPI using (Loop)
open import _PPI2 using (π₁ᵈ)
open import _PPI5 using (s1-adj; s1-loop)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：Ωⁿ 定义层（组合形——迭代循环空间）
-- ────────────────────────────────────────────────────────────────────

-- Ω¹ᵈ：基点闭走空间（= Loop G x——定义相等，零新件；n=1 一致性的定义层根源）
Ω1ᵈ : (G : DiGraph) → DiGraph.V G → Set
Ω1ᵈ G x = Loop G x

-- Ω²Walk：AStep 图上的走（2-腔 = AStep 链——同伦 2-胞腔的组合形；
-- 关系入定义：2-步生成元 = AStep（与 AHomotopy 的 gen 案同源数据））
data Ω2Walk (G : DiGraph) (x : DiGraph.V G) : Walk G x x → Walk G x x → Set where
  nil2  : ∀ (w : Walk G x x) → Ω2Walk G x w w
  cons2 : ∀ {w1 w2 w3 : Walk G x x} → AStep G w1 w2 → Ω2Walk G x w2 w3 → Ω2Walk G x w1 w3

-- Ω²ᵈ：常值闭走处的闭 2-走（基点 = nil x）。
-- 注：nil 是 AStep 孤立点（两沿皆 ≥1 边——_PPI2 ⑥ inv-law-false 同根），
-- 故 Ω²ᵈ 在常值基点处近平凡；非平凡 2-腔活在**非恒定闭走**处（见 §4 S²ᵈ 实例）。
Ω2ᵈ : (G : DiGraph) → DiGraph.V G → Set
Ω2ᵈ G x = Ω2Walk G x (nil x) (nil x)

-- 迭代模式（Ωⁿ 一般形——注记级，索引族泛化立界）：
--   Ω^{k+1}ᵈ = 在「k 阶数据 + (k+1)-阶步关系」上的闭走；
--   具体：Ω¹ᵈ = Walk(V,edge)(x,x)；Ω²ᵈ = Walk(Walk,AStep)(nil,nil)；
--        Ω³ᵈ = Walk(Ω2Walk,Ω3Step)(nil2,nil2)…… 每阶载体 = 上阶闭走、步关系 = 上阶同伦生成元。

-- ────────────────────────────────────────────────────────────────────
-- ④ 主引理层：S²ᵈ 最小例（∂Δ³ 组合球面 + Ω¹/Ω² 结构）
-- ────────────────────────────────────────────────────────────────────

-- S²ᵈ = ∂Δ³（四面体边界）：顶点 Fin 4，1-骨架 = K4（无向全图的双向边形）。
-- 四个面三角：(0,1,2) (0,1,3) (0,2,3) (1,2,3)——面三角恰是 AStep slide 的载体。
s2v0 s2v1 s2v2 s2v3 : Fin 4
s2v0 = fzero
s2v1 = fsuc fzero
s2v2 = fsuc (fsuc fzero)
s2v3 = fsuc (fsuc (fsuc fzero))

data S2edge : Fin 4 → Fin 4 → Set where
  s01 : S2edge s2v0 s2v1
  s10 : S2edge s2v1 s2v0
  s02 : S2edge s2v0 s2v2
  s20 : S2edge s2v2 s2v0
  s03 : S2edge s2v0 s2v3
  s30 : S2edge s2v3 s2v0
  s12 : S2edge s2v1 s2v2
  s21 : S2edge s2v2 s2v1
  s13 : S2edge s2v1 s2v3
  s31 : S2edge s2v3 s2v1
  s23 : S2edge s2v2 s2v3
  s32 : S2edge s2v3 s2v2

-- S²ᵈ 的 1-骨架图（K4 双向）
s2-adj : DiGraph
s2-adj = record { V = Fin 4 ; edge = S2edge }

-- Ω¹ 结构（s2v0 处）：三角面圈 w3（3 边）与双折返 w'（2 边）
w3 : Walk s2-adj s2v0 s2v0
w3 = cons s01 (cons s12 (cons s20 (nil s2v0)))

w' : Walk s2-adj s2v0 s2v0
w' = cons s02 (cons s20 (nil s2v0))

-- 形状核对（refl 级——构造形钉死）
chk-w3-shape : w3 ≡ cons s01 (cons s12 (cons s20 (nil s2v0)))
chk-w3-shape = refl

chk-w'-shape : w' ≡ cons s02 (cons s20 (nil s2v0))
chk-w'-shape = refl

-- 面三角 (s2v0,s2v1,s2v2) 上的 slide/expand（AStep 生成元——2-腔本体）
face012-slide : AStep s2-adj w3 w'
face012-slide = slide (nil s2v0) (cons s20 (nil s2v0)) s01 s12 s02

face012-expand : AStep s2-adj w' w3
face012-expand = expand (nil s2v0) (cons s20 (nil s2v0)) s01 s12 s02

-- Ω² 最小见证：w3 处的闭 2-走（slide ∘ expand = 闭合 2-腔——三角面的「填充」数据形）
omega2-wit : Ω2Walk s2-adj s2v0 w3 w3
omega2-wit = cons2 face012-slide (cons2 face012-expand (nil2 w3))

-- 第二面核对：面 (s2v0,s2v1,s2v3) 同构形（对称面族一致性）
w3b : Walk s2-adj s2v0 s2v0
w3b = cons s01 (cons s13 (cons s30 (nil s2v0)))

face013-slide : AStep s2-adj w3b (cons s03 (cons s30 (nil s2v0)))
face013-slide = slide (nil s2v0) (cons s30 (nil s2v0)) s01 s13 s03

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 组合层：π₀-Ω1 恒等桥（n=1 一致性锚点第四验）
-- ────────────────────────────────────────────────────────────────────

-- π₀(Ω¹ᵈ)：闭走按 A-同伦商
π0-Ω1 : (G : DiGraph) → DiGraph.V G → Set
π0-Ω1 G x = Ω1ᵈ G x / AHomotopy G

-- 恒等双向（定义相等承载——Ω1ᵈ := Loop，π₁ᵈ := Loop/AHomotopy）
π0ω1-to : ∀ (G : DiGraph) (x : DiGraph.V G) → π0-Ω1 G x → π₁ᵈ G x
π0ω1-to G x z = z

π0ω1-from : ∀ (G : DiGraph) (x : DiGraph.V G) → π₁ᵈ G x → π0-Ω1 G x
π0ω1-from G x z = z

-- 往返恒等（refl 级——定义相等即证明）
chk-π0ω1-r1 : ∀ (G : DiGraph) (x : DiGraph.V G) (z : π0-Ω1 G x) → π0ω1-from G x (π0ω1-to G x z) ≡ z
chk-π0ω1-r1 G x z = refl

chk-π0ω1-r2 : ∀ (G : DiGraph) (x : DiGraph.V G) (z : π₁ᵈ G x) → π0ω1-to G x (π0ω1-from G x z) ≡ z
chk-π0ω1-r2 G x z = refl

-- 商构造子级核对（S¹ᵈ 锚点实例：s1-loop 的两侧对齐）
chk-π0ω1-s1 : π0ω1-to s1-adj fzero [ s1-loop ] ≡ [ s1-loop ]
chk-π0ω1-s1 = refl

chk-π0ω1-s1' : π0ω1-from s1-adj fzero [ s1-loop ] ≡ [ s1-loop ]
chk-π0ω1-s1' = refl

-- 锚点第四验主件：n=1 时 Ω¹ 刻画与 π₁ᵈ/商型桥对齐（恒等同构四件全 refl 级）
-- 一致性核对结论：π₀(Ω¹ᵈ) ≅ π₁ᵈ（恒等——定义层同物）。

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 核对层 + 立界注记
-- ────────────────────────────────────────────────────────────────────

-- S¹ᵈ 锚点：s1-loop ∈ Ω¹ᵈ（Ω¹ 载体与 Loop 同物的具体见证）
chk-ω1-s1 : Ω1ᵈ s1-adj fzero
chk-ω1-s1 = s1-loop

-- S²ᵈ 锚点：w3/w' ∈ Ω¹ᵈ（S²ᵈ 的 Ω¹ 结构非平凡——含三角 slide 关系）
chk-ω1-s2 : Ω1ᵈ s2-adj s2v0
chk-ω1-s2 = w3

chk-Ω2-s2 : Ω2Walk s2-adj s2v0 w3 w'
chk-Ω2-s2 = cons2 face012-slide (nil2 w')

-- 立界（精确剩余——B4 未证面，不硬拱）：
-- (i) 刻画定理一般 n：πₙᵈ(Sⁿᵈ,x) ≃ π₀(Ωⁿᵈ X)——n=1 案已证（上方恒等桥）；
--     n≥2 需 Ω³ 填充理论（3-腔 = Ω2Walk 之间的 Ω3Walk）+ π₀ 商型，估 1-2 批。
-- (ii) π₀-Ω2 定形：Ω2Walk /（3-填充）——填充关系 = Ω3Walk，定义层可循迭代模式，商型估 1 批。
-- (iii) S²ᵈ 完整 Ω¹ 分类：w3 族（4 面三角圈）+ 双折返族 + 长圈——按 _PPI4g 计数范式推广，估 1 批。
-- (iv) Ωⁿ 一般形索引族泛化（注记级模式 → 可编译族），估 ~40-60 行。
