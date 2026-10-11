{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5i ——「π₂ᵈ 定义 = 经典同伦类」对齐定理（_PPI5f 立界件 (iii)）
--
-- 数学背景：π₂ 有两个经典定义——(A) 迭代循环空间 π₀(Ω²X)（Whitehead 形）；
--   (B) 基点映射类 [S², X]_*。本件在离散组合形下建立两定义的**对齐**：
--   侧 A = π₂ᵈ := π0-Ω2-at（_PPI5f，选项 1 刻画）；侧 B = 基点映射类商 BMapQ
--   （_PPI5c，选项 2 形）。对齐的构造性内容 = **k₂ 平凡化 ⟹ 商面类平凡**定理
--   （3-腔填充见证即商面等式见证——eq/ 承载），S²ᵈ 全形两侧一致。
-- 核心原则：
-- 1. 组合形即终形（不碰 K(G,n)/ℝⁿ）；「经典同伦类」取本地可用形（映射类选项 2）；
-- 2. 对齐的构造性方向先证（k2-zero→class-triv）；逆向（类平凡 ⟹ 填充见证存在）
--   需商面有效化——构造性边界，如实立界；
-- 3. 诚实标注：侧 B 的顶点映射形是映射类的**离散影**（复形映射形需 Simplex 装配
--   ——B2 立界件），常值映射非保边故 eval 面立界；
-- 包含：k2-zero→class-triv（对齐主定理·构造向）｜S²ᵈ 全形对齐核对（双面+一致形）
--       ｜侧 B 映射类陈述层（S2MapQ/cst-map/平凡类代表）｜一般形立界注记

module _PPI5i where

open import Data.Nat using (ℕ)

open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)
open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _≡ᴱ_; refl to reflᴱ)

open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; AStep; AHomotopy)
open import _PPI5 using (BasedMap; DHomotopy)
open import _PPI5c using (BMHom; BMapQ; bmQ)
open import _PPI5d
  using (Ω2Walk; nil2; cons2; s2-adj; s2v0; w3; w3b; omega2-wit)
open import _PPI5f
  using (Ω3Step; Ω3Walk; refl3; gen3; fill-tri; π0-Ω2-at; π₂ᵈ;
         omega2-wit-triv; omega2-witb-triv; chk-π2-wit-triv; chk-π2-witb-triv)

-- ────────────────────────────────────────────────────────────────────
-- ① 基础件层：k₂ 平凡化谓词（PT-4 语义注记的可构造形）
-- ────────────────────────────────────────────────────────────────────

-- k₂=0 的构造性语义：2-腔 c 被 3-腔填充至平凡 2-腔（nil2 w）
-- （经典：k₂ 代表为上同调类，平凡类 ⟺ 代表被 3-腔填充——PT-4 语义注记对齐）
-- 具体形：c 在 w 处 3-可缩
k2-triv-at : (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x)
           → Ω2Walk G x w w → Set
k2-triv-at G x w c = Ω3Walk G x c (nil2 w)

-- ────────────────────────────────────────────────────────────────────
-- ② 主引理层：对齐主定理（构造向——k₂ 平凡化 ⟹ 商面类平凡）
-- ────────────────────────────────────────────────────────────────────

-- 对齐主定理（构造向）：3-腔填充见证 ⟹ π₂ 商面等式见证
-- 「定义=经典同伦类」的构造性内容：k₂ 的平凡化数据恰是商面类的平凡化证明
k2-zero→class-triv :
    (w : Walk s2-adj s2v0 s2v0) (c : Ω2Walk s2-adj s2v0 w w)
  → k2-triv-at s2-adj s2v0 w c
  → _≡_ {A = π0-Ω2-at s2-adj s2v0 w} ([ c ]) ([ nil2 w ])
k2-zero→class-triv w c h = eq/ c (nil2 w) h

-- 逆向（陈述形——构造性边界立界）：类平凡 ⟹ 存在填充见证
-- 需商面有效化（SetQuotient 无计算截面）——经典逻辑下成立，构造性下为选择型
-- 立界注记：若改用「2-腔显式配对商」（带见证的呈现）可得双向——随 (i)(ii) 一批

-- ────────────────────────────────────────────────────────────────────
-- ③ S²ᵈ 全形对齐核对（双面 + 一致形）
-- ────────────────────────────────────────────────────────────────────

-- 面 (0,1,2) 侧：omega2-wit 的 k₂ 平凡化 → 商面类平凡（主定理调用）
align-wit-012 :
    _≡_ {A = π0-Ω2-at s2-adj s2v0 w3} ([ _PPI5d.omega2-wit ]) ([ nil2 w3 ])
align-wit-012 = k2-zero→class-triv w3 _PPI5d.omega2-wit _PPI5f.omega2-wit-triv

-- 一致形核对：主定理路径与 _PPI5f 直证路径**定义相等**（同一证明项）
-- （chk-π2-wit-triv = eq/ omega2-wit (nil2 w3) (gen3 (fill-tri face012-slide))
--   而 omega2-wit-triv 恰为该 3-腔——两路径 defeq 同一）
align-agree-012 : align-wit-012 ≡ chk-π2-wit-triv
align-agree-012 = refl

-- 面 (0,1,3) 侧：witb 同款
align-wit-013 :
    _≡_ {A = π0-Ω2-at s2-adj s2v0 w3b} ([ _PPI5f.omega2-witb ]) ([ nil2 w3b ])
align-wit-013 = k2-zero→class-triv w3b _PPI5f.omega2-witb _PPI5f.omega2-witb-triv

align-agree-013 : align-wit-013 ≡ chk-π2-witb-triv
align-agree-013 = refl

-- S²ᵈ 全形判定：两侧（012/013）对齐齐备 + 一致形 refl 级
-- ⇒ 「π₂ᵈ 商面读法」与「k₂ 平凡化读法」在 S²ᵈ 上完全一致

-- ────────────────────────────────────────────────────────────────────
-- ④ 侧 B 映射类陈述层（选项 2 形——离散影）
-- ────────────────────────────────────────────────────────────────────

-- S²ᵈ 顶点基点映射类（选项 2 本地可用形）
S2MapQ : Set
S2MapQ = BMapQ s2v0 (DiGraph.V s2-adj) s2v0

-- 平凡映射类的常值代表（顶点层）
cst-map : BasedMap (DiGraph.V s2-adj) s2v0 (DiGraph.V s2-adj) s2v0
cst-map = record { to = λ _ → s2v0 ; to-base = reflᴱ }

-- 平凡类代表：bmQ cst-map : S2MapQ
-- ⚠ 诚实边界：①顶点映射形是映射类的离散影（复形映射形需 Simplex 装配——B2 立界件）；
--   ②常值映射非保边（s2-adj 无自环处）——映射类→π₂ᵈ 的 eval 面需保边前提
--   （GraphMap/edge-p record 形立界 ~40 行）；③类等式侧 A↔侧 B 的桥 =
--   「对齐定理」全形（方向二/3-塌缩完备性——_PPI5h Dir2 同族立界）

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 核对层
-- ────────────────────────────────────────────────────────────────────

-- 常值 2-腔的 k₂ 平凡形（nil2 自填——refl3 承载）
k2-triv-nil : k2-triv-at s2-adj s2v0 w3 (nil2 w3)
k2-triv-nil = refl3 (nil2 w3)

-- 主定理于平凡元退化核对：[nil2 w3] ≡ [nil2 w3]（自反形——gen 不触发）
align-nil : _≡_ {A = π0-Ω2-at s2-adj s2v0 w3} ([ nil2 w3 ]) ([ nil2 w3 ])
align-nil = k2-zero→class-triv w3 (nil2 w3) (refl3 (nil2 w3))

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 立界注记（一般形精确剩余——不硬拱）
-- ────────────────────────────────────────────────────────────────────
-- (a) 逆向（类平凡 ⟹ 填充见证）：商面有效化——构造性边界；
-- (b) 侧 A↔侧 B 桥全形：eval（保边映射 → 2-腔推前）+ lift（2-腔 → 映射重构）
--     ——需 GraphMap/edge-p（~40 行）+ Simplex 装配（B2 立界件）；
-- (c) 方向二/3-塌缩完备性（_PPI5h Dir2 同族）；
-- (d) 一般图 X 上的对齐（S²ᵈ 之外——需 Ω3Walk 生成集完备形，_PPI5f (i) 立界件）。
