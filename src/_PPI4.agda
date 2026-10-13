{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4 —— (d) π₁ 对接 statement 修正（定稿 + 骨架）
--
-- 数学背景：P2.2c 的 (d) 件 =「π₁ᵈ(|K(X)|) ≅ π₁ᵈ(X)」的对接同构。b2-群分水岭实录反噬本句：
-- walk 反向落 Gᵒᵖ、无 flip 的有向图上 π₁ᵈ 仅成幺半群 ⇒ 原句「群同构」的「群」字没有承载。
-- 决策 6：statement 先修正，倾向 B（加对称图前提、群同构形）。本文件 = 陈述定稿 + 骨架（零洞零 postulate）。
--
-- 二选一实证对比（定稿依据）：
--   A' 弱形 MonoidIso（无条件）：两侧永远是幺半群（⊞ᵈ 三律已在 _PPI2 全形）——退化面可证，
--      但弱于 McCord「群同构」叙述，且丢掉「逆元存在性 = 对称图判据」这条已实证的本体论信息；
--   B' 强形 GroupIso + flip 前提：对称图条件下两侧升群（invᵈ 需 flip）——与经典叙述对齐；
--      且本句的 poset 对（Gskel/Gcmp）由构造自对称（flip 可证，见 §1）⇒ **前提代价为零而强度对齐**。
--   ⇒ 定稿 **B'**；A' 作为无向一般图退化面同文保留（弱形类型一并落码，供后续降级陈述复用）。
--
-- 核心原则：
-- 1. 只落陈述与骨架——待证件全部立界注记（零洞零 postulate 红线）
-- 2. MonoidIso/GroupIso 按 presentation 最小性判据三自检（见 §2 record 注）
-- 3. 相等取 Cubical _≡_（π₁ᵈ = 商型，其等式即商上路径——与 _PPI2 同世界，防双 _≡_ 世界缺桥）
-- 4. 自环分离是结构性必要（cmpEdge 含反身自环、KEdge 不含——P2.2b x≢y 分离同源）——见 §4 附⑤
--
-- 包含：§1 图对构造（Gskel 对称形 / Gcmp）+ flip 自带性；§2 最小同构 record（三自检）；
--       §3 陈述定稿（弱形 A' / 强形 B'）；§4 骨架（两向 map 设计 + 待证四件清单 + 自环收缩附⑤）
module _PPI4 where

open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong)
open import Cubical.HITs.SetQuotients using ([_])
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.McCordCore using (cmpEdge)
open import Sovereign.Synthesis._PMc2 using (KEdge)
open import Sovereign.Synthesis.BarceloAHomotopy
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; invᵈ)

--------------------------------------------------------------------------------
-- §1 图对构造（行 1-骨架对称形 / 可比图）+ flip 自带性
--------------------------------------------------------------------------------

-- 1-骨架的有向化（对称形：正序 ⊎ 反序——正是 skel-iff 的右端形 `IsChain2 x y ⊎ IsChain2 y x`）
Gskel : ∀ {n} (P : FinitePoset n) → DiGraph
Gskel P = record { V = Fin _ ; edge = λ x y → KEdge P x y ⊎ KEdge P y x }

-- 可比图（McCordCore 的 cmpEdge = x⊑y ⊎ y⊑x——自带对称性）
Gcmp : ∀ {n} (P : FinitePoset n) → DiGraph
Gcmp P = record { V = Fin _ ; edge = cmpEdge P }

-- 对称性前提（B' 的显式条件——一般有向图无此件即掉到幺半群，b2-群分水岭）
Flip : (G : DiGraph) → Set
Flip G = ∀ {u v} → DiGraph.edge G u v → DiGraph.edge G v u

-- 本句 poset 对由构造自对称（B' 前提代价为零的实证——两 flip 均为定义级可证）
Gskel-flip : ∀ {n} (P : FinitePoset n) → Flip (Gskel P)
Gskel-flip P (inj₁ e) = inj₂ e
Gskel-flip P (inj₂ e) = inj₁ e

Gcmp-flip : ∀ {n} (P : FinitePoset n) → Flip (Gcmp P)
Gcmp-flip P (inj₁ e) = inj₂ e
Gcmp-flip P (inj₂ e) = inj₁ e

--------------------------------------------------------------------------------
-- §2 最小同构 record（presentation 最小性判据三自检）
--   自检一问：每字段是 ①presentation 关系 / ②结构公理 / ③可导出性质？
--   ① 无——本 record 载「同构数据」，非展示关系（与 B3 的 relations 字段不同类）；
--   ② to-·/to-e/from-·/from-e = 同态结构公理（合法，同 UniversalAlgebra.Group 口径）；
--      to∘from/from∘to = 同构的定义部件（往返恒等）；
--   ③ 不入字段的可导出件：to 单射/满射（由往返导出）、from-· 余律一致性、逆唯一性、
--      GroupIso 的 from-inv（由 to-inv + 往返导出）——全部降定理，零新公理。
--------------------------------------------------------------------------------

record MonoidIso (A B : Set)
       (_·A_ : A → A → A) (eA : A)
       (_·B_ : B → B → B) (eB : B) : Set where
  field
    to      : A → B
    from    : B → A
    to-·    : ∀ x y → to (x ·A y) ≡ to x ·B to y
    to-e    : to eA ≡ eB
    from-·  : ∀ x y → from (x ·B y) ≡ from x ·A from y
    from-e  : from eB ≡ eA
    to∘from : ∀ y → to (from y) ≡ y
    from∘to : ∀ x → from (to x) ≡ x

record GroupIso (A B : Set)
       (_·A_ : A → A → A) (eA : A) (invA : A → A)
       (_·B_ : B → B → B) (eB : B) (invB : B → B) : Set where
  field
    mono   : MonoidIso A B _·A_ eA _·B_ eB
    to-inv : ∀ x → MonoidIso.to mono (invA x) ≡ invB (MonoidIso.to mono x)

--------------------------------------------------------------------------------
-- §3 陈述定稿（未来态锁定：锚定「两 π₁ᵈ 的同构形」为 RHS，反推所需数据）
--------------------------------------------------------------------------------

-- §3.1 弱形 A'（无条件——退化面定稿保留，供无向一般图陈述复用）
π₁对接-弱形 : ∀ {n} (P : FinitePoset n) (x : Fin n) → Set
π₁对接-弱形 P x =
  MonoidIso (π₁ᵈ (Gskel P) x) (π₁ᵈ (Gcmp P) x)
            (_⊞ᵈ_ {G = Gskel P}) [ nil x ]
            (_⊞ᵈ_ {G = Gcmp P})  [ nil x ]

-- §3.2 强形 B'（**定稿**——对称图前提 + 群同构形；flip 由 §1 实例满足）
π₁对接-强形 : ∀ {n} (P : FinitePoset n) (x : Fin n) → Set
π₁对接-强形 P x =
  GroupIso (π₁ᵈ (Gskel P) x) (π₁ᵈ (Gcmp P) x)
           (_⊞ᵈ_ {G = Gskel P}) [ nil x ] (invᵈ {G = Gskel P} (Gskel-flip P))
           (_⊞ᵈ_ {G = Gcmp P})  [ nil x ] (invᵈ {G = Gcmp P}  (Gcmp-flip P))

--------------------------------------------------------------------------------
-- §4 骨架（两向 map 设计 + 待证四件清单——立界注记，零洞零 postulate）
--------------------------------------------------------------------------------

-- §4.1 两向 map（类型形态；证明体待补——本文件不落洞）
--   to   : π₁ᵈ (Gskel P) x → π₁ᵈ (Gcmp P) x
--     落法：边级 toE : KEdge P u v ⊎ KEdge P v u → cmpEdge P u v
--            （inj₁ (h , _) ↦ inj₁ h；inj₂ (h , _) ↦ inj₂ h ——IsChain2 = ⊑ × x≢y 投影）
--          + walk 逐步提升（cons 保形，nil ↦ nil）+ resp（AHomotopy 合同——++w-resp/⊞-resp 范式）
--          + quot 提升（π₁ᵈ-rec squash/ —— _PPI2 既有形）
--   from : π₁ᵈ (Gcmp P) x → π₁ᵈ (Gskel P) x
--     落法：skel-iff（x≢y 情形）给逆向边译 fromE（cmpEdge ↔ KEdge ⊎ KEdge-flipped 取逆向）
--          + **自环收缩**（见附⑤：cmpEdge x x 非空而 KEdge x x 空——自环段 ↦ nil）
--          + walk 提升 + quot 提升（同形）
--
-- §4.2 待证四件清单（各需什么）
--   ① to-·（同态性）：翻译与 ++w 交换（AStep-concat-r/l 范式）+ ⊞ᵈ 经 ⊞-resp 提升
--      ——机械件，~20 行；全走 _PPI2 既有合同性族，零新引理
--   ② to∘from ∼ id：边往返（cmp→chain2→cmp 恒等，x≢y 分支）+ 自环收缩之逆（补回自环 ∼ nil）
--      ——核心件，~30-50 行；依赖附⑤
--   ③ from∘to ∼ id：对称件（skel-iff 逆向逐边 + 同上）——~30-50 行；依赖附⑤
--   ④ to-inv（B' 专）：rev 与翻译交换（flip 自然性：toE ∘ Gskel-flip ≡ Gcmp-flip ∘ toE，inj 交换即证）
--      + rev-resp 范式（_PPI2 既有四案）——~20 行
--
-- §4.3 附⑤：自环收缩引理（②③ 的公共依赖，~10-20 行）
--   陈述：cons e 段（e : cmpEdge P x x 自环）在 AHomotopy 下 ∼ 删段（expand 对消 or refl' 形）
--   根源：cmpEdge 含反身自环（⊑ 反身）而 KEdge 不含（x≢y 分离）——P2.2b 的 x≢y 必要分离同源；
--         这是**图对的固有差异**，不是证明技巧问题，故列为陈述层附带件而非隐藏在 map 里。
--
-- §4.4 工时与依赖汇总：①~④ + 附⑤ 合计 ~100-160 行，纯工时件（无本体论缺口、无新机件需求）——
--     b2-群 rev/rev-resp/⊞-resp 族与 P2.2b skel-iff 全部现成，路线无悬空。
