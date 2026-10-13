{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5k
-- A1b 施工批·阶段1（原子①②）：Ω4Step/Ω4Walk/Ω4ᵈ 定义层 + π₃ᵈ 商面 + rec₃ᵈ/elim₃ᵈ
--
-- 数学背景：Ω⁴+ 机件（高阶环路迭代 4 阶）——A1b 设计报告（18ae71e）签名草案落地。
--   n 阶迭代模式（_PPI5d:54-57）在 4 阶的展开：指标层 +1 的对偶复制。
--   逆=symm3 内置/复合=trans3（3-腔层面自带——比 2→3 阶少两件机件）；
--   Ω4Walk 是 data 非商型（无 uip 面——_PPI4o 立界不涉）。
--
-- 核心原则：
--   1. 逐字对偶：fill-tet 对偶 fill-tri（trans3 h (symm3 h) vs cons2 s (cons2 (invAStep s) ...)）；
--   2. 复用零重证：Ω2Walk/Ω3Step/Ω3Walk/Ω3ᵈ 全件直引（_PPI5d/_PPI5f）；
--   3. 注释导航、回执权威（内容审核纪律——本件每件由编译计算承载）；
--   4. 商型（HIT)as pattern discipline：π₃ᵈ = Ω3ᵈ / Ω4Walk（SetQuotients rec/elim）。
--
-- 包含：Ω4Step（fill-tet）｜Ω4Walk（refl4/symm4/trans4/gen4）｜Ω4ᵈ｜R4｜π₃ᵈ
--       ｜rec₃ᵈ/elim₃ᵈ｜最小实例核对 ×3｜阶段期边界（原子③④⑥留阶段2）
-- 策略：泛型 data 归纳＋SetQuotient rec/elim 范式（_PPI5j 同款）｜来源：A1b 报告+人类批准第一波

module _PPI5k where

open import Cubical.Foundations.Prelude using (_≡_; refl; isProp; isSet)
open import Cubical.HITs.SetQuotients using (_/_; [_]; rec; elimProp)
open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; Walk; nil)
open import _PPI5d using (Ω2Walk; nil2; cons2; s2-adj; s2v0)
open import _PPI5f using (Ω3Step; fill-tri; Ω3Walk; refl3; symm3; trans3; gen3; Ω3ᵈ)

-- ────────────────────────────────────────────────────────────────────
-- §1 Ω4Step（单构造子 fill-tet——fill-tri 逐字对偶，指标层 +1）
-- ────────────────────────────────────────────────────────────────────
-- 「往返 3-腔可 4-填充」：h : c → c' 的 3-走，其往返 trans3 h (symm3 h)
--   与基点自 3-走 refl3 c 在 Ω4 面等值。

data Ω4Step (G : DiGraph) (x : DiGraph.V G)
  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
  → Ω3Walk G x c c' → Ω3Walk G x c c' → Set where
  fill-tet : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
    (h : Ω3Walk G x c c') → Ω4Step G x (trans3 h (symm3 h)) (refl3 c)

-- ────────────────────────────────────────────────────────────────────
-- §2 Ω4Walk（等价闭包四律——Ω3Walk 同款模板）与 Ω4ᵈ
-- ────────────────────────────────────────────────────────────────────

data Ω4Walk (G : DiGraph) (x : DiGraph.V G)
  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
  → Ω3Walk G x c c' → Ω3Walk G x c c' → Set where
  refl4  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
    (k : Ω3Walk G x c c') → Ω4Walk G x k k
  symm4  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
    {k k' : Ω3Walk G x c c'} → Ω4Walk G x k k' → Ω4Walk G x k' k
  trans4 : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
    {k k' k'' : Ω3Walk G x c c'} → Ω4Walk G x k k' → Ω4Walk G x k' k'' → Ω4Walk G x k k''
  gen4   : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
    {k k' : Ω3Walk G x c c'} → Ω4Step G x k k' → Ω4Walk G x k k'

-- Ω4ᵈ：基点 3-走（refl3 (nil2 (nil x))) 处的 4-走圈
Ω4ᵈ : (G : DiGraph) → DiGraph.V G → Set
Ω4ᵈ G x = Ω4Walk G x {w1 = nil x} {w2 = nil x} (refl3 (nil2 (nil x))) (refl3 (nil2 (nil x)))

-- 设置：Ω3ᵈ 上的 Ω4 关系（π₃ᵈ 的商关基础——两律容器）
R4 : ∀ (G : DiGraph) (x : DiGraph.V G) → Ω3ᵈ G x → Ω3ᵈ G x → Set
R4 G x k k' = Ω4Walk G x {w1 = nil x} {w2 = nil x} k k'

-- ────────────────────────────────────────────────────────────────────
-- §3 π₃ᵈ 商面 + rec₃ᵈ/elim₃ᵈ（SetQuotient 复用——_PPI5j 范式）
-- ────────────────────────────────────────────────────────────────────

π₃ᵈ : (G : DiGraph) → DiGraph.V G → Set
π₃ᵈ G x = (Ω3ᵈ G x) / R4 G x

rec₃ᵈ : {G : DiGraph} {x : DiGraph.V G} (B : Set) (st : isSet B)
        (g : Ω3ᵈ G x → B)
        (resp : (a b : Ω3ᵈ G x) → R4 G x a b → g a ≡ g b)
      → π₃ᵈ G x → B
rec₃ᵈ B st g resp = rec st g resp

elim₃ᵈ : {G : DiGraph} {x : DiGraph.V G} {P : π₃ᵈ G x → Set}
        (pr : (q : π₃ᵈ G x) → isProp (P q)) (f : (k : Ω3ᵈ G x) → P [ k ])
      → (q : π₃ᵈ G x) → P q
elim₃ᵈ pr f = elimProp pr f

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层（最小实例 ×3——任意图可成立，零 AStep 依赖）
-- ────────────────────────────────────────────────────────────────────

-- ① Ω4ᵈ 最小元（refl4 封底——任意图）
chk4-nil : (G : DiGraph) (x : DiGraph.V G) → Ω4ᵈ G x
chk4-nil G x = refl4 (refl3 (nil2 (nil x)))

-- ② 具象 fill-tet 实例（Gskel/两链无关——任意图上：h 取基点自 3-走）
c0 : Ω2Walk s2-adj s2v0 (nil s2v0) (nil s2v0)
c0 = nil2 (nil s2v0)

chk-tet : Ω4Step s2-adj s2v0
          {w1 = nil s2v0} {w2 = nil s2v0} {c = c0} {c' = c0}
          (trans3 (refl3 c0) (symm3 (refl3 c0))) (refl3 c0)
chk-tet = fill-tet (refl3 c0)

-- ③ π₃ᵈ 基点最小商元
chk-p3-nil : π₃ᵈ s2-adj s2v0
chk-p3-nil = [ refl3 (nil2 (nil s2v0)) ]

-- ────────────────────────────────────────────────────────────────────
-- 阶段期边界（诚实——原子③④⑥留阶段2：
--   ③ Gskel 4阶实例需 Gskel two-chain 载入（_PPI4 面接）
--   ④ S²ᵈ 4阶 fund2 对账需 Ω3Walk-at-w3 面（_PDH5 fund2 衔接）
--   ⑥ whisk-swap 需 add2⁺/addL⁺/addR⁺ 运算面（_PPI5j:139-141）
-- 逆=symm3 内置/复合=trans3 的「少两件机件」设计由 §1-2 本身兑现（无新逆/复合构造子）
-- )

-- ════════════════════════════════════════════════════════════════════
-- §5 续段（阶段 2）：原子③④⑥——追加式（阶段 1 回执 36283007 零触碰）
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────────────────────
-- §5.0 续段导入区（追加——显式 using）
-- ────────────────────────────────────────────────────────────────────

open import Sovereign.Synthesis.McCordPi0 using (two-chain; ⊑₂-01; _⊑₂_)
open import _PPI4
open import _PPI4d using (w2)
open import Data.Fin using (Fin; zero; suc)

-- ────────────────────────────────────────────────────────────────────
-- §5a 原子③ Gskel 4 阶实例
-- ────────────────────────────────────────────────────────────────────

Gk : DiGraph
Gk = Gskel two-chain

Gk-x : DiGraph.V Gk
Gk-x = zero

-- Gskel 4 阶对象②：基点 3-走圈的 4-走（存在面——nil4 推论面）
Gskel4 : Set
Gskel4 = Ω4ᵈ Gk Gk-x

-- Gskel 4 阶非空（refl4 封底——4 阶圈至少含单位 3-腔）
gskel4-nonempty : Ω4ᵈ Gk Gk-x
gskel4-nonempty = refl4 (refl3 (nil2 (nil Gk-x)))

-- Gskel 3-圈基点对象（4-走圈的载体侧——对应 _PPI4b 的 w0 形闭走）
w0g : Walk Gk Gk-x Gk-x
w0g = nil Gk-x

nil2g : Ω2Walk Gk Gk-x w0g w0g
nil2g = nil2 w0g

refl3g : Ω3Walk Gk Gk-x nil2g nil2g
refl3g = refl3 nil2g

-- 4 阶面在 Gskel 上可定义（R4 有类型——Gskel 4 阶内点）
Gskel4-elt : Set
Gskel4-elt = Ω4ᵈ Gk Gk-x

-- ────────────────────────────────────────────────────────────────────
-- §5b 原子④ S²ᵈ 4 阶 fund2 对账（face-面 vs walk-阶形态分化——立界）
-- ────────────────────────────────────────────────────────────────────

-- S²ᵈ 的 4-阶面（形式侧）：基点 3-走圈的 4-走（与 _PDH5 的 face 面异形态）
S2-Omega4 : Set
S2-Omega4 = Ω4ᵈ s2-adj s2v0

-- S²ᵈ 4-阶非空（同 Gskel4 案——任意图）——重命名后文引用统一用 s2-Omega4-nz

-- 形态分化立界：
--   _PDH5.fund2-cycle 是 **face 面** 项（Face2→Trit 上的 2-闭链），不属 Ω4Walk
--   数据族（walk 阶形态）。两者非直接 exchangeable——接桥需 Ω3Walk-面复叠，
--   属 A1b 报告立界清单第 iii 条（boundary 注记如实）。

-- ────────────────────────────────────────────────────────────────────
-- §5c 原子⑥ whisk-swap（前后缘饰交换——A1c 前件）
-- ────────────────────────────────────────────────────────────────────

open import _PPI5j using (addL⁺; addR⁺; add2⁺; π₂ᵈ⁺)

-- whisk-swap（原子⑥）= **证明任务转派** A1c-1/2 批（e8547974 重派/主会话）——
--   本件不落签名：addL⁺/addR⁺ 俱 rec 商映射，等式两侧递归异路径（refl 不可达），
--   真证词需 whiskΩ3 缘饰引理装配（A1c 报告 §4 排程）——本节零内容（立界注记面）。
