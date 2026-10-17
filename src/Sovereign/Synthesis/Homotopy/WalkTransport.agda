{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.WalkTransport
--
-- 数学背景（桥件甲1 的**解墙基建**，路线 (i)：给 `Walk` 加沿顶点等式的传输原理）：
--   `Walk`（Sovereign.Synthesis.Homotopy.BarceloAHomotopy）的载体是「顶点链」，
--   其构造子 `nil v : Walk G v v` 只居留**对角型**（同一起点与终点）。
--   桥件甲1 的墙③（nil 传输墙）是：`nil a : Walk G a a` 沿顶点等式 `e : a ≡ v`
--   搬到 `Walk G v v` 上，在**定义层不是可构造的家项**——`subst` / `subst₂` / `cong`
--   三路实测皆 `UnequalTerms`。根因：传输（`transp`）在数据族上**不归约**为构造子，
--   故 `transport (λ i → Walk G (e i) (e i)) (nil a)` 是**卡住的项**，
--   它不是 `nil v`，也无法在定义层被识别为任何构造子。
--
--   本模块给 `Walk` 配「沿顶点等式的传输原理」：
--     ① 传输件（§1–§2）：用 cubical `transport`（= `transp` 的路径族形）把
--        `Walk G (e i) ·` / `Walk G (e i) (e i)` 一族沿 `e` 搬动；
--     ② 计算律（§3–§5）：用 `J` + `transportRefl` 把**传输结果与构造子形接上**——
--        即给出 `transport … (nil u) ≡ nil u'` 这类**等式**（墙③ 的破墙件）。
--   关键机制：`e` 是自由变量时传输卡住，但 `J` 允许我们把命题降到 `e = refl`；
--   在 `refl` 上传输退化为**常族传输**，由 `transportRefl` 收口为构造子形。
--
-- 核心原则：
--   1. 传输件用 cubical `transport`（**不是** `subst`——`subst` 形在数据族上卡在
--      「传输后的项不归约为构造子」，这正是墙③ 本身）；
--   2. 计算律一律 `J` + `transportRefl`（不引 K、不引 postulate；cubical 默认禁 K）；
--   3. 全部泛型：对任意 `DiGraph`、任意顶点等式成立，不依赖任何具体图；
--   4. 具体实例只作**对抗验证**（在定义层独立收口 + 引理在具体点实例化）。
--
-- 诚实边界（**必读**，不得把本基建说成万能）：
--   ① 本基建给的是**等式**（`… ≡ nil u'` 形），解决的是「**产出**一个 walk」的场合
--      （例如桥件 `bt-collapse` 的归纳步需要「把闭走搬到新端点并落回构造子形」）。
--      它**不**解决「**匹配**一个传输过的 walk」——即从一个 `Walk G v v` 的实参上
--      消去 `transport` 形、或对抽象点 `w : Walk G v v` 拆分构造子
--      （后者是墙① K 死墙：`SplitError.UnificationStuck`，与传输无关）。
--      消去方向属**另一族工作**（需 `transport-filler` 一族或 code/decode 形）。
--   ② 传输用的等式是 **cubical `Cubical.Foundations.Prelude._≡_`（Path 型）**——
--      形如 `transport (λ i → Walk G (e i) v) w` 要求 `e i` 可作用（`i : I`）。
--      若调用方的顶点等式是 stdlib 归纳型 `Relation.Binary.PropositionalEquality._≡_`，
--      本模块不能直接套用（那条路正是 `subst` 形的墙本身），须先换到路径族。
--   ③ 本模块**只读复用** `BarceloAHomotopy`（`DiGraph`/`Walk`/`nil`/`cons`/`_++w_`），
--      不改动被复用文件；也不在 `Walk` 上加任何新构造子。
--   ④ 「传输对拼接分配」（§5）只对 `_++w_` 成立；对一般二元运算不比这更强。
--
-- 包含：walk-transp-left/right/both（传输三件）· edge-transp（边传输）·
--   计算律 walk-transp-*-nil（含单侧非对角形与闭合形）· walk-transp-*-cons ·
--   walk-transp-both-++w · 具体点对抗验证 · 墙③ 破墙见证（二顶点商图上的 nil 搬运）

module Sovereign.Synthesis.Homotopy.WalkTransport where

open import Cubical.Foundations.Prelude using (_≡_; PathP; refl; sym; cong; cong₂; _∙_; transport; transportRefl; J)
open import Cubical.Data.Empty.Base using (⊥)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (DiGraph; Walk; nil; cons; _++w_)
open DiGraph using (V; edge)

-- ────────────────────────────────────────────────────────────────────
-- §1. 传输三件：沿顶点等式把 walk 搬到新端点
-- ────────────────────────────────────────────────────────────────────

-- 左端点传输：`e : u ≡ u'` 把 `Walk G u v` 搬到 `Walk G u' v`
walk-transp-left : ∀ {G : DiGraph} {u u' v} (e : u ≡ u') → Walk G u v → Walk G u' v
walk-transp-left {G = G} {v = v} e = transport (λ i → Walk G (e i) v)

-- 右端点传输：`e : v ≡ v'` 把 `Walk G u v` 搬到 `Walk G u v'`
walk-transp-right : ∀ {G : DiGraph} {u v v'} (e : v ≡ v') → Walk G u v → Walk G u v'
walk-transp-right {G = G} {u = u} e = transport (λ i → Walk G u (e i))

-- 双端传输（本件主角）：`e : u ≡ u'` 把 `Walk G u u` 搬到 `Walk G u' u'`
-- —— 正是「`nil a` 搬到 `Walk G v v`」所需的搬运形。
walk-transp-both : ∀ {G : DiGraph} {u u'} (e : u ≡ u') → Walk G u u → Walk G u' u'
walk-transp-both {G = G} e = transport (λ i → Walk G (e i) (e i))

-- ────────────────────────────────────────────────────────────────────
-- §2. 边传输：`edge` 是普通函数（类型线），同一机制照搬
-- ────────────────────────────────────────────────────────────────────

edge-transp : ∀ {G : DiGraph} {u u' v} (e : u ≡ u') → edge G u v → edge G u' v
edge-transp {G = G} {v = v} e = transport (λ i → edge G (e i) v)

-- 边传输的 refl 案（常族传输由 transportRefl 直接收口）
edge-transp-refl : ∀ {G : DiGraph} {u v} (ed : edge G u v) → edge-transp {G = G} refl ed ≡ ed
edge-transp-refl ed = transportRefl ed

-- ────────────────────────────────────────────────────────────────────
-- §3. 计算律：nil 案（墙③ 的破墙件）
-- ────────────────────────────────────────────────────────────────────

-- ★ 双端 nil：`nil u` 沿 `e` 搬运后**是构造子** `nil u'`（破墙③ 的主件）
walk-transp-both-nil : ∀ {G : DiGraph} {u u'} (e : u ≡ u')
                     → walk-transp-both {G = G} {u = u} {u' = u'} e (nil u) ≡ nil u'
walk-transp-both-nil {G = G} {u = u} = J P d
  where
  P : ∀ u' → u ≡ u' → Set
  P u' e = walk-transp-both {G = G} {u = u} {u' = u'} e (nil u) ≡ nil u'

  d : P u refl
  d = transportRefl (nil u)

-- 单侧（左）nil：右端点**不动** ⇒ 值型是 `Walk G u' u`（**非对角**，`nil` 不居留此型——
-- 故单侧传输**单独**不能产出构造子）。可证的最强形：与「从另一端点回搬」相等。
walk-transp-left-nil : ∀ {G : DiGraph} {u u'} (e : u ≡ u')
                     → walk-transp-left {G = G} {v = u} e (nil u)
                     ≡ transport (λ i → Walk G u' ((sym e) i)) (nil u')
walk-transp-left-nil {G = G} {u = u} = J P d
  where
  P : ∀ u' → u ≡ u' → Set
  P u' e = walk-transp-left {G = G} {v = u} e (nil u)
         ≡ transport (λ i → Walk G u' ((sym e) i)) (nil u')

  d : P u refl
  d = refl

-- 单侧（左）nil 的**闭合形**：只搬一侧不够，把另一侧也搬上才回到构造子形。
-- 这是「单侧不产出构造子」的精确陈述（而非口号）。
walk-transp-left-nil-closed : ∀ {G : DiGraph} {u u'} (e : u ≡ u')
  → transport (λ i → Walk G u' (e i)) (walk-transp-left {G = G} {v = u} e (nil u)) ≡ nil u'
walk-transp-left-nil-closed {G = G} {u = u} = J P d
  where
  P : ∀ u' → u ≡ u' → Set
  P u' e = transport (λ i → Walk G u' (e i)) (walk-transp-left {G = G} {v = u} e (nil u))
         ≡ nil u'

  d : P u refl
  d = transportRefl (transport (λ _ → Walk G u u) (nil u)) ∙ transportRefl (nil u)

-- 单侧（右）nil：左端点**不动** ⇒ 值型是 `Walk G v v'`（**非对角**）
walk-transp-right-nil : ∀ {G : DiGraph} {v v'} (e : v ≡ v')
                      → walk-transp-right {G = G} {u = v} e (nil v)
                      ≡ transport (λ i → Walk G ((sym e) i) v') (nil v')
walk-transp-right-nil {G = G} {v = v} = J P d
  where
  P : ∀ v' → v ≡ v' → Set
  P v' e = walk-transp-right {G = G} {u = v} e (nil v)
         ≡ transport (λ i → Walk G ((sym e) i) v') (nil v')

  d : P v refl
  d = refl

-- 单侧（右）nil 的闭合形
walk-transp-right-nil-closed : ∀ {G : DiGraph} {v v'} (e : v ≡ v')
  → transport (λ i → Walk G (e i) v') (walk-transp-right {G = G} {u = v} e (nil v)) ≡ nil v'
walk-transp-right-nil-closed {G = G} {v = v} = J P d
  where
  P : ∀ v' → v ≡ v' → Set
  P v' e = transport (λ i → Walk G (e i) v') (walk-transp-right {G = G} {u = v} e (nil v))
         ≡ nil v'

  d : P v refl
  d = transportRefl (transport (λ _ → Walk G v v) (nil v)) ∙ transportRefl (nil v)

-- ────────────────────────────────────────────────────────────────────
-- §4. 计算律：cons 案（传输沿构造子分配——头边由 edge-transp 搬运，尾递归）
-- ────────────────────────────────────────────────────────────────────

-- 左传输对 `cons` 分配：头边搬到 `edge G u' v`，尾不变
walk-transp-left-cons : ∀ {G : DiGraph} {u u' v w} (e : u ≡ u')
                        (ed : edge G u v) (p : Walk G v w)
                      → walk-transp-left {G = G} {v = w} e (cons ed p)
                      ≡ cons (edge-transp {G = G} {v = v} e ed) p
walk-transp-left-cons {G = G} {u = u} {v = v} {w = w} = J P d
  where
  P : ∀ u' → u ≡ u' → Set
  P u' e = (ed : edge G u v) (p : Walk G v w)
         → walk-transp-left {G = G} {v = w} e (cons ed p)
         ≡ cons (edge-transp {G = G} {v = v} e ed) p

  d : P u refl
  d ed p = transportRefl (cons ed p) ∙ sym (cong (λ x → cons x p) (transportRefl ed))

-- 右传输对 `cons` 分配：头边不变，尾递归搬运
walk-transp-right-cons : ∀ {G : DiGraph} {u v w w'} (e : w ≡ w')
                         (ed : edge G u v) (p : Walk G v w)
                       → walk-transp-right {G = G} {u = u} e (cons ed p)
                       ≡ cons ed (walk-transp-right {G = G} {u = v} e p)
walk-transp-right-cons {G = G} {u = u} {v = v} {w = w} = J P d
  where
  P : ∀ w' → w ≡ w' → Set
  P w' e = (ed : edge G u v) (p : Walk G v w)
         → walk-transp-right {G = G} {u = u} e (cons ed p)
         ≡ cons ed (walk-transp-right {G = G} {u = v} e p)

  d : P w refl
  d ed p = transportRefl (cons ed p) ∙ sym (cong (cons ed) (transportRefl p))

-- ────────────────────────────────────────────────────────────────────
-- §5. 与 `_++w_` 的相容性：双端传输对拼接分配
--     （`p : u → v`、`q : v → u`；两段各自沿对应一侧搬运）
-- ────────────────────────────────────────────────────────────────────

walk-transp-both-++w : ∀ {G : DiGraph} {u u' v} (e : u ≡ u')
                       (p : Walk G u v) (q : Walk G v u)
                     → walk-transp-both {G = G} e (p ++w q)
                     ≡ walk-transp-left {G = G} {v = v} e p
                       ++w walk-transp-right {G = G} {u = v} e q
walk-transp-both-++w {G = G} {u = u} {v = v} = J P d
  where
  P : ∀ u' → u ≡ u' → Set
  P u' e = (p : Walk G u v) (q : Walk G v u)
         → walk-transp-both {G = G} {u = u} {u' = u'} e (p ++w q)
         ≡ walk-transp-left {G = G} {v = v} e p
           ++w walk-transp-right {G = G} {u = v} e q

  d : P u refl
  d p q = transportRefl (p ++w q)
        ∙ sym (cong₂ (λ a b → a ++w b) (transportRefl p) (transportRefl q))

-- ────────────────────────────────────────────────────────────────────
-- §6. 具体点对抗验证（定义层独立收口 + 引理在具体点实例化）
--     ——「只有具体实例与定理实例一致，才算闭合」
-- ────────────────────────────────────────────────────────────────────

-- 最简图：单点 + 自环（顶点型 ⊤，边型恒 ⊤）
G⊤ : DiGraph
G⊤ = record { V = ⊤ ; edge = λ _ _ → ⊤ }

-- 核对件 1（**定义层**，不经 §3 的 J 引理）：常族传输由 transportRefl 收口
check-both-nil-refl : walk-transp-both {G = G⊤} {u = tt} {u' = tt} refl (nil tt) ≡ nil tt
check-both-nil-refl = transportRefl (nil tt)

-- 核对件 2（**同一命题经 §3 引理**）：J 引理在具体点给出同一等式
check-both-nil-refl-via-J : walk-transp-both {G = G⊤} {u = tt} {u' = tt} refl (nil tt) ≡ nil tt
check-both-nil-refl-via-J = walk-transp-both-nil refl

-- 核对件 3（**定义层**）：边传输 refl 案
check-edge-transp-refl : edge-transp {G = G⊤} {u = tt} {v = tt} refl tt ≡ tt
check-edge-transp-refl = transportRefl tt

-- 核对件 4（cons 案的具体点实例化）
check-left-cons : walk-transp-left {G = G⊤} {v = tt} refl (cons tt (nil tt))
                ≡ cons (edge-transp {G = G⊤} {v = tt} refl tt) (nil tt)
check-left-cons = walk-transp-left-cons refl tt (nil tt)

-- 核对件 5（§5 相容件在具体点上的实例化）
check-both-++w : walk-transp-both {G = G⊤} refl (nil tt ++w nil tt)
               ≡ walk-transp-left {G = G⊤} {v = tt} refl (nil tt)
                 ++w walk-transp-right {G = G⊤} {u = tt} refl (nil tt)
check-both-++w = walk-transp-both-++w refl (nil tt) (nil tt)

-- ────────────────────────────────────────────────────────────────────
-- §7. 墙③ 破墙见证：二顶点商图（桥件甲1「trivial 2-vertex」的具体化）
--     目的：证明墙③ 在本基建下**不再是墙**——
--     两个**不同**顶点被一条顶点等式识别，`nil a` 被搬到 `Walk G v v`
--     并**得到构造子形** `nil v`。
-- ────────────────────────────────────────────────────────────────────

-- 二顶点：`Bool` 的两点；`R` 只把 `false` 与 `true` 识别（其余不识别）
data R : Bool → Bool → Set where
  r-ft : R false true

-- 顶点型 = 商（两个顶点被一条路径识别）
V2 : Set
V2 = Bool / R

-- 二顶点图：无边（最简图——`nil` 是唯一 walk），顶点两两由商路径相连
G2 : DiGraph
G2 = record { V = V2 ; edge = λ _ _ → ⊥ }

-- 顶点等式 `e : a ≡ v`（`a = [ false ]`、`v = [ true ]`）——**不是** refl（两端不同构造子）
e2 : PathP (λ _ → V2) [ false ] [ true ]
e2 = eq/ false true r-ft

-- 原始传输形：定义层**卡住**（不归约为任何构造子）——这就是墙③ 的物质形态。
-- 本行只是把 `walk-transp-both` 展开（definitional），用来点明卡住的项长什么样。
bt-nil-branch-raw : walk-transp-both {G = G2} e2 (nil [ false ])
                  ≡ transport (λ i → Walk G2 (e2 i) (e2 i)) (nil [ false ])
bt-nil-branch-raw = refl

-- ★ 破墙：把 `nil a` 沿顶点等式搬到 `Walk G2 v v` 并**得到构造子形** `nil v`
bt-nil-branch-witness : walk-transp-both {G = G2} e2 (nil [ false ]) ≡ nil [ true ]
bt-nil-branch-witness = walk-transp-both-nil e2
