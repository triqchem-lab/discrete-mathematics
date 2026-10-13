{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI（P2.2c 前置件设计 spike：几何实现骨架层 + πₙ≥1 机件）
--
-- 数学背景：P2.2c 主件 = McCord 弱等价 |K(X)| → X（∀πₙ 同构）——(a) 几何实现机件、
--   (b) πₙ≥1 机件为前置。本探针交：① 2-骨架**粘合数据形**（面沿边的粘合映射）+
--   2 点链最小实例（2 顶点 + 1 边 + 0 面）；② πₙ spike 最小可用形 = 离散 loop 空间
--   Ω(G,x) = 闭 walk + AHomotopy 等价（BarceloAHomotopy 现成件），π₁ 离散形 = spec 三律；
--   ③ P2.2c 主件精确剩余清单（文末）。设计 spike 允许「数据形 + 最小实例 + 剩余清单」。
--
-- 核心原则：
--   1. 复用优先：KVert/KEdge/KTri/tri-face-*（_PMc2）、Walk/AHomotopy/AH-*（BarceloAHomotopy）
--      、two-chain（McCordPi0）零重证；
--   2. presentation 最小性判据：粘合映射 ∂₂ 是**实现函子的面映射数据**（单形呈现的结构部分，
--      同 B3 relations 定位），非导出性质；其余可导出件（tri-face 投影）不入字段；
--   3. 不冒充几何实现：Sk2 承载是组合占位，真商拓扑在剩余清单 (a2)。
module _PPI where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂)
open import Relation.Nullary using (¬_)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Synthesis.McCordPi0 using (two-chain; _⊑₂_; ⊑₂-00; ⊑₂-01; ⊑₂-11)
open import Sovereign.Synthesis._PMc2
  using (KVert; KEdge; KTri; tri-face-xy; tri-face-yz; chain2-KEdge; an2-KEdge-absurd)
open import Sovereign.Topology.OrderComplex using (chain3-down)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep; slide; expand; AHomotopy; refl'; symm; trans'; gen;
         AH-refl; AH-symm; AH-trans)

--------------------------------------------------------------------------------
-- ① 几何实现骨架层：2-骨架粘合数据（面沿边的粘合映射）
--------------------------------------------------------------------------------

-- 面的边界三元组（面沿边粘合到 1-骨架的指令数据形——带顶点序：12/23/13 三边）
data FaceBoundary {n} (P : FinitePoset n) : {x y z : Fin n} → Set where
  bd : ∀ {x y z}
       (e12 : KEdge P x y) (e23 : KEdge P y z) (e13 : KEdge P x z)
     → FaceBoundary P {x} {y} {z}

-- 2-骨架粘合数据 record（设计 spike 数据形）
-- 自检（presentation 最小性）：① Sk2/ιv/ιf = 实现承载与包含（实现函子输入端数据）；
-- ② ∂₂ = 面映射（单形呈现的结构部分——B3 relations 同定位）；③ tri-face 投影类可导出件不入字段 ✓
record K2Gluing {n} (P : FinitePoset n) : Set₁ where
  field
    -- 实现承载（组合占位——真几何实现在剩余清单 (a2)）
    Sk2 : Set
    -- 顶点/面的包含（几何化：单形 → 粘合类）
    ιv  : KVert {n} → Sk2
    ιf  : ∀ {x y z} → KTri P x y z → Sk2
    -- 粘合映射：面 → 边界三元组（面沿 1-骨架三边粘合）
    ∂₂  : ∀ {x y z} (t : KTri P x y z) → FaceBoundary P {x} {y} {z}

--------------------------------------------------------------------------------
-- 2 点链最小实例（2 顶点 + 1 边 + 0 面）
--------------------------------------------------------------------------------

-- KTri two-chain 不可居留（0 面）——IsChain2 只在 (0,1) 存活，逐案归谬
chain2-00-absurd : KEdge two-chain fzero fzero → ⊥
chain2-00-absurd (_ , n) = n refl

chain2-10-absurd : KEdge two-chain (fsuc fzero) fzero → ⊥
chain2-10-absurd (() , _)

chain2-11-absurd : KEdge two-chain (fsuc fzero) (fsuc fzero) → ⊥
chain2-11-absurd (_ , n) = n refl

tri2-absurd : ∀ (x y z : Fin 2) → KTri two-chain x y z → ⊥
tri2-absurd fzero fzero _ (hxy , _) = chain2-00-absurd hxy
tri2-absurd (fsuc fzero) (fsuc fzero) _ (hxy , _) = chain2-11-absurd hxy
tri2-absurd (fsuc fzero) fzero _ (hxy , _) = chain2-10-absurd hxy
tri2-absurd fzero (fsuc fzero) fzero (_ , hyz) = chain2-10-absurd hyz
tri2-absurd fzero (fsuc fzero) (fsuc fzero) (_ , hyz) = chain2-11-absurd hyz

-- 2 点链的 2-骨架：Sk2 = Fin 2（两顶点），面映射空（0 面），边界映射空
skel2-two-chain : K2Gluing two-chain
skel2-two-chain = record
  { Sk2 = Fin 2
  ; ιv  = λ v → v
  ; ιf  = λ {x} {y} {z} t → ⊥-elim (tri2-absurd x y z t)
  ; ∂₂  = λ {x} {y} {z} t → ⊥-elim (tri2-absurd x y z t)
  }

-- 对账件：2 点链 2-骨架 = 2 顶点 + 1 边（chain2-KEdge 在 _PMc2 ✓）+ 0 面（tri2-absurd）
-- ——与 McCordPi0 的 two-chain Connected 判定一致。
check-edge : KEdge two-chain fzero (fsuc fzero)
check-edge = chain2-KEdge

--------------------------------------------------------------------------------
-- ② πₙ≥1 spike：离散 loop 空间 Ω + π₁ 离散形（Walk/AHomotopy 商型 spec）
--------------------------------------------------------------------------------

-- 离散 loop 空间：以 x 为基点的闭 walk
Loop : (G : DiGraph) → DiGraph.V G → Set
Loop G x = Walk G x x

-- π₁ 离散形 = Loop 模 A-homotopy 的商型（spec 三律——承载 = 等价类）
record π₁-Spec (G : DiGraph) (x : DiGraph.V G) : Set₁ where
  field
    _∼_     : Loop G x → Loop G x → Set
    ∼-refl  : ∀ ℓ → ℓ ∼ ℓ
    ∼-sym   : ∀ {ℓ m} → ℓ ∼ m → m ∼ ℓ
    ∼-trans : ∀ {ℓ m n} → ℓ ∼ m → m ∼ n → ℓ ∼ n

-- 最小可用实例：AHomotopy 三律直接闭合（Barcelo 机件零重证）
π₁-discrete : ∀ (G : DiGraph) (x : DiGraph.V G) → π₁-Spec G x
π₁-discrete G x = record
  { _∼_     = AHomotopy G
  ; ∼-refl  = AH-refl
  ; ∼-sym   = AH-symm
  ; ∼-trans = AH-trans
  }

-- 2 点图（two-chain 的比较图组合形）：V = Fin 2，边 = 0→1
G2 : DiGraph
G2 = record { V = Fin 2 ; edge = λ a b → (a ≡ fzero × b ≡ fsuc fzero) }

-- 最小 loop 实例：基点 fzero 的平凡 loop
ℓ0 : Loop G2 fzero
ℓ0 = nil fzero

π₁-G2 : π₁-Spec G2 fzero
π₁-G2 = π₁-discrete G2 fzero

-- 对账件：ℓ0 自反（三律实例过型）
check-ℓ0 : π₁-Spec._∼_ π₁-G2 ℓ0 ℓ0
check-ℓ0 = π₁-Spec.∼-refl π₁-G2 ℓ0

--------------------------------------------------------------------------------
-- ③ P2.2c 主件（|K(X)| → X 弱等价）精确剩余清单
--
-- (a1) 一般 KTri 的第三边（13-边）引理——⊑ 传递 + 对偶归谬，FinitePoset.trans 字段名核对后 ~6 行
--      （本 spike 对 two-chain 以 tri2-absurd 特案回避，一般形待补）；
-- (a2) 真几何实现：单纯形几何 + 商拓扑/承载拓扑——本库 Topology 面仅 Alexandroff 有限拓扑，
--      无一般拓扑空间机件 ⇒ 估 1-2 批（含 Δⁿ 单纯形、面映射/退化映射族、CW 粘合拓扑）；
-- (a3) n-骨架归纳（2-骨架 → n-骨架）+ 粘合结合性（∂ 复合相容）；
-- (b1) concat 合同性：⊞-resp（ℓ ∼ ℓ' → m ∼ m' → ℓ++m ∼ ℓ'++m'）——AStep 两生成元
--      （slide/expand）× _++w_ 合同 + AHomotopy 归纳，估 30-60 行；
-- (b2) 商型实化：π₁ᵈ = Loop / AHomotopy 用 Cubical.HITs.SetQuotients（A4/Stab 先例）
--      ~20 行 + 群结构（单位/逆/结合 modulo ∼——依赖 b1）；
-- (b3) πₙ≥2 机件：球面映射同伦类的组合逼近（Sⁿ 组合球面定义 + 同伦类）——估 1-2 批；
-- (c)  弱等价组装：McCord 经典路线（|K(X)| 形变收缩 + 单纯逼近）——依赖 (a2)(b1-b3)，估 1 批；
-- (d)  π₁ 对接：π₁ᵈ(|K(X)|) ≅ π₁ᵈ(X)（P2.2c 的 π₁ 面）——依赖 (b2)+(c)。
--
-- 现状判定：(a)(b) 前置的数据形与最小可用实例已交（本探针）；组合层（P2.2b）与 π₀ 面
-- （P2.2a）无悬空；路线无阻塞，纯增量。

--------------------------------------------------------------------------------
-- ④ 续批（P2.2c 前置件轻件实化）：(a1) tri-face-xz ＋ (b1) ⊞-resp concat 合同性
--------------------------------------------------------------------------------

-- (a1) 面单形性第三面：三角的 13-边仍是边——**纯投影**（OrderComplex.chain3-down
--   已全证三边分解含 xz：⊑-trans 跳接 + antisym 矛盾，复用零重证）
tri-face-xz : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → KEdge P x z
tri-face-xz P t = proj₁ (proj₂ (chain3-down P t))

-- (b1) concat 合同性（π₁ 乘法良定义的输入件）——walk 连接结合律为基座
walk-assoc : ∀ (G : DiGraph) {a b c d : DiGraph.V G} (p : Walk G a b) (x : Walk G b c) (q : Walk G c d)
           → ((p ++w x) ++w q) ≡ (p ++w (x ++w q))
walk-assoc G (nil v) x q = refl                     -- (nil ++ x) ++ q = x ++ q = nil ++ (x ++ q) [defeq]
walk-assoc G (cons e p) x q = cong (cons e) (walk-assoc G p x q)   -- 递归 [cons 同步]

-- AStep 在右侧拼接下合同（slide/expand 两生成元 × ++w）
AStep-concat-r : ∀ (G : DiGraph) {a b c : DiGraph.V G} {w1 w2 : Walk G a b}
               → AStep G w1 w2 → (q : Walk G b c) → AStep G (w1 ++w q) (w2 ++w q)
AStep-concat-r G (slide p b e1 e2 e3) q =
  subst₂ (λ u v → AStep G u v) eql eqr (slide p (b ++w q) e1 e2 e3)
  where
    eql : p ++w cons e1 (cons e2 (b ++w q)) ≡ (p ++w cons e1 (cons e2 b)) ++w q
    eql = sym (walk-assoc G p (cons e1 (cons e2 b)) q)
    eqr : p ++w cons e3 (b ++w q) ≡ (p ++w cons e3 b) ++w q
    eqr = sym (walk-assoc G p (cons e3 b) q)
AStep-concat-r G (expand p b e1 e2 e3) q =
  subst₂ (λ u v → AStep G u v) eql eqr (expand p (b ++w q) e1 e2 e3)
  where
    eql : p ++w cons e3 (b ++w q) ≡ (p ++w cons e3 b) ++w q
    eql = sym (walk-assoc G p (cons e3 b) q)
    eqr : p ++w cons e1 (cons e2 (b ++w q)) ≡ (p ++w cons e1 (cons e2 b)) ++w q
    eqr = sym (walk-assoc G p (cons e1 (cons e2 b)) q)

-- AStep 在左侧拼接下合同（结构直接——walk-assoc 反向归位）
AStep-concat-l : ∀ (G : DiGraph) {a b c : DiGraph.V G} (p0 : Walk G a b) {w1 w2 : Walk G b c}
               → AStep G w1 w2 → AStep G (p0 ++w w1) (p0 ++w w2)
AStep-concat-l G p0 (slide p b e1 e2 e3) =
  subst₂ (λ u v → AStep G u v) eql eqr (slide (p0 ++w p) b e1 e2 e3)
  where
    eql : (p0 ++w p) ++w (cons e1 (cons e2 b)) ≡ p0 ++w (p ++w (cons e1 (cons e2 b)))
    eql = walk-assoc G p0 p (cons e1 (cons e2 b))
    eqr : (p0 ++w p) ++w (cons e3 b) ≡ p0 ++w (p ++w (cons e3 b))
    eqr = walk-assoc G p0 p (cons e3 b)
AStep-concat-l G p0 (expand p b e1 e2 e3) =
  subst₂ (λ u v → AStep G u v) eql eqr (expand (p0 ++w p) b e1 e2 e3)
  where
    eql : (p0 ++w p) ++w (cons e3 b) ≡ p0 ++w (p ++w (cons e3 b))
    eql = walk-assoc G p0 p (cons e3 b)
    eqr : (p0 ++w p) ++w (cons e1 (cons e2 b)) ≡ p0 ++w (p ++w (cons e1 (cons e2 b)))
    eqr = walk-assoc G p0 p (cons e1 (cons e2 b))

-- AHomotopy 在两侧拼接下合同（四案归纳——disp2-respects 同款范式）
++w-resp-r : ∀ (G : DiGraph) {a b c : DiGraph.V G} {w1 w2 : Walk G a b}
           → AHomotopy G w1 w2 → (q : Walk G b c) → AHomotopy G (w1 ++w q) (w2 ++w q)
++w-resp-r G (refl' w) q = refl' (w ++w q)               -- 案 refl：拼接保持 [defeq]
++w-resp-r G (symm h) q = symm (++w-resp-r G h q)       -- 案 symm：IH 反向 [递归①]
++w-resp-r G (trans' h1 h2) q = trans' (++w-resp-r G h1 q) (++w-resp-r G h2 q)  -- 案 trans' [递归②③]
++w-resp-r G (gen s) q = gen (AStep-concat-r G s q)     -- 案 gen：生成元合同 [归约]

++w-resp-l : ∀ (G : DiGraph) {a b c : DiGraph.V G} (p0 : Walk G a b) {w1 w2 : Walk G b c}
           → AHomotopy G w1 w2 → AHomotopy G (p0 ++w w1) (p0 ++w w2)
++w-resp-l G p0 (refl' w) = refl' (p0 ++w w)
++w-resp-l G p0 (symm h) = symm (++w-resp-l G p0 h)
++w-resp-l G p0 (trans' h1 h2) = trans' (++w-resp-l G p0 h1) (++w-resp-l G p0 h2)
++w-resp-l G p0 (gen s) = gen (AStep-concat-l G p0 s)

-- ⊞-resp：concat 合同性（π₁ 乘法良定义输入件——ℓ ∼ ℓ' → m ∼ m' → ℓ++m ∼ ℓ'++m'）
⊞-resp : ∀ (G : DiGraph) {a b c : DiGraph.V G} {ℓ ℓ' : Walk G a b} {m m' : Walk G b c}
       → AHomotopy G ℓ ℓ' → AHomotopy G m m' → AHomotopy G (ℓ ++w m) (ℓ' ++w m')
⊞-resp G {ℓ = ℓ} {m' = m'} hℓ hm = trans' (++w-resp-l G ℓ hm) (++w-resp-r G hℓ m')
--   LHS: ℓ++m  →(固定 ℓ 移 m)→  ℓ++m'  →(固定 m' 移 ℓ)→  ℓ'++m'  [IH 两连]

-- ── G2 最小实例核对（两件）──
check-⊞-ℓ0 : AHomotopy G2 ((nil fzero) ++w (nil fzero)) ((nil fzero) ++w (nil fzero))
check-⊞-ℓ0 = ⊞-resp G2 (AH-refl (nil fzero)) (AH-refl (nil fzero))

check-concat-ℓ0 : AHomotopy G2 ((nil fzero) ++w (nil fzero)) ((nil fzero) ++w (nil fzero))
check-concat-ℓ0 = ++w-resp-r G2 (AH-refl (nil fzero)) (nil fzero)
