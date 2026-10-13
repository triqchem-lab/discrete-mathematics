{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI3 —— (a2) 组合几何实现 spike：Simplex / Nerve / Skel 三件套 + 最小实例
--
-- 数学背景：
--   McCord/Barcelo 理论属有限拓扑——|K(X)| 的几何实现走**序复形组合形**
--   （神经 = 严格链族，半单纯集呈现），不走 ℝⁿ 凸包（连续统红线：ε-逃逸/不可数）。
--   n-单形 = 偏序集中 (n+1) 个顶点的严格递增链（全序子集）；
--   面映射 ∂ᵢ = 删第 i 顶点（纯组合，无几何无实数）。
--
-- 核心原则：
--   1. 复用优先：Strict/IsChain2/IsChain3（OrderComplex）、KVert/KEdge/KTri（_PMc2）、
--      two-chain/_⊑₂_（McCordPi0）零重证；
--   2. presentation 最小性：半单纯集形——链单射故**退化映射不在架**
--      （不设无用字段；「无退化」是定理性事实非遗漏，同 B3 relations 判据）；
--   3. 面映射 ∂ᵢ 是实现函子面映射数据（B3 relations 同定位）；
--      ∂ 复合律（半单纯关系 ∂ᵢ∂ⱼ = ∂ⱼ₋₁∂ᵢ）属 (a3) 预备件，见节尾立界。
--
-- 包含：<ᵢ（Fin 序）· skip/skip-<（删点）· Simplex（顶点表+链性）· face（∂ᵢ）
--       · Nerve（神经）· Sk/Sk-inj/face-Sk（骨架递升+∂ 封闭可导出件）
--       · nerve-two-chain/edge12/vert0/vert1/no-tri2（two-chain 最小实例）
--       · GraphNerve/G2adj/G2nerve-edge（G2 的 nerve 同形件）· 核对层
module _PPI3 where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_≟_ to _≟ℕ_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (¬_)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Synthesis.McCordPi0 using (two-chain; _⊑₂_; ⊑₂-00; ⊑₂-01; ⊑₂-11)
open import Sovereign.Synthesis.OrderComplex using (Strict)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：Fin 序 + 删点（组合面映射的机件）
-- ────────────────────────────────────────────────────────────────────

-- Fin 上的序（自含形——suc (toℕ i) ≤ toℕ j，规避 stdlib 版本形状漂移）
infix 4 _<ᵢ_
_<ᵢ_ : ∀ {k} → Fin k → Fin k → Set
i <ᵢ j = suc (toℕ i) ≤ toℕ j

-- 删点：skip i j = 从 (suc m) 元表中删第 i 元后第 j 元的原位置
skip : ∀ {m} → Fin (suc m) → Fin m → Fin (suc m)
skip fzero j = fsuc j
skip (fsuc i) fzero = fzero
skip (fsuc i) (fsuc j) = fsuc (skip i j)

-- 删点保序（∂ᵢ 良定性的机件——机械分案）
skip-< : ∀ {m} (i : Fin (suc m)) {j k : Fin m} → j <ᵢ k → skip i j <ᵢ skip i k
skip-< fzero {j} {k} p = s≤s p
skip-< (fsuc i) {fzero} {fzero} ()
skip-< (fsuc i) {fzero} {fsuc k} p = s≤s z≤n
skip-< (fsuc i) {fsuc j} {fzero} ()
skip-< (fsuc i) {fsuc j} {fsuc k} (s≤s p) = s≤s (skip-< i {j} {k} p)

-- ────────────────────────────────────────────────────────────────────
-- ④ 主件层：组合单形（顶点表 + 链性）
-- ────────────────────────────────────────────────────────────────────

-- k-顶点组合单形 = 有序 k 元链（IsChain k 形泛化）：
--   vert = 顶点表（第 i 顶点）；vchain = 表序 ⟹ 严格链性
record Simplex {n} (P : FinitePoset n) (k : ℕ) : Set where
  field
    vert   : Fin k → Fin n
    vchain : (i j : Fin k) → i <ᵢ j → Strict P (vert i) (vert j)

-- 面映射 ∂ᵢ = 删第 i 顶点（组合形——无几何）
face : ∀ {n} (P : FinitePoset n) {k} (s : Simplex P (suc k)) (i : Fin (suc k)) → Simplex P k
face P s i = record
  { vert   = λ j → Simplex.vert s (skip i j)
  ; vchain = λ j₁ j₂ lt → Simplex.vchain s (skip i j₁) (skip i j₂) (skip-< i lt) }

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 组合层：神经（Nerve）+ 骨架（Skel）
-- ────────────────────────────────────────────────────────────────────

-- X 的神经：k-单形 = X 中 k 元全序子集（严格链）——接 OrderComplex
-- （k=1 顶点 / k=2 边 / k=3 面；半单纯集：无退化映射——链单射是定理性事实）
Nerve : ∀ {n} (P : FinitePoset n) (k : ℕ) → Set
Nerve P k = Simplex P k

-- m-骨架承载：维数 ≤ m 的单形族（维数 k ↔ suc k 顶点）
Sk : ∀ {n} (P : FinitePoset n) (m : ℕ) → Set
Sk P m = Σ ℕ (λ k → k ≤ m × Simplex P (suc k))

-- 骨架递升：Sk 0 ⊂ Sk 1 ⊂ Sk 2 ⊂ …（K2Gluing 泛化预备）
Sk-inj : ∀ {n} (P : FinitePoset n) {m} → Sk P m → Sk P (suc m)
Sk-inj P (k , le , s) = k , m≤m+1 le , s
  where
    m≤m+1 : ∀ {k m} → k ≤ m → k ≤ suc m
    m≤m+1 z≤n = z≤n
    m≤m+1 (s≤s p) = s≤s (m≤m+1 p)

-- ∂ 封闭（可导出件——不入 record 字段，presentation 最小性）：
--   m-骨架单形的面仍在 m-骨架（face 降维）
face-Sk : ∀ {n} (P : FinitePoset n) {m k} (s : Simplex P (suc (suc k)))
        → suc k ≤ m → (i : Fin (suc (suc k))) → Sk P m
face-Sk P {m} {k} s le i = k , drop le , face P s i
  where
    drop : ∀ {k m} → suc k ≤ m → k ≤ m
    drop (s≤s p) = step p
      where
        step : ∀ {k m} → k ≤ m → k ≤ suc m
        step z≤n = z≤n
        step (s≤s p) = s≤s (step p)

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 实例层：two-chain 的神经与 2-骨架（最小实例）
-- ────────────────────────────────────────────────────────────────────

-- 顶点单形（dim 0）
-- ≤ 归谬辅助（一层 () 只看构造子头——suc m ≤ m 的 s≤s 头可合，需递归消解）
≤-irrefl-1 : ∀ {m} → ¬ (suc m ≤ m)
≤-irrefl-1 {zero} ()
≤-irrefl-1 {suc m} (s≤s p) = ≤-irrefl-1 {m} p

≤-zero-impossible : ∀ {m} → ¬ (suc m ≤ zero)
≤-zero-impossible ()

-- 顶点单形（dim 0）——顶层命名件（免 record 内模式 λ 的字段投影卡死）
vert0v : Fin 1 → Fin 2
vert0v fzero = fzero

vert0c : (i j : Fin 1) → i <ᵢ j → Strict two-chain (vert0v i) (vert0v j)
vert0c fzero fzero p = ⊥-elim (≤-irrefl-1 {zero} p)

vert0 : Simplex two-chain 1
vert0 = record { vert = vert0v ; vchain = vert0c }

vert1v : Fin 1 → Fin 2
vert1v fzero = fsuc fzero

vert1c : (i j : Fin 1) → i <ᵢ j → Strict two-chain (vert1v i) (vert1v j)
vert1c fzero fzero p = ⊥-elim (≤-irrefl-1 {zero} p)

vert1 : Simplex two-chain 1
vert1 = record { vert = vert1v ; vchain = vert1c }

-- 边单形（dim 1）：0 ⊏ 1
f0≢f1 : _≡_ {A = Fin 2} fzero (fsuc fzero) → ⊥
f0≢f1 ()

edge12v : Fin 2 → Fin 2
edge12v fzero = fzero
edge12v (fsuc fzero) = fsuc fzero

edge12c : (i j : Fin 2) → i <ᵢ j → Strict two-chain (edge12v i) (edge12v j)
edge12c fzero (fsuc fzero) p = ⊑₂-01 , f0≢f1
edge12c fzero fzero p = ⊥-elim (≤-irrefl-1 {zero} p)
edge12c (fsuc fzero) (fsuc fzero) p = ⊥-elim (≤-irrefl-1 {suc zero} p)
edge12c (fsuc fzero) fzero p = ⊥-elim (≤-zero-impossible p)

edge12 : Simplex two-chain 2
edge12 = record { vert = edge12v ; vchain = edge12c }

-- two-chain 无 2-单形（三顶点严格链不可居留——Fin 2 只容两异点）
no-tri2 : Simplex two-chain 3 → ⊥
no-tri2 s = go (Simplex.vert s fzero) (Simplex.vert s (fsuc fzero)) (Simplex.vert s (fsuc (fsuc fzero)))
               (Simplex.vchain s fzero (fsuc fzero) lem01)
               (Simplex.vchain s (fsuc fzero) (fsuc (fsuc fzero)) lem12)
  where
    lem01 : _<ᵢ_ {2} fzero (fsuc fzero)
    lem01 = s≤s z≤n
    lem12 : _<ᵢ_ {3} (fsuc fzero) (fsuc (fsuc fzero))
    lem12 = s≤s (s≤s z≤n)
    -- 逐顶点分案：Strict two-chain 的 ⊑ 分量只有 ⊑₂-00/01/11 三个形
    -- （构造子指标强制端点），配合 ≢ 分量消解全部存活分支（≤27 case 边界内）：
    --   ⊑₂-00/11 案：a≢b 与 a≡b 矛盾；⊑₂-01 案（a=0,b=1）：第二对 ⊑₂-11 ⇒ b=1=c ⇒ b≢c 矛盾
    --   （第二对的 ⊑₂-00/01 构造子指标与 b=1 不合，被覆盖检查自动排除）
    go : (a b c : Fin 2) → Strict two-chain a b → Strict two-chain b c → ⊥
    go .fzero .fzero c (⊑₂-00 , a≢b) _ = a≢b refl
    go .(fsuc fzero) .(fsuc fzero) c (⊑₂-11 , a≢b) _ = a≢b refl
    go .fzero .(fsuc fzero) .(fsuc fzero) (⊑₂-01 , _) (⊑₂-11 , b≢c) = b≢c refl

-- two-chain 的神经与 2-骨架实例
nerve-two-chain : Nerve two-chain 2
nerve-two-chain = edge12

sk2-two-chain : Sk two-chain 2
sk2-two-chain = 1 , s≤s z≤n , edge12

-- ────────────────────────────────────────────────────────────────────
-- ⑦ G2 的 nerve（图神经 = clique 复形——对称图同形件）
-- ────────────────────────────────────────────────────────────────────

-- 图神经：k-单形 = k 个两两相邻顶点（clique）
record GraphNerve (V : Set) (adj : V → V → Set) (k : ℕ) : Set where
  field
    gvert   : Fin k → V
    gclique : ∀ i j → ¬ (i ≡ j) → adj (gvert i) (gvert j)

-- G2（Barcelo 双点图）的对称化邻接：相异即邻（K2 形）
G2adj : Fin 2 → Fin 2 → Set
G2adj x y = ¬ (x ≡ y)

-- 恒等顶点表（2 点）
g2v : Fin 2 → Fin 2
g2v fzero = fzero
g2v (fsuc fzero) = fsuc fzero

-- 表单射（2 点分案）
g2v-inj : ∀ i j → g2v i ≡ g2v j → i ≡ j
g2v-inj fzero fzero p = refl
g2v-inj fzero (fsuc fzero) ()
g2v-inj (fsuc fzero) fzero ()
g2v-inj (fsuc fzero) (fsuc fzero) p = refl

G2nerve-edge : GraphNerve (Fin 2) G2adj 2
G2nerve-edge = record
  { gvert   = g2v
  ; gclique = λ i j ne p → ne (g2v-inj i j p) }

-- ────────────────────────────────────────────────────────────────────
-- ⑧ 核对层（refl 级交叉）
-- ────────────────────────────────────────────────────────────────────

-- 面映射逐点核对：∂₀ edge12 = vert1 形（顶点逐点相等——免 funext）
check-face0-v : Simplex.vert (face two-chain edge12 fzero) fzero ≡ fsuc fzero
check-face0-v = refl

check-face1-v : Simplex.vert (face two-chain edge12 (fsuc fzero)) fzero ≡ fzero
check-face1-v = refl

-- 删点核对
check-skip : skip {1} (fsuc fzero) fzero ≡ fzero
check-skip = refl

-- 骨架递升核对
check-sk-inj : proj₁ (Sk-inj two-chain sk2-two-chain) ≡ 1
check-sk-inj = refl

-- ────────────────────────────────────────────────────────────────────
-- ⑨ 精确剩余（设计 spike 立界——供 (a3)/(d) 定基）
-- ────────────────────────────────────────────────────────────────────
-- (i)   ∂ 复合律（半单纯关系）：face (face s i) j ≈ face (face s (j+1)) i（j<i 形）
--       —— (a3) n-骨架归纳的结合性预备，~15-25 行（skip 双删交换 + vert 逐点）；
-- (ii)  KnGluing 泛化：K2Gluing 的 Sk2 占位承载 ← 对接本文件 Sk 2 形
--       （ιv/ιf ↔ 单形包含；∂₂ ↔ face 三边包）——(a3) 主件；
-- (iii) 一般图神经（对称化可达性偏序化）属 (d) π₁ 对接件——G2 同形件已给，
--       一般形待 (d) 定陈述（群/幺半群分水岭：有向图无 flip 时逆律缺失）；
-- (iv)  真几何（ℝⁿ 凸包）**明确排除**（连续统红线）——组合形即终形，非遗漏；
-- (v)   退化映射：神经为半单纯集（链单射 ⇒ 无退化）——定理性事实非缺口。

-- ────────────────────────────────────────────────────────────────────
-- ⑩ (a3) 预备件 + KnGluing 对接（2026-10-11——决策 3 顺推件；细化 ⑨(i)(ii)）
--   (i)  ∂ 复合律（半单纯关系）：face∘face 双删交换——vert 逐点形
--        （record 级等式需 funExt/证明无关，vert 数据层即定律本体——立界注记）；
--   (ii) KnGluing 对接：Sk 形 → K2Gluing 实例（ιv/ιf ↔ 单形包含；∂₂ ↔ face 三边包）。
-- 修程注：fzero : Fin (suc n) 构造子形——m 未细化时结果位构造不出（本节全部
--   Fin m 结果件均以 {zero}/{suc _} 形细化 m（隐式形模式）；递归件的 m 细化
--   由 fsuc 尾模式承担（skip-< 同诀）。
-- ────────────────────────────────────────────────────────────────────
open import Sovereign.Synthesis.OrderComplex using (chain3-down; lin3; lin3-chain3)
open import Sovereign.Synthesis._PMc2 using (KVert; KEdge; KTri; tri-face-xy; tri-face-yz)
open import _PPI using (FaceBoundary; bd; K2Gluing)

-- ⑩.1 删点双向映射（skip 的两个逆向件）
-- unskip b a lt = 原位 a 在删 b 后的余位（a < b 时 a 的余位 = a 本身）
unskip : ∀ {m} (b a : Fin (suc m)) → a <ᵢ b → Fin m
unskip {zero} fzero fzero ()
unskip {suc _} fzero _ ()
unskip {suc _} (fsuc _) fzero _ = fzero
unskip {suc _} (fsuc i) (fsuc j) (s≤s p) = fsuc (unskip i j p)

skip-unskip : ∀ {m} (b a : Fin (suc m)) (lt : a <ᵢ b) → skip b (unskip b a lt) ≡ a
skip-unskip {zero} fzero fzero ()
skip-unskip {suc _} fzero _ ()
skip-unskip {suc _} (fsuc _) fzero _ = refl
skip-unskip {suc _} (fsuc i) (fsuc j) (s≤s p) = cong fsuc (skip-unskip i j p)

-- shift a b lt = 原位 b 在删 a 后的余位（a < b 时 b 的余位前移一位）
shift : ∀ {m} (a b : Fin (suc m)) → a <ᵢ b → Fin m
shift {zero} fzero fzero ()
shift {suc _} fzero fzero ()
shift {suc _} fzero (fsuc b) _ = b
shift {suc _} (fsuc _) fzero ()
shift {suc _} (fsuc a) (fsuc b) (s≤s p) = fsuc (shift a b p)

skip-shift : ∀ {m} (a b : Fin (suc m)) (lt : a <ᵢ b) → skip a (shift a b lt) ≡ b
skip-shift {zero} fzero fzero ()
skip-shift {suc _} fzero fzero ()
skip-shift {suc _} fzero (fsuc b) _ = refl
skip-shift {suc _} (fsuc _) fzero ()
skip-shift {suc _} (fsuc a) (fsuc b) (s≤s p) = cong fsuc (skip-shift a b p)

-- 双删交换（skip 核心代数——∂ 复合律的组合引理）：
--   先删 B 再删 A 余位 = 先删 A 再删 B 余位（删对 {A,B} 与顺序无关）
skip-comm2 : ∀ {m} (A B : Fin (suc (suc m))) (lt : A <ᵢ B) (x : Fin m)
  → skip B (skip (unskip B A lt) x) ≡ skip A (skip (shift A B lt) x)
skip-comm2 fzero fzero ()
skip-comm2 (fsuc _) fzero ()
skip-comm2 fzero (fsuc _) _ _ = refl
skip-comm2 (fsuc A) (fsuc B) (s≤s lt) fzero = refl
skip-comm2 (fsuc A) (fsuc B) (s≤s lt) (fsuc x) = cong fsuc (skip-comm2 A B lt x)

-- ⑩.2 ∂ 复合律（半单纯关系）——vert 逐点形
--   两条删 {A,B} 的复合面在顶点数据上逐点相等：
--   face (face s B) (unskip B A lt) 与 face (face s A) (shift A B lt)
face-face-comm : ∀ {n} (P : FinitePoset n) {k} (s : Simplex P (suc (suc k)))
  (A B : Fin (suc (suc k))) (lt : A <ᵢ B) (x : Fin k)
  → Simplex.vert (face P (face P s B) (unskip B A lt)) x
  ≡ Simplex.vert (face P (face P s A) (shift A B lt)) x
face-face-comm P s A B lt x = cong (Simplex.vert s) (skip-comm2 A B lt x)

-- ⑩.3 KnGluing 对接件：顶点单形 / 三角单形 / 面三边包
-- 顶点单形（dim 0——vchain 在 Fin 1 无严格对，空真；通用 P）
vert-simplex : ∀ {n} (P : FinitePoset n) (v : Fin n) → Simplex P 1
vert-simplex P v = record
  { vert   = λ _ → v
  ; vchain = λ i j lt → ⊥-elim (f1-<absurd i j lt) }
  where
    f1-<absurd : (i j : Fin 1) → i <ᵢ j → ⊥
    f1-<absurd fzero fzero lt = ≤-zero-impossible lt

-- 三角单形（dim 2）：KTri x y z ↦ 顶点表 (x,y,z)——vchain 由三边供证
tri-v : ∀ {n} (x y z : Fin n) → Fin 3 → Fin n
tri-v x y z fzero = x
tri-v x y z (fsuc fzero) = y
tri-v x y z (fsuc (fsuc fzero)) = z

-- 面三边包 ↔ bd 槽位表：face0(删x)=e23 / face1(删y)=e13 / face2(删z)=e12
tri-c : ∀ {n} (P : FinitePoset n) {x y z : Fin n}
        (hxy : Strict P x y) (hyz : Strict P y z)
      → (i j : Fin 3) → i <ᵢ j → Strict P (tri-v x y z i) (tri-v x y z j)
tri-c P hxy hyz fzero fzero lt = ⊥-elim (≤-zero-impossible lt)
tri-c P hxy hyz fzero (fsuc fzero) _ = hxy
tri-c P hxy hyz fzero (fsuc (fsuc fzero)) _ =
  proj₁ (proj₂ (chain3-down P (hxy , hyz)))          -- xz 边：chain3-down 纯投影（(a1) 件）
tri-c P hxy hyz (fsuc fzero) fzero lt = ⊥-elim (≤-zero-impossible lt)
tri-c P hxy hyz (fsuc fzero) (fsuc fzero) lt = ⊥-elim (≤-irrefl-1 lt)
tri-c P hxy hyz (fsuc fzero) (fsuc (fsuc fzero)) _ = hyz
tri-c P hxy hyz (fsuc (fsuc fzero)) fzero lt = ⊥-elim (≤-zero-impossible lt)
tri-c P hxy hyz (fsuc (fsuc fzero)) (fsuc fzero) (s≤s p) = ⊥-elim (≤-zero-impossible p)
tri-c P hxy hyz (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) lt = ⊥-elim (≤-irrefl-1 lt)

tri-simplex : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → Simplex P 3
tri-simplex P {x} {y} {z} t = record
  { vert   = tri-v x y z
  ; vchain = tri-c P (tri-face-xy P t) (tri-face-yz P t) }

tri-xz : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → Strict P x z
tri-xz P t = proj₁ (proj₂ (chain3-down P t))

-- ⑩.4 Sk 形 → K2Gluing（ιv/ιf ↔ 单形包含；∂₂ ↔ face 三边包）——(a3) 主件
sk2-v : ∀ {n} (P : FinitePoset n) → KVert {n} → Sk P 2
sk2-v P v = 0 , z≤n , vert-simplex P v

sk2-f : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → Sk P 2
sk2-f P t = 2 , s≤s (s≤s z≤n) , tri-simplex P t

sk2-∂ : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → FaceBoundary P {x} {y} {z}
sk2-∂ P t = bd (tri-face-xy P t) (tri-face-yz P t) (tri-xz P t)

K2-from-Sk : ∀ {n} (P : FinitePoset n) → K2Gluing P
K2-from-Sk P = record
  { Sk2 = Sk P 2
  ; ιv  = sk2-v P
  ; ιf  = sk2-f P
  ; ∂₂  = sk2-∂ P }

-- 对接核对：ιv 的顶点数据 = 原顶点（单形包含语义）
dock-ιv-vert : ∀ {n} (P : FinitePoset n) (v : Fin n)
  → Simplex.vert (proj₂ (proj₂ (K2Gluing.ιv (K2-from-Sk P) v))) fzero ≡ v
dock-ιv-vert P v = refl

-- 对接核对：∂₂ 的三分量 = face 三边包（bd 槽位表逐字）
∂₂-pack : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → K2Gluing.∂₂ (K2-from-Sk P) t
  ≡ bd (tri-face-xy P t) (tri-face-yz P t) (tri-xz P t)
∂₂-pack P t = refl

-- ⑩.5 核对层（refl 级交叉——face 三边包 vert 表）
tri-f0-v0 : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → Simplex.vert (face P (tri-simplex P t) fzero) fzero ≡ y
tri-f0-v0 P t = refl
tri-f0-v1 : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → Simplex.vert (face P (tri-simplex P t) fzero) (fsuc fzero) ≡ z
tri-f0-v1 P t = refl
tri-f1-v0 : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → Simplex.vert (face P (tri-simplex P t) (fsuc fzero)) fzero ≡ x
tri-f1-v0 P t = refl
tri-f1-v1 : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → Simplex.vert (face P (tri-simplex P t) (fsuc fzero)) (fsuc fzero) ≡ z
tri-f1-v1 P t = refl
tri-f2-v0 : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → Simplex.vert (face P (tri-simplex P t) (fsuc (fsuc fzero))) fzero ≡ x
tri-f2-v0 P t = refl
tri-f2-v1 : ∀ {n} (P : FinitePoset n) {x y z : Fin n} (t : KTri P x y z)
  → Simplex.vert (face P (tri-simplex P t) (fsuc (fsuc fzero))) (fsuc fzero) ≡ y
tri-f2-v1 P t = refl

-- 双删交换实例核对（lin3 三链：两条删 {0,1} 路径同值）
check-ff-lin3 :
    Simplex.vert (face lin3 (face lin3 (tri-simplex lin3 lin3-chain3) (fsuc fzero)) fzero) fzero
  ≡ Simplex.vert (face lin3 (face lin3 (tri-simplex lin3 lin3-chain3) fzero) fzero) fzero
check-ff-lin3 = refl

-- two-chain 对接注入（ιv 两顶点可分——与 old skel2-two-chain 的 Fin 2 占位顶点层一致）
dock-inj-two-chain :
    K2Gluing.ιv (K2-from-Sk two-chain) fzero
  ≡ K2Gluing.ιv (K2-from-Sk two-chain) (fsuc fzero) → ⊥
dock-inj-two-chain p = f0≢f1 (cong (λ c → Simplex.vert (proj₂ (proj₂ c)) fzero) p)

-- ⑩.6 精确剩余（(a3) 后续定基）
--   (i)   face-face-comm 的 record 级提升需 funExt/证明无关（vchain 为证明字段）——立界；
--   (ii)  K2Gluing.Sk2 与 Sk 2 的承载级同一（iso/等价桥）——本件给构造 + vert 级对接核对；
--   (iii) n-骨架归纳（KnGluing 泛化到 n）依赖 (i)(ii) 落定；
--   (iv)  一般图神经（对称化偏序化）属 (d) π₁ 对接件（群/幺半群分水岭先定陈述）。
