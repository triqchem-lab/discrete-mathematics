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
open import Sovereign.Topology.McCordPi0 using (two-chain; _⊑₂_; ⊑₂-00; ⊑₂-01; ⊑₂-11)
open import Sovereign.Topology.OrderComplex using (Strict)

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
