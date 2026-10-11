{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5 —— πₙ-B1：面偏序 + 等价桥（Sⁿᵈ 离散球面 A+C 双视图 + DHomotopy 骨架 + n=1 锚点）
--
-- 数学背景：
--   按 docs/plan/pi-n-design.md（设计权威）：Sⁿᵈ = ∂Δ^{n+1}（组合球面），
--   A+C 双视图——C 视图 = 面偏序（子集包含，呈现层）；A 视图 = 面复形
--   （k 顶点链，计算层）——两者是同一组合对象的两个视图（barycentric 同一）。
--   不走 ℝⁿ 凸包（连续统红线）；n=1 案 = 三角圈边界，其骨架圈的规范 loop
--   就是 Loop/Walk 件——「圈↔loop」对接的最小真件（一般桥归 B3，签名级立界）。
--
-- 核心原则：
--   1. 复用优先：Simplex/face/<ᵢ（_PPI3）零重证；FinitePoset（AlexandroffFinite）、
--      Strict（OrderComplex）、DiGraph/Walk（BarceloAHomotopy）全引现件；
--   2. DHomotopy 按 AHomotopy 三律构造子形复制（refl'/symm'/trans'/gen——关系入定义）；
--      本批 gen = 逐点步，柱体单步细化（Iᵈ×Sⁿᵈ）归 B2，如实立界；
--   3. 等价桥（本批已证）：DHomotopy f g ↔ (∀ s → f s ≡ g s)（dh-pw / pw-dh 双向）；
--   4. 未决点立档不隐：Sⁿᵈ 圈长参数化保留（不拍板）；C₄ 相位不打通（保持判）。
--
-- 包含：linPoset · strict-lin · Snd-face/S0d-face/S1d-face · sub-face · vert-distinct
--       · BasedMap · DStep/DHomotopy · dh-pw/pw-dh · S1edge/s1-adj/s1-loop
--       · S1-bridge-stmt（签名级立界）· S¹ᵈ 六面实例 + G2 折叠 + 核对层
module _PPI5 where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (_≤?_; ≤-refl; ≤-trans; ≤-antisym; 1+n≢n; n≤1+n; suc-injective)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.OrderComplex using (Strict)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil; cons)
open import _PPI3 using (_<ᵢ_; Simplex; face)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：全序偏序 + Strict 线性桥（组合单形的承载）
-- ────────────────────────────────────────────────────────────────────

-- Fin m 上的线性序（Δ^{m-1} 的顶点序——A 视图的承载偏序）
linPoset : (m : ℕ) → FinitePoset m
linPoset m = record
  { _⊑_       = λ a b → toℕ a ≤ toℕ b
  ; ⊑-dec     = λ a b → (toℕ a) ≤? (toℕ b)
  ; ⊑-refl    = λ a → ≤-refl
  ; ⊑-trans   = λ a b c → ≤-trans
  ; ⊑-antisym = λ a b p q → toℕ-injective (≤-antisym p q)
  }

-- Strict 线性桥：suc (toℕ a) ≤ toℕ b ⟹ Strict（免匹配总引理）
strict-lin : ∀ {m} (a b : Fin m) → suc (toℕ a) ≤ toℕ b → Strict (linPoset m) a b
strict-lin a b p =
  ≤-trans (n≤1+n (toℕ a)) p ,
  λ eq → 1+n≢n (≤-antisym (subst (λ z → suc (toℕ a) ≤ z) (cong toℕ (sym eq)) p)
                          (n≤1+n (toℕ a)))

-- Fin 异名辅助（fsuc 头同构——按 prover_limits #51 纪律走注入消解非空模式）
fsuc-ne : ∀ {n} {a b : Fin n} → a ≢ b → fsuc a ≢ fsuc b
fsuc-ne d eq = d (toℕ-injective (suc-injective (cong toℕ eq)))

-- ────────────────────────────────────────────────────────────────────
-- ④ 球面双视图：Sⁿᵈ = ∂Δ^{n+1}（A 计算层 + C 呈现层）
-- ────────────────────────────────────────────────────────────────────

-- A 视图（计算层）：Sⁿᵈ 的 k-面 = n+2 顶点全序集中的 k 顶点链
Snd-face : (n k : ℕ) → Set
Snd-face n k = Simplex (linPoset (suc (suc n))) k

S0d-face : ℕ → Set
S0d-face = Snd-face 0

S1d-face : ℕ → Set
S1d-face = Snd-face 1

-- C 视图（呈现层）：面 = 有序顶点子集——包含关系（面偏序的原子）
sub-face : ∀ {n k l} → Snd-face n k → Snd-face n l → Set
sub-face s t = ∀ i → Σ (Fin _) (λ j → Simplex.vert s i ≡ Simplex.vert t j)

-- 子集合法性核：链性 ⟹ 顶点互异
vert-distinct : ∀ {n k} (s : Snd-face n k) (i j : Fin k) → i <ᵢ j →
                Simplex.vert s i ≢ Simplex.vert s j
vert-distinct s i j p = proj₂ (Simplex.vchain s i j p)

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 基点映射 + DHomotopy 骨架（三律构造子形——AHomotopy 范式复制）
-- ────────────────────────────────────────────────────────────────────

record BasedMap (S : Set) (s₀ : S) (X : Set) (x₀ : X) : Set where
  field
    to      : S → X
    to-base : to s₀ ≡ x₀

-- 柱体单步（B1 形 = 逐点步；B2 细化为 Iᵈ 柱体单步——立界）
DStep : {S X : Set} → (S → X) → (S → X) → Set
DStep {S} f g = ∀ s → f s ≡ g s

data DHomotopy {S X : Set} : (S → X) → (S → X) → Set where
  refl'  : ∀ {f : S → X} → DHomotopy f f
  symm'  : ∀ {f g : S → X} → DHomotopy f g → DHomotopy g f
  trans' : ∀ {f g h : S → X} → DHomotopy f g → DHomotopy g h → DHomotopy f h
  gen    : ∀ {f g : S → X} → DStep f g → DHomotopy f g

-- 等价桥（本批已证，双向）：DHomotopy ↔ 逐点相等
dh-pw : {S X : Set} {f g : S → X} → DHomotopy f g → ∀ s → f s ≡ g s
dh-pw refl'        s = refl
dh-pw (symm' q)      s = sym (dh-pw q s)
dh-pw (trans' q1 q2) s = trans (dh-pw q1 s) (dh-pw q2 s)
dh-pw (gen d)        s = d s

pw-dh : {S X : Set} {f g : S → X} → (∀ s → f s ≡ g s) → DHomotopy f g
pw-dh pw = gen pw

-- ────────────────────────────────────────────────────────────────────
-- ⑥ n=1 锚点：S¹ᵈ 骨架圈 = 三角圈图，规范 loop 是真 Walk 件
-- ────────────────────────────────────────────────────────────────────

data S1edge : Fin 3 → Fin 3 → Set where
  e01 : S1edge fzero (fsuc fzero)
  e12 : S1edge (fsuc fzero) (fsuc (fsuc fzero))
  e20 : S1edge (fsuc (fsuc fzero)) fzero

s1-adj : DiGraph
s1-adj = record { V = Fin 3 ; edge = S1edge }

-- S¹ᵈ 的规范闭圈（骨架 1-圈）——「圈↔loop」对接的 S¹ᵈ 侧真件
s1-loop : Walk s1-adj fzero fzero
s1-loop = cons e01 (cons e12 (cons e20 (nil fzero)))

-- n=1 一般桥（B3 主件——签名级立界）：
--   [S¹ᵈ, X]_*（BasedMap + DHomotopy 模）↔ π₁ᵈ(X, x₀)（Loop + AHomotopy 模）。
--   最小真件 = s1-loop（上）；一般双向 map 归 B3（需 f 对 S1edge 同态条件 + 两同伦互导）。
S1-bridge-stmt : Set₁
S1-bridge-stmt = (G : DiGraph) (x : DiGraph.V G) → Set

-- ────────────────────────────────────────────────────────────────────
-- ⑦ 最小实例：S¹ᵈ 六面 + G2 折叠映射 + 核对层（refl 级）
-- ────────────────────────────────────────────────────────────────────

-- 顶点表命名件（免匹配范式——record 内模式 λ 会卡后字段合一，fork 教训）
vert-v0 : Fin 1 → Fin 3
vert-v0 fzero = fzero

vert-v1 : Fin 1 → Fin 3
vert-v1 fzero = fsuc fzero

vert-v2 : Fin 1 → Fin 3
vert-v2 fzero = fsuc (fsuc fzero)

vert-01 : Fin 2 → Fin 3
vert-01 fzero = fzero
vert-01 (fsuc fzero) = fsuc fzero

vert-12 : Fin 2 → Fin 3
vert-12 fzero = fsuc fzero
vert-12 (fsuc fzero) = fsuc (fsuc fzero)

vert-02 : Fin 2 → Fin 3
vert-02 fzero = fzero
vert-02 (fsuc fzero) = fsuc (fsuc fzero)

-- 二/一元链的链性分派器（case 穷尽 ≤27；难案走 #51 注入消解）
vchain-2case : ∀ {n} (f : Fin 2 → Fin (suc (suc n))) →
               toℕ (f fzero) ≤ toℕ (f (fsuc fzero)) →
               f fzero ≢ f (fsuc fzero) →
               (i j : Fin 2) → i <ᵢ j → Strict (linPoset (suc (suc n))) (f i) (f j)
vchain-2case f le ne fzero (fsuc fzero)  p = le , ne
vchain-2case f le ne fzero fzero        ()
vchain-2case f le ne (fsuc fzero) fzero ()
vchain-2case f le ne (fsuc fzero) (fsuc fzero) (s≤s ())

vchain-1case : ∀ {n} (f : Fin 1 → Fin (suc (suc n))) →
               (i j : Fin 1) → i <ᵢ j → Strict (linPoset (suc (suc n))) (f i) (f j)
vchain-1case f fzero fzero ()

-- S¹ᵈ 的 6 个真面（3 顶点 + 3 边——顶面三元链不入）
vv0 : S1d-face 1
vv0 = record { vert = vert-v0 ; vchain = vchain-1case vert-v0 }

vv1 : S1d-face 1
vv1 = record { vert = vert-v1 ; vchain = vchain-1case vert-v1 }

vv2 : S1d-face 1
vv2 = record { vert = vert-v2 ; vchain = vchain-1case vert-v2 }

v01 : S1d-face 2
v01 = record { vert = vert-01 ; vchain = vchain-2case vert-01 z≤n (λ ()) }

v12 : S1d-face 2
v12 = record { vert = vert-12 ; vchain = vchain-2case vert-12 (s≤s z≤n) (fsuc-ne (λ ())) }

v02 : S1d-face 2
v02 = record { vert = vert-02 ; vchain = vchain-2case vert-02 z≤n (λ ()) }

-- C 视图包含核对：顶点 ⊆ 边（面偏序 0 < 1 层原子）
check-sub-v0 : sub-face vv0 v01
check-sub-v0 fzero = fzero , refl

-- 面映射核对：∂₀(v01) = 顶点 1（删首点）
check-face0-v01 : toℕ (Simplex.vert (face (linPoset 3) v01 fzero) fzero) ≡ 1
check-face0-v01 = refl

-- G2 折叠映射（S¹ᵈ 面 → 两顶点图）+ DHomotopy 双向桥核对
g2fold : Fin 3 → Fin 2
g2fold fzero = fzero
g2fold (fsuc fzero) = fsuc fzero
g2fold (fsuc (fsuc fzero)) = fzero

check-dh-g2 : DHomotopy g2fold g2fold
check-dh-g2 = refl'

check-pw-g2 : ∀ v → g2fold v ≡ g2fold v
check-pw-g2 = dh-pw refl'

check-bridge-round : DHomotopy g2fold g2fold
check-bridge-round = pw-dh (λ v → refl)

-- S¹ᵈ 六面顶点表核对（A 视图取值）
check-v01-0 : toℕ (Simplex.vert v01 fzero) ≡ 0
check-v01-0 = refl
check-v01-1 : toℕ (Simplex.vert v01 (fsuc fzero)) ≡ 1
check-v01-1 = refl
check-v12-0 : toℕ (Simplex.vert v12 fzero) ≡ 1
check-v12-0 = refl
check-v02-1 : toℕ (Simplex.vert v02 (fsuc fzero)) ≡ 2
check-v02-1 = refl
check-vv2-0 : toℕ (Simplex.vert vv2 fzero) ≡ 2
check-vv2-0 = refl

-- ────────────────────────────────────────────────────────────────────
-- ⑧ 精确剩余（立界——B2/B3 前置清单）
--   (i) C→A 桥：子集排序成链（需可判定排程）——B2；
--   (ii) DHomotopy 柱体细化（Iᵈ 组合区间 + 单步生成元 + 三律保持）——B2；
--   (iii) [Sⁿᵈ,X]_* 商型 + n=1 一般桥（圈↔loop 双向 map）——B3；
--   (iv) Sⁿᵈ 圈长 4 vs k+1 参数化保留（未决点，不拍板）；
--   (v) C₄ 相位不打通（保持判——球面对称群 ≠ 框架相位群，如实注记）。
-- ────────────────────────────────────────────────────────────────────
