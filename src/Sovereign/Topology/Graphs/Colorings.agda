{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.Colorings
-- 任务池 P2 图论续第二件：图着色——相邻顶点异色（proper k-着色）与色数。
--   数学背景：着色/色数是图论基础面；四色定理是经典深件——本模块定义层 +
--   小例全证（K2/K3）+ 深件立界。与 Connectivity.Bipartite（二着色 Bool 形）
--   的桥接对齐。
--
-- 核心原则：
-- 1. Coloring = Σ 色映射 + 异色性谓词（关系入定义——性质随数据携带）
-- 2. 小例全证（K2：2-色有/1-色无；K3：3-色有/2-色无）+ 一般形立界
-- 3. 0 postulate / 0 hole；复用零重证（Graph 面 GraphBasic；Bipartite 桥 Connectivity；
--    K2 件 Trees 直引）
--
-- 包含：Coloring/TwoColoring · cf2 桥 · bipartite→2 · K2/K3 全证 · 核对层

module Sovereign.Topology.Graphs.Colorings where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Topology.Graphs.GraphBasic using (Graph; V; adj; adj-sym; adj-irrefl)
open import Sovereign.Topology.Graphs.Connectivity using (Bipartite)
open import Sovereign.Topology.Graphs.Trees using (Bit; b0; b1; neq01; neq10; adj2; adj2-sym; adj2-irrefl; K2)

--------------------------------------------------------------------------------
-- §1 定义层：Coloring（Σ 形——色映射 + 异色性，性质随数据携带）
--------------------------------------------------------------------------------

-- proper k-着色：色映射 c : V → Fin k + 相邻异色
Coloring : (G : Graph) (k : ℕ) → Set
Coloring G k = Σ (V G → Fin k) (λ c → ∀ {x y} → adj G x y → ¬ (c x ≡ c y))

TwoColoring : (G : Graph) → Set
TwoColoring G = Coloring G 2

--------------------------------------------------------------------------------
-- §2 主引理层：Bool ⇄ Fin 2 桥 + Bipartite 对齐
--------------------------------------------------------------------------------

-- Bool → Fin 2（Bipartite 的 Bool 色面 → Coloring 的 Fin 2 形）
cf2 : Bool → Fin 2
cf2 false  = fzero
cf2 true   = fsuc fzero

cf2-inj : ∀ b b' → cf2 b ≡ cf2 b' → b ≡ b'
cf2-inj false false  _ = refl
cf2-inj true  true   _ = refl
cf2-inj false true   e = ⊥-elim (fz≢fs e)
  where
  fz≢fs : ∀ {n} → fzero ≡ fsuc n → ⊥
  fz≢fs ()
cf2-inj true  false  e = ⊥-elim (fz≢fs (sym e))
  where
  fz≢fs : ∀ {n} → fzero ≡ fsuc n → ⊥
  fz≢fs ()

-- Bipartite ⟹ 2-着色（Bool 形直译——异色性经 cf2-inj 传递）
bipartite→2 : (G : Graph) → Bipartite G → TwoColoring G
bipartite→2 G (b , proper) = (λ x → cf2 (b x)) , λ {x} {y} h → λ e → proper h (cf2-inj _ _ e)

--------------------------------------------------------------------------------
-- §3 主引理层：K2 全证（2-色有 / 1-色无）
--------------------------------------------------------------------------------

cf2-Bit : Bit → Fin 2
cf2-Bit b0 = fzero
cf2-Bit b1 = fsuc fzero

proper-K2 : ∀ {x y} → adj2 x y → ¬ (cf2-Bit x ≡ cf2-Bit y)
proper-K2 {b0} {b1} _ ()
proper-K2 {b1} {b0} _ ()
proper-K2 {b0} {b0} h _ = ⊥-elim (h refl)
proper-K2 {b1} {b1} h _ = ⊥-elim (h refl)

color2-K2 : TwoColoring K2
color2-K2 = cf2-Bit , proper-K2

-- Fin 1 全元素 ≡ zero（1-色恒常形）
fin1-all : (n : Fin 1) → n ≡ fzero
fin1-all fzero    = refl
fin1-all (fsuc f) = ⊥-elim (noFin0 f)
  where
  noFin0 : Fin 0 → ⊥
  noFin0 ()

not-1-K2 : ¬ (Coloring K2 1)
not-1-K2 (c , proper) = proper neq01 (trans (fin1-all (c b0)) (sym (fin1-all (c b1))))

--------------------------------------------------------------------------------
-- §4 主引理层：K3 全证（3-色有 / 2-色无）
--------------------------------------------------------------------------------

data Tri : Set where
  t0 t1 t2 : Tri

adj3 : Tri → Tri → Set
adj3 x y = x ≡ y → ⊥

a01 : adj3 t0 t1
a01 ()

a02 : adj3 t0 t2
a02 ()

a12 : adj3 t1 t2
a12 ()

adj3-sym : ∀ {x y} → adj3 x y → adj3 y x
adj3-sym f e = f (sym e)

adj3-irrefl : ∀ {x} → adj3 x x → ⊥
adj3-irrefl f = f refl

K3 : Graph
K3 = record
  { V          = Tri
  ; adj        = adj3
  ; adj-sym    = adj3-sym
  ; adj-irrefl = adj3-irrefl
  }

cf3 : Tri → Fin 3
cf3 t0 = fzero
cf3 t1 = fsuc fzero
cf3 t2 = fsuc (fsuc fzero)

proper-K3 : ∀ {x y} → adj3 x y → ¬ (cf3 x ≡ cf3 y)
proper-K3 {t0} {t1} _ ()
proper-K3 {t0} {t2} _ ()
proper-K3 {t1} {t0} _ ()
proper-K3 {t1} {t2} _ ()
proper-K3 {t2} {t0} _ ()
proper-K3 {t2} {t1} _ ()
proper-K3 {t0} {t0} h _ = ⊥-elim (h refl)
proper-K3 {t1} {t1} h _ = ⊥-elim (h refl)
proper-K3 {t2} {t2} h _ = ⊥-elim (h refl)

color3-K3 : Coloring K3 3
color3-K3 = cf3 , proper-K3

-- Fin 2 三分点必有两点同色（构造性 pigeonhole——8 案消解）
eq-pair : (f : Tri → Fin 2) → (f t0 ≡ f t1) ⊎ (f t0 ≡ f t2) ⊎ (f t1 ≡ f t2)
eq-pair f with f t0 | f t1 | f t2
... | fzero       | fzero        | _           = inj₁ refl
... | fzero       | fsuc fzero   | fzero       = inj₂ (inj₁ refl)
... | fzero       | fsuc fzero   | fsuc fzero  = inj₂ (inj₂ refl)
... | fsuc fzero  | fzero        | fzero       = inj₂ (inj₂ refl)
... | fsuc fzero  | fzero        | fsuc fzero  = inj₂ (inj₁ refl)
... | fsuc fzero  | fsuc fzero   | _           = inj₁ refl

not-2-K3 : ¬ (Coloring K3 2)
not-2-K3 (c , proper) = helper (eq-pair c)
  where
  helper : (c t0 ≡ c t1) ⊎ (c t0 ≡ c t2) ⊎ (c t1 ≡ c t2) → ⊥
  helper (inj₁ e)        = proper a01 e
  helper (inj₂ (inj₁ e)) = proper a02 e
  helper (inj₂ (inj₂ e)) = proper a12 e

--------------------------------------------------------------------------------
-- §5 核对层
--------------------------------------------------------------------------------

check-color2-K2 : TwoColoring K2
check-color2-K2 = color2-K2

check-color3-K3 : Coloring K3 3
check-color3-K3 = color3-K3

check-not-1-K2 : ¬ (Coloring K2 1)
check-not-1-K2 = not-1-K2

check-not-2-K3 : ¬ (Coloring K3 2)
check-not-2-K3 = not-2-K3

-- 立界注记（§6——深件不硬拱）：
-- (i) 四色定理（平面图 4-着色——经典深件，远超本模块）；
-- (ii) 色数 χ(G) 的最小化形（k-着色存在性判定 + 下界估计）；
-- (iii) Brooks 定理（χ ≤ Δ 除完全图/奇圈）；
-- (iv) Bipartite ⟺ 2-着色的逆向（→ 方向已由本模块桥件覆盖一半——逆向需可构造二分）
