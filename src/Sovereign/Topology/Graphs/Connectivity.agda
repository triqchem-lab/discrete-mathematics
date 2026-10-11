{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.Connectivity
-- 图连通性基础（Mathlib SimpleGraph.Connectivity 对标）
--
-- 数学背景：可达关系 = 邻接的自反传递闭包；连通分支 = 顶点集对可达关系的商
--   （π₀ = V / Reachable——SetQuotient 形）；割点/桥 = 删点/删边后的不可达判据；
--   二分 = Bool 二着色（邻接顶点异色）。
--   本模块是任务池 T-2 批第二件（缺面清单 §四 Connectivity 原子分解五件）。
--
-- 核心原则：
-- 1. 关系入定义（Reachable = reflR/stepR 归纳构造——自反传递闭包的生成方式）
-- 2. 双≡世界分导入（PropEq ≡ 供 GraphBasic 语义面；Cubical Path ≡ᶜ 供商面 eq/）
-- 3. 0 postulate / 0 hole；商面良定义经 eq/（HIT 承载，不自证等价关系包）
--
-- 包含：Reachable（自反传递闭包）· Connected · π₀ 分支商 · 割点/桥判据
--       · Bipartite 二着色 · 核对层（K2 全项）

module Sovereign.Topology.Graphs.Connectivity where

open import Agda.Builtin.Equality using (_≡_) renaming (refl to reflᴾ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

-- 双≡世界分导入（第四案范式）：商面用 Cubical Path（≡ᶜ），语义面保留 PropEq ≡
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)

open import Sovereign.Topology.Graphs.GraphBasic
  using (Graph; V; adj; adj-sym; adj-irrefl; subGraph; removeV; removeEdge; K2)

--------------------------------------------------------------------------------
-- §1 基础件层：可达关系（自反传递闭包——关系入定义）
--------------------------------------------------------------------------------

data Reachable (G : Graph) : V G → V G → Set where
  reflR : ∀ x → Reachable G x x
  stepR : ∀ {x y z} → adj G x y → Reachable G y z → Reachable G x z

-- 传递（导出件——归纳于第一段）
reachable-trans :
    {G : Graph} {x y z : V G}
  → Reachable G x y → Reachable G y z → Reachable G x z
reachable-trans (reflR _) q = q
reachable-trans (stepR e p) q = stepR e (reachable-trans p q)

-- 对称（导出件——边对称性 lift；数学理由：无向图的路可逆走）
reachable-sym :
    {G : Graph} {x y : V G}
  → Reachable G x y → Reachable G y x
reachable-sym {G} (reflR x) = reflR x
reachable-sym {G} {u} {v} (stepR e p) =
  reachable-trans (reachable-sym p) (stepR (adj-sym G e) (reflR u))

--------------------------------------------------------------------------------
-- §2 主引理层：连通性与分支商
--------------------------------------------------------------------------------

-- 连通（逐点形——无 funext 纪律）
Connected : (G : Graph) → Set
Connected G = ∀ x y → Reachable G x y

-- 分支商：顶点集对可达关系的商（SetQuotient 承载）
π₀ : (G : Graph) → Set
π₀ G = V G / Reachable G

-- 分支类投射（显式钉 A/R——[_] 隐式阻塞绕开）
classOf : (G : Graph) → V G → π₀ G
classOf G x = [_] {A = V G} {R = Reachable G} x

-- 良定义核（Component 良定义——eq/ 直给，隐式 A/R 显式钉）
quot-def : (G : Graph) (x y : V G) → Reachable G x y → classOf G x ≡ᶜ classOf G y
quot-def G x y r = eq/ {A = V G} {R = Reachable G} x y r

-- 连通图的分支商单类（导出件）
connected-1class :
    (G : Graph) → Connected G → ∀ x y → classOf G x ≡ᶜ classOf G y
connected-1class G c x y = eq/ {A = V G} {R = Reachable G} x y (c x y)

--------------------------------------------------------------------------------
-- §3 主引理层：割点与桥（删点/删边后的不可达判据）
--------------------------------------------------------------------------------

-- x 分离 a b：G 中可达、删 x 后不可达
separates : (G : Graph) → (x a b : V G) → Set
separates G x a b = Reachable G a b × ¬ (Reachable (removeV G x) a b)

-- 割点：分离某对非 x 顶点
isCutVertex : (G : Graph) → V G → Set
isCutVertex G x =
  Σ (V G) (λ a → Σ (V G) (λ b → (a ≡ x → ⊥) × (b ≡ x → ⊥) × separates G x a b))

-- 桥：删该边后两端不可达
isBridge : (G : Graph) → (x y : V G) → Set
isBridge G x y = adj G x y × ¬ (Reachable (removeEdge G x y) x y)

--------------------------------------------------------------------------------
-- §4 主引理层：二分（Bool 二着色——关系入定义形）
--------------------------------------------------------------------------------

Bipartite : (G : Graph) → Set
Bipartite G = Σ (V G → Bool) (λ c → ∀ {x y} → adj G x y → ¬ (c x ≡ c y))

-- 子图继承二分（导出件——着色限制到 W）
bip-sub :
    (G : Graph) (W : V G → Set)
  → Bipartite G → Bipartite (subGraph G W)
bip-sub G W (c , badj) = (λ w → c (proj₁ w)) , (λ h → badj h)

--------------------------------------------------------------------------------
-- §5 核对层：K2 全项（Bool 二点——refl 级核对）
--------------------------------------------------------------------------------

-- Bool 归假形（具名件——两 case）
bool-false-not-true : {x : Bool} → (x ≡ true → ⊥) → x ≡ false
bool-false-not-true {true} nt = ⊥-elim (nt reflᴾ)
bool-false-not-true {false} _ = reflᴾ

true≢false : true ≡ false → ⊥
true≢false ()

-- 核对 1：K2 连通（4 case）
check-conn-K2 : Connected K2
check-conn-K2 true true = reflR true
check-conn-K2 true false = stepR (λ ()) (reflR false)
check-conn-K2 false true = stepR (λ ()) (reflR true)
check-conn-K2 false false = reflR false

-- 核对 2：K2 分支商单类（良定义核直调）
check-1class-K2 : ∀ x y → classOf K2 x ≡ᶜ classOf K2 y
check-1class-K2 x y = quot-def K2 x y (check-conn-K2 x y)

-- 核对 3：K2 无割点（反面核对——删任一点不破坏剩余可达）
check-nocut-K2 : isCutVertex K2 true → ⊥
check-nocut-K2 (true , b , na , nb , _) = na reflᴾ
check-nocut-K2 (false , true , _ , nb , _) = nb reflᴾ
check-nocut-K2 (false , false , _ , _ , _ , nreach) = nreach (reflR false)

-- 核对 4：K2 唯一边是桥（删边后两端不可达——4 case 无边 + 闭走归等）
rem-K2-noedge : ∀ u v → adj (removeEdge K2 true false) u v → ⊥
rem-K2-noedge true false (_ , np) = np (inj₁ (reflᴾ , reflᴾ))
rem-K2-noedge false true (_ , np) = np (inj₂ (reflᴾ , reflᴾ))
rem-K2-noedge true true (h , _) = h reflᴾ
rem-K2-noedge false false (h , _) = h reflᴾ

rem-K2-reach-eq : {u v : Bool} → Reachable (removeEdge K2 true false) u v → u ≡ v
rem-K2-reach-eq (reflR x) = reflᴾ
rem-K2-reach-eq (stepR e p) = ⊥-elim (rem-K2-noedge _ _ e)

check-bridge-K2 : isBridge K2 true false
check-bridge-K2 = (λ ()) , (λ r → true≢false (rem-K2-reach-eq r))

-- 核对 5：K2 二分（恒等着色）+ 子图继承
check-bip-K2 : Bipartite K2
check-bip-K2 = (λ x → x) , (λ h → h)

check-bip-sub-K2 : Bipartite (subGraph K2 (λ _ → ⊤))
check-bip-sub-K2 = bip-sub K2 (λ _ → ⊤) check-bip-K2
