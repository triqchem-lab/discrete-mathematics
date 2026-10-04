{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.AtkinQAnalysis
-- 任务书第二层·2.3：Atkin Q-analysis 与离散同伦（1970s）的构造性核
--
-- 数学背景：Atkin, "From cohomology in physics to q-connectivity in social
--   science"（Int. J. Man-Machine Studies 4 (1972), 341–362）首次把同伦直觉
--   移植到单纯复形上：两个 p-单形共享 q-面则 q-连通；Q-analysis 用连通分量的
--   「洞」刻画组合结构的结构性断裂。本模块给出其**顶点层（q = 0）**的
--   构造性形式化：复形 1-骨架的连通性 = 边关系上的自反传递闭包（路径）。
--
-- ⚠ 诚实边界：
--   1. 一般 q 层（共享 q-面的 p-单形链、按维数分层的连通分量）需要单纯形
--      编码（Fin (k+1) → Fin n 单调映射族），是 roadmap——本模块锁 q = 0 层。
--   2. Atkin 的 shomotopy（伪同伦）同样依赖一般单形族，不入本模块。
--   3. 顶点层 q-连通与 GaoYangRigidLock 的动力学核、AlexandroffFinite 的
--      偏序集拓扑互补：三者覆盖「离散同伦」任务书层的定义性基建。
--   4. 【本地资产接线】路径代数谱系：`HoTT/HomotopyPi1.agda` 的 PathAlg record
--      （复合 ∘p + 单位 ε + 逆 inv + 结合/单位/逆三律，π₁(T⁶) = 格点加法实例）
--      是**代数结构层**；本模块 Path 是**可达性关系层**（归纳两构造，供
--      bottom-connects 等消费）——互补不重复：代数律挂 PathAlg，可达性判定挂本层。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.AtkinQAnalysis where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Function.Base using (_∘_)

--------------------------------------------------------------------------------
-- §1. 复形 1-骨架：对称边谓词
--------------------------------------------------------------------------------

record Graph (n : ℕ) : Set₁ where
  field
    Edge     : Fin n → Fin n → Set
    Edge-sym : ∀ x y → Edge x y → Edge y x

--------------------------------------------------------------------------------
-- §2. 顶点层 q-连通：路径（自反传递闭包，两构造子）
--------------------------------------------------------------------------------

data Path {n : ℕ} (E : Fin n → Fin n → Set) : Fin n → Fin n → Set where
  nil  : ∀ x → Path E x x
  cons : ∀ x y z → E x y → Path E y z → Path E x z

-- 自反
path-refl : ∀ {n} {E : Fin n → Fin n → Set} x → Path E x x
path-refl x = nil x

-- 传递（拼接；无需对称律）
path-trans : ∀ {n} {E : Fin n → Fin n → Set} {x y z} →
  Path E x y → Path E y z → Path E x z
path-trans (nil x) q = q
path-trans (cons x w y e p) q = cons x w _ e (path-trans p q)

--------------------------------------------------------------------------------
-- §3. Atkin 定理：边的两端点 q-连通（共享 0-面的 1-单形彼此 0-连通）
--
-- 对称律在 Graph 层给出（Edge-sym 字段）；裸 Path 上无对称（构造性事实：
-- 对称需要边谓词自身对称，不自由）。
--------------------------------------------------------------------------------

edge-connects : ∀ {n} {E : Fin n → Fin n → Set} {x y} → E x y → Path E x y
edge-connects {x = x} {y = y} e = cons x y y e (nil y)

path-symₘ : ∀ {n} (G : Graph n) {x y} → Path (Graph.Edge G) x y → Path (Graph.Edge G) y x
path-symₘ G (nil x) = nil x
path-symₘ G (cons x y z e p) =
  path-trans (path-symₘ G p)
             (cons y x x (Graph.Edge-sym G x y e) (nil x))

path-transₘ : ∀ {n} (G : Graph n) {x y z} →
  Path (Graph.Edge G) x y → Path (Graph.Edge G) y z → Path (Graph.Edge G) x z
path-transₘ G (nil x) q = q
path-transₘ G (cons x w y e p) q = cons x w _ e (path-transₘ G p q)

--------------------------------------------------------------------------------
-- §4. 具体点对抗（对抗验证协议 §6）：K₃ 完全图
--
-- Edge = x ≢ y（对称性由 ≢ 的对称 + ≡ 的对称给出）；
-- 0 → 2 有显式路径 0 → 1 → 2（两步边）。
--------------------------------------------------------------------------------

tri : Graph 3
tri = record
  { Edge     = λ x y → x ≢ y
  ; Edge-sym = λ x y h → h ∘ sym
  }

tri-0-1 : Graph.Edge tri fzero (fsuc fzero)
tri-0-1 = λ ()

tri-1-2 : Graph.Edge tri (fsuc fzero) (fsuc (fsuc fzero))
tri-1-2 = λ ()

-- 显式路径：0 → 1 → 2
tri-path-0-1-2 :
  Path (Graph.Edge tri) fzero (fsuc (fsuc fzero))
tri-path-0-1-2 =
  cons fzero (fsuc fzero) (fsuc (fsuc fzero))
       tri-0-1
       (cons (fsuc fzero) (fsuc (fsuc fzero)) (fsuc (fsuc fzero))
             tri-1-2 (nil (fsuc (fsuc fzero))))

-- 对抗回证：路径的对称给出 2 → 0
tri-path-2-0 :
  Path (Graph.Edge tri) (fsuc (fsuc fzero)) fzero
tri-path-2-0 = path-symₘ tri tri-path-0-1-2
