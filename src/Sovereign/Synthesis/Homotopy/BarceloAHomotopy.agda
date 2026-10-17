{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.BarceloAHomotopy
-- 任务书 2.4：Barcelo/Babson A-homotopy——图映射同伦的组合近似（定义层 + 等价闭包）
--
-- 数学背景：A-homotopy 是图同伦的组合替代（Barcelo 1992 / Babson-Bennequin）——
--   walk 的 elementary 替换（邻边扩张/收缩）生成的等价关系，端点保持。
--   本模块立最小可证件：DiGraph + Walk + AStep（elementary move）+ AHomotopy（等价闭包）
--   + 自反/对称/传递 + 保持端点（类型级内建）。
--
-- 核心原则：
-- 1. 纯构造（data/record 形——零 mod-helper 零 literal 归纳）
-- 2. 结构即生成方式（AStep 生成元 + AHomotopy 等价闭包——展示群八要素的组合版）
-- 3. 诚实边界：A-homotopy 类的群结构（π₁^A）留后续层
--
-- 包含：DiGraph / Walk / AStep / AHomotopy / refl-sym-trans 三律

module Sovereign.Synthesis.Homotopy.BarceloAHomotopy where

open import Data.Empty using (⊥; ⊥-elim)

-- ────────────────────────────────────────────────────────────────────
-- §1. 有向图 + walk（相邻边见证的顶点链）
-- ────────────────────────────────────────────────────────────────────

record DiGraph : Set₁ where
  field
    V    : Set
    edge : V → V → Set

open DiGraph

-- walk：u 到 v 的边链（归纳构造——nil 自环 + cons 扩张）
data Walk (G : DiGraph) : V G → V G → Set where
  nil  : ∀ v → Walk G v v
  cons : ∀ {u v w} → edge G u v → Walk G v w → Walk G u w

-- ────────────────────────────────────────────────────────────────────
-- §2. walk 连接 + elementary A-homotopy（三角形边替换生成元）
-- ────────────────────────────────────────────────────────────────────

infixr 5 _++w_
_++w_ : ∀ {G : DiGraph} {u v w} → Walk G u v → Walk G v w → Walk G u w
nil v ++w q = q
cons e p ++w q = cons e (p ++w q)

-- elementary 生成元（Barcelo 三角形边替换）：
--   slide：p·(x→y)·(y→z)·b ⟶ p·(x→z)·b（(x,z) 边）
--   expand：反向
data AStep (G : DiGraph) : ∀ {u v} → Walk G u v → Walk G u v → Set where
  slide  : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v)
         → (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G x z)
         → AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
  expand : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v)
         → (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G x z)
         → AStep G (p ++w (cons e3 b)) (p ++w (cons e1 (cons e2 b)))

-- ────────────────────────────────────────────────────────────────────
-- §3. A-homotopy：AStep 的等价闭包（三律构造子保证等价关系）
-- ────────────────────────────────────────────────────────────────────

data AHomotopy (G : DiGraph) : ∀ {u v} → Walk G u v → Walk G u v → Set where
  refl'  : ∀ {u v} (w : Walk G u v) → AHomotopy G w w
  symm   : ∀ {u v} {w1 w2 : Walk G u v} → AHomotopy G w1 w2 → AHomotopy G w2 w1
  trans' : ∀ {u v} {w1 w2 w3 : Walk G u v} → AHomotopy G w1 w2 → AHomotopy G w2 w3 → AHomotopy G w1 w3
  gen    : ∀ {u v} {w1 w2 : Walk G u v} → AStep G w1 w2 → AHomotopy G w1 w2

-- 等价三律（引理形——下游可引）
AH-refl : ∀ {G : DiGraph} {u v} (w : Walk G u v) → AHomotopy G w w
AH-refl = refl'

AH-symm : ∀ {G : DiGraph} {u v} {w1 w2 : Walk G u v} → AHomotopy G w1 w2 → AHomotopy G w2 w1
AH-symm = symm

AH-trans : ∀ {G : DiGraph} {u v} {w1 w2 w3 : Walk G u v} → AHomotopy G w1 w2 → AHomotopy G w2 w3 → AHomotopy G w1 w3
AH-trans = trans'

-- AStep 包含（生成元 ⊆ 等价闭包）
AStep⊆AH : ∀ {G : DiGraph} {u v} {w1 w2 : Walk G u v} → AStep G w1 w2 → AHomotopy G w1 w2
AStep⊆AH = gen

-- 端点保持（类型级内建——AHomotopy 只在同端点 walk 间成立）
-- 匹配 Barcelo/Babson 的 A-homotopy 定义（任务书 2.4 定义层）
