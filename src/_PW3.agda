{-# OPTIONS --rewriting --guardedness #-}

-- | _PW3
-- 接线第三波：载体桥件（前两批 11 线后的硬面——承载对应定理）
--
-- 核心原则：
--   1. 载体桥 = 两个不同承载世界的**同值对账定理**（refl 级优先）+ 真实 import 边
--   2. 不改旧件语义（只引不改）
--   3. 桥① Kirchhoff×Matchings：Tri 组合度数（列表承载）≡ Laplacian 对角（矩阵承载）
--      桥② Ramsey×Colorings：Bool 边着色计数 ≡ Fin 2（cf2）载体计数（守恒）
--
-- 包含：idx3/eqTri/dec3/K3Graph/deg≡lap（桥①）· pentF/redU/redUF/redU-cons（桥②）

module _PW3 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Integer using (ℤ; +_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Sovereign.Topology.Graphs.GraphBasic using (Graph; V; adj; adj-sym; adj-irrefl; degree)
open import Sovereign.Topology.Graphs.Matchings using (Tri; t0; t1; t2; adj3; adj3-sym; adj3-irrefl)
open import Sovereign.Problem.Hodge.KirchhoffZ using (L)
open import Sovereign.Topology.Graphs.Colorings using (cf2)
open import Sovereign.Topology.Graphs.RamseyFinite using (isEdge5; pent; v0; v1; v2; v3; v4)

-- ────────────────────────────────────────────────────────────────────
-- §1 桥①：Tri 组合承载 ↔ Fin 3 矩阵承载（Kirchhoff 对角）
-- ────────────────────────────────────────────────────────────────────

-- 载体对应：Tri → Fin 3（组合顶点 → 矩阵行号）
idx3 : Tri → Fin 3
idx3 t0 = fzero
idx3 t1 = fsuc fzero
idx3 t2 = fsuc (fsuc fzero)

-- Tri 相等可判（9 case 穷举）
eqTri : (x y : Tri) → Dec (x ≡ y)
eqTri t0 t0 = yes refl
eqTri t0 t1 = no λ ()
eqTri t0 t2 = no λ ()
eqTri t1 t0 = no λ ()
eqTri t1 t1 = yes refl
eqTri t1 t2 = no λ ()
eqTri t2 t0 = no λ ()
eqTri t2 t1 = no λ ()
eqTri t2 t2 = yes refl

-- adj3 可判（x≢y ⟹ 邻接成立；x≡y ⟹ 不邻接）
dec3 : (x y : Tri) → Dec (adj3 x y)
dec3 x y with eqTri x y
... | yes p = no λ f → f p
... | no neq = yes neq

-- K3 作为 GraphBasic.Graph（关系入定义：adj3 + 对称 + 无自环）
K3Graph : Graph
K3Graph = record
  { V         = Tri
  ; adj       = adj3
  ; adj-sym   = adj3-sym
  ; adj-irrefl = adj3-irrefl
  }

-- 列表承载枚举（K3 顶点全表）
enum3 : List Tri
enum3 = t0 ∷ t1 ∷ t2 ∷ []

-- ★ 载体桥①主定理：K3 组合度数（GraphBasic 列表承载）≡ Kirchhoff Laplacian 对角（矩阵承载）
--   两边各自归约至 + 2——承载对应经 idx3，数值经 defeq 闭合
deg≡lap : (x : Tri) → + (degree K3Graph dec3 enum3 x) ≡ L (idx3 x) (idx3 x)
deg≡lap t0 = refl
deg≡lap t1 = refl
deg≡lap t2 = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 桥②：Ramsey Bool 边着色承载 ↔ Colorings Fin 2 值承载（cf2 守恒）
-- ────────────────────────────────────────────────────────────────────

-- Ramsey 边着色的 Fin 2 值形（cf2 = Colorings 桥件直用——真实 import 边）
pentF : Fin 5 → Fin 5 → Fin 2
pentF i j = cf2 (pent i j)

-- cf2 保持边判定（Bool 载体 true ⟺ Fin 2 载体 fsuc fzero）
w3-cf2-edge : ∀ i j → pent i j ≡ true → pentF i j ≡ fsuc fzero
w3-cf2-edge i j e = cong cf2 e

w3-pentF-red : pentF v0 v1 ≡ fsuc fzero
w3-pentF-red = refl

w3-pentF-blue : pentF v0 v2 ≡ fzero
w3-pentF-blue = refl

-- 计数守恒：5-环红边数（无序对 10 项）在两承载世界同值
b2n : Bool → ℕ
b2n true  = 1
b2n false = 0

f2n : Fin 2 → ℕ
f2n fzero        = 0
f2n (fsuc fzero) = 1
f2n (fsuc (fsuc ()))

-- Bool 载体计数（isEdge5 无序对 10 项）
redU : ℕ
redU =
  b2n (isEdge5 0 1) + b2n (isEdge5 0 2) + b2n (isEdge5 0 3) + b2n (isEdge5 0 4) +
  b2n (isEdge5 1 2) + b2n (isEdge5 1 3) + b2n (isEdge5 1 4) +
  b2n (isEdge5 2 3) + b2n (isEdge5 2 4) + b2n (isEdge5 3 4)

-- Fin 2 载体计数（pentF 同 10 对）
redUF : ℕ
redUF =
  f2n (pentF v0 v1) + f2n (pentF v0 v2) + f2n (pentF v0 v3) + f2n (pentF v0 v4) +
  f2n (pentF v1 v2) + f2n (pentF v1 v3) + f2n (pentF v1 v4) +
  f2n (pentF v2 v3) + f2n (pentF v2 v4) + f2n (pentF v3 v4)

-- ★ 载体桥②a 守恒：两承载计数同值
redU-cons : redUF ≡ redU
redU-cons = refl

-- ★ 载体桥②b 内容锚：五边形恰 5 条红边（R(3,3)>5 下界见证的计数面）
redU-5 : redU ≡ 5
redU-5 = refl

-- ────────────────────────────────────────────────────────────────────
-- §3 余叶件查漏（如实注记）
--   Flows/TuringMachine/FiniteModelTheory/RelationClosures/WellFounded/QuotientBasic
--   仍为叶——自然桥候选：Flows×Trees（流分解立界面）/TM×DFA（等价深件）/
--   FMT×PropositionalLogic（语义衔接深件）/逻辑组×Finiteness（Dec 消费面）——
--   均涉深件或需新机件，无 defeq 级自然桥，如实列不硬造。
-- ────────────────────────────────────────────────────────────────────
