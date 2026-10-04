{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.OrderComplexFaces
-- 任务书第二层·2.3 general q 层启动：序复形三角的 q 层数据
--
-- 数学背景：Atkin (1972) Q-analysis 的 general q 层——两个 p-单形
--   q-连通当且仅当它们共享一个 q-面。本模块给出序复形 K(lin3)
--   （3-元链的序复形 = 填充三角）的最小 q 层数据：
--
--   满链 tri = [0,1,2]（2-单形）的三个 1-面（删除一个顶点）：
--     face0 = [1,2]（删 0）、face1 = [0,2]（删 1）、face2 = [0,1]（删 2）
--   ①每个面是合法链（IsChain 2——序复形公理「面的面还是面」的面层实例）
--   ②三面两两顶点共享（q=0 共享数据，衔接 AtkinQ1 的边连通语义）
--   ③每面含于满链 tri（In 谓词枚举——面关系的基础层）
--
-- 技术要点：cubical 下 ℕ ≤ 的空类型裸 () 不可靠（深分裂陷阱）——
--   反向分支统一经 s≤z-elim（suc _ ≤ zero 的单层冲突，() 安全）与
--   s≤s-inv（剥一层 s≤s）组合导出 ⊥。
--
-- ⚠ 诚实边界：
--   1. 实例层（lin3 的唯一 2-单形）；一般 skip 删除算子 + 多单形复形
--      的泛型 q 层 roadmap（路径 A）。
--   2. q=1 的面共享层（共享 0-面）；更高 q（三角间共享边）需多三角
--      复形，roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.OrderComplexFaces where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.OrderComplex
  using (lin3; IsChain)

--------------------------------------------------------------------------------
-- §0. 算术矛盾助手（cubical 安全：单层冲突的 () + 引理化）
--------------------------------------------------------------------------------

s≤z-elim : ∀ {m : ℕ} → suc m ≤ zero → ⊥
s≤z-elim ()

s≤s-inv : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
s≤s-inv (s≤s p) = p

--------------------------------------------------------------------------------
-- §1. 三角形 2-单形：lin3 的满链 [0,1,2]（恒等函数）
--------------------------------------------------------------------------------

tri : Fin 3 → Fin 3
tri fzero = fzero
tri (fsuc fzero) = fsuc fzero
tri (fsuc (fsuc fzero)) = fsuc (fsuc fzero)

--------------------------------------------------------------------------------
-- §2. 三个 1-面（各删除一个顶点的子链，直接 λ 定义）
--------------------------------------------------------------------------------

-- face0 = [1,2]（删顶点 0）
face0 : Fin 2 → Fin 3
face0 fzero = fsuc fzero
face0 (fsuc fzero) = fsuc (fsuc fzero)

-- face1 = [0,2]（删顶点 1）
face1 : Fin 2 → Fin 3
face1 fzero = fzero
face1 (fsuc fzero) = fsuc (fsuc fzero)

-- face2 = [0,1]（删顶点 2）
face2 : Fin 2 → Fin 3
face2 fzero = fzero
face2 (fsuc fzero) = fsuc fzero

--------------------------------------------------------------------------------
-- §3. 面合法性：三个面都是 IsChain 2（序复形公理的面层实例化）
--
-- 每面四指标组合：一支有效（元素具体的 s≤s z≤n + λ ()）+ 三支矛盾
-- （h 经 s≤z-elim / s≤z-elim ∘ s≤s-inv 导出 ⊥，cubical 安全）。
--------------------------------------------------------------------------------

face0-chain : IsChain lin3 2 face0
face0-chain fzero (fsuc fzero) h = (s≤s z≤n , λ ())
face0-chain fzero fzero h = ⊥-elim (s≤z-elim h)
face0-chain (fsuc fzero) fzero h = ⊥-elim (s≤z-elim h)
face0-chain (fsuc fzero) (fsuc fzero) h = ⊥-elim (s≤z-elim (s≤s-inv h))

face1-chain : IsChain lin3 2 face1
face1-chain fzero (fsuc fzero) h = (z≤n , λ ())
face1-chain fzero fzero h = ⊥-elim (s≤z-elim h)
face1-chain (fsuc fzero) fzero h = ⊥-elim (s≤z-elim h)
face1-chain (fsuc fzero) (fsuc fzero) h = ⊥-elim (s≤z-elim (s≤s-inv h))

face2-chain : IsChain lin3 2 face2
face2-chain fzero (fsuc fzero) h = (z≤n , λ ())
face2-chain fzero fzero h = ⊥-elim (s≤z-elim h)
face2-chain (fsuc fzero) fzero h = ⊥-elim (s≤z-elim h)
face2-chain (fsuc fzero) (fsuc fzero) h = ⊥-elim (s≤z-elim (s≤s-inv h))

--------------------------------------------------------------------------------
-- §4. 顶点共享（q=0 共享数据）：三面两两共享顶点
--------------------------------------------------------------------------------

In : (Fin 2 → Fin 3) → Fin 3 → Set
In f v = (f fzero ≡ v) ⊎ (f (fsuc fzero) ≡ v)

-- face0=[1,2] 与 face1=[0,2] 共享顶点 2
share-f0-f1 : ∃-syntax (λ v → In face0 v × In face1 v)
share-f0-f1 = fsuc (fsuc fzero) , (inj₂ refl , inj₂ refl)

-- face1=[0,2] 与 face2=[0,1] 共享顶点 0
share-f1-f2 : ∃-syntax (λ v → In face1 v × In face2 v)
share-f1-f2 = fzero , (inj₁ refl , inj₁ refl)

-- face2=[0,1] 与 face0=[1,2] 共享顶点 1
share-f2-f0 : ∃-syntax (λ v → In face2 v × In face0 v)
share-f2-f0 = fsuc fzero , (inj₂ refl , inj₁ refl)

--------------------------------------------------------------------------------
-- §5. 面含于满链：三面的所有顶点都在 tri 中（面关系基础层）
--------------------------------------------------------------------------------

In-tri : Fin 3 → Set
In-tri v = (tri fzero ≡ v) ⊎ ((tri (fsuc fzero) ≡ v) ⊎ (tri (fsuc (fsuc fzero)) ≡ v))

subset-f0-tri : ∀ v → In face0 v → In-tri v
subset-f0-tri v (inj₁ h) = inj₂ (inj₁ h)
subset-f0-tri v (inj₂ h) = inj₂ (inj₂ h)

subset-f1-tri : ∀ v → In face1 v → In-tri v
subset-f1-tri v (inj₁ h) = inj₁ h
subset-f1-tri v (inj₂ h) = inj₂ (inj₂ h)

subset-f2-tri : ∀ v → In face2 v → In-tri v
subset-f2-tri v (inj₁ h) = inj₁ h
subset-f2-tri v (inj₂ h) = inj₂ (inj₁ h)
