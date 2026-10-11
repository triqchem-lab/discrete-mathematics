{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.RamseyFinite
-- 有限 Ramsey 定理面：2-着色泛型形 + R(3,3)=6 下界见证（五边形着色）
-- 数学背景：R(3,3)=6——任意 K₆ 的红/蓝 2-着色必含单色三角；
--   下界（>5）= K₅ 存在无单色三角着色（五边形环：红=五边形边、蓝=对角）。
--   上界（≤6）= 六人宴会定理（鸽巢论证）——深件立界。
--
-- 核心原则：
-- 1. Coloring2 = 边谓词函数形（true=红/false=蓝——确定性承载）
-- 2. mono3 = 三顶点同色判据（Bool 通道——计算面 refl 核对）
-- 3. 下界 = 十组三分量全核对（C(5,3)=10 枚举即全部——完备性注记）
-- 4. 0 postulate / 0 hole
--
-- 包含：Coloring2 · mono3 · pent（五边形着色）· 无单色三角十核对 · 立界注记

module Sovereign.Topology.Graphs.RamseyFinite where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- §1 2-着色与单色三角判据
Coloring2 : ℕ → Set
Coloring2 N = Fin N → Fin N → Bool

mono3 : ∀ {N} (c : Coloring2 N) → Fin N → Fin N → Fin N → Bool
mono3 c i j k = (c i j ∧ c i k ∧ c j k) ∨ (not (c i j) ∧ not (c i k) ∧ not (c j k))

-- §2 五边形着色（红 = 环边——isEdge5 查表；蓝 = 其余=对角）
isEdge5 : ℕ → ℕ → Bool
isEdge5 0 1 = true
isEdge5 1 0 = true
isEdge5 1 2 = true
isEdge5 2 1 = true
isEdge5 2 3 = true
isEdge5 3 2 = true
isEdge5 3 4 = true
isEdge5 4 3 = true
isEdge5 4 0 = true
isEdge5 0 4 = true
isEdge5 _ _ = false

pent : Coloring2 5
pent i j = isEdge5 (toℕ i) (toℕ j)

v0 v1 v2 v3 v4 : Fin 5
v0 = fzero
v1 = fsuc fzero
v2 = fsuc (fsuc fzero)
v3 = fsuc (fsuc (fsuc fzero))
v4 = fsuc (fsuc (fsuc (fsuc fzero)))

-- §3 无单色三角——十组三分量全核对（C(5,3)=10 即全部无序三元组）
no-mono-012 : mono3 pent v0 v1 v2 ≡ false
no-mono-012 = refl
no-mono-013 : mono3 pent v0 v1 v3 ≡ false
no-mono-013 = refl
no-mono-014 : mono3 pent v0 v1 v4 ≡ false
no-mono-014 = refl
no-mono-023 : mono3 pent v0 v2 v3 ≡ false
no-mono-023 = refl
no-mono-024 : mono3 pent v0 v2 v4 ≡ false
no-mono-024 = refl
no-mono-034 : mono3 pent v0 v3 v4 ≡ false
no-mono-034 = refl
no-mono-123 : mono3 pent v1 v2 v3 ≡ false
no-mono-123 = refl
no-mono-124 : mono3 pent v1 v2 v4 ≡ false
no-mono-124 = refl
no-mono-134 : mono3 pent v1 v3 v4 ≡ false
no-mono-134 = refl
no-mono-234 : mono3 pent v2 v3 v4 ≡ false
no-mono-234 = refl

-- §4 sanity：单色三角判据真形核对（K3 全红例——K3 全红三角必 mono）
allRed : Coloring2 3
allRed _ _ = true

check-mono-k3 : mono3 allRed fzero (fsuc fzero) (fsuc (fsuc fzero)) ≡ true
check-mono-k3 = refl

-- §5 立界注记（不设空壳签名）：R(3,3)=6 上界（六人宴会定理——鸽巢 ~80-150 行）／
-- 一般 R(m,n) 定义与存在性（Ramsey 定理——深件）／精确值表（R(4,3)=9 等——计算面）。
