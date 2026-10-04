{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.BoundaryGF3
-- 任务书第四层·4.2 链复形接线（最小核）：三角形 ∂² = 0 的 GF(3) 构造性实例
--
-- 数学背景：链复形公理 ∂² = 0（边界之边界为零）是离散 Hodge 理论的地基
--   （Eckmann 1944/45；本库任务书 §4.2 的链复形方向）。本模块给出最小完备
--   实例：三角形（3 顶点 0,1,2 / 3 有向边 01,12,20）上的
--     ∂₁ : 边链 (GF(3))³ → 顶点链 (GF(3))³（每顶点 = 入边系数 ⊖ 出边系数），
--     ∂₀ : 顶点链 → 系数和（0-链 → (−1)-链），
--   并证明 ∂₀ (∂₁ e) ≡ T₀ 对任意边链——即 ∂² = 0 在 1→0→(−1) 截面成立。
--
-- 证明策略：配对弹出（docs/techniques/pair-popping.md，相消型）——
--   和式 (f a ⊕ b) ⊕ (f b ⊕ c) ⊕ (f c ⊕ f? a) 中每对 (x, f x) 经
--   交换结合重排相消；零件 = Base/Trit 已证的 ⊕-comm/assoc/inverse/identityˡ。
--
-- ⚠ 诚实边界 + 本地资产接线：
--   1. 【上游已有】∂₁∘∂₂ = 0（面→边→顶点两层边界）已由
--      `Algebra/Jacobian/jac_Topology.agda` §2 闭合（入射矩阵 M_∂ + GF(3) 消元
--      rank/nullity 双侧证书）；同调维数接口 = `Problem/Hodge/ChainComplex.agda`
--      的 ChainComplex 记录 + dimH（tri 实例 H₀ = H₁ = 1）。本模块补 jac_Topology
--      没有的 **∂₀ 求和截面**（0-链 → (−1)-链），与上游互补、不重复造轮。
--   2. 一般 n 的 ∂₁/∂₂ 与完整 Eckmann 分解是 roadmap（矩阵机件接 jac_Topology）。
--   3. H₁ ≠ 0 的非边缘闭链见证（同调非平凡性）是 roadmap——本模块只证 ∂² = 0。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.BoundaryGF3 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; _⊕_; negate; ⊕-comm; ⊕-assoc; ⊕-inverse; ⊕-identityˡ)
open import Sovereign.Problem.Hodge.EckmannGF3 using (V3; zeroV)

--------------------------------------------------------------------------------
-- §1. 三角形边界算子
--
-- 边索引：0 = 边 01，1 = 边 12，2 = 边 20（定向三角形）。
-- 顶点链第 v 分量 = 入边系数 ⊕ negate（出边系数）：
--   v0 = f e2 ⊕ e0（e20 入，e01 出）；v1 = f e0 ⊕ e1；v2 = f e1 ⊕ e2。
--------------------------------------------------------------------------------

∂₁ : V3 → V3
∂₁ e fzero = negate (e (fsuc (fsuc fzero))) ⊕ e fzero
∂₁ e (fsuc fzero) = negate (e fzero) ⊕ e (fsuc fzero)
∂₁ e (fsuc (fsuc fzero)) = negate (e (fsuc fzero)) ⊕ e (fsuc (fsuc fzero))

-- ∂₀：0-链 → (−1)-链 = 系数和
∂₀ : V3 → Trit
∂₀ c = (c fzero ⊕ c (fsuc fzero)) ⊕ c (fsuc (fsuc fzero))

--------------------------------------------------------------------------------
-- §2. 零件引理（配对弹出）
--------------------------------------------------------------------------------

-- 单对相消：(f x ⊕ y) ⊕ (f y ⊕ x) ≡ 0 —— 一对有向边首尾相接的边界为零
pairwise : ∀ x y → (negate x ⊕ y) ⊕ (negate y ⊕ x) ≡ T₀
pairwise x y = begin
  (negate x ⊕ y) ⊕ (negate y ⊕ x)
  ≡⟨ ⊕-assoc (negate x) y (negate y ⊕ x) ⟩
  negate x ⊕ (y ⊕ (negate y ⊕ x))
  ≡⟨ cong (λ w → negate x ⊕ w) (sym (⊕-assoc y (negate y) x)) ⟩
  negate x ⊕ ((y ⊕ negate y) ⊕ x)
  ≡⟨ cong (λ w → negate x ⊕ (w ⊕ x)) (⊕-inverse y) ⟩
  negate x ⊕ (T₀ ⊕ x)
  ≡⟨ cong (negate x ⊕_) (⊕-identityˡ x) ⟩
  negate x ⊕ x
  ≡⟨ ⊕-comm (negate x) x ⟩
  x ⊕ negate x
  ≡⟨ ⊕-inverse x ⟩
  T₀ ∎

-- 邻对前移：(f x ⊕ y) ⊕ (f y ⊕ z) ≡ f x ⊕ z —— 中点 y 的入出相消
shift : ∀ x y z → (negate x ⊕ y) ⊕ (negate y ⊕ z) ≡ negate x ⊕ z
shift x y z = begin
  (negate x ⊕ y) ⊕ (negate y ⊕ z)
  ≡⟨ ⊕-assoc (negate x) y (negate y ⊕ z) ⟩
  negate x ⊕ (y ⊕ (negate y ⊕ z))
  ≡⟨ cong (λ w → negate x ⊕ w) (sym (⊕-assoc y (negate y) z)) ⟩
  negate x ⊕ ((y ⊕ negate y) ⊕ z)
  ≡⟨ cong (λ w → negate x ⊕ (w ⊕ z)) (⊕-inverse y) ⟩
  negate x ⊕ (T₀ ⊕ z)
  ≡⟨ cong (negate x ⊕_) (⊕-identityˡ z) ⟩
  negate x ⊕ z
  ∎

--------------------------------------------------------------------------------
-- §3. 主定理：∂₀ (∂₁ e) ≡ T₀ 对任意边链（∂² = 0，0 维截面）
--
-- ∂₀(∂₁ e) = (P ⊕ Q) ⊕ R，P = f e2 ⊕ e0, Q = f e0 ⊕ e1, R = f e1 ⊕ e2。
-- shift e0 e1 e2 : P ⊕ Q ≡ f e2 ⊕ e1；pairwise e2 e1 : (f e2 ⊕ e1) ⊕ (f e1 ⊕ e2) ≡ 0。
--------------------------------------------------------------------------------

boundary-null : ∀ e → ∂₀ (∂₁ e) ≡ T₀
boundary-null e = begin
  (∂₁ e fzero ⊕ ∂₁ e (fsuc fzero)) ⊕ ∂₁ e (fsuc (fsuc fzero))
  ≡⟨ cong₂ _⊕_ (shift (e (fsuc (fsuc fzero))) (e fzero) (e (fsuc fzero)))
               refl ⟩
  ((negate (e (fsuc (fsuc fzero))) ⊕ e (fsuc fzero)) ⊕
   ∂₁ e (fsuc (fsuc fzero)))
  ≡⟨ pairwise (e (fsuc (fsuc fzero))) (e (fsuc fzero)) ⟩
  T₀ ∎

--------------------------------------------------------------------------------
-- §4. 具体点对抗（对抗验证协议 §6）：全 1 圈链
--
-- 三角形定向圈链 e = (1,1,1)：每顶点边界 = f 1 ⊕ 1 = 2 ⊕ 1 = 0 —— 闭链；
-- ∂₀(∂₁ e) = 0 具体点实例。
--------------------------------------------------------------------------------

loop1 : V3
loop1 _ = T₁

-- 圈链是闭 1-链：三个顶点分量全为零（独立 refl，不经 boundary-null）
loop1-closed-v0 : ∂₁ loop1 fzero ≡ T₀
loop1-closed-v0 = refl

loop1-closed-v1 : ∂₁ loop1 (fsuc fzero) ≡ T₀
loop1-closed-v1 = refl

loop1-closed-v2 : ∂₁ loop1 (fsuc (fsuc fzero)) ≡ T₀
loop1-closed-v2 = refl

-- 定理在圈链上的实例化
loop1-boundary-null : ∂₀ (∂₁ loop1) ≡ T₀
loop1-boundary-null = boundary-null loop1

-- 对照：非圈链（只走边 01）在顶点 1 留下 −1 ≠ 0 —— ∂₁ 不是零映射
open1 : V3
open1 fzero = T₁
open1 _ = T₀

open1-not-closed : ¬ (∂₁ open1 (fsuc fzero) ≡ T₀)
open1-not-closed = λ ()
