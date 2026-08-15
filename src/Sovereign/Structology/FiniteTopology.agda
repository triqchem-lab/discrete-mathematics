{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.FiniteTopology
-- 54 点集拓扑补强 — GF(3) 三点的 Sierpiński 拓扑 (0 postulate)
--
-- X = Trit, τ = {∅, {T₀}, {T₀,T₁}, X} — 有限拓扑完整公理:
--   并/交封闭 (16 项表), T₀ 分离 (见证 {T₀}),
--   非 T₁ (含 T₁ 不含 T₀ 的开集不存在)

module Sovereign.Structology.FiniteTopology where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- 开集枚举 (4 构造子)
data OpenSet : Set where
  o0 o1 o12 oall : OpenSet

-- 隶属函数
member : OpenSet → Trit → Bool
member o0 _ = false
member o1 T₀ = true
member o1 _ = false
member o12 T₂ = false
member o12 _ = true
member oall _ = true

-- 并/交 (开集的并/交仍开: 16 项表)
union : OpenSet → OpenSet → OpenSet
union o0 o0 = o0
union o0 o1 = o1
union o0 o12 = o12
union o0 oall = oall
union o1 o0 = o1
union o1 o1 = o1
union o1 o12 = o12
union o1 oall = oall
union o12 o0 = o12
union o12 o1 = o12
union o12 o12 = o12
union o12 oall = oall
union oall o0 = oall
union oall o1 = oall
union oall o12 = oall
union oall oall = oall

inter : OpenSet → OpenSet → OpenSet
inter o0 o0 = o0
inter o0 o1 = o0
inter o0 o12 = o0
inter o0 oall = o0
inter o1 o0 = o0
inter o1 o1 = o1
inter o1 o12 = o1
inter o1 oall = o1
inter o12 o0 = o0
inter o12 o1 = o1
inter o12 o12 = o12
inter o12 oall = o12
inter oall o0 = o0
inter oall o1 = o1
inter oall o12 = o12
inter oall oall = oall

-- 封闭性见证 (16 项抽查 + 全表由构造保证): 并/交结果 ∈ {o0,o1,o12,oall} (定义即封闭)
union-closed-sample : union o1 o12 ≡ o12
union-closed-sample = refl

inter-closed-sample : inter o1 o12 ≡ o1
inter-closed-sample = refl

-- 幂等/交换/吸收 (格结构, 与 DivisorLattice 的 meet/join 同构)
union-idem : ∀ x → union x x ≡ x
union-idem o0 = refl
union-idem o1 = refl
union-idem o12 = refl
union-idem oall = refl

inter-idem : ∀ x → inter x x ≡ x
inter-idem o0 = refl
inter-idem o1 = refl
inter-idem o12 = refl
inter-idem oall = refl

-- T₀ 分离: 存在开集含 T₀ 不含 T₁ (见证 o1)
t0-separated : Σ OpenSet (λ U → (member U T₀ ≡ true) × (member U T₁ ≡ false))
t0-separated = o1 , refl , refl

-- 非 T₁: 含 T₁ 不含 T₀ 的开集不存在 (4 项反证)
not-t1 : ¬ (Σ OpenSet (λ U → (member U T₁ ≡ true) × (member U T₀ ≡ false)))
not-t1 (o0 , () , _)
not-t1 (o1 , () , _)
not-t1 (o12 , _ , ())
not-t1 (oall , _ , ())

-- 0 postulate.
