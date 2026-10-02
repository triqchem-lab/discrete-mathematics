{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.Finiteness.Dedekind
-- 任务书第一层·1.1 P0-a：型有限 ⟹ Dedekind 有限（构造性，可证）
--
-- 数学背景：Dedekind (1888) Definition 64。在构造性类型论中「有限」被重新定义为
--   型有限，Dedekind 定义变成一条**需要证明的定理**（本模块）。
--   反向（Dedekind ⟹ 型有限）在构造性逻辑下不成立 —— 缺口声明在 FinitenessZoo §5。
--
-- 证明路线（0 postulate）：把 f 沿 ≃ 搬运到 Fin n（f' = to ∘ f ∘ from），
--   用 FiniteDynamics.injSurj（Fin n 上单射→满射，Dedekind 有限性的构造性实例）
--   得满射，再搬运回来；两处往返式（from-to / to-from）闭合。
--   InjA/SurjA 与 FiniteDynamics.Inj/Surj 在 Fin n 上定义同形 ⇒ injSurj 直接消费。
--
-- 0 postulate / 0 hole。
module Sovereign.Analysis.Finiteness.Dedekind where

open import Data.Fin using (Fin)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)
open import Sovereign.Structology.PlatonicTorusProjection using (_≃_)
open import Sovereign.Analysis.FiniteDynamics using (injSurj)
open import Sovereign.Analysis.Finiteness.Foundations
  using (InjA; DedekindFinite; Finite; ≃-to-inj; ≃-from-inj)

-- 主定理（任务书 P0-a）
finite→dedekindFinite : ∀ {A : Set} → Finite A → DedekindFinite A
finite→dedekindFinite {A} (n , e) f injF i = j , prf
  where
    f' : Fin n → Fin n
    f' x = _≃_.to e (f (_≃_.from e x))
    f'-inj : InjA f'
    f'-inj x y eq = ≃-from-inj e x y (injF _ _ (≃-to-inj e _ _ eq))
    x₀ : Fin n
    x₀ = proj₁ (injSurj f' f'-inj (_≃_.to e i))
    hit : f' x₀ ≡ _≃_.to e i
    hit = proj₂ (injSurj f' f'-inj (_≃_.to e i))
    j : A
    j = _≃_.from e x₀
    prf : f j ≡ i
    prf = trans (sym (_≃_.from-to e (f j))) (trans (cong (_≃_.from e) hit) (_≃_.from-to e i))
