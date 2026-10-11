{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteEMIdentityChecks
-- 离散 EM 恒等式（d²=0 族）的跨域实例核对件汇（波 2-C 检查件外移）。
--
-- 数学背景：curl∘grad=0 与 div∘curl=0 两条恒等式（真证明在 DiscreteEMField3D/DiscreteEMCore）
-- 的「定理命名面」——原居 Topology/DeRhamComplex 与 Topology/HomologicalAlgebra（纯委托
-- wrapper 族），属「定理模块调实例核对」型错位边；迁至 Physics 侧独立检查件模块（同层合法）。
--
-- 核心原则：
--   1. 本模块只承载委托/核对面（wrapper = 上游恒等式的命名引用），不新增数学内容；
--   2. 两源模块的 d-squared-zero 同名——Homological 形改名 d-squared-zero-hom（零消费者实证）；
--   3. Topology 两件保留头注与迁移指针，零 Physics 依赖。
--
-- 包含：§1 de Rham 形（curl-grad-zero-full/div-curl-zero-full/d-squared-zero/de-rham-complex）
--       §2 同调形（chain-complex/d-squared-zero-hom/grad-in-ker-curl/curl-in-ker-div）

module Sovereign.Physics.DiscreteEMIdentityChecks where

open import Data.Fin using (Fin) renaming (zero to fz)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Sovereign.Physics.DiscreteEMField3D
  using (GF3; ScalarField; VectorField; grad; curl; div; curl-grad-zero)
open import Sovereign.Physics.DiscreteEMCore using (div-curl-zero)

---------------------------------------------------------------------------------
-- §1. de Rham 形（自 Topology/DeRhamComplex 迁入——波 2-C）
---------------------------------------------------------------------------------

curl-grad-zero-full : ∀ φ p → curl (grad φ) p ≡ (fz , fz , fz)
curl-grad-zero-full = curl-grad-zero

div-curl-zero-full : ∀ A p → div (curl A) p ≡ fz
div-curl-zero-full = div-curl-zero

d-squared-zero :
  (∀ A p → div (curl A) p ≡ fz)
  × (∀ φ p → curl (grad φ) p ≡ (fz , fz , fz))
d-squared-zero = div-curl-zero , curl-grad-zero

de-rham-complex :
  (∀ φ p → curl (grad φ) p ≡ (fz , fz , fz))
  ×
  (∀ A p → div (curl A) p ≡ fz)
de-rham-complex = curl-grad-zero , div-curl-zero

---------------------------------------------------------------------------------
-- §2. 同调形（自 Topology/HomologicalAlgebra 迁入——波 2-C；d-squared-zero 同名改 -hom）
---------------------------------------------------------------------------------

chain-complex :
  (∀ φ p → curl (grad φ) p ≡ (fz , fz , fz))
  × (∀ A p → div (curl A) p ≡ fz)
chain-complex = curl-grad-zero , div-curl-zero

d-squared-zero-hom :
  (∀ A p → div (curl A) p ≡ fz)
  × (∀ φ p → curl (grad φ) p ≡ (fz , fz , fz))
d-squared-zero-hom = div-curl-zero , curl-grad-zero

grad-in-ker-curl : ∀ φ p → curl (grad φ) p ≡ (fz , fz , fz)
grad-in-ker-curl = curl-grad-zero

curl-in-ker-div : ∀ A p → div (curl A) p ≡ fz
curl-in-ker-div = div-curl-zero
