{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Lie.LieAlgebra
-- 离散李代数 — GF(3) 上的括号结构完整形式化 (0 postulate)
--
-- 与 jac_LieGroup (Jacobian 家族) 分开的独立建立; 重复内容为有意为之。
--
-- 结构:
--   §1 局部 2×2 GF(3) 矩阵环 (对式 Mat2T: 加法/取负/乘法)
--   §2 李括号 [X,Y] = XY − YX: 基括号表 + 反称 (81 项穷举)
--      + Jacobi 恒等式 (729 项穷举 — 结合代数交换子恒等式,
--      逐项 refl 同时校验括号定义)
--   §3 三维旋量李代数 (so(3) 的 GF(3) 离散版): 循环括号
--      [x1,x2]=x3, [x2,x3]=x1, [x3,x1]=x2 — 反称 (9 项) + Jacobi (27 项)

module Sovereign.Algebra.Lie.LieAlgebra where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse;
  ⊗-comm; ⊗-assoc; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.GF27 using (negate-⊕)

--------------------------------------------------------------------------------
-- §1. 局部 2×2 GF(3) 矩阵环 (对式, 全归约)
--------------------------------------------------------------------------------

Mat2T : Set
Mat2T = (Trit × Trit) × (Trit × Trit)

mzero : Mat2T
mzero = (T₀ , T₀) , (T₀ , T₀)

mtadd : Mat2T → Mat2T → Mat2T
mtadd ((a , b) , (c , d)) ((e , f) , (g , h)) =
  ((a ⊕ e) , (b ⊕ f)) , ((c ⊕ g) , (d ⊕ h))

mtneg : Mat2T → Mat2T
mtneg ((a , b) , (c , d)) = ((negate a , negate b) , (negate c , negate d))

mtmul : Mat2T → Mat2T → Mat2T
mtmul ((a , b) , (c , d)) ((e , f) , (g , h)) =
  (((a ⊗ e) ⊕ (b ⊗ g)) , ((a ⊗ f) ⊕ (b ⊗ h))) ,
  (((c ⊗ e) ⊕ (d ⊗ g)) , ((c ⊗ f) ⊕ (d ⊗ h)))

-- 9 矩阵枚举 (构造子 — 供 81/729 项穷举模式匹配)
data M9 : Set where
  m0 m1 m2 m3 m4 m5 m6 m7 m8 : M9

toMat : M9 → Mat2T
toMat m0 = (T₀ , T₀) , (T₀ , T₀)
toMat m1 = (T₁ , T₀) , (T₀ , T₀)    -- E11
toMat m2 = (T₀ , T₁) , (T₀ , T₀)    -- E12
toMat m3 = (T₀ , T₀) , (T₁ , T₀)    -- E21
toMat m4 = (T₀ , T₀) , (T₀ , T₁)    -- E22
toMat m5 = (T₁ , T₀) , (T₀ , T₁)    -- I₂
toMat m6 = (T₁ , T₁) , (T₀ , T₀)    -- E11⊕E12
toMat m7 = (T₀ , T₀) , (T₁ , T₁)    -- E21⊕E22
toMat m8 = (T₁ , T₁) , (T₁ , T₁)    -- 全 1

--------------------------------------------------------------------------------
-- §2. 李括号 [X,Y] = XY − YX
--------------------------------------------------------------------------------

-- 减法即加法 (GF(3): −x = negate x)
br : Mat2T → Mat2T → Mat2T
br X Y = mtadd (mtmul X Y) (mtneg (mtmul Y X))

-- M9 上的括号 (经 toMat 归约)
brM : M9 → M9 → Mat2T
brM X Y = br (toMat X) (toMat Y)

-- 基括号表 ([E11,E12] = E12 等 — 标准 gl(2) 关系的 GF(3) 版)
br-E11-E12 : brM m1 m2 ≡ toMat m2 ; br-E11-E12 = refl
br-E11-E21 : brM m1 m3 ≡ mtneg (toMat m3) ; br-E11-E21 = refl
br-E12-E21 : brM m2 m3 ≡ mtadd (toMat m1) (mtneg (toMat m4)) ; br-E12-E21 = refl
br-I2-any : brM m5 m1 ≡ mzero ; br-I2-any = refl
br-I2-E12 : brM m5 m2 ≡ mzero ; br-I2-E12 = refl
br-E12-E12 : brM m2 m2 ≡ mzero ; br-E12-E12 = refl
-- 反称: [X,Y] + [Y,X] = 0 (81 项穷举)
asym : ∀ X Y → mtadd (brM X Y) (brM Y X) ≡ mzero
asym m0 m0 = refl
asym m0 m1 = refl
asym m0 m2 = refl
asym m0 m3 = refl
asym m0 m4 = refl
asym m0 m5 = refl
asym m0 m6 = refl
asym m0 m7 = refl
asym m0 m8 = refl
asym m1 m0 = refl
asym m1 m1 = refl
asym m1 m2 = refl
asym m1 m3 = refl
asym m1 m4 = refl
asym m1 m5 = refl
asym m1 m6 = refl
asym m1 m7 = refl
asym m1 m8 = refl
asym m2 m0 = refl
asym m2 m1 = refl
asym m2 m2 = refl
asym m2 m3 = refl
asym m2 m4 = refl
asym m2 m5 = refl
asym m2 m6 = refl
asym m2 m7 = refl
asym m2 m8 = refl
asym m3 m0 = refl
asym m3 m1 = refl
asym m3 m2 = refl
asym m3 m3 = refl
asym m3 m4 = refl
asym m3 m5 = refl
asym m3 m6 = refl
asym m3 m7 = refl
asym m3 m8 = refl
asym m4 m0 = refl
asym m4 m1 = refl
asym m4 m2 = refl
asym m4 m3 = refl
asym m4 m4 = refl
asym m4 m5 = refl
asym m4 m6 = refl
asym m4 m7 = refl
asym m4 m8 = refl
asym m5 m0 = refl
asym m5 m1 = refl
asym m5 m2 = refl
asym m5 m3 = refl
asym m5 m4 = refl
asym m5 m5 = refl
asym m5 m6 = refl
asym m5 m7 = refl
asym m5 m8 = refl
asym m6 m0 = refl
asym m6 m1 = refl
asym m6 m2 = refl
asym m6 m3 = refl
asym m6 m4 = refl
asym m6 m5 = refl
asym m6 m6 = refl
asym m6 m7 = refl
asym m6 m8 = refl
asym m7 m0 = refl
asym m7 m1 = refl
asym m7 m2 = refl
asym m7 m3 = refl
asym m7 m4 = refl
asym m7 m5 = refl
asym m7 m6 = refl
asym m7 m7 = refl
asym m7 m8 = refl
asym m8 m0 = refl
asym m8 m1 = refl
asym m8 m2 = refl
asym m8 m3 = refl
asym m8 m4 = refl
asym m8 m5 = refl
asym m8 m6 = refl
asym m8 m7 = refl
asym m8 m8 = refl

-- Jacobi: [[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0 (729 项穷举)
jacobi : ∀ X Y Z → mtadd (br (brM X Y) (toMat Z)) (mtadd (br (brM Y Z) (toMat X)) (br (brM Z X) (toMat Y))) ≡ mzero
jacobi m0 m0 m0 = refl
jacobi m0 m0 m1 = refl
jacobi m0 m0 m2 = refl
jacobi m0 m0 m3 = refl
jacobi m0 m0 m4 = refl
jacobi m0 m0 m5 = refl
jacobi m0 m0 m6 = refl
jacobi m0 m0 m7 = refl
jacobi m0 m0 m8 = refl
jacobi m0 m1 m0 = refl
jacobi m0 m1 m1 = refl
jacobi m0 m1 m2 = refl
jacobi m0 m1 m3 = refl
jacobi m0 m1 m4 = refl
jacobi m0 m1 m5 = refl
jacobi m0 m1 m6 = refl
jacobi m0 m1 m7 = refl
jacobi m0 m1 m8 = refl
jacobi m0 m2 m0 = refl
jacobi m0 m2 m1 = refl
jacobi m0 m2 m2 = refl
jacobi m0 m2 m3 = refl
jacobi m0 m2 m4 = refl
jacobi m0 m2 m5 = refl
jacobi m0 m2 m6 = refl
jacobi m0 m2 m7 = refl
jacobi m0 m2 m8 = refl
jacobi m0 m3 m0 = refl
jacobi m0 m3 m1 = refl
jacobi m0 m3 m2 = refl
jacobi m0 m3 m3 = refl
jacobi m0 m3 m4 = refl
jacobi m0 m3 m5 = refl
jacobi m0 m3 m6 = refl
jacobi m0 m3 m7 = refl
jacobi m0 m3 m8 = refl
jacobi m0 m4 m0 = refl
jacobi m0 m4 m1 = refl
jacobi m0 m4 m2 = refl
jacobi m0 m4 m3 = refl
jacobi m0 m4 m4 = refl
jacobi m0 m4 m5 = refl
jacobi m0 m4 m6 = refl
jacobi m0 m4 m7 = refl
jacobi m0 m4 m8 = refl
jacobi m0 m5 m0 = refl
jacobi m0 m5 m1 = refl
jacobi m0 m5 m2 = refl
jacobi m0 m5 m3 = refl
jacobi m0 m5 m4 = refl
jacobi m0 m5 m5 = refl
jacobi m0 m5 m6 = refl
jacobi m0 m5 m7 = refl
jacobi m0 m5 m8 = refl
jacobi m0 m6 m0 = refl
jacobi m0 m6 m1 = refl
jacobi m0 m6 m2 = refl
jacobi m0 m6 m3 = refl
jacobi m0 m6 m4 = refl
jacobi m0 m6 m5 = refl
jacobi m0 m6 m6 = refl
jacobi m0 m6 m7 = refl
jacobi m0 m6 m8 = refl
jacobi m0 m7 m0 = refl
jacobi m0 m7 m1 = refl
jacobi m0 m7 m2 = refl
jacobi m0 m7 m3 = refl
jacobi m0 m7 m4 = refl
jacobi m0 m7 m5 = refl
jacobi m0 m7 m6 = refl
jacobi m0 m7 m7 = refl
jacobi m0 m7 m8 = refl
jacobi m0 m8 m0 = refl
jacobi m0 m8 m1 = refl
jacobi m0 m8 m2 = refl
jacobi m0 m8 m3 = refl
jacobi m0 m8 m4 = refl
jacobi m0 m8 m5 = refl
jacobi m0 m8 m6 = refl
jacobi m0 m8 m7 = refl
jacobi m0 m8 m8 = refl
jacobi m1 m0 m0 = refl
jacobi m1 m0 m1 = refl
jacobi m1 m0 m2 = refl
jacobi m1 m0 m3 = refl
jacobi m1 m0 m4 = refl
jacobi m1 m0 m5 = refl
jacobi m1 m0 m6 = refl
jacobi m1 m0 m7 = refl
jacobi m1 m0 m8 = refl
jacobi m1 m1 m0 = refl
jacobi m1 m1 m1 = refl
jacobi m1 m1 m2 = refl
jacobi m1 m1 m3 = refl
jacobi m1 m1 m4 = refl
jacobi m1 m1 m5 = refl
jacobi m1 m1 m6 = refl
jacobi m1 m1 m7 = refl
jacobi m1 m1 m8 = refl
jacobi m1 m2 m0 = refl
jacobi m1 m2 m1 = refl
jacobi m1 m2 m2 = refl
jacobi m1 m2 m3 = refl
jacobi m1 m2 m4 = refl
jacobi m1 m2 m5 = refl
jacobi m1 m2 m6 = refl
jacobi m1 m2 m7 = refl
jacobi m1 m2 m8 = refl
jacobi m1 m3 m0 = refl
jacobi m1 m3 m1 = refl
jacobi m1 m3 m2 = refl
jacobi m1 m3 m3 = refl
jacobi m1 m3 m4 = refl
jacobi m1 m3 m5 = refl
jacobi m1 m3 m6 = refl
jacobi m1 m3 m7 = refl
jacobi m1 m3 m8 = refl
jacobi m1 m4 m0 = refl
jacobi m1 m4 m1 = refl
jacobi m1 m4 m2 = refl
jacobi m1 m4 m3 = refl
jacobi m1 m4 m4 = refl
jacobi m1 m4 m5 = refl
jacobi m1 m4 m6 = refl
jacobi m1 m4 m7 = refl
jacobi m1 m4 m8 = refl
jacobi m1 m5 m0 = refl
jacobi m1 m5 m1 = refl
jacobi m1 m5 m2 = refl
jacobi m1 m5 m3 = refl
jacobi m1 m5 m4 = refl
jacobi m1 m5 m5 = refl
jacobi m1 m5 m6 = refl
jacobi m1 m5 m7 = refl
jacobi m1 m5 m8 = refl
jacobi m1 m6 m0 = refl
jacobi m1 m6 m1 = refl
jacobi m1 m6 m2 = refl
jacobi m1 m6 m3 = refl
jacobi m1 m6 m4 = refl
jacobi m1 m6 m5 = refl
jacobi m1 m6 m6 = refl
jacobi m1 m6 m7 = refl
jacobi m1 m6 m8 = refl
jacobi m1 m7 m0 = refl
jacobi m1 m7 m1 = refl
jacobi m1 m7 m2 = refl
jacobi m1 m7 m3 = refl
jacobi m1 m7 m4 = refl
jacobi m1 m7 m5 = refl
jacobi m1 m7 m6 = refl
jacobi m1 m7 m7 = refl
jacobi m1 m7 m8 = refl
jacobi m1 m8 m0 = refl
jacobi m1 m8 m1 = refl
jacobi m1 m8 m2 = refl
jacobi m1 m8 m3 = refl
jacobi m1 m8 m4 = refl
jacobi m1 m8 m5 = refl
jacobi m1 m8 m6 = refl
jacobi m1 m8 m7 = refl
jacobi m1 m8 m8 = refl
jacobi m2 m0 m0 = refl
jacobi m2 m0 m1 = refl
jacobi m2 m0 m2 = refl
jacobi m2 m0 m3 = refl
jacobi m2 m0 m4 = refl
jacobi m2 m0 m5 = refl
jacobi m2 m0 m6 = refl
jacobi m2 m0 m7 = refl
jacobi m2 m0 m8 = refl
jacobi m2 m1 m0 = refl
jacobi m2 m1 m1 = refl
jacobi m2 m1 m2 = refl
jacobi m2 m1 m3 = refl
jacobi m2 m1 m4 = refl
jacobi m2 m1 m5 = refl
jacobi m2 m1 m6 = refl
jacobi m2 m1 m7 = refl
jacobi m2 m1 m8 = refl
jacobi m2 m2 m0 = refl
jacobi m2 m2 m1 = refl
jacobi m2 m2 m2 = refl
jacobi m2 m2 m3 = refl
jacobi m2 m2 m4 = refl
jacobi m2 m2 m5 = refl
jacobi m2 m2 m6 = refl
jacobi m2 m2 m7 = refl
jacobi m2 m2 m8 = refl
jacobi m2 m3 m0 = refl
jacobi m2 m3 m1 = refl
jacobi m2 m3 m2 = refl
jacobi m2 m3 m3 = refl
jacobi m2 m3 m4 = refl
jacobi m2 m3 m5 = refl
jacobi m2 m3 m6 = refl
jacobi m2 m3 m7 = refl
jacobi m2 m3 m8 = refl
jacobi m2 m4 m0 = refl
jacobi m2 m4 m1 = refl
jacobi m2 m4 m2 = refl
jacobi m2 m4 m3 = refl
jacobi m2 m4 m4 = refl
jacobi m2 m4 m5 = refl
jacobi m2 m4 m6 = refl
jacobi m2 m4 m7 = refl
jacobi m2 m4 m8 = refl
jacobi m2 m5 m0 = refl
jacobi m2 m5 m1 = refl
jacobi m2 m5 m2 = refl
jacobi m2 m5 m3 = refl
jacobi m2 m5 m4 = refl
jacobi m2 m5 m5 = refl
jacobi m2 m5 m6 = refl
jacobi m2 m5 m7 = refl
jacobi m2 m5 m8 = refl
jacobi m2 m6 m0 = refl
jacobi m2 m6 m1 = refl
jacobi m2 m6 m2 = refl
jacobi m2 m6 m3 = refl
jacobi m2 m6 m4 = refl
jacobi m2 m6 m5 = refl
jacobi m2 m6 m6 = refl
jacobi m2 m6 m7 = refl
jacobi m2 m6 m8 = refl
jacobi m2 m7 m0 = refl
jacobi m2 m7 m1 = refl
jacobi m2 m7 m2 = refl
jacobi m2 m7 m3 = refl
jacobi m2 m7 m4 = refl
jacobi m2 m7 m5 = refl
jacobi m2 m7 m6 = refl
jacobi m2 m7 m7 = refl
jacobi m2 m7 m8 = refl
jacobi m2 m8 m0 = refl
jacobi m2 m8 m1 = refl
jacobi m2 m8 m2 = refl
jacobi m2 m8 m3 = refl
jacobi m2 m8 m4 = refl
jacobi m2 m8 m5 = refl
jacobi m2 m8 m6 = refl
jacobi m2 m8 m7 = refl
jacobi m2 m8 m8 = refl
jacobi m3 m0 m0 = refl
jacobi m3 m0 m1 = refl
jacobi m3 m0 m2 = refl
jacobi m3 m0 m3 = refl
jacobi m3 m0 m4 = refl
jacobi m3 m0 m5 = refl
jacobi m3 m0 m6 = refl
jacobi m3 m0 m7 = refl
jacobi m3 m0 m8 = refl
jacobi m3 m1 m0 = refl
jacobi m3 m1 m1 = refl
jacobi m3 m1 m2 = refl
jacobi m3 m1 m3 = refl
jacobi m3 m1 m4 = refl
jacobi m3 m1 m5 = refl
jacobi m3 m1 m6 = refl
jacobi m3 m1 m7 = refl
jacobi m3 m1 m8 = refl
jacobi m3 m2 m0 = refl
jacobi m3 m2 m1 = refl
jacobi m3 m2 m2 = refl
jacobi m3 m2 m3 = refl
jacobi m3 m2 m4 = refl
jacobi m3 m2 m5 = refl
jacobi m3 m2 m6 = refl
jacobi m3 m2 m7 = refl
jacobi m3 m2 m8 = refl
jacobi m3 m3 m0 = refl
jacobi m3 m3 m1 = refl
jacobi m3 m3 m2 = refl
jacobi m3 m3 m3 = refl
jacobi m3 m3 m4 = refl
jacobi m3 m3 m5 = refl
jacobi m3 m3 m6 = refl
jacobi m3 m3 m7 = refl
jacobi m3 m3 m8 = refl
jacobi m3 m4 m0 = refl
jacobi m3 m4 m1 = refl
jacobi m3 m4 m2 = refl
jacobi m3 m4 m3 = refl
jacobi m3 m4 m4 = refl
jacobi m3 m4 m5 = refl
jacobi m3 m4 m6 = refl
jacobi m3 m4 m7 = refl
jacobi m3 m4 m8 = refl
jacobi m3 m5 m0 = refl
jacobi m3 m5 m1 = refl
jacobi m3 m5 m2 = refl
jacobi m3 m5 m3 = refl
jacobi m3 m5 m4 = refl
jacobi m3 m5 m5 = refl
jacobi m3 m5 m6 = refl
jacobi m3 m5 m7 = refl
jacobi m3 m5 m8 = refl
jacobi m3 m6 m0 = refl
jacobi m3 m6 m1 = refl
jacobi m3 m6 m2 = refl
jacobi m3 m6 m3 = refl
jacobi m3 m6 m4 = refl
jacobi m3 m6 m5 = refl
jacobi m3 m6 m6 = refl
jacobi m3 m6 m7 = refl
jacobi m3 m6 m8 = refl
jacobi m3 m7 m0 = refl
jacobi m3 m7 m1 = refl
jacobi m3 m7 m2 = refl
jacobi m3 m7 m3 = refl
jacobi m3 m7 m4 = refl
jacobi m3 m7 m5 = refl
jacobi m3 m7 m6 = refl
jacobi m3 m7 m7 = refl
jacobi m3 m7 m8 = refl
jacobi m3 m8 m0 = refl
jacobi m3 m8 m1 = refl
jacobi m3 m8 m2 = refl
jacobi m3 m8 m3 = refl
jacobi m3 m8 m4 = refl
jacobi m3 m8 m5 = refl
jacobi m3 m8 m6 = refl
jacobi m3 m8 m7 = refl
jacobi m3 m8 m8 = refl
jacobi m4 m0 m0 = refl
jacobi m4 m0 m1 = refl
jacobi m4 m0 m2 = refl
jacobi m4 m0 m3 = refl
jacobi m4 m0 m4 = refl
jacobi m4 m0 m5 = refl
jacobi m4 m0 m6 = refl
jacobi m4 m0 m7 = refl
jacobi m4 m0 m8 = refl
jacobi m4 m1 m0 = refl
jacobi m4 m1 m1 = refl
jacobi m4 m1 m2 = refl
jacobi m4 m1 m3 = refl
jacobi m4 m1 m4 = refl
jacobi m4 m1 m5 = refl
jacobi m4 m1 m6 = refl
jacobi m4 m1 m7 = refl
jacobi m4 m1 m8 = refl
jacobi m4 m2 m0 = refl
jacobi m4 m2 m1 = refl
jacobi m4 m2 m2 = refl
jacobi m4 m2 m3 = refl
jacobi m4 m2 m4 = refl
jacobi m4 m2 m5 = refl
jacobi m4 m2 m6 = refl
jacobi m4 m2 m7 = refl
jacobi m4 m2 m8 = refl
jacobi m4 m3 m0 = refl
jacobi m4 m3 m1 = refl
jacobi m4 m3 m2 = refl
jacobi m4 m3 m3 = refl
jacobi m4 m3 m4 = refl
jacobi m4 m3 m5 = refl
jacobi m4 m3 m6 = refl
jacobi m4 m3 m7 = refl
jacobi m4 m3 m8 = refl
jacobi m4 m4 m0 = refl
jacobi m4 m4 m1 = refl
jacobi m4 m4 m2 = refl
jacobi m4 m4 m3 = refl
jacobi m4 m4 m4 = refl
jacobi m4 m4 m5 = refl
jacobi m4 m4 m6 = refl
jacobi m4 m4 m7 = refl
jacobi m4 m4 m8 = refl
jacobi m4 m5 m0 = refl
jacobi m4 m5 m1 = refl
jacobi m4 m5 m2 = refl
jacobi m4 m5 m3 = refl
jacobi m4 m5 m4 = refl
jacobi m4 m5 m5 = refl
jacobi m4 m5 m6 = refl
jacobi m4 m5 m7 = refl
jacobi m4 m5 m8 = refl
jacobi m4 m6 m0 = refl
jacobi m4 m6 m1 = refl
jacobi m4 m6 m2 = refl
jacobi m4 m6 m3 = refl
jacobi m4 m6 m4 = refl
jacobi m4 m6 m5 = refl
jacobi m4 m6 m6 = refl
jacobi m4 m6 m7 = refl
jacobi m4 m6 m8 = refl
jacobi m4 m7 m0 = refl
jacobi m4 m7 m1 = refl
jacobi m4 m7 m2 = refl
jacobi m4 m7 m3 = refl
jacobi m4 m7 m4 = refl
jacobi m4 m7 m5 = refl
jacobi m4 m7 m6 = refl
jacobi m4 m7 m7 = refl
jacobi m4 m7 m8 = refl
jacobi m4 m8 m0 = refl
jacobi m4 m8 m1 = refl
jacobi m4 m8 m2 = refl
jacobi m4 m8 m3 = refl
jacobi m4 m8 m4 = refl
jacobi m4 m8 m5 = refl
jacobi m4 m8 m6 = refl
jacobi m4 m8 m7 = refl
jacobi m4 m8 m8 = refl
jacobi m5 m0 m0 = refl
jacobi m5 m0 m1 = refl
jacobi m5 m0 m2 = refl
jacobi m5 m0 m3 = refl
jacobi m5 m0 m4 = refl
jacobi m5 m0 m5 = refl
jacobi m5 m0 m6 = refl
jacobi m5 m0 m7 = refl
jacobi m5 m0 m8 = refl
jacobi m5 m1 m0 = refl
jacobi m5 m1 m1 = refl
jacobi m5 m1 m2 = refl
jacobi m5 m1 m3 = refl
jacobi m5 m1 m4 = refl
jacobi m5 m1 m5 = refl
jacobi m5 m1 m6 = refl
jacobi m5 m1 m7 = refl
jacobi m5 m1 m8 = refl
jacobi m5 m2 m0 = refl
jacobi m5 m2 m1 = refl
jacobi m5 m2 m2 = refl
jacobi m5 m2 m3 = refl
jacobi m5 m2 m4 = refl
jacobi m5 m2 m5 = refl
jacobi m5 m2 m6 = refl
jacobi m5 m2 m7 = refl
jacobi m5 m2 m8 = refl
jacobi m5 m3 m0 = refl
jacobi m5 m3 m1 = refl
jacobi m5 m3 m2 = refl
jacobi m5 m3 m3 = refl
jacobi m5 m3 m4 = refl
jacobi m5 m3 m5 = refl
jacobi m5 m3 m6 = refl
jacobi m5 m3 m7 = refl
jacobi m5 m3 m8 = refl
jacobi m5 m4 m0 = refl
jacobi m5 m4 m1 = refl
jacobi m5 m4 m2 = refl
jacobi m5 m4 m3 = refl
jacobi m5 m4 m4 = refl
jacobi m5 m4 m5 = refl
jacobi m5 m4 m6 = refl
jacobi m5 m4 m7 = refl
jacobi m5 m4 m8 = refl
jacobi m5 m5 m0 = refl
jacobi m5 m5 m1 = refl
jacobi m5 m5 m2 = refl
jacobi m5 m5 m3 = refl
jacobi m5 m5 m4 = refl
jacobi m5 m5 m5 = refl
jacobi m5 m5 m6 = refl
jacobi m5 m5 m7 = refl
jacobi m5 m5 m8 = refl
jacobi m5 m6 m0 = refl
jacobi m5 m6 m1 = refl
jacobi m5 m6 m2 = refl
jacobi m5 m6 m3 = refl
jacobi m5 m6 m4 = refl
jacobi m5 m6 m5 = refl
jacobi m5 m6 m6 = refl
jacobi m5 m6 m7 = refl
jacobi m5 m6 m8 = refl
jacobi m5 m7 m0 = refl
jacobi m5 m7 m1 = refl
jacobi m5 m7 m2 = refl
jacobi m5 m7 m3 = refl
jacobi m5 m7 m4 = refl
jacobi m5 m7 m5 = refl
jacobi m5 m7 m6 = refl
jacobi m5 m7 m7 = refl
jacobi m5 m7 m8 = refl
jacobi m5 m8 m0 = refl
jacobi m5 m8 m1 = refl
jacobi m5 m8 m2 = refl
jacobi m5 m8 m3 = refl
jacobi m5 m8 m4 = refl
jacobi m5 m8 m5 = refl
jacobi m5 m8 m6 = refl
jacobi m5 m8 m7 = refl
jacobi m5 m8 m8 = refl
jacobi m6 m0 m0 = refl
jacobi m6 m0 m1 = refl
jacobi m6 m0 m2 = refl
jacobi m6 m0 m3 = refl
jacobi m6 m0 m4 = refl
jacobi m6 m0 m5 = refl
jacobi m6 m0 m6 = refl
jacobi m6 m0 m7 = refl
jacobi m6 m0 m8 = refl
jacobi m6 m1 m0 = refl
jacobi m6 m1 m1 = refl
jacobi m6 m1 m2 = refl
jacobi m6 m1 m3 = refl
jacobi m6 m1 m4 = refl
jacobi m6 m1 m5 = refl
jacobi m6 m1 m6 = refl
jacobi m6 m1 m7 = refl
jacobi m6 m1 m8 = refl
jacobi m6 m2 m0 = refl
jacobi m6 m2 m1 = refl
jacobi m6 m2 m2 = refl
jacobi m6 m2 m3 = refl
jacobi m6 m2 m4 = refl
jacobi m6 m2 m5 = refl
jacobi m6 m2 m6 = refl
jacobi m6 m2 m7 = refl
jacobi m6 m2 m8 = refl
jacobi m6 m3 m0 = refl
jacobi m6 m3 m1 = refl
jacobi m6 m3 m2 = refl
jacobi m6 m3 m3 = refl
jacobi m6 m3 m4 = refl
jacobi m6 m3 m5 = refl
jacobi m6 m3 m6 = refl
jacobi m6 m3 m7 = refl
jacobi m6 m3 m8 = refl
jacobi m6 m4 m0 = refl
jacobi m6 m4 m1 = refl
jacobi m6 m4 m2 = refl
jacobi m6 m4 m3 = refl
jacobi m6 m4 m4 = refl
jacobi m6 m4 m5 = refl
jacobi m6 m4 m6 = refl
jacobi m6 m4 m7 = refl
jacobi m6 m4 m8 = refl
jacobi m6 m5 m0 = refl
jacobi m6 m5 m1 = refl
jacobi m6 m5 m2 = refl
jacobi m6 m5 m3 = refl
jacobi m6 m5 m4 = refl
jacobi m6 m5 m5 = refl
jacobi m6 m5 m6 = refl
jacobi m6 m5 m7 = refl
jacobi m6 m5 m8 = refl
jacobi m6 m6 m0 = refl
jacobi m6 m6 m1 = refl
jacobi m6 m6 m2 = refl
jacobi m6 m6 m3 = refl
jacobi m6 m6 m4 = refl
jacobi m6 m6 m5 = refl
jacobi m6 m6 m6 = refl
jacobi m6 m6 m7 = refl
jacobi m6 m6 m8 = refl
jacobi m6 m7 m0 = refl
jacobi m6 m7 m1 = refl
jacobi m6 m7 m2 = refl
jacobi m6 m7 m3 = refl
jacobi m6 m7 m4 = refl
jacobi m6 m7 m5 = refl
jacobi m6 m7 m6 = refl
jacobi m6 m7 m7 = refl
jacobi m6 m7 m8 = refl
jacobi m6 m8 m0 = refl
jacobi m6 m8 m1 = refl
jacobi m6 m8 m2 = refl
jacobi m6 m8 m3 = refl
jacobi m6 m8 m4 = refl
jacobi m6 m8 m5 = refl
jacobi m6 m8 m6 = refl
jacobi m6 m8 m7 = refl
jacobi m6 m8 m8 = refl
jacobi m7 m0 m0 = refl
jacobi m7 m0 m1 = refl
jacobi m7 m0 m2 = refl
jacobi m7 m0 m3 = refl
jacobi m7 m0 m4 = refl
jacobi m7 m0 m5 = refl
jacobi m7 m0 m6 = refl
jacobi m7 m0 m7 = refl
jacobi m7 m0 m8 = refl
jacobi m7 m1 m0 = refl
jacobi m7 m1 m1 = refl
jacobi m7 m1 m2 = refl
jacobi m7 m1 m3 = refl
jacobi m7 m1 m4 = refl
jacobi m7 m1 m5 = refl
jacobi m7 m1 m6 = refl
jacobi m7 m1 m7 = refl
jacobi m7 m1 m8 = refl
jacobi m7 m2 m0 = refl
jacobi m7 m2 m1 = refl
jacobi m7 m2 m2 = refl
jacobi m7 m2 m3 = refl
jacobi m7 m2 m4 = refl
jacobi m7 m2 m5 = refl
jacobi m7 m2 m6 = refl
jacobi m7 m2 m7 = refl
jacobi m7 m2 m8 = refl
jacobi m7 m3 m0 = refl
jacobi m7 m3 m1 = refl
jacobi m7 m3 m2 = refl
jacobi m7 m3 m3 = refl
jacobi m7 m3 m4 = refl
jacobi m7 m3 m5 = refl
jacobi m7 m3 m6 = refl
jacobi m7 m3 m7 = refl
jacobi m7 m3 m8 = refl
jacobi m7 m4 m0 = refl
jacobi m7 m4 m1 = refl
jacobi m7 m4 m2 = refl
jacobi m7 m4 m3 = refl
jacobi m7 m4 m4 = refl
jacobi m7 m4 m5 = refl
jacobi m7 m4 m6 = refl
jacobi m7 m4 m7 = refl
jacobi m7 m4 m8 = refl
jacobi m7 m5 m0 = refl
jacobi m7 m5 m1 = refl
jacobi m7 m5 m2 = refl
jacobi m7 m5 m3 = refl
jacobi m7 m5 m4 = refl
jacobi m7 m5 m5 = refl
jacobi m7 m5 m6 = refl
jacobi m7 m5 m7 = refl
jacobi m7 m5 m8 = refl
jacobi m7 m6 m0 = refl
jacobi m7 m6 m1 = refl
jacobi m7 m6 m2 = refl
jacobi m7 m6 m3 = refl
jacobi m7 m6 m4 = refl
jacobi m7 m6 m5 = refl
jacobi m7 m6 m6 = refl
jacobi m7 m6 m7 = refl
jacobi m7 m6 m8 = refl
jacobi m7 m7 m0 = refl
jacobi m7 m7 m1 = refl
jacobi m7 m7 m2 = refl
jacobi m7 m7 m3 = refl
jacobi m7 m7 m4 = refl
jacobi m7 m7 m5 = refl
jacobi m7 m7 m6 = refl
jacobi m7 m7 m7 = refl
jacobi m7 m7 m8 = refl
jacobi m7 m8 m0 = refl
jacobi m7 m8 m1 = refl
jacobi m7 m8 m2 = refl
jacobi m7 m8 m3 = refl
jacobi m7 m8 m4 = refl
jacobi m7 m8 m5 = refl
jacobi m7 m8 m6 = refl
jacobi m7 m8 m7 = refl
jacobi m7 m8 m8 = refl
jacobi m8 m0 m0 = refl
jacobi m8 m0 m1 = refl
jacobi m8 m0 m2 = refl
jacobi m8 m0 m3 = refl
jacobi m8 m0 m4 = refl
jacobi m8 m0 m5 = refl
jacobi m8 m0 m6 = refl
jacobi m8 m0 m7 = refl
jacobi m8 m0 m8 = refl
jacobi m8 m1 m0 = refl
jacobi m8 m1 m1 = refl
jacobi m8 m1 m2 = refl
jacobi m8 m1 m3 = refl
jacobi m8 m1 m4 = refl
jacobi m8 m1 m5 = refl
jacobi m8 m1 m6 = refl
jacobi m8 m1 m7 = refl
jacobi m8 m1 m8 = refl
jacobi m8 m2 m0 = refl
jacobi m8 m2 m1 = refl
jacobi m8 m2 m2 = refl
jacobi m8 m2 m3 = refl
jacobi m8 m2 m4 = refl
jacobi m8 m2 m5 = refl
jacobi m8 m2 m6 = refl
jacobi m8 m2 m7 = refl
jacobi m8 m2 m8 = refl
jacobi m8 m3 m0 = refl
jacobi m8 m3 m1 = refl
jacobi m8 m3 m2 = refl
jacobi m8 m3 m3 = refl
jacobi m8 m3 m4 = refl
jacobi m8 m3 m5 = refl
jacobi m8 m3 m6 = refl
jacobi m8 m3 m7 = refl
jacobi m8 m3 m8 = refl
jacobi m8 m4 m0 = refl
jacobi m8 m4 m1 = refl
jacobi m8 m4 m2 = refl
jacobi m8 m4 m3 = refl
jacobi m8 m4 m4 = refl
jacobi m8 m4 m5 = refl
jacobi m8 m4 m6 = refl
jacobi m8 m4 m7 = refl
jacobi m8 m4 m8 = refl
jacobi m8 m5 m0 = refl
jacobi m8 m5 m1 = refl
jacobi m8 m5 m2 = refl
jacobi m8 m5 m3 = refl
jacobi m8 m5 m4 = refl
jacobi m8 m5 m5 = refl
jacobi m8 m5 m6 = refl
jacobi m8 m5 m7 = refl
jacobi m8 m5 m8 = refl
jacobi m8 m6 m0 = refl
jacobi m8 m6 m1 = refl
jacobi m8 m6 m2 = refl
jacobi m8 m6 m3 = refl
jacobi m8 m6 m4 = refl
jacobi m8 m6 m5 = refl
jacobi m8 m6 m6 = refl
jacobi m8 m6 m7 = refl
jacobi m8 m6 m8 = refl
jacobi m8 m7 m0 = refl
jacobi m8 m7 m1 = refl
jacobi m8 m7 m2 = refl
jacobi m8 m7 m3 = refl
jacobi m8 m7 m4 = refl
jacobi m8 m7 m5 = refl
jacobi m8 m7 m6 = refl
jacobi m8 m7 m7 = refl
jacobi m8 m7 m8 = refl
jacobi m8 m8 m0 = refl
jacobi m8 m8 m1 = refl
jacobi m8 m8 m2 = refl
jacobi m8 m8 m3 = refl
jacobi m8 m8 m4 = refl
jacobi m8 m8 m5 = refl
jacobi m8 m8 m6 = refl
jacobi m8 m8 m7 = refl
jacobi m8 m8 m8 = refl


--------------------------------------------------------------------------------
-- §3. 三维旋量李代数 (so(3) 的 GF(3) 离散版)
--------------------------------------------------------------------------------

-- 李代数空间 = GF(3)³ (so(3) 的离散版 — 27 元素, 三维旋量空间)
-- 范畴修正 (2026-08-16): so(3) 是域 GF(3) 上的三维向量空间 (非 Fin 3);
-- 括号 = GF(3) 叉积 (结构常数与 ℝ³ 叉积一致, 反称由 2 ≢ 0 承载)
Lie3 : Set
Lie3 = Trit × Trit × Trit

-- 基向量
x1 x2 x3 : Lie3
x1 = T₁ , T₀ , T₀
x2 = T₀ , T₁ , T₀
x3 = T₀ , T₀ , T₁

-- GF(3) 叉积: (a,b,c) × (d,e,f) =
--   (b⊗f ⊕ negate(c⊗e), c⊗d ⊕ negate(a⊗f), a⊗e ⊕ negate(b⊗d))
br3 : Lie3 → Lie3 → Lie3
br3 (a , b , c) (d , e , f) =
  ((b ⊗ f) ⊕ negate (c ⊗ e)) ,
  ((c ⊗ d) ⊕ negate (a ⊗ f)) ,
  ((a ⊗ e) ⊕ negate (b ⊗ d))

-- 分量加法 (GF(3)³)
add3 : Lie3 → Lie3 → Lie3
add3 (a , b , c) (d , e , f) = (a ⊕ d) , (b ⊕ e) , (c ⊕ f)

-- 零元
zero3 : Lie3
zero3 = T₀ , T₀ , T₀

-- 基循环三式: [x1,x2]=x3, [x2,x3]=x1, [x3,x1]=x2
cyc12 : br3 x1 x2 ≡ x3 ; cyc12 = refl
cyc23 : br3 x2 x3 ≡ x1 ; cyc23 = refl
cyc31 : br3 x3 x1 ≡ x2 ; cyc31 = refl

neg3v : Lie3 → Lie3
neg3v (a , b , c) = negate a , negate b , negate c

-- 基反称对 ([xi,xj] = −[xj,xi], 对角 0)
br3-x1x1 : br3 x1 x1 ≡ zero3 ; br3-x1x1 = refl
br3-x2x2 : br3 x2 x2 ≡ zero3 ; br3-x2x2 = refl
br3-x3x3 : br3 x3 x3 ≡ zero3 ; br3-x3x3 = refl
br3-x1x3 : br3 x1 x3 ≡ neg3v x2 ; br3-x1x3 = refl
br3-x2x1 : br3 x2 x1 ≡ neg3v x3 ; br3-x2x1 = refl
br3-x3x2 : br3 x3 x2 ≡ neg3v x1 ; br3-x3x2 = refl

-- 反称 (27×27 = 729 项穷举): [x,y] + [y,x] = 0
-- 基枚举 (构造子 — 供 Jacobi 27 项穷举模式匹配)
data Basis3 : Set where
  e1 e2 e3 : Basis3

toVec : Basis3 → Lie3
toVec e1 = T₁ , T₀ , T₀
toVec e2 = T₀ , T₁ , T₀
toVec e3 = T₀ , T₀ , T₁

-- 基 Jacobi (3³ = 27 项): [[ei,ej],ek] + [[ej,ek],ei] + [[ek,ei],ej] = 0
jacobi3 : ∀ i j k → add3 (br3 (br3 (toVec i) (toVec j)) (toVec k))
                     (add3 (br3 (br3 (toVec j) (toVec k)) (toVec i))
                           (br3 (br3 (toVec k) (toVec i)) (toVec j))) ≡ zero3
jacobi3 e1 e1 e1 = refl
jacobi3 e1 e1 e2 = refl
jacobi3 e1 e1 e3 = refl
jacobi3 e1 e2 e1 = refl
jacobi3 e1 e2 e2 = refl
jacobi3 e1 e2 e3 = refl
jacobi3 e1 e3 e1 = refl
jacobi3 e1 e3 e2 = refl
jacobi3 e1 e3 e3 = refl
jacobi3 e2 e1 e1 = refl
jacobi3 e2 e1 e2 = refl
jacobi3 e2 e1 e3 = refl
jacobi3 e2 e2 e1 = refl
jacobi3 e2 e2 e2 = refl
jacobi3 e2 e2 e3 = refl
jacobi3 e2 e3 e1 = refl
jacobi3 e2 e3 e2 = refl
jacobi3 e2 e3 e3 = refl
jacobi3 e3 e1 e1 = refl
jacobi3 e3 e1 e2 = refl
jacobi3 e3 e1 e3 = refl
jacobi3 e3 e2 e1 = refl
jacobi3 e3 e2 e2 = refl
jacobi3 e3 e2 e3 = refl
jacobi3 e3 e3 e1 = refl
jacobi3 e3 e3 e2 = refl
jacobi3 e3 e3 e3 = refl

-- 诚实边界: 全 Jacobi (27³ 项) 由括号的三线性 (双线性两个槽位) +
-- 基 Jacobi 27 项导出 — 三线性归约的结构证明留待深化 (未以 postulate 驻留)。

-- 0 postulate.

--------------------------------------------------------------------------------
-- 反称性 asym3 (构造性: br3 双线性, 替代原 729 case 穷举)
--------------------------------------------------------------------------------

swap4 : ∀ A B C D → (A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (B ⊕ D)
swap4 A B C D =
  trans (sym (⊕-assoc (A ⊕ B) C D))
    (trans (cong (λ u → u ⊕ D) (⊕-assoc A B C))
      (trans (cong (λ u → (A ⊕ u) ⊕ D) (⊕-comm B C))
        (trans (cong (λ u → u ⊕ D) (sym (⊕-assoc A C B)))
          (⊕-assoc (A ⊕ C) B D))))

-- 分量加法交换/结合
add3-comm : ∀ x y → add3 x y ≡ add3 y x
add3-comm (a , b , c) (d , e , f) = cong₃ (λ p q r → p , q , r) (⊕-comm a d) (⊕-comm b e) (⊕-comm c f)
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl

add3-assoc : ∀ x y z → add3 (add3 x y) z ≡ add3 x (add3 y z)
add3-assoc (a , b , c) (d , e , f) (g , h , i) =
  cong₃ (λ p q r → p , q , r) (⊕-assoc a d g) (⊕-assoc b e h) (⊕-assoc c f i)
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl

-- br3 保加法 (左线性, 逐分量)
br3-addˡ : ∀ x y z → br3 (add3 x y) z ≡ add3 (br3 x z) (br3 y z)
br3-addˡ (a₁ , b₁ , c₁) (a₂ , b₂ , c₂) (d , e , f) =
  cong₃ (λ p q r → p , q , r) c0 c1 c2
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl
    c0 : ((b₁ ⊕ b₂) ⊗ f) ⊕ negate ((c₁ ⊕ c₂) ⊗ e)
       ≡ ((b₁ ⊗ f) ⊕ negate (c₁ ⊗ e)) ⊕ ((b₂ ⊗ f) ⊕ negate (c₂ ⊗ e))
    c0 = begin
      ((b₁ ⊕ b₂) ⊗ f) ⊕ negate ((c₁ ⊕ c₂) ⊗ e)
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ b₁ b₂ f) (cong negate (⊗-distribʳ-⊕ c₁ c₂ e)) ⟩
      ((b₁ ⊗ f) ⊕ (b₂ ⊗ f)) ⊕ negate ((c₁ ⊗ e) ⊕ (c₂ ⊗ e))
        ≡⟨ cong (((b₁ ⊗ f) ⊕ (b₂ ⊗ f)) ⊕_) (negate-⊕ (c₁ ⊗ e) (c₂ ⊗ e)) ⟩
      ((b₁ ⊗ f) ⊕ (b₂ ⊗ f)) ⊕ (negate (c₁ ⊗ e) ⊕ negate (c₂ ⊗ e))
        ≡⟨ swap4 (b₁ ⊗ f) (b₂ ⊗ f) (negate (c₁ ⊗ e)) (negate (c₂ ⊗ e)) ⟩
      ((b₁ ⊗ f) ⊕ negate (c₁ ⊗ e)) ⊕ ((b₂ ⊗ f) ⊕ negate (c₂ ⊗ e))
      ∎
    c1 : ((c₁ ⊕ c₂) ⊗ d) ⊕ negate ((a₁ ⊕ a₂) ⊗ f)
       ≡ ((c₁ ⊗ d) ⊕ negate (a₁ ⊗ f)) ⊕ ((c₂ ⊗ d) ⊕ negate (a₂ ⊗ f))
    c1 = begin
      ((c₁ ⊕ c₂) ⊗ d) ⊕ negate ((a₁ ⊕ a₂) ⊗ f)
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ c₁ c₂ d) (cong negate (⊗-distribʳ-⊕ a₁ a₂ f)) ⟩
      ((c₁ ⊗ d) ⊕ (c₂ ⊗ d)) ⊕ negate ((a₁ ⊗ f) ⊕ (a₂ ⊗ f))
        ≡⟨ cong (((c₁ ⊗ d) ⊕ (c₂ ⊗ d)) ⊕_) (negate-⊕ (a₁ ⊗ f) (a₂ ⊗ f)) ⟩
      ((c₁ ⊗ d) ⊕ (c₂ ⊗ d)) ⊕ (negate (a₁ ⊗ f) ⊕ negate (a₂ ⊗ f))
        ≡⟨ swap4 (c₁ ⊗ d) (c₂ ⊗ d) (negate (a₁ ⊗ f)) (negate (a₂ ⊗ f)) ⟩
      ((c₁ ⊗ d) ⊕ negate (a₁ ⊗ f)) ⊕ ((c₂ ⊗ d) ⊕ negate (a₂ ⊗ f))
      ∎
    c2 : ((a₁ ⊕ a₂) ⊗ e) ⊕ negate ((b₁ ⊕ b₂) ⊗ d)
       ≡ ((a₁ ⊗ e) ⊕ negate (b₁ ⊗ d)) ⊕ ((a₂ ⊗ e) ⊕ negate (b₂ ⊗ d))
    c2 = begin
      ((a₁ ⊕ a₂) ⊗ e) ⊕ negate ((b₁ ⊕ b₂) ⊗ d)
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ a₁ a₂ e) (cong negate (⊗-distribʳ-⊕ b₁ b₂ d)) ⟩
      ((a₁ ⊗ e) ⊕ (a₂ ⊗ e)) ⊕ negate ((b₁ ⊗ d) ⊕ (b₂ ⊗ d))
        ≡⟨ cong (((a₁ ⊗ e) ⊕ (a₂ ⊗ e)) ⊕_) (negate-⊕ (b₁ ⊗ d) (b₂ ⊗ d)) ⟩
      ((a₁ ⊗ e) ⊕ (a₂ ⊗ e)) ⊕ (negate (b₁ ⊗ d) ⊕ negate (b₂ ⊗ d))
        ≡⟨ swap4 (a₁ ⊗ e) (a₂ ⊗ e) (negate (b₁ ⊗ d)) (negate (b₂ ⊗ d)) ⟩
      ((a₁ ⊗ e) ⊕ negate (b₁ ⊗ d)) ⊕ ((a₂ ⊗ e) ⊕ negate (b₂ ⊗ d))
      ∎

-- br3 保加法 (右线性)
br3-addʳ : ∀ x y z → br3 x (add3 y z) ≡ add3 (br3 x y) (br3 x z)
br3-addʳ (a , b , c) (d₁ , e₁ , f₁) (d₂ , e₂ , f₂) =
  cong₃ (λ p q r → p , q , r) c0 c1 c2
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl
    c0 : (b ⊗ (f₁ ⊕ f₂)) ⊕ negate (c ⊗ (e₁ ⊕ e₂))
       ≡ ((b ⊗ f₁) ⊕ negate (c ⊗ e₁)) ⊕ ((b ⊗ f₂) ⊕ negate (c ⊗ e₂))
    c0 = begin
      (b ⊗ (f₁ ⊕ f₂)) ⊕ negate (c ⊗ (e₁ ⊕ e₂))
        ≡⟨ cong₂ _⊕_ (⊗-distribˡ-⊕ b f₁ f₂) (cong negate (⊗-distribˡ-⊕ c e₁ e₂)) ⟩
      ((b ⊗ f₁) ⊕ (b ⊗ f₂)) ⊕ negate ((c ⊗ e₁) ⊕ (c ⊗ e₂))
        ≡⟨ cong (((b ⊗ f₁) ⊕ (b ⊗ f₂)) ⊕_) (negate-⊕ (c ⊗ e₁) (c ⊗ e₂)) ⟩
      ((b ⊗ f₁) ⊕ (b ⊗ f₂)) ⊕ (negate (c ⊗ e₁) ⊕ negate (c ⊗ e₂))
        ≡⟨ swap4 (b ⊗ f₁) (b ⊗ f₂) (negate (c ⊗ e₁)) (negate (c ⊗ e₂)) ⟩
      ((b ⊗ f₁) ⊕ negate (c ⊗ e₁)) ⊕ ((b ⊗ f₂) ⊕ negate (c ⊗ e₂))
      ∎
    c1 : (c ⊗ (d₁ ⊕ d₂)) ⊕ negate (a ⊗ (f₁ ⊕ f₂))
       ≡ ((c ⊗ d₁) ⊕ negate (a ⊗ f₁)) ⊕ ((c ⊗ d₂) ⊕ negate (a ⊗ f₂))
    c1 = begin
      (c ⊗ (d₁ ⊕ d₂)) ⊕ negate (a ⊗ (f₁ ⊕ f₂))
        ≡⟨ cong₂ _⊕_ (⊗-distribˡ-⊕ c d₁ d₂) (cong negate (⊗-distribˡ-⊕ a f₁ f₂)) ⟩
      ((c ⊗ d₁) ⊕ (c ⊗ d₂)) ⊕ negate ((a ⊗ f₁) ⊕ (a ⊗ f₂))
        ≡⟨ cong (((c ⊗ d₁) ⊕ (c ⊗ d₂)) ⊕_) (negate-⊕ (a ⊗ f₁) (a ⊗ f₂)) ⟩
      ((c ⊗ d₁) ⊕ (c ⊗ d₂)) ⊕ (negate (a ⊗ f₁) ⊕ negate (a ⊗ f₂))
        ≡⟨ swap4 (c ⊗ d₁) (c ⊗ d₂) (negate (a ⊗ f₁)) (negate (a ⊗ f₂)) ⟩
      ((c ⊗ d₁) ⊕ negate (a ⊗ f₁)) ⊕ ((c ⊗ d₂) ⊕ negate (a ⊗ f₂))
      ∎
    c2 : (a ⊗ (e₁ ⊕ e₂)) ⊕ negate (b ⊗ (d₁ ⊕ d₂))
       ≡ ((a ⊗ e₁) ⊕ negate (b ⊗ d₁)) ⊕ ((a ⊗ e₂) ⊕ negate (b ⊗ d₂))
    c2 = begin
      (a ⊗ (e₁ ⊕ e₂)) ⊕ negate (b ⊗ (d₁ ⊕ d₂))
        ≡⟨ cong₂ _⊕_ (⊗-distribˡ-⊕ a e₁ e₂) (cong negate (⊗-distribˡ-⊕ b d₁ d₂)) ⟩
      ((a ⊗ e₁) ⊕ (a ⊗ e₂)) ⊕ negate ((b ⊗ d₁) ⊕ (b ⊗ d₂))
        ≡⟨ cong (((a ⊗ e₁) ⊕ (a ⊗ e₂)) ⊕_) (negate-⊕ (b ⊗ d₁) (b ⊗ d₂)) ⟩
      ((a ⊗ e₁) ⊕ (a ⊗ e₂)) ⊕ (negate (b ⊗ d₁) ⊕ negate (b ⊗ d₂))
        ≡⟨ swap4 (a ⊗ e₁) (a ⊗ e₂) (negate (b ⊗ d₁)) (negate (b ⊗ d₂)) ⟩
      ((a ⊗ e₁) ⊕ negate (b ⊗ d₁)) ⊕ ((a ⊗ e₂) ⊕ negate (b ⊗ d₂))
      ∎

-- add3 分量零律
add3-zeroˡ : ∀ x → add3 zero3 x ≡ x
add3-zeroˡ (a , b , c) = cong₃ (λ p q r → p , q , r) (⊕-identityˡ a) (⊕-identityˡ b) (⊕-identityˡ c)
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl

-- ★ asym3: br3 x y + br3 y x = 0 ★
asym3 : ∀ x y → add3 (br3 x y) (br3 y x) ≡ zero3
asym3 (a , b , c) (d , e , f) = cong₃ (λ p q r → p , q , r) c0 c1 c2
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl
    neg-add-zero : ∀ u → (negate u) ⊕ u ≡ T₀
    neg-add-zero u = trans (⊕-comm (negate u) u) (⊕-inverse u)
    c0 : ((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ b)) ≡ T₀
    c0 = begin
      ((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ b))
        ≡⟨ cong (((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕_) (cong₂ (λ (u v : Trit) → u ⊕ negate v) (⊗-comm e c) (⊗-comm f b)) ⟩
      ((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕ ((c ⊗ e) ⊕ negate (b ⊗ f))
        ≡⟨ swap4 (b ⊗ f) (negate (c ⊗ e)) (c ⊗ e) (negate (b ⊗ f)) ⟩
      ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ (negate (c ⊗ e) ⊕ negate (b ⊗ f))
        ≡⟨ cong (((b ⊗ f) ⊕ (c ⊗ e)) ⊕_) (sym (negate-⊕ (c ⊗ e) (b ⊗ f))) ⟩
      ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ negate ((c ⊗ e) ⊕ (b ⊗ f))
        ≡⟨ cong (λ u → u ⊕ negate ((c ⊗ e) ⊕ (b ⊗ f))) (⊕-comm (b ⊗ f) (c ⊗ e)) ⟩
      ((c ⊗ e) ⊕ (b ⊗ f)) ⊕ negate ((c ⊗ e) ⊕ (b ⊗ f))
        ≡⟨ ⊕-inverse ((c ⊗ e) ⊕ (b ⊗ f)) ⟩
      T₀
      ∎
    c1 : ((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕ ((f ⊗ a) ⊕ negate (d ⊗ c)) ≡ T₀
    c1 = begin
      ((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕ ((f ⊗ a) ⊕ negate (d ⊗ c))
        ≡⟨ cong (((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕_) (cong₂ (λ (u v : Trit) → u ⊕ negate v) (⊗-comm f a) (⊗-comm d c)) ⟩
      ((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕ ((a ⊗ f) ⊕ negate (c ⊗ d))
        ≡⟨ swap4 (c ⊗ d) (negate (a ⊗ f)) (a ⊗ f) (negate (c ⊗ d)) ⟩
      ((c ⊗ d) ⊕ (a ⊗ f)) ⊕ (negate (a ⊗ f) ⊕ negate (c ⊗ d))
        ≡⟨ cong (((c ⊗ d) ⊕ (a ⊗ f)) ⊕_) (sym (negate-⊕ (a ⊗ f) (c ⊗ d))) ⟩
      ((c ⊗ d) ⊕ (a ⊗ f)) ⊕ negate ((a ⊗ f) ⊕ (c ⊗ d))
        ≡⟨ cong (λ u → u ⊕ negate ((a ⊗ f) ⊕ (c ⊗ d))) (⊕-comm (c ⊗ d) (a ⊗ f)) ⟩
      ((a ⊗ f) ⊕ (c ⊗ d)) ⊕ negate ((a ⊗ f) ⊕ (c ⊗ d))
        ≡⟨ ⊕-inverse ((a ⊗ f) ⊕ (c ⊗ d)) ⟩
      T₀
      ∎
    c2 : ((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕ ((d ⊗ b) ⊕ negate (e ⊗ a)) ≡ T₀
    c2 = begin
      ((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕ ((d ⊗ b) ⊕ negate (e ⊗ a))
        ≡⟨ cong (((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕_) (cong₂ (λ (u v : Trit) → u ⊕ negate v) (⊗-comm d b) (⊗-comm e a)) ⟩
      ((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕ ((b ⊗ d) ⊕ negate (a ⊗ e))
        ≡⟨ swap4 (a ⊗ e) (negate (b ⊗ d)) (b ⊗ d) (negate (a ⊗ e)) ⟩
      ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ (negate (b ⊗ d) ⊕ negate (a ⊗ e))
        ≡⟨ cong (((a ⊗ e) ⊕ (b ⊗ d)) ⊕_) (sym (negate-⊕ (b ⊗ d) (a ⊗ e))) ⟩
      ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate ((b ⊗ d) ⊕ (a ⊗ e))
        ≡⟨ cong (λ u → u ⊕ negate ((b ⊗ d) ⊕ (a ⊗ e))) (⊕-comm (a ⊗ e) (b ⊗ d)) ⟩
      ((b ⊗ d) ⊕ (a ⊗ e)) ⊕ negate ((b ⊗ d) ⊕ (a ⊗ e))
        ≡⟨ ⊕-inverse ((b ⊗ d) ⊕ (a ⊗ e)) ⟩
      T₀
      ∎
