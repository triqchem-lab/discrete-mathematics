{-# OPTIONS --guardedness #-}
module Sovereign.Problem.YangMills.All where

-- Yang-Mills 质量间隙
open import Sovereign.Problem.YangMills.jac_YM_DetMul   public  -- det(AB)=det(A)det(B)
open import Sovereign.Problem.YangMills.jac_YM_L3       public  -- 质量间隙 L3
open import Sovereign.Problem.YangMills.jac_YM_Full     public  -- SU(2) 全规模
open import Sovereign.Problem.YangMills.jac_YM_Action   public  -- Wilson 作用量
open import Sovereign.Problem.YangMills.jac_YMTransfer  public  -- 转移矩阵
open import Sovereign.Problem.YangMills.jac_YM_Transfer public  -- 转移矩阵(通用)
open import Sovereign.Problem.YangMills.jac_WilsonLoop      public
open import Sovereign.Problem.YangMills.jac_WilsonPlaquette public
open import Sovereign.Problem.YangMills.jac_SU2_Embedding   public
open import Sovereign.Problem.YangMills.jac_SUn_GF9         public
