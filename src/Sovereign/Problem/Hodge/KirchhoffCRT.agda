{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.KirchhoffCRT
-- 任务书第四层·4.1：Kirchhoff / Matrix-Tree 的 CRT 通道（K₃ 实例）
--
-- 数学背景（人类纠偏后修正）：矩阵树定理在 GF(3) 单域上退化（K₃ 树数
--   3 ≡ 0 被模吞）。**本库正解不是 ℤ，而是 CRT 通道**——
--   `Algebra/Jacobian/jac_CRTDet.agda` 拱顶石已闭合
--   det(M) = crt12(det(M₃), det(M₄))（det-crt12，一般 N）：
--   GF(3) 分量虽退化，**Fin 4 分量保信息**（3 mod 4 = 3 ≠ 0），
--   crt12 重构即得 d3 ≠ 0——树数 ≢ 0 可判，无需 ℤ。
--
-- 本模块（K₃ 拉普拉斯主子式换到 Duodec 系数）：
--   ① mt-det2：主子式 [[2, 11], [11, 2]]（mod 12，−1 ≡ 11）的 det = d3；
--   ② mt-gf3-degenerate：GF(3) 分量 π3 = T₀——退化的机器见证（树数 3 与 0
--      在 GF(3) 上不可区分）；
--   ③ mt-fin4-preserves：Fin 4 分量 ≢ 0——信息保留的机器见证；
--   ④ mt-crt-reconstruct：crt12(π3, π4) ≡ d3——重构保真（crt12-roundtrip 实例）。
--
-- 复用（本地资产）：jac_CRTDet.det2D（2×2 Duodec 行列式）+ crt12-roundtrip
--   + Duodecimal 的 12 环算子（全表 refl）。与 KirchhoffZ（ℤ 对照域）并列：
--   ℤ 给精确值 3，CRT 通道给「mod 12 非零可判」——本库判非零只需后者。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.KirchhoffCRT where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d3; d2; d11; π3; π4; crt12; crt12-roundtrip)
open import Sovereign.Algebra.Jacobian.jac_CRTDet
  using (det2D)

--------------------------------------------------------------------------------
-- §1. K₃ 拉普拉斯主子式（Duodec 系数）
--
-- ℤ 侧 [[2, −1], [−1, 2]] 换到 mod 12：2 ↦ d2，−1 ↦ d11。
-- det = 2·2 − 11·11 (mod 12) = 4 − 121 = −117 ≡ 3 (mod 12) = d3。
--------------------------------------------------------------------------------

mt-det2 : det2D d2 d11 d11 d2 ≡ d3
mt-det2 = refl

--------------------------------------------------------------------------------
-- §2. GF(3) 分量退化（树数 3 ≡ 0 的机器见证）
--------------------------------------------------------------------------------

mt-gf3-degenerate : π3 (det2D d2 d11 d11 d2) ≡ π3 d0
mt-gf3-degenerate = refl

--------------------------------------------------------------------------------
-- §3. Fin 4 分量保信息（3 mod 4 = 3 ≠ 0）
--------------------------------------------------------------------------------

mt-fin4-preserves : π4 (det2D d2 d11 d11 d2) ≢ π4 d0
mt-fin4-preserves = λ ()

--------------------------------------------------------------------------------
-- §4. CRT 重构保真（crt12-roundtrip 实例）
--------------------------------------------------------------------------------

mt-crt-reconstruct :
  crt12 (π3 (det2D d2 d11 d11 d2)) (π4 (det2D d2 d11 d11 d2)) ≡ d3
mt-crt-reconstruct = crt12-roundtrip (det2D d2 d11 d11 d2)
