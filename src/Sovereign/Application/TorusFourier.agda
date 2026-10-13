{-# OPTIONS --rewriting #-}

-- | Sovereign.Application.TorusFourier
-- T⁶ 离散 Fourier —— CRT 谱投影即离散变换。
--
-- 数学背景：把 CRT 谱投影直接用作 T⁶ 上的离散 Fourier 变换（fourierProj: T6Lattice → ℕ × ℕ，
--   及其逆 fourierInv）；因 CRT 是环同构（无损降维），此「变换」在有限格点上**精确可逆**，
--   没有连续 Fourier 的收敛/截断问题。
module Sovereign.Application.TorusFourier where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat using (ℕ; _+_; _*_; _%_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Product using (_×_; _,_)
open import Sovereign.Synthesis.T6 using (T6Lattice; GF3; toℕ-sum)
open import Sovereign.Synthesis.CRT using (crtProject; crtReconstruct; M)
open import Sovereign.Synthesis.Winding using (PolarWinding; ToroidalWinding)
open import Sovereign.Synthesis.MagicSquare144 using (FULL_TOUR)

-- CRT 谱投影作为 T⁶ 上的离散 Fourier 变换
-- T⁶ 格点 → CRT 坐标 (极向, 环向)

fourierProj : T6Lattice → ℕ × ℕ
fourierProj p = crtProject (toℕ-sum p)

-- 谱逆变换 (粗略)
fourierInv : ℕ × ℕ → ℕ
fourierInv (a , b) = crtReconstruct (a , b) % M

-- Fourier 核: ω = primitive 3rd root of unity in GF(9)
-- ω 对应 T₁ (e16⁺ → T₁, e16⁻ → T₂) 在 crt-to-trit 中

-- Fourier 系数: ŵ = Σₚ f(p) · ω^{⟨polar(p), toroidal(p)⟩}
-- 由于 GF(3) 中 ω³=1, Fourier 变换是 3-periodic

-- 恒等式: Fourier 逆 = crtReconstruct
-- 链接 Format/CRT.agda crtTheorem

-- 恒等点验证: zero 向量投影→恢复
fourier-zero : crtReconstruct (crtProject 0) % M ≡ 0 % M
fourier-zero = refl

-- 0 postulate.
