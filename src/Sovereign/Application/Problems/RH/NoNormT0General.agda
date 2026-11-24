{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.NoNormT0General
-- t=0 谱系全称化（M2 · A2.4）
--
-- 数学背景（oracle v2 冻结 + classify 承载）:
--   t² + 3s² = 4·3ⁿ 取 t=0: s² = 4·3ⁿ/3 —— n 偶无整数解（NoNormT0Even 双层已证）,
--   n 奇恰 s = ±2·3^{(n−1)/2}（正部见证 Witness.ws; **唯一性**由本件的
--   t0-odd 从 NormClassify.classify 派生 —— 此前标注的「差唯一性方向」至此补齐）。
--
-- 本模块证明（0 postulate）:
--   §1 pow3-pos / mul2-pos: 3^k 与 2·3^k 非零（classify 偶形式消去的矛盾核）
--   §2 t0-odd: sol n 0 s ⟹ ∃k, n = 2k+1 ∧ s = 2·3^k（唯一性, 经 classify 分派）
--
-- 诚实边界: 负部 s 的符号对称（±2·3^k）未形式化, 同 Witness/NoNormT0Even 边界;
--   n 偶无解方向库内已有两条独立路径（no-norm-t0-even 与 classify 偶形式 + pow3-pos）。

module Sovereign.Application.Problems.RH.NoNormT0General where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open import Sovereign.Application.Problems.RH.NormClassify
  using (sol; BSol; classify)
open NoNormPrelude using (pow3; dub)

--------------------------------------------------------------------------------
-- §1. 非零引理（3 的幂与 2·3^k 恒正——消去 classify 偶形式）
--------------------------------------------------------------------------------

-- c·x ≡ 0 ⇒ x ≡ 0（suc 情形: c·suc x' 的 + 递归落在构造子 suc x' 上 ⇒ suc 头 ⇒ () 通过;
--   注意不能直接对 pow3 (suc k) ≡ zero 用 (): LHS 于抽象 k 处 stuck, 空型检查拒绝 —— 实测）
mult3-zero : ∀ x → 3 * x ≡ zero → x ≡ zero
mult3-zero zero e = refl
mult3-zero (suc x') ()

mult2-zero : ∀ x → 2 * x ≡ zero → x ≡ zero
mult2-zero zero e = refl
mult2-zero (suc x') ()

pow3-pos : ∀ k → pow3 k ≡ zero → ⊥
pow3-pos zero ()
pow3-pos (suc k) e = pow3-pos k (mult3-zero (pow3 k) e)

mul2-pos : ∀ k → 2 * pow3 k ≡ zero → ⊥
mul2-pos zero ()
mul2-pos (suc k) e =
  pow3-pos k (mult3-zero (pow3 k) (mult2-zero (pow3 (suc k)) e))

--------------------------------------------------------------------------------
-- §2. t=0 唯一性: sol n 0 s ⟹ n = 2k+1 且 s = 2·3^k
--------------------------------------------------------------------------------

t0-odd : ∀ n s → sol n zero s
       → Σ ℕ (λ k → n ≡ suc (dub k) × s ≡ 2 * pow3 k)
t0-odd n s h with classify n zero s h
... | inj₁ (k , e-n , inj₁ (a , b)) = ⊥-elim (pow3-pos k (sym a))
... | inj₁ (k , e-n , inj₂ (a , b)) = ⊥-elim (mul2-pos k (sym a))
... | inj₂ (k , e-n , inj₁ (a , b)) = (k , e-n , b)
... | inj₂ (k , e-n , inj₂ (a , b)) = ⊥-elim (pow3-pos (suc k) (sym a))

-- 注记: n 偶无解方向 = 本件 §2 的推论（偶形式被 §1 消去 ⇒ 只剩奇形式）
-- 与 NoNormT0Even.no-norm-t0-even（ℤ 层独立证明）双路径并存, 互为对账。
