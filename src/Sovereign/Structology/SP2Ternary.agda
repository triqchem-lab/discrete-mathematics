{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.SP2Ternary
-- SP2 三进制读法: 两条轨道岔口 (0 postulate, 纯 Z/3 计算)
--
-- SP2 = 磁→光的电磁场转化。它的三进制表示把三个方向/频率标成 Z/3 = {0,1,2},
-- 生成操作落在两条不同轨道上, 恰对应卢先生的两条原话:
--   * 倍频 ×2 (二进制读法): 轨 {1,2}, 周期 2, 永不归零 — 「2 SP 2 重金属」/乌比斯环
--   * 加一 +1 (三进制读法): 轨 {0,1,2}, 周期 3, 闭合归零 — 「任何的零都是三个的」
--
-- 本模块只证明算子的轨道结构 (refl / λ()); 物理/本体论解读见知识库, 不进入证明链。

module Sovereign.Structology.SP2Ternary where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

--------------------------------------------------------------------------------
-- SP2 方向: Fin 3, 标签 {0,1,2}
--------------------------------------------------------------------------------

SP2Dir : Set
SP2Dir = Fin 3

--------------------------------------------------------------------------------
-- 二进制读法: 倍频算子 ×2 mod 3
-- 轨道 [1 → 2 → 1 → 2 → ...], 周期 2, 永不归零
-- 对应卢先生: 「2 SP 2 重金属」, 乌比斯环「两个周期跑不出」
--------------------------------------------------------------------------------

double : SP2Dir → SP2Dir
double zero = zero
double (suc zero) = suc (suc zero)          -- 2·1 = 2 mod 3
double (suc (suc zero)) = suc zero          -- 2·2 = 4 ≡ 1 mod 3

--------------------------------------------------------------------------------
-- 三进制读法: 加一算子 +1 mod 3
-- 轨道 [0 → 1 → 2 → 0], 周期 3, 闭合归零
-- 对应卢先生: 「任何的零都是三个的」「三进制归零」
--------------------------------------------------------------------------------

succ3 : SP2Dir → SP2Dir
succ3 zero = suc zero
succ3 (suc zero) = suc (suc zero)
succ3 (suc (suc zero)) = zero

--------------------------------------------------------------------------------
-- 核心定理 1: 倍频算子的 1 轨不包含 0 (永不归零)
--------------------------------------------------------------------------------

double-1 : double (suc zero) ≡ suc (suc zero)
double-1 = refl

double-2 : double (suc (suc zero)) ≡ suc zero
double-2 = refl

double-1-not-zero : ¬ (double (suc zero) ≡ zero)
double-1-not-zero = λ ()

double-2-not-zero : ¬ (double (suc (suc zero)) ≡ zero)
double-2-not-zero = λ ()

--------------------------------------------------------------------------------
-- 核心定理 2: 加一算子的 0 轨周期 3, 闭合归零
--------------------------------------------------------------------------------

succ3-0 : succ3 zero ≡ suc zero
succ3-0 = refl

succ3-1 : succ3 (suc zero) ≡ suc (suc zero)
succ3-1 = refl

succ3-2 : succ3 (suc (suc zero)) ≡ zero
succ3-2 = refl

--------------------------------------------------------------------------------
-- 核心定理 3: 两条轨道的关系
--------------------------------------------------------------------------------

double-0 : double zero ≡ zero
double-0 = refl

succ3-closes : succ3 (suc (suc zero)) ≡ zero
succ3-closes = refl

-- 0 postulate.
