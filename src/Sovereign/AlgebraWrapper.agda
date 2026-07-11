{-# OPTIONS --guardedness #-}

module Sovereign.AlgebraWrapper where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

cancel : (a b c : ℕ) → (a + b) ∸ (a + c) ≡ b ∸ c
cancel zero    b c = refl
cancel (suc a) b c = cancel a b c

-- 显式归约引理: 绕过 v2.9.0 _*_ 定义等价差异
suc*-≡ : ∀ n m → suc n * m ≡ m + n * m
suc*-≡ n m = refl

suc∸-≡ : ∀ n m → suc n ∸ suc m ≡ n ∸ m
suc∸-≡ n m = refl

distrib-lemma : (a b c : ℕ) → (b * a) ∸ (c * a) ≡ (b ∸ c) * a
distrib-lemma a 0      0      = refl
distrib-lemma a 0      (suc c) = refl
distrib-lemma a (suc b) 0      = refl
distrib-lemma a (suc b) (suc c) 
  rewrite suc*-≡ b a | suc*-≡ c a | suc∸-≡ b c = ans
  where
    ans : (a + b * a) ∸ (a + c * a) ≡ (b ∸ c) * a
    ans = trans (cancel a (b * a) (c * a)) (distrib-lemma a b c)
