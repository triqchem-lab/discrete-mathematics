{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.Matrix12LowerWitness
-- M14: 12×12 恒等子式下界见证（144 测试对的 δ-表 + 单射性）
--
-- 数学背景（M14 注记: docs/techniques/M14-12x12矩阵指数上下界-2026-11-26.md）:
--   · 测试对 m := (E_ii, E_ik), m 遍历 (Fin 12)² —— 144 对;
--     E_ii *M12  E_ik = E_ik（恒等子式: (r,c) 处 = δ_{r,i}·δ_{c,k}）
--   · 144 个输出 E_ik 两两不同（E-inj 单射）⇒ 双线性秩 ≥ 144
--     （数学锚点: Bläser/Alder–Strassen 型; 精确 rank(⟨12,12,12⟩) 文献未知;
--      完整秩理论的 Agda 化 [构造性缺席·候选级]）
--   · 形态: valE/tabulate 定义（ℕ 纯算术, 无 ⊗-catch-all 风险）+ 144 条
--     mulEii 实例逐字发射（oracle_matrix12_lower.py, 先算后验 δ-表核对 144/144 ✓）
--
-- 诚实边界: 「单射 ⇒ 秩 ≥ 144」的最终一步需要 ℚ/ℕ 秩理论（维数论证）,
--   本件交付 δ-见证与单射性, 维数论证登记为后续。

module Sovereign.Algebra.LinearAlgebra.Matrix12LowerWitness where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (does)
open import Data.Nat.Properties
  using (_≟_; *-identityˡ; *-zeroˡ; *-identityʳ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Sovereign.Algebra.Spectral.DCCayleyGraph using (Matrix12; _*M12_)

--------------------------------------------------------------------------------
-- §0. 等值指示函数与基矩阵
--------------------------------------------------------------------------------

eqN : ℕ → ℕ → ℕ
eqN zero zero = 1
eqN zero (suc _) = 0
eqN (suc _) zero = 0
eqN (suc x) (suc y) = eqN x y

-- δ_{r,ii}·δ_{c,kk}: 基矩阵 E(ii,kk) 在 (r,c) 处的值
valE : ℕ → ℕ → ℕ → ℕ → ℕ
valE ii kk r c = eqN r ii * eqN c kk

E : Fin 12 → Fin 12 → Matrix12 ℕ
E ii kk = tabulate (λ r → tabulate (λ c → valE (toℕ ii) (toℕ kk) (toℕ r) (toℕ c)))

-- E 的读取刻画（lookup∘tabulate 两次直约, 无归约地雷）
E-at : ∀ (i k r c : Fin 12)
    → lookup (lookup (E i k) r) c ≡ valE (toℕ i) (toℕ k) (toℕ r) (toℕ c)
E-at i k r c =
  trans (cong (λ row → lookup row c)
              (lookup∘tabulate (λ r' → tabulate (λ c' → valE (toℕ i) (toℕ k) (toℕ r') (toℕ c'))) r))
        (lookup∘tabulate (λ c' → valE (toℕ i) (toℕ k) (toℕ r) (toℕ c')) c)

eqN-refl : ∀ x → eqN x x ≡ 1
eqN-refl zero = refl
eqN-refl (suc x) = eqN-refl x

eqN-1→eq : ∀ x y → eqN x y ≡ 1 → x ≡ y
eqN-1→eq zero zero _ = refl
eqN-1→eq zero (suc y) ()
eqN-1→eq (suc x) zero ()
eqN-1→eq (suc x) (suc y) p = cong suc (eqN-1→eq x y p)


--------------------------------------------------------------------------------
-- §1. ★ 单射性: E i k ≡ E i' k' ⇒ (i ≡ i') × (k ≡ k')
--     （144 个测试对的输出两两不同——秩下界 144 的见证本体）
--------------------------------------------------------------------------------

-- eqN 值域二分: {0, 1}（eqN 递归定义的 4 子句直接给）
eqN-range : ∀ a b → (eqN a b ≡ zero) ⊎ (eqN a b ≡ 1)
eqN-range Data.Nat.zero Data.Nat.zero = inj₂ refl
eqN-range Data.Nat.zero (Data.Nat.suc b) = inj₁ refl
eqN-range (Data.Nat.suc a) Data.Nat.zero = inj₁ refl
eqN-range (Data.Nat.suc a) (Data.Nat.suc b) = eqN-range a b

0≠1 : Data.Nat.zero ≢ Data.Nat.suc Data.Nat.zero
0≠1 ()

-- 秩下界的核: 两 δ 因子之积 ≡ 1 ⇒ 两因子各 ≡ 1（eqN-range 二分; 零因子 → 1≡0 荒谬）
eqN-prod→both : ∀ a b c d
  → eqN a b * eqN c d ≡ 1
  → (eqN a b ≡ 1) × (eqN c d ≡ 1)
eqN-prod→both a b c d h with eqN-range a b
... | inj₁ h0 = ⊥-elim (0≠1 (sym z1))
  where
  s1 : eqN a b * eqN c d ≡ Data.Nat.zero * eqN c d
  s1 = trans (cong (λ w → w * eqN c d) h0) (*-zeroˡ (eqN c d))
  z1 : 1 ≡ Data.Nat.zero
  z1 = trans (sym h) s1
... | inj₂ h1 = h1 , δ2-1
  where
  s1 : 1 * eqN c d ≡ eqN a b * eqN c d
  s1 = cong (λ w → w * eqN c d) (sym h1)
  δ2-1 : eqN c d ≡ 1
  δ2-1 = trans (sym (*-identityˡ (eqN c d))) (trans s1 (trans h refl))

E-inj : ∀ (i k i' k' : Fin 12)
    → E i k ≡ E i' k'
    → (i ≡ i') × (k ≡ k')
E-inj i k i' k' eq = toℕ-injective (eqN-1→eq (toℕ i) (toℕ i') δ1)
                   , toℕ-injective (eqN-1→eq (toℕ k) (toℕ k') δ2)
  where
  pivot : lookup (lookup (E i k) i) k ≡ eqN (toℕ i) (toℕ i') * eqN (toℕ k) (toℕ k')
  pivot = trans (cong (λ M → lookup (lookup M i) k) eq) (E-at i' k' i k)
  at1 : lookup (lookup (E i k) i) k ≡ 1
  at1 =
    trans (E-at i k i k)
    (trans (cong (λ w → w * eqN (toℕ k) (toℕ k)) (eqN-refl (toℕ i)))
    (trans (*-identityˡ (eqN (toℕ k) (toℕ k)))
           (eqN-refl (toℕ k))))
  prem : eqN (toℕ i) (toℕ i') * eqN (toℕ k) (toℕ k') ≡ 1
  prem = trans (sym pivot) at1
  δpair : (eqN (toℕ i) (toℕ i') ≡ 1) × (eqN (toℕ k) (toℕ k') ≡ 1)
  δpair = eqN-prod→both (toℕ i) (toℕ i') (toℕ k) (toℕ k') prem
  δ1 = proj₁ δpair
  δ2 = proj₂ δpair

--------------------------------------------------------------------------------
-- §2. δ-见证: 144 条 mulEii 实例（oracle 逐字发射）
--------------------------------------------------------------------------------
mulEii-0-0 : (E zero zero) *M12 (E zero zero) ≡ E zero zero
mulEii-0-0 = refl
mulEii-0-1 : (E zero zero) *M12 (E zero (suc zero)) ≡ E zero (suc zero)
mulEii-0-1 = refl
mulEii-0-2 : (E zero zero) *M12 (E zero (suc (suc zero))) ≡ E zero (suc (suc zero))
mulEii-0-2 = refl
mulEii-0-3 : (E zero zero) *M12 (E zero (suc (suc (suc zero)))) ≡ E zero (suc (suc (suc zero)))
mulEii-0-3 = refl
mulEii-0-4 : (E zero zero) *M12 (E zero (suc (suc (suc (suc zero))))) ≡ E zero (suc (suc (suc (suc zero))))
mulEii-0-4 = refl
mulEii-0-5 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc zero)))))) ≡ E zero (suc (suc (suc (suc (suc zero)))))
mulEii-0-5 = refl
mulEii-0-6 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc (suc zero))))))) ≡ E zero (suc (suc (suc (suc (suc (suc zero))))))
mulEii-0-6 = refl
mulEii-0-7 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-0-7 = refl
mulEii-0-8 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E zero (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-0-8 = refl
mulEii-0-9 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E zero (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-0-9 = refl
mulEii-0-10 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E zero (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-0-10 = refl
mulEii-0-11 : (E zero zero) *M12 (E zero (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E zero (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-0-11 = refl
mulEii-1-0 : (E (suc zero) (suc zero)) *M12 (E (suc zero) zero) ≡ E (suc zero) zero
mulEii-1-0 = refl
mulEii-1-1 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc zero)) ≡ E (suc zero) (suc zero)
mulEii-1-1 = refl
mulEii-1-2 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc zero))) ≡ E (suc zero) (suc (suc zero))
mulEii-1-2 = refl
mulEii-1-3 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc zero)))) ≡ E (suc zero) (suc (suc (suc zero)))
mulEii-1-3 = refl
mulEii-1-4 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc zero))))) ≡ E (suc zero) (suc (suc (suc (suc zero))))
mulEii-1-4 = refl
mulEii-1-5 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc zero) (suc (suc (suc (suc (suc zero)))))
mulEii-1-5 = refl
mulEii-1-6 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc zero) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-1-6 = refl
mulEii-1-7 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc zero) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-1-7 = refl
mulEii-1-8 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-1-8 = refl
mulEii-1-9 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-1-9 = refl
mulEii-1-10 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-1-10 = refl
mulEii-1-11 : (E (suc zero) (suc zero)) *M12 (E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-1-11 = refl
mulEii-2-0 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) zero) ≡ E (suc (suc zero)) zero
mulEii-2-0 = refl
mulEii-2-1 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc zero)) ≡ E (suc (suc zero)) (suc zero)
mulEii-2-1 = refl
mulEii-2-2 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc zero))) ≡ E (suc (suc zero)) (suc (suc zero))
mulEii-2-2 = refl
mulEii-2-3 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc zero)))) ≡ E (suc (suc zero)) (suc (suc (suc zero)))
mulEii-2-3 = refl
mulEii-2-4 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc zero))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc zero))))
mulEii-2-4 = refl
mulEii-2-5 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc zero)))))
mulEii-2-5 = refl
mulEii-2-6 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-2-6 = refl
mulEii-2-7 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-2-7 = refl
mulEii-2-8 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-2-8 = refl
mulEii-2-9 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-2-9 = refl
mulEii-2-10 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-2-10 = refl
mulEii-2-11 : (E (suc (suc zero)) (suc (suc zero))) *M12 (E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-2-11 = refl
mulEii-3-0 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) zero) ≡ E (suc (suc (suc zero))) zero
mulEii-3-0 = refl
mulEii-3-1 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc zero)) ≡ E (suc (suc (suc zero))) (suc zero)
mulEii-3-1 = refl
mulEii-3-2 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc zero))) ≡ E (suc (suc (suc zero))) (suc (suc zero))
mulEii-3-2 = refl
mulEii-3-3 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc zero))) (suc (suc (suc zero)))
mulEii-3-3 = refl
mulEii-3-4 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
mulEii-3-4 = refl
mulEii-3-5 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero)))))
mulEii-3-5 = refl
mulEii-3-6 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-3-6 = refl
mulEii-3-7 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-3-7 = refl
mulEii-3-8 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-3-8 = refl
mulEii-3-9 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-3-9 = refl
mulEii-3-10 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-3-10 = refl
mulEii-3-11 : (E (suc (suc (suc zero))) (suc (suc (suc zero)))) *M12 (E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-3-11 = refl
mulEii-4-0 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) zero) ≡ E (suc (suc (suc (suc zero)))) zero
mulEii-4-0 = refl
mulEii-4-1 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc zero)) ≡ E (suc (suc (suc (suc zero)))) (suc zero)
mulEii-4-1 = refl
mulEii-4-2 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc zero))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc zero))
mulEii-4-2 = refl
mulEii-4-3 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
mulEii-4-3 = refl
mulEii-4-4 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))
mulEii-4-4 = refl
mulEii-4-5 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))
mulEii-4-5 = refl
mulEii-4-6 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-4-6 = refl
mulEii-4-7 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-4-7 = refl
mulEii-4-8 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-4-8 = refl
mulEii-4-9 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-4-9 = refl
mulEii-4-10 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-4-10 = refl
mulEii-4-11 : (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero))))) *M12 (E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-4-11 = refl
mulEii-5-0 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) zero) ≡ E (suc (suc (suc (suc (suc zero))))) zero
mulEii-5-0 = refl
mulEii-5-1 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc zero))))) (suc zero)
mulEii-5-1 = refl
mulEii-5-2 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc zero))
mulEii-5-2 = refl
mulEii-5-3 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero)))
mulEii-5-3 = refl
mulEii-5-4 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero))))
mulEii-5-4 = refl
mulEii-5-5 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))
mulEii-5-5 = refl
mulEii-5-6 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-5-6 = refl
mulEii-5-7 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-5-7 = refl
mulEii-5-8 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-5-8 = refl
mulEii-5-9 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-5-9 = refl
mulEii-5-10 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-5-10 = refl
mulEii-5-11 : (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero)))))) *M12 (E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-5-11 = refl
mulEii-6-0 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) zero) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) zero
mulEii-6-0 = refl
mulEii-6-1 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc zero)
mulEii-6-1 = refl
mulEii-6-2 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero))
mulEii-6-2 = refl
mulEii-6-3 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero)))
mulEii-6-3 = refl
mulEii-6-4 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero))))
mulEii-6-4 = refl
mulEii-6-5 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero)))))
mulEii-6-5 = refl
mulEii-6-6 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-6-6 = refl
mulEii-6-7 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-6-7 = refl
mulEii-6-8 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-6-8 = refl
mulEii-6-9 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-6-9 = refl
mulEii-6-10 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-6-10 = refl
mulEii-6-11 : (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero))))))) *M12 (E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-6-11 = refl
mulEii-7-0 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) zero) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) zero
mulEii-7-0 = refl
mulEii-7-1 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero)
mulEii-7-1 = refl
mulEii-7-2 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero))
mulEii-7-2 = refl
mulEii-7-3 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero)))
mulEii-7-3 = refl
mulEii-7-4 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero))))
mulEii-7-4 = refl
mulEii-7-5 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero)))))
mulEii-7-5 = refl
mulEii-7-6 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-7-6 = refl
mulEii-7-7 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-7-7 = refl
mulEii-7-8 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-7-8 = refl
mulEii-7-9 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-7-9 = refl
mulEii-7-10 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-7-10 = refl
mulEii-7-11 : (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-7-11 = refl
mulEii-8-0 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) zero) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) zero
mulEii-8-0 = refl
mulEii-8-1 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc zero)
mulEii-8-1 = refl
mulEii-8-2 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc zero))
mulEii-8-2 = refl
mulEii-8-3 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc zero)))
mulEii-8-3 = refl
mulEii-8-4 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc zero))))
mulEii-8-4 = refl
mulEii-8-5 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc zero)))))
mulEii-8-5 = refl
mulEii-8-6 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-8-6 = refl
mulEii-8-7 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-8-7 = refl
mulEii-8-8 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-8-8 = refl
mulEii-8-9 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-8-9 = refl
mulEii-8-10 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-8-10 = refl
mulEii-8-11 : (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-8-11 = refl
mulEii-9-0 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) zero) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) zero
mulEii-9-0 = refl
mulEii-9-1 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc zero)
mulEii-9-1 = refl
mulEii-9-2 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc zero))
mulEii-9-2 = refl
mulEii-9-3 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc zero)))
mulEii-9-3 = refl
mulEii-9-4 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc zero))))
mulEii-9-4 = refl
mulEii-9-5 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc zero)))))
mulEii-9-5 = refl
mulEii-9-6 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-9-6 = refl
mulEii-9-7 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-9-7 = refl
mulEii-9-8 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-9-8 = refl
mulEii-9-9 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-9-9 = refl
mulEii-9-10 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-9-10 = refl
mulEii-9-11 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-9-11 = refl
mulEii-10-0 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) zero) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) zero
mulEii-10-0 = refl
mulEii-10-1 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc zero)
mulEii-10-1 = refl
mulEii-10-2 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc zero))
mulEii-10-2 = refl
mulEii-10-3 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc zero)))
mulEii-10-3 = refl
mulEii-10-4 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc zero))))
mulEii-10-4 = refl
mulEii-10-5 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc zero)))))
mulEii-10-5 = refl
mulEii-10-6 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-10-6 = refl
mulEii-10-7 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-10-7 = refl
mulEii-10-8 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-10-8 = refl
mulEii-10-9 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-10-9 = refl
mulEii-10-10 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-10-10 = refl
mulEii-10-11 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-10-11 = refl
mulEii-11-0 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) zero) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) zero
mulEii-11-0 = refl
mulEii-11-1 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc zero)) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc zero)
mulEii-11-1 = refl
mulEii-11-2 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc zero))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc zero))
mulEii-11-2 = refl
mulEii-11-3 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc zero)))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc zero)))
mulEii-11-3 = refl
mulEii-11-4 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc zero))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc zero))))
mulEii-11-4 = refl
mulEii-11-5 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc zero)))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc zero)))))
mulEii-11-5 = refl
mulEii-11-6 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc zero))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc zero))))))
mulEii-11-6 = refl
mulEii-11-7 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
mulEii-11-7 = refl
mulEii-11-8 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
mulEii-11-8 = refl
mulEii-11-9 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
mulEii-11-9 = refl
mulEii-11-10 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
mulEii-11-10 = refl
mulEii-11-11 : (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) *M12 (E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ≡ E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
mulEii-11-11 = refl
