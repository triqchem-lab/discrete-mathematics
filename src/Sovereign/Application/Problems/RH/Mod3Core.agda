{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.Mod3Core
-- ℕ 层 mod-3 递降基建（M2 · A2.3-续 前置; 三案枚举路线, rh-allcurves-plan §五）
--
-- 数学背景:
--   递降步: sol n t s（n≥2）⇒ t² ≡ 0 (mod 3)（p=3 素, t²+3s² ≡ RHS ≡ 0）⇒ 3∣t。
--   取 t = 3t₀ 剥一层得 sol (n−1) s t₀; 再剥得 sol (n−2) t₀ s₀
--   —— 即 oracle v2 冻结的「解集 = 3·解集(n−2)」。
--   本模块是三案枚举的机械件:
--   §1 三分拆 tri3-split: ∀ t, t ∈ {q·3, suc(q·3), suc(suc(q·3))}
--       （**右乘形式**: +3 平移 = cong suc∘suc∘suc, 零算术链——2026-11-24 设计决策,
--        左乘形式 3*q 的平移需 +-suc×3 + mul3-suc 链, 白付三层）
--   §2 矛盾核 no-suc-mult3: suc (3*A) ≢ 3*q（互递归双层归纳; r=1/2 案用）
--   §3 形状件 sq-suc: (suc a)² ≡ suc (a + (a + a²))（stdlib *-suc 即得）
--
-- 0 postulate。复用 stdlib: suc-injective / +-suc / *-cancelˡ-≡;
-- NoNormPrelude: pow3 / *-assoc / *-comm / *-distribˡ / +-zeroʳ;
-- Witness（兄弟件, 非 import 依赖）: sq3（这里自带 comm 版本 sq3ʳ）。

module Sovereign.Application.Problems.RH.Mod3Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
open import Data.Nat.Properties using (suc-injective; +-suc; *-suc; *-cancelˡ-≡)
open import Function using (_∘_)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open NoNormPrelude using (pow3; *-assoc; *-comm; *-distribˡ; +-zeroʳ)

--------------------------------------------------------------------------------
-- §1. 三分拆（右乘形式）
--------------------------------------------------------------------------------

Tri3 : ℕ → Set
Tri3 t = (Σ ℕ (λ q → t ≡ q * 3))
       ⊎ ((Σ ℕ (λ q → t ≡ suc (q * 3)))
       ⊎ (Σ ℕ (λ q → t ≡ suc (suc (q * 3)))))

-- 平移引理: P t ⇒ P (t+3) 各案升值一位（右乘形式下全是 cong）
--   r=0: t ≡ q·3 ⇒ t+3 ≡ suc q·3（(suc q)*3 = 3 + q*3 = suc³(q*3) 定义归约）
tri3-shift-r0 : ∀ q → suc (suc (suc (q * 3))) ≡ suc q * 3
tri3-shift-r0 q = refl

tri3-shift : ∀ t → Tri3 t → Tri3 (suc (suc (suc t)))
tri3-shift t (inj₁ (q , e)) =
  inj₁ (suc q , trans (cong (λ z → suc (suc (suc z))) e) (tri3-shift-r0 q))
tri3-shift t (inj₂ (inj₁ (q , e))) =
  inj₂ (inj₁ (suc q , trans (cong (suc ∘ suc ∘ suc) e)
    (cong suc (tri3-shift-r0 q))))
tri3-shift t (inj₂ (inj₂ (q , e))) =
  inj₂ (inj₂ (suc q , trans (cong (suc ∘ suc ∘ suc) e)
    (cong (suc ∘ suc) (tri3-shift-r0 q))))

-- 三步配对归纳: go t : Tri3 t × Tri3 (suc t) × Tri3 (suc (suc t))
tri3-go : ∀ t → Tri3 t × Tri3 (suc t) × Tri3 (suc (suc t))
tri3-go zero =
  ( inj₁ (zero , refl)
  , inj₂ (inj₁ (zero , refl))
  , inj₂ (inj₂ (zero , refl)) )
tri3-go (suc t) =
  ( proj₁ (proj₂ (tri3-go t))
  , proj₂ (proj₂ (tri3-go t))
  , tri3-shift t (proj₁ (tri3-go t)) )

tri3-split : ∀ t → Tri3 t
tri3-split t = proj₁ (tri3-go t)

--------------------------------------------------------------------------------
-- §2. 矛盾核: suc (3*A) ≢ 3*q（互递归双层归纳）
--------------------------------------------------------------------------------

-- 互递归双层归纳（都在 A 上递降）
mutual
  -- 形状件: 3 * suc A ≡ suc A * 3 ≡ suc³ (A * 3)（comm + 定义归约）
  3suc : ∀ A → 3 * suc A ≡ suc (suc (suc (A * 3)))
  3suc A = *-comm 3 (suc A)

  -- 辅助: 3*A ≢ suc (suc (q*3))（A 归纳; 递回 no-suc-mult3 于 A-1）
  no-suc2-mult3 : ∀ A q → 3 * A ≡ suc (suc (q * 3)) → ⊥
  no-suc2-mult3 zero q ()
  no-suc2-mult3 (suc A) q h =
    no-suc-mult3 A q
      (trans (cong suc (sym (*-comm A 3)))
        (trans (suc-injective (suc-injective (trans (sym (3suc A)) h)))
               (*-comm q 3)))

  no-suc-mult3 : ∀ A q → suc (3 * A) ≡ 3 * q → ⊥
  no-suc-mult3 A zero ()
  no-suc-mult3 A (suc q) h =
    no-suc2-mult3 A q (suc-injective (trans h (3suc q)))

--------------------------------------------------------------------------------
-- §3. 形状件
--------------------------------------------------------------------------------

-- (suc a)² ≡ suc (a + (a + a²))（定义展开到 suc (a + a*suc a) 后套 *-suc）
sq-suc : ∀ a → (suc a) * (suc a) ≡ suc (a + (a + a * a))
sq-suc a = cong (λ z → suc (a + z)) (*-suc a a)

-- 3 消去（stdlib *-cancelˡ-≡, NonZero 3 实例自动）
mult3-inj : ∀ a b → 3 * a ≡ 3 * b → a ≡ b
mult3-inj a b h = *-cancelˡ-≡ a b 3 h

--------------------------------------------------------------------------------
-- §4. mod-3 平方三分（r=0 案 t² ≡ 3·(3·(q²)); r=1/2 案 t² 含 suc³(3·K) 形）
--------------------------------------------------------------------------------

-- 右乘平方: (q*3)² ≡ 3*(3*(q*q))（comm 归位 + Witness 同款 sq3 链）
sq3ʳ : ∀ q → (q * 3) * (q * 3) ≡ 3 * (3 * (q * q))
sq3ʳ q = trans (cong₂ _*_ (*-comm q 3) (*-comm q 3)) (sq3L q)
  where
  sq3L : ∀ q → (3 * q) * (3 * q) ≡ 3 * (3 * (q * q))
  sq3L q = trans (*-assoc 3 q (3 * q))
         (trans (cong (3 *_) (*-comm q (3 * q)))
         (trans (cong (3 *_) (*-assoc 3 q q))
                refl))
