{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselCRTSynth
-- G4 CRT 合成定理：SOVEREIGN_LCM = 3¹¹·2¹⁶ 的根分类 8-case 合成
--
-- 数学背景：x² ≡ 1 (mod N) ⟺ [3¹¹ ∣ x²∸1 ∧ 2¹⁶ ∣ x²∸1]（CRT 正交分解）
--   3 侧二分：pow3 11 ∣ x∸1 ⊎ pow3 11 ∣ suc x（Hensel 提升——px 桥 + three-side + core 全幂收缩）
--   2 侧四分：fourfold′（Dec 外置，加法判定）
--   合成：2 × 4 = 8-case 结构（唯一性等式层 x < N → x = rootᵢ 属后续批）
--
-- 核心原则：
-- 1. 策略 E CRT 正交分解（锚定 N 的因子分解，零 mod-helper 零 ∣?）
-- 2. 加法替代除法（消去律=除法影子——全程 divides 字段 + 闭合 clash）
-- 3. 复用优先（px/core/three-side/two-side/fourfold′/two-add 全部引用，零复制）
--
-- 包含：crt-split（N 正交分解）、pow3-side（3¹¹ 侧二分提升）、s-lcm-eight-case（8-case 合成）

module Sovereign.Algebra.HenselCRTSynth where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_)
open import Data.Nat.Divisibility using (_∣_; divides; ∣-trans; ∣m+n∣m⇒∣n; m∣m*n; n∣m*n)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor)
open import Data.Nat.Properties using (*-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec)
open import Sovereign.Algebra.Hensel3Side using (pow3; px; three-side; core)
open import Sovereign.Algebra.Hensel2Side using (pow2; two-side; fourfold′; two-add)
open import Sovereign.Algebra.SovereignLCMRoots using (SOVEREIGN_LCM)

--------------------------------------------------------------------------------
-- §1. CRT 正交分解：SOVEREIGN_LCM = 3¹¹ · 2¹⁶
--------------------------------------------------------------------------------

-- 3¹¹ ∣ N（m∣m*n 型，定义性：pow3 11 * pow2 16 ≡ 177147 * 65536 = N）
pow3-11-div : pow3 11 ∣ SOVEREIGN_LCM
pow3-11-div = m∣m*n {m = pow3 11} (pow2 16)

-- 2¹⁶ ∣ N（n∣m*n 型）
pow2-16-div : pow2 16 ∣ SOVEREIGN_LCM
pow2-16-div = n∣m*n (pow3 11) {n = pow2 16}

-- CRT 正交分解：N ∣ n → 3¹¹ ∣ n × 2¹⁶ ∣ n
crt-split : ∀ n → SOVEREIGN_LCM ∣ n → pow3 11 ∣ n × pow2 16 ∣ n
crt-split n h = ∣-trans pow3-11-div h , ∣-trans pow2-16-div h

--------------------------------------------------------------------------------
-- §2. 3¹¹ 侧二分提升（Hensel 提升核心件）
--------------------------------------------------------------------------------

-- 3 ∣ 3¹¹（全幂含 3，定义性 pow3 11 ≡ 3 * pow3 10）
three∣pow3 : 3 ∣ pow3 11
three∣pow3 = m∣m*n {m = 3} (pow3 10)

-- 3 ∣ 2 封闭 clash（三模式：0·3 / 3 / (2+q)·3 深度）
clash-3-2 : 3 ∣ 2 → ⊥
clash-3-2 (divides zero ())          -- 2 ≡ 0 封闭 clash
clash-3-2 (divides (suc zero) ())    -- 2 ≡ 3 封闭 clash
clash-3-2 (divides (suc (suc q)) ()) -- 2 ≡ (2+q)·3 ≥ 6 深度 clash

-- 3 偶性交替：3∣m → ¬3∣suc(suc m)（two-add 加法桥 + ∣m+n∣m⇒∣n 收缩至 3∣2）
not3-sum : ∀ m → 3 ∣ m → ¬ (3 ∣ suc (suc m))
not3-sum m h2 h2s = clash-3-2 (∣m+n∣m⇒∣n (subst (3 ∣_) (sym (two-add m)) h2s) h2)

-- 3-互素全幂：¬3∣a → Coprime a (pow3 k)（core 收缩分类，零复制 coprime-a-pow2 范式）
coprime-a-pow3 : ∀ k a → ¬ (3 ∣ a) → Coprime a (pow3 k)
coprime-a-pow3 k a nt3 {e} (e∣a , e∣pow3) with core k e e∣pow3
...   | inj₁ e≡1 = e≡1
...   | inj₂ 3∣e = ⊥-elim (nt3 (∣-trans 3∣e e∣a))

-- 全幂收缩（coprime-divisor 型，镜像 pow2-∣-iter）
pow3-∣-iter : ∀ k a b → Coprime a (pow3 k) → pow3 k ∣ a * b → pow3 k ∣ b
pow3-∣-iter k a b c h = coprime-divisor (coprime-3-a-aux k a c) h
  where
    coprime-3-a-aux : ∀ k a → Coprime a (pow3 k) → Coprime (pow3 k) a
    coprime-3-a-aux k a c (d∣pow3 , d∣a) = c (d∣a , d∣pow3)


-- px 桥（顶层具名）：x = suc m 时 x*x∸1 ≡ m * suc (suc m)
px-bridge-r : ∀ m → pow3 11 ∣ suc m * suc m ∸ 1 → pow3 11 ∣ m * suc (suc m)
px-bridge-r m h = subst (pow3 11 ∣_) (sym (px (suc m))) h

px-bridge-l : ∀ m → pow3 11 ∣ m * suc (suc m) → pow3 11 ∣ suc (suc m) * m
px-bridge-l m h = subst (pow3 11 ∣_) (*-comm m (suc (suc m))) h

-- 3¹¹ 侧二分·suc m 形（单 with：three-side 应用与收缩组合，分离引理避免双重 with 联合归一化）
pow3-side-suc : ∀ m → pow3 11 ∣ suc m * suc m ∸ 1
              → pow3 11 ∣ m ⊎ pow3 11 ∣ suc (suc m)
pow3-side-suc m h = go (three-side (suc m) (∣-trans three∣pow3 h))
  where
    go : 3 ∣ m ⊎ 3 ∣ suc (suc m) → pow3 11 ∣ m ⊎ pow3 11 ∣ suc (suc m)
    go (inj₁ 3∣m) = inj₁ (pow3-∣-iter 11 (suc (suc m)) m
                          (coprime-a-pow3 11 (suc (suc m)) (not3-sum m 3∣m))
                          (px-bridge-l m (px-bridge-r m h)))
    go (inj₂ 3∣ssm) = inj₂ (pow3-∣-iter 11 m (suc (suc m))
                            (coprime-a-pow3 11 m (λ hd → not3-sum m hd 3∣ssm))
                            (px-bridge-r m h))

-- 3¹¹ 侧二分：3¹¹ ∣ x²∸1 → 3¹¹ ∣ x∸1 ⊎ 3¹¹ ∣ suc x（x 分裂 + suc m 形收缩）
pow3-side : ∀ x → pow3 11 ∣ x * x ∸ 1 → pow3 11 ∣ x ∸ 1 ⊎ pow3 11 ∣ suc x
pow3-side x h with x
...   | zero = inj₁ (divides zero refl)
...   | suc m = pow3-side-suc m h

--------------------------------------------------------------------------------
-- §3. 8-case 合成（2 × 4）
--------------------------------------------------------------------------------

-- 双二分合成（2×2 结构）
s-lcm-two-dichotomy : ∀ x → SOVEREIGN_LCM ∣ x * x ∸ 1
  → (pow3 11 ∣ x ∸ 1 ⊎ pow3 11 ∣ suc x)
  × (pow2 15 ∣ x ∸ 1 ⊎ pow2 15 ∣ suc x)
s-lcm-two-dichotomy x h =
  pow3-side x (proj₁ (crt-split (x * x ∸ 1) h)) ,
  two-side x (proj₂ (crt-split (x * x ∸ 1) h))

-- 8-case 合成定理：N ∣ x²∸1 → [3¹¹ 二分] × [2¹⁶ 四分] = 2 × 4 = 8-case 结构
s-lcm-eight-case : ∀ x → SOVEREIGN_LCM ∣ x * x ∸ 1
  → Dec (pow2 16 ∣ x ∸ 1) → Dec (pow2 16 ∣ suc x)
  → (pow3 11 ∣ x ∸ 1 ⊎ pow3 11 ∣ suc x)
  × ((pow2 16 ∣ x ∸ 1)
   ⊎ (pow2 16 ∣ suc x)
   ⊎ (pow2 15 ∣ x ∸ 1 × ¬ pow2 16 ∣ x ∸ 1)
   ⊎ (pow2 15 ∣ suc x × ¬ pow2 16 ∣ suc x))
s-lcm-eight-case x h d1 d2 =
  pow3-side x (proj₁ (crt-split (x * x ∸ 1) h)) ,
  fourfold′ x (proj₂ (crt-split (x * x ∸ 1) h)) d1 d2
