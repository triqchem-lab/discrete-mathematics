{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.NormD1
-- ℤ[i] 范数线: x² + y² = 4·3ⁿ 的**全称分类**（A1 · D1–D3, 2026-11-25 收口）
--
-- 数学背景（oracle norm-d1 冻结, 2026-11-25; n ≤ 12 全域枚举一致 ✓）:
--   · **3 惰性于 ℤ[i]**: x² + y² ≡ 0 (mod 3) ⟹ 3∣x ∧ 3∣y（平方 mod 3 ∈ {0,1},
--     1+1 = 2 ≢ 0）⟹ 解集 = 3·解集(n−2) 双坐标剥层递降;
--   · **可解 ⟺ n 偶**: n = 2k 时 (x,y) = (±2·3^k, 0) / (0, ±2·3^k);
--     **n 奇无解** —— 与 d=3 线的 t=0 谱系（NoNormT0Even）互为镜像。
--   · 负部由 ℤ 符号对称给出（未形式化, 同 Witness/NormClassify 边界）。
--
-- 本件（0 postulate, 独立具名引理形态）:
--   §1 载体 solD1 / BSolD1（偶-only Σ; oracle norm-d1 冻结陈述）
--   §2 系数-1 版上界链 xCap-le/yCap-le（承 NormClassify 的 ≤from≡/≤≡r/mono-sq）
--   §3 9≤4 空型（新封闭空型; 16≤12 复用 NormClassify）
--   §4 base0-thm: 9 格（2 冻结解见证 + 7 absurd）+ catch-all ×2
--   §5 base1-thm: **无解定理**（16 格 absurd + catch-all ×2; 奇指数镜面）
--   §6 递降形状件（A1·D2, 2026-11-25; 骨架承 NormClassify §7 的 d=3 镜像）:
--      · nm3s2: suc²(3·A) ≢ 3·q（剥两层 suc 后归约到 no-suc-mult3, 3 行）
--      · x1-shape / x2-shape: x ≡ 3q+1 ⇒ x² ≡ suc(3·K₁);
--        x ≡ 3q+2 ⇒ x² ≡ suc(3·suc J)（suc⁴ 经 sym(cong suc (3suc J)) 归一）
--      · s1s0 / s0s1 / s1s1: 和式形状件 —— **六个非零 mod-3 组合全部化归
--        no-suc-mult3 / nm3s2 两核**（无需 no-suc4/5/8-mult3）
--   §7 递降核 descentD1: tri3-split 双坐标 9 案 = 8 矛盾 + 1 双剥层
--      （sol-nextD1: 9·(t₀²+s₀²) ≡ 4·3^(m+2) ⟹ t₀²+s₀² ≡ 4·3^m, mult3-inj 双次）
--   §8 全称 classifyD1（∀② 的 d=1 镜像; two-ind 两步归纳）:
--      pow3-dub（3^(2k) = (3^k)²）+ witness-satD1（(2·3^k)² + 0 = 4·3^(2k)）
--      + liftD1（ witness 升层, 索引 k ↦ suc k, dub-suc 归位）
--      ⇒ solD1 n x y ⇒ BSolD1 n x y（正向分类; 见证满足性由 witness-satD1 承载,
--        与 NormClassify §8 同边界——逆向蕴含不作陈述）。

module Sovereign.Application.Problems.RH.NormD1 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s)
open import Data.Nat.Properties
  using (≤-trans; m≤m+n; m≤n+m; +-suc; suc-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open import Sovereign.Application.Problems.RH.NormClassify
  using (mono-sq; ≤from≡; ≤≡r; ≤1↓; s≤0-empty; ↓4; 16≤12-empty;
         shape1; mul4-3out; distr-sym)
open import Sovereign.Application.Problems.RH.Mod3Core
  using (tri3-split; no-suc-mult3; sq-suc; sq3ʳ; mult3-inj; 3suc)
open NoNormPrelude
  using (pow3; dub; dub-suc; *-comm; *-assoc; +-zeroʳ)
open import Sovereign.Application.Problems.RH.Witness
  using (two-ind; sq3)

--------------------------------------------------------------------------------
-- §1. 载体（系数 1: x² + y², 区别于 d=3 的 x² + 3s²）
--------------------------------------------------------------------------------

solD1 : ℕ → ℕ → ℕ → Set
solD1 n x y = x * x + y * y ≡ 4 * pow3 n

-- v2 冻结（oracle norm-d1; 偶-only; 负部 ℤ 对称未形式化同前边界）
BSolD1 : ℕ → ℕ → ℕ → Set
BSolD1 n x y =
  Σ ℕ (λ k → n ≡ dub k × ((x ≡ 2 * pow3 k × y ≡ zero)
                        ⊎ (x ≡ zero × y ≡ 2 * pow3 k)))

--------------------------------------------------------------------------------
-- §2. 系数-1 版上界链（承 NormClassify 的 ≤from≡/≤≡r/mono-sq）
--------------------------------------------------------------------------------

xCap-le : ∀ N n x y → N ≤ x → solD1 n x y → N * N ≤ 4 * pow3 n
xCap-le N n x y le h =
  ≤-trans (mono-sq N x le)
          (≤from≡ (x * x) (y * y) (4 * pow3 n) h)

yCap-le : ∀ T n x y → T ≤ y → solD1 n x y → T * T ≤ 4 * pow3 n
yCap-le T n x y le h =
  ≤-trans (mono-sq T y le)
          (≤-trans (m≤n+m (y * y) (x * x))
                   (≤≡r (x * x + y * y) (4 * pow3 n) h))

--------------------------------------------------------------------------------
-- §3. 9≤4 空型（新封闭空型; 16≤12 复用 NormClassify）
--------------------------------------------------------------------------------

9≤4-empty : 3 * 3 ≤ 4 → ⊥
9≤4-empty h = s≤0-empty (↓4 h)

--------------------------------------------------------------------------------
-- §4. base0-thm（n = 0: x² + y² = 4; 冻结解 (0,2)/(2,0)）
--------------------------------------------------------------------------------

base0-thm : ∀ x y → solD1 0 x y → BSolD1 0 x y
base0-thm zero zero ()
base0-thm zero (suc zero) ()
base0-thm zero (suc (suc zero)) h = zero , refl , inj₂ (refl , refl)
base0-thm (suc zero) zero ()
base0-thm (suc zero) (suc zero) ()
base0-thm (suc zero) (suc (suc zero)) ()
base0-thm (suc (suc zero)) zero h = zero , refl , inj₁ (refl , refl)
base0-thm (suc (suc zero)) (suc zero) ()
base0-thm (suc (suc zero)) (suc (suc zero)) ()
-- x ≥ 3（任意 y）: 9 ≤ x² ≤ x² + y² ≡ 4
base0-thm (suc (suc (suc k))) y h =
  ⊥-elim (9≤4-empty (xCap-le 3 0 (suc (suc (suc k))) y (m≤m+n 3 k) h))
-- x = 0..2, y ≥ 3: 9 ≤ y² ≤ x² + y² ≡ 4
base0-thm zero (suc (suc (suc k))) h =
  ⊥-elim (9≤4-empty (yCap-le 3 0 zero (suc (suc (suc k))) (m≤m+n 3 k) h))
base0-thm (suc zero) (suc (suc (suc k))) h =
  ⊥-elim (9≤4-empty (yCap-le 3 0 (suc zero) (suc (suc (suc k))) (m≤m+n 3 k) h))
base0-thm (suc (suc zero)) (suc (suc (suc k))) h =
  ⊥-elim (9≤4-empty (yCap-le 3 0 (suc (suc zero)) (suc (suc (suc k))) (m≤m+n 3 k) h))

--------------------------------------------------------------------------------
-- §5. base1-thm（n = 1: x² + y² = 12 **无解** —— 奇指数镜面）
--     16 格全 absurd + x≥4 / y≥4 catch-all（16≤12 复用）
--------------------------------------------------------------------------------

base1-thm : ∀ x y → solD1 (suc zero) x y → ⊥
base1-thm zero zero ()
base1-thm zero (suc zero) ()
base1-thm zero (suc (suc zero)) ()
base1-thm zero (suc (suc (suc zero))) ()
base1-thm (suc zero) zero ()
base1-thm (suc zero) (suc zero) ()
base1-thm (suc zero) (suc (suc zero)) ()
base1-thm (suc zero) (suc (suc (suc zero))) ()
base1-thm (suc (suc zero)) zero ()
base1-thm (suc (suc zero)) (suc zero) ()
base1-thm (suc (suc zero)) (suc (suc zero)) ()
base1-thm (suc (suc zero)) (suc (suc (suc zero))) ()
base1-thm (suc (suc (suc zero))) zero ()
base1-thm (suc (suc (suc zero))) (suc zero) ()
base1-thm (suc (suc (suc zero))) (suc (suc zero)) ()
base1-thm (suc (suc (suc zero))) (suc (suc (suc zero))) ()
-- x ≥ 4（任意 y）: 16 ≤ x² ≤ x² + y² ≡ 12
base1-thm (suc (suc (suc (suc k)))) y h =
  ⊥-elim (16≤12-empty (xCap-le 4 1 (suc (suc (suc (suc k)))) y (m≤m+n 4 k) h))
-- x = 0..3, y ≥ 4: 16 ≤ y² ≤ x² + y² ≡ 12
base1-thm zero (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 zero (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base1-thm (suc zero) (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 (suc zero) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base1-thm (suc (suc zero)) (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 (suc (suc zero)) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base1-thm (suc (suc (suc zero))) (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 (suc (suc (suc zero))) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))

--------------------------------------------------------------------------------
-- §6a. 和式 mod-3 矛盾核 mirror: suc²(3·A) ≢ 3·q
--------------------------------------------------------------------------------

nm3s2 : ∀ A q → suc (suc (3 * A)) ≡ 3 * q → ⊥
nm3s2 A zero ()
nm3s2 A (suc q') h =
  no-suc-mult3 q' A
    (sym (trans (suc-injective (suc-injective (trans h (3suc q'))))
                (cong (λ z → suc z) (*-comm q' 3))))

--------------------------------------------------------------------------------
-- §6b. x² 形状引理 r=1: x ≡ 3q+1 ⇒ x² ≡ suc(3·K₁)
--------------------------------------------------------------------------------

x1-shape : ∀ q x → x ≡ suc (q * 3) → x * x ≡ suc (3 * ((q + q) + 3 * (q * q)))
x1-shape q x ex = begin
  x * x                                                                ≡⟨ cong₂ _*_ ex ex ⟩
  suc (q * 3) * suc (q * 3)                                           ≡⟨ sq-suc (q * 3) ⟩
  suc ((q * 3) + ((q * 3) + (q * 3) * (q * 3)))                        ≡⟨ cong suc (shape1 q) ⟩
  suc (3 * ((q + q) + 3 * (q * q)))                                    ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §6c. x² 形状引理 r=2: x ≡ 3q+2 ⇒ x² ≡ suc(3·suc J)（suc⁴ 经 3suc 归一）
--------------------------------------------------------------------------------

x2-shape : ∀ q x → x ≡ suc (suc (q * 3))
         → x * x ≡ suc (3 * suc (q + (q + ((q + q) + 3 * (q * q)))))
x2-shape q x ex = tt-shifted
  where
  K1 = (q + q) + 3 * (q * q)
  J  = q + (q + K1)
  a' = suc (q * 3)
  aa : a' * a' ≡ suc (3 * K1)
  aa = trans (sq-suc (q * 3)) (cong suc (shape1 q))
  inner1 : a' + a' * a' ≡ suc (suc ((q * 3) + 3 * K1))
  inner1 = trans (cong (λ z → suc (q * 3) + z) aa)
                 (cong suc (+-suc (q * 3) (3 * K1)))
  inner2 : a' + (a' + a' * a')
         ≡ suc (suc (suc ((q * 3) + ((q * 3) + 3 * K1))))
  inner2 = trans (cong (λ z → suc (q * 3) + z) inner1)
                 (trans (cong suc (+-suc (q * 3) (suc ((q * 3) + 3 * K1))))
                        (cong (suc ∘ suc)
                              (+-suc (q * 3) ((q * 3) + 3 * K1))))
  inner3 : (q * 3) + ((q * 3) + 3 * K1) ≡ J * 3
  inner3 = trans inner3core (*-comm 3 J)
    where
    inner3core : (q * 3) + ((q * 3) + 3 * K1) ≡ 3 * J
    inner3core = begin
      q * 3 + (q * 3 + 3 * K1)
        ≡⟨ cong (λ z → q * 3 + (z + 3 * K1)) (*-comm q 3) ⟩
      q * 3 + (3 * q + 3 * K1)
        ≡⟨ cong (λ z → q * 3 + z) (distr-sym 3 q K1) ⟩
      q * 3 + 3 * (q + K1)
        ≡⟨ cong (λ z → z + 3 * (q + K1)) (*-comm q 3) ⟩
      3 * q + 3 * (q + K1)
        ≡⟨ distr-sym 3 q (q + K1) ⟩
      3 * J
      ∎
      where open ≡-Reasoning
  tt : x * x ≡ suc (suc (suc (suc (J * 3))))
  tt = trans (cong₂ _*_ ex ex)
      (trans (sq-suc a')
      (trans (cong suc inner2)
             (cong (λ z → suc (suc (suc (suc z)))) inner3)))
  tt-shifted : x * x ≡ suc (3 * suc J)
  tt-shifted = trans tt (sym (cong suc (3suc J)))

--------------------------------------------------------------------------------
-- §6d. 和式形状件
--------------------------------------------------------------------------------

-- suc(3A) + 3B ≡ suc(3·(A+B))（LHS 定义归约 suc(3A+3B) + cong）
s1s0 : ∀ A B → suc (3 * A) + 3 * B ≡ suc (3 * (A + B))
s1s0 A B = cong suc (distr-sym 3 A B)

-- 3C + suc(3K) ≡ suc(3·(C+K))
s0s1 : ∀ C K → 3 * C + suc (3 * K) ≡ suc (3 * (C + K))
s0s1 C K = trans (+-suc (3 * C) (3 * K)) (cong suc (distr-sym 3 C K))

-- suc(3A) + suc(3B) ≡ suc²(3·(A+B))
s1s1 : ∀ A B → suc (3 * A) + suc (3 * B) ≡ suc (suc (3 * (A + B)))
s1s1 A B = trans (cong suc (+-suc (3 * A) (3 * B))) (cong (suc ∘ suc) (distr-sym 3 A B))

--------------------------------------------------------------------------------
-- §6e. x ≢ 0 (mod 3) 的矛盾（对 y 三案分支）
--------------------------------------------------------------------------------

xnz1 : ∀ m q x y → solD1 (suc (suc m)) x y → x ≡ suc (q * 3) → ⊥
xnz1 m q x y h ex = R
  where
  K1 = (q + q) + 3 * (q * q)
  xx : x * x ≡ suc (3 * K1)
  xx = x1-shape q x ex
  D : x * x + y * y ≡ 3 * (4 * pow3 (suc m))
  D = trans h (mul4-3out (pow3 (suc m)))
  R : ⊥
  R with tri3-split y
  ... | inj₁ (s₀ , ey) =
    ⊥-elim (no-suc-mult3 (K1 + 3 * (s₀ * s₀)) (4 * pow3 (suc m)) B)
    where
    yy : y * y ≡ 3 * (3 * (s₀ * s₀))
    yy = trans (cong₂ _*_ ey ey) (sq3ʳ s₀)
    S : x * x + y * y ≡ suc (3 * (K1 + 3 * (s₀ * s₀)))
    S = trans (cong (λ z → z + y * y) xx)
          (trans (cong (λ z → suc (3 * K1) + z) yy)
                 (s1s0 K1 (3 * (s₀ * s₀))))
    B : suc (3 * (K1 + 3 * (s₀ * s₀))) ≡ 3 * (4 * pow3 (suc m))
    B = trans (sym S) D
  ... | inj₂ (inj₁ (q' , ey)) =
    ⊥-elim (nm3s2 (K1 + K1') (4 * pow3 (suc m)) B)
    where
    K1' = (q' + q') + 3 * (q' * q')
    yy : y * y ≡ suc (3 * K1')
    yy = x1-shape q' y ey
    S : x * x + y * y ≡ suc (suc (3 * (K1 + K1')))
    S = trans (cong (λ z → z + y * y) xx)
          (trans (cong (λ z → suc (3 * K1) + z) yy) (s1s1 K1 K1'))
    B : suc (suc (3 * (K1 + K1'))) ≡ 3 * (4 * pow3 (suc m))
    B = trans (sym S) D
  ... | inj₂ (inj₂ (q' , ey)) =
    ⊥-elim (nm3s2 (K1 + suc J') (4 * pow3 (suc m)) B)
    where
    J' = q' + (q' + ((q' + q') + 3 * (q' * q')))
    yy : y * y ≡ suc (3 * suc J')
    yy = x2-shape q' y ey
    S : x * x + y * y ≡ suc (suc (3 * (K1 + suc J')))
    S = trans (cong (λ z → z + y * y) xx)
          (trans (cong (λ z → suc (3 * K1) + z) yy) (s1s1 K1 (suc J')))
    B : suc (suc (3 * (K1 + suc J'))) ≡ 3 * (4 * pow3 (suc m))
    B = trans (sym S) D

xnz2 : ∀ m q x y → solD1 (suc (suc m)) x y → x ≡ suc (suc (q * 3)) → ⊥
xnz2 m q x y h ex = R
  where
  K1 = (q + q) + 3 * (q * q)
  J  = q + (q + K1)
  xx : x * x ≡ suc (3 * suc J)
  xx = x2-shape q x ex
  D : x * x + y * y ≡ 3 * (4 * pow3 (suc m))
  D = trans h (mul4-3out (pow3 (suc m)))
  R : ⊥
  R with tri3-split y
  ... | inj₁ (s₀ , ey) =
    ⊥-elim (no-suc-mult3 (suc J + 3 * (s₀ * s₀)) (4 * pow3 (suc m)) B)
    where
    yy : y * y ≡ 3 * (3 * (s₀ * s₀))
    yy = trans (cong₂ _*_ ey ey) (sq3ʳ s₀)
    S : x * x + y * y ≡ suc (3 * (suc J + 3 * (s₀ * s₀)))
    S = trans (cong (λ z → z + y * y) xx)
          (trans (cong (λ z → suc (3 * suc J) + z) yy)
                 (s1s0 (suc J) (3 * (s₀ * s₀))))
    B : suc (3 * (suc J + 3 * (s₀ * s₀))) ≡ 3 * (4 * pow3 (suc m))
    B = trans (sym S) D
  ... | inj₂ (inj₁ (q' , ey)) =
    ⊥-elim (nm3s2 (suc J + K1') (4 * pow3 (suc m)) B)
    where
    K1' = (q' + q') + 3 * (q' * q')
    yy : y * y ≡ suc (3 * K1')
    yy = x1-shape q' y ey
    S : x * x + y * y ≡ suc (suc (3 * (suc J + K1')))
    S = trans (cong (λ z → z + y * y) xx)
          (trans (cong (λ z → suc (3 * suc J) + z) yy) (s1s1 (suc J) K1'))
    B : suc (suc (3 * (suc J + K1'))) ≡ 3 * (4 * pow3 (suc m))
    B = trans (sym S) D
  ... | inj₂ (inj₂ (q' , ey)) =
    ⊥-elim (nm3s2 (suc J + suc J') (4 * pow3 (suc m)) B)
    where
    J' = q' + (q' + ((q' + q') + 3 * (q' * q')))
    yy : y * y ≡ suc (3 * suc J')
    yy = x2-shape q' y ey
    S : x * x + y * y ≡ suc (suc (3 * (suc J + suc J')))
    S = trans (cong (λ z → z + y * y) xx)
          (trans (cong (λ z → suc (3 * suc J) + z) yy) (s1s1 (suc J) (suc J')))
    B : suc (suc (3 * (suc J + suc J'))) ≡ 3 * (4 * pow3 (suc m))
    B = trans (sym S) D

--------------------------------------------------------------------------------
-- §6f. y ≢ 0 (mod 3) 的矛盾（x ≡ t₀·3 已定; y = 3q+1 / 3q+2 两案）
--------------------------------------------------------------------------------

ynz1 : ∀ m t₀ q x y → solD1 (suc (suc m)) x y
     → x ≡ t₀ * 3 → y ≡ suc (q * 3) → ⊥
ynz1 m t₀ q x y h ex ey =
  ⊥-elim (no-suc-mult3 (3 * (t₀ * t₀) + K1) (4 * pow3 (suc m)) B)
  where
  K1 = (q + q) + 3 * (q * q)
  xx : x * x ≡ 3 * (3 * (t₀ * t₀))
  xx = trans (cong₂ _*_ ex ex) (sq3ʳ t₀)
  yy : y * y ≡ suc (3 * K1)
  yy = x1-shape q y ey
  S : x * x + y * y ≡ suc (3 * (3 * (t₀ * t₀) + K1))
  S = trans (cong₂ _+_ xx yy) (s0s1 (3 * (t₀ * t₀)) K1)
  D : x * x + y * y ≡ 3 * (4 * pow3 (suc m))
  D = trans h (mul4-3out (pow3 (suc m)))
  B : suc (3 * (3 * (t₀ * t₀) + K1)) ≡ 3 * (4 * pow3 (suc m))
  B = trans (sym S) D

ynz2 : ∀ m t₀ q x y → solD1 (suc (suc m)) x y
     → x ≡ t₀ * 3 → y ≡ suc (suc (q * 3)) → ⊥
ynz2 m t₀ q x y h ex ey =
  ⊥-elim (no-suc-mult3 (3 * (t₀ * t₀) + suc J') (4 * pow3 (suc m)) B)
  where
  J' = q + (q + ((q + q) + 3 * (q * q)))
  xx : x * x ≡ 3 * (3 * (t₀ * t₀))
  xx = trans (cong₂ _*_ ex ex) (sq3ʳ t₀)
  yy : y * y ≡ suc (3 * suc J')
  yy = x2-shape q y ey
  S : x * x + y * y ≡ suc (3 * (3 * (t₀ * t₀) + suc J'))
  S = trans (cong₂ _+_ xx yy) (s0s1 (3 * (t₀ * t₀)) (suc J'))
  D : x * x + y * y ≡ 3 * (4 * pow3 (suc m))
  D = trans h (mul4-3out (pow3 (suc m)))
  B : suc (3 * (3 * (t₀ * t₀) + suc J')) ≡ 3 * (4 * pow3 (suc m))
  B = trans (sym S) D

--------------------------------------------------------------------------------
-- §7. r=0 双剥层 + 递降核（A1·D2 收口）
--------------------------------------------------------------------------------

sol-nextD1 : ∀ m t₀ s₀ x y → solD1 (suc (suc m)) x y
           → x ≡ t₀ * 3 → y ≡ s₀ * 3 → solD1 m t₀ s₀
sol-nextD1 m t₀ s₀ x y h ex ey =
  mult3-inj (t₀ * t₀ + s₀ * s₀) (4 * pow3 m)
    (mult3-inj (3 * (t₀ * t₀ + s₀ * s₀)) (3 * (4 * pow3 m)) R)
  where
  sqx : x * x ≡ 3 * (3 * (t₀ * t₀))
  sqx = trans (cong₂ _*_ ex ex) (sq3ʳ t₀)
  sqy : y * y ≡ 3 * (3 * (s₀ * s₀))
  sqy = trans (cong₂ _*_ ey ey) (sq3ʳ s₀)
  A0 : x * x + y * y ≡ 3 * (3 * (t₀ * t₀)) + 3 * (3 * (s₀ * s₀))
  A0 = cong₂ _+_ sqx sqy
  B : 3 * (3 * (t₀ * t₀)) + 3 * (3 * (s₀ * s₀))
      ≡ 3 * (3 * (t₀ * t₀ + s₀ * s₀))
  B = trans (distr-sym 3 (3 * (t₀ * t₀)) (3 * (s₀ * s₀)))
            (cong (3 *_) (distr-sym 3 (t₀ * t₀) (s₀ * s₀)))
  P : x * x + y * y ≡ 3 * (3 * (t₀ * t₀ + s₀ * s₀))
  P = trans A0 B
  D : 4 * pow3 (suc (suc m)) ≡ 3 * (3 * (4 * pow3 m))
  D = trans (mul4-3out (pow3 (suc m))) (cong (3 *_) (mul4-3out (pow3 m)))
  Q : x * x + y * y ≡ 3 * (3 * (4 * pow3 m))
  Q = trans h D
  R : 3 * (3 * (t₀ * t₀ + s₀ * s₀)) ≡ 3 * (3 * (4 * pow3 m))
  R = trans (sym P) Q

descentD1 : ∀ m x y → solD1 (suc (suc m)) x y
          → Σ ℕ (λ t₀ → x ≡ t₀ * 3 × Σ ℕ (λ s₀ → y ≡ s₀ * 3 × solD1 m t₀ s₀))
descentD1 m x y h with tri3-split x
descentD1 m x y h | inj₁ (t₀ , ex) with tri3-split y
descentD1 m x y h | inj₁ (t₀ , ex) | inj₁ (s₀ , ey) =
  t₀ , ex , s₀ , ey , sol-nextD1 m t₀ s₀ x y h ex ey
descentD1 m x y h | inj₁ (t₀ , ex) | inj₂ (inj₁ (q , ey)) =
  ⊥-elim (ynz1 m t₀ q x y h ex ey)
descentD1 m x y h | inj₁ (t₀ , ex) | inj₂ (inj₂ (q , ey)) =
  ⊥-elim (ynz2 m t₀ q x y h ex ey)
descentD1 m x y h | inj₂ (inj₁ (q , ex)) = ⊥-elim (xnz1 m q x y h ex)
descentD1 m x y h | inj₂ (inj₂ (q , ex)) = ⊥-elim (xnz2 m q x y h ex)

--------------------------------------------------------------------------------
-- §8. 全称分类 classifyD1（A1·D3; 两步归纳: §4/§5 基案 + §7 递降核 + §8 提升）
--------------------------------------------------------------------------------

-- 3^(2k) = (3^k)²（dub × pow3 桥; 归纳; 归纳步复用 Witness sq3）
pow3-dub : ∀ k → pow3 (dub k) ≡ pow3 k * pow3 k
pow3-dub zero = refl
pow3-dub (suc k) =
  trans (cong pow3 (dub-suc k))
  (trans (cong (λ z → 3 * (3 * z)) (pow3-dub k))
         (sym (sq3 (pow3 k))))

-- 见证: (2·3^k)² + 0 ≡ 4·3^(2k)（oracle norm-d1 冻结解的正部形态）
witness-satD1 : ∀ k → solD1 (dub k) (2 * pow3 k) zero
witness-satD1 k =
  trans (+-zeroʳ ((2 * pow3 k) * (2 * pow3 k)))
  (trans sq2-chain (sym (cong (4 *_) (pow3-dub k))))
  where
  sq2-chain : (2 * pow3 k) * (2 * pow3 k) ≡ 4 * (pow3 k * pow3 k)
  sq2-chain =
    trans (*-assoc 2 (pow3 k) (2 * pow3 k))
    (trans (cong (2 *_)
                 (trans (*-comm (pow3 k) (2 * pow3 k))
                        (*-assoc 2 (pow3 k) (pow3 k))))
           (sym (*-assoc 2 2 (pow3 k * pow3 k))))

-- BSolD1 提升: (t₀,s₀) 在层 m ⇒ (3·t₀, 3·s₀) 在层 m+2
-- （右乘 3 经 *-assoc + *-comm 归一到 pow3 (suc k) = 3·3^k）
liftD1 : ∀ m t₀ s₀ x y → BSolD1 m t₀ s₀ → x ≡ t₀ * 3 → y ≡ s₀ * 3
       → BSolD1 (suc (suc m)) x y
liftD1 m t₀ s₀ x y (k , e-m , inj₁ (e-t , e-s)) e-x e-y =
  suc k , trans (cong (λ z → suc (suc z)) e-m) (sym (dub-suc k)) ,
      inj₁ (trans (trans e-x (cong (_* 3) e-t))
                  (trans (*-assoc 2 (pow3 k) 3)
                         (cong (2 *_) (*-comm (pow3 k) 3))) ,
            trans e-y (cong (_* 3) e-s))
liftD1 m t₀ s₀ x y (k , e-m , inj₂ (e-t , e-s)) e-x e-y =
  suc k , trans (cong (λ z → suc (suc z)) e-m) (sym (dub-suc k)) ,
      inj₂ (trans e-x (cong (_* 3) e-t) ,
            trans (trans e-y (cong (_* 3) e-s))
                  (trans (*-assoc 2 (pow3 k) 3)
                         (cong (2 *_) (*-comm (pow3 k) 3))))

-- ★ 全称分类 ∀② 的 d=1 镜像: x² + y² = 4·3ⁿ ⇔ BSolD1 n x y
classifyD1 : ∀ n x y → solD1 n x y → BSolD1 n x y
classifyD1 = two-ind P base0 base1 step
  where
  P : ℕ → Set
  P n = ∀ x y → solD1 n x y → BSolD1 n x y
  base0 : P zero
  base0 = base0-thm
  -- n = 1: 奇指数无解定理（§5）—— 空指域上的空洞见证
  base1 : P (suc zero)
  base1 x y h = ⊥-elim (base1-thm x y h)
  step : ∀ m → P m → P (suc (suc m))
  step m IH x y h = liftD1 m t₀ s₀ x y (IH t₀ s₀ solm) ex ey
    where
    w    = descentD1 m x y h
    t₀   = proj₁ w
    rest = proj₂ w
    ex   = proj₁ rest
    rest2 = proj₂ rest
    s₀   = proj₁ rest2
    rest3 = proj₂ rest2
    ey   = proj₁ rest3
    solm = proj₂ rest3
