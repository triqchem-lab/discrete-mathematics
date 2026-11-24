{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.NormClassify
-- 范数方程 n=0 基案全称分类（M2 · A2.3 首件; base1/base2 与递降核待续）
-- 陈述冻结: oracle_rh_tables.py norm v2
--
-- 数学背景: t² + 3s² = 4·3ⁿ 取 n=0 即 t² + 3s² = 4。
-- ℕ 正部解恰两枚: (1,1) 与 (2,0)（oracle n=0 枚举一致; 负部由 ℤ 符号对称给出, 见 Witness 头注）。
-- 证明骨架: 16 格模式全覆盖 —— 12 格小值枚举（含 10 格 absurd + 2 格冻结解见证）,
-- 4 格 catch-all（t≥3 / t=0,s≥3 / t=1,s≥3 / t=2,s≥3）由
-- 「t≥3 ⇒ 9 ≤ t²」「s≥3 ⇒ 27 ≤ 3s²」配 「t² ≤ t²+3s² ≡ 4」反证。
-- 全部 ≤-链走显式类型引理（9≤4-empty / 27≤4-empty）, 不用 absurd-lambda
-- —— 2026-11-24 实测 (λ ()) 于此处触发 UnsolvedMetaVariables（隐式参数无解）,
-- 具名封闭引理的 absurd 子句 `() ` 则机械通过。
module Sovereign.Application.Problems.RH.NormClassify where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; *-monoˡ-≤; *-monoʳ-≤; m≤m+n; m≤n+m)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open NoNormPrelude using (pow3)

--------------------------------------------------------------------------------

sol : ℕ → ℕ → ℕ → Set
sol n t s = t * t + 3 * (s * s) ≡ 4 * pow3 n

BSol0 : ℕ → ℕ → Set
BSol0 t s = (t ≡ 1 × s ≡ 1) ⊎ (t ≡ 2 × s ≡ 0)

≤from≡ : ∀ a b r → a + b ≡ r → a ≤ r
≤from≡ a b r h = subst (λ z → a ≤ z) h (m≤m+n a b)

≤≡r : ∀ x r → x ≡ r → x ≤ r
≤≡r x r h = subst (λ z → x ≤ z) h ≤-refl

mono-sq : ∀ (b t : ℕ) → b ≤ t → b * b ≤ t * t
mono-sq b t le = ≤-trans (*-monoʳ-≤ b le) (*-monoˡ-≤ t le)

--------------------------------------------------------------------------------
-- 封闭反证引理（显式类型; 不用 absurd-lambda —— 2026-11-24 实测其隐式参数无解）
-- 注: --cubical 下 absurd 子句只看**顶层**构造子, 故 `9 ≤ 4` 不能直接 `()`
-- （顶层 s≤s 合法）; 须用 ≤1↓ 显式降层到 `suc _ ≤ zero`（两个数据构造子
-- z≤n/s≤s 均被排除, 覆盖检查器裁决空型, 同 ≡ 型 absurd 同一机制）。
--------------------------------------------------------------------------------

≤1↓ : ∀ {a b} → suc a ≤ suc b → a ≤ b
≤1↓ (s≤s p) = p

s≤0-empty : ∀ {a} → suc a ≤ zero → ⊥
s≤0-empty ()

9≤4-empty : 3 * 3 ≤ 4 → ⊥
9≤4-empty h = s≤0-empty (≤1↓ (≤1↓ (≤1↓ (≤1↓ h))))

27≤4-empty : 3 * (3 * 3) ≤ 4 → ⊥
27≤4-empty h = s≤0-empty (≤1↓ (≤1↓ (≤1↓ (≤1↓ h))))

--------------------------------------------------------------------------------
-- catch-all 反证核（全显式签名; stdlib *-monoˡ-≤ 为 Preservesʳ 展开型,
-- 深层隐参合一实测 UnsolvedMetaVariables —— 故引理逐参调用, 零隐参待解）
--------------------------------------------------------------------------------

-- t ≥ 3: 9 ≤ t² ≤ t² + 3s² ≡ 4（≤from≡: h 形如 t² + 3s² ≡ 4 ⇒ t² ≤ 4）
t3-absurd : ∀ t s → 3 ≤ t → sol 0 t s → ⊥
t3-absurd t s le h =
  9≤4-empty
    (≤-trans
      (mono-sq 3 t le)
      (≤from≡ (t * t) (3 * (s * s)) 4 h))

-- hi: 3s² ≤ t² + 3s² ≡ 4
hi3s : ∀ t s → sol 0 t s → 3 * (s * s) ≤ 4
hi3s t s h =
  ≤-trans
    (m≤n+m (3 * (s * s)) (t * t))
    (≤≡r (t * t + 3 * (s * s)) 4 h)

-- lo: 27 = 3·(3·3) ≤ 3s²（*-monoʳ-≤ = 左固定 k*m ≤ k*n; monoˡ 是右固定 *k 形式）
lo3s : ∀ s → 3 ≤ s → 3 * (3 * 3) ≤ 3 * (s * s)
lo3s s le = *-monoʳ-≤ 3 (mono-sq 3 s le)

-- 合成: 27 ≤ 3s² ≤ 4 ⇒ ⊥
-- （签名不带 t: 2026-11-24 实测 2.9.0-nightly 下「签名级未使用显式参数」
--   触发 UnsolvedMetaVariables; 子句级未使用 h 不触发, 已用探针二分定位）
s3-absurd : ∀ s → 3 * (s * s) ≤ 4 → 3 * (3 * 3) ≤ 3 * (s * s) → ⊥
s3-absurd s hi lo = 27≤4-empty (≤-trans lo hi)

--------------------------------------------------------------------------------
-- base0 全称分类: t ∈ {0,1,2,≥3} × s ∈ {0,1,2,≥3} 全覆盖
--------------------------------------------------------------------------------

base0-thm : ∀ t s → sol 0 t s → BSol0 t s
base0-thm zero zero ()
base0-thm zero (suc zero) ()
base0-thm zero (suc (suc zero)) ()
base0-thm (suc zero) zero ()
base0-thm (suc zero) (suc zero) h = inj₁ ( refl , refl )
base0-thm (suc zero) (suc (suc zero)) ()
base0-thm (suc (suc zero)) zero h = inj₂ ( refl , refl )
base0-thm (suc (suc zero)) (suc zero) ()
base0-thm (suc (suc zero)) (suc (suc zero)) ()
-- t ≥ 3（任意 s）
base0-thm (suc (suc (suc k))) s h =
  ⊥-elim (t3-absurd (suc (suc (suc k))) s (m≤m+n 3 k) h)
-- t = 0, s ≥ 3
base0-thm zero (suc (suc (suc k))) h =
  ⊥-elim (s3-absurd (suc (suc (suc k)))
    (hi3s zero (suc (suc (suc k))) h)
    (lo3s (suc (suc (suc k))) (m≤m+n 3 k)))
-- t = 1, s ≥ 3
base0-thm (suc zero) (suc (suc (suc k))) h =
  ⊥-elim (s3-absurd (suc (suc (suc k)))
    (hi3s (suc zero) (suc (suc (suc k))) h)
    (lo3s (suc (suc (suc k))) (m≤m+n 3 k)))
-- t = 2, s ≥ 3
base0-thm (suc (suc zero)) (suc (suc (suc k))) h =
  ⊥-elim (s3-absurd (suc (suc (suc k)))
    (hi3s (suc (suc zero)) (suc (suc (suc k))) h)
    (lo3s (suc (suc (suc k))) (m≤m+n 3 k)))
