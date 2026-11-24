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
  using (≤-trans; ≤-refl; *-monoˡ-≤; *-monoʳ-≤; m≤m+n; m≤n+m; +-comm; +-assoc; +-suc; suc-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open import Function using (_∘_)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open import Sovereign.Application.Problems.RH.Mod3Core
  using (tri3-split; no-suc-mult3; 3suc; sq-suc; mult3-inj; sq3ʳ)
open NoNormPrelude using (pow3; *-assoc; *-comm; *-distribˡ; +-zeroʳ; dub; dub-suc)

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

--------------------------------------------------------------------------------
-- §4b. 通用 catch-all 反证核（参数化 RHS; base1/base2 复用）
--------------------------------------------------------------------------------

-- t 上界链: N ≤ t ⇒ N² ≤ t² ≤ t²+3s² ≡ 4·3ⁿ（返回 ≤ 证据）
-- s 上界链: T ≤ s ⇒ 3T² ≤ 3s² ≤ t²+3s² ≡ 4·3ⁿ
-- 【内核 bug 绕行 2026-11-24 微探针实证】--cubical 下对「domain 为 ≤ 型」的
-- telescope 函数参数（cap : X ≤ Y → ⊥）施应用 → codomain 被吞 → CannotApply
-- （变量作参数/整体传递均正常, 仅施应用炸; domain 为 ℕ 则正常, 见探针 M系列）。
-- 故本件只返回 ≤ 证据, 调用方对**具名**空型引理施应用（具名应用不受 bug 影响,
-- s3-absurd/27≤4-empty 链已证）。
tCap-le : ∀ N n t s → N ≤ t → sol n t s → N * N ≤ 4 * pow3 n
tCap-le N n t s le h =
  ≤-trans
    (mono-sq N t le)
    (≤from≡ (t * t) (3 * (s * s)) (4 * pow3 n) h)

sCap-le : ∀ T n t s → T ≤ s → sol n t s → 3 * (T * T) ≤ 4 * pow3 n
sCap-le T n t s le h =
  ≤-trans
    (*-monoʳ-≤ 3 (mono-sq T s le))
    (≤-trans
      (m≤n+m (3 * (s * s)) (t * t))
      (≤≡r (t * t + 3 * (s * s)) (4 * pow3 n) h))

-- 四步降层（≤1↓ × 4: suc⁴a ≤ suc⁴b → a ≤ b）
↓4 : ∀ {a b} → suc (suc (suc (suc a))) ≤ suc (suc (suc (suc b))) → a ≤ b
↓4 h = ≤1↓ (≤1↓ (≤1↓ (≤1↓ h)))

-- 封闭空型（absurd 由覆盖检查器裁决: 降层到 suc _ ≤ zero）
16≤12-empty : 4 * 4 ≤ 12 → ⊥
16≤12-empty h = s≤0-empty (↓4 (↓4 (↓4 h)))

27≤12-empty : 3 * (3 * 3) ≤ 12 → ⊥
27≤12-empty h = s≤0-empty (↓4 (↓4 (↓4 h)))

49≤36-empty : 7 * 7 ≤ 36 → ⊥
49≤36-empty h = s≤0-empty (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 h)))))))))

48≤36-empty : 3 * (4 * 4) ≤ 36 → ⊥
48≤36-empty h = s≤0-empty (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 (↓4 h)))))))))

--------------------------------------------------------------------------------
-- §5. base1 全称分类（n = 1: t² + 3s² = 12; 冻结解 (0,2) 与 (3,1)）
-- oracle v2: n=1 奇, k=0: t ∈ {0, 3^1=3}; (t,s) = (0,±2·3⁰) / (±3,±3⁰)
--------------------------------------------------------------------------------

BSol1 : ℕ → ℕ → Set
BSol1 t s = (t ≡ zero × s ≡ suc (suc zero)) ⊎ (t ≡ 3 × s ≡ suc zero)

base1-thm : ∀ t s → sol (suc zero) t s → BSol1 t s
base1-thm zero zero ()
base1-thm zero (suc zero) ()
base1-thm zero (suc (suc zero)) h = inj₁ ( refl , refl )
base1-thm (suc zero) zero ()
base1-thm (suc zero) (suc zero) ()
base1-thm (suc zero) (suc (suc zero)) ()
base1-thm (suc (suc zero)) zero ()
base1-thm (suc (suc zero)) (suc zero) ()
base1-thm (suc (suc zero)) (suc (suc zero)) ()
base1-thm (suc (suc (suc zero))) zero ()
base1-thm (suc (suc (suc zero))) (suc zero) h = inj₂ ( refl , refl )
base1-thm (suc (suc (suc zero))) (suc (suc zero)) ()
-- t ≥ 4（任意 s）: 16 ≤ t² ≤ t² + 3s² ≡ 12
base1-thm (suc (suc (suc (suc k)))) s h =
  ⊥-elim (16≤12-empty (tCap-le 4 1 (suc (suc (suc (suc k)))) s (m≤m+n 4 k) h))
-- t = 0..3, s ≥ 3: 27 ≤ 3s² ≤ t² + 3s² ≡ 12
base1-thm zero (suc (suc (suc k))) h =
  ⊥-elim (27≤12-empty (sCap-le 3 1 zero (suc (suc (suc k))) (m≤m+n 3 k) h))
base1-thm (suc zero) (suc (suc (suc k))) h =
  ⊥-elim (27≤12-empty (sCap-le 3 1 (suc zero) (suc (suc (suc k))) (m≤m+n 3 k) h))
base1-thm (suc (suc zero)) (suc (suc (suc k))) h =
  ⊥-elim (27≤12-empty (sCap-le 3 1 (suc (suc zero)) (suc (suc (suc k))) (m≤m+n 3 k) h))
base1-thm (suc (suc (suc zero))) (suc (suc (suc k))) h =
  ⊥-elim (27≤12-empty (sCap-le 3 1 (suc (suc (suc zero))) (suc (suc (suc k))) (m≤m+n 3 k) h))

--------------------------------------------------------------------------------
-- §6. base2 全称分类（n = 2: t² + 3s² = 36; 冻结解 (3,3) 与 (6,0)）
-- oracle v2: n=2 偶, k=1: t ∈ {±3,±6}; (t,s) = (±3,±3) / (±6,0)
--------------------------------------------------------------------------------

BSol2 : ℕ → ℕ → Set
BSol2 t s = (t ≡ 3 × s ≡ 3) ⊎ (t ≡ 6 × s ≡ zero)

base2-thm : ∀ t s → sol (suc (suc zero)) t s → BSol2 t s
base2-thm zero zero ()
base2-thm zero (suc zero) ()
base2-thm zero (suc (suc zero)) ()
base2-thm zero (suc (suc (suc zero))) ()
base2-thm (suc zero) zero ()
base2-thm (suc zero) (suc zero) ()
base2-thm (suc zero) (suc (suc zero)) ()
base2-thm (suc zero) (suc (suc (suc zero))) ()
base2-thm (suc (suc zero)) zero ()
base2-thm (suc (suc zero)) (suc zero) ()
base2-thm (suc (suc zero)) (suc (suc zero)) ()
base2-thm (suc (suc zero)) (suc (suc (suc zero))) ()
base2-thm (suc (suc (suc zero))) zero ()
base2-thm (suc (suc (suc zero))) (suc zero) ()
base2-thm (suc (suc (suc zero))) (suc (suc zero)) ()
base2-thm (suc (suc (suc zero))) (suc (suc (suc zero))) h = inj₁ ( refl , refl )
base2-thm (suc (suc (suc (suc zero)))) zero ()
base2-thm (suc (suc (suc (suc zero)))) (suc zero) ()
base2-thm (suc (suc (suc (suc zero)))) (suc (suc zero)) ()
base2-thm (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) ()
base2-thm (suc (suc (suc (suc (suc zero))))) zero ()
base2-thm (suc (suc (suc (suc (suc zero))))) (suc zero) ()
base2-thm (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) ()
base2-thm (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) ()
base2-thm (suc (suc (suc (suc (suc (suc zero)))))) zero h = inj₂ ( refl , refl )
base2-thm (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) ()
base2-thm (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) ()
base2-thm (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) ()
-- t ≥ 7（任意 s）: 49 ≤ t² ≤ t² + 3s² ≡ 36
base2-thm (suc (suc (suc (suc (suc (suc (suc k))))))) s h =
  ⊥-elim (49≤36-empty
    (tCap-le 7 2 (suc (suc (suc (suc (suc (suc (suc k))))))) s
      (m≤m+n 7 k) h))
-- t = 0..6, s ≥ 4: 48 ≤ 3s² ≤ t² + 3s² ≡ 36
base2-thm zero (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 zero (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base2-thm (suc zero) (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 (suc zero) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base2-thm (suc (suc zero)) (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 (suc (suc zero)) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base2-thm (suc (suc (suc zero))) (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 (suc (suc (suc zero))) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base2-thm (suc (suc (suc (suc zero)))) (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 (suc (suc (suc (suc zero)))) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base2-thm (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base2-thm (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc k)))) h =
  ⊥-elim (48≤36-empty (sCap-le 4 2 (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))

--------------------------------------------------------------------------------
-- §7. 递降核（n ≥ 2: sol (n) t s ⇒ t = 3t₀ 且 sol (n−1) s t₀）
-- 数学: t² ≡ 0 (mod 3)（p=3 素）⇒ 3∣t; 剥一层后角色互换（s 升 t 位）
-- 证明: tri3-split 三案; r=0 剥层, r=1/2 由 no-suc-mult3 反证（Mod3Core）
--------------------------------------------------------------------------------

-- 左分配（NoNormPrelude 的 *-distribˡ 是右分配形式 (a+b)*c ≡ a*c+b*c,
-- 经 comm 绕行自建; Witness 的 distribʳ 同款范式）
ldistr : ∀ a b c → a * (b + c) ≡ a * b + a * c
ldistr a b c = begin
  a * (b + c)
    ≡⟨ *-comm a (b + c) ⟩
  (b + c) * a
    ≡⟨ *-distribˡ b c a ⟩
  b * a + c * a
    ≡⟨ cong₂ _+_ (*-comm b a) (*-comm c a) ⟩
  a * b + a * c
  ∎
  where open ≡-Reasoning

distr-sym : ∀ a b c → a * b + a * c ≡ a * (b + c)
distr-sym a b c = sym (ldistr a b c)

mul4-3out : ∀ X → 4 * (3 * X) ≡ 3 * (4 * X)
mul4-3out X =
  trans (sym (*-assoc 4 3 X))
  (trans (cong (_* X) (*-comm 4 3))
         (*-assoc 3 4 X))

-- r=0 剥层: t = q·3 ⇒ sol (m+1) t s ⇒ sol m s q
sol-next : ∀ m q t s → sol (suc m) t s → t ≡ q * 3 → sol m s q
sol-next m q t s h e =
  trans (+-comm (s * s) (3 * (q * q))) (mult3-inj _ _ B)
  where
  sq-t : t * t ≡ 3 * (3 * (q * q))
  sq-t = trans (cong₂ _*_ e e) (sq3ʳ q)
  A0 : t * t + 3 * (s * s) ≡ 3 * (3 * (q * q)) + 3 * (s * s)
  A0 = cong (λ z → z + 3 * (s * s)) sq-t
  A1 : 3 * (3 * (q * q)) + 3 * (s * s) ≡ 4 * pow3 (suc m)
  A1 = trans (sym A0) h
  A2 : 3 * (3 * (q * q)) + 3 * (s * s) ≡ 3 * (4 * pow3 m)
  A2 = trans A1 (mul4-3out (pow3 m))
  B : 3 * (3 * (q * q) + s * s) ≡ 3 * (4 * pow3 m)
  B = trans (sym (distr-sym 3 (3 * (q * q)) (s * s))) A2

-- K1: (3q+1)² 与 (3q+2)² 展开的公共 3-倍部
shape1 : ∀ q → (q * 3) + ((q * 3) + (q * 3) * (q * 3))
               ≡ 3 * ((q + q) + 3 * (q * q))
shape1 q = begin
  q * 3 + (q * 3 + (q * 3) * (q * 3))
    ≡⟨ cong₂ (λ u v → u + (v + (q * 3) * (q * 3))) (*-comm q 3) (*-comm q 3) ⟩
  3 * q + (3 * q + (q * 3) * (q * 3))
    ≡⟨ cong (λ z → 3 * q + (3 * q + z)) (sq3ʳ q) ⟩
  3 * q + (3 * q + 3 * (3 * (q * q)))
    ≡⟨ sym (+-assoc (3 * q) (3 * q) (3 * (3 * (q * q)))) ⟩
  (3 * q + 3 * q) + 3 * (3 * (q * q))
    ≡⟨ cong (λ z → z + 3 * (3 * (q * q))) (distr-sym 3 q q) ⟩
  3 * (q + q) + 3 * (3 * (q * q))
    ≡⟨ distr-sym 3 (q + q) (3 * (q * q)) ⟩
  3 * ((q + q) + 3 * (q * q))
  ∎
  where open ≡-Reasoning

-- r=1 反证: t = 3q+1 ⇒ t² + 3s² ≡ suc(3·K) ≢ 3·L
r1-absurd : ∀ m q t s → sol (suc m) t s → t ≡ suc (q * 3) → ⊥
r1-absurd m q t s h e =
  ⊥-elim (no-suc-mult3 ((q + q) + 3 * (q * q) + s * s) (4 * pow3 m) B)
  where
  K1 = (q + q) + 3 * (q * q)
  tt : t * t ≡ suc (3 * K1)
  tt = trans (cong₂ _*_ e e) (trans (sq-suc (q * 3)) (cong suc (shape1 q)))
  C : t * t + 3 * (s * s) ≡ suc (3 * (K1 + s * s))
  C = trans (cong (λ z → z + 3 * (s * s)) tt)
            (cong suc (distr-sym 3 K1 (s * s)))
  D : t * t + 3 * (s * s) ≡ 3 * (4 * pow3 m)
  D = trans h (mul4-3out (pow3 m))
  B : suc (3 * (K1 + s * s)) ≡ 3 * (4 * pow3 m)
  B = trans (sym C) D

-- suc⁴ 变体（r2 的 t² 带四层 suc; RHS 经 3suc 归位后剥三层, 内部复用 no-suc-mult3;
--   不能直接 suc-injective ×3: RHS 3*(4·pow3 …) 非 suc 头, 剥不动 —— 2026-11-24 实测）
no-suc4-mult3 : ∀ A q → suc (suc (suc (suc (3 * A)))) ≡ 3 * q → ⊥
no-suc4-mult3 A zero ()
no-suc4-mult3 A (suc q') h =
  no-suc-mult3 A q'
    (trans (suc-injective (suc-injective (suc-injective (trans h (3suc q')))))
           (*-comm q' 3))

-- r=2 反证: t = 3q+2 ⇒ t² = 3·J + 4 形, 剥三层 suc 后同 r=1
r2-absurd : ∀ m q t s → sol (suc m) t s → t ≡ suc (suc (q * 3)) → ⊥
r2-absurd m q t s h e =
  ⊥-elim (no-suc4-mult3 (J + s * s) (4 * pow3 m) C4)
  where
  K1 = (q + q) + 3 * (q * q)
  J = q + (q + K1)
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
  inner3 : (q * 3) + ((q * 3) + 3 * K1) ≡ 3 * J
  inner3 = begin
    q * 3 + (q * 3 + 3 * K1)
      ≡⟨ cong (λ z → q * 3 + (z + 3 * K1)) (*-comm q 3) ⟩
    q * 3 + (3 * q + 3 * K1)
      ≡⟨ cong (λ z → q * 3 + z) (distr-sym 3 q K1) ⟩
    q * 3 + 3 * (q + K1)
      ≡⟨ cong (λ z → z + 3 * (q + K1)) (*-comm q 3) ⟩
    3 * q + 3 * (q + K1)
      ≡⟨ distr-sym 3 q (q + K1) ⟩
    3 * (q + (q + K1))
    ∎
    where open ≡-Reasoning
  tt : t * t ≡ suc (suc (suc (suc (3 * J))))
  tt = trans (cong₂ _*_ e e)
      (trans (sq-suc a')
      (trans (cong suc inner2)
             (cong (λ z → suc (suc (suc (suc z)))) inner3)))
  D : t * t + 3 * (s * s) ≡ 3 * (4 * pow3 m)
  D = trans h (mul4-3out (pow3 m))
  E : t * t + 3 * (s * s) ≡ suc (suc (suc (suc (3 * (J + s * s)))))
  E = trans (cong (λ z → z + 3 * (s * s)) tt)
            (cong (λ z → suc (suc (suc (suc z))))
                  (distr-sym 3 J (s * s)))
  C4 : suc (suc (suc (suc (3 * (J + s * s))))) ≡ 3 * (4 * pow3 m)
  C4 = trans (sym E) D

descent1 : ∀ m t s → sol (suc m) t s
         → Σ ℕ (λ t₀ → (t ≡ t₀ * 3) × sol m s t₀)
descent1 m t s h with tri3-split t
... | inj₁ (q , e) = (q , e , sol-next m q t s h e)
... | inj₂ (inj₁ (q , e)) = ⊥-elim (r1-absurd m q t s h e)
... | inj₂ (inj₂ (q , e)) = ⊥-elim (r2-absurd m q t s h e)

--------------------------------------------------------------------------------
-- §8. v2 冻结分类族 BSol 与全称 classify（两步归纳; 递降核 §7 + 基案 §5-§6 合成）
--------------------------------------------------------------------------------

-- v2 冻结（ℕ 正部代表元; oracle norm v2; 负部由 ℤ 符号对称, 未形式化同 Witness 边界）:
-- n = 2k（偶）: (t,s) = (3^k, 3^k) 或 (2·3^k, 0);  n = 2k+1（奇）: (0, 2·3^k) 或 (3^{k+1}, 3^k)
BSol : ℕ → ℕ → ℕ → Set
BSol n t s =
  (Σ ℕ (λ k → n ≡ dub k × ((t ≡ pow3 k × s ≡ pow3 k)
                          ⊎ (t ≡ 2 * pow3 k × s ≡ zero))))
  ⊎ (Σ ℕ (λ k → n ≡ suc (dub k) × ((t ≡ zero × s ≡ 2 * pow3 k)
                                   ⊎ (t ≡ pow3 (suc k) × s ≡ pow3 k))))

-- 3·(2·x) ≡ 2·(3·x)（闭字面 3·2 交换, assoc 双向）
mul3-2 : ∀ x → 3 * (2 * x) ≡ 2 * (3 * x)
mul3-2 x =
  trans (sym (*-assoc 3 2 x))
  (trans (cong (_* x) (*-comm 3 2))
         (*-assoc 2 3 x))

-- ×3 提升: BSol m ⟹ BSol (m+2)（即「解集 = 3·解集(n−2)」的表示元映射）
BSol×3 : ∀ m t₀ s₀ → BSol m t₀ s₀ → BSol (suc (suc m)) (3 * t₀) (3 * s₀)
BSol×3 m t₀ s₀ (inj₁ (k , e-n , inj₁ (a , b))) =
  inj₁ (suc k , trans (cong (λ z → suc (suc z)) e-n) (sym (dub-suc k)) ,
        inj₁ (cong (3 *_) a , cong (3 *_) b))
BSol×3 m t₀ s₀ (inj₁ (k , e-n , inj₂ (a , b))) =
  inj₁ (suc k , trans (cong (λ z → suc (suc z)) e-n) (sym (dub-suc k)) ,
        inj₂ (trans (cong (3 *_) a) (mul3-2 (pow3 k)) , cong (3 *_) b))
BSol×3 m t₀ s₀ (inj₂ (k , e-n , inj₁ (a , b))) =
  inj₂ (suc k ,
        trans (cong (λ z → suc (suc z)) e-n) (sym (cong suc (dub-suc k))) ,
        inj₁ (cong (3 *_) a , trans (cong (3 *_) b) (mul3-2 (pow3 k))))
BSol×3 m t₀ s₀ (inj₂ (k , e-n , inj₂ (a , b))) =
  inj₂ (suc k ,
        trans (cong (λ z → suc (suc z)) e-n) (sym (cong suc (dub-suc k))) ,
        inj₂ (cong (3 *_) a , cong (3 *_) b))

-- 基案分类（BSol0/BSol1 → BSol 0/1; 字面 1/2/3 与 pow3 槽定义归约互认）
bs0→ : ∀ t s → BSol0 t s → BSol zero t s
bs0→ t s (inj₁ p) = inj₁ (zero , refl , inj₁ p)
bs0→ t s (inj₂ p) = inj₁ (zero , refl , inj₂ p)

bs1→ : ∀ t s → BSol1 t s → BSol (suc zero) t s
bs1→ t s (inj₁ p) = inj₂ (zero , refl , inj₁ p)
bs1→ t s (inj₂ p) = inj₂ (zero , refl , inj₂ p)

-- 全称分类主定理（∀②）: 两步归纳 go（偶/奇双基案 + ×3 提升步）
go : ∀ n → (∀ t s → sol n t s → BSol n t s)
         × (∀ t s → sol (suc n) t s → BSol (suc n) t s)
go zero =
  ( (λ t s h → bs0→ t s (base0-thm t s h))
  , (λ t s h → bs1→ t s (base1-thm t s h)) )
go (suc n) = (proj₂ (go n) , step (proj₁ (go n)))
  where
  step : (∀ t s → sol n t s → BSol n t s)
       → ∀ t s → sol (suc (suc n)) t s → BSol (suc (suc n)) t s
  step IH t s h =
    subst (λ y → BSol (suc (suc n)) t y) (sym e-s')
      (subst (λ x → BSol (suc (suc n)) x (3 * t₁)) (sym e-t')
             (BSol×3 n t₀ t₁ (IH t₀ t₁ h₂)))
    where
    w1 = descent1 (suc n) t s h
    t₀ = proj₁ w1
    e-t = proj₁ (proj₂ w1)
    h₁ = proj₂ (proj₂ w1)
    w2 = descent1 n s t₀ h₁
    t₁ = proj₁ w2
    e-s = proj₁ (proj₂ w2)
    h₂ = proj₂ (proj₂ w2)
    e-t' = trans e-t (*-comm t₀ 3)
    e-s' = trans e-s (*-comm t₁ 3)

-- **∀② 全称分类**: ∀ n t s, t² + 3s² = 4·3ⁿ ⇒ (t,s) 为 v2 冻结形式（正部）
classify : ∀ n t s → sol n t s → BSol n t s
classify n t s h = proj₁ (go n) t s h
