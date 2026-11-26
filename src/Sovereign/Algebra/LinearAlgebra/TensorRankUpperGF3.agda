{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankUpperGF3
-- M16-D: 「ω = 9/4 在 GF(3) 上」的两半, 写成同一种有限语言——以及 Strassen 能覆盖的那一段
--
-- 数学背景
--   秩分解 ⟨n,n,n⟩ = Σ_{k<r} a_k ⊗ b_k ⊗ c_k 的项数 r 与尺寸 n 的比值, 给出指数的上界:
--     有一个 (n, r) 的分解且 r < n^(p/q)  ⟹  指数 < p/q。
--   Lean 的原句（`MatrixExponent/FieldExtension.lean:72`, 阅读层逐字读到）:
--     exponent_lt_iff_rank : exponent F a b c < s ↔ ∃ n r, 2 ≤ n ∧ RankLE F (side n a) … r ∧ r < n ^ s
--   取形状 a = b = c = 1（`Rectangle/Bounds.lean:15 square`, side n 1 = n）, 并把 s 取成分数 p/q:
--     「指数 < p/q」的有限形态 = ∃ n r, 2 ≤ n × RankLE₃ n r × (r ^ q < n ^ p)。
--   于是「每域 ω = 9/4」在 GF(3) 上拆成两半, 都是关于 RankLE₃ 的有限命题:
--     下半（外部定理, 见 TensorRankGF3.ω₃-boundary）: ∀ n r, 2 ≤ n → RankLE₃ n r → n ^ 9 ≤ r ^ 4
--     上半（本件 ω₃-upper）:                    ∀ p q, 9 * q < 4 * p → ∃ n r, … ∧ r ^ q < n ^ p
--
-- 内容
--   §1 两条算术引理（不依赖 stdlib 的类型类实例）: 幂对指数单调、底严格增
--   §2 严格节省的类型 Saving₃; 外部上半的陈述 ω₃-upper（无居民）
--   §3 ★ strassen-saving: Strassen 覆盖 p/q ≥ 17/6 的全部 (p, q)
--   §4 ★ saving-above / ★ exactness₃: 有下半时, 节省只能落在 9/4 之上——两半不重叠
--
-- 诚实边界
--   · ω₃-upper 是外部定理（Lean `UpperBound.lean:44 upper_bound` 取 F = ZMod 3）的陈述, 本库不证、无居民。
--     「Lean 的实数陈述 ⟹ 本处的分数形态」是阅读层的 [手工论证·未验证]（s = p/q 时 r < n^(p/q) ⟺ r ^ q < n ^ p）。
--   · 本件能证的上半只有 Strassen 那一段（17/6 ≈ 2.833）, 离 9/4 还有空档。
--     Lean 那边靠 9/4 的见证不是显式的: `Coefficients.lean:43 candidate := Classical.epsilon …`,
--     上界机器在一个用选择公理挑出的代数闭域上工作, 再由 `closed_laws` 推广到一切代数闭域（阅读层）。
--   · exactness₃ 把两半都当**假设**, 不是断言它们成立。
--
-- 复用(先查后写): ω₃-boundary(TensorRankGF3) / rank-strassen-pow(TensorRankPowGF3)。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankUpperGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤n⇒m≤1+n; m≤m+n; m<n+m; ≰⇒>; <-irrefl; ≤-<-trans; <-≤-trans
       ; *-comm; *-assoc; *-identityʳ; *-identityˡ; *-monoˡ-≤; *-monoʳ-≤; ^-*-assoc; ^-monoˡ-≤)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3 using (RankLE₃; ω₃-boundary)
open import Sovereign.Algebra.LinearAlgebra.TensorRankPowGF3 using (rank-strassen-pow; cert-base)

--------------------------------------------------------------------------------
-- §1. 算术引理
--------------------------------------------------------------------------------

-- m ≤ n · m（底 n ≥ 1）
m≤n·m : ∀ (m n : ℕ) → 1 ≤ n → m ≤ n * m
m≤n·m m (suc n) h = m≤m+n m (n * m)

-- 1 ≤ n ^ k（底 n ≥ 1）
1≤pow : ∀ (n k : ℕ) → 1 ≤ n → 1 ≤ n ^ k
1≤pow n zero h = ≤-refl
1≤pow n (suc k) h = ≤-trans (1≤pow n k h) (m≤n·m (n ^ k) n h)

-- 幂对指数单调（底 n ≥ 1; n = 0 时 n ^ 0 ≤ n ^ (suc k) 为假, 所以要这个前提）
pow-exp-mono : ∀ (n a b : ℕ) → 1 ≤ n → a ≤ b → n ^ a ≤ n ^ b
pow-exp-mono n zero b h z≤n = 1≤pow n b h
pow-exp-mono n (suc a) (suc b) h (s≤s e) = *-monoʳ-≤ n (pow-exp-mono n a b h e)

-- u < v、w > 0 ⟹ u · w < v · w（不走类型类实例: 用非严格单调 + 一步加法）
mul-< : ∀ (u v w : ℕ) → u < v → 0 < w → (u * w) < (v * w)
mul-< u v w h hw = ≤-trans (m<n+m (u * w) hw) (*-monoˡ-≤ w h)

-- 底严格增: a < b、k > 0 ⟹ a ^ k < b ^ k
--   对 k 归纳; 归纳步把 a · X ≤ b · X（非严格）与 b · X < b · Y（严格, 用归纳假设）接起来,
--   这样 a = 0 时也成立（不要求 a ^ k > 0）
pow-base-< : ∀ (k a b : ℕ) → 0 < k → a < b → (a ^ k) < (b ^ k)
pow-base-< (suc zero) a b hk h = mul-< a b 1 h (s≤s z≤n)
pow-base-< (suc (suc k)) a b hk h = ≤-<-trans step₁ step₂
  where
  hb : 0 < b
  hb = ≤-trans (s≤s z≤n) h
  step₁ : (a * (a * a ^ k)) ≤ (b * (a * a ^ k))
  step₁ = *-monoˡ-≤ (a * a ^ k) (≤-trans (m≤n⇒m≤1+n ≤-refl) h)
  step₂ : (b * (a * a ^ k)) < (b * (b * b ^ k))
  step₂ = ≤-<-trans (≤-reflexive (*-comm b (a * a ^ k)))
          (<-≤-trans (mul-< (a * a ^ k) (b * b ^ k) b (pow-base-< (suc k) a b (s≤s z≤n) h) hb)
                     (≤-reflexive (*-comm (b * b ^ k) b)))

-- 基数的严格版: 7^6 < 2^17（117649 + 1 + 13422 = 131072）
cert-strict : 7 ^ 6 < 2 ^ 17
cert-strict = m≤m+n (suc (7 ^ 6)) 13422

--------------------------------------------------------------------------------
-- §2. 严格节省的类型 / 外部上半的陈述
--------------------------------------------------------------------------------

-- 「指数 < p/q」的有限形态: 尺寸 n ≥ 2 有一个 r 项分解, 且 r ^ q < n ^ p
Saving₃ : ℕ → ℕ → Set
Saving₃ p q = Σ ℕ (λ n → Σ ℕ (λ r → (2 ≤ n) × RankLE₃ n r × (r ^ q < n ^ p)))

-- 外部上半（无居民）: 每个比值 p/q > 9/4 都有一个严格节省
ω₃-upper : Set
ω₃-upper = ∀ p q → 9 * q < 4 * p → Saving₃ p q

--------------------------------------------------------------------------------
-- §3. Strassen 覆盖的那一段
--------------------------------------------------------------------------------

1≤2 : 1 ≤ 2
1≤2 = s≤s z≤n

-- ★ 对一切 p/q ≥ 17/6, GF(3) 上有严格节省: 取 n = 2^(6q)、r = 7^(6q)（M13 的 6q 次张量幂）
--   r ^ q = (7^6)^(q²) < (2^17)^(q²) = 2^(17q²) ≤ 2^(6qp) = n ^ p
strassen-saving : ∀ p q → 0 < q → 17 * q ≤ 6 * p → Saving₃ p q
strassen-saving p (suc q′) h sq =
  (2 ^ (6 * suc q′)) , (7 ^ (6 * suc q′)) , n≥2 , rank-strassen-pow (6 * suc q′) , saving
  where
  Q : ℕ
  Q = suc q′ * suc q′

  hQ : 0 < Q
  hQ = s≤s z≤n

  n≥2 : 2 ≤ 2 ^ (6 * suc q′)
  n≥2 = pow-exp-mono 2 1 (6 * suc q′) 1≤2 one≤6q
    where
    -- 6 * suc q′ 按定义就是 suc (q′ + 5 * suc q′)
    one≤6q : 1 ≤ 6 * suc q′
    one≤6q = s≤s z≤n

  e1 : (7 ^ (6 * suc q′)) ^ suc q′ ≡ (7 ^ 6) ^ Q
  e1 = trans (^-*-assoc 7 (6 * suc q′) (suc q′))
         (trans (cong (λ t → 7 ^ t) (*-assoc 6 (suc q′) (suc q′)))
                (sym (^-*-assoc 7 6 Q)))

  st : (7 ^ 6) ^ Q < (2 ^ 17) ^ Q
  st = pow-base-< Q (7 ^ 6) (2 ^ 17) hQ cert-strict

  -- stdlib 的 _*_ 是左结合: a * b * c 读作 (a * b) * c
  e3 : 6 * p * suc q′ ≡ 6 * suc q′ * p
  e3 = trans (*-assoc 6 p (suc q′))
        (trans (cong (λ t → 6 * t) (*-comm p (suc q′)))
               (sym (*-assoc 6 (suc q′) p)))

  e2 : (2 ^ 17) ^ Q ≡ 2 ^ (17 * suc q′ * suc q′)
  e2 = trans (^-*-assoc 2 17 Q) (cong (λ t → 2 ^ t) (sym (*-assoc 17 (suc q′) (suc q′))))

  -- 17q′ · q′ ≤ 6p · q′ = 6q′ · p
  mo : 2 ^ (17 * suc q′ * suc q′) ≤ 2 ^ (6 * suc q′ * p)
  mo = pow-exp-mono 2 (17 * suc q′ * suc q′) (6 * suc q′ * p) 1≤2
         (≤-trans (*-monoˡ-≤ (suc q′) sq) (≤-reflexive e3))

  e4 : 2 ^ (6 * suc q′ * p) ≡ (2 ^ (6 * suc q′)) ^ p
  e4 = sym (^-*-assoc 2 (6 * suc q′) p)

  saving : (7 ^ (6 * suc q′)) ^ suc q′ < (2 ^ (6 * suc q′)) ^ p
  saving = ≤-<-trans (≤-reflexive e1)
             (<-≤-trans st (≤-trans (≤-reflexive e2) (≤-trans mo (≤-reflexive e4))))

--------------------------------------------------------------------------------
-- §4. 两半不重叠
--------------------------------------------------------------------------------

-- 0 < 4
0<4 : 0 < 4
0<4 = s≤s z≤n

-- ★ 有下半（ω₃-boundary）时, 任何严格节省都满足 9 * q < 4 * p
--   若 4p ≤ 9q, 则 n^(9q) ≤ r^(4q) < n^(4p) ≤ n^(9q), 矛盾
saving-above : ω₃-boundary → ∀ p q → Saving₃ p q → 9 * q < 4 * p
saving-above B p q (n , r , 2≤n , ρ , sv) = ≰⇒> contra
  where
  h1 : 1 ≤ n
  h1 = ≤-trans 1≤2 2≤n

  hb : n ^ 9 ≤ r ^ 4
  hb = B n r 2≤n ρ

  -- 下半两边取 q 次幂: n^(9q) ≤ r^(4q)
  e1 : n ^ (9 * q) ≤ r ^ (4 * q)
  e1 = ≤-trans (≤-reflexive (sym (^-*-assoc n 9 q)))
         (≤-trans (^-monoˡ-≤ q hb) (≤-reflexive (^-*-assoc r 4 q)))

  -- 节省两边取 4 次幂（严格）: r^(4q) < n^(4p)
  e2 : r ^ (4 * q) < n ^ (4 * p)
  e2 = ≤-<-trans
         (≤-reflexive (trans (cong (λ t → r ^ t) (*-comm 4 q)) (sym (^-*-assoc r q 4))))
         (≤-trans (pow-base-< 4 (r ^ q) (n ^ p) 0<4 sv)
                  (≤-reflexive (trans (^-*-assoc n p 4) (cong (λ t → n ^ t) (*-comm p 4)))))

  contra : 4 * p ≤ 9 * q → ⊥
  contra h = <-irrefl refl (≤-<-trans e1 (<-≤-trans e2 e3))
    where
    e3 : n ^ (4 * p) ≤ n ^ (9 * q)
    e3 = pow-exp-mono n (4 * p) (9 * q) h1 h

-- ★ 两半一旦都成立, 「有严格节省」恰好在 9/4 之上的那些 (p, q)
exactness₃ : ω₃-boundary → ω₃-upper →
  ∀ p q → (Saving₃ p q → 9 * q < 4 * p) × (9 * q < 4 * p → Saving₃ p q)
exactness₃ B U p q = (λ sv → saving-above B p q sv) , (λ h → U p q h)

-- 与库内见证相容: 下半在 (2, 7) 处的实例 2^9 = 512 ≤ 2401 = 7^4 成立
boundary-strassen : 2 ^ 9 ≤ 7 ^ 4
boundary-strassen = m≤m+n (2 ^ 9) 1889
