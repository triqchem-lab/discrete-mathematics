{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankProfileGF3
-- M26: 秩剖面的算术 —— Σ 秩 = n³ 的分解, 秩剖面 (n₁, n₂, n₃) 只能是哪几种（2026-11-28 登记）。
--
-- 数学背景
--   设 ⟨n,n,n⟩ 的分解有 r 项, 首因子的矩阵秩是 1 / 2 / 3 的项数分别是 n₁ / n₂ / n₃。
--   项数与秩和是
--       n₁ + n₂ + n₃ = r,      n₁ + 2·n₂ + 3·n₃ = Σ 秩。
--   两式相减得 n₂ + 2·n₃ = Σ 秩 − r =: d（d = Δ, 即 Σ 秩超出 n³ 的部分）, 于是
--       n₂ = d − 2·n₃,   n₁ = r − d + n₃;   特别地 n₃ ≤ d / 2。
--   「互补幂等」法（Yang 等, arXiv:2609.18722）只在 Σ 秩 = n³ 即 d = 0 时有刚性。对 F₃ 上假设存在的
--   19 项分解, d = 0 意味着 n₂ + 2·n₃ = 8, 秩剖面恰好是
--       (11,8,0)  (12,6,1)  (13,4,2)  (14,2,3)  (15,0,4)
--   这五种。本件把这段算术写进内核; 它不依赖任何关于分解存在性的假设。
--
-- 本件给出的
--   ① profile-Δ: 两式 ⟹ n₂ + 2·n₃ ≡ d;
--   ② profile-param: 再加项数 ⟹ n₁ + d ≡ r + n₃（n₁ 的参数化, 不用减法）;
--   ③ profile-2n₃≤ / profile-n₃≤ / halve: 2·n₃ ≤ d, n₃ ≤ d, 2k ≤ 2m ⟹ k ≤ m;
--   ④ ★★ profiles-19: r = 19、d = 8 时秩剖面恰是上述五种之一;
--   ⑤ profiles-23: r = 23、d = 4 时恰是 (19,4,0) (20,2,1) (21,0,2) 三种。
--
-- 诚实边界
--   · 纯算术, 不含任何张量秩的定理。「Σ 秩 ≥ n³」（d ≥ 0）在 TensorRankBudgetGF3;
--     秩为 0 的项（零首因子）不计入 n₁ n₂ n₃, 所以 r 大于秩非零的项数时本件的前提不成立——那是对的。
--   · 这里的「矩阵秩」只是剖面的读法: 内核里没有 3×3 矩阵秩的定义（GF3Rank 未完成）。
--
-- 复用（先查后写）: Data.Nat.Solver 的 +-×-Solver（库内 12 个模块的先例）/
--   +-cancelˡ-≡·+-cancelʳ-≡·m≤n⇒m<n∨m≡n·<⇒≤pred(Data.Nat.Properties)。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankProfileGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _^_; z≤n)
open import Data.Nat.Properties
  using (+-cancelˡ-≡; +-cancelʳ-≡; *-cancelˡ-≤; +-comm; ≤-reflexive; ≤-trans; ≤-antisym; m≤m+n; m≤n⇒m<n∨m≡n; <⇒≤pred)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- §1 两个方程
--------------------------------------------------------------------------------

-- ★ 项数与秩和 ⟹ n₂ + 2·n₃ ≡ d, 其中 d 是秩和超出 r 的部分
profile-Δ : ∀ n₁ n₂ n₃ r d → n₁ + n₂ + n₃ ≡ r → n₁ + 2 * n₂ + 3 * n₃ ≡ r + d → n₂ + 2 * n₃ ≡ d
profile-Δ n₁ n₂ n₃ r d h₁ h₂ =
  +-cancelˡ-≡ r (n₂ + 2 * n₃) d
    (trans (trans (sym (cong (_+ (n₂ + 2 * n₃)) h₁))
                  (solve 3 (λ a b c → (a :+ b :+ c) :+ (b :+ con 2 :* c) := a :+ con 2 :* b :+ con 3 :* c)
                         refl n₁ n₂ n₃))
            h₂)

-- ★ n₁ 的参数化（不用减法）: n₁ + d ≡ r + n₃
profile-param : ∀ n₁ n₂ n₃ r d → n₁ + n₂ + n₃ ≡ r → n₂ + 2 * n₃ ≡ d → n₁ + d ≡ r + n₃
profile-param n₁ n₂ n₃ r d h₁ e =
  trans (cong (n₁ +_) (sym e))
        (trans (solve 3 (λ a b c → a :+ (b :+ con 2 :* c) := (a :+ b :+ c) :+ c) refl n₁ n₂ n₃)
               (cong (_+ n₃) h₁))

-- n₃ ≤ d
twiceLaw : ∀ n → n + n ≡ 2 * n
twiceLaw n = solve 1 (λ c → c :+ c := con 2 :* c) refl n

-- 2·n₃ ≤ d
profile-2n₃≤ : ∀ n₂ n₃ d → n₂ + 2 * n₃ ≡ d → 2 * n₃ ≤ d
profile-2n₃≤ n₂ n₃ d e = ≤-trans s3 s4
  where
  s3 : 2 * n₃ ≤ n₂ + 2 * n₃
  s3 = ≤-trans (m≤m+n (2 * n₃) n₂) (≤-reflexive (+-comm (2 * n₃) n₂))
  s4 : n₂ + 2 * n₃ ≤ d
  s4 = ≤-reflexive e

-- n₃ ≤ d
profile-n₃≤ : ∀ n₂ n₃ d → n₂ + 2 * n₃ ≡ d → n₃ ≤ d
profile-n₃≤ n₂ n₃ d e = ≤-trans (m≤m+n n₃ n₃) (≤-trans (≤-reflexive (twiceLaw n₃)) (profile-2n₃≤ n₂ n₃ d e))

-- 对半: 2k ≤ 2m ⟹ k ≤ m（所以 n₃ ≤ d / 2）
halve : ∀ k m → 2 * k ≤ 2 * m → k ≤ m
halve k m le = *-cancelˡ-≤ 2 le

--------------------------------------------------------------------------------
-- §2 有界自然数的穷举
--------------------------------------------------------------------------------

-- k ≤ suc m ⟹ k ≤ m 或 k ≡ suc m
k≤suc-cases : ∀ {k m} → k ≤ suc m → (k ≤ m) ⊎ (k ≡ suc m)
k≤suc-cases le with m≤n⇒m<n∨m≡n le
... | inj₂ eq = inj₂ eq
... | inj₁ lt = inj₁ (<⇒≤pred lt)

≤4-cases : ∀ k → k ≤ 4 → (k ≡ 0) ⊎ (k ≡ 1) ⊎ (k ≡ 2) ⊎ (k ≡ 3) ⊎ (k ≡ 4)
≤4-cases k le with k≤suc-cases le
... | inj₂ eq = inj₂ (inj₂ (inj₂ (inj₂ eq)))
... | inj₁ le₃ with k≤suc-cases le₃
...   | inj₂ eq = inj₂ (inj₂ (inj₂ (inj₁ eq)))
...   | inj₁ le₂ with k≤suc-cases le₂
...     | inj₂ eq = inj₂ (inj₂ (inj₁ eq))
...     | inj₁ le₁ with k≤suc-cases le₁
...       | inj₂ eq = inj₂ (inj₁ eq)
...       | inj₁ le₀ = inj₁ (≤-antisym le₀ z≤n)

≤2-cases : ∀ k → k ≤ 2 → (k ≡ 0) ⊎ (k ≡ 1) ⊎ (k ≡ 2)
≤2-cases k le with k≤suc-cases le
... | inj₂ eq = inj₂ (inj₂ eq)
... | inj₁ le₁ with k≤suc-cases le₁
...   | inj₂ eq = inj₂ (inj₁ eq)
...   | inj₁ le₀ = inj₁ (≤-antisym le₀ z≤n)

-- 参数化落地: n₃ = k, 且 c₁ + d ≡ r + k、c₂ + 2k ≡ d 是算术恒等式时, n₁ ≡ c₁、n₂ ≡ c₂
profile-at : ∀ n₁ n₂ n₃ r d k c₁ c₂ → n₃ ≡ k → n₁ + d ≡ r + n₃ → n₂ + 2 * n₃ ≡ d →
  c₁ + d ≡ r + k → c₂ + 2 * k ≡ d → (n₁ ≡ c₁) × (n₂ ≡ c₂)
profile-at n₁ n₂ n₃ r d k c₁ c₂ h₃ h₁ h₂ q₁ q₂ =
  -- 右消去律的第一个参数是被消去的加数
  +-cancelʳ-≡ d n₁ c₁ (trans (trans h₁ (cong (r +_) h₃)) (sym q₁)) ,
  +-cancelʳ-≡ (2 * k) n₂ c₂ (trans (cong (λ v → n₂ + 2 * v) (sym h₃)) (trans h₂ (sym q₂)))

-- 把 profile-at 给的一对（n₁ 与 n₂）连同 n₃ ≡ k 拼成三元组
triple : ∀ {a b c : Set} → a × b → c → a × b × c
triple (x , y) z = x , y , z

--------------------------------------------------------------------------------
-- §3 ★★ r = 19、Σ 秩 = 27: 恰好五种
--------------------------------------------------------------------------------

profiles-19 : ∀ n₁ n₂ n₃ → n₁ + n₂ + n₃ ≡ 19 → n₁ + 2 * n₂ + 3 * n₃ ≡ 27 →
  (n₁ ≡ 11 × n₂ ≡ 8 × n₃ ≡ 0) ⊎
  (n₁ ≡ 12 × n₂ ≡ 6 × n₃ ≡ 1) ⊎
  (n₁ ≡ 13 × n₂ ≡ 4 × n₃ ≡ 2) ⊎
  (n₁ ≡ 14 × n₂ ≡ 2 × n₃ ≡ 3) ⊎
  (n₁ ≡ 15 × n₂ ≡ 0 × n₃ ≡ 4)
profiles-19 n₁ n₂ n₃ h₁ h₂ with profile-Δ n₁ n₂ n₃ 19 8 h₁ h₂
... | e with profile-param n₁ n₂ n₃ 19 8 h₁ e
...   | p with ≤4-cases n₃ (halve n₃ 4 (profile-2n₃≤ n₂ n₃ 8 e))
...     | inj₁ refl = inj₁ (triple (profile-at n₁ n₂ n₃ 19 8 0 11 8 refl p e refl refl) refl)
...     | inj₂ (inj₁ refl) = inj₂ (inj₁ (triple (profile-at n₁ n₂ n₃ 19 8 1 12 6 refl p e refl refl) refl))
...     | inj₂ (inj₂ (inj₁ refl)) = inj₂ (inj₂ (inj₁ (triple (profile-at n₁ n₂ n₃ 19 8 2 13 4 refl p e refl refl) refl)))
...     | inj₂ (inj₂ (inj₂ (inj₁ refl))) = inj₂ (inj₂ (inj₂ (inj₁ (triple (profile-at n₁ n₂ n₃ 19 8 3 14 2 refl p e refl refl) refl))))
...     | inj₂ (inj₂ (inj₂ (inj₂ refl))) = inj₂ (inj₂ (inj₂ (inj₂ (triple (profile-at n₁ n₂ n₃ 19 8 4 15 0 refl p e refl refl) refl))))

-- r = 23、Σ 秩 = 27: 恰好三种
profiles-23 : ∀ n₁ n₂ n₃ → n₁ + n₂ + n₃ ≡ 23 → n₁ + 2 * n₂ + 3 * n₃ ≡ 27 →
  (n₁ ≡ 19 × n₂ ≡ 4 × n₃ ≡ 0) ⊎
  (n₁ ≡ 20 × n₂ ≡ 2 × n₃ ≡ 1) ⊎
  (n₁ ≡ 21 × n₂ ≡ 0 × n₃ ≡ 2)
profiles-23 n₁ n₂ n₃ h₁ h₂ with profile-Δ n₁ n₂ n₃ 23 4 h₁ h₂
... | e with profile-param n₁ n₂ n₃ 23 4 h₁ e
...   | p with ≤2-cases n₃ (halve n₃ 2 (profile-2n₃≤ n₂ n₃ 4 e))
...     | inj₁ refl = inj₁ (triple (profile-at n₁ n₂ n₃ 23 4 0 19 4 refl p e refl refl) refl)
...     | inj₂ (inj₁ refl) = inj₂ (inj₁ (triple (profile-at n₁ n₂ n₃ 23 4 1 20 2 refl p e refl refl) refl))
...     | inj₂ (inj₂ refl) = inj₂ (inj₂ (triple (profile-at n₁ n₂ n₃ 23 4 2 21 0 refl p e refl refl) refl))

--------------------------------------------------------------------------------
-- §4 读法核对（具体分解的剖面）
--------------------------------------------------------------------------------

-- Strassen 的 7 项（2×2）: 剖面 (6,1,0), Σ 秩 = 8 = 2³, d = 0
strassen-Σrank : 6 + 2 * 1 + 3 * 0 ≡ 2 ^ 3
strassen-Σrank = refl

-- Laderman 的 23 项（3×3）: 剖面 (17,4,2), Σ 秩 = 31, 不是 27 —— d = 4, 幂等的刚性形式用不上
laderman-not-Δ0 : ¬ (17 + 4 + 2 ≡ 23 × 17 + 2 * 4 + 3 * 2 ≡ 27)
laderman-not-Δ0 (_ , ())

-- Δ = 1 的剖面 (10,9,0) 不在 profiles-19 的表里（Σ 秩 = 28）
Δ1-not-in-table : ¬ (10 + 2 * 9 + 3 * 0 ≡ 27)
Δ1-not-in-table ()
