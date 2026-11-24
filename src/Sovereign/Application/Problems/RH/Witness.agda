{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.Witness
-- 范数方程的可计算见证（M2 · A2.2）
--
-- 数学背景（陈述冻结: oracle_rh_tables.py norm, v2）:
--   t² + 3s² = 4·3ⁿ 的整数解集（有限值形式, n=1..12 全枚举核验一致）:
--     n = 2k+1 (奇): (t,s) = (0, ±2·3ᵏ) 或 (±3^(k+1), ±3ᵏ)
--     n = 2k   (偶): (t,s) = (±3ᵏ, ±3ᵏ) 或 (±2·3ᵏ, 0)
--   本模块给出**正部见证函数**（ℕ 代表元）:
--     witness n = (wt n, ws n)，wt/ws 按 2 步递归（n 偶 → (2·3ᵏ, 0)，n 奇 → (0, 2·3ᵏ)）
--   主定理 witness-sat : ∀ n → wt n * wt n + 3 * (ws n * ws n) ≡ 4 * pow3 n
--   （两步归纳；归纳步的算术核心 = 9·(a² + 3b²) = 4·3^{n+2}）
--
-- 诚实边界:
--   · 见证的是**范数方程**（一条 ℤ/ℕ 恒等式），不是曲线的存在性——头注明示；
--   · ℕ 代表元只覆盖正部；负部 (−t, s) 等由 ℤ 符号对称给出（未形式化，注记）;
--   · v1「整除式冻结判据」已被 n=7 反例（t=±2·3⁴）否证——本文件不使用它，
--     陈述以 oracle v2 有限值形式为准（NormClassify 承载分类方向）。
-- 0 postulate。复用 NoNormPrelude（pow3 / *-assoc / *-comm / *-distribˡ / +-zeroʳ）。

module Sovereign.Application.Problems.RH.Witness where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open NoNormPrelude
  using (pow3; *-assoc; *-comm; *-distribˡ; +-zeroʳ)

--------------------------------------------------------------------------------
-- §1. 见证函数（2 步递归定义: 偶/奇分支各就各位）
--------------------------------------------------------------------------------

wt : ℕ → ℕ   -- t 分量: 偶 n ↦ 2·3^{n/2}; 奇 n ↦ 0
wt zero = 2
wt (suc zero) = 0
wt (suc (suc n)) = 3 * wt n

ws : ℕ → ℕ   -- s 分量: 偶 n ↦ 0; 奇 n ↦ 2·3^{n/2}
ws zero = 0
ws (suc zero) = 2
ws (suc (suc n)) = 3 * ws n

--------------------------------------------------------------------------------
-- §2. 两步归纳原理
--------------------------------------------------------------------------------

two-ind : ∀ (P : ℕ → Set) →
  P zero → P (suc zero) → (∀ n → P n → P (suc (suc n))) → ∀ n → P n
two-ind P p0 p1 step n = proj₁ (go n)
  where
  go : ∀ n → P n × P (suc n)
  go zero = p0 , p1
  go (suc m) = proj₂ (go m) , step m (proj₁ (go m))

--------------------------------------------------------------------------------
-- §3. 归纳步的算术核心
--------------------------------------------------------------------------------

-- 引理 A: (3·a)·(3·a) ≡ 3·(3·(a·a))
sq3 : ∀ a → (3 * a) * (3 * a) ≡ 3 * (3 * (a * a))
sq3 a = begin
  (3 * a) * (3 * a)
    ≡⟨ *-assoc 3 a (3 * a) ⟩
  3 * (a * (3 * a))
    ≡⟨ cong (3 *_) (*-comm a (3 * a)) ⟩
  3 * ((3 * a) * a)
    ≡⟨ cong (3 *_) (*-assoc 3 a a) ⟩
  3 * (3 * (a * a))
    ∎

-- 引理 B': 右分配（经 comm + 左分配构造; NoNormPrelude 只有左分配）
distribʳ : ∀ a b c → a * (b + c) ≡ a * b + a * c
distribʳ a b c = begin
  a * (b + c)
    ≡⟨ *-comm a (b + c) ⟩
  (b + c) * a
    ≡⟨ *-distribˡ b c a ⟩
  b * a + c * a
    ≡⟨ cong₂ _+_ (*-comm b a) (*-comm c a) ⟩
  a * b + a * c
    ∎

-- 引理 B: 3·(3·x) + 3·(3·(3·y)) ≡ 3·(3·(x + 3·y))
split9 : ∀ x y → 3 * (3 * x) + 3 * (3 * (3 * y)) ≡ 3 * (3 * (x + 3 * y))
split9 x y = begin
  3 * (3 * x) + 3 * (3 * (3 * y))
    ≡⟨ cong₂ _+_ (sym (*-assoc 3 3 x)) (sym (*-assoc 3 3 (3 * y))) ⟩
  (3 * 3) * x + (3 * 3) * (3 * y)
    ≡⟨ sym (distribʳ (3 * 3) x (3 * y)) ⟩
  (3 * 3) * (x + 3 * y)
    ≡⟨ *-assoc 3 3 (x + 3 * y) ⟩
  3 * (3 * (x + 3 * y))
    ∎

-- 引理 C: 3·(3·z) ≡ 4·(3·(3·w)) 当 z ≡ 4·w（换 4 到外层）
mul4-out : ∀ z w → z ≡ 4 * w → 3 * (3 * z) ≡ 4 * (3 * (3 * w))
mul4-out z w e = begin
  3 * (3 * z)
    ≡⟨ cong (λ v → 3 * (3 * v)) e ⟩
  3 * (3 * (4 * w))
    ≡⟨ sym (*-assoc 3 3 (4 * w)) ⟩
  (3 * 3) * (4 * w)
    ≡⟨ *-comm (3 * 3) (4 * w) ⟩
  (4 * w) * (3 * 3)
    ≡⟨ *-assoc 4 w (3 * 3) ⟩
  4 * (w * (3 * 3))
    ≡⟨ cong (4 *_) (*-comm w (3 * 3)) ⟩
  4 * ((3 * 3) * w)
    ≡⟨ cong (4 *_) (*-assoc 3 3 w) ⟩
  4 * (3 * (3 * w))
    ∎

--------------------------------------------------------------------------------
-- §4. 主定理: witness-sat（两步归纳）
--------------------------------------------------------------------------------

Sat : ℕ → Set
Sat n = wt n * wt n + 3 * (ws n * ws n) ≡ 4 * pow3 n

sat-step : ∀ n → Sat n → Sat (suc (suc n))
sat-step n h = begin
  (3 * wt n) * (3 * wt n) + 3 * ((3 * ws n) * (3 * ws n))
    ≡⟨ cong₂ _+_ (sq3 (wt n)) (cong (3 *_) (sq3 (ws n))) ⟩
  3 * (3 * (wt n * wt n)) + 3 * (3 * (3 * (ws n * ws n)))
    ≡⟨ split9 (wt n * wt n) (ws n * ws n) ⟩
  3 * (3 * (wt n * wt n + 3 * (ws n * ws n)))
    ≡⟨ cong (λ v → 3 * (3 * v)) h ⟩
  3 * (3 * (4 * pow3 n))
    ≡⟨ mul4-out (4 * pow3 n) (pow3 n) refl ⟩
  4 * (3 * (3 * pow3 n))
    ≡⟨ refl ⟩
  4 * pow3 (suc (suc n))
    ∎

witness-sat : ∀ n → Sat n
witness-sat = two-ind Sat base0 base1 sat-step
  where
  base0 : Sat zero                                   -- 2² + 3·0² = 4·3⁰
  base0 = refl                                       -- 4 + 0 ≡ 4（+ 对首参递归, 定义性）
  base1 : Sat (suc zero)                             -- 0² + 3·2² = 4·3¹
  base1 = refl

--------------------------------------------------------------------------------
-- §5. 见证与冻结陈述的对应（注记, 非证明义务）
--------------------------------------------------------------------------------
-- witness n = (wt n, ws n):
--   n = 2k（偶）: (2·3ᵏ, 0)   —— v2 偶分支代表元
--   n = 2k+1（奇）: (0, 2·3ᵏ) —— v2 奇分支代表元
-- 负部/另一代表元（±3ᵏ,±3ᵏ 等）由 ℤ 符号对称给出（未形式化, 注记）。
