{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Fermat.FermatL4_NatLift
-- 费马大定理的离散基座 — L4 ℤ/ℕ 提升层
--
-- 数学背景 (13-flt-analysis.md §9.2 "ℤ 提升是元论证" 的构造性闭合):
--   L2 已证 GF(3) 层: n 偶 ⟹ 非零三元无解 (flt-even-nonsol), 即任何解必过零通道.
--   本层把该同余事实**提升到整数**: 通过模 3 同态 red₃ : ℕ → Trit,
--   证明一个真正的 ℤ 命题:
--
--     若 a,b,c ∈ ℤ⁺, 3 ∤ abc, 且 n = 2k ≥ 2 为偶, 则 aⁿ + bⁿ ≠ cⁿ.
--
--   等价叙述 (零通道的整数形式): n 偶的费马方程任何正整数解必须满足 3 | abc.
--   这是 13-flt-analysis §3.3/§5.2 中"勾股三元组必含 3 的倍数"的精确一般化.
--
-- 精确边界 (写进类型, 不越界):
--   * 本定理是**同余必要条件**: 它排除的只是"三数皆非 3 倍数"的情形.
--   * 它不断言 ℤ 上无解 (那需要 Archimedes 序, 见 13-flt §5), 只断言解的形状约束.
--   * 奇指数 n 的情形在 GF(3) 层处处有解 (flt-mod3-sol-112/221), 本层不涉及.
--
-- 本层主定理 (全部 0 postulate):
--   red₃ 环同态: red₃-homo-+ , red₃-homo-* , red₃-pow (幂与 pow3 交换)
--   flt-even-nat-nonsol : 3∤abc + n偶 ⟹ aⁿ+bⁿ≠cⁿ   [主定理, 含零通道推论]
--   flt-even-nat-zero-channel : aⁿ+bⁿ=cⁿ + n偶 ⟹ 3|a ⊎ 3|b ⊎ 3|c
--
-- 依赖: FermatL1 (pow3-even, GF(3)× 偶次坍缩), Trit (环公理), Data.Nat

module Sovereign.Problem.Fermat.FermatL4_NatLift where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_
  ; ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc
  ; ⊗-distribˡ-⊕)
open import Sovereign.Problem.Fermat.FermatL0 using (pow3; pow3-expand)
open import Sovereign.Problem.Fermat.FermatL1 using (pow3-even)

--------------------------------------------------------------------------------
-- §1. 模 3 同态 red₃ : ℕ → Trit
--
-- red₃ n = n mod 3 (嵌入 Trit). 逐 3 步递归, 不经 mod-helper (proof-engineer 附录 1).
--------------------------------------------------------------------------------

red₃ : ℕ → Trit
red₃ zero = T₀
red₃ (suc zero) = T₁
red₃ (suc (suc zero)) = T₂
red₃ (suc (suc (suc n))) = red₃ n

-- red₃ 吸收 3 步: red₃ (n+3) = red₃ n
red₃-step3 : ∀ n → red₃ (suc (suc (suc n))) ≡ red₃ n
red₃-step3 n = refl

-- red₃ 把后继映为"加 T₁": red₃ (n+1) = red₃ n ⊕ T₁
red₃-suc : ∀ n → red₃ (suc n) ≡ red₃ n ⊕ T₁
red₃-suc zero = refl
red₃-suc (suc zero) = refl
red₃-suc (suc (suc zero)) = refl
red₃-suc (suc (suc (suc n))) = begin
  red₃ (suc (suc (suc (suc n))))    ≡⟨ red₃-step3 (suc n) ⟩
  red₃ (suc n)                      ≡⟨ red₃-suc n ⟩
  red₃ n ⊕ T₁                        ≡⟨ cong (_⊕ T₁) (sym (red₃-step3 n)) ⟩
  red₃ (suc (suc (suc n))) ⊕ T₁      ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §2. red₃ 保持加法 (环同态)
--------------------------------------------------------------------------------

red₃-homo-+ : ∀ m n → red₃ (m + n) ≡ red₃ m ⊕ red₃ n
red₃-homo-+ zero n = begin
  red₃ (zero + n)    ≡⟨⟩
  red₃ n             ≡⟨ sym (⊕-identityˡ (red₃ n)) ⟩
  T₀ ⊕ red₃ n        ≡⟨⟩
  red₃ zero ⊕ red₃ n  ∎
  where open ≡-Reasoning
red₃-homo-+ (suc m) n = begin
  red₃ (suc m + n)            ≡⟨⟩
  red₃ (suc (m + n))          ≡⟨ red₃-suc (m + n) ⟩
  red₃ (m + n) ⊕ T₁            ≡⟨ cong₂ _⊕_ (red₃-homo-+ m n) refl ⟩
  (red₃ m ⊕ red₃ n) ⊕ T₁       ≡⟨ swap (red₃ m) (red₃ n) ⟩
  (red₃ m ⊕ T₁) ⊕ red₃ n       ≡⟨ cong₂ _⊕_ (sym (red₃-suc m)) refl ⟩
  red₃ (suc m) ⊕ red₃ n        ∎
  where open ≡-Reasoning
        -- (a ⊕ b) ⊕ T₁ ≡ (a ⊕ T₁) ⊕ b : GF(3) 交换+结合
        swap : ∀ a b → (a ⊕ b) ⊕ T₁ ≡ (a ⊕ T₁) ⊕ b
        swap a b = begin
          (a ⊕ b) ⊕ T₁        ≡⟨ ⊕-assoc a b T₁ ⟩
          a ⊕ (b ⊕ T₁)        ≡⟨ cong (a ⊕_) (⊕-comm b T₁) ⟩
          a ⊕ (T₁ ⊕ b)        ≡⟨ sym (⊕-assoc a T₁ b) ⟩
          (a ⊕ T₁) ⊕ b         ∎

--------------------------------------------------------------------------------
-- §3. red₃ 保持乘法 (环同态)
--------------------------------------------------------------------------------

red₃-homo-* : ∀ m n → red₃ (m * n) ≡ red₃ m ⊗ red₃ n
red₃-homo-* zero n = begin
  red₃ (zero * n)    ≡⟨⟩
  red₃ zero           ≡⟨⟩
  T₀                  ≡⟨ sym (⊗-zeroˡ-internal (red₃ n)) ⟩
  T₀ ⊗ red₃ n         ≡⟨⟩
  red₃ zero ⊗ red₃ n  ∎
  where open ≡-Reasoning
        ⊗-zeroˡ-internal : ∀ x → T₀ ⊗ x ≡ T₀
        ⊗-zeroˡ-internal T₀ = refl; ⊗-zeroˡ-internal T₁ = refl; ⊗-zeroˡ-internal T₂ = refl
red₃-homo-* (suc m) n = begin
  red₃ (suc m * n)            ≡⟨⟩
  red₃ (n + m * n)            ≡⟨ red₃-homo-+ n (m * n) ⟩
  red₃ n ⊕ red₃ (m * n)       ≡⟨ cong (red₃ n ⊕_) (red₃-homo-* m n) ⟩
  red₃ n ⊕ (red₃ m ⊗ red₃ n)  ≡⟨ ⊕-comm (red₃ n) (red₃ m ⊗ red₃ n) ⟩
  (red₃ m ⊗ red₃ n) ⊕ red₃ n  ≡⟨ cong₂ _⊕_ refl (sym (⊗-identityʳ (red₃ n))) ⟩
  (red₃ m ⊗ red₃ n) ⊕ (red₃ n ⊗ T₁) ≡⟨ cong (_⊕ (red₃ n ⊗ T₁)) (⊗-comm (red₃ m) (red₃ n)) ⟩
  (red₃ n ⊗ red₃ m) ⊕ (red₃ n ⊗ T₁) ≡⟨ sym (⊗-distribˡ-⊕ (red₃ n) (red₃ m) T₁) ⟩
  red₃ n ⊗ (red₃ m ⊕ T₁)      ≡⟨ cong (red₃ n ⊗_) (sym (red₃-suc m)) ⟩
  red₃ n ⊗ red₃ (suc m)       ≡⟨ ⊗-comm (red₃ n) (red₃ (suc m)) ⟩
  red₃ (suc m) ⊗ red₃ n        ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §3b. 本地不等号 与 pow3 镜像 (定义前置, 供 §4/§5 引用)
--------------------------------------------------------------------------------

-- 本地不等号 (同 FermatL0 ≢₃ 惯例)
_≢_ : Trit → Trit → Set
x ≢ y = x ≡ y → ⊥

-- 偶次坍缩: 非零元偶次幂 = T₁ (直接引用 L1.pow3-even; FermatL0.pow3)
pow3-even-eq : ∀ x → x ≢ T₀ → ∀ n → pow3 x (n * 2) ≡ T₁
pow3-even-eq x xn0 n = pow3-even x (λ eq → xn0 eq) n

--------------------------------------------------------------------------------
-- §4. red₃ 与幂交换: red₃ (a^n) = pow3 (red₃ a) n
--     (把 GF(3) 层 pow3 的结果经同态拉回 ℕ)
--------------------------------------------------------------------------------

red₃-pow : ∀ a n → red₃ (a ^ n) ≡ pow3 (red₃ a) n
red₃-pow a zero = begin
  red₃ (a ^ zero)   ≡⟨⟩
  red₃ 1             ≡⟨⟩
  T₁                 ≡⟨ sym (pow3-refl-zero (red₃ a)) ⟩
  pow3 (red₃ a) zero ∎
  where open ≡-Reasoning
        pow3-refl-zero : ∀ x → pow3 x zero ≡ T₁
        pow3-refl-zero x = refl
red₃-pow a (suc n) = begin
  red₃ (a ^ suc n)        ≡⟨⟩
  red₃ (a * a ^ n)        ≡⟨ red₃-homo-* a (a ^ n) ⟩
  red₃ a ⊗ red₃ (a ^ n)   ≡⟨ cong (red₃ a ⊗_) (red₃-pow a n) ⟩
  red₃ a ⊗ pow3 (red₃ a) n    ≡⟨ sym (pow3-expand (red₃ a) n) ⟩
  pow3 (red₃ a) (suc n) ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §5. 主定理: 偶次费马方程 ℤ 层无"三皆非 3-倍数"解
--
--   精确陈述: 若 a,b,c ∈ ℕ⁺, 3∤a, 3∤b, 3∤c, n = (suc k)*2 ≥ 2,
--   则 aⁿ + bⁿ ≠ cⁿ.
--
--   证明: 反设相等, 经 red₃ 同态拉回 GF(3):
--     red₃(aⁿ+bⁿ) = red₃(aⁿ) ⊕ red₃(bⁿ) = pow3(red₃ a)(2k) ⊕ pow3(red₃ b)(2k)
--                  = T₁ ⊕ T₁ = T₂          (3∤ 前提 ⟹ red₃ 非零 ⟹ pow3-even)
--     但 red₃(cⁿ) = pow3(red₃ c)(2k) = T₁, 与 T₂ ≠ T₁ 矛盾.
--------------------------------------------------------------------------------

T₂≢T₁ : T₂ ≡ T₁ → ⊥
T₂≢T₁ ()

flt-even-nat-nonsol : ∀ a b c k →
                      red₃ a ≢ T₀ → red₃ b ≢ T₀ → red₃ c ≢ T₀ →
                      a ^ (suc k * 2) + b ^ (suc k * 2) ≡ c ^ (suc k * 2) → ⊥
flt-even-nat-nonsol a b c k ra rb rc eq =
  T₂≢T₁ (trans (sym lhs) (trans (cong red₃ eq) rhs))
  where
  open ≡-Reasoning
  n = suc k * 2
  -- red₃ a^n = T₁ (3∤a ⟹ red₃ a 非零 ⟹ 偶次坍缩)
  pa : red₃ (a ^ n) ≡ T₁
  pa = trans (red₃-pow a n) (pow3-even-eq (red₃ a) ra (suc k))
  pb : red₃ (b ^ n) ≡ T₁
  pb = trans (red₃-pow b n) (pow3-even-eq (red₃ b) rb (suc k))
  -- 左端经同态 = T₁ ⊕ T₁ = T₂
  lhs : red₃ (a ^ n + b ^ n) ≡ T₂
  lhs = begin
    red₃ (a ^ n + b ^ n)        ≡⟨ red₃-homo-+ (a ^ n) (b ^ n) ⟩
    red₃ (a ^ n) ⊕ red₃ (b ^ n) ≡⟨ cong₂ _⊕_ pa pb ⟩
    T₁ ⊕ T₁                      ≡⟨⟩
    T₂                            ∎
  -- 右端 red₃ c^n = T₁
  rhs : red₃ (c ^ n) ≡ T₁
  rhs = trans (red₃-pow c n) (pow3-even-eq (red₃ c) rc (suc k))

--------------------------------------------------------------------------------
-- §6. 零通道 (整数形式): aⁿ+bⁿ=cⁿ + n偶 ⟹ 3|a ⊎ 3|b ⊎ 3|c
--
--   3|a 用 red₃ a ≡ T₀ 表示 (即 a ≡ 0 mod 3). 由 flt-even-nat-nonsol 直接取反.
--------------------------------------------------------------------------------

-- 三分支穷举: 每个 ℕ 的 red₃ 要么零要么非零
red₃-zero? : ∀ n → red₃ n ≡ T₀ ⊎ red₃ n ≢ T₀
red₃-zero? zero = inj₁ refl
red₃-zero? (suc zero) = inj₂ (λ ())
red₃-zero? (suc (suc zero)) = inj₂ (λ ())
red₃-zero? (suc (suc (suc n))) = red₃-zero? n

flt-even-nat-zero-channel : ∀ a b c k →
                            a ^ (suc k * 2) + b ^ (suc k * 2) ≡ c ^ (suc k * 2) →
                            red₃ a ≡ T₀ ⊎ red₃ b ≡ T₀ ⊎ red₃ c ≡ T₀
flt-even-nat-zero-channel a b c k eq with red₃-zero? a | red₃-zero? b | red₃-zero? c
flt-even-nat-zero-channel a b c k eq | inj₁ za | _       | _       = inj₁ za
flt-even-nat-zero-channel a b c k eq | inj₂ za | inj₁ zb | _       = inj₂ (inj₁ zb)
flt-even-nat-zero-channel a b c k eq | inj₂ za | inj₂ zb | inj₁ zc = inj₂ (inj₂ zc)
flt-even-nat-zero-channel a b c k eq | inj₂ za | inj₂ zb | inj₂ zc =
  ⊥-elim (flt-even-nat-nonsol a b c k za zb zc eq)
