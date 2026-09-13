{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.FinMixedRadix
--
-- 混合基数编码的注入性（离散基座，用于有限状态空间的编码链）。
--
-- 基 19（Fin 19）与基 12（Fin 12）两个实例都给出，供不同状态编码复用。
--
-- 数学背景：
--   把 (Fin k → Fin 19) 编码为自然数
--       enc k f = f 0 + 19 * enc k (f ∘ suc)
--   这是 19 进制的 Horner 展开。本模块证明：
--     1. 首位可提取：(enc (suc k) f) % 19 ≡ toℕ (f 0)      [head]
--     2. 尾位可提取：enc (suc k) f ≡ enc (suc k) g
--                    ⇒ enc k (f ∘ suc) ≡ enc k (g ∘ suc)     [enc-tail]
--     3. 编码注入（逐点）：enc k f ≡ enc k g ⇒ ∀ i, f i ≡ g i [enc-inj-pointwise]
--
-- 核心原则：
--   1. **只用 % 19 / *19 的字面量**，不引入对变量不归约的除数（见 prover_limits
--      agda-nonzero-instance-search）
--   2. **逐点注入**而非函数相等：本库无 funExt（非 cubical）
--   3. 消去步骤用 `≡-Reasoning` 而非嵌套 `cong (λ z → z * 19)`（后者在 Agda
--      2.9.0 下会多推断一层应用，见 prover_limits agda-cong-lambda-extra-application）
--
-- 包含：enc / head / head-eq / tail-eq / enc-tail / enc-inj-pointwise
-- 0 postulate / 0 hole。

module Sovereign.Analysis.FinMixedRadix where

open import Data.Nat using (ℕ; _+_; _*_; _%_; _^_; _≤_; _<_; zero; suc; z≤n; s≤s)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective; toℕ-fromℕ<)
open import Data.Nat.Properties using (*-comm; +-cancelˡ-≡; *-cancelʳ-≡; +-mono-≤; *-mono-≤; ≤-refl; m≤n⇒m≤1+n;
  ≤-reflexive; ≤-trans; +-comm; +-assoc; *-suc)
open import Data.Nat.DivMod using ([m+kn]%n≡m%n; m<n⇒m%n≡m)
open import Function.Base using (_∘_)
open import Sovereign.Structology.T6Rewrite
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst; module ≡-Reasoning)

enc : ∀ k → (Fin k → Fin 19) → ℕ
enc zero f = 0
enc (suc k) f = toℕ (f fzero) + 19 * enc k (f ∘ fsuc)

head : ∀ k (f : Fin (suc k) → Fin 19) → (toℕ (f fzero) + 19 * enc k (f ∘ fsuc)) % 19 ≡ toℕ (f fzero)
head k f = trans (cong (λ z → (toℕ (f fzero) + z) % 19) (*-comm 19 (enc k (f ∘ fsuc))))
                 (trans ([m+kn]%n≡m%n (toℕ (f fzero)) (enc k (f ∘ fsuc)) 19)
                        (m<n⇒m%n≡m (toℕ<n (f fzero))))

head-eq : ∀ k (f g : Fin (suc k) → Fin 19) → enc (suc k) f ≡ enc (suc k) g → toℕ (f fzero) ≡ toℕ (g fzero)
head-eq k f g eq = trans (sym (head k f)) (trans (cong (_% 19) eq) (head k g))

tail-eq : ∀ k (f g : Fin (suc k) → Fin 19) → enc (suc k) f ≡ enc (suc k) g →
  19 * enc k (f ∘ fsuc) ≡ 19 * enc k (g ∘ fsuc)
tail-eq k f g eq =
  +-cancelˡ-≡ (toℕ (g fzero)) (19 * enc k (f ∘ fsuc)) (19 * enc k (g ∘ fsuc))
    (subst (λ (z : ℕ) → z + 19 * enc k (f ∘ fsuc) ≡ toℕ (g fzero) + 19 * enc k (g ∘ fsuc))
           (head-eq k f g eq) eq)

enc-tail : ∀ k (f g : Fin (suc k) → Fin 19) → enc (suc k) f ≡ enc (suc k) g → enc k (f ∘ fsuc) ≡ enc k (g ∘ fsuc)
enc-tail k f g eq = *-cancelʳ-≡ (enc k (f ∘ fsuc)) (enc k (g ∘ fsuc)) 19 (begin
  enc k (f ∘ fsuc) * 19   ≡⟨ *-comm (enc k (f ∘ fsuc)) 19 ⟩
  19 * enc k (f ∘ fsuc)   ≡⟨ tail-eq k f g eq ⟩
  19 * enc k (g ∘ fsuc)   ≡⟨ *-comm 19 (enc k (g ∘ fsuc)) ⟩
  enc k (g ∘ fsuc) * 19   ∎)
  where open ≡-Reasoning

-- enc 注入性（逐点，避开 funext）
enc-inj-pointwise : ∀ k (f g : Fin k → Fin 19) → enc k f ≡ enc k g → ∀ i → f i ≡ g i
enc-inj-pointwise zero f g eq ()
enc-inj-pointwise (suc k) f g eq fzero = toℕ-injective (head-eq k f g eq)
enc-inj-pointwise (suc k) f g eq (fsuc i) =
  enc-inj-pointwise k (f ∘ fsuc) (g ∘ fsuc) (enc-tail k f g eq) i

--------------------------------------------------------------------------------
-- §2. 编码到 Fin N 的界（N k = 19 + 19 * N k 递归界，N 0 = 0）
--
-- 关键：用递归定义的界 N k 而非 19^k，避开 `19 ^ suc k` 与 `19 + 19 * 19^k`
-- 归约形式不同导致 ≤-refl 不闭合的算术归一化问题。
--------------------------------------------------------------------------------

N : ℕ → ℕ
N zero = 0
N (suc k) = 19 + 19 * N k

-- 首位 < 19 ⟹ 首位 ≤ 19
suc≤⇒≤ : ∀ {a : ℕ} → suc a ≤ 19 → a ≤ 19
suc≤⇒≤ (s≤s p) = m≤n⇒m≤1+n p

enc≤N : ∀ k (f : Fin k → Fin 19) → enc k f ≤ N k
enc≤N zero f = z≤n
enc≤N (suc k) f =
  +-mono-≤ (suc≤⇒≤ (toℕ<n (f fzero)))
           (*-mono-≤ (≤-refl {19}) (enc≤N k (f ∘ fsuc)))

-- 编码进 Fin (suc (N k))
encFin : ∀ k → (Fin k → Fin 19) → Fin (suc (N k))
encFin k f = fromℕ< (s≤s (enc≤N k f))

toℕ-encFin : ∀ k f → toℕ (encFin k f) ≡ enc k f
toℕ-encFin k f = toℕ-fromℕ< _

-- encFin 的逐点注入性
encFin-inj-pointwise :
  ∀ k (f g : Fin k → Fin 19) → encFin k f ≡ encFin k g → ∀ i → f i ≡ g i
encFin-inj-pointwise k f g eq =
  enc-inj-pointwise k f g
    (trans (sym (toℕ-encFin k f)) (trans (cong toℕ eq) (toℕ-encFin k g)))

--------------------------------------------------------------------------------
-- §3. 基 12 版本（Fin 12，用于 pairEnc 打包后的状态编码）
--
-- 与 §1–§2 完全同构，只把 19 换成 12；界用递归 N12 而非 12^k。
--------------------------------------------------------------------------------

enc12 : ∀ k → (Fin k → Fin 12) → ℕ
enc12 zero f = 0
enc12 (suc k) f = toℕ (f fzero) + 12 * enc12 k (f ∘ fsuc)

head12 : ∀ k (f : Fin (suc k) → Fin 12) →
  (toℕ (f fzero) + 12 * enc12 k (f ∘ fsuc)) % 12 ≡ toℕ (f fzero)
head12 k f =
  trans (cong (λ z → (toℕ (f fzero) + z) % 12) (*-comm 12 (enc12 k (f ∘ fsuc))))
        (trans ([m+kn]%n≡m%n (toℕ (f fzero)) (enc12 k (f ∘ fsuc)) 12)
               (m<n⇒m%n≡m (toℕ<n (f fzero))))

head12-eq : ∀ k (f g : Fin (suc k) → Fin 12) →
  enc12 (suc k) f ≡ enc12 (suc k) g → toℕ (f fzero) ≡ toℕ (g fzero)
head12-eq k f g eq = trans (sym (head12 k f)) (trans (cong (_% 12) eq) (head12 k g))

tail12-eq : ∀ k (f g : Fin (suc k) → Fin 12) → enc12 (suc k) f ≡ enc12 (suc k) g →
  12 * enc12 k (f ∘ fsuc) ≡ 12 * enc12 k (g ∘ fsuc)
tail12-eq k f g eq =
  +-cancelˡ-≡ (toℕ (g fzero)) (12 * enc12 k (f ∘ fsuc)) (12 * enc12 k (g ∘ fsuc))
    (subst (λ (z : ℕ) → z + 12 * enc12 k (f ∘ fsuc) ≡ toℕ (g fzero) + 12 * enc12 k (g ∘ fsuc))
           (head12-eq k f g eq) eq)

enc12-tail : ∀ k (f g : Fin (suc k) → Fin 12) →
  enc12 (suc k) f ≡ enc12 (suc k) g → enc12 k (f ∘ fsuc) ≡ enc12 k (g ∘ fsuc)
enc12-tail k f g eq = *-cancelʳ-≡ (enc12 k (f ∘ fsuc)) (enc12 k (g ∘ fsuc)) 12 (begin
  enc12 k (f ∘ fsuc) * 12   ≡⟨ *-comm (enc12 k (f ∘ fsuc)) 12 ⟩
  12 * enc12 k (f ∘ fsuc)   ≡⟨ tail12-eq k f g eq ⟩
  12 * enc12 k (g ∘ fsuc)   ≡⟨ *-comm 12 (enc12 k (g ∘ fsuc)) ⟩
  enc12 k (g ∘ fsuc) * 12   ∎)
  where open ≡-Reasoning

enc12-inj-pointwise : ∀ k (f g : Fin k → Fin 12) → enc12 k f ≡ enc12 k g → ∀ i → f i ≡ g i
enc12-inj-pointwise zero f g eq ()
enc12-inj-pointwise (suc k) f g eq fzero = toℕ-injective (head12-eq k f g eq)
enc12-inj-pointwise (suc k) f g eq (fsuc i) =
  enc12-inj-pointwise k (f ∘ fsuc) (g ∘ fsuc) (enc12-tail k f g eq) i

-- 递归界 N12
N12 : ℕ → ℕ
N12 zero = 11
N12 (suc k) = 11 + 12 * N12 k

-- 首位 < 12 ⟹ 首位 ≤ 11
suc≤⇒≤11 : ∀ {m : ℕ} → suc m ≤ 12 → m ≤ 11
suc≤⇒≤11 (s≤s p) = p

enc12≤N12 : ∀ k (f : Fin k → Fin 12) → enc12 k f ≤ N12 k
enc12≤N12 zero f = z≤n
enc12≤N12 (suc k) f =
  +-mono-≤ (suc≤⇒≤11 (toℕ<n (f fzero)))
           (*-mono-≤ (≤-refl {12}) (enc12≤N12 k (f ∘ fsuc)))

enc12Fin : ∀ k → (Fin k → Fin 12) → Fin (suc (N12 k))
enc12Fin k f = fromℕ< (s≤s (enc12≤N12 k f))

toℕ-enc12Fin : ∀ k f → toℕ (enc12Fin k f) ≡ enc12 k f
toℕ-enc12Fin k f = toℕ-fromℕ< _

enc12Fin-inj-pointwise :
  ∀ k (f g : Fin k → Fin 12) → enc12Fin k f ≡ enc12Fin k g → ∀ i → f i ≡ g i
enc12Fin-inj-pointwise k f g eq =
  enc12-inj-pointwise k f g
    (trans (sym (toℕ-enc12Fin k f)) (trans (cong toℕ eq) (toℕ-enc12Fin k g)))

--------------------------------------------------------------------------------
-- §4. C1：基 12 编码的上界 enc12 k f + 1 ≤ 12 ^ k（等价于 enc12 k f < 12 ^ k）
--
-- 未来态锚定：目标右端 12 ^ suc k 定义性归约为 12 * 12 ^ k，
-- 故把左端往 `12 * (enc12 k … + 1)` 形态推，而不是从 12^k 逐项剥离。
-- 关键算术引理是 bound-arith：(11 + 12a) + 1 ≡ 12 * suc a
-- （用 *-suc 展开 `12 * suc a`，绕开 `12 * suc a` 的深归约形）。
--
-- 与 §2 的 N12 路线并存：N12 是「编码 ≤ 递归界」，本条直接给出 12^k 的严格界，
-- 供 C2–C4 的 `stateEnc : … → Fin (12 ^ k)` 使用。
--------------------------------------------------------------------------------

-- 算术引理：(11 + 12 * a) + 1 ≡ 12 * (a + 1)
-- 结论必须写成 `12 * (a + 1)`：Agda 的 `_+_` 对首参数递归，`a + 1` 不归约为 `suc a`，
-- 故 `12 * suc a` 与 `12 * (a + 1)` 不是同一归约形（末步用 +-comm a 1 桥接）。
bound-arith : ∀ a → (11 + 12 * a) + 1 ≡ 12 * (a + 1)
bound-arith a = begin
  (11 + 12 * a) + 1   ≡⟨ cong (_+ 1) (+-comm 11 (12 * a)) ⟩
  (12 * a + 11) + 1   ≡⟨ +-assoc (12 * a) 11 1 ⟩
  12 * a + (11 + 1)   ≡⟨⟩
  12 * a + 12         ≡⟨ +-comm (12 * a) 12 ⟩
  12 + 12 * a         ≡⟨ sym (*-suc 12 a) ⟩
  12 * suc a          ≡⟨ cong (12 *_) (sym (+-comm a 1)) ⟩
  12 * (a + 1)        ∎
  where open ≡-Reasoning

-- C1 主定理：enc12 k f + 1 ≤ 12 ^ k
enc12-bound : ∀ k (f : Fin k → Fin 12) → enc12 k f + 1 ≤ 12 ^ k
enc12-bound zero f = s≤s z≤n
enc12-bound (suc k) f =
  ≤-trans
    (+-mono-≤ (+-mono-≤ (suc≤⇒≤11 (toℕ<n (f fzero)))
                        (≤-refl {12 * enc12 k (f ∘ fsuc)}))
              (≤-refl {1}))
    (≤-trans (≤-reflexive (bound-arith (enc12 k (f ∘ fsuc))))
             (*-mono-≤ (≤-refl {12}) (enc12-bound k (f ∘ fsuc))))

-- 严格界形式：suc (enc12 k f) ≤ 12 ^ k（供 fromℕ< 构造 Fin (12 ^ k)）
-- 注：`x + 1` 与 `suc x` 不是同一归约形（见 prover_limits:
-- agda-nat-plus-first-arg-normal-form），故用 subst + +-comm 桥接。
suc≤12 : ∀ k (f : Fin k → Fin 12) → suc (enc12 k f) ≤ 12 ^ k
suc≤12 k f = subst (λ z → z ≤ 12 ^ k) (+-comm (enc12 k f) 1) (enc12-bound k f)

--------------------------------------------------------------------------------
-- §5. 对抗验证（具体点独立 refl 计算，与 §4 定理实例交叉比对）
--
-- 全 11 的编码恰好取到 12 ^ k - 1，故界是**紧**的：任何更小的界都会失败。
--------------------------------------------------------------------------------

f11 : Fin 12
f11 = fromℕ< {11} {12} (≤-refl {12})

f0 : Fin 12
f0 = fromℕ< {0} {12} (s≤s z≤n)

-- k = 1，f = [11]：enc12 = 11，11 + 1 = 12 = 12 ^ 1
_ : enc12 1 (λ _ → f11) + 1 ≡ 12
_ = refl

-- k = 2，f = [11,11]：enc12 = 11 + 12 * 11 = 143，143 + 1 = 144 = 12 ^ 2
_ : enc12 2 (λ { fzero → f11 ; (fsuc _) → f11 }) + 1 ≡ 144
_ = refl

-- k = 3，f = [11,11,11]：enc12 = 11 + 12 * 143 = 1727，1727 + 1 = 1728 = 12 ^ 3
_ : enc12 3 (λ _ → f11) + 1 ≡ 1728
_ = refl

-- 全零：enc12 = 0，0 + 1 = 1
_ : enc12 3 (λ _ → f0) + 1 ≡ 1
_ = refl
