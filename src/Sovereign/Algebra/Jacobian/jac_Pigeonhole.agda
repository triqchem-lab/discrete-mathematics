{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_Pigeonhole
-- 鸽巢原理: GF(3)¹ 上 单射 ⟹ 满射
-- 完全构造性证明, 0 postulate
--
-- 策略: 显式等式传递 + 9-case 碰撞穷举
--
-- 元理论对齐: 与 Dvir (2009) 有限域挂谷猜想证明同构 —
--   Dvir 将高维几何重叠还原为多项式空间维数与点集阶数的鸽巢矛盾;
--   本模块将雅可比逐点条件还原为函数表矩阵的列互异与行列式非零。
--   参见: docs/Kakeya-元诊断-连续统病态vs离散自愈.md §二

module Sovereign.Algebra.Jacobian.jac_Pigeonhole where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)

open import Agda.Builtin.Equality.Rewrite

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂)

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (n<1+n; <-irrefl)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Fin.Properties using (pigeonhole)
open import Function using (_∘_)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Inj1 : (Trit → Trit) → Set
Inj1 f = ∀ {x y} → f x ≡ f y → x ≡ y

Surj1 : (Trit → Trit) → Set
Surj1 f = ∀ q → Σ Trit (λ p → f p ≡ q)

ne01 : T₀ ≡ T₁ → ⊥ ; ne01 ()
ne02 : T₀ ≡ T₂ → ⊥ ; ne02 ()
ne12 : T₁ ≡ T₂ → ⊥ ; ne12 ()

--------------------------------------------------------------------------------
-- 核心: 3 个不同值 misses q → 碰撞 → 矛盾
-- 显式传递等式证明, 避免 with 抽象问题
--------------------------------------------------------------------------------

all-miss-T₀ : ∀ f → Inj1 f →
  (f T₀ ≡ T₀ → ⊥) → (f T₁ ≡ T₀ → ⊥) → (f T₂ ≡ T₀ → ⊥) → ⊥
all-miss-T₀ f inj n₀ n₁ n₂ =
  go (f T₀) refl (f T₁) refl (f T₂) refl
  where
  go : ∀ a → a ≡ f T₀ → ∀ b → b ≡ f T₁ → ∀ c → c ≡ f T₂ → ⊥
  go T₀ e₀ _ _ _ _ = n₀ (sym e₀)
  go _ _ T₀ e₁ _ _ = n₁ (sym e₁)
  go _ _ _ _ T₀ e₂ = n₂ (sym e₂)
  go T₁ e₀ T₁ e₁ _ _ = ne01 (inj (trans (sym e₀) e₁))
  go T₁ e₀ T₂ _ T₁ e₂ = ne02 (inj (trans (sym e₀) e₂))
  go T₁ _ T₂ e₁ T₂ e₂ = ne12 (inj (trans (sym e₁) e₂))
  go T₂ _ T₁ e₁ T₁ e₂ = ne12 (inj (trans (sym e₁) e₂))
  go T₂ e₀ T₁ _ T₂ e₂ = ne02 (inj (trans (sym e₀) e₂))
  go T₂ e₀ T₂ e₁ _ _ = ne01 (inj (trans (sym e₀) e₁))

all-miss-T₁ : ∀ f → Inj1 f →
  (f T₀ ≡ T₁ → ⊥) → (f T₁ ≡ T₁ → ⊥) → (f T₂ ≡ T₁ → ⊥) → ⊥
all-miss-T₁ f inj n₀ n₁ n₂ =
  go (f T₀) refl (f T₁) refl (f T₂) refl
  where
  go : ∀ a → a ≡ f T₀ → ∀ b → b ≡ f T₁ → ∀ c → c ≡ f T₂ → ⊥
  go T₁ e₀ _ _ _ _ = n₀ (sym e₀)
  go _ _ T₁ e₁ _ _ = n₁ (sym e₁)
  go _ _ _ _ T₁ e₂ = n₂ (sym e₂)
  go T₀ e₀ T₀ e₁ _ _ = ne01 (inj (trans (sym e₀) e₁))
  go T₀ e₀ T₂ _ T₀ e₂ = ne02 (inj (trans (sym e₀) e₂))
  go T₀ _ T₂ e₁ T₂ e₂ = ne12 (inj (trans (sym e₁) e₂))
  go T₂ _ T₀ e₁ T₀ e₂ = ne12 (inj (trans (sym e₁) e₂))
  go T₂ e₀ T₀ _ T₂ e₂ = ne02 (inj (trans (sym e₀) e₂))
  go T₂ e₀ T₂ e₁ _ _ = ne01 (inj (trans (sym e₀) e₁))

all-miss-T₂ : ∀ f → Inj1 f →
  (f T₀ ≡ T₂ → ⊥) → (f T₁ ≡ T₂ → ⊥) → (f T₂ ≡ T₂ → ⊥) → ⊥
all-miss-T₂ f inj n₀ n₁ n₂ =
  go (f T₀) refl (f T₁) refl (f T₂) refl
  where
  go : ∀ a → a ≡ f T₀ → ∀ b → b ≡ f T₁ → ∀ c → c ≡ f T₂ → ⊥
  go T₂ e₀ _ _ _ _ = n₀ (sym e₀)
  go _ _ T₂ e₁ _ _ = n₁ (sym e₁)
  go _ _ _ _ T₂ e₂ = n₂ (sym e₂)
  go T₀ e₀ T₀ e₁ _ _ = ne01 (inj (trans (sym e₀) e₁))
  go T₀ e₀ T₁ _ T₀ e₂ = ne02 (inj (trans (sym e₀) e₂))
  go T₀ _ T₁ e₁ T₁ e₂ = ne12 (inj (trans (sym e₁) e₂))
  go T₁ _ T₀ e₁ T₀ e₂ = ne12 (inj (trans (sym e₁) e₂))
  go T₁ e₀ T₀ _ T₁ e₂ = ne02 (inj (trans (sym e₀) e₂))
  go T₁ e₀ T₁ e₁ _ _ = ne01 (inj (trans (sym e₀) e₁))

--------------------------------------------------------------------------------
-- 鸽巢定理: 单射 ⟹ 满射
--------------------------------------------------------------------------------

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Trit 可判定等式
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

_≟T_ : ∀ (x y : Trit) → Dec (x ≡ y)
T₀ ≟T T₀ = yes refl
T₀ ≟T T₁ = no λ ()
T₀ ≟T T₂ = no λ ()
T₁ ≟T T₀ = no λ ()
T₁ ≟T T₁ = yes refl
T₁ ≟T T₂ = no λ ()
T₂ ≟T T₀ = no λ ()
T₂ ≟T T₁ = no λ ()
T₂ ≟T T₂ = yes refl

pigeonhole-1 : ∀ f → Inj1 f → Surj1 f
pigeonhole-1 f inj T₀ with f T₀ ≟T T₀
... | yes e = T₀ , e
... | no n₀ with f T₁ ≟T T₀
... | yes e = T₁ , e
... | no n₁ with f T₂ ≟T T₀
... | yes e = T₂ , e
... | no n₂ = ⊥-elim (all-miss-T₀ f inj n₀ n₁ n₂)
pigeonhole-1 f inj T₁ with f T₀ ≟T T₁
... | yes e = T₀ , e
... | no n₀ with f T₁ ≟T T₁
... | yes e = T₁ , e
... | no n₁ with f T₂ ≟T T₁
... | yes e = T₂ , e
... | no n₂ = ⊥-elim (all-miss-T₁ f inj n₀ n₁ n₂)
pigeonhole-1 f inj T₂ with f T₀ ≟T T₂
... | yes e = T₀ , e
... | no n₀ with f T₁ ≟T T₂
... | yes e = T₁ , e
... | no n₁ with f T₂ ≟T T₂
... | yes e = T₂ , e
... | no n₂ = ⊥-elim (all-miss-T₂ f inj n₀ n₁ n₂)

--------------------------------------------------------------------------------
-- 4. GF(3)² 鸽巢原理 (9 点)
--------------------------------------------------------------------------------

GF3² : Set
GF3² = Trit × Trit

Inj2 : (GF3² → GF3²) → Set
Inj2 F = ∀ {p q} → F p ≡ F q → p ≡ q

Surj2 : (GF3² → GF3²) → Set
Surj2 F = ∀ q → Σ GF3² (λ p → F p ≡ q)

-- GF(3)² 可判定等式 (由分量级 ≟T 构造)
pair-eq : ∀ {a b c d : Trit} → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
pair-eq refl refl = refl

fst² : GF3² → Trit
fst² (x , y) = x

snd² : GF3² → Trit
snd² (x , y) = y

_≟²_ : ∀ (p q : GF3²) → Dec (p ≡ q)
(a , b) ≟² (c , d) with a ≟T c | b ≟T d
... | yes ea | yes eb = yes (pair-eq ea eb)
... | no na | _ = no (λ eq → na (cong fst² eq))
... | _ | no nb = no (λ eq → nb (cong snd² eq))

--------------------------------------------------------------------------------
-- 4b. Fin 编码基础设施 (用于 pigeonhole 标准库调用)
--------------------------------------------------------------------------------

-- GF3² → Fin 9 双射
encode9 : GF3² → Fin 9
encode9 (T₀ , T₀) = zero
encode9 (T₀ , T₁) = suc zero
encode9 (T₀ , T₂) = suc (suc zero)
encode9 (T₁ , T₀) = suc (suc (suc zero))
encode9 (T₁ , T₁) = suc (suc (suc (suc zero)))
encode9 (T₁ , T₂) = suc (suc (suc (suc (suc zero))))
encode9 (T₂ , T₀) = suc (suc (suc (suc (suc (suc zero)))))
encode9 (T₂ , T₁) = suc (suc (suc (suc (suc (suc (suc zero))))))
encode9 (T₂ , T₂) = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

decode9 : Fin 9 → GF3²
decode9 zero = (T₀ , T₀)
decode9 (suc zero) = (T₀ , T₁)
decode9 (suc (suc zero)) = (T₀ , T₂)
decode9 (suc (suc (suc zero))) = (T₁ , T₀)
decode9 (suc (suc (suc (suc zero)))) = (T₁ , T₁)
decode9 (suc (suc (suc (suc (suc zero))))) = (T₁ , T₂)
decode9 (suc (suc (suc (suc (suc (suc zero)))))) = (T₂ , T₀)
decode9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = (T₂ , T₁)
decode9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = (T₂ , T₂)

encode9-decode9 : ∀ (i : Fin 9) → encode9 (decode9 i) ≡ i
encode9-decode9 zero = refl
encode9-decode9 (suc zero) = refl
encode9-decode9 (suc (suc zero)) = refl
encode9-decode9 (suc (suc (suc zero))) = refl
encode9-decode9 (suc (suc (suc (suc zero)))) = refl
encode9-decode9 (suc (suc (suc (suc (suc zero))))) = refl
encode9-decode9 (suc (suc (suc (suc (suc (suc zero)))))) = refl
encode9-decode9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
encode9-decode9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl

decode9-encode9 : ∀ (p : GF3²) → decode9 (encode9 p) ≡ p
decode9-encode9 (T₀ , T₀) = refl
decode9-encode9 (T₀ , T₁) = refl
decode9-encode9 (T₀ , T₂) = refl
decode9-encode9 (T₁ , T₀) = refl
decode9-encode9 (T₁ , T₁) = refl
decode9-encode9 (T₁ , T₂) = refl
decode9-encode9 (T₂ , T₀) = refl
decode9-encode9 (T₂ , T₁) = refl
decode9-encode9 (T₂ , T₂) = refl

{-# REWRITE decode9-encode9 #-}

encode9-injective : ∀ {p q : GF3²} → encode9 p ≡ encode9 q → p ≡ q
encode9-injective {p} {q} eq =
  trans (sym (decode9-encode9 p)) (trans (cong decode9 eq) (decode9-encode9 q))

decode9-injective : ∀ {i j : Fin 9} → decode9 i ≡ decode9 j → i ≡ j
decode9-injective {i} {j} eq =
  trans (sym (encode9-decode9 i)) (trans (cong encode9 eq) (encode9-decode9 j))

-- compress/expand: punchOut/punchIn 的本地定义 (自包含, 不依赖 stdlib punchOut)
-- 关键: 将 {n} 写为 LHS 显式参数, 使用 Data.Nat.zero/suc 消除与 Fin.zero/suc 的歧义
compress : {n : ℕ} → (k : Fin (ℕ.suc n)) → (j : Fin (ℕ.suc n)) → k ≢ j → Fin n
compress {Data.Nat.zero}  zero    zero    k≢j = ⊥-elim (k≢j refl)  -- n=0: Fin 1 只有 zero, k≢j 不可能
compress {Data.Nat.suc n} zero    zero    k≢j = ⊥-elim (k≢j refl)
compress {Data.Nat.suc n} zero    (suc j) _    = j
compress {Data.Nat.suc n} (suc k) zero    _    = zero
compress {Data.Nat.suc n} (suc k) (suc j) k≢j = suc (compress {n} k j (k≢j ∘ cong suc))

expand : {n : ℕ} → (k : Fin (ℕ.suc n)) → Fin n → Fin (ℕ.suc n)
expand {Data.Nat.zero}  zero    ()                       -- n=0: Fin 0 无元素
expand {Data.Nat.suc n} zero    j     = suc j
expand {Data.Nat.suc n} (suc k) zero  = zero
expand {Data.Nat.suc n} (suc k) (suc j) = suc (expand {n} k j)

expand∘compress : {n : ℕ} → (k : Fin (ℕ.suc n)) → (j : Fin (ℕ.suc n)) → (k≢j : k ≢ j) → expand k (compress k j k≢j) ≡ j
expand∘compress {Data.Nat.zero}  zero    zero    k≢j = ⊥-elim (k≢j refl)  -- n=0: 不可能
expand∘compress {Data.Nat.suc n} zero    zero    k≢j = ⊥-elim (k≢j refl)
expand∘compress {Data.Nat.suc n} zero    (suc j) _    = refl
expand∘compress {Data.Nat.suc n} (suc k) zero    _    = refl
expand∘compress {Data.Nat.suc n} (suc k) (suc j) k≢j = cong suc (expand∘compress {n} k j (k≢j ∘ cong suc))

--------------------------------------------------------------------------------
-- 4c. 构造性 nine-miss (标准库 pigeonhole, 0 postulate)
--
-- 策略: Fin 9 → Fin 8 编码 + pigeonhole 碰撞 + injectivity 矛盾
-- 标准库 Data.Fin.Properties.pigeonhole 已在 FiniteDynamics.agda 等模块使用
--------------------------------------------------------------------------------

-- pigeonhole 包装: Fin 9 → Fin 8 → 碰撞对
pigeonhole-9→8 : (f : Fin 9 → Fin 8) → Σ (Fin 9) (λ i → Σ (Fin 9) (λ j → i ≢ j × f i ≡ f j))
pigeonhole-9→8 f =
  let (i , (j , (i<j , fi≡fj))) = pigeonhole (n<1+n 8) f
  in  (i , (j , (≢-from-< i<j , fi≡fj)))
  where
    ≢-from-< : {i j : Fin 9} → toℕ i < toℕ j → i ≢ j
    ≢-from-< i<j eq rewrite eq = <-irrefl refl i<j

-- 核心引理: 单射 + 全部 miss → 矛盾
-- 9 个单射像从 8 点补集中取 → pigeonhole 碰撞 → 矛盾
nine-miss-⊥ : ∀ (F : GF3² → GF3²) → Inj2 F → ∀ q →
    F (T₀ , T₀) ≢ q → F (T₀ , T₁) ≢ q → F (T₀ , T₂) ≢ q →
    F (T₁ , T₀) ≢ q → F (T₁ , T₁) ≢ q → F (T₁ , T₂) ≢ q →
    F (T₂ , T₀) ≢ q → F (T₂ , T₁) ≢ q → F (T₂ , T₂) ≢ q →
    ⊥
nine-miss-⊥ F inj q n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ =
  contradiction
  where
    miss : (idx : Fin 9) → F (decode9 idx) ≢ q
    miss zero                                           = n₀
    miss (suc zero)                                     = n₁
    miss (suc (suc zero))                               = n₂
    miss (suc (suc (suc zero)))                         = n₃
    miss (suc (suc (suc (suc zero))))                   = n₄
    miss (suc (suc (suc (suc (suc zero)))))             = n₅
    miss (suc (suc (suc (suc (suc (suc zero))))))       = n₆
    miss (suc (suc (suc (suc (suc (suc (suc zero))))))) = n₇
    miss (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = n₈

    k : Fin 9
    k = encode9 q

    ne-k : (idx : Fin 9) → k ≢ encode9 (F (decode9 idx))
    ne-k idx eq = miss idx (sym (encode9-injective eq))

    g : Fin 9 → Fin 8
    g idx = compress k (encode9 (F (decode9 idx))) (ne-k idx)

    contradiction : ⊥
    contradiction with pigeonhole-9→8 g
    ... | (i , (j , (i≢j , gi≡gj))) =
      i≢j (decode9-injective (inj Fi≡Fj))
      where
        Fi≡Fj : F (decode9 i) ≡ F (decode9 j)
        Fi≡Fj = encode9-injective
          (trans (sym (expand∘compress k (encode9 (F (decode9 i))) (ne-k i)))
          (trans (cong (expand k) gi≡gj)
                 (expand∘compress k (encode9 (F (decode9 j))) (ne-k j))))

-- GF(3)² 鸽巢: 单射 ⟹ 满射
pigeonhole-2 : ∀ F → Inj2 F → Surj2 F
pigeonhole-2 F inj q with F (T₀ , T₀) ≟² q
... | yes e = (T₀ , T₀) , e
... | no n₀ with F (T₀ , T₁) ≟² q
... | yes e = (T₀ , T₁) , e
... | no n₁ with F (T₀ , T₂) ≟² q
... | yes e = (T₀ , T₂) , e
... | no n₂ with F (T₁ , T₀) ≟² q
... | yes e = (T₁ , T₀) , e
... | no n₃ with F (T₁ , T₁) ≟² q
... | yes e = (T₁ , T₁) , e
... | no n₄ with F (T₁ , T₂) ≟² q
... | yes e = (T₁ , T₂) , e
... | no n₅ with F (T₂ , T₀) ≟² q
... | yes e = (T₂ , T₀) , e
... | no n₆ with F (T₂ , T₁) ≟² q
... | yes e = (T₂ , T₁) , e
... | no n₇ with F (T₂ , T₂) ≟² q
... | yes e = (T₂ , T₂) , e
... | no n₈ = ⊥-elim (nine-miss-⊥ F inj q n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈)
