------------------------------------------------------------------------
-- | Sovereign.Application.Problems.RH.NoNormT0Even
-- t = 0 投影域失配反例 — 完整形式化证明（0 postulate / 0 hole）
--
-- 数学背景:
--   Weil 刚性范数方程 t² + 3s² = 4·3ⁿ 在 t = 0 时退化为 3s² = 4·3ⁿ，
--   即 s² = 4·3ⁿ⁻¹。当 n−1 为奇数（n 偶）时 RHS 的 3-adic 赋值为奇，
--   平方赋值必偶 —— 无整数解。
--   与 Lean 侧 no_norm_t0_even : ¬∃s, 3s² = 4·3^(2k) 同型。
--   几何含义：这类 (t=0, 偶扩张) 曲线的 Frobenius 特征值
--   π = ±3^{n/2}·i 落在 ℚ(i) —— 不在 ℚ(√−3) = ℤ[ω] 分式域内，
--   即「投影域失配」：刚性形式 t²+3s²=4q 的适用域是 CM 域 ℚ(√−3)。
--
-- 证法（3-adic 无穷递降，Sqrt2Irrational 骨架的 3-adic 移植）:
--   · 三分剩余视图 Res0/Res1/Res2（带证据）：任何 s 是 3k / 3k+1 / 3k+2。
--   · Res1/Res2 平方 = 1 + 3·(...)（suc-tri-sq / suc2-tri-sq），
--     而 RHS = 3·(...)（rhs-tri）—— ¬tri-suc 直接矛盾。
--   · Res0（s = 3a）：s² = 3·(3a²)，方程两边剥两层 3（tri-inj）
--     得 a² = 4·3ⁿ⁻² —— 同型小解，对指数结构归纳闭合。
--
-- 自包含：仅依赖 Agda 内建（Nat、_≡_），与 fork stdlib 无耦合。
-- 零 postulate、零 hole。
-- 辅助层放在子模块 NoNormPrelude 内（不 public 重导出）：通用名（⊥ / ¬ / cong / sym / trans /
-- +-comm / *-comm / pow3 / tri …）不进入库的扁平命名空间，避免与其他模块的顶层名重复。
--
-- 主定理（ℕ 层）: no-sq-4pow3-odd : ∀ m s → s·s ≢ 4·3^(2m+1)
-- 主定理（ℤ 层）: no-norm-t0-even : ∀ m → ¬∃ s:ℤ, 3·s² = 4·3^(2m+2)
------------------------------------------------------------------------

module Sovereign.Application.Problems.RH.NoNormT0Even where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)


-- ── 辅助层（逻辑工具 + ℕ 算术）。子模块、不 public 重导出，理由见文件头 ──
module NoNormPrelude where
  ------------------------------------------------------------------------
  -- 逻辑工具（自包含，同 Sqrt2Irrational 范式）

  data ⊥ : Set where

  ⊥-elim : ∀ {A : Set} → ⊥ → A
  ⊥-elim ()

  ¬ : Set → Set
  ¬ A = A → ⊥

  data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  open Σ public

  infixr 1 _⊎_
  infixr 4 _,_

  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl eq = eq

  suc-inj : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  -- 不声明结合级时默认优先级高于 _*_，会把 `s * s ≢ 4 * …` 解析成 `s * (s ≢ 4) * …`
  infix 4 _≢_

  zero≠suc : ∀ {n : Nat} → zero ≡ suc n → ⊥
  zero≠suc ()

  ------------------------------------------------------------------------
  -- 算术引理（builtin 语义：+ 与 * 均对第一参数递归）

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-zeroʳ : ∀ n → n + zero ≡ n
  +-zeroʳ zero    = refl
  +-zeroʳ (suc n) = cong suc (+-zeroʳ n)

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm zero    n = sym (+-zeroʳ n)
  +-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc zero    b c = refl
  +-assoc (suc a) b c = cong suc (+-assoc a b c)

  +-swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
  +-swap a b c =
    trans (sym (+-assoc a b c))
      (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

  *-zeroʳ : ∀ n → n * zero ≡ zero
  *-zeroʳ zero    = refl
  *-zeroʳ (suc n) = *-zeroʳ n

  *-suc : ∀ m n → m * suc n ≡ m + m * n
  *-suc zero    n = refl
  *-suc (suc m) n =
    cong suc (trans (cong (n +_) (*-suc m n)) (+-swap n m (m * n)))

  *-comm : ∀ m n → m * n ≡ n * m
  *-comm zero    n = sym (*-zeroʳ n)
  *-comm (suc m) n = trans (cong (n +_) (*-comm m n)) (sym (*-suc n m))

  *-distribˡ : ∀ a b c → (a + b) * c ≡ a * c + b * c
  *-distribˡ zero    b c = refl
  *-distribˡ (suc a) b c =
    trans (cong (c +_) (*-distribˡ a b c)) (sym (+-assoc c (a * c) (b * c)))

  *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
  *-assoc zero    b c = refl
  *-assoc (suc a) b c =
    trans (*-distribˡ b (a * b) c) (cong (b * c +_) (*-assoc a b c))

  ------------------------------------------------------------------------
  -- 翻倍与三倍

  dub : Nat → Nat
  dub n = n + n

  dub-suc : ∀ m → dub (suc m) ≡ suc (suc (dub m))
  dub-suc m = cong suc (+-suc m m)

  tri : Nat → Nat
  tri n = 3 * n

  -- 3·(suc k) = suc³(3·k)
  --   定义范式（builtin 乘法对第一参递归）：
  --   3 * suc k = suc k + (suc k + (suc k + zero))
  --   3 * k     = k + (k + (k + zero))      （当 k 是 suc _ 时；变量 k 时同范式）
  --   三步 +-suc 把 suc 拉到最前。
  tri-step : ∀ k → tri (suc k) ≡ suc (suc (suc (tri k)))
  tri-step k =
    trans (cong suc (+-suc k (k + suc (k + zero))))
          (cong (λ z → suc (suc z)) inside)
    where
    inside : k + (k + suc (k + zero)) ≡ suc (k + (k + (k + zero)))
    inside = trans (cong (λ z → k + z) (+-suc k (k + zero)))
                   (+-suc k (k + (k + zero)))

  tri-inj : ∀ x y → tri x ≡ tri y → x ≡ y
  tri-inj zero    zero    e   = refl
  tri-inj zero    (suc y) e   = ⊥-elim (zero≠suc (trans e (tri-step y)))
  tri-inj (suc x) zero    e   =
    ⊥-elim (zero≠suc (sym (trans (sym (tri-step x)) e)))
  tri-inj (suc x) (suc y) e =
    cong suc (tri-inj x y
      (suc-inj (suc-inj (suc-inj
        (trans (sym (tri-step x)) (trans e (tri-step y)))))))

  ------------------------------------------------------------------------
  -- 三分剩余视图（带证据）：s = 3k / 3k+1 / 3k+2

  data Res0 (n : Nat) : Set where
    r0 : (k : Nat) → n ≡ tri k → Res0 n

  data Res1 (n : Nat) : Set where
    r1 : (k : Nat) → n ≡ suc (tri k) → Res1 n

  data Res2 (n : Nat) : Set where
    r2 : (k : Nat) → n ≡ suc (suc (tri k)) → Res2 n

  tri3 : ∀ n → Res0 n ⊎ (Res1 n ⊎ Res2 n)
  tri3 zero    = inj₁ (r0 zero refl)
  tri3 (suc n) with tri3 n
  ... | inj₁ (r0 k e)         = inj₂ (inj₁ (r1 k (cong suc e)))
  ... | inj₂ (inj₁ (r1 k e))  = inj₂ (inj₂ (r2 k (cong suc e)))
  ... | inj₂ (inj₂ (r2 k e))  =
        inj₁ (r0 (suc k) (trans (cong suc e) (sym (tri-step k))))

  nz : ∀ y → y ≡ zero ⊎ Σ Nat (λ y' → y ≡ suc y')
  nz zero    = inj₁ refl
  nz (suc y) = inj₂ (y , refl)

  ------------------------------------------------------------------------
  -- mod-3 核心矛盾：3x ≢ 1 + 3y，即 tri x ≢ suc (tri y)

  ¬tri-suc : ∀ x y → tri x ≡ suc (tri y) → ⊥
  ¬tri-suc zero    y e = zero≠suc e
  ¬tri-suc (suc x) y e with nz y
  ... | inj₁ y≡0 =
    zero≠suc (sym (trans e2 (cong tri y≡0)))
    where
    e2 : suc (suc (tri x)) ≡ tri y
    e2 = suc-inj (trans (sym (tri-step x)) e)
  ... | inj₂ (y' , y≡sy') =
    ¬tri-suc x y' goal
    where
    e2 : suc (suc (tri x)) ≡ tri y
    e2 = suc-inj (trans (sym (tri-step x)) e)
    e3 : suc (suc (tri x)) ≡ tri (suc y')
    e3 = trans e2 (cong tri y≡sy')
    goal : tri x ≡ suc (tri y')
    goal = suc-inj (suc-inj (trans e3 (tri-step y')))

  ------------------------------------------------------------------------
  -- 3 的幂与 RHS 的 tri 形状

  pow3 : Nat → Nat
  pow3 zero    = suc zero
  pow3 (suc e) = 3 * pow3 e

  -- 4·3^(e+1) = 3·(4·3^e)
  rhs-tri : ∀ e → 4 * pow3 (suc e) ≡ tri (4 * pow3 e)
  rhs-tri e =
    trans (sym (*-assoc 4 3 (pow3 e)))
      (trans (cong (_* pow3 e) (*-comm 4 3))
             (*-assoc 3 4 (pow3 e)))

  ------------------------------------------------------------------------
  -- 平方的剩余类计算

  tri-distr : ∀ a b → tri (a + b) ≡ tri a + tri b
  tri-distr a b =
    trans (*-comm 3 (a + b))
      (trans (*-distribˡ a b 3)
        (trans (cong (λ z → a * 3 + z) (*-comm b 3))
               (cong (λ z → z + 3 * b) (*-comm a 3))))

  -- (3a)² = 3·(3a²)
  tri-sq : ∀ a → tri a * tri a ≡ tri (tri (a * a))
  tri-sq a =
    trans (*-assoc 3 a (tri a))
      (cong (3 *_)
        (trans (sym (*-assoc a 3 a))
          (trans (cong (_* a) (*-comm a 3))
                 (*-assoc 3 a a))))

  -- (1+x)² = 1 + (x + (x + x²))
  suc*-sq : ∀ x → suc x * suc x ≡ suc (x + (x + x * x))
  suc*-sq x =
    trans (*-suc (suc x) x)
      (cong (λ y → suc x + y)
        (trans (*-comm (suc x) x) (*-suc x x)))

  -- (3k+1)² = 1 + 3·(3k² + 2k)
  suc-tri-sq : ∀ k → suc (tri k) * suc (tri k)
              ≡ suc (tri (k + (k + tri (k * k))))
  suc-tri-sq k =
    trans (suc*-sq (tri k)) (cong suc body)
    where
    body : tri k + (tri k + tri k * tri k) ≡ tri (k + (k + tri (k * k)))
    body = trans step1 (trans step2 step3)
      where
      step1 : tri k + (tri k + tri k * tri k) ≡ tri k + (tri k + tri (tri (k * k)))
      step1 = cong (λ z → tri k + (tri k + z)) (tri-sq k)
      step2 : tri k + (tri k + tri (tri (k * k))) ≡ tri k + tri (k + tri (k * k))
      step2 = cong (λ z → tri k + z) (sym (tri-distr k (tri (k * k))))
      step3 : tri k + tri (k + tri (k * k)) ≡ tri (k + (k + tri (k * k)))
      step3 = sym (tri-distr k (k + tri (k * k)))

  pull2 : ∀ p q x → p + (q + x) ≡ x + (p + q)
  pull2 p q x = trans (sym (+-assoc p q x)) (+-comm (p + q) x)

  pull4 : ∀ a b c d x → a + (b + (c + (d + x))) ≡ x + (a + (b + (c + d)))
  pull4 a b c d x =
    trans (cong (a +_) (cong (b +_) (pull2 c d x)))
      (trans (cong (a +_) (+-swap b x (c + d)))
             (+-swap a x (b + (c + d))))

  -- (3k+2)² = 1 + 3·(3k² + 4k + 1)
  suc2-tri-sq : ∀ k → suc (suc (tri k)) * suc (suc (tri k))
              ≡ suc (tri (suc (tri (k * k) + (k + (k + (k + k))))))
  suc2-tri-sq k =
    trans (suc*-sq (suc (tri k)))
      (trans (cong suc body3) c3)
    where
    X : Nat
    X = tri (tri (k * k))

    s1 : suc (tri k) * suc (tri k) ≡ suc (tri (k + (k + tri (k * k))))
    s1 = suc-tri-sq k

    s2 : suc (tri k) + suc (tri k) * suc (tri k)
       ≡ suc (suc (tri k + tri (k + (k + tri (k * k)))))
    s2 = trans (cong (suc (tri k) +_) s1)
           (cong suc (+-suc (tri k) (tri (k + (k + tri (k * k))))))

    s3 : suc (tri k) + (suc (tri k) + suc (tri k) * suc (tri k))
       ≡ suc (suc (suc (tri k + (tri k + tri (k + (k + tri (k * k)))))))
    s3 =
      trans (cong (suc (tri k) +_) s2)
        (trans (cong suc (+-suc (tri k)
                  (suc (tri k + tri (k + (k + tri (k * k)))))))
               (cong (λ z → suc (suc z))
                 (+-suc (tri k) (tri k + tri (k + (k + tri (k * k)))))))

    s4 : tri (k + (k + tri (k * k)))
       ≡ tri k + (tri k + X)
    s4 = trans (tri-distr k (k + tri (k * k)))
             (cong (tri k +_) (tri-distr k (tri (k * k))))

    body3 : suc (tri k) + (suc (tri k) + suc (tri k) * suc (tri k))
         ≡ suc (suc (suc (tri k + (tri k + (tri k + (tri k + X))))))
    body3 =
      trans s3
        (cong (λ z → suc (suc (suc (tri k + (tri k + z))))) s4)

    triV : tri (suc (tri (k * k) + (k + (k + (k + k)))))
        ≡ suc (suc (suc (X + (tri k + (tri k + (tri k + tri k))))))
    triV =
      trans (tri-step (tri (k * k) + (k + (k + (k + k)))))
        (cong (λ z → suc (suc (suc z)))
          (trans (tri-distr (tri (k * k)) (k + (k + (k + k))))
            (cong (X +_)
              (trans (tri-distr k (k + (k + k)))
                (cong (tri k +_)
                  (trans (tri-distr k (k + k))
                         (cong (tri k +_) (tri-distr k k))))))))

    c3 : suc (suc (suc (suc (tri k + (tri k + (tri k + (tri k + X)))))))
      ≡ suc (tri (suc (tri (k * k) + (k + (k + (k + k))))))
    c3 =
      trans (cong (λ z → suc (suc (suc (suc z))))
                    (pull4 (tri k) (tri k) (tri k) (tri k) X))
            (cong suc (sym triV))

open NoNormPrelude

------------------------------------------------------------------------
-- 主定理（ℕ 层）：s² = 4·3^(2m+1) 无自然数解
--   （2m+1 为奇指数 —— 平方的 3-adic 赋值必偶，矛盾）

no-sq-4pow3-odd : ∀ (m : Nat) (s : Nat) → s * s ≢ 4 * pow3 (suc (dub m))
no-sq-4pow3-odd zero s e with tri3 s
... | inj₁ (r0 a s≡) =
  ¬tri-suc (a * a) 1
    (tri-inj (tri (a * a)) 4
      (trans (sym sq) (trans e (rhs-tri zero))))
  where
  sq : s * s ≡ tri (tri (a * a))
  sq = trans (cong (λ z → z * z) s≡) (tri-sq a)
... | inj₂ (inj₁ (r1 k s≡)) =
  ¬tri-suc 4 (k + (k + tri (k * k)))
    (sym (trans (sym (trans (cong (λ z → z * z) s≡) (suc-tri-sq k)))
                (trans e (rhs-tri zero))))
... | inj₂ (inj₂ (r2 k s≡)) =
  ¬tri-suc 4 (suc (tri (k * k) + (k + (k + (k + k)))))
    (sym (trans (sym (trans (cong (λ z → z * z) s≡) (suc2-tri-sq k)))
                (trans e (rhs-tri zero))))
no-sq-4pow3-odd (suc m) s e with tri3 s
... | inj₁ (r0 a s≡) =
  no-sq-4pow3-odd m a
    (tri-inj (a * a) (4 * pow3 (suc (dub m)))
      (tri-inj (tri (a * a)) (tri (4 * pow3 (suc (dub m))))
        (trans (sym sq)
          (trans e
            (trans (cong (λ z → 4 * pow3 (suc z)) (dub-suc m))
              (trans (rhs-tri (suc (suc (dub m))))
                     (cong tri (rhs-tri (suc (dub m))))))))))
  where
  sq : s * s ≡ tri (tri (a * a))
  sq = trans (cong (λ z → z * z) s≡) (tri-sq a)
... | inj₂ (inj₁ (r1 k s≡)) =
  ¬tri-suc (4 * pow3 (suc (suc (dub m)))) (k + (k + tri (k * k)))
    (sym (trans (sym (trans (cong (λ z → z * z) s≡) (suc-tri-sq k)))
                (trans e
                  (trans (cong (λ z → 4 * pow3 (suc z)) (dub-suc m))
                         (rhs-tri (suc (suc (dub m))))))))
... | inj₂ (inj₂ (r2 k s≡)) =
  ¬tri-suc (4 * pow3 (suc (suc (dub m))))
    (suc (tri (k * k) + (k + (k + (k + k)))))
    (sym (trans (sym (trans (cong (λ z → z * z) s≡) (suc2-tri-sq k)))
                (trans e
                  (trans (cong (λ z → 4 * pow3 (suc z)) (dub-suc m))
                         (rhs-tri (suc (suc (dub m))))))))

------------------------------------------------------------------------
-- ℤ 层（自包含极简整数，只需正负两态与乘法）

data ℤ : Set where
  +_     : Nat → ℤ
  -[1+_] : Nat → ℤ

infixl 7 _*ℤ_

_*ℤ_ : ℤ → ℤ → ℤ
(+ a)       *ℤ (+ b)       = + (a * b)
(+ zero)    *ℤ (-[1+ b ])  = + zero
(+ suc a)   *ℤ (-[1+ b ])  = -[1+ (a + suc a * b) ]
(-[1+ a ])  *ℤ (+ zero)    = + zero
(-[1+ a ])  *ℤ (+ suc b)   = -[1+ (a + suc a * b) ]   -- −(a+1)(b+1) = −(1 + ab + a + b)
(-[1+ a ])  *ℤ (-[1+ b ])  = + (suc a * suc b)

ℤpow3 : Nat → ℤ
ℤpow3 e = + (pow3 e)

posInj : ∀ a b → (+ a ≡ + b) → a ≡ b
posInj a b refl = refl

-- ℤ 层主定理（Lean 侧 no_norm_t0_even 对应，偶指数 2m+2）：
--   t = 0、q = 3^(2m+2) 时 3·s² = 4·3^(2m+2) 无整数解
--   3·|s|² = 4·3^(2m+2) ⇒ |s|² = 4·3^(2m+1)（剥一层 3，rhs-tri + tri-inj）
no-norm-t0-even : ∀ (m : Nat) →
  ¬ (Σ ℤ (λ s → (+ 3) *ℤ (s *ℤ s) ≡ (+ 4) *ℤ ℤpow3 (suc (suc (dub m)))))
no-norm-t0-even m ((+ n) , eq) =
  peel n (posInj _ _ eq)
  where
  peel : ∀ n → 3 * (n * n) ≡ 4 * pow3 (suc (suc (dub m))) → ⊥
  peel n h = no-sq-4pow3-odd m n
    (tri-inj (n * n) (4 * pow3 (suc (dub m)))
      (trans h (rhs-tri (suc (dub m)))))
no-norm-t0-even m ((-[1+ n ]) , eq) =
  peel n (posInj _ _ eq)
  where
  peel : ∀ n → 3 * (suc n * suc n) ≡ 4 * pow3 (suc (suc (dub m))) → ⊥
  peel n h = no-sq-4pow3-odd m (suc n)
    (tri-inj (suc n * suc n) (4 * pow3 (suc (dub m)))
      (trans h (rhs-tri (suc (dub m)))))

-- GF(9) 实例（WeilRigidity 轨道的 t=0 投影失配）：3s² = 36 无整数解
no-norm-t0-q9 :
  ¬ (Σ ℤ (λ s → (+ 3) *ℤ (s *ℤ s) ≡ (+ 4) *ℤ ℤpow3 (suc (suc (dub zero)))))
no-norm-t0-q9 = no-norm-t0-even zero
