{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- | Sovereign.Problem.Sqrt2.Sqrt2Valuation
-- 方案 B：√2 无理性的 2-adic 赋值（指数/对数）版证明
--
-- 数学背景:
--   赋值 v₂（"整除性的对数"）: n = 2^k·u（u 奇）时 k = v₂(n)。
--   v₂(x²) = 2·v₂(x) 恒偶，而 v₂(2) = 1 奇 —— 指数奇偶性矛盾。
--   本模块不定义 v₂ 函数：对 a、b 各提取分解 n = two^ k u（u 奇），
--   平方后 LHS 指数 k+k 为偶、RHS 指数 1+(j+j) 为奇，
--   用指数二分 + 剥层引理（strip-lt）收矛盾。
--   与 Sqrt2Irrational 的无穷递降互为替代证明：此处不递降，
--   用的是"指数的奇偶性"（对数 parity）。
--
-- 依赖: Sovereign.Problem.Sqrt2.Sqrt2Irrational（自建模块，只读导入，
--   复用 parity/Odd/odd-square/¬dub-sucdub/dub-inj/≤ 工具箱）；0 postulate。
------------------------------------------------------------------------

module Sovereign.Problem.Sqrt2.Sqrt2Valuation where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Sovereign.Problem.Sqrt2.Sqrt2Irrational

------------------------------------------------------------------------
-- 2 的幂（dub 迭代）：two^ k u 读作 2^k·u

two^ : Nat → Nat → Nat
two^ zero    u = u
two^ (suc k) u = dub (two^ k u)

------------------------------------------------------------------------
-- L1 平方提取: (two^ k u)² ≡ two^ (k + k) (u²)
--    指数翻倍 = "对数翻倍"

sq-two^ : ∀ k u → (two^ k u) * (two^ k u) ≡ two^ (k + k) (u * u)
sq-two^ zero    u = refl
sq-two^ (suc k) u =
  trans (*-dub² (two^ k u))
  (trans (cong dub (cong dub (sq-two^ k u)))
         (cong dub (cong (λ e → two^ e (u * u)) (sym (+-suc k k)))))

------------------------------------------------------------------------
-- L2 分裂: two^ (m + r) u ≡ two^ m (two^ r u)

two^-split : ∀ m r u → two^ (m + r) u ≡ two^ m (two^ r u)
two^-split zero    r u = refl
two^-split (suc m) r u = cong dub (two^-split m r u)

------------------------------------------------------------------------
-- L2b 同深度单射: two^ m X ≡ two^ m Y → X ≡ Y（m 层 dub-inj）

two^-inj : ∀ m X Y → two^ m X ≡ two^ m Y → X ≡ Y
two^-inj zero    X Y e = e
two^-inj (suc m) X Y e = two^-inj m X Y (dub-inj (two^ m X) (two^ m Y) e)

------------------------------------------------------------------------
-- L3 奇数平方为奇（方程形与谓词形）

odd-sq : ∀ u → Odd u → Σ Nat (λ t → u * u ≡ suc (dub t))
odd-sq u (odd k ek) =
  proj₁ (odd-square k) ,
  trans (cong (λ z → z * z) ek) (proj₂ (odd-square k))

odd-sq-odd : ∀ u → Odd u → Odd (u * u)
odd-sq-odd u (odd k ek) =
  odd (proj₁ (odd-square k))
      (trans (cong (λ z → z * z) ek) (proj₂ (odd-square k)))

------------------------------------------------------------------------
-- L4 剥层引理: LHS 是 two^ m 奇核，RHS 在同深度多一个 2 因子 → 矛盾
--    （归纳剥 m 层后奇撞偶）

strip-lt : ∀ m r X Y → Odd X
  → two^ m X ≡ dub (two^ (m + r) Y)
  → ⊥
strip-lt zero    r X Y (odd k ek) e =
  ¬dub-sucdub (two^ (zero + r) Y) k (trans (sym e) ek)
strip-lt (suc m) r X Y (odd k ek) e =
  strip-lt m r X Y (odd k ek)
    (dub-inj (two^ m X) (two^ (suc m + r) Y) e)

------------------------------------------------------------------------
-- L5 指数二分与差提取

≤-dich : ∀ m n → m ≤ n ⊎ suc n ≤ m
≤-dich zero    n       = inj₁ z≤n
≤-dich (suc m) zero    = inj₂ (s≤s z≤n)
≤-dich (suc m) (suc n) with ≤-dich m n
...   | inj₁ p = inj₁ (s≤s p)
...   | inj₂ p = inj₂ (s≤s p)

≤→diff : ∀ m n → m ≤ n → Σ Nat (λ r → n ≡ m + r)
≤→diff zero    n      z≤n     = n , refl
≤→diff (suc m) (suc n) (s≤s p) with ≤→diff m n p
...   | (r , eq) = r , cong suc eq

------------------------------------------------------------------------
-- L4b 偶指数 ≠ 奇指数（奇偶提取的前置）

kk≢sucjj : ∀ k j → k + k ≢ suc (j + j)
kk≢sucjj zero    j        eq = zero≠suc eq
kk≢sucjj (suc k') zero    eq = zero≠suc (trans (sym (suc-inj eq)) (+-suc k' k'))
kk≢sucjj (suc k') (suc j') eq =
  kk≢sucjj k' j'
    (trans (suc-inj (trans (sym (+-suc k' k')) (suc-inj eq)))
           (+-suc j' j'))

------------------------------------------------------------------------
-- 主引理: LHS 指数 k+k（偶）对 RHS 指数 suc (j+j)（奇）—— 三分律收矛盾

no-root : ∀ k j u v → Odd u → Odd v
  → two^ (k + k) (u * u) ≡ two^ (suc (j + j)) (v * v)
  → ⊥
no-root k j u v ou ov e with ≤-dich (k + k) (j + j)
no-root k j u v ou ov e | inj₁ kk≤jj with ≤→diff (k + k) (j + j) kk≤jj
no-root k j u v ou ov e | inj₁ kk≤jj | (r , rj) =
  strip-lt (k + k) r (u * u) (v * v) (odd-sq-odd u ou)
    (trans e (cong (λ e' → two^ (suc e') (v * v)) rj))
no-root k j u v ou ov e | inj₂ s≤ with ≤→diff (suc (j + j)) (k + k) s≤
no-root k j u v ou ov e | inj₂ s≤ | (r , rk) with r
no-root k j u v ou ov e | inj₂ s≤ | (r , rk) | zero =
  kk≢sucjj k j (trans rk (cong suc (+-zeroʳ (j + j))))
no-root k j u v ou ov e | inj₂ s≤ | (r , rk) | suc r' =
  let eq-common : two^ (suc (j + j)) (v * v) ≡ two^ (suc (j + j)) (two^ (suc r') (u * u))
      eq-common = trans (sym e)
        (trans (cong (λ e' → two^ e' (u * u)) rk)
               (two^-split (suc (j + j)) (suc r') (u * u)))
      eqv : v * v ≡ two^ (suc r') (u * u)
      eqv = two^-inj (suc (j + j)) (v * v) (two^ (suc r') (u * u)) eq-common
  in ¬dub-sucdub (two^ r' (u * u)) (proj₁ (odd-sq v ov))
       (trans (sym eqv) (proj₂ (odd-sq v ov)))

------------------------------------------------------------------------
-- 分解存在性（对数提取）: 非零 n 可写成 two^ k u 且 u 奇
--   递降-free: 对 n 的 ≤-强化结构归纳，偶数情形剥一层 two^

≤-substˡ : ∀ {a b c : Nat} → a ≡ b → a ≤ c → b ≤ c
≤-substˡ refl p = p

≤-suc+ : ∀ x y → suc x ≤ x + suc y
≤-suc+ zero    y = s≤s z≤n
≤-suc+ (suc x) y = s≤s (≤-suc+ x y)

dub≤→≤ : ∀ w n → dub w ≤ suc n → w ≤ n
dub≤→≤ zero    n _  = z≤n
dub≤→≤ (suc w') n p = ≤-trans (≤-suc+ w' w') (≤-inv p)

decomp≤ : ∀ n m → m ≤ n → m ≢ zero
  → Σ Nat (λ k → Σ Nat (λ u → Σ (m ≡ two^ k u) (λ _ → Odd u)))
decomp≤ zero    m m≤n m≠0 = ⊥-elim (m≠0 (≤-zero m m≤n))
decomp≤ (suc n) m m≤n m≠0 with parity m
... | inj₂ om = zero , m , refl , om
... | inj₁ (even w em) with decomp≤ n w (dub≤→≤ w n (≤-substˡ em m≤n))
                               (λ we → m≠0 (trans em (cong dub we)))
...   | (k , u , eqw , ou) = suc k , u , trans em (cong dub eqw) , ou

decomp : ∀ n → n ≢ zero
  → Σ Nat (λ k → Σ Nat (λ u → Σ (n ≡ two^ k u) (λ _ → Odd u)))
decomp n n≠0 = decomp≤ n n (≤-refl n) n≠0

------------------------------------------------------------------------
-- 定理（赋值版）: ∀ a b : ℕ, b ≢ 0 → a² ≢ 2·b²
--   把 a、b 各自分解为 2 的幂 × 奇数，代入方程后由 no-root 收尾。
--   与 Sqrt2Irrational.sqrt2-pair-absurd 同一陈述，不同的证明。

a≠0-of : ∀ (a b : Nat) → b ≢ zero → a * a ≡ dub (b * b) → a ≢ zero
a≠0-of a b b≠0 eq ae =
  b≠0 (sq-zero b (dub-zero (b * b) (trans (sym eq) (cong (λ z → z * z) ae))))

sqrt2-irrational-valuation : ∀ (a b : Nat) → b ≢ zero → a * a ≡ dub (b * b) → ⊥
sqrt2-irrational-valuation a b b≠0 eq
  with decomp a (a≠0-of a b b≠0 eq) | decomp b b≠0
... | (ka , ua , ea , ou) | (kb , vb , eb , ov) =
  no-root ka kb ua vb ou ov
    (trans (sym (sq-two^ ka ua))
    (trans (sym (cong (λ z → z * z) ea))
    (trans eq
    (cong dub (trans (cong (λ z → z * z) eb) (sq-two^ kb vb))))))
