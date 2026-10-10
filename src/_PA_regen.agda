{-# OPTIONS --cubical --guardedness #-}

-- | _PA_regen（事故回收探针——第一代三件重建）
--
-- 数学背景：ℤ[t,t⁻¹] 函数表示（LaurentCubical）的三组基础件：
--   A. mono 卷积引理（两单项式卷积 = 单项式 c·d·t^(n+m)）
--   B. t·t⁻¹ ≡ 1 家族（含 tneg = -t ≠ t⁻¹ 的反证 tneg-goal-false）
--   C. grow/dist 基础件（窗口零扩 + 逐项分配 + ℤ/+pos 桥）
--
-- 核心原则：
--   1. 零洞零 postulate；∙ 链 ≤3；具名拆分；where 有序（禁前向引用）
--   2. 禁碰「字面头+stuck 尾」（字面剥 suc 链爆点）
--   3. 真二元加一律写 `+ (pos …)` 括号形（空格算符陷阱：`x + pos n` 解析为 `x +pos n`）
--   4. Nat/Int 序双库 renaming 消歧（`_<ℕ_`/`_≤ℕ_` vs Int `_<`/`_≤`）
module _PA_regen where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_; subst; subst2; _,_)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Int using (ℤ; pos; negsuc; sucℤ; _+_; _-_; _·_; _+pos_; -_)
open import Cubical.Data.Int.Properties using
  (+Comm; +Assoc; minusPlus; sucℤ+; ·AnnihilR; ·DistL+; pos0+; inj-+z)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc)
open import Cubical.Data.Nat.Order using (suc-≤-suc; ≤-refl) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Cubical.Data.Int.Order using (_<_; _≤_; Trichotomy; lt; eq; gt; isIrrefl<; ≤-+o)
open import Sovereign.Algebra.ProbeArith using (triℤ)
open import Sovereign.Algebra.LaurentCubical using
  (Laurent; sums; mono; mono-coeff; R1; tvar; tneg; _*L_; sum-ℤ; abs)

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = p ∙ q

-- ══════════════════════════════════════════════════════════════════
-- C0. ℤ 基础件（零元 / 判别族 / sucℤ 定义桥）—— A、B、C 共用
-- ══════════════════════════════════════════════════════════════════

-- 右零：x + (pos 0) ≡ x（两构造子叶）
zero-r : ∀ x → x + (pos 0) ≡ x
zero-r (pos n) = refl
zero-r (negsuc n) = refl

-- sucℤ 定义桥（三 refl 叶；括号形真二元加）
sucℤ-def : ∀ z → sucℤ z ≡ z + (pos 1)
sucℤ-def (pos n) = refl
sucℤ-def (negsuc zero) = refl
sucℤ-def (negsuc (suc n)) = refl

-- 判别族：负元不可等于 pos 形（cubical 空模式不认构子相异 → 判别族 + subst tt）
isNeg : ℤ → Set
isNeg (pos _) = ⊥
isNeg (negsuc _) = Unit

neg≢pos0 : negsuc 0 ≡ pos 0 → ⊥
neg≢pos0 e = rec (subst isNeg e tt)

-- ══════════════════════════════════════════════════════════════════
-- A. mono 卷积家族
-- ══════════════════════════════════════════════════════════════════

-- n - n ≡ 0（inj-z+ 消去法；A/B 由其派生）
n∸n : ∀ n → n - n ≡ pos 0
n∸n n = inj-+z {n} {n - n} {pos 0} (trans (minusPlus n n) (pos0+ n))

A : ∀ j → pos (suc j) + negsuc j ≡ pos 0
A j = n∸n (pos (suc j))

B : ∀ k → negsuc k + pos (suc k) ≡ pos 0
B k = n∸n (negsuc k)

abs-n∸n : ∀ n → abs (n - n) ≡ zero
abs-n∸n n = cong abs (n∸n n)

-- mono-coeff 对角线（tri 三叶，lt/gt 归谬）
mono-coeff-eq : ∀ c n → mono-coeff c n n ≡ c
mono-coeff-eq c n with triℤ n n
... | lt x = rec (isIrrefl< x)
... | eq _ = refl
... | gt x = rec (isIrrefl< x)

-- ℤ 桥族
plus-minus-cancel : ∀ n m → (n + m) - n ≡ m
plus-minus-cancel n m = inj-+z {n} {(n + m) - n} {m} (trans (minusPlus n (n + m)) (+Comm n m))

k≡n+m-bridge : ∀ k n m → k - n ≡ m → k ≡ n + m
k≡n+m-bridge k n m e = trans (sym (minusPlus n k)) (trans (cong (λ w → w + n) e) (+Comm m n))

k-n≡m-bridge : ∀ k n m → k ≡ n + m → k - n ≡ m
k-n≡m-bridge k n m e = trans (cong (λ w → w - n) e) (plus-minus-cancel n m)

-- 序桥（≤-+o + sucℤ+ 链；隐式 {o} 命名钉死）
k<n+m-bridge : ∀ k n m → k < n + m → k - n < m
k<n+m-bridge k n m x =
  subst2 _≤_ (sym (sucℤ+ k (- n))) (plus-minus-cancel n m) (≤-+o {o = - n} x)

sucℤn-n : ∀ n → sucℤ n + (- n) ≡ pos 1
sucℤn-n n = trans (cong (λ w → w + (- n)) (sucℤ-def n)) (plus-minus-cancel n (pos 1))

k>n+m-a : ∀ n m → sucℤ (n + m) + (- n) ≡ (sucℤ n + (- n)) + m
k>n+m-a n m =
  trans (cong (λ w → w + (- n)) (sucℤ+ n m))
  (trans (sym (+Assoc (sucℤ n) m (- n)))
  (trans (cong (sucℤ n +_) (+Comm m (- n)))
         (+Assoc (sucℤ n) (- n) m)))

k>n+m-b : ∀ n m → (sucℤ n + (- n)) + m ≡ sucℤ m
k>n+m-b n m =
  trans (cong (λ w → w + m) (sucℤn-n n))
  (trans (+Comm (pos 1) m) (sym (sucℤ-def m)))

k>n+m-bridge : ∀ k n m → n + m < k → m < k - n
k>n+m-bridge k n m x = subst2 _≤_ (trans (k>n+m-a n m) (k>n+m-b n m)) refl (≤-+o {o = - n} x)

-- 归约引理的共享桥族（cross / t·t⁻¹ 家族共用）
irrefl-<≡ : ∀ x y → x ≡ y → x < y → ⊥
irrefl-<≡ x y e lt' = isIrrefl< (subst (λ w → x < w) (sym e) lt')

n-1≡-1 : ∀ n → n ≡ pos 0 → n - (pos 1) ≡ negsuc 0
n-1≡-1 n e = cong (λ w → w - (pos 1)) e

shift-eq : ∀ n → n - (pos 1) ≡ negsuc 0 → n ≡ pos 0
shift-eq n e = trans (sym (minusPlus (pos 1) n)) (cong (λ w → w + (pos 1)) e)

n+1≡1 : ∀ n → n ≡ pos 0 → n - negsuc 0 ≡ pos 1
n+1≡1 n e = cong (λ w → w - negsuc 0) e

shift-eq2 : ∀ n → n - negsuc 0 ≡ pos 1 → n ≡ pos 0
shift-eq2 n e = trans (sym (minusPlus (negsuc 0) n)) (cong (λ w → w + negsuc 0) e)

-- 九叶分派（双 tri：5 直叶 + 4 矛盾叶）
cross : ∀ (c d : ℤ) (n m k : ℤ)
  → c · mono-coeff d m (k - n) ≡ mono-coeff (c · d) (n + m) k
cross c d n m k with triℤ (k - n) m | triℤ k (n + m)
... | eq _ | eq _ = refl
... | lt _ | lt _ = ·AnnihilR c
... | gt _ | gt _ = ·AnnihilR c
... | lt _ | gt _ = ·AnnihilR c
... | gt _ | lt _ = ·AnnihilR c
... | eq e1 | lt x = rec (irrefl-<≡ k (n + m) (k≡n+m-bridge k n m e1) x)
... | eq e1 | gt x = rec (irrefl-<≡ (n + m) k (sym (k≡n+m-bridge k n m e1)) x)
... | lt x | eq e2 = rec (irrefl-<≡ (k - n) m (k-n≡m-bridge k n m e2) x)
... | gt x | eq e2 = rec (irrefl-<≡ m (k - n) (sym (k-n≡m-bridge k n m e2)) x)

-- 归约：窗口 abs (n - n) 经 subst 归零 + mono-coeff-eq 对角线
conv-reduce : ∀ (c d : ℤ) (n m k : ℤ)
  → sums k (mono c n *L mono d m) ≡ c · mono-coeff d m (k - n)
conv-reduce c d n m k = trans win (cong (λ z → z · mono-coeff d m (k - n)) (mono-coeff-eq c n))
  where
  F : ℤ → ℤ
  F i = mono-coeff c n i · mono-coeff d m (k - i)
  win : sums k (mono c n *L mono d m) ≡ mono-coeff c n n · mono-coeff d m (k - n)
  win = subst (λ w → sum-ℤ F n w ≡ mono-coeff c n n · mono-coeff d m (k - n))
              (sym (abs-n∸n n)) refl

mono-conv : ∀ (c d : ℤ) (n m k : ℤ)
  → sums k (mono c n *L mono d m) ≡ mono-coeff (c · d) (n + m) k
mono-conv c d n m k = trans (conv-reduce c d n m k) (cross c d n m k)

-- ══════════════════════════════════════════════════════════════════
-- B. t·t⁻¹ ≡ 1 家族
-- ══════════════════════════════════════════════════════════════════

-- B 节主件（桥族已上移至 A 节前）
tinv : Laurent
tinv = mono (pos 1) (negsuc 0)

t-tinv-shape : ∀ n → sums n (tvar *L tinv) ≡ pos 1 · mono-coeff (pos 1) (negsuc 0) (n - (pos 1))
t-tinv-shape n = refl

t-tinv-core : ∀ n → pos 1 · mono-coeff (pos 1) (negsuc 0) (n - (pos 1)) ≡ mono-coeff (pos 1) (pos 0) n
t-tinv-core n with triℤ (n - (pos 1)) (negsuc 0) | triℤ n (pos 0)
... | eq _ | eq _ = refl
... | lt _ | lt _ = refl
... | gt _ | gt _ = refl
... | lt _ | gt _ = refl
... | gt _ | lt _ = refl
... | eq e1 | lt x = rec (irrefl-<≡ n (pos 0) (shift-eq n e1) x)
... | eq e1 | gt x = rec (irrefl-<≡ (pos 0) n (sym (shift-eq n e1)) x)
... | lt x | eq e2 = rec (irrefl-<≡ (n - (pos 1)) (negsuc 0) (n-1≡-1 n e2) x)
... | gt x | eq e2 = rec (irrefl-<≡ (negsuc 0) (n - (pos 1)) (sym (n-1≡-1 n e2)) x)

t-tinv : ∀ n → sums n (tvar *L tinv) ≡ sums n R1
t-tinv n = trans (t-tinv-shape n) (t-tinv-core n)

tinv-t-shape : ∀ n → sums n (tinv *L tvar) ≡ pos 1 · mono-coeff (pos 1) (pos 1) (n - negsuc 0)
tinv-t-shape n = refl

tinv-t-core : ∀ n → pos 1 · mono-coeff (pos 1) (pos 1) (n - negsuc 0) ≡ mono-coeff (pos 1) (pos 0) n
tinv-t-core n with triℤ (n - negsuc 0) (pos 1) | triℤ n (pos 0)
... | eq _ | eq _ = refl
... | lt _ | lt _ = refl
... | gt _ | gt _ = refl
... | lt _ | gt _ = refl
... | gt _ | lt _ = refl
... | eq e1 | lt x = rec (irrefl-<≡ n (pos 0) (shift-eq2 n e1) x)
... | eq e1 | gt x = rec (irrefl-<≡ (pos 0) n (sym (shift-eq2 n e1)) x)
... | lt x | eq e2 = rec (irrefl-<≡ (n - negsuc 0) (pos 1) (n+1≡1 n e2) x)
... | gt x | eq e2 = rec (irrefl-<≡ (pos 1) (n - negsuc 0) (sym (n+1≡1 n e2)) x)

tinv-t : ∀ n → sums n (tinv *L tvar) ≡ sums n R1
tinv-t n = trans (tinv-t-shape n) (tinv-t-core n)

-- tneg = -t ≠ t⁻¹ 的反证：t·(-t) = -t² 在 n=2 处 ≠ R1
tneg-sums2 : sums (pos 2) (tvar *L tneg) ≡ negsuc 0
tneg-sums2 = refl

r1-sums2 : sums (pos 2) R1 ≡ pos 0
r1-sums2 = refl

tneg-goal-false : (∀ n → sums n (tvar *L tneg) ≡ sums n R1) → ⊥
tneg-goal-false h = neg≢pos0 (trans (sym tneg-sums2) (trans (h (pos 2)) r1-sums2))

-- ══════════════════════════════════════════════════════════════════
-- C. grow/dist 基础件
-- ══════════════════════════════════════════════════════════════════

sucL-pos : ∀ (L : ℤ) (m : ℕ) → sucℤ L +pos m ≡ sucℤ (L +pos m)
sucL-pos L zero = refl
sucL-pos L (suc m) = cong sucℤ (sucL-pos L m)

sucℤ+right : ∀ z m → sucℤ (z + (pos m)) ≡ z + (pos (suc m))
sucℤ+right z m = trans (sucℤ-def (z + (pos m))) (sym (+Assoc z (pos m) (pos 1)))

-- +pos 与真二元加的桥：z +pos m ≡ z + (pos m)（对 m 归纳）
+pos-≡+ : ∀ z m → z +pos m ≡ z + (pos m)
+pos-≡+ z zero = sym (zero-r z)
+pos-≡+ z (suc m) = trans (cong sucℤ (+pos-≡+ z m)) (sucℤ+right z m)

sucL-pos-suc-a : ∀ (L : ℤ) (j : ℕ) → sucℤ L +pos j ≡ (L + (pos j)) + (pos 1)
sucL-pos-suc-a L j = trans (sucL-pos L j)
  (trans (cong sucℤ (+pos-≡+ L j)) (sucℤ-def (L + (pos j))))

sucL-pos-suc : ∀ (L : ℤ) (j : ℕ) → sucℤ L +pos j ≡ L + (pos (suc j))
sucL-pos-suc L j = trans (sucL-pos-suc-a L j) (sym (+Assoc L (pos j) (pos 1)))

+rot : ∀ b c d → b + (c + d) ≡ c + (b + d)
+rot b c d = trans (+Assoc b c d) (trans (cong (λ w → w + d) (+Comm b c)) (sym (+Assoc c b d)))

+swap-mid : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+swap-mid a b c d = trans (sym (+Assoc a b (c + d)))
  (trans (cong (a +_) (+rot b c d)) (+Assoc a c (b + d)))

-- Σ 头剥：sum-ℤ t L (suc n) ≡ t L + sum-ℤ t (sucℤ L) n
sum-ℤ-uncons : ∀ (t : ℤ → ℤ) (L : ℤ) (n : ℕ) → sum-ℤ t L (suc n) ≡ t L + sum-ℤ t (sucℤ L) n
sum-ℤ-uncons t L zero = refl
sum-ℤ-uncons t L (suc n) =
  trans (cong (λ w → w + t (L +pos suc (suc n))) (sum-ℤ-uncons t L n))
  (trans (sym (+Assoc (t L) (sum-ℤ t (sucℤ L) n) (t (L +pos suc (suc n)))))
  (cong (λ w → t L + (sum-ℤ t (sucℤ L) n + t w)) (sym (sucL-pos L (suc n)))))

-- 尾零剥离
sum-ℤ-drop-tail : ∀ (t : ℤ → ℤ) (L : ℤ) (n : ℕ)
  → t (L +pos (suc n)) ≡ pos 0 → sum-ℤ t L (suc n) ≡ sum-ℤ t L n
sum-ℤ-drop-tail t L n h =
  trans (cong (λ w → sum-ℤ t L n + w) h) (zero-r (sum-ℤ t L n))

z<suc : ∀ d → zero <ℕ suc d
z<suc d = suc-≤-suc (d , +-zero d)

<weak : ∀ j d → j <ℕ d → j <ℕ suc d
<weak j d (k , p) = suc k , cong suc p

-- 右扩：尾部 d 项为零 → 长窗 = 短窗
sum-ℤ-grow-right : ∀ (t : ℤ → ℤ) (L : ℤ) (n d : ℕ)
  → (∀ j → j <ℕ d → t (L +pos suc (n +ℕ j)) ≡ pos 0)
  → sum-ℤ t L (n +ℕ d) ≡ sum-ℤ t L n
sum-ℤ-grow-right t L n zero h = cong (sum-ℤ t L) (+-zero n)
sum-ℤ-grow-right t L n (suc d) h =
    trans (cong (sum-ℤ t L) (+-suc n d))
  (trans (sum-ℤ-drop-tail t L (n +ℕ d) (h d ≤-refl))
         (sum-ℤ-grow-right t L n d (λ j jlt → h j (<weak j d jlt))))

-- 左扩：前 d 项为零 → 长窗起点右移 d
sum-ℤ-grow-left : ∀ (t : ℤ → ℤ) (L : ℤ) (n d : ℕ)
  → (∀ j → j <ℕ d → t (L +pos j) ≡ pos 0)
  → sum-ℤ t L (d +ℕ n) ≡ sum-ℤ t (L +pos d) n
sum-ℤ-grow-left t L n zero h = refl
sum-ℤ-grow-left t L n (suc d) h = trans helper1 helper2
  where
  S : ℤ
  S = sum-ℤ t (sucℤ L) (d +ℕ n)
  head0 : t L ≡ pos 0
  head0 = h zero (z<suc d)
  h' : ∀ j → j <ℕ d → t (sucℤ L +pos j) ≡ pos 0
  h' j jlt = trans (cong t (sucL-pos-suc L j))
    (trans (cong t (sym (+pos-≡+ L (suc j)))) (h (suc j) (suc-≤-suc jlt)))
  helper1 : sum-ℤ t L (suc (d +ℕ n)) ≡ S
  helper1 = trans (sum-ℤ-uncons t L (d +ℕ n)) (trans (cong (λ w → w + S) head0) (sym (pos0+ S)))
  helper2 : S ≡ sum-ℤ t (L +pos suc d) n
  helper2 = trans (sum-ℤ-grow-left t (sucℤ L) n d h')
                  (cong (λ z → sum-ℤ t z n) (trans (sucL-pos-suc L d) (sym (+pos-≡+ L (suc d)))))

-- 逐项分配
dist-term : ∀ (f g h : ℤ → ℤ) (k i : ℤ)
  → (f i + g i) · h (k - i) ≡ f i · h (k - i) + g i · h (k - i)
dist-term f g h k i = ·DistL+ (f i) (g i) (h (k - i))
