{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Algebra.RingTheory.LaurentRingLaws
--
-- Laurent 多项式环 ℤ[t,t⁻¹]（函数表示）的环公理层：⑦A 裁决排期项。
--   组件：mono 卷积引理 / t·t⁻¹≡1 / 卷积分配（逐项+窗口件）/ sum-ℤ 代数（split·swap·分配·重引）
-- 数学背景：ℤ[t,t⁻¹] = { f : ℤ → ℤ | 有限支撑 }；*L = 窗口卷积（LaurentCubical）。
-- 来源：四路并行子件（2026-10-10）合并；oracle 7a1e5ebb 排假先行（64.9 万断言）。
--
-- 核心原则：
-- 1. 系数层陈述（函数表示下系数即全部信息；fst 级升级用 canon-sums-unique）
-- 2. 全部具名引理、每项 ∙ 链 ≤3；零洞零 postulate 零 REWRITE
-- 3. 禁区（实测爆点）：字面头+stuck 尾项的搬运/比较（字面剥 suc 链）
module Sovereign.Algebra.RingTheory.LaurentRingLaws where

-- ──── 一代 sum-ℤ 核心（④ 恢复） ────

-- | _PA_assoc（⑦A 子件④探针：卷积结合律——sum-ℤ 双和交换核心件）
--
-- 核心：sum-ℤ-split（和分配）+ sum-ℤ-swap（双和交换/interchange）+ · 分配两形

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; -_; pos; negsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int.Properties using (+Comm; +Assoc; ·DistR+; ·DistL+; minusPlus; pos0+; -Cancel'; -Involutive; -Dist+)
open import Sovereign.Algebra.RingTheory.LaurentCubical using (sum-ℤ)

-- 三元交换：b + (c + d) ≡ c + (b + d)
+swap3 : ∀ b c d → b + (c + d) ≡ c + (b + d)
+swap3 b c d = +Assoc b c d ∙ cong (_+ d) (+Comm b c) ∙ sym (+Assoc c b d)

-- 四元交叉：(a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d = sym (+Assoc a b (c + d)) ∙ cong (a +_) (+swap3 b c d) ∙ +Assoc a c (b + d)

-- 和分配：Σ (f + g) ≡ Σ f + Σ g
sum-ℤ-split : ∀ (f g : ℤ → ℤ) (L : ℤ) (n : ℕ) →
  sum-ℤ (λ i → f i + g i) L n ≡ sum-ℤ f L n + sum-ℤ g L n
sum-ℤ-split f g L zero = refl
sum-ℤ-split f g L (suc n) =
  cong (_+ (f (L + pos (suc n)) + g (L + pos (suc n)))) (sum-ℤ-split f g L n)
  ∙ +interchange (sum-ℤ f L n) (sum-ℤ g L n) (f (L + pos (suc n))) (g (L + pos (suc n)))

-- 双和交换（interchange）：Σᵢ Σⱼ F i j ≡ Σⱼ Σᵢ F i j
sum-ℤ-swap : ∀ (F : ℤ → ℤ → ℤ) (L₁ : ℤ) (n : ℕ) (L₂ : ℤ) (m : ℕ) →
  sum-ℤ (λ i → sum-ℤ (F i) L₂ m) L₁ n ≡ sum-ℤ (λ j → sum-ℤ (λ i → F i j) L₁ n) L₂ m
sum-ℤ-swap F L₁ zero L₂ m = refl
sum-ℤ-swap F L₁ (suc n) L₂ m =
  cong (_+ sum-ℤ (F (L₁ + pos (suc n))) L₂ m) (sum-ℤ-swap F L₁ n L₂ m)
  ∙ sym (sum-ℤ-split (λ j → sum-ℤ (λ i → F i j) L₁ n) (F (L₁ + pos (suc n))) L₂ m)

-- 右乘分配：(Σ φ) · c ≡ Σ (λ i → φ i · c)
sum-ℤ-·r : ∀ (φ : ℤ → ℤ) (L : ℤ) (n : ℕ) (c : ℤ) →
  sum-ℤ φ L n · c ≡ sum-ℤ (λ i → φ i · c) L n
sum-ℤ-·r φ L zero c = refl
sum-ℤ-·r φ L (suc n) c =
  ·DistL+ (sum-ℤ φ L n) (φ (L + pos (suc n))) c
  ∙ cong (_+ φ (L + pos (suc n)) · c) (sum-ℤ-·r φ L n c)

-- 左乘分配：Σ (λ i → c · φ i) ≡ c · (Σ φ)
sum-ℤ-·l : ∀ (c : ℤ) (φ : ℤ → ℤ) (L : ℤ) (n : ℕ) →
  sum-ℤ (λ i → c · φ i) L n ≡ c · sum-ℤ φ L n
sum-ℤ-·l c φ L zero = refl
sum-ℤ-·l c φ L (suc n) =
  cong (_+ c · φ (L + pos (suc n))) (sum-ℤ-·l c φ L n)
  ∙ sym (·DistR+ c (sum-ℤ φ L n) (φ (L + pos (suc n))))

-- ────────────────────────────────────────────────────────────────────
-- 指数移位件（窗口重引基础设施）
-- ────────────────────────────────────────────────────────────────────

-- 移位交换：(L + s) - j ≡ (L - j) + s
+-shift : ∀ L j s → (L + s) - j ≡ (L - j) + s
+-shift L j s = sym (+Assoc L s (- j)) ∙ cong (L +_) (+Comm s (- j)) ∙ +Assoc L (- j) s

-- 抵消移位：(k - i) + (i - j) ≡ k - j
-shift : ∀ k i j → (k - i) + (i - j) ≡ k - j
-shift k i j = +Assoc (k - i) i (- j) ∙ cong (_+ (- j)) (minusPlus i k)

-- 右零：x + pos 0 ≡ x
zero-r : ∀ x → x + pos 0 ≡ x
zero-r (pos n) = refl
zero-r (negsuc n) = refl

-- 尾部相消：(- i) + (- j + j) ≡ - i
inner-kill : ∀ i j → (- i) + (- j + j) ≡ - i
inner-kill i j = cong ((- i) +_) (-Cancel' j) ∙ zero-r (- i)

-- 内层三元交换（命名拆分——击败嵌套精化）
inner-swap : ∀ i j → (- j) + ((- i) + j) ≡ (- i) + (- j + j)
inner-swap i j = +swap3 (- j) (- i) j

-- 负差展开：- (i - j) ≡ (- i) + j
neg-shuffle : ∀ i j → - (i - j) ≡ (- i) + j
neg-shuffle i j = -Dist+ i (- j) ∙ cong ((- i) +_) (-Involutive j)

-- 重引恒等式：(k - j) - (i - j) ≡ k - i
shuffle : ∀ k i j → (k - j) - (i - j) ≡ k - i
shuffle k i j =
  cong ((k + - j) +_) (neg-shuffle i j)
  ∙ sym (+Assoc k (- j) ((- i) + j))
  ∙ cong (k +_) (inner-swap i j ∙ inner-kill i j)

-- 逐点同余：Σ 逐点等则和等
sum-ℤ-cong : ∀ (φ ψ : ℤ → ℤ) (L : ℤ) (n : ℕ) → (∀ i → φ i ≡ ψ i) →
  sum-ℤ φ L n ≡ sum-ℤ ψ L n
sum-ℤ-cong φ ψ L zero h = h L
sum-ℤ-cong φ ψ L (suc n) h =
  cong (_+ φ (L + pos (suc n))) (sum-ℤ-cong φ ψ L n h) ∙ cong (sum-ℤ ψ L n +_) (h (L + pos (suc n)))

-- 窗口平移重引：Σᵢ ψ(i - j) 在 [L, L+n] ≡ Σ_l ψ l 在 [L - j, (L - j) + n]
sum-ℤ-reindex : ∀ (ψ : ℤ → ℤ) (L : ℤ) (n : ℕ) (j : ℤ) →
  sum-ℤ (λ i → ψ (i - j)) L n ≡ sum-ℤ ψ (L - j) n
sum-ℤ-reindex ψ L zero j = refl
sum-ℤ-reindex ψ L (suc n) j =
  cong (_+ ψ ((L + pos (suc n)) - j)) (sum-ℤ-reindex ψ L n j)
  ∙ cong (sum-ℤ ψ (L - j) n +_) (cong ψ (+-shift L j (pos (suc n))))

-- ──── 一代 mono-conv/t·t⁻¹/grow·dist（重建 _PA_regen） ────

-- | _PA_regen（事故回收探针——第一代三件重建）
--
-- 数学背景：ℤ[t,t⁻¹] 函数表示（LaurentCubical）的三组基础件：
--   wA. mono 卷积引理（两单项式卷积 = 单项式 c·d·t^(n+m)）
--   wB. t·t⁻¹ ≡ 1 家族（含 tneg = -t ≠ t⁻¹ 的反证 tneg-goal-false）
--   wC. grow/dist 基础件（窗口零扩 + 逐项分配 + ℤ/+pos 桥）
--
-- 核心原则：
--   1. 零洞零 postulate；∙ 链 ≤3；具名拆分；where 有序（禁前向引用）
--   2. 禁碰「字面头+stuck 尾」（字面剥 suc 链爆点）
--   3. 真二元加一律写 `+ (pos …)` 括号形（空格算符陷阱：`x + pos n` 解析为 `x +pos n`）
--   4. Nat/Int 序双库 renaming 消歧（`_<ℕ_`/`_≤ℕ_` vs Int `_<`/`_≤`）

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
open import Sovereign.Algebra.NumberTheory.ProbeArith using (triℤ)
open import Sovereign.Algebra.RingTheory.LaurentCubical using
  (Laurent; sums; mono; mono-coeff; R1; tvar; tneg; _*L_; sum-ℤ; abs)

trans : ∀ {ℓ} {wA : Set ℓ} {x y z : wA} → x ≡ y → y ≡ z → x ≡ z
trans p q = p ∙ q

-- ══════════════════════════════════════════════════════════════════
-- C0. ℤ 基础件（零元 / 判别族 / sucℤ 定义桥）—— wA、wB、wC 共用
-- ══════════════════════════════════════════════════════════════════

-- 右零：x + (pos 0) ≡ x（两构造子叶）
zero-r0 : ∀ x → x + (pos 0) ≡ x
zero-r0 (pos n) = refl
zero-r0 (negsuc n) = refl

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
-- wA. mono 卷积家族
-- ══════════════════════════════════════════════════════════════════

-- n - n ≡ 0（inj-z+ 消去法；wA/wB 由其派生）
n∸n : ∀ n → n - n ≡ pos 0
n∸n n = inj-+z {n} {n - n} {pos 0} (trans (minusPlus n n) (pos0+ n))

wA : ∀ j → pos (suc j) + negsuc j ≡ pos 0
wA j = n∸n (pos (suc j))

wB : ∀ k → negsuc k + pos (suc k) ≡ pos 0
wB k = n∸n (negsuc k)

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
-- wB. t·t⁻¹ ≡ 1 家族
-- ══════════════════════════════════════════════════════════════════

-- wB 节主件（桥族已上移至 wA 节前）
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
-- wC. grow/dist 基础件
-- ══════════════════════════════════════════════════════════════════

sucL-pos : ∀ (L : ℤ) (m : ℕ) → sucℤ L +pos m ≡ sucℤ (L +pos m)
sucL-pos L zero = refl
sucL-pos L (suc m) = cong sucℤ (sucL-pos L m)

sucℤ+right : ∀ z m → sucℤ (z + (pos m)) ≡ z + (pos (suc m))
sucℤ+right z m = trans (sucℤ-def (z + (pos m))) (sym (+Assoc z (pos m) (pos 1)))

-- +pos 与真二元加的桥：z +pos m ≡ z + (pos m)（对 m 归纳）
+pos-to-+ : ∀ z m → z +pos m ≡ z + (pos m)
+pos-to-+ z zero = sym (zero-r0 z)
+pos-to-+ z (suc m) = trans (cong sucℤ (+pos-to-+ z m)) (sucℤ+right z m)

sucL-pos-suc-a : ∀ (L : ℤ) (j : ℕ) → sucℤ L +pos j ≡ (L + (pos j)) + (pos 1)
sucL-pos-suc-a L j = trans (sucL-pos L j)
  (trans (cong sucℤ (+pos-to-+ L j)) (sucℤ-def (L + (pos j))))

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
  trans (cong (λ w → sum-ℤ t L n + w) h) (zero-r0 (sum-ℤ t L n))

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
    (trans (cong t (sym (+pos-to-+ L (suc j)))) (h (suc j) (suc-≤-suc jlt)))
  helper1 : sum-ℤ t L (suc (d +ℕ n)) ≡ S
  helper1 = trans (sum-ℤ-uncons t L (d +ℕ n)) (trans (cong (λ w → w + S) head0) (sym (pos0+ S)))
  helper2 : S ≡ sum-ℤ t (L +pos suc d) n
  helper2 = trans (sum-ℤ-grow-left t (sucℤ L) n d h')
                  (cong (λ z → sum-ℤ t z n) (trans (sucL-pos-suc L d) (sym (+pos-to-+ L (suc d)))))

-- 逐项分配
dist-term : ∀ (f g h : ℤ → ℤ) (k i : ℤ)
  → (f i + g i) · h (k - i) ≡ f i · h (k - i) + g i · h (k - i)
dist-term f g h k i = ·DistL+ (f i) (g i) (h (k - i))

-- ──── 二代 A2/A4（_PAW） ────

-- | _PAW（⑦A 原子：A2 窗口等价（★）+ A4 零因子卷积）
--
-- A2：两窗口同含支撑 ⇒ 和相等（修正版 Covers——任务书版右零区差一，已报父代理）
-- A4：支撑空 ⇒ 卷积 = 0

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong; subst; _,_)
open import Cubical.Data.Int using (ℤ; pos; sucℤ; _+_; _-_; _·_; _+pos_)
open import Cubical.Data.Int.Order using (_≤_; ≤-refl) renaming (_<_ to _<ℤ_)
open import Cubical.Data.Int.Properties using (·AnnihilL; ·AnnihilR; sucℤ+; +Comm)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-suc)
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.RingTheory.LaurentCubical using
  (sum-ℤ; sum-ℤ-zero; Laurent; coeff; sums; _*L_; mono-coeff; abs; min-ℤ; min-ℤ≤ˡ; min-ℤ≤ʳ)
open import Sovereign.Algebra.NumberTheory.ProbeArith using (pos-split; ≤-witness; ≤-eq)

-- ────────────────────────────────────────────────────────────────────
-- Covers（修正版）：窗口 [L, L+n] 外项为零；右零区 L +pos n <ℤ i（= i > L+n）
--   任务书版写 L +pos suc n，漏 i = L+n+1，反例 t = δ_{L+n+1}（已报父代理）
-- ────────────────────────────────────────────────────────────────────
Covers : (ℤ → ℤ) → ℤ → ℕ → Set
Covers t L n = ∀ i → (i <ℤ L) ⊎ (L +pos n <ℤ i) → t i ≡ pos 0

-- ────────────────────────────────────────────────────────────────────
-- 桥族（全具名；∙ 链 ≤3）
-- ────────────────────────────────────────────────────────────────────

-- +pos 递归式（Base）：z +pos suc j = sucℤ (z +pos j) ⇒ 此桥为 refl
sucℤ-+pos : ∀ z j → sucℤ (z +pos j) ≡ z +pos suc j
sucℤ-+pos z j = refl

-- 右加 sucℤ 交换：z + sucℤ x ≡ sucℤ (z + x)（+Comm + sucℤ+ 组合）
+sucℤ-swap : ∀ z x → z + sucℤ x ≡ sucℤ (z + x)
+sucℤ-swap z x = +Comm z (sucℤ x) ∙ sym (sucℤ+ x z) ∙ cong sucℤ (+Comm x z)

-- +pos 形与 + pos 形桥：z +pos m ≡ z + pos m（对 m 归纳）
+pos-≡+2 : ∀ z m → z +pos m ≡ z + pos m
+pos-≡+2 z zero = sym (zero-r z)
+pos-≡+2 z (suc m) = cong sucℤ (+pos-≡+2 z m) ∙ sym (+sucℤ-swap z (pos m))

-- +pos 在 ℕ 参上单调（见证复用）
+pos-mono-≤ : ∀ z a b → a ≤ℕ b → (z +pos a) ≤ (z +pos b)
+pos-mono-≤ z a b (k , p) = k , (sym (pos-split z a k) ∙ cong (z +pos_) (+-comm a k) ∙ cong (z +pos_) p)

-- ℕ 级见证：suc K ≤ suc (K +ℕ j)（见证 j）
suc-K-≤ : ∀ K j → suc K ≤ℕ suc (K +ℕ j)
suc-K-≤ K j = j , (+-suc j K ∙ cong suc (+-comm j K))

-- 左零区条件转化：Covers ⇒ 扩窗起点段为零
cover-left : ∀ (t : ℤ → ℤ) L n (MIN : ℤ) k → MIN +pos k ≡ L → Covers t L n
           → ∀ j → j <ℕ k → t (MIN +pos j) ≡ pos 0
cover-left t L n MIN k eL cov j jlt = cov (MIN +pos j) (inl left<)
  where
  left-base : MIN +pos suc j ≤ MIN +pos k
  left-base = +pos-mono-≤ MIN (suc j) k jlt
  left-mid : sucℤ (MIN +pos j) ≤ MIN +pos k
  left-mid = subst (_≤ MIN +pos k) (sucℤ-+pos MIN j) left-base
  left< : sucℤ (MIN +pos j) ≤ L
  left< = subst (sucℤ (MIN +pos j) ≤_) eL left-mid

-- 右零区条件转化（出口为 grow-right 所需的 + pos 形）：对任意 j 成立
cover-right : ∀ (t : ℤ → ℤ) L n (MIN : ℤ) K → MIN +pos K ≡ L +pos n → Covers t L n
            → ∀ j → t (MIN + pos (suc (K +ℕ j))) ≡ pos 0
cover-right t L n MIN K e cov j = subst (λ z → t z ≡ pos 0) (+pos-≡+2 MIN (suc (K +ℕ j))) core
  where
  right-base : MIN +pos suc K ≤ MIN +pos suc (K +ℕ j)
  right-base = +pos-mono-≤ MIN (suc K) (suc (K +ℕ j)) (suc-K-≤ K j)
  right-mid : sucℤ (MIN +pos K) ≤ MIN +pos suc (K +ℕ j)
  right-mid = subst (_≤ MIN +pos suc (K +ℕ j)) (sucℤ-+pos MIN K) right-base
  right> : L +pos n <ℤ MIN +pos suc (K +ℕ j)
  right> = subst (_≤ MIN +pos suc (K +ℕ j)) (cong sucℤ e) right-mid
  core : t (MIN +pos suc (K +ℕ j)) ≡ pos 0
  core = cov (MIN +pos suc (K +ℕ j)) (inr right>)

-- ────────────────────────────────────────────────────────────────────
-- A2 主件：两窗口同含支撑 ⇒ 和相等
--   路线：双侧左扩到公共起点 MIN = min-ℤ L L'，再各右扩到 K1+K2 与 K2+K1（+ -comm 收口）
-- ────────────────────────────────────────────────────────────────────

sum-ℤ-window-eq : ∀ (t : ℤ → ℤ) L n L' n' → Covers t L n → Covers t L' n'
                → sum-ℤ t L n ≡ sum-ℤ t L' n'
sum-ℤ-window-eq t L n L' n' cov cov' = side1 ∙ crossw ∙ sym side2
  where
  MIN : ℤ
  MIN = min-ℤ L L'
  kL : ℕ
  kL = ≤-witness (min-ℤ≤ˡ L L')
  eL : MIN +pos kL ≡ L
  eL = ≤-eq (min-ℤ≤ˡ L L')
  kL' : ℕ
  kL' = ≤-witness (min-ℤ≤ʳ L L')
  eL' : MIN +pos kL' ≡ L'
  eL' = ≤-eq (min-ℤ≤ʳ L L')
  K1 : ℕ
  K1 = kL +ℕ n
  K2 : ℕ
  K2 = kL' +ℕ n'
  e1 : MIN +pos K1 ≡ L +pos n
  e1 = pos-split MIN kL n ∙ cong (_+pos n) eL
  e2 : MIN +pos K2 ≡ L' +pos n'
  e2 = pos-split MIN kL' n' ∙ cong (_+pos n') eL'
  step1L : sum-ℤ t L n ≡ sum-ℤ t MIN K1
  step1L = sym (cong (λ z → sum-ℤ t z n) eL)
         ∙ sym (sum-ℤ-grow-left t MIN n kL (cover-left t L n MIN kL eL cov))
  step1R : sum-ℤ t MIN K1 ≡ sum-ℤ t MIN (K1 +ℕ K2)
  step1R = sym (sum-ℤ-grow-right t MIN K1 K2 (λ j _ → cover-right t L n MIN K1 e1 cov j))
  side1 : sum-ℤ t L n ≡ sum-ℤ t MIN (K1 +ℕ K2)
  side1 = step1L ∙ step1R
  step2L : sum-ℤ t L' n' ≡ sum-ℤ t MIN K2
  step2L = sym (cong (λ z → sum-ℤ t z n') eL')
         ∙ sym (sum-ℤ-grow-left t MIN n' kL' (cover-left t L' n' MIN kL' eL' cov'))
  step2R : sum-ℤ t MIN K2 ≡ sum-ℤ t MIN (K2 +ℕ K1)
  step2R = sym (sum-ℤ-grow-right t MIN K2 K1 (λ j _ → cover-right t L' n' MIN K2 e2 cov' j))
  side2 : sum-ℤ t L' n' ≡ sum-ℤ t MIN (K2 +ℕ K1)
  side2 = step2L ∙ step2R
  crossw : sum-ℤ t MIN (K1 +ℕ K2) ≡ sum-ℤ t MIN (K2 +ℕ K1)
  crossw = cong (sum-ℤ t MIN) (+-comm K1 K2)

-- ────────────────────────────────────────────────────────────────────
-- A4：零因子卷积（支撑空 ⇒ 卷积 = 0）
-- ────────────────────────────────────────────────────────────────────

conv-zeroˡ : ∀ (f g : Laurent) k → (∀ i → coeff f i ≡ pos 0) → sums k (f *L g) ≡ pos 0
conv-zeroˡ (f , Lf , Uf , bf) (g , _) k h =
  sum-ℤ-zero (λ i → f i · g (k - i)) Lf (abs (Uf - Lf))
    (λ i → cong (_· g (k - i)) (h i) ∙ ·AnnihilL (g (k - i)))

conv-zeroʳ : ∀ (f g : Laurent) k → (∀ i → coeff g i ≡ pos 0) → sums k (f *L g) ≡ pos 0
conv-zeroʳ (f , Lf , Uf , bf) (g , _) k h =
  sum-ℤ-zero (λ i → f i · g (k - i)) Lf (abs (Uf - Lf))
    (λ i → cong (f i ·_) (h (k - i)) ∙ ·AnnihilR (f i))

-- ────────────────────────────────────────────────────────────────────
-- 交叉核对（refl 级小件）
-- ────────────────────────────────────────────────────────────────────

zero-fn : ℤ → ℤ
zero-fn _ = pos 0

zero-covers : ∀ L n → Covers zero-fn L n
zero-covers L n i _ = refl

-- 核对 1：主件端到端（零函数两窗口 [0,0] 与 [5,8]）
test-window-eq : sum-ℤ zero-fn (pos 0) 0 ≡ sum-ℤ zero-fn (pos 5) 3
test-window-eq = sum-ℤ-window-eq zero-fn (pos 0) 0 (pos 5) 3
                   (zero-covers (pos 0) 0) (zero-covers (pos 5) 3)

-- 核对 2：单点支撑 mono 两窗口偏移（refl 级计算：mono (pos 1) (pos 2)）
test-mono : sum-ℤ (mono-coeff (pos 1) (pos 2)) (pos 1) 3
          ≡ sum-ℤ (mono-coeff (pos 1) (pos 2)) (pos 0) 8
test-mono = refl

-- ──── 二代 A5（_PAI） ────

-- | _PAI（⑦A · *assoc 装配链第 4 步：逐点内层等式 A5-inner-eq）
--
-- 装配链：sum-ℤ-·r → sym ·Assoc → sum-ℤ-swap →【本件点化】→ sum-ℤ-·l → sum-ℤ-reindex → ★window-eq
-- 本件形态（未来态锚定——产出即第 5/6 步入口形）：
--   LHS = Σᵢ∈W f j · (g (i-j) · h (k-i))   （swap 后的内层和，W = 任意窗口 (L,n)）
--   RHS = f j · Σₗ g l · h ((k-j) - l)     （·l 拉出 f j + reindex l = i - j，窗口平移 L - j）
-- 分支（bf-j）：j ∉ [Lf,Uf] → f j ≡ 0 → 两边 0·_-形（供 ★window-eq 扩窗归零用）

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong)
open import Cubical.Data.Int using (ℤ; pos; _+_; _-_; _·_)
open import Cubical.Data.Int.Order using (_<_; Trichotomy; lt; eq; gt)
open import Cubical.Data.Int.Properties using (·AnnihilL)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.NumberTheory.ProbeArith using (triℤ)
open import Sovereign.Algebra.RingTheory.LaurentCubical using (sum-ℤ; sum-ℤ-zero)

-- ────────────────────────────────────────────────────────────────────
-- 1. shuffle 点化（summand 级）：h 的指数重引
--    shuffle k i j : (k - j) - (i - j) ≡ k - i  ⇒  h (k - i) ≡ h ((k - j) - (i - j))
-- ────────────────────────────────────────────────────────────────────

shuffle-point : ∀ (g h : ℤ → ℤ) (k i j : ℤ)
  → g (i - j) · h (k - i) ≡ g (i - j) · h ((k - j) - (i - j))
shuffle-point g h k i j = cong (g (i - j) ·_) (cong h (sym (shuffle k i j)))

-- ────────────────────────────────────────────────────────────────────
-- 2. 内核重引（g/h 件，无 f）：Σᵢ g(i-j)·h(k-i) ≡ Σₗ g l·h((k-j)-l)（窗口平移 L - j）
-- ────────────────────────────────────────────────────────────────────

inner-core : ∀ (g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ)
  → sum-ℤ (λ i → g (i - j) · h (k - i)) L n
  ≡ sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
inner-core g h k j L n =
    sum-ℤ-cong (λ i → g (i - j) · h (k - i))
               (λ i → g (i - j) · h ((k - j) - (i - j))) L n
               (λ i → shuffle-point g h k i j)
  ∙ sum-ℤ-reindex (λ l → g l · h ((k - j) - l)) L n j

-- ────────────────────────────────────────────────────────────────────
-- 3. 内支主件（任意 j 成立）：·l 拉出 f j + 内核重引
-- ────────────────────────────────────────────────────────────────────

inner-main : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ)
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
inner-main f g h k j L n =
    sum-ℤ-·l (f j) (λ i → g (i - j) · h (k - i)) L n
  ∙ cong (f j ·_) (inner-core g h k j L n)

-- ────────────────────────────────────────────────────────────────────
-- 4. 外支归零件（f j ≡ 0 → 两边 0·_-形）
-- ────────────────────────────────────────────────────────────────────

inner-zero-lhs : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) → f j ≡ pos 0
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n ≡ pos 0
inner-zero-lhs f g h k j L n fj0 =
  sum-ℤ-zero (λ i → f j · (g (i - j) · h (k - i))) L n
    (λ i → cong (_· (g (i - j) · h (k - i))) fj0 ∙ ·AnnihilL (g (i - j) · h (k - i)))

inner-zero-rhs : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) → f j ≡ pos 0
  → f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n ≡ pos 0
inner-zero-rhs f g h k j L n fj0 =
  cong (_· sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n) fj0
  ∙ ·AnnihilL (sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n)

zero-branch : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) → f j ≡ pos 0
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
zero-branch f g h k j L n fj0 =
    inner-zero-lhs f g h k j L n fj0
  ∙ sym (inner-zero-rhs f g h k j L n fj0)

-- ────────────────────────────────────────────────────────────────────
-- 5. A5-inner-eq（tri 分派：内支 = inner-main / 外支 = zero-branch）
--    bf = f 的有限支撑证人（IsFinSupp 形状：j ∉ [Lf,Uf] → f j ≡ 0）
-- ────────────────────────────────────────────────────────────────────

inner-eq : ∀ (f g h : ℤ → ℤ) (Lf Uf : ℤ)
         (bf : ∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
         (k j L : ℤ) (n : ℕ)
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
inner-eq f g h Lf Uf bf k j L n with triℤ j Lf | triℤ Uf j
... | lt x | _     = zero-branch f g h k j L n (bf j (inl x))
... | eq e | lt y  = zero-branch f g h k j L n (bf j (inr y))
... | eq e | eq e' = inner-main f g h k j L n
... | eq e | gt y  = inner-main f g h k j L n
... | gt x | lt y  = zero-branch f g h k j L n (bf j (inr y))
... | gt x | eq e' = inner-main f g h k j L n
... | gt x | gt y  = inner-main f g h k j L n

-- ────────────────────────────────────────────────────────────────────
-- 6. 验证点（②）：内支小例（refl 交叉）+ 外支小例（归零交叉）
-- ────────────────────────────────────────────────────────────────────

-- 内支：全 1 系数、窗口 (pos 0, 1)、k = 0、j = 0：1·(1·1)+1·(1·1) = 1·(1·1+1·1) = 2
check-in : sum-ℤ (λ i → pos 1 · (pos 1 · pos 1)) (pos 0) 1
         ≡ pos 1 · sum-ℤ (λ l → pos 1 · pos 1) (pos 0 - pos 0) 1
check-in = refl

-- 外支：f j = 0 → 两边 0·_-形，各归零
check-out-lhs : sum-ℤ (λ i → pos 0 · (pos 1 · pos 1)) (pos 0) 1 ≡ pos 0
check-out-lhs = refl

check-out-rhs : pos 0 · sum-ℤ (λ l → pos 1 · pos 1) (pos 0 - pos 0) 1 ≡ pos 0
check-out-rhs = refl

check-out : sum-ℤ (λ i → pos 0 · (pos 1 · pos 1)) (pos 0) 1
          ≡ pos 0 · sum-ℤ (λ l → pos 1 · pos 1) (pos 0 - pos 0) 1
check-out = inner-eq (λ _ → pos 0) (λ _ → pos 1) (λ _ → pos 1) (pos 0) (pos 0)
                    (λ n _ → refl) (pos 0) (pos 0) (pos 0) 1

-- ──── 二代 D1/D2（_PAD） ────

-- | _PAD（⑦A 子件 D2/D1：卷积分配律——系数层）
--   D2（易）：右分配 h *L (f +L g)——左因子同为 h，窗口同源，split 直通
--   D1（中）：左分配 (f +L g) *L h——窗口 = 并集（min/max），需窗口平移件

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong; cong₂; subst; _,_; fst; snd)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; -_; sucℤ; _+pos_; pos; negsuc)
open import Cubical.Data.Int.Properties using (·DistR+; ·DistL+; +Comm; +Assoc; -Cancel'; minusPlus; pos0+; ·AnnihilL)
open import Cubical.Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-assoc; +-suc; +-zero)
open import Cubical.Data.Nat.Order renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Cubical.Data.Int.Order using (_<_; _≤_; isTrans<; <-weaken; ≤-<-trans; isIrrefl<)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.NumberTheory.ProbeArith using (pos-+pos; triℤ)
open import Cubical.Data.Int.Order using (Trichotomy; lt; eq; gt)
open import Sovereign.Algebra.RingTheory.LaurentCubical using
  (Laurent; sums; _+L_; _*L_; sum-ℤ; sum-ℤ-zero; abs; min-ℤ; max-ℤ; min-ℤ≤ˡ; min-ℤ≤ʳ; max-ℤ≤ˡ; max-ℤ≤ʳ)

-- ────────────────────────────────────────────────────────────────────
-- 窗口平移件（grow 件的反向——扩窗不改和，当扩入项为零）
-- ────────────────────────────────────────────────────────────────────

-- 左移（反向 grow-left）：前 d 项为零 → 短窗 (L +pos d, n) = 长窗 (L, d +ℕ n)
sum-ℤ-shiftL : ∀ (t : ℤ → ℤ) (L : ℤ) (n d : ℕ)
  → (∀ j → j <ℕ d → t (L +pos j) ≡ pos 0)
  → sum-ℤ t L (d +ℕ n) ≡ sum-ℤ t (L +pos d) n
sum-ℤ-shiftL t L n d h = sum-ℤ-grow-left t L n d h

-- 右移（反向 grow-right）：尾 d 项为零 → 长窗 (L, n +ℕ d) = 短窗 (L, n)
sum-ℤ-shiftR-gen : ∀ (t : ℤ → ℤ) (L : ℤ) (n d : ℕ)
  → (∀ j → j <ℕ d → t (L + pos (suc (n +ℕ j))) ≡ pos 0)
  → sum-ℤ t L (n +ℕ d) ≡ sum-ℤ t L n
sum-ℤ-shiftR-gen t L n d h = sum-ℤ-grow-right t L n d h

-- ────────────────────────────────────────────────────────────────────
-- D2：右分配（窗口同源——左因子恒为 h）
-- ────────────────────────────────────────────────────────────────────

dist-r : ∀ (f g h : Laurent) (k : ℤ)
  → sums k (h *L (f +L g)) ≡ sums k (h *L f) + sums k (h *L g)
dist-r (f , (Lf , Uf , bf)) (g , (Lg , Ug , bg)) (h , (Lh , Uh , bh)) k =
  trans (sum-ℤ-cong (λ i → h i · (f (k - i) + g (k - i)))
                    (λ i → h i · f (k - i) + h i · g (k - i))
                    Lh (abs (Uh - Lh))
                    (λ i → ·DistR+ (h i) (f (k - i)) (g (k - i))))
        (sum-ℤ-split (λ i → h i · f (k - i)) (λ i → h i · g (k - i)) Lh (abs (Uh - Lh)))

-- ────────────────────────────────────────────────────────────────────
-- D1 地基件：ℤ 见证桥 + 窗口扩展
-- ℤ ≤ 的见证形（Cubical.Data.Int.Order）：x ≤ y = Σ ℕ (λ d → x +pos d ≡ y)
-- ────────────────────────────────────────────────────────────────────

-- +pos 与 + pos 一致性（构造子定义性）
plus-pos-def : ∀ z n → z +pos n ≡ z + pos n
plus-pos-def z n = refl

-- x + (- x) ≡ 0
x-plus-neg : ∀ x → x + (- x) ≡ pos 0
x-plus-neg x = +Comm x (- x) ∙ -Cancel' x

-- 左零：pos 0 + z ≡ z（pos0+ 现成件的反向）
zero-l : ∀ z → pos 0 + z ≡ z
zero-l z = sym (pos0+ z)

-- 内移：x + (z + (- x)) ≡ (x + (- x)) + z
shift-aux : ∀ x z → x + (z + (- x)) ≡ (x + (- x)) + z
shift-aux x z = cong (x +_) (+Comm z (- x)) ∙ +Assoc x (- x) z

-- 移位差：(x + z) - x ≡ z
shift-lemma : ∀ x z → (x + z) - x ≡ z
shift-lemma x z = sym (+Assoc x z (- x)) ∙ shift-aux x z ∙ (cong (_+ z) (x-plus-neg x) ∙ zero-l z)

-- 见证差：x +pos d ≡ y → y - x ≡ pos d
shift-diff : ∀ x d y → x +pos d ≡ y → y - x ≡ pos d
shift-diff x d y p = sym (cong (λ w → w - x) p) ∙ shift-lemma x (pos d)

-- 差见证：y - x ≡ pos d → x +pos d ≡ y
diff-shift : ∀ x d y → y - x ≡ pos d → x +pos d ≡ y
diff-shift x d y p = plus-pos-def x d ∙ +Comm x (pos d) ∙ (sym (cong (_+ x) p) ∙ minusPlus x y)

-- abs-分配：abs (pos k + pos s) ≡ k +ℕ s（构造件——+pos 对变量卡，refl 不过）
abs-pos-plus : ∀ k s → abs (pos k + pos s) ≡ k +ℕ s
abs-pos-plus k s = cong abs (pos-+pos k s)

-- abs-见证桥：pos 0 ≤ c → abs (c + pos s) ≡ abs c +ℕ s
abs-shift : ∀ (c : ℤ) (s : ℕ) → pos 0 ≤ c → abs (c + pos s) ≡ abs c +ℕ s
abs-shift c s (k , p) = subst (λ z → abs (z + pos s) ≡ abs z +ℕ s) p-inv (abs-pos-plus k s)
  where
  p-inv : pos k ≡ c
  p-inv = sym (pos-+pos 0 k) ∙ p

-- abs-见证等价：x +pos d ≡ y → abs (y - x) ≡ d
abs-witness : ∀ x d y → x +pos d ≡ y → abs (y - x) ≡ d
abs-witness x d y p = cong abs (shift-diff x d y p)

-- ℤ 移位洗牌：(x + pos s) - y ≡ (x - y) + pos s
shuffle1 : ∀ x s y → (x + pos s) - y ≡ (x - y) + pos s
shuffle1 x s y =
      sym (+Assoc x (pos s) (- y))
    ∙ cong (x +_) (+Comm (pos s) (- y))
    ∙ +Assoc x (- y) (pos s)

-- 反向消去：(- c) + c ≡ 0
neg-cancel-l : ∀ c → (- c) + c ≡ pos 0
neg-cancel-l c = +Comm (- c) c ∙ x-plus-neg c

-- 尾洗牌：(a + (- c)) + (c + (- b)) ≡ a + (- b)
tail-shuf : ∀ a c b → (a + (- c)) + (c + (- b)) ≡ a + (- b)
tail-shuf a c b = sym (+Assoc a (- c) (c + (- b))) ∙ cong (a +_) (mid c b)
  where
  mid : ∀ c b → (- c) + (c + (- b)) ≡ (- b)
  mid c b = +Assoc (- c) c (- b) ∙ cong (_+ (- b)) (neg-cancel-l c) ∙ zero-l (- b)

-- 三角差：a - b ≡ (a - c) + (c - b)
shuffle2 : ∀ a b c → a - b ≡ (a - c) + (c - b)
shuffle2 a b c = sym (tail-shuf a c b)

-- ────────────────────────────────────────────────────────────────────
-- D1 装配件：+pos 组合 + 见证组装 + 零区归一 + 窗口主件
-- ────────────────────────────────────────────────────────────────────

-- sucℤ 翻转：sucℤ x +pos n ≡ x +pos suc n
sucℤ-pos-flip : ∀ x n → sucℤ x +pos n ≡ x +pos suc n
sucℤ-pos-flip x zero = refl
sucℤ-pos-flip x (suc n) = cong sucℤ (sucℤ-pos-flip x n)

-- +pos 组合：(x +pos a) +pos b ≡ x +pos (a +ℕ b)
+pos-+pos : ∀ x a b → (x +pos a) +pos b ≡ x +pos (a +ℕ b)
+pos-+pos x a zero = cong (x +pos_) (sym (+-zero a))
+pos-+pos x a (suc b) = cong sucℤ (+pos-+pos x a b) ∙ cong (x +pos_) (sym (+-suc a b))

-- 见证组装：j <ℕ d → x +pos j < x +pos d
<-from-wit : ∀ x j d → j <ℕ d → (x +pos j) < (x +pos d)
comm-shuf : ∀ j r → j +ℕ suc r ≡ r +ℕ suc j
comm-shuf j r = +-comm j (suc r) ∙ sym (+-suc r j)

<-from-wit x j d (r , pr) = r , (
      sucℤ-pos-flip (x +pos j) r
    ∙ +pos-+pos x j (suc r)
    ∙ cong (x +pos_) (comm-shuf j r ∙ pr))

-- 零区归一：Uf < Lf → f 处处零
f-zero-out : ∀ (f : ℤ → ℤ) Lf Uf
  → (∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
  → Uf < Lf → ∀ i → f i ≡ pos 0
f-zero-out f Lf Uf bf u<lf i with triℤ i Lf
... | lt i<lf = bf i (inl i<lf)
... | eq e = bf i (inr (subst (Uf <_) (sym e) u<lf))
... | gt lf<i = bf i (inr (isTrans< u<lf lf<i))

-- ℕ 计数桥：suc ((dL +ℕ w) +ℕ j) ≡ dL +ℕ suc (w +ℕ j)
count-eq : ∀ dL w j → suc ((dL +ℕ w) +ℕ j) ≡ dL +ℕ suc (w +ℕ j)
count-eq dL w j = cong suc (sym (+-assoc dL w j)) ∙ sym (+-suc dL (w +ℕ j))

-- ℕ 洗牌：a +ℕ (dL +ℕ dR) ≡ (dL +ℕ a) +ℕ dR
n-shuf : ∀ a dL dR → a +ℕ (dL +ℕ dR) ≡ (dL +ℕ a) +ℕ dR
n-shuf a dL dR = +-assoc a dL dR ∙ cong (_+ℕ dR) (+-comm a dL)

-- 窗口主件（好支）：Lf ≤ Uf 见证 w0 → 并窗和 = 原窗和
good-core : ∀ (t f : ℤ → ℤ) Lf Uf Lm Um dL dR w0
  → Lm +pos dL ≡ Lf → Uf +pos dR ≡ Um → Lf +pos w0 ≡ Uf
  → (∀ i → f i ≡ pos 0 → t i ≡ pos 0)
  → (∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
  → sum-ℤ t Lm (abs (Um - Lm)) ≡ sum-ℤ t Lf (abs (Uf - Lf))
good-core t f Lf Uf Lm Um dL dR w0 pL pR pw f0 bf = trans step1 (trans step2 (trans step3 step4))
  where
  w = abs (Uf - Lf)
  c≥0 : pos 0 ≤ Uf - Lf
  c≥0 = subst (pos 0 ≤_) (sym (shift-diff Lf w0 Uf pw)) (w0 , pos-+pos 0 w0)
  pR′ : Uf + pos dR ≡ Um
  pR′ = sym (plus-pos-def Uf dR) ∙ pR
  um-lm-a : Um - Lm ≡ (Uf - Lm) + pos dR
  um-lm-a = sym (cong (λ z → z - Lm) pR′) ∙ shuffle1 Uf dR Lm
  um-lm-b : (Uf - Lm) + pos dR ≡ (Uf - Lf) + pos (dL +ℕ dR)
  um-lm-b =
        cong (_+ pos dR) (shuffle2 Uf Lm Lf)
      ∙ cong (λ z → ((Uf - Lf) + z) + pos dR) (shift-diff Lm dL Lf pL)
      ∙ (sym (+Assoc (Uf - Lf) (pos dL) (pos dR)) ∙ cong ((Uf - Lf) +_) (pos-+pos dL dR))
  um-lm : Um - Lm ≡ (Uf - Lf) + pos (dL +ℕ dR)
  um-lm = um-lm-a ∙ um-lm-b
  W≡ : abs (Um - Lm) ≡ abs (Uf - Lf) +ℕ (dL +ℕ dR)
  W≡ = cong abs um-lm ∙ abs-shift (Uf - Lf) (dL +ℕ dR) c≥0
  idW : (dL +ℕ abs (Uf - Lf)) +ℕ dR ≡ abs (Um - Lm)
  idW = sym (W≡ ∙ n-shuf (abs (Uf - Lf)) dL dR)
  zerosL : ∀ j → j <ℕ dL → t (Lm +pos j) ≡ pos 0
  zerosL j j<dL = f0 (Lm +pos j) (bf (Lm +pos j) (inl (subst ((Lm +pos j) <_) pL (<-from-wit Lm j dL j<dL))))
  i-form-a : ∀ j → Lm + pos (suc ((dL +ℕ w) +ℕ j)) ≡ Lf +pos suc (w +ℕ j)
  i-form-a j =
        sym (plus-pos-def Lm (suc ((dL +ℕ w) +ℕ j)))
      ∙ cong (Lm +pos_) (count-eq dL w j)
      ∙ (sym (+pos-+pos Lm dL (suc (w +ℕ j))) ∙ cong (_+pos suc (w +ℕ j)) pL)
  i-form-b : ∀ j → Lf +pos suc (w +ℕ j) ≡ Uf +pos suc j
  i-form-b j =
        cong (Lf +pos_) (sym (+-suc w j))
      ∙ (sym (+pos-+pos Lf w (suc j)) ∙ cong (λ z → (Lf +pos z) +pos suc j) (abs-witness Lf w0 Uf pw))
      ∙ cong (_+pos suc j) pw
  zerosR : ∀ j → j <ℕ dR → t (Lm + pos (suc ((dL +ℕ w) +ℕ j))) ≡ pos 0
  zerosR j j<dR = f0 (Lm + pos (suc ((dL +ℕ w) +ℕ j)))
    (bf (Lm + pos (suc ((dL +ℕ w) +ℕ j)))
      (inr (subst (Uf <_) (sym (i-form-a j ∙ i-form-b j)) (j , sucℤ-pos-flip Uf j))))
  step1 : sum-ℤ t Lm (abs (Um - Lm)) ≡ sum-ℤ t Lm ((dL +ℕ w) +ℕ dR)
  step1 = cong (sum-ℤ t Lm) (sym idW)
  step2 : sum-ℤ t Lm ((dL +ℕ w) +ℕ dR) ≡ sum-ℤ t Lm (dL +ℕ w)
  step2 = sum-ℤ-shiftR-gen t Lm (dL +ℕ w) dR zerosR
  step3 : sum-ℤ t Lm (dL +ℕ w) ≡ sum-ℤ t (Lm +pos dL) w
  step3 = sum-ℤ-shiftL t Lm w dL zerosL
  step4 : sum-ℤ t (Lm +pos dL) w ≡ sum-ℤ t Lf w
  step4 = cong (λ z → sum-ℤ t z w) pL

-- 窗口主件（含退化支）：Uf < Lf 时 t 处处零 → 两侧零和
sum-ℤ-window : ∀ (t f : ℤ → ℤ) Lf Uf Lm Um dL dR
  → Lm +pos dL ≡ Lf → Uf +pos dR ≡ Um
  → (∀ i → f i ≡ pos 0 → t i ≡ pos 0)
  → (∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
  → sum-ℤ t Lm (abs (Um - Lm)) ≡ sum-ℤ t Lf (abs (Uf - Lf))
sum-ℤ-window t f Lf Uf Lm Um dL dR pL pR f0 bf with triℤ Lf Uf
... | gt u<lf =
      trans (sum-ℤ-zero t Lm (abs (Um - Lm)) (λ i → f0 i (f-zero-out f Lf Uf bf u<lf i)))
            (sym (sum-ℤ-zero t Lf (abs (Uf - Lf)) (λ i → f0 i (f-zero-out f Lf Uf bf u<lf i))))
... | eq e = good-core t f Lf Uf Lm Um dL dR zero pL pR e f0 bf
... | lt x = good-core t f Lf Uf Lm Um dL dR (suc (fst x)) pL pR
            (sym (sucℤ-pos-flip Lf (fst x)) ∙ snd x) f0 bf

-- ────────────────────────────────────────────────────────────────────
-- D1：左分配（窗口 = 并集 min/max）
-- ────────────────────────────────────────────────────────────────────

dist-l : ∀ (f g h : Laurent) (k : ℤ)
  → sums k ((f +L g) *L h) ≡ sums k (f *L h) + sums k (g *L h)
dist-l (f , (Lf , Uf , bf)) (g , (Lg , Ug , bg)) (h , (Lh , Uh , bh)) k =
  trans (sum-ℤ-cong (λ i → (f i + g i) · h (k - i))
                    (λ i → f i · h (k - i) + g i · h (k - i))
                    (min-ℤ Lf Lg) (abs (max-ℤ Uf Ug - min-ℤ Lf Lg))
                    (λ i → ·DistL+ (f i) (g i) (h (k - i))))
        (trans (sum-ℤ-split (λ i → f i · h (k - i)) (λ i → g i · h (k - i))
                            (min-ℤ Lf Lg) (abs (max-ℤ Uf Ug - min-ℤ Lf Lg)))
               (cong₂ _+_ winF winG))
  where
  winF : sum-ℤ (λ i → f i · h (k - i)) (min-ℤ Lf Lg) (abs (max-ℤ Uf Ug - min-ℤ Lf Lg))
       ≡ sum-ℤ (λ i → f i · h (k - i)) Lf (abs (Uf - Lf))
  winF = sum-ℤ-window (λ i → f i · h (k - i)) f Lf Uf (min-ℤ Lf Lg) (max-ℤ Uf Ug)
          (fst (min-ℤ≤ˡ Lf Lg)) (fst (max-ℤ≤ˡ Uf Ug))
          (snd (min-ℤ≤ˡ Lf Lg)) (snd (max-ℤ≤ˡ Uf Ug))
          (λ i fi → cong (_· h (k - i)) fi ∙ ·AnnihilL (h (k - i))) bf
  winG : sum-ℤ (λ i → g i · h (k - i)) (min-ℤ Lf Lg) (abs (max-ℤ Uf Ug - min-ℤ Lf Lg))
       ≡ sum-ℤ (λ i → g i · h (k - i)) Lg (abs (Ug - Lg))
  winG = sum-ℤ-window (λ i → g i · h (k - i)) g Lg Ug (min-ℤ Lf Lg) (max-ℤ Uf Ug)
          (fst (min-ℤ≤ʳ Lf Lg)) (fst (max-ℤ≤ʳ Uf Ug))
          (snd (min-ℤ≤ʳ Lf Lg)) (snd (max-ℤ≤ʳ Uf Ug))
          (λ i gi → cong (_· h (k - i)) gi ∙ ·AnnihilL (h (k - i))) bg

-- ──── 二代 A6 *assoc（_PAA6） ────

-- | _PAA6（A6-assoc 装配：*assoc —— 卷积结合律，系数层）
--
-- 数学：ℤ[t,t⁻¹] 函数表示的卷积满足结合律。
--   内核 = sum-ℤ 双和交换（sum-ℤ-swap）+ A5 逐点内层等式（inner-eq）
--        + 窗口归一（_PAD.sum-ℤ-window；Covers 修正契约语义：零区恰在闭窗外）。
-- 装配链（未来态锚定）：
--   Σᵢ∈Wfg (Σⱼ∈Wf f·g)·h →〔·r + ·Assoc 整形〕→〔swap〕→〔inner-eq 点化〕
--   →〔内窗归一〕→ Σⱼ∈Wf f·(Σₗ∈Wg g·h) = RHS。
-- ⚠ 空格算符陷阱（本件血泪）：`x + pos n` 会被解析为 `x +pos n`（与 `_+pos_` 合并）！
--   真 `_+_` 一律写括号形 `x + (pos n)`；两形转换用自证桥 `pos-eq`。
-- 纪律：全具名、∙ 链 ≤3、where 有序、零洞零 postulate、-M2G。

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong; cong₂; subst; _,_; fst; snd)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; -_; sucℤ; _+pos_; pos; negsuc)
open import Cubical.Data.Int.Properties
  using (·DistR+; ·DistL+; +Comm; +Assoc; ·Assoc; -Cancel'; minusPlus; pos0+; ·AnnihilL; ·AnnihilR; -Dist+)
open import Cubical.Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-assoc; +-suc; +-zero)
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Cubical.Data.Int.Order using (_<_; _≤_; Trichotomy; lt; eq; gt; isTrans<; <-weaken; ≤-<-trans; isIrrefl<)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.NumberTheory.ProbeArith using (triℤ; pos-+pos; pos-split; ≤-witness; ≤-eq)
open import Sovereign.Algebra.RingTheory.LaurentCubical using
  ( Laurent; sums; _*L_; sum-ℤ; sum-ℤ-zero; abs; mono; mono-coeff; coeff; lt≤ )

-- ────────────────────────────────────────────────────────────────────
-- 区域 0：真 + / +pos 两形桥（消空格算符歧义）
-- ────────────────────────────────────────────────────────────────────

-- 真 + 右零（case 归约；`+ (pos 0)` 括号形防歧义）
zero-r+ : ∀ x → x + (pos 0) ≡ x
zero-r+ (pos n) = refl
zero-r+ (negsuc n) = refl

-- pos 加法合并（归纳 + Nat ±桥）
pos-sp : ∀ a b → (pos a) + (pos b) ≡ pos (a +ℕ b)
pos-sp a zero = cong pos (sym (+-zero a))
pos-sp a (suc b) = cong sucℤ (pos-sp a b) ∙ cong pos (sym (+-suc a b))

-- 两形桥：z +pos n ≡ z + (pos n)（z +pos 零/suc 递归式 + +sucℤ-swap）
pos-eq : ∀ z n → z +pos n ≡ z + (pos n)
pos-eq z zero = sym (zero-r+ z)
pos-eq z (suc n) = cong sucℤ (pos-eq z n) ∙ sym (+sucℤ-swap z (pos n))

-- ────────────────────────────────────────────────────────────────────
-- 区域 1：ℤ 序/差式桥（全具名，∙ 链 ≤3）
-- ────────────────────────────────────────────────────────────────────

-- ≤ 传递（见证形拼接）
≤-trans' : ∀ {x y z : ℤ} → x ≤ y → y ≤ z → x ≤ z
≤-trans' (d1 , e1) (d2 , e2) = (d1 +ℕ d2) , (sym (+pos-+pos _ d1 d2) ∙ cong (_+pos d2) e1 ∙ e2)

-- < → ≤（见证换算：sucℤ x +pos d ≡ y → x +pos suc d ≡ y）
<-to-≤ : ∀ {x y : ℤ} → x < y → x ≤ y
<-to-≤ {x} {y} (d , e) = suc d , (sym (sucℤ-pos-flip x d) ∙ e)

-- ≡ → ≤（x +pos 0 ≡ x 定义性）
eq-to-≤ : ∀ {x y : ℤ} → x ≡ y → x ≤ y
eq-to-≤ {x} e = 0 , e

-- 差式分配：a - (b + c) ≡ (a - b) - c
minus-sum : ∀ a b c → a - (b + c) ≡ (a - b) - c
minus-sum a b c = cong (a +_) (-Dist+ b c) ∙ +Assoc a (- b) (- c)

-- 平移桥 L：Lf +pos d ≡ j → (Lf + Lg - j) +pos d ≡ Lg
shift-l-eq : ∀ (Lf Lg j : ℤ) (d : ℕ) → Lf +pos d ≡ j → (Lf + Lg - j) +pos d ≡ Lg
shift-l-eq Lf Lg j d e = body
  where
  e+ : Lf + (pos d) ≡ j
  e+ = sym (pos-eq Lf d) ∙ e
  pre : (Lf + Lg) - j ≡ Lg - (pos d)
  pre = cong (λ z → (Lf + Lg) - z) (sym e+)
      ∙ minus-sum (Lf + Lg) Lf (pos d)
      ∙ cong (λ z → z - (pos d)) (shift-lemma Lf Lg)
  body : (Lf + Lg - j) +pos d ≡ Lg
  body = cong (_+pos d) pre ∙ pos-eq (Lg - (pos d)) d ∙ minusPlus (pos d) Lg

-- 平移桥 R（好支：Lf ≤ j ≤ Uf、Lg ≤ Ug 见证齐）：
--   Ug +pos d ≡ (Lf + Lg - j) +pos (dF +ℕ dG)
shift-r-eq : ∀ (Lf Uf Lg Ug j : ℤ) (dF dG d : ℕ)
  → Lf +pos dF ≡ Uf → Lg +pos dG ≡ Ug → j +pos d ≡ Uf
  → Ug +pos d ≡ (Lf + Lg - j) +pos (dF +ℕ dG)
shift-r-eq Lf Uf Lg Ug j dF dG d pF pG pD = sym total
  where
  pF+ : Lf + (pos dF) ≡ Uf
  pF+ = sym (pos-eq Lf dF) ∙ pF
  pG+ : Lg + (pos dG) ≡ Ug
  pG+ = sym (pos-eq Lg dG) ∙ pG
  pD+ : j + (pos d) ≡ Uf
  pD+ = sym (pos-eq j d) ∙ pD
  rot : (Lf + Lg) + (pos dF) ≡ (Lf + (pos dF)) + Lg
  rot = sym (+Assoc Lf Lg (pos dF)) ∙ cong (Lf +_) (+Comm Lg (pos dF)) ∙ +Assoc Lf (pos dF) Lg
  t1 : (Lf + Lg - j) +pos (dF +ℕ dG) ≡ ((Lf + Lg - j) + (pos dF)) + (pos dG)
  t1 = pos-eq (Lf + Lg - j) (dF +ℕ dG)
     ∙ cong ((Lf + Lg - j) +_) (sym (pos-sp dF dG))
     ∙ +Assoc (Lf + Lg - j) (pos dF) (pos dG)
  t2 : ((Lf + Lg - j) + (pos dF)) + (pos dG) ≡ ((Uf + Lg) - j) + (pos dG)
  t2 = cong (λ z → z + (pos dG))
       (sym (+-shift (Lf + Lg) j (pos dF)) ∙ cong (λ z → z - j) rot ∙ cong (λ z → (z + Lg) - j) pF+)
  t3 : ((Uf + Lg) - j) + (pos dG) ≡ (Uf + (Lg - j)) + (pos dG)
  t3 = cong (λ z → z + (pos dG))
       (shuffle2 (Uf + Lg) j Lg
        ∙ cong (λ z → z + (Lg - j)) (cong (λ z → z - Lg) (+Comm Uf Lg) ∙ shift-lemma Lg Uf))
  inner4 : (Lg - j) + (pos dG) ≡ Ug - j
  inner4 = sym (+-shift Lg j (pos dG)) ∙ cong (λ z → z - j) pG+
  t4 : (Uf + (Lg - j)) + (pos dG) ≡ Ug + (Uf - j)
  t4 = sym (+Assoc Uf (Lg - j) (pos dG)) ∙ cong (Uf +_) inner4 ∙ +swap3 Uf Ug (- j)
  t5 : Ug + (Uf - j) ≡ Ug +pos d
  t5 = cong (Ug +_) (shift-diff j d Uf pD) ∙ sym (pos-eq Ug d)
  total-a : (Lf + Lg - j) +pos (dF +ℕ dG) ≡ (Uf + (Lg - j)) + (pos dG)
  total-a = t1 ∙ t2 ∙ t3
  total : (Lf + Lg - j) +pos (dF +ℕ dG) ≡ Ug +pos d
  total = total-a ∙ t4 ∙ t5

-- abs 合并：好支下 abs ((Uf + Ug) - (Lf + Lg)) ≡ dF +ℕ dG
abs-comb : ∀ (Lf Uf Lg Ug : ℤ) (dF dG : ℕ)
  → Lf +pos dF ≡ Uf → Lg +pos dG ≡ Ug
  → abs ((Uf + Ug) - (Lf + Lg)) ≡ dF +ℕ dG
abs-comb Lf Uf Lg Ug dF dG pF pG = abs-witness (Lf + Lg) (dF +ℕ dG) (Uf + Ug) flush
  where
  pF+ : Lf + (pos dF) ≡ Uf
  pF+ = sym (pos-eq Lf dF) ∙ pF
  pG+ : Lg + (pos dG) ≡ Ug
  pG+ = sym (pos-eq Lg dG) ∙ pG
  flush1 : (Lf + Lg) +pos (dF +ℕ dG) ≡ (Lf + Lg) + ((pos dF) + (pos dG))
  flush1 = pos-eq (Lf + Lg) (dF +ℕ dG) ∙ cong ((Lf + Lg) +_) (sym (pos-sp dF dG))
  flush2 : (Lf + Lg) + ((pos dF) + (pos dG)) ≡ Uf + Ug
  flush2 = +interchange Lf Lg (pos dF) (pos dG) ∙ cong₂ _+_ pF+ pG+
  flush : (Lf + Lg) +pos (dF +ℕ dG) ≡ Uf + Ug
  flush = flush1 ∙ flush2

-- ────────────────────────────────────────────────────────────────────
-- 区域 2：零支与内窗归一
-- ────────────────────────────────────────────────────────────────────

-- 零支整项：f j ≡ 0 → 两侧同零
zero-both : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) (Lg : ℤ) (nG : ℕ) → f j ≡ pos 0
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) Lg nG
zero-both f g h k j L n Lg nG fj0 =
  inner-zero-lhs f g h k j L n fj0 ∙ sym (cong (_· S) fj0 ∙ ·AnnihilL S)
  where
  S : ℤ
  S = sum-ℤ (λ l → g l · h ((k - j) - l)) Lg nG

-- 内窗归一（好支）：[Lf+Lg-j, abs((Uf+Ug)-(Lf+Lg))] → [Lg, abs(Ug-Lg)]
win-good : ∀ (g h : ℤ → ℤ) (Lg Ug : ℤ)
           (bg : ∀ n → (n < Lg) ⊎ (Ug < n) → g n ≡ pos 0)
           (k j Lf Uf : ℤ) (lfj : Lf ≤ j) (juf : j ≤ Uf) (lgug : Lg ≤ Ug)
  → sum-ℤ (λ l → g l · h ((k - j) - l)) (Lf + Lg - j) (abs ((Uf + Ug) - (Lf + Lg)))
  ≡ sum-ℤ (λ l → g l · h ((k - j) - l)) Lg (abs (Ug - Lg))
win-good g h Lg Ug bg k j Lf Uf lfj juf lgug =
    cong (sum-ℤ t Lm) (sym absf)
  ∙ sum-ℤ-window t g Lg Ug Lm Um dLf dJ pL pR
      (λ i gi → cong (_· h ((k - j) - i)) gi ∙ ·AnnihilL (h ((k - j) - i))) bg
  where
  t : ℤ → ℤ
  t l = g l · h ((k - j) - l)
  Lm Um : ℤ
  Lm = Lf + Lg - j
  Um = Lm +pos abs ((Uf + Ug) - (Lf + Lg))
  dLf dJ : ℕ
  dLf = fst lfj
  dJ = fst juf
  lfuf : Lf ≤ Uf
  lfuf = ≤-trans' lfj juf
  pL : Lm +pos dLf ≡ Lg
  pL = shift-l-eq Lf Lg j dLf (snd lfj)
  absf : abs (Um - Lm) ≡ abs ((Uf + Ug) - (Lf + Lg))
  absf = abs-witness Lm (abs ((Uf + Ug) - (Lf + Lg))) Um refl
  pR : Ug +pos dJ ≡ Um
  pR = shift-r-eq Lf Uf Lg Ug j (fst lfuf) (fst lgug) dJ (snd lfuf) (snd lgug) (snd juf)
     ∙ cong (Lm +pos_) (sym (abs-comb Lf Uf Lg Ug (fst lfuf) (fst lgug) (snd lfuf) (snd lgug)))

win-norm : ∀ (g h : ℤ → ℤ) (Lg Ug : ℤ)
           (bg : ∀ n → (n < Lg) ⊎ (Ug < n) → g n ≡ pos 0)
           (k j Lf Uf : ℤ) (lfj : Lf ≤ j) (juf : j ≤ Uf)
  → sum-ℤ (λ l → g l · h ((k - j) - l)) (Lf + Lg - j) (abs ((Uf + Ug) - (Lf + Lg)))
  ≡ sum-ℤ (λ l → g l · h ((k - j) - l)) Lg (abs (Ug - Lg))
win-norm g h Lg Ug bg k j Lf Uf lfj juf with triℤ Ug Lg
... | lt u<lg =
      sum-ℤ-zero t (Lf + Lg - j) (abs ((Uf + Ug) - (Lf + Lg))) (λ l → t-zero l)
    ∙ sym (sum-ℤ-zero t Lg (abs (Ug - Lg)) (λ l → t-zero l))
  where
  t : ℤ → ℤ
  t l = g l · h ((k - j) - l)
  t-zero : ∀ l → t l ≡ pos 0
  t-zero l = cong (_· h ((k - j) - l)) (f-zero-out g Lg Ug bg u<lg l) ∙ ·AnnihilL (h ((k - j) - l))
... | eq e = win-good g h Lg Ug bg k j Lf Uf lfj juf (eq-to-≤ (sym e))
... | gt x = win-good g h Lg Ug bg k j Lf Uf lfj juf (<-to-≤ x)

-- ────────────────────────────────────────────────────────────────────
-- 区域 3：逐点等式（inner-eq 点化 + 内窗归一；tri 六叶分派）
-- ────────────────────────────────────────────────────────────────────

term-main : ∀ (f g h : ℤ → ℤ) (Lf Uf Lg Ug : ℤ)
            (bf : ∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
            (bg : ∀ n → (n < Lg) ⊎ (Ug < n) → g n ≡ pos 0)
            (k j : ℤ) → Lf ≤ j → j ≤ Uf
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) (Lf + Lg) (abs ((Uf + Ug) - (Lf + Lg)))
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) Lg (abs (Ug - Lg))
term-main f g h Lf Uf Lg Ug bf bg k j lfj juf =
    inner-eq f g h Lf Uf bf k j (Lf + Lg) (abs ((Uf + Ug) - (Lf + Lg)))
  ∙ cong (f j ·_) (win-norm g h Lg Ug bg k j Lf Uf lfj juf)

term-eq : ∀ (f g h : ℤ → ℤ) (Lf Uf Lg Ug : ℤ)
          (bf : ∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
          (bg : ∀ n → (n < Lg) ⊎ (Ug < n) → g n ≡ pos 0)
          (k j : ℤ)
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) (Lf + Lg) (abs ((Uf + Ug) - (Lf + Lg)))
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) Lg (abs (Ug - Lg))
term-eq f g h Lf Uf Lg Ug bf bg k j with triℤ j Lf | triℤ Uf j
... | lt x | _     = zero-both f g h k j (Lf + Lg) (abs ((Uf + Ug) - (Lf + Lg))) Lg (abs (Ug - Lg)) (bf j (inl x))
... | _     | lt x = zero-both f g h k j (Lf + Lg) (abs ((Uf + Ug) - (Lf + Lg))) Lg (abs (Ug - Lg)) (bf j (inr x))
... | eq e  | eq e' = term-main f g h Lf Uf Lg Ug bf bg k j (eq-to-≤ (sym e)) (eq-to-≤ (sym e'))
... | eq e  | gt y  = term-main f g h Lf Uf Lg Ug bf bg k j (eq-to-≤ (sym e)) (<-to-≤ y)
... | gt x  | eq e' = term-main f g h Lf Uf Lg Ug bf bg k j (<-to-≤ x) (eq-to-≤ (sym e'))
... | gt x  | gt y  = term-main f g h Lf Uf Lg Ug bf bg k j (<-to-≤ x) (<-to-≤ y)

-- ────────────────────────────────────────────────────────────────────
-- 区域 4：装配（2 ∙ 链：整形 → swap → 点化）
-- ────────────────────────────────────────────────────────────────────

reshape : ∀ (f g h : ℤ → ℤ) (Lf : ℤ) (nF : ℕ) (k i : ℤ)
  → sum-ℤ (λ j → f j · g (i - j)) Lf nF · h (k - i)
  ≡ sum-ℤ (λ j → f j · (g (i - j) · h (k - i))) Lf nF
reshape f g h Lf nF k i =
    sum-ℤ-·r (λ j → f j · g (i - j)) Lf nF (h (k - i))
  ∙ sum-ℤ-cong (λ j → (f j · g (i - j)) · h (k - i)) (λ j → f j · (g (i - j) · h (k - i))) Lf nF
      (λ j → sym (·Assoc (f j) (g (i - j)) (h (k - i))))

*assoc : ∀ (f g h : Laurent) (k : ℤ) → sums k ((f *L g) *L h) ≡ sums k (f *L (g *L h))
*assoc (f , (Lf , Uf , bf)) (g , (Lg , Ug , bg)) (h , (Lh , Uh , bh)) k =
    sum-ℤ-cong
      (λ i → sum-ℤ (λ j → f j · g (i - j)) Lf nF · h (k - i))
      (λ i → sum-ℤ (λ j → f j · (g (i - j) · h (k - i))) Lf nF)
      (Lf + Lg) nfg
      (λ i → reshape f g h Lf nF k i)
  ∙ sum-ℤ-swap (λ i j → f j · (g (i - j) · h (k - i))) (Lf + Lg) nfg Lf nF
  ∙ sum-ℤ-cong
      (λ j → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) (Lf + Lg) nfg)
      (λ j → f j · sum-ℤ (λ l → g l · h ((k - j) - l)) Lg nG)
      Lf nF
      (λ j → term-eq f g h Lf Uf Lg Ug bf bg k j)
  where
  nF nG nfg : ℕ
  nF = abs (Uf - Lf)
  nG = abs (Ug - Lg)
  nfg = abs ((Uf + Ug) - (Lf + Lg))

-- ────────────────────────────────────────────────────────────────────
-- 区域 5：核对层（refl 级对抗交叉——独立计算，不信 *assoc）
-- ────────────────────────────────────────────────────────────────────

check-mono : sums (pos 3) ((mono (pos 1) (pos 0) *L mono (negsuc 0) (pos 1)) *L mono (pos 1) (pos 1))
           ≡ sums (pos 3) (mono (pos 1) (pos 0) *L (mono (negsuc 0) (pos 1) *L mono (pos 1) (pos 1)))
check-mono = refl

zl : Laurent
zl = (λ _ → pos 0) , (pos 1 , pos 0 , λ n _ → refl)

check-degen : sums (pos 0) ((zl *L mono (pos 1) (pos 0)) *L mono (pos 1) (pos 0))
            ≡ sums (pos 0) (zl *L (mono (pos 1) (pos 0) *L mono (pos 1) (pos 0)))
check-degen = refl

-- ────────────────────────────────────────────────────────────────────
-- 【空格算符陷阱注记】（2026-10-11，_PAA6 血泪发现 + refl 探针实证）
--   `x + pos n` 会被 Agda 解析为 `x +pos n`（与 _+pos_ 合并）！需要真二元 +
--   一律写 `x + (pos n)` 括号形。真桥：zero-r+ / pos-sp / pos-eq / +pos-to-+。
--   旧「+ pos」桥（zero-r / plus-pos-def / +pos-≡+2 等）实为自反空件（语义 = refl）。
-- ────────────────────────────────────────────────────────────────────
