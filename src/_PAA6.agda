{-# OPTIONS --cubical --guardedness #-}

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
module _PAA6 where

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
open import Sovereign.Algebra.ProbeArith using (triℤ; pos-+pos; pos-split; ≤-witness; ≤-eq)
open import Sovereign.Algebra.LaurentCubical using
  ( Laurent; sums; _*L_; sum-ℤ; sum-ℤ-zero; abs; mono; mono-coeff; coeff; lt≤ )
open import Sovereign.Algebra.LaurentRingLaws using
  ( sum-ℤ-·l; sum-ℤ-·r; sum-ℤ-cong; sum-ℤ-swap; +-shift; +interchange; +swap3 )
open import _PAI using (inner-eq; inner-main; inner-zero-lhs)
open import _PAD using
  ( shift-lemma; shuffle2; shift-diff; abs-pos-plus; +pos-+pos
  ; x-plus-neg; neg-cancel-l; abs-witness; f-zero-out; sum-ℤ-window; sucℤ-pos-flip )
open import _PAW using (+sucℤ-swap)

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
