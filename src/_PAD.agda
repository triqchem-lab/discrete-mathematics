{-# OPTIONS --cubical --guardedness #-}

-- | _PAD（⑦A 子件 D2/D1：卷积分配律——系数层）
--   D2（易）：右分配 h *L (f +L g)——左因子同为 h，窗口同源，split 直通
--   D1（中）：左分配 (f +L g) *L h——窗口 = 并集（min/max），需窗口平移件
module _PAD where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong; cong₂; subst; _,_; fst; snd)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; -_; sucℤ; _+pos_; pos; negsuc)
open import Cubical.Data.Int.Properties using (·DistR+; ·DistL+; +Comm; +Assoc; -Cancel'; minusPlus; pos0+; ·AnnihilL)
open import Cubical.Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-assoc; +-suc; +-zero)
open import Cubical.Data.Nat.Order renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Cubical.Data.Int.Order using (_<_; _≤_; isTrans<; <-weaken; ≤-<-trans; isIrrefl<)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.ProbeArith using (pos-+pos; triℤ)
open import Cubical.Data.Int.Order using (Trichotomy; lt; eq; gt)
open import Sovereign.Algebra.LaurentCubical using
  (Laurent; sums; _+L_; _*L_; sum-ℤ; sum-ℤ-zero; abs; min-ℤ; max-ℤ; min-ℤ≤ˡ; min-ℤ≤ʳ; max-ℤ≤ˡ; max-ℤ≤ʳ)
open import Sovereign.Algebra.LaurentRingLaws using
  (sum-ℤ-split; sum-ℤ-cong; sum-ℤ-grow-left; sum-ℤ-grow-right; trans)

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
