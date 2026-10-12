{-# OPTIONS --rewriting --guardedness #-}

-- | _PMN1
-- Myhill-Nerode 实例级：(ab)* 的 ~_L 分类（2 活类 ab 前缀形 + 1 死类 ⟺ 3 状态 DFA）
-- + aⁿbⁿ 负例（~_L 无穷类——前缀区分见证全证）。
--
-- 数学背景：
--   L = (ab)* = {ε, ab, abab, …}（读序）。右商 u⁻¹L = {w | u·w ∈ L}。~_L 类全形 3 类：
--   C₀ = (ab)*（u⁻¹L = L）· C₁ = (ab)*a（u⁻¹L = b(ab)*）· C₂ = 死类（u⁻¹L = ∅）。
--   任务书「2 类」= 2 活类（ab 前缀形 {(ab)ᵏ, (ab)ᵏa}）——全形含死类共 3（陈述细化注记）。
--   Myhill-Nerode 实例：u ~_L v ⟺ starS u ≡ starS v（3 状态机状态相等——类⟺状态双向）。
--   负例 L′ = {aⁿbⁿ}：aʲ ~ aᵏ（j≢k）不可能——区分后缀 bᵏ（aᵏbᵏ ∈ L′ 而 aʲbᵏ ∉ L′）。
--
-- 核心原则：
-- 1. DFA.run 为右折叠（List 头=最后读入字母）——栈序约定全件统一（"ab" 的栈形=[𝒃,𝒂]）；
-- 2. ~_L 逐点形（∀ w → …）——免 funext；
-- 3. 类⟺状态双向：same-state-quot（同态⇒同类）+ rep-inj（异态⇒分离）；
-- 4. 负例全证（非骨架）：shape 引理 + 计数注入 ⟹ 区分后缀定理 + 不可合并推论。
--
-- 包含：Letter · a-stack/b-stack · δab/acc3/abDFA/starS · AbStar/AbStarA（语义形）·
--       _~L_ · starS-cat · same-state-quot · rep/rep-inj · mn-instance ·
--       AnBn · abn-stack · anbn-shape · anbn-distinct · neg-merge · 核对层

module _PMN1 where

-- ══════════════════════════════════════════════════════════════════
-- §0 导入区
-- ══════════════════════════════════════════════════════════════════
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.Automata.DFA
  using (DFA; run; accepts)

-- ══════════════════════════════════════════════════════════════════
-- §1 字母、栈序与 (ab)* DFA（① 语言定义 + run 识别）
-- ══════════════════════════════════════════════════════════════════

-- 字母表 {a, b}
data Letter : Set where
  a b : Letter

-- 栈序形：读序词 aᵏ 的栈形 = [𝒂,…,𝒂]（头=最后读入字母，与 DFA.run 右折叠一致）
a-stack : ℕ → List Letter
a-stack zero    = []
a-stack (suc n) = a ∷ a-stack n

b-stack : ℕ → List Letter
b-stack zero    = []
b-stack (suc n) = b ∷ b-stack n

-- (ab)* 的 3 状态机：s0=偶段(接受) · s1=偶段后单 a(拒) · s2=死(拒)
s0 s1 s2 : Fin 3
s0 = fzero
s1 = fsuc fzero
s2 = fsuc (fsuc fzero)

δab : Fin 3 → Letter → Fin 3
δab fzero             a = s1
δab fzero             b = s2
δab (fsuc fzero)      a = s2
δab (fsuc fzero)      b = s0
δab (fsuc (fsuc fzero)) _ = s2

acc3 : Fin 3 → Bool
acc3 fzero     = true
acc3 (fsuc _)  = false

abDFA : DFA (Fin 3) Letter
abDFA = record
  { δ      = δab
  ; q₀     = s0
  ; accept = acc3
  }

starS : List Letter → Fin 3
starS = run abDFA

-- 语义形：(ab)* = {ε, ab, abab, …} 读序；栈形 = 𝒃∷𝒂∷ 逐层 + 尾 a 形
data AbStar : List Letter → Set where
  εL     : AbStar []
  cons-ab : ∀ {w} → AbStar w → AbStar (b ∷ (a ∷ w))

data AbStarA : List Letter → Set where
  aL : ∀ {w} → AbStar w → AbStarA (a ∷ w)

-- ① run 识别：语义形 ⟹ 机态（soundness）
sound0 : ∀ {w} → AbStar w → starS w ≡ s0
sound0 εL            = refl
sound0 (cons-ab {w} p) rewrite sound0 p = refl

sound1 : ∀ {w} → AbStarA w → starS w ≡ s1
sound1 (aL {w} p) rewrite sound0 p = refl

-- ══════════════════════════════════════════════════════════════════
-- §2 右不变等价 ~_L（逐点形）与 3 类全形
-- ══════════════════════════════════════════════════════════════════

-- 读序连接 u·w 的栈形 = w ++ u（头=最后读入——w 的字母在 u 之后读入）
rcat : List Letter → List Letter → List Letter
rcat u w = w ++ u

-- u ~_L v ⟺ 对一切续读 w，接受性一致（右不变等价——逐点形免 funext）
_~L_ : List Letter → List Letter → Set
u ~L v = ∀ w → accepts abDFA (rcat u w) ≡ accepts abDFA (rcat v w)

~-refl : ∀ u → u ~L u
~-refl u w = refl

~-sym : ∀ {u v} → u ~L v → v ~L u
~-sym hyp w = sym (hyp w)

~-trans : ∀ {u v t} → u ~L v → v ~L t → u ~L t
~-trans hyp1 hyp2 w = trans (hyp1 w) (hyp2 w)

-- 续读子（从状态 q 起读栈序词 w——与 starS 同折叠形）
post : Fin 3 → List Letter → Fin 3
post q []       = q
post q (x ∷ w)  = δab (post q w) x

-- 关键引理：starS (w ++ u) = post (starS u) w（右折叠的拼接律）
starS-cat : ∀ w u → starS (w ++ u) ≡ post (starS u) w
starS-cat []       u = refl
starS-cat (x ∷ w)  u = cong (λ q → δab q x) (starS-cat w u)

-- 主引理①：同态 ⟹ 同类（分类方向的引擎）
same-state-quot : ∀ u v → starS u ≡ starS v → u ~L v
same-state-quot u v hyp w =
  trans (cong acc3 (starS-cat w u))
    (trans (cong (λ q → acc3 (post q w)) hyp)
       (cong acc3 (sym (starS-cat w v))))

-- 3 类代表（ab 前缀形 2 活类 + 死类）
rep : Fin 3 → List Letter
rep fzero                = []
rep (fsuc fzero)         = a ∷ []
rep (fsuc (fsuc fzero))  = b ∷ []

starS-rep : ∀ q → starS (rep q) ≡ q
starS-rep fzero               = refl
starS-rep (fsuc fzero)        = refl
starS-rep (fsuc (fsuc fzero)) = refl

-- 分类：任一 u 同类于其态代表（3 类穷尽）
classify : ∀ u → u ~L rep (starS u)
classify u = same-state-quot u (rep (starS u)) (sym (starS-rep (starS u)))

-- 分离（3 对代表两两区分——区分后缀见证全 refl 级）
false≢true : false ≡ true → ⊥
false≢true ()

-- ε vs 死代表 [𝒃]：后缀 [] 区分（ε ∈ L 而 b ∉ L）
sep-0-2 : ¬ ([] ~L (b ∷ []))
sep-0-2 hyp = false≢true (sym (hyp []))

-- ε vs [𝒂]：后缀 [𝒃] 区分（ab ∈ L 而 b ∉ L）
sep-0-1 : ¬ ([] ~L (a ∷ []))
sep-0-1 hyp = false≢true (hyp (b ∷ []))

-- [𝒂] vs [𝒃]：后缀 [𝒃] 区分（ab ∈ L 而 bb ∉ L）
sep-1-2 : ¬ ((a ∷ []) ~L (b ∷ []))
sep-1-2 hyp = false≢true (sym (hyp (b ∷ [])))

-- 代表单射：异态代表必分离（9 案）
rep-inj : ∀ q₁ q₂ → rep q₁ ~L rep q₂ → q₁ ≡ q₂
rep-inj fzero               fzero               _    = refl
rep-inj fzero               (fsuc fzero)        hyp  = ⊥-elim (sep-0-1 hyp)
rep-inj fzero               (fsuc (fsuc fzero)) hyp  = ⊥-elim (sep-0-2 hyp)
rep-inj (fsuc fzero)        fzero               hyp  = ⊥-elim (sep-0-1 (~-sym hyp))
rep-inj (fsuc fzero)        (fsuc fzero)        _    = refl
rep-inj (fsuc fzero)        (fsuc (fsuc fzero)) hyp  = ⊥-elim (sep-1-2 hyp)
rep-inj (fsuc (fsuc fzero)) fzero               hyp  = ⊥-elim (sep-0-2 (~-sym hyp))
rep-inj (fsuc (fsuc fzero)) (fsuc fzero)        hyp  = ⊥-elim (sep-1-2 (~-sym hyp))
rep-inj (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) _    = refl

-- ══════════════════════════════════════════════════════════════════
-- §3 Myhill-Nerode 主件（③ 类 ⟺ 状态——实例级双向）
-- ══════════════════════════════════════════════════════════════════

-- 方向→：u ~_L v ⟹ starS u ≡ starS v（分离+传递收口）
mn-forward : ∀ u v → u ~L v → starS u ≡ starS v
mn-forward u v hyp = rep-inj (starS u) (starS v) chain
  where
  chain : rep (starS u) ~L rep (starS v)
  chain = ~-trans (~-sym (classify u)) (~-trans hyp (classify v))

-- 方向←：starS u ≡ starS v ⟹ u ~_L v（same-state-quot）
mn-back : ∀ u v → starS u ≡ starS v → u ~L v
mn-back = same-state-quot

-- 类计数面：3 态穷尽（2 活类 ab 前缀形 + 死类——任务书「2 类」=活类计数）
three-state : (q : Fin 3) → q ≡ s0 ⊎ (q ≡ s1 ⊎ q ≡ s2)
three-state fzero               = inj₁ refl
three-state (fsuc fzero)        = inj₂ (inj₁ refl)
three-state (fsuc (fsuc fzero)) = inj₂ (inj₂ refl)

-- ══════════════════════════════════════════════════════════════════
-- §4 aⁿbⁿ 负例（④ 无穷类——区分见证全证）
-- ══════════════════════════════════════════════════════════════════

-- L′ = {aⁿbⁿ}（读序）；栈形 = [𝒃ⁿ,𝒂ⁿ]
data AnBn : List Letter → Set where
  anbn-base : AnBn []
  anbn-step : ∀ {w} → AnBn w → AnBn (b ∷ (w ++ (a ∷ [])))

-- 尾插恒等（𝒂 串专用——a-stack n ++ [𝒂] ≡ 𝒂 ∷ a-stack n 反向）
a-snoc : ∀ n → a ∷ a-stack n ≡ a-stack n ++ (a ∷ [])
a-snoc zero    = refl
a-snoc (suc n) = cong (λ z → a ∷ z) (a-snoc n)

-- aᵏbᵏ 栈形 ∈ AnBn（正例族）
abn-stack : (n : ℕ) → AnBn (b-stack n ++ a-stack n)
abn-stack zero    = anbn-base
abn-stack (suc n) = subst-front (anbn-step (abn-stack n))
  where
  -- 目标：𝒃 ∷ ((b-stack n ++ a-stack n) ++ [𝒂]) ≡ 𝒃 ∷ (b-stack n ++ (𝒂 ∷ a-stack n))
  tail-lemma : ∀ n → (b-stack n ++ a-stack n) ++ (a ∷ [])
               ≡ b-stack n ++ (a ∷ a-stack n)
  tail-lemma n =
    trans (++-assoc (b-stack n) (a-stack n) (a ∷ []))
      (cong (λ zs → b-stack n ++ zs) (sym (a-snoc n)))
  subst-front : AnBn (b ∷ ((b-stack n ++ a-stack n) ++ (a ∷ [])))
              → AnBn (b ∷ (b-stack n ++ (a ∷ a-stack n)))
  subst-front p = subst AnBn (cong (λ z → b ∷ z) (tail-lemma n)) p

-- 形状引理：AnBn w ⟹ w = [𝒃ⁿ,𝒂ⁿ]（注入的前件）
anbn-shape : ∀ {w} → AnBn w → Σ ℕ (λ n → w ≡ b-stack n ++ a-stack n)
anbn-shape anbn-base        = zero , refl
anbn-shape (anbn-step {w} p) with anbn-shape p
... | n , refl = suc n ,
      cong (λ z → b ∷ z)
        (trans (++-assoc (b-stack n) (a-stack n) (a ∷ []))
           (cong (λ zs → b-stack n ++ zs) (sym (a-snoc n))))

-- 计数件（𝒃/𝒂 分量——注入引理的度量面）
countA : List Letter → ℕ
countA []       = zero
countA (a ∷ w)  = suc (countA w)
countA (b ∷ w)  = countA w

countB : List Letter → ℕ
countB []       = zero
countB (a ∷ w)  = countB w
countB (b ∷ w)  = suc (countB w)

countA-++ : ∀ xs ys → countA (xs ++ ys) ≡ countA xs + countA ys
countA-++ []       ys = refl
countA-++ (a ∷ xs) ys = cong suc (countA-++ xs ys)
countA-++ (b ∷ xs) ys = countA-++ xs ys

countB-++ : ∀ xs ys → countB (xs ++ ys) ≡ countB xs + countB ys
countB-++ []       ys = refl
countB-++ (a ∷ xs) ys = countB-++ xs ys
countB-++ (b ∷ xs) ys = cong suc (countB-++ xs ys)

countA-a-stack : ∀ n → countA (a-stack n) ≡ n
countA-a-stack zero    = refl
countA-a-stack (suc n) = cong suc (countA-a-stack n)

countA-b-stack : ∀ n → countA (b-stack n) ≡ zero
countA-b-stack zero    = refl
countA-b-stack (suc n) = countA-b-stack n

countB-a-stack : ∀ n → countB (a-stack n) ≡ zero
countB-a-stack zero    = refl
countB-a-stack (suc n) = countB-a-stack n

countB-b-stack : ∀ n → countB (b-stack n) ≡ n
countB-b-stack zero    = refl
countB-b-stack (suc n) = cong suc (countB-b-stack n)

-- 区分后缀定理：j ≢ k ⟹ aʲbᵏ ∉ AnBn（aᵏbᵏ ∈ AnBn 由 abn-stack 给）
anbn-distinct : ∀ j k → j ≢ k → ¬ AnBn (rcat (a-stack j) (b-stack k))
anbn-distinct j k ne p with anbn-shape p
... | n , eq = ne (trans (countA-inj eq) (sym (countB-inj eq)))
  where
  -- eq : b-stack k ++ a-stack j ≡ b-stack n ++ a-stack n
  -- 计数两侧：𝒂 分量给 j ≡ n；𝒃 分量给 k ≡ n
  countA-inj : b-stack k ++ a-stack j ≡ b-stack n ++ a-stack n → j ≡ n
  countA-inj e = trans (sym lem₁) (trans (cong countA e) lem₂)
    where
    lem₁ : countA (b-stack k ++ a-stack j) ≡ j
    lem₁ = trans (countA-++ (b-stack k) (a-stack j))
             (trans (cong (λ z → z + countA (a-stack j)) (countA-b-stack k))
                (countA-a-stack j))
    lem₂ : countA (b-stack n ++ a-stack n) ≡ n
    lem₂ = trans (countA-++ (b-stack n) (a-stack n))
             (trans (cong (λ z → z + countA (a-stack n)) (countA-b-stack n))
                (countA-a-stack n))
  countB-inj : b-stack k ++ a-stack j ≡ b-stack n ++ a-stack n → k ≡ n
  countB-inj e = trans (sym lem₁) (trans (cong countB e) lem₂)
    where
    lem₁ : countB (b-stack k ++ a-stack j) ≡ k
    lem₁ = trans (countB-++ (b-stack k) (a-stack j))
             (trans (cong (λ z → z + countB (a-stack j)) (countB-b-stack k))
                (trans (cong (λ z → k + z) (countB-a-stack j)) (+-identityʳ k)))
    lem₂ : countB (b-stack n ++ a-stack n) ≡ n
    lem₂ = trans (countB-++ (b-stack n) (a-stack n))
             (trans (cong (λ z → z + countB (a-stack n)) (countB-b-stack n))
                (trans (cong (λ z → n + z) (countB-a-stack n)) (+-identityʳ n)))

-- 不可合并推论：aʲ 与 aᵏ（j≢k）在 ~_{L′} 下不可合并（无穷类）
_~N_ : List Letter → List Letter → Set
u ~N v = (∀ w → AnBn (rcat u w) → AnBn (rcat v w))
       × (∀ w → AnBn (rcat v w) → AnBn (rcat u w))

neg-merge : ∀ j k → j ≢ k → ¬ (a-stack j ~N a-stack k)
neg-merge j k ne hyp = anbn-distinct j k ne (proj₂ hyp (b-stack k) (abn-stack k))

-- ══════════════════════════════════════════════════════════════════
-- §5 核对层（⑤ 具体值双通道）
-- ══════════════════════════════════════════════════════════════════

-- (ab)* 成员核对（栈序：ε / "ab" / "abab" ∈ L；"a"/"b"/"ba" ∉ L）
check-empty : accepts abDFA [] ≡ true
check-empty = refl

check-ab : accepts abDFA (b ∷ a ∷ []) ≡ true
check-ab = refl

check-abab : accepts abDFA (b ∷ a ∷ b ∷ a ∷ []) ≡ true
check-abab = refl

check-a : accepts abDFA (a ∷ []) ≡ false
check-a = refl

check-b : accepts abDFA (b ∷ []) ≡ false
check-b = refl

check-ba : accepts abDFA (a ∷ b ∷ []) ≡ false
check-ba = refl

-- 语义形实例（sound0/sound1 反调）
check-sound0-ex : starS (b ∷ a ∷ []) ≡ s0
check-sound0-ex = sound0 (cons-ab εL)

check-sound1-ex : starS (a ∷ []) ≡ s1
check-sound1-ex = sound1 (aL εL)

-- 类⟺状态实例：ε ~ "ab"（同态同调——MN 的 3 类面）
check-mn-same : [] ~L (b ∷ a ∷ [])
check-mn-same = mn-back [] (b ∷ a ∷ []) refl

-- 分离实例回显：sep-0-1/sep-0-2/sep-1-2 三对本身即类型级核对（见 §2）

-- aⁿbⁿ 正负例（区分见证）
check-anbn-22 : AnBn (b-stack 2 ++ a-stack 2)
check-anbn-22 = abn-stack 2

1≢2 : 1 ≢ 2
1≢2 ()

check-dist-12 : ¬ AnBn (rcat (a-stack 1) (b-stack 2))
check-dist-12 = anbn-distinct 1 2 1≢2

check-neg-merge : ¬ (a-stack 1 ~N a-stack 2)
check-neg-merge = neg-merge 1 2 1≢2
