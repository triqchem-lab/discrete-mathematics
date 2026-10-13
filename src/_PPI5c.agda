{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI5c —— πₙ-B3：[Sⁿᵈ,X]_* 商型 + n=1 桥（3 段形）+ k 元排序成链
-- 数学背景：
--   B1（_PPI5）定 Sⁿᵈ 双视图与 DHomotopy↔逐点桥；B2（_PPI5b）定 C→A 桥与柱体 Chain。
--   本件三件（设计文档选项 2 主定义路线）：
--   ① [Sⁿᵈ,X]_* 商型 = 基点映射 / DHomotopy 诱导等价（Cubical SetQuotient）；
--   ② n=1 桥（3 段形）：S¹ᵈ 型基点映射（S1Seg 三段像）↔ π₁ᵈ——to₁ 全向 + segOf 构造向 +
--     往返核对；一般长圈的切分 from（细分族 Cyc k）立界；
--   ③ k 元排序成链（insertion 形泛化 sort2：ins/sortL + 有序性家族）。
-- 核心原则：
--   · 双≡世界钉参：Cubical ≡ 为主（商型世界），PropEq 件全部 ≡ᴱ/symᴱ/transᴱ/congᴱ 前缀（CRT 教训）；
--   · 商关系 R 可取任意 Set 值——R 侧 PropEq 件零转换（eq/ 直收）；
--   · 复用零重证（DHomotopy/++w-resp-r/l/π₁ᵈ/[_] 全直用）。
-- 包含：BMHom/BMapQ ｜ S1Seg/s1loopOf/segOf/to₁/fromSeg/往返核对 ｜ ins/sortL/∈族 ｜ 核对层
module _PPI5c where

-- ── 导入区 ──────────────────────────────────────────────────────────
-- Cubical 世界（商型承载——≡ 为 Path）
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong; subst)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; rec; elimProp)

-- PropEq 世界（_PPI5/Barcelo 族——全部前缀钉参）
open import Relation.Binary.PropositionalEquality using ()
  renaming (_≡_ to _≡ᴱ_; refl to reflᴱ; sym to symᴱ; trans to transᴱ; cong to congᴱ; subst to substᴱ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; Walk; nil; cons; _++w_; AHomotopy; refl'; symm; trans'; gen)
open import _PPI using (++w-resp-r; ++w-resp-l)
open import _PPI5 using (BasedMap; DHomotopy; DStep)
open import _PPI2 using (π₁ᵈ; []-resp)

-- ── ① [Sⁿᵈ,X]_* 商型（选项 2 主定义：基点映射模 DHomotopy）────────────
-- 同伦关系 = DHomotopy 于载体映射（等价性由 DHomotopy 三律构造子承载：refl'/symm'/trans'）

BMHom : {S : Set} {s₀ : S} {X : Set} {x₀ : X}
      → BasedMap S s₀ X x₀ → BasedMap S s₀ X x₀ → Set
BMHom f g = DHomotopy (BasedMap.to f) (BasedMap.to g)

-- 基点映射同伦类商（设计文档选项 2）
BMapQ : {S : Set} (s₀ : S) (X : Set) (x₀ : X) → Set
BMapQ {S} s₀ X x₀ = BasedMap S s₀ X x₀ / BMHom

-- 商面投射（平名件——mixfix 定义形在 mutual 前置域受限，免匹配纪律同族）
bmQ : {S : Set} {s₀ : S} {X : Set} {x₀ : X} → BasedMap S s₀ X x₀ → BMapQ s₀ X x₀
bmQ f = [ f ]

-- （eqQ 包装层删除——bmQ 的隐式在合一位 stuck；eq/ 直用即全能力，无消费者不设包装）

-- ── ② n=1 桥（3 段形）：S1Seg ↔ π₁ᵈ ─────────────────────────────
-- S¹ᵈ 型基点映射的三段像形（基点烘入定义，免 transports）：
--   基点 x 固定；段像 w01 : x→y、w12 : y→z、w20 : z x（回边闭合）
record S1Seg (G : DiGraph) (x : DiGraph.V G) : Set where
  constructor seg
  field
    y z  : DiGraph.V G
    w01  : Walk G x y
    w12  : Walk G y z
    w20  : Walk G z x

open S1Seg

-- 诱导闭走（π₁ᵈ 的代表）
s1loopOf : {G : DiGraph} {x : DiGraph.V G} → S1Seg G x → Walk G x x
s1loopOf s = w01 s ++w (w12 s ++w w20 s)

-- 3 段代表的构造向（一般长圈的切分形 from 立界——细分族 Cyc k 属后续）
segOf : {G : DiGraph} {x : DiGraph.V G} (y z : DiGraph.V G)
      → Walk G x y → Walk G y z → Walk G z x → S1Seg G x
segOf = seg

-- 商面（本批工作形：loop 级同伦；分段级 S1SegHom（顶点搬运+段同伦）
--   与 loop 级的两同伦互导 = 精确剩余件（见 §4））
S1SegHomL : {G : DiGraph} {x : DiGraph.V G} → S1Seg G x → S1Seg G x → Set
S1SegHomL {G} s t = AHomotopy G (s1loopOf s) (s1loopOf t)

[S1] : {G : DiGraph} {x : DiGraph.V G} → Set
[S1] {G} {x} = S1Seg G x / S1SegHomL

-- n=1 桥 · to₁ 全向：[S¹ᵈ,G]_* → π₁ᵈ G x（商面映射——R 同即 AHomotopy，eq/ 直收）
to₁ : {G : DiGraph} {x : DiGraph.V G} → [S1] {G} {x} → π₁ᵈ G x
to₁ {G} {x} = rec squash/ (λ s → [ s1loopOf s ]) (λ _ _ r → []-resp r)

-- n=1 桥 · 构造向（3 段形）：S1Seg → 类
fromSeg : {G : DiGraph} {x : DiGraph.V G} → S1Seg G x → [S1] {G} {x}
fromSeg s = [ s ]

-- 往返核对（构造向·defeq 段）：to₁ ∘ fromSeg = λ s → [ s1loopOf s ] [defeq]
to-from-seg : {G : DiGraph} {x : DiGraph.V G} (s : S1Seg G x)
            → to₁ (fromSeg s) ≡ [ s1loopOf s ]
to-from-seg s = refl

-- 一般往返（π₁ᵈ 侧 from 的全向）= 精确剩余（§4：需细分族 Cyc k）
-- 小核对实例（G2s 两向边图：三段形往返 + 拼接形）
module _ where
  -- 双点对称图 G2s（沿 _PPI2/_PPI4d 词表：e01/e10 双向边）
  data G2sE : Fin 2 → Fin 2 → Set where
    g01 : G2sE fzero (fsuc fzero)
    g10 : G2sE (fsuc fzero) fzero
  G2s : DiGraph
  G2s = record { V = Fin 2 ; edge = G2sE }

  -- 三段形件（各段非空）：w01=g01（0→1）、w12=g10·g01（1→0→1）、w20=g10（1→0）
  s2 : S1Seg G2s fzero
  s2 = seg (fsuc fzero) (fsuc fzero)
         (cons g01 (nil (fsuc fzero)))
         (cons g10 (cons g01 (nil (fsuc fzero))))
         (cons g10 (nil fzero))

  -- 往返核对（defeq 段）：to₁ ∘ fromSeg = λ s → [s1loopOf s]，loop = 四边 0→1→0→1→0
  chk-to-from-s2 : to₁ (fromSeg s2)
                 ≡ [ cons g01 (cons g10 (cons g01 (cons g10 (nil fzero)))) ]
  chk-to-from-s2 = refl

-- ── ③ k 元排序成链（insertion 形泛化 sort2）──────────────────────
-- insertion 表排序（toℕ 序）——成员互保 + 有序性家族（sort2 为其 k=2 形）
open import Data.Nat.Properties using (_≤?_; ≤-refl; ≤-trans; n≤1+n; ≰⇒>)

mutual
  ins : {m : ℕ} → Fin m → List (Fin m) → List (Fin m)
  ins a [] = a ∷ []
  ins a (b ∷ bs) = insAux a b bs (toℕ a ≤? toℕ b)

  insAux : {m : ℕ} (a b : Fin m) → List (Fin m) → Dec (Data.Nat._≤_ (toℕ a) (toℕ b)) → List (Fin m)
  insAux a b bs (yes _) = a ∷ b ∷ bs
  insAux a b bs (no _)  = b ∷ ins a bs

sortL : {m : ℕ} → List (Fin m) → List (Fin m)
sortL [] = []
sortL (a ∷ as) = ins a (sortL as)

-- 成员（PropEq 世界形）
data _∈_ {m : ℕ} : Fin m → List (Fin m) → Set where
  here  : ∀ {a} {bs} → a ∈ (a ∷ bs)
  there : ∀ {a} {b} {bs} → a ∈ bs → a ∈ (b ∷ bs)

-- 成员互保（ins）
ins-self : {m : ℕ} (a : Fin m) (bs : List (Fin m)) → a ∈ ins a bs
ins-self {m} a [] = here
ins-self {m} a (b ∷ bs) = insAux-self (toℕ a ≤? toℕ b)
  where
  insAux-self : (d : Dec (Data.Nat._≤_ (toℕ a) (toℕ b))) → a ∈ insAux a b bs d
  insAux-self (yes _) = here
  insAux-self (no _)  = there (ins-self a bs)

ins-∈-l : {m : ℕ} (a x : Fin m) (bs : List (Fin m)) → x ∈ (a ∷ bs) → x ∈ ins a bs
ins-∈-l {m} a x [] h = h
ins-∈-l {m} a x (b ∷ bs) h = insAux-∈-l (toℕ a ≤? toℕ b) h
  where
  insAux-∈-l : (d : Dec (Data.Nat._≤_ (toℕ a) (toℕ b))) → x ∈ (a ∷ b ∷ bs) → x ∈ insAux a b bs d
  insAux-∈-l (yes _) here = here
  insAux-∈-l (yes _) (there h) = there h
  insAux-∈-l (no _) here = there (ins-self a bs)
  insAux-∈-l (no _) (there here) = here
  insAux-∈-l (no _) (there (there h)) = there (ins-∈-l a x bs (there h))

ins-∈-r : {m : ℕ} (a x : Fin m) (bs : List (Fin m)) → x ∈ ins a bs → x ∈ (a ∷ bs)
ins-∈-r {m} a x [] here = here
ins-∈-r {m} a x (b ∷ bs) h = insAux-∈-r (toℕ a ≤? toℕ b) h
  where
  insAux-∈-r : (d : Dec (Data.Nat._≤_ (toℕ a) (toℕ b))) → x ∈ insAux a b bs d → x ∈ (a ∷ b ∷ bs)
  insAux-∈-r (yes _) here = here
  insAux-∈-r (yes _) (there h) = there h
  insAux-∈-r (no _) here = there here
  insAux-∈-r (no _) (there h) = r-go (ins-∈-r a x bs h)
    where
    r-go : x ∈ (a ∷ bs) → x ∈ (a ∷ b ∷ bs)
    r-go here = here
    r-go (there h') = there (there h')

-- 有序性（list 头支配形：AllLE + Sorted）
AllLE : {m : ℕ} → Fin m → List (Fin m) → Set
AllLE a bs = ∀ {x} → x ∈ bs → Data.Nat._≤_ (toℕ a) (toℕ x)

data Sorted {m : ℕ} : List (Fin m) → Set where
  s-nil  : Sorted []
  s-cons : ∀ {a} {bs} → AllLE a bs → Sorted bs → Sorted (a ∷ bs)

ins-sorted : {m : ℕ} (a : Fin m) (bs : List (Fin m)) → Sorted bs → Sorted (ins a bs)
ins-sorted {m} a [] _ = s-cons (λ ()) s-nil
ins-sorted {m} a (b ∷ bs) (s-cons alle sbs) = insAux-sorted (toℕ a ≤? toℕ b) alle sbs
  where
  insAux-sorted : (d : Dec (Data.Nat._≤_ (toℕ a) (toℕ b)))
                → AllLE b bs → Sorted bs → Sorted (insAux a b bs d)
  insAux-sorted (yes le) alle sbs = s-cons a-le (s-cons alle sbs)
    where
    a-le : AllLE a (b ∷ bs)
    a-le here = le
    a-le (there h) = ≤-trans le (alle h)
  insAux-sorted (no nle) alle sbs = s-cons b-le (ins-sorted a bs sbs)
    where
    b≤a : Data.Nat._≤_ (toℕ b) (toℕ a)
    b≤a = ≤-trans (n≤1+n (toℕ b)) (≰⇒> nle)
    b-le : AllLE b (ins a bs)
    b-le h = b-le-go (ins-∈-r a _ bs h)
      where
      b-le-go : ∀ {x : Fin m} → x ∈ (a ∷ bs) → Data.Nat._≤_ (toℕ b) (toℕ x)
      b-le-go here = b≤a
      b-le-go (there h') = alle h'

sortL-sorted : {m : ℕ} (xs : List (Fin m)) → Sorted (sortL xs)
sortL-sorted [] = s-nil
sortL-sorted (a ∷ as) = ins-sorted a (sortL as) (sortL-sorted as)

-- 成员互保（sortL）
sortL-∈-l : {m : ℕ} (x : Fin m) (xs : List (Fin m)) → x ∈ xs → x ∈ sortL xs
sortL-∈-l x [] ()
sortL-∈-l x (a ∷ as) here = ins-∈-l a x (sortL as) here
sortL-∈-l x (a ∷ as) (there h) = ins-∈-l a x (sortL as) (there (sortL-∈-l x as h))

-- ── 核对层 ─────────────────────────────────────────────────────────
-- ③ 的 k=2 对账（sort2 像集同形）：具体值两序归一
chk-sort-21 : sortL {3} (fsuc (fsuc fzero) ∷ fzero ∷ []) ≡ (fzero ∷ fsuc (fsuc fzero) ∷ [])
chk-sort-21 = refl

chk-sort-12 : sortL {3} (fzero ∷ fsuc (fsuc fzero) ∷ []) ≡ (fzero ∷ fsuc (fsuc fzero) ∷ [])
chk-sort-12 = refl

chk-ins-self-2 : ins-self {3} (fsuc fzero) (fsuc (fsuc fzero) ∷ []) ≡ here
chk-ins-self-2 = refl

-- ── §4 精确剩余（立界）─────────────────────────────────────────────
-- (i) n=1 桥一般向：π₁ᵈ → [S¹ᵈ,G]_* 的全向 from（任意长圈 → 三段切分）需
--     细分族 Cyc k（k 圈图）+ 切分引理——S1Seg 只吃 3 段形；~60-100 行；
-- (ii) 分段级 S1SegHom（顶点搬运 py/pz + 段同伦 coe 形）与 loop 级 S1SegHomL
--     的两同伦互导——to₁ 的真内容升级件；~40-80 行；
-- (iii) ① 商型的 elimProp 面消去定理族（同伦诱导的 map 复合等）；
-- (iv) Simplex 装配（sortL → Simplex (linPoset m) k：lookup-monotone +
--     Sorted→Strict 链证）——~40 行；sort2 其 k=2 特例已在 _PPI5b。
-- 未决点照立档：Sⁿᵈ 圈长参数化（本批 S1Seg 固定 3 段形）；C₄ 相位不打通。
