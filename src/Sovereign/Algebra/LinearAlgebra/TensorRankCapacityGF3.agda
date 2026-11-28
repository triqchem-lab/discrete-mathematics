{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankCapacityGF3
-- M25: 容量引理 —— 秩分解里「限制后恒零的项」可以全部丢掉, 以及由此得到的容量不等式（2026-11-28 登记）。
-- 指标集泛型: X Y Z 是任意集合, 只用到 Trit 上的求和。
--
-- 数学背景
--   设 T : X → Y → Z → Trit 有 r 项分解 T(x,y,z) = Σ_i a i x ⊗ (b i y ⊗ c i z)（M22 的 RankLE）。
--   取子空间 W ⊆ ⟨X⟩（第一因子空间）与 V ⊆ W^⊥, 记 N(W) = #{i : a i ∈ W}。首因子落在 W 里的项在
--   V 上全为零, 所以限制到 V 之后它们对和张没有贡献:
--       T|_V 有 r − N(W) 项分解;  于是对 T|_V 的任何下界 L（任何分解都至少 L 项）:  N(W) + L ≤ r。
--   这就是 D'Ambrosio 的 capacity-and-profile 策略里的「容量约束」(Wang arXiv:2609.06725 把它与自动化
--   下界框架结合; PROVEN §二十三 用它对 736 个轨道的证书界做了探针)。
--
-- 本件给出的
--   ① yesCnt: 可判定谓词在 Fin r 上的成立个数;
--   ② rank-cons / rank-tail: 分解在首项处的拆分与拼装;
--   ③ ★ rank-drops: 对 r 归纳——首项属于 P 就丢掉它（M23 的 rank-drop）, 否则对余项归纳再拼回首项;
--   ④ ★ capacity: 先沿 ι : X' → X 拉回（M22 的 rank-pull）, 再用 ③ 丢掉全部 P-项;
--   ⑤ ★ capacity-bound: 配合「L 是限制张量的下界」得到 N + L ≤ r;
--   ⑥ inSpan / vanish-inSpan / capacity-span: W 由一组生成元 g 给出、V 与 g 逐点正交时的版本。
--
-- 诚实边界
--   · 本件不改进任何下界数字。具体子空间的下界 L 要另行证明（例如直线 W 的 L = n·rank, 需要先补
--     GF(3) 上 3×3 矩阵的秩理论——库内 GF3Rank 未完成）。
--   · P 必须可判定; 「首因子落在 W 里」本身在本件里不可判定, 调用方要自己给出可判定的 P 及
--     「P 蕴含落在 W 里」的证据（vanish-inSpan / capacity-span）。
--   · r − N 是截断减法; N ≤ r 由 yesCnt≤ 给出。
--
-- 复用（先查后写）: RankLE·rank-pull(TensorRankIndexGF3) / rank-drop·rank-cong(TensorRankAlgebraGF3) /
--   sumFin·sumFin-cong·sumFin-zero(GF3LaplacianN) / rank-laderman(TensorRankLadermanGF3)。
--   M20（TensorRankRestrictGF3）只有支撑计数词汇与 weighted-zero, 没有「落在子空间里的项数」这条限制;
--   M23 的 rank-drop 一次只丢一项, 且下标固定给。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankCapacityGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; m∸n+n≡m; +-monoʳ-≤; +-comm)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; Dec; ¬_)

open import Sovereign.Base.Trit using (Trit; T₀; _⊕_; _⊗_; ⊗-zeroʳ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong; sumFin-zero)
open import Sovereign.Algebra.LinearAlgebra.TensorRankIndexGF3 using (RankLE; rank-pull)
open import Sovereign.Algebra.LinearAlgebra.TensorRankAlgebraGF3 using (rank-drop; rank-cong)

-- record 字段不随模块按名字导出, 本地打开泛型 record
open RankLE using (ra; rb; rc; rank-eq)

--------------------------------------------------------------------------------
-- §1 可判定谓词的成立个数
--------------------------------------------------------------------------------

yesCnt : ∀ {r} {P : Fin r → Set} → (∀ i → Dec (P i)) → ℕ
yesCnt {zero} {P} d = zero
yesCnt {suc r} {P} d = step (d fzero) (yesCnt (λ i → d (fsuc i)))
  where
  step : Dec (P fzero) → ℕ → ℕ
  step (yes _) n = suc n
  step (no _) n = n

yesCnt-yes : ∀ {r} {P : Fin (suc r) → Set} (d : ∀ i → Dec (P i)) (p : P fzero) →
  yesCnt d ≡ suc (yesCnt (λ i → d (fsuc i)))
yesCnt-yes {P = P} d p with d fzero
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

yesCnt-no : ∀ {r} {P : Fin (suc r) → Set} (d : ∀ i → Dec (P i)) (np : ¬ P fzero) →
  yesCnt d ≡ yesCnt (λ i → d (fsuc i))
yesCnt-no d np with d fzero
... | yes p = ⊥-elim (np p)
... | no _ = refl

-- 截断减法与后继: N ≤ r 时 suc r ∸ N ≡ suc (r ∸ N)（N 是变元时这不是定义等价）
suc∸ : ∀ r N → N ≤ r → suc r ∸ N ≡ suc (r ∸ N)
suc∸ zero .zero z≤n = refl
suc∸ (suc r) zero _ = refl
suc∸ (suc r) (suc n) (s≤s le) = suc∸ r n le

yesCnt≤ : ∀ {r} {P : Fin r → Set} (d : ∀ i → Dec (P i)) → yesCnt d ≤ r
yesCnt≤ {zero} {P} d = ≤-refl
yesCnt≤ {suc r} {P} d with d fzero
-- with 之后目标里露出 d fzero, 两个分支里 yesCnt 都直接归约, 不需要搬运
... | yes _ = s≤s (yesCnt≤ (λ i → d (fsuc i)))
... | no _ = m≤n⇒m≤1+n (yesCnt≤ (λ i → d (fsuc i)))

--------------------------------------------------------------------------------
-- §2 分解在首项处的拆分与拼装
--------------------------------------------------------------------------------

-- 首项
firstTerm : ∀ {X Y Z r} {T : X → Y → Z → Trit} → RankLE X Y Z T (suc r) → X → Y → Z → Trit
firstTerm ρ x y z = (ra ρ fzero x) ⊗ ((rb ρ fzero y) ⊗ (rc ρ fzero z))

-- 余和（第 1 项起）
restTerms : ∀ {X Y Z r} {T : X → Y → Z → Trit} → RankLE X Y Z T (suc r) → X → Y → Z → Trit
restTerms ρ x y z = sumFin (λ j → (ra ρ (fsuc j) x) ⊗ ((rb ρ (fsuc j) y) ⊗ (rc ρ (fsuc j) z)))

-- 余项自己是一个 r 项分解（张量换成余和）
rank-tail : ∀ {X Y Z r} {T : X → Y → Z → Trit} (ρ : RankLE X Y Z T (suc r)) → RankLE X Y Z (restTerms ρ) r
rank-tail ρ = record
  { ra = λ j x → ra ρ (fsuc j) x
  ; rb = λ j y → rb ρ (fsuc j) y
  ; rc = λ j z → rc ρ (fsuc j) z
  ; rank-eq = λ x y z → refl
  }

-- T = 首项 ⊕ 余和
head-tail : ∀ {X Y Z r} {T : X → Y → Z → Trit} (ρ : RankLE X Y Z T (suc r)) x y z →
  T x y z ≡ (firstTerm ρ x y z) ⊕ (restTerms ρ x y z)
head-tail ρ x y z = sym (rank-eq ρ x y z)

-- 在前面添一项
rank-cons : ∀ {X Y Z k} (a : X → Trit) (b : Y → Trit) (c : Z → Trit) (Tt : X → Y → Z → Trit) →
  RankLE X Y Z Tt k → RankLE X Y Z (λ x y z → (a x ⊗ (b y ⊗ c z)) ⊕ Tt x y z) (suc k)
rank-cons {X} {Y} {Z} {k} a b c Tt ρt = record
  { ra = hds
  ; rb = λ { fzero → b ; (fsuc j) → rb ρt j }
  ; rc = λ { fzero → c ; (fsuc j) → rc ρt j }
  ; rank-eq = λ x y z → cong ((a x ⊗ (b y ⊗ c z)) ⊕_) (rank-eq ρt x y z)
  }
  where
  hds : Fin (suc k) → X → Trit
  hds fzero = a
  hds (fsuc j) = ra ρt j

--------------------------------------------------------------------------------
-- §3 ★ 丢掉全部限制后恒零的项
--------------------------------------------------------------------------------

-- 对 r 归纳: 首项属于 P 就丢掉它; 否则对余项归纳, 再把首项拼回去。
-- 返回时把计数一并带出, 免得类型里出现「不可约的 yesCnt」。
rank-drops-aux : (r : ℕ) → ∀ {X Y Z} (T : X → Y → Z → Trit) (P : Fin r → Set) (P? : ∀ i → Dec (P i))
                 (ρ : RankLE X Y Z T r) → (∀ i (p : P i) x → ra ρ i x ≡ T₀) →
                 Σ ℕ (λ N → RankLE X Y Z T (r ∸ N) × yesCnt P? ≡ N)
rank-drops-aux zero T P P? ρ van = zero , ρ , refl
rank-drops-aux (suc r) {X} {Y} {Z} T P P? ρ van with P? fzero
... | yes p =
  let rest = rank-drops-aux r T (λ i → P (fsuc i)) (λ i → P? (fsuc i))
               (rank-drop T ρ fzero (λ x → van fzero p x)) (λ i q x → van (fsuc i) q x)
  in suc (proj₁ rest) , proj₁ (proj₂ rest) , cong suc (proj₂ (proj₂ rest))
... | no np =
  let ρt = rank-tail ρ
      rest = rank-drops-aux r (restTerms ρ) (λ i → P (fsuc i)) (λ i → P? (fsuc i)) ρt (λ i q x → van (fsuc i) q x)
      N = proj₁ rest
      N≤r = subst (_≤ r) (proj₂ (proj₂ rest)) (yesCnt≤ (λ i → P? (fsuc i)))
      glued = rank-cong (λ x y z → sym (head-tail ρ x y z))
                (rank-cons (ra ρ fzero) (rb ρ fzero) (rc ρ fzero) (restTerms ρ) (proj₁ (proj₂ rest)))
  in N , subst (λ M → RankLE X Y Z T M) (sym (suc∸ r N N≤r)) glued , proj₂ (proj₂ rest)

-- ★ P-项的首因子恒零 ⟹ T 有 r ∸ #{P-项} 项分解
rank-drops : ∀ {X Y Z r} (T : X → Y → Z → Trit) (P : Fin r → Set) (P? : ∀ i → Dec (P i))
             (ρ : RankLE X Y Z T r) → (∀ i (p : P i) x → ra ρ i x ≡ T₀) →
             RankLE X Y Z T (r ∸ yesCnt P?)
rank-drops {X} {Y} {Z} {r} T P P? ρ van =
  subst (RankLE X Y Z T) (cong (r ∸_) (sym (proj₂ (proj₂ aux)))) (proj₁ (proj₂ aux))
  where
  aux = rank-drops-aux r T P P? ρ van

-- 计数已知为 N 的版本
rank-drops-count : ∀ {X Y Z r} (T : X → Y → Z → Trit) (P : Fin r → Set) (P? : ∀ i → Dec (P i)) (N : ℕ) →
  yesCnt P? ≡ N → (ρ : RankLE X Y Z T r) → (∀ i (p : P i) x → ra ρ i x ≡ T₀) →
  RankLE X Y Z T (r ∸ N)
rank-drops-count {X} {Y} {Z} {r} T P P? N eqN ρ van =
  subst (RankLE X Y Z T) (cong (r ∸_) eqN) (rank-drops T P P? ρ van)

--------------------------------------------------------------------------------
-- §4 ★ 容量: 限制到 V ⊆ W^⊥ 后丢掉落在 W 里的项
--------------------------------------------------------------------------------

-- 下界的词汇: L 是 T 的下界 = T 的任何分解都至少 L 项（与 rank-2x2-lower 的写法同一口径）
LowerBound : ∀ {X Y Z} (T : X → Y → Z → Trit) (L : ℕ) → Set
LowerBound {X} {Y} {Z} T L = ∀ k → RankLE X Y Z T k → L ≤ k

-- ★ 沿 ι : X' → X 限制; P-项在 X' 上恒零 ⟹ 限制后的张量有 r ∸ #{P-项} 项分解
capacity : (X' : Set) → ∀ {X Y Z r} (T : X → Y → Z → Trit) (ι : X' → X) (P : Fin r → Set)
           (P? : ∀ i → Dec (P i)) (ρ : RankLE X Y Z T r) →
           (∀ i (p : P i) (x' : X') → ra ρ i (ι x') ≡ T₀) →
           RankLE X' Y Z (λ x' y z → T (ι x') y z) (r ∸ yesCnt P?)
capacity X' T ι P P? ρ van =
  rank-drops _ P P? (rank-pull X' T ι ρ) (λ i p x' → van i p x')

-- ★ 容量不等式: N + L ≤ r
capacity-bound : (X' : Set) → ∀ {X Y Z r} (T : X → Y → Z → Trit) (ι : X' → X) (P : Fin r → Set)
                 (P? : ∀ i → Dec (P i)) (ρ : RankLE X Y Z T r) (L : ℕ) →
                 (∀ i (p : P i) (x' : X') → ra ρ i (ι x') ≡ T₀) →
                 LowerBound (λ x' y z → T (ι x') y z) L →
                 yesCnt P? + L ≤ r
capacity-bound X' {X} {Y} {Z} {r} T ι P P? ρ L van lb =
  -- 右端: N + (r ∸ N) = (r ∸ N) + N = r
  subst (λ v → yesCnt P? + L ≤ v) (trans (+-comm (yesCnt P?) (r ∸ yesCnt P?)) (m∸n+n≡m (yesCnt≤ P?)))
        (+-monoʳ-≤ (yesCnt P?) (lb (r ∸ yesCnt P?) (capacity X' T ι P P? ρ van)))

--------------------------------------------------------------------------------
-- §5 W 由生成元给出
--------------------------------------------------------------------------------

-- a 落在 g 的张成里: 逐点 a x ≡ Σ_j c j ⊗ g j x（点态写法, 不用商空间; 与 GF3Dim 的 Span 同一口径）
inSpan : ∀ {X : Set} {m} (g : Fin m → X → Trit) (a : X → Trit) → Set
inSpan {X} {m} g a = Σ (Fin m → Trit) (λ c → ∀ x → a x ≡ sumFin (λ j → (c j) ⊗ (g j x)))

-- W ⊥ V（逐点: 每个 g j 在 ι 的像上为零）且 a ∈ W ⟹ a 在 V 上恒零
vanish-inSpan : ∀ {X : Set} {X' : Set} {m} (g : Fin m → X → Trit) (ι : X' → X) (a : X → Trit) →
  (∀ j x' → g j (ι x') ≡ T₀) → inSpan g a → ∀ x' → a (ι x') ≡ T₀
vanish-inSpan {X} {X'} {m} g ι a orth (c , e) x' =
  trans (e (ι x'))
        (trans (sumFin-cong (λ j → cong (λ v → (c j) ⊗ v) (orth j x')))
               (trans (sumFin-cong (λ j → ⊗-zeroʳ (c j))) (sumFin-zero {m})))

-- ★ 容量（W = span g 的版本）: P 可判定, P-项的首因子都落在 span g 里, ι 的像与 g 正交
capacity-span : (X' : Set) → ∀ {X Y Z r m} (T : X → Y → Z → Trit) (ι : X' → X) (g : Fin m → X → Trit)
                (P : Fin r → Set) (P? : ∀ i → Dec (P i)) (ρ : RankLE X Y Z T r) →
                (∀ i (p : P i) → inSpan g (ra ρ i)) → (∀ j x' → g j (ι x') ≡ T₀) →
                RankLE X' Y Z (λ x' y z → T (ι x') y z) (r ∸ yesCnt P?)
capacity-span X' T ι g P P? ρ inW orth =
  capacity X' T ι P P? ρ (λ i p x' → vanish-inSpan g ι (ra ρ i) orth (inW i p) x')
