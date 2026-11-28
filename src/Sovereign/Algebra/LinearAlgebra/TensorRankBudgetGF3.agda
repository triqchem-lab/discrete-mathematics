{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankBudgetGF3
-- M27: 秩预算 —— 首因子由 N 个秩一片块拼成的 ⟨n,n,n⟩ 分解满足 n³ ≤ N（2026-11-28 登记）。
--
-- 数学背景
--   设 ⟨n,n,n⟩ 有 r 项分解, 首因子 A_t 是 n×n 矩阵。把每个 A_t 写成若干秩一矩阵之和
--   （A_t = Σ_α ℓ ⊗ ρ）, 全部片块共 N 个。「分割展平」是 n³ × n³ 的矩阵
--       P[(i,a,b),(i'',i',k')] = Σ_t A_t[i,i''] · B_t[a,b] · C_t[i',k'],
--   由矩阵乘法的结构常数, 它等于 [i = i'][i'' = a][b = k'] —— 一个置换矩阵（重排坐标后是恒等矩阵）。
--   换入片块: A_t[i,i''] = Σ ℓ[i]·ρ[i''], 于是
--       P[(i,a,b),(i'',i',k')] = Σ_片块 (ℓ[i]·B_t[a,b]) · (ρ[i'']·C_t[i',k']),   t = 片块所属的项,
--   即 P = X·Yᵀ, X、Y 都是 n³ × N。P 的 n³ 行线性无关（置换矩阵）, 又都落在 Y 的 N 列张成的空间里,
--   所以 n³ ≤ N。取片块数最少的写法就得 Σ_t rank(A_t) ≥ n³: 「秩预算」, 也就是「互补幂等」法里的 Δ ≥ 0。
--
-- 本件给出的
--   ① Pieces: 「首因子由 N 个秩一片块拼成」的记录（片块有左向量、右向量、所属的项）;
--   ② ★★ rank-budget: n³ ≤ N（结论写成 n * n * n = (n * n) * n; 证明里用 n * (n * n)）。
--
-- 诚实边界
--   · 内核里没有 3×3 矩阵秩的定义（GF3Rank 未完成）, 所以结论是对「片块数」说的;
--     「Σ_t rank(A_t) ≥ n³」要把每个首因子的最小片块分解拼成 Pieces, 这一步本件没有写。
--   · 等号可以取到: Strassen 的 7 项（2×2）Σ 秩 = 8 = 2³, 标准 n³ 项分解也是。
--   · 本件不改进任何下界数字。
--
-- 复用（先查后写）: RankLE(TensorRankIndexGF3) / mm·oneIf(TensorRankGF3) / sumFin-swap₃·oneIf-δc
--   (TensorRankFlattenGF3) / sumFin-δ·δc(GF3Dim) / fromFun·toFun·fromFun-toFun·toFun-fromFun(GF3Count) /
--   fromFun-cong(GF3BasisCount) / 3^-mono-<(GF3RankNullity) / sumFin-scale(TensorRankAlgebraGF3) /
--   combine·combine-surjective·injective⇒≤
--   (Data.Fin.Properties) / TritSolver(TritStdlibRing)。计数论证的形状与 M23 的 SpanGen.bound 相同。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankBudgetGF3 where

open import Data.Nat using (ℕ; zero; suc; _*_; _≤_; _<_; _^_)
open import Data.Nat.Properties using (<⇒≱; ≮⇒≥; *-assoc)
open import Data.Fin using (Fin; combine) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (combine-surjective; injective⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; _⊕_; _⊗_; ⊕-identityˡ; ⊕-identityʳ; ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc
  ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong; sumFin-zero)
open import Sovereign.Algebra.LinearAlgebra.GF3Dim using (δc; sumFin-δ)
open import Sovereign.Algebra.LinearAlgebra.GF3Count using (toFun; fromFun; fromFun-toFun; toFun-fromFun)
open import Sovereign.Algebra.LinearAlgebra.GF3BasisCount using (fromFun-cong)
open import Sovereign.Algebra.LinearAlgebra.GF3RankNullity using (3^-mono-<)
open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3 using (sumFin-swap₃; oneIf-δc; δc-sym)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3 using (Pos; Out; mm; oneIf)
open import Sovereign.Algebra.LinearAlgebra.TensorRankIndexGF3 using (RankLE)
open import Sovereign.Algebra.LinearAlgebra.TensorRankAlgebraGF3 using (sumFin-scale)
open import Sovereign.Algebra.RingTheory.TritStdlibRing using (module TritSolver)
open TritSolver using (_:=_; _:+_; _:*_; :-_) renaming (con to conₜ)

-- record 字段不随模块按名字导出, 本地打开泛型 record
open RankLE using (ra; rb; rc; rank-eq)

--------------------------------------------------------------------------------
-- §0 sumFin 的小引理
--------------------------------------------------------------------------------

-- 右因子提出和号
sumFin-scaleʳ : ∀ {r} (u : Fin r → Trit) (k : Trit) → sumFin (λ i → (u i) ⊗ k) ≡ (sumFin u) ⊗ k
sumFin-scaleʳ {zero} u k = refl
sumFin-scaleʳ {suc r} u k =
  trans (cong₂ _⊕_ refl (sumFin-scaleʳ (λ i → u (fsuc i)) k))
        (sym (⊗-distribʳ-⊕ (u fzero) (sumFin (λ i → u (fsuc i))) k))

-- 求和次序交换（两项都不带额外因子）
sumFin-swap-plain : ∀ m r (g : Fin m → Fin r → Trit) →
  sumFin (λ i → sumFin (λ q → g q i)) ≡ sumFin (λ q → sumFin (λ i → g q i))
sumFin-swap-plain m r g = trans s1 (trans s2 s3)
  where
  s1 : sumFin (λ i → sumFin (λ q → g q i)) ≡ sumFin (λ i → (sumFin (λ q → g q i)) ⊗ T₁)
  s1 = sumFin-cong (λ i → sym (⊗-identityʳ (sumFin (λ q → g q i))))
  s2 : sumFin (λ i → (sumFin (λ q → g q i)) ⊗ T₁) ≡ sumFin (λ q → sumFin (λ i → (g q i) ⊗ T₁))
  s2 = sumFin-swap₃ m r (λ q i → g q i) (λ _ → T₁)
  s3 : sumFin (λ q → sumFin (λ i → (g q i) ⊗ T₁)) ≡ sumFin (λ q → sumFin (λ i → g q i))
  s3 = sumFin-cong (λ q → sumFin-cong (λ i → ⊗-identityʳ (g q i)))

-- 指示函数只挑出一项: Σ_t [t₀ = t] ⊗ f t ≡ f t₀
pickOwn : ∀ {r} (f : Fin r → Trit) (t₀ : Fin r) → sumFin (λ t → oneIf t₀ t ⊗ f t) ≡ f t₀
pickOwn f t₀ = trans (sumFin-cong (λ t → cong (λ v → v ⊗ f t) (oneIf-δc t₀ t))) (sumFin-δ f t₀)

-- 指示函数对称
oneIf-sym : ∀ {n} (i j : Fin n) → oneIf i j ≡ oneIf j i
oneIf-sym i j = trans (oneIf-δc i j) (trans (δc-sym i j) (sym (oneIf-δc j i)))

-- 同上, 指示函数在右边: Σ_j f j ⊗ [j = i] ≡ f i
collapseʳ : ∀ {d} (f : Fin d → Trit) (i : Fin d) → sumFin (λ j → (f j) ⊗ oneIf j i) ≡ f i
collapseʳ f i =
  trans (sumFin-cong (λ j → trans (⊗-comm (f j) (oneIf j i))
                               (trans (cong (λ v → v ⊗ f j) (oneIf-δc j i))
                                      (cong (λ v → v ⊗ f j) (δc-sym j i)))))
        (sumFin-δ f i)

--------------------------------------------------------------------------------
-- §1 片块
--------------------------------------------------------------------------------

-- 首因子由 N 个秩一片块拼成: 片块 u 的左向量 ℓ u、右向量 ρ u, 属于第 own u 项;
-- 第 t 项的首因子 = Σ_{属于 t 的片块} (ℓ u) ⊗ (ρ u)（逐项: a t (i , j) ≡ Σ_u [own u = t] ⊗ ℓ u i ⊗ ρ u j）
record Pieces (n N r : ℕ) (a : Fin r → Pos n → Trit) : Set where
  field
    ℓ : Fin N → Fin n → Trit
    rv : Fin N → Fin n → Trit
    own : Fin N → Fin r
    assemble : ∀ t i j → a t (i , j) ≡ sumFin (λ u → oneIf (own u) t ⊗ ((ℓ u i) ⊗ (rv u j)))

-- 三重指标: (第一因子的行 i, 第二因子的位置 (a , b)) / (第三因子的位置 (i'' , k'), 第一因子的列 i'')
Idx : ℕ → Set
Idx n = Fin n × Fin n × Fin n

-- 三重指标上的和
sumIdx₃ : ∀ {n} → (Idx n → Trit) → Trit
sumIdx₃ g = sumFin (λ i → sumFin (λ a → sumFin (λ b → g (i , a , b))))

-- 分割展平 P 的结构: 由 mm 的三个指示函数之积
P : ∀ {n} → Idx n → Idx n → Trit
P (i , a , b) (i'' , i' , k') = oneIf i i' ⊗ (oneIf i'' a ⊗ oneIf b k')

-- mm 在这些位置上就是 P（定义等价, 这里只是把它写成一条引理供阅读）
mm-is-P : ∀ {n} (i a b i'' i' k' : Fin n) →
  mm n (i , i'') (a , b) (i' , k') ≡ P (i , a , b) (i'' , i' , k')
mm-is-P i a b i'' i' k' = refl

module Budget (n r N : ℕ) (ρ : RankLE (Pos n) (Pos n) (Out n) (mm n) r)
               (pc : Pieces n N r (ra ρ)) where

  open Pieces pc public

  -- X、Y: n³ × N
  X : Idx n → Fin N → Trit
  X (i , a , b) u = (ℓ u i) ⊗ (rb ρ (own u) (a , b))

  Y : Idx n → Fin N → Trit
  Y (i'' , i' , k') u = (rv u i'') ⊗ (rc ρ (own u) (i' , k'))

  --------------------------------------------------------------------------------
  -- ② P = X·Yᵀ
  --------------------------------------------------------------------------------

  -- 片块 u 对 P 的贡献
  piece-term : ∀ (i a b i'' i' k' : Fin n) (u : Fin N) →
    sumFin (λ t → ((oneIf (own u) t ⊗ ((ℓ u i) ⊗ (rv u i''))) ⊗
                   ((rb ρ t (a , b)) ⊗ (rc ρ t (i' , k'))))) ≡
    (X (i , a , b) u) ⊗ (Y (i'' , i' , k') u)
  piece-term i a b i'' i' k' u =
    trans (sumFin-cong (λ t →
             TritSolver.solve 5 (λ p l v c d → (p :* (l :* v)) :* (c :* d) := p :* ((l :* c) :* (v :* d)))
               refl (oneIf (own u) t) (ℓ u i) (rv u i'') (rb ρ t (a , b)) (rc ρ t (i' , k'))))
          (pickOwn (λ t → ((ℓ u i) ⊗ (rb ρ t (a , b))) ⊗ ((rv u i'') ⊗ (rc ρ t (i' , k')))) (own u))

  P-factor : ∀ row col → P row col ≡ sumFin (λ u → (X row u) ⊗ (Y col u))
  P-factor (i , a , b) (i'' , i' , k') =
    trans (sym (rank-eq ρ (i , i'') (a , b) (i' , k')))
          (trans (sumFin-cong (λ t → cong (λ v → v ⊗ ((rb ρ t (a , b)) ⊗ (rc ρ t (i' , k'))))
                                           (assemble t i i'')))
                (trans (sumFin-swap₃ N r
                               (λ u t → (oneIf (own u) t) ⊗ ((ℓ u i) ⊗ (rv u i'')))
                               (λ t → (rb ρ t (a , b)) ⊗ (rc ρ t (i' , k'))))
                       (sumFin-cong (λ u → piece-term i a b i'' i' k' u))))

  --------------------------------------------------------------------------------
  -- ③ P 的行线性无关: 行的线性组合逐点为零 ⟹ 系数全零
  --------------------------------------------------------------------------------

  -- Σ_b c(i,a,b) ⊗ P(i,a,b) col ≡ c(i,a,k') ⊗ (i = i')(i'' = a)
  collapse-b : ∀ (c : Idx n → Trit) (i a i'' i' k' : Fin n) →
    sumFin (λ b → (c (i , a , b)) ⊗ (oneIf i i' ⊗ (oneIf i'' a ⊗ oneIf b k'))) ≡
    (c (i , a , k')) ⊗ (oneIf i i' ⊗ oneIf i'' a)
  collapse-b c i a i'' i' k' =
    trans (sumFin-cong (λ b →
             TritSolver.solve 4 (λ cc p q s → cc :* (p :* (q :* s)) := (cc :* (p :* q)) :* s)
               refl (c (i , a , b)) (oneIf i i') (oneIf i'' a) (oneIf b k')))
          (collapseʳ (λ b → (c (i , a , b)) ⊗ (oneIf i i' ⊗ oneIf i'' a)) k')

  collapse-a : ∀ (c : Idx n → Trit) (i i'' i' k' : Fin n) →
    sumFin (λ a → (c (i , a , k')) ⊗ (oneIf i i' ⊗ oneIf i'' a)) ≡ (c (i , i'' , k')) ⊗ (oneIf i i')
  collapse-a c i i'' i' k' =
    trans (sumFin-cong (λ a →
             trans (TritSolver.solve 3 (λ cc p q → cc :* (p :* q) := (cc :* p) :* q)
                     refl (c (i , a , k')) (oneIf i i') (oneIf i'' a))
                  (cong (λ v → ((c (i , a , k')) ⊗ (oneIf i i')) ⊗ v) (oneIf-sym i'' a))))
          (collapseʳ (λ a → (c (i , a , k')) ⊗ (oneIf i i')) i'')

  P-collapse : ∀ (c : Idx n → Trit) (col : Idx n) → sumIdx₃ (λ row → (c row) ⊗ P row col) ≡
    c (proj₁ (proj₂ col) , proj₁ col , proj₂ (proj₂ col))
  P-collapse c (i'' , i' , k') =
    trans (sumFin-cong (λ i → trans (sumFin-cong (λ a → collapse-b c i a i'' i' k')) (collapse-a c i i'' i' k')))
          (collapseʳ (λ i → c (i , i'' , k')) i')

  rows-indep : ∀ (c c' : Idx n → Trit) →
    (∀ col → sumIdx₃ (λ row → (c row) ⊗ P row col) ≡ sumIdx₃ (λ row → (c' row) ⊗ P row col)) →
    ∀ row → c row ≡ c' row
  rows-indep c c' h (i , a , b) =
    trans (sym (P-collapse c (a , i , b))) (trans (h (a , i , b)) (P-collapse c' (a , i , b)))

  --------------------------------------------------------------------------------
  -- ④ 行落在 Y 的 N 列张成的空间里
  --------------------------------------------------------------------------------

  -- 三层嵌套和, 指标取科里化: 少写括号
  Σ₃ : (Fin n → Fin n → Fin n → Trit) → Trit
  Σ₃ g = sumFin (λ i → sumFin (λ a → sumFin (λ b → g i a b)))

  Σ₃-sumIdx₃ : ∀ (h : Idx n → Trit) → Σ₃ (λ i a b → h (i , a , b)) ≡ sumIdx₃ h
  Σ₃-sumIdx₃ h = refl

  cong₃ : ∀ {g h : Fin n → Fin n → Fin n → Trit} → (∀ i a b → g i a b ≡ h i a b) → Σ₃ g ≡ Σ₃ h
  cong₃ e = sumFin-cong (λ i → sumFin-cong (λ a → sumFin-cong (λ b → e i a b)))

  -- 左因子提出三层和
  Σ₃-scaleˡ : ∀ (k : Trit) (g : Fin n → Fin n → Fin n → Trit) → k ⊗ Σ₃ g ≡ Σ₃ (λ i a b → k ⊗ (g i a b))
  Σ₃-scaleˡ k g = trans s1 (sumFin-cong s2)
    where
    s1 : k ⊗ Σ₃ g ≡ sumFin (λ i → k ⊗ sumFin (λ a → sumFin (λ b → g i a b)))
    s1 = sym (sumFin-scale k (λ i → sumFin (λ a → sumFin (λ b → g i a b))))
    s2 : ∀ i → k ⊗ sumFin (λ a → sumFin (λ b → g i a b)) ≡
         sumFin (λ a → sumFin (λ b → k ⊗ (g i a b)))
    s2 i = trans (sym (sumFin-scale k (λ a → sumFin (λ b → g i a b))))
                 (sumFin-cong (λ a → sym (sumFin-scale k (λ b → g i a b))))

  -- 右因子送进三层和
  scaleʳ₃ : ∀ (g : Fin n → Fin n → Fin n → Trit) (k : Trit) → (Σ₃ g) ⊗ k ≡ Σ₃ (λ i a b → (g i a b) ⊗ k)
  scaleʳ₃ g k = trans (⊗-comm (Σ₃ g) k) (trans (Σ₃-scaleˡ k g) (cong₃ (λ i a b → ⊗-comm k (g i a b))))

  -- 最外层的 u 依次换过 i、a、b 三层
  Σ₃-swap : ∀ (H : Fin N → Fin n → Fin n → Fin n → Trit) →
    sumFin (λ u → Σ₃ (H u)) ≡ Σ₃ (λ i a b → sumFin (λ u → H u i a b))
  Σ₃-swap H = trans q1 (sumFin-cong q2)
    where
    q1 : sumFin (λ u → Σ₃ (H u)) ≡ sumFin (λ i → sumFin (λ u → sumFin (λ a → sumFin (λ b → H u i a b))))
    q1 = sumFin-swap-plain n N (λ i u → sumFin (λ a → sumFin (λ b → H u i a b)))
    q2 : ∀ i → sumFin (λ u → sumFin (λ a → sumFin (λ b → H u i a b))) ≡
         sumFin (λ a → sumFin (λ b → sumFin (λ u → H u i a b)))
    -- where 块里后定义的名字前面用不了: 先写内层两步, 再写 q2
    swapA : ∀ i → sumFin (λ u → sumFin (λ a → sumFin (λ b → H u i a b))) ≡
            sumFin (λ a → sumFin (λ u → sumFin (λ b → H u i a b)))
    swapA i = sumFin-swap-plain n N (λ a u → sumFin (λ b → H u i a b))
    swapB : ∀ i a → sumFin (λ u → sumFin (λ b → H u i a b)) ≡ sumFin (λ b → sumFin (λ u → H u i a b))
    swapB i a = sumFin-swap-plain n N (λ b u → H u i a b)
    q2 i = trans (swapA i) (sumFin-cong (swapB i))

  -- c 在 X 系数下的坐标
  coord : (Idx n → Trit) → Fin N → Trit
  coord c u = Σ₃ (λ i a b → c (i , a , b) ⊗ X (i , a , b) u)

  -- 固定一行: Σ_u (c ⊗ X) ⊗ Y ≡ c ⊗ Σ_u X ⊗ Y
  row-step : ∀ (c : Idx n → Trit) (col : Idx n) (row : Idx n) →
    sumFin (λ u → ((c row) ⊗ (X row u)) ⊗ (Y col u)) ≡ (c row) ⊗ sumFin (λ u → (X row u) ⊗ (Y col u))
  row-step c col row = trans s1 s2
    where
    s1 : sumFin (λ u → ((c row) ⊗ (X row u)) ⊗ (Y col u)) ≡ sumFin (λ u → (c row) ⊗ ((X row u) ⊗ (Y col u)))
    s1 = sumFin-cong (λ u → ⊗-assoc (c row) (X row u) (Y col u))
    s2 : sumFin (λ u → (c row) ⊗ ((X row u) ⊗ (Y col u))) ≡ (c row) ⊗ sumFin (λ u → (X row u) ⊗ (Y col u))
    s2 = sumFin-scale (c row) (λ u → (X row u) ⊗ (Y col u))

  -- ★ 用 Y 的列重组: Σ_u coord c u ⊗ Y col u = Σ_{i,a,b} c ⊗ Σ_u X ⊗ Y
  row-expand : ∀ (c : Idx n → Trit) (col : Idx n) →
    sumFin (λ u → (coord c u) ⊗ (Y col u)) ≡ Σ₃ (λ i a b → c (i , a , b) ⊗ sumFin (λ u → (X (i , a , b) u) ⊗ (Y col u)))
  row-expand c col = trans e1 (trans e2 e3)
    where
    e1u : ∀ u → (coord c u) ⊗ (Y col u) ≡ Σ₃ (λ i a b → ((c (i , a , b)) ⊗ (X (i , a , b) u)) ⊗ (Y col u))
    e1u u = scaleʳ₃ (λ i a b → c (i , a , b) ⊗ X (i , a , b) u) (Y col u)
    e1 : sumFin (λ u → (coord c u) ⊗ (Y col u)) ≡
         sumFin (λ u → Σ₃ (λ i a b → ((c (i , a , b)) ⊗ (X (i , a , b) u)) ⊗ (Y col u)))
    e1 = sumFin-cong e1u
    e2 : sumFin (λ u → Σ₃ (λ i a b → ((c (i , a , b)) ⊗ (X (i , a , b) u)) ⊗ (Y col u))) ≡
         Σ₃ (λ i a b → sumFin (λ u → ((c (i , a , b)) ⊗ (X (i , a , b) u)) ⊗ (Y col u)))
    e2 = Σ₃-swap (λ u i a b → ((c (i , a , b)) ⊗ (X (i , a , b) u)) ⊗ (Y col u))
    e3 : Σ₃ (λ i a b → sumFin (λ u → ((c (i , a , b)) ⊗ (X (i , a , b) u)) ⊗ (Y col u))) ≡
         Σ₃ (λ i a b → c (i , a , b) ⊗ sumFin (λ u → (X (i , a , b) u) ⊗ (Y col u)))
    e3 = cong₃ (λ i a b → row-step c col (i , a , b))

  --------------------------------------------------------------------------------
  -- ⑤ 计数
  --------------------------------------------------------------------------------

  idx : Idx n → Fin (n * (n * n))
  idx (i , a , b) = combine i (combine a b)

  idx-surjective : ∀ (x : Fin (n * (n * n))) → Σ (Idx n) (λ row → idx row ≡ x)
  idx-surjective x with combine-surjective x
  ... | j , k , e1 with combine-surjective k
  ...   | a , b , e2 = (j , a , b) , trans (cong (combine j) e2) e1

  -- 嵌入 Fin (3^(n³)) → Fin (3^N)
  φ : Fin (3 ^ (n * (n * n))) → Fin (3 ^ N)
  φ κ = fromFun N (coord (λ row → toFun (n * (n * n)) κ (idx row)))

  φ-injective : Injective _≡_ _≡_ φ
  φ-injective {κ} {κ'} e = κ≡κ'
    where
    c : Idx n → Trit
    c row = toFun (n * (n * n)) κ (idx row)

    c' : Idx n → Trit
    c' row = toFun (n * (n * n)) κ' (idx row)

    -- 坐标逐项相同
    coord-eq : ∀ u → (coord c u) ≡ (coord c' u)
    coord-eq u =
      trans (sym (toFun-fromFun N (coord c) u))
            (trans (cong (λ z → toFun N z u) e) (toFun-fromFun N (coord c') u))

    col-eq : ∀ col → sumFin (λ u → (coord c u) ⊗ (Y col u)) ≡ sumFin (λ u → (coord c' u) ⊗ (Y col u))
    col-eq col = sumFin-cong (λ u → cong₂ _⊗_ (coord-eq u) refl)

    -- 两边都用 P = X·Yᵀ 与行展开化成同一形状
    hyp : ∀ col → sumIdx₃ (λ row → (c row) ⊗ P row col) ≡ sumIdx₃ (λ row → (c' row) ⊗ P row col)
    hyp col = trans (sym (Σ₃-sumIdx₃ lhs)) (trans hyp₃ (Σ₃-sumIdx₃ rhs))
      where
      -- 两侧化成 Σ₃ 形状
      lhs : Idx n → Trit
      lhs row = c row ⊗ P row col
      rhs : Idx n → Trit
      rhs row = c' row ⊗ P row col
      hyp₃ : Σ₃ (λ i a b → c (i , a , b) ⊗ P (i , a , b) col) ≡ Σ₃ (λ i a b → c' (i , a , b) ⊗ P (i , a , b) col)
      -- Σ₃ (c ⊗ P) → Σ₃ (c ⊗ Σ_u X ⊗ Y) → Σ_u coord c u ⊗ Y → Σ_u coord c' u ⊗ Y → … → Σ₃ (c' ⊗ P)
      hyp₃ = trans (cong₃ toSum) (trans (sym (row-expand c col))
                  (trans (col-eq col) (trans (row-expand c' col) (cong₃ fromSum))))
        where
        toSum : ∀ i a b → c (i , a , b) ⊗ P (i , a , b) col ≡
                c (i , a , b) ⊗ sumFin (λ u → (X (i , a , b) u) ⊗ (Y col u))
        toSum i a b = cong (λ v → c (i , a , b) ⊗ v) (P-factor (i , a , b) col)
        fromSum : ∀ i a b → c' (i , a , b) ⊗ sumFin (λ u → (X (i , a , b) u) ⊗ (Y col u)) ≡
                  c' (i , a , b) ⊗ P (i , a , b) col
        fromSum i a b = sym (toSum' i a b)
          where
          toSum' : ∀ i a b → c' (i , a , b) ⊗ P (i , a , b) col ≡
                   c' (i , a , b) ⊗ sumFin (λ u → (X (i , a , b) u) ⊗ (Y col u))
          toSum' i a b = cong (λ v → c' (i , a , b) ⊗ v) (P-factor (i , a , b) col)

    row-eq : ∀ row → c row ≡ c' row
    row-eq row = rows-indep c c' hyp row

    -- 指标 x 被 idx 取满, 所以 toFun 逐点相同
    x-eq : ∀ x → toFun (n * (n * n)) κ x ≡ toFun (n * (n * n)) κ' x
    x-eq x with idx-surjective x
    ... | row , er =
      trans (sym (cong (toFun (n * (n * n)) κ) er)) (trans (row-eq row) (cong (toFun (n * (n * n)) κ') er))

    κ≡κ' : κ ≡ κ'
    κ≡κ' =
      -- κ ≡ fromFun (toFun κ) ≡ fromFun (toFun κ') ≡ κ'
      trans (sym (fromFun-toFun (n * (n * n)) κ))
            (trans (fromFun-cong (n * (n * n)) (toFun (n * (n * n)) κ) (toFun (n * (n * n)) κ') x-eq)
                   (fromFun-toFun (n * (n * n)) κ'))

  -- ★★ n³ ≤ N
  budget : n * (n * n) ≤ N
  budget = ≮⇒≥ contra
    where
    contra : N < n * (n * n) → ⊥
    contra hlt = <⇒≱ (3^-mono-< hlt) (injective⇒≤ φ-injective)

--------------------------------------------------------------------------------
-- §6 主定理
--------------------------------------------------------------------------------

-- ★★ 秩预算: 首因子由 N 个秩一片块拼成 ⟹ n³ ≤ N
rank-budget : ∀ n r N (ρ : RankLE (Pos n) (Pos n) (Out n) (mm n) r) →
  Pieces n N r (ra ρ) → n * n * n ≤ N
-- 结论里的 n * n * n 是左结合的 (n * n) * n; 证明里用的是 n * (n * n), 差一个 *-assoc
rank-budget n r N ρ pc = subst (_≤ N) (sym (*-assoc n n n)) (Budget.budget n r N ρ pc)
