{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3
-- M16-B: 展平下界 —— GF(3) 上 n×n 矩阵乘法张量的 r 项秩分解必满足 n² ≤ r（计数证法）
--
-- 数学背景
--   设 ⟨n,n,n⟩ 的结构常数 T(x,y,z) = [x.1 = z.1][x.2 = y.1][y.2 = z.2] 有 r 项分解
--     Σ_k a k x ⊗ b k y ⊗ c k z ≡ T(x,y,z)。
--   取定 k : Fin n。对每个位置 x₀ 令 y₀ = (x₀.2, k)、z₀ = (x₀.1, k), 则对一切 x
--     Σ_i (w x₀ i) ⊗ (a i x) ≡ [x = x₀],   其中 w x₀ i = b i y₀ ⊗ c i z₀。
--   即 n² 个标准基向量全部落在 span{a 0, …, a (r−1)} 里。标准基张成一切, 所以每个
--   v : Pos n → Trit 都有「坐标」t v : Fin r → Trit 使 Σ_i (t v i) ⊗ (a i x) ≡ v x。
--   计数: (Pos n → Trit) 有 3^(n²) 个元素, (Fin r → Trit) 有 3^r 个; 「每 v 都有原像」
--   给出单射 Fin (3^(n²)) → Fin (3^r), 故 3^(n²) ≤ 3^r, 即 n² ≤ r。
--
-- 为什么用计数、不用矩阵秩
--   Lean 对应件 `MatrixExponent/Flattening.lean:6 rank_lower` 走展平后矩阵的秩
--   (`Rectangle.RankLE.area`)。本库没有矩阵秩的不变性理论; 这里用有限域才有的办法 ——
--   基数比较代替维数比较(`GF3RankNullity` 的「基数版维数」口径)。
--
-- 内容
--   §1 Trit 值 sumFin 的分配 / 提公因子 / 双和交换
--   §2 oneIf 与 δc 的关系
--   §3 给定秩分解: 标准基落在张成里 ⟹ 一切函数都在张成里 (★ span-full)
--   §4 计数: 单射 ⟹ 3^(n²) ≤ 3^r ⟹ ★ rank-lower : n² ≤ r
--
-- 诚实边界
--   · 只对 GF(3) 陈述(计数用了 |Trit| = 3); Lean 的陈述对任意域。
--   · 这是经典的展平界, 不是外部定理的一部分。n = 2 处: 本件给 r ≥ 4, Strassen(M13)给 r ≤ 7。
--   · 「n = 2 时秩恰为 7」已证: TensorRankHK2GF3.rank₂₂₂-is-7（Hopcroft–Kerr 的排除论证,
--     下半 rank-2x2-lower : ∀ r → RankLE₃ 2 r → 7 ≤ r, 2026-11-28）。本件的界（4）比它弱, 两者相容
--     （TensorRankHK2GF3.check-weaker 把本件的界作用在同一个分解上）。
--   · 外部定理(`TensorRankGF3.ω₃-boundary`, 全称句)本件**没有**推进: 它要求 n^9 ≤ r^4。
--
-- 复用(先查后写): sumFin-add(GF3RankNullity) / sumFin-δ(GF3Dim) / fromFun·toFun 往返
--   (GF3Count) / fromFun-cong(GF3BasisCount) / 3^-mono-<(GF3RankNullity) /
--   injective⇒≤·combine-surjective(stdlib) / oneIf·RankLE₃·cong₁(TensorRankGF3)。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3 where

open import Data.Nat using (ℕ; zero; suc; _*_; _^_; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (<⇒≱; ≮⇒≥)
open import Data.Fin using (Fin; combine) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; injective⇒≤; combine-surjective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; _⊕_; _⊗_
  ; ⊗-identityʳ; ⊗-comm; ⊗-assoc; ⊗-zeroˡ; ⊗-zeroʳ
  ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong; sumFin-zero)
open import Sovereign.Algebra.LinearAlgebra.GF3Dim using (δc; δc-self; δc-neq; sumFin-δ)
open import Sovereign.Algebra.LinearAlgebra.GF3Count
  using (fromFun; toFun; fromFun-toFun; toFun-fromFun)
open import Sovereign.Algebra.LinearAlgebra.GF3BasisCount using (fromFun-cong)
open import Sovereign.Algebra.LinearAlgebra.GF3RankNullity using (sumFin-add; 3^-mono-<)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3
  using (Pos; Out; oneIf; mm; RankLE₃; rank-strassen; cong₁)

-- record 字段不随模块按名字导出, 本地打开 record 模块(不 public: 不转出口)
open RankLE₃ using (ra; rb; rc; rank-eq)

--------------------------------------------------------------------------------
-- §1. Trit 值 sumFin 的三条线性律
--------------------------------------------------------------------------------

-- 右分配进求和: Σ (u i ⊕ v i) ⊗ c i ≡ (Σ u i ⊗ c i) ⊕ (Σ v i ⊗ c i)
--   (逐点用 ⊗-distribʳ-⊕, 再用库内已有的 sumFin-add)
sumFin-distrʳ : ∀ {r} (u v c : Fin r → Trit) →
  sumFin (λ i → ((u i ⊕ v i) ⊗ c i)) ≡
  (sumFin (λ i → (u i ⊗ c i))) ⊕ (sumFin (λ i → (v i ⊗ c i)))
sumFin-distrʳ u v c =
  trans (sumFin-cong (λ i → ⊗-distribʳ-⊕ (u i) (v i) (c i)))
        (sumFin-add (λ i → (u i ⊗ c i)) (λ i → (v i ⊗ c i)))

-- 提左公因子(右结合形): Σ (k ⊗ (u i ⊗ c i)) ≡ k ⊗ Σ (u i ⊗ c i)
sumFin-scale₃ : ∀ {r} (k : Trit) (u c : Fin r → Trit) →
  sumFin (λ i → (k ⊗ ((u i) ⊗ (c i)))) ≡ k ⊗ sumFin (λ i → ((u i) ⊗ (c i)))
sumFin-scale₃ {zero} k u c = sym (⊗-zeroʳ k)
sumFin-scale₃ {suc r} k u c =
  trans (cong₁ (k ⊗ ((u fzero) ⊗ (c fzero)))
               (sumFin (λ i → (k ⊗ ((u (fsuc i)) ⊗ (c (fsuc i))))))
               (k ⊗ sumFin (λ i → ((u (fsuc i)) ⊗ (c (fsuc i)))))
               (sumFin-scale₃ k (λ i → u (fsuc i)) (λ i → c (fsuc i))))
        (sym (⊗-distribˡ-⊕ k ((u fzero) ⊗ (c fzero))
                          (sumFin (λ i → ((u (fsuc i)) ⊗ (c (fsuc i)))))))

-- 双和交换(Fubini): Σ_i (Σ_q g q i) ⊗ c i ≡ Σ_q Σ_i (g q i ⊗ c i)
--   对 m 归纳; 零位: 内和为 T₀, ⊗-zeroˡ 把每项化成 T₀, 再 sumFin-zero
sumFin-swap₃ : ∀ m r (g : Fin m → Fin r → Trit) (c : Fin r → Trit) →
  sumFin (λ i → ((sumFin (λ q → g q i)) ⊗ c i)) ≡
  sumFin (λ q → sumFin (λ i → ((g q i) ⊗ c i)))
sumFin-swap₃ zero r g c =
  trans (sumFin-cong {n = r} {g = λ i → ((sumFin (λ q → g q i)) ⊗ (c i))} {h = λ i → T₀}
                     (λ i → ⊗-zeroˡ (c i)))
        (sumFin-zero {n = r})
sumFin-swap₃ (suc m) r g c =
  trans (sumFin-distrʳ (λ i → g fzero i) (λ i → sumFin (λ q → g (fsuc q) i)) c)
    (trans (cong₁ (sumFin (λ i → ((g fzero i) ⊗ (c i))))
                  (sumFin (λ i → ((sumFin (λ q → g (fsuc q) i)) ⊗ (c i))))
                  (sumFin (λ q → sumFin (λ i → ((g (fsuc q) i) ⊗ (c i)))))
                  (sumFin-swap₃ m r (λ q i → g (fsuc q) i) c))
          refl)

--------------------------------------------------------------------------------
-- §2. oneIf(指示函数) 与 δc(库内标准基) 的关系
--------------------------------------------------------------------------------

oneIf-refl : ∀ {n} (i : Fin n) → oneIf i i ≡ T₁
oneIf-refl i with i ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

oneIf-δc : ∀ {n} (i j : Fin n) → oneIf i j ≡ δc i j
oneIf-δc i j with i ≟ j
... | yes _ = refl
... | no  _ = refl

-- δc 对称
δc-sym : ∀ {n} (i j : Fin n) → δc i j ≡ δc j i
δc-sym i j with i ≟ j
... | yes p   = sym (trans (cong (δc j) p) (δc-self j))
... | no  ¬p  = sym (δc-neq j i (λ q → ¬p (sym q)))

-- 三因子轮换: a ⊗ (b ⊗ c) ≡ c ⊗ (a ⊗ b)
⊗-rot : ∀ a b c → (a ⊗ (b ⊗ c)) ≡ (c ⊗ (a ⊗ b))
⊗-rot a b c = trans (sym (⊗-assoc a b c)) (⊗-comm (a ⊗ b) c)

--------------------------------------------------------------------------------
-- §3. 给定秩分解: 标准基落在张成里 ⟹ 一切函数都在张成里
--------------------------------------------------------------------------------

-- 对位置的双重求和(先行后列)
sumX : ∀ {n} → (Pos n → Trit) → Trit
sumX {n} f = sumFin (λ p → sumFin (λ q → f (p , q)))

-- 双重求和的交换: Σ_i (Σ_{x₀} h x₀ i) ⊗ c i ≡ Σ_{x₀} Σ_i (h x₀ i ⊗ c i)
sumX-swap : ∀ {n r} (h : Pos n → Fin r → Trit) (c : Fin r → Trit) →
  sumFin (λ i → ((sumX (λ x₀ → h x₀ i)) ⊗ c i)) ≡
  sumX (λ x₀ → sumFin (λ i → (h x₀ i ⊗ c i)))
sumX-swap {n} {r} h c =
  trans (sumFin-swap₃ n r (λ p i → sumFin (λ q → h (p , q) i)) c)
        (sumFin-cong (λ p → sumFin-swap₃ n r (λ q i → h (p , q) i) c))

module Span (n r : ℕ) (ρ : RankLE₃ n r) (k : Fin n) where

  -- 从秩分解读出的权: w x₀ i = (b i 在 (x₀.2 , k) 处) ⊗ (c i 在 (x₀.1 , k) 处)
  w : Pos n → Fin r → Trit
  w x₀ i = (rb ρ i (proj₂ x₀ , k)) ⊗ (rc ρ i (proj₁ x₀ , k))

  -- 指示函数(标准基向量), 用库内 δc 写
  e : Pos n → Pos n → Trit
  e x₀ x = (δc (proj₁ x₀) (proj₁ x)) ⊗ (δc (proj₂ x₀) (proj₂ x))

  -- 张量在 (y₀ , z₀) 处的值就是指示函数
  mm-e : ∀ x₀ x → mm n x (proj₂ x₀ , k) (proj₁ x₀ , k) ≡ e x₀ x
  mm-e x₀ x =
    trans (cong (λ z → ((oneIf (proj₁ x) (proj₁ x₀)) ⊗ z))
                (trans (cong (λ z → ((oneIf (proj₂ x) (proj₂ x₀)) ⊗ z)) (oneIf-refl k))
                       (⊗-identityʳ (oneIf (proj₂ x) (proj₂ x₀)))))
          (cong₂ _⊗_ (trans (oneIf-δc (proj₁ x) (proj₁ x₀)) (δc-sym (proj₁ x) (proj₁ x₀)))
                     (trans (oneIf-δc (proj₂ x) (proj₂ x₀)) (δc-sym (proj₂ x) (proj₂ x₀))))

  -- ★ 标准基落在 span{a i} 里: Σ_i (w x₀ i) ⊗ (a i x) ≡ e x₀ x
  basis-in-span : ∀ x₀ x → sumFin (λ i → ((w x₀ i) ⊗ (ra ρ i x))) ≡ e x₀ x
  basis-in-span x₀ x =
    trans (sym (sumFin-cong {g = λ i → ((ra ρ i x) ⊗ (w x₀ i))}
                            {h = λ i → ((w x₀ i) ⊗ (ra ρ i x))}
                            (λ i → ⊗-comm (ra ρ i x) (w x₀ i))))
          (trans (rank-eq ρ x (proj₂ x₀ , k) (proj₁ x₀ , k)) (mm-e x₀ x))

  -- δ 的两次消化: 先列后行。sumFin-δ 的形状是「δc 固定指标 求和变量 ⊗ 被加项」,
  -- 而和项里 δc 是「求和变量 固定指标」且不在首位 —— 先 δc-sym 翻转, 再挪到首位
  -- 单个和项的整理
  summand-rot : ∀ (v : Pos n → Trit) (p q p₀ q₀ : Fin n) →
    ((v (p₀ , q₀)) ⊗ ((δc p₀ p) ⊗ (δc q₀ q))) ≡ ((δc q q₀) ⊗ ((v (p₀ , q₀)) ⊗ (δc p₀ p)))
  summand-rot v p q p₀ q₀ =
    trans (cong (λ z → ((v (p₀ , q₀)) ⊗ ((δc p₀ p) ⊗ z))) (δc-sym q₀ q))
          (⊗-rot (v (p₀ , q₀)) (δc p₀ p) (δc q q₀))

  -- 列和: 消化 δc q ·
  d1 : ∀ (v : Pos n → Trit) (p q : Fin n) → sumX (λ x₀ → ((v x₀) ⊗ (e x₀ (p , q)))) ≡
       sumFin (λ p₀ → ((v (p₀ , q)) ⊗ (δc p₀ p)))
  d1 v p q =
    sumFin-cong (λ p₀ → trans (sumFin-cong (λ q₀ → summand-rot v p q p₀ q₀))
                              (sumFin-δ (λ q₀ → ((v (p₀ , q₀)) ⊗ (δc p₀ p))) q))

  -- 行和: 消化 δc p ·
  d2 : ∀ (v : Pos n → Trit) (p q : Fin n) → sumFin (λ p₀ → ((v (p₀ , q)) ⊗ (δc p₀ p))) ≡ v (p , q)
  d2 v p q =
    trans (sumFin-cong (λ p₀ → trans (⊗-comm (v (p₀ , q)) (δc p₀ p))
                                     (cong (λ z → (z ⊗ (v (p₀ , q)))) (δc-sym p₀ p))))
          (sumFin-δ (λ p₀ → v (p₀ , q)) p)

  delta : ∀ v x → sumX (λ x₀ → ((v x₀) ⊗ (e x₀ x))) ≡ v x
  delta v (p , q) = trans (d1 v p q) (d2 v p q)

  -- v 的坐标: t v i = Σ_{x₀} (v x₀) ⊗ (w x₀ i)
  t : (Pos n → Trit) → Fin r → Trit
  t v i = sumX (λ x₀ → (v x₀) ⊗ (w x₀ i))

  -- 四步链, 每步单独给类型(避免 Agda 在元变量位置猜类型)
  s1 : ∀ (v : Pos n → Trit) (x : Pos n) → sumFin (λ i → ((t v i) ⊗ (ra ρ i x))) ≡
                sumX (λ x₀ → sumFin (λ i → (((v x₀) ⊗ (w x₀ i)) ⊗ (ra ρ i x))))
  s1 v x = sumX-swap (λ x₀ i → (v x₀) ⊗ (w x₀ i)) (λ i → ra ρ i x)

  s2 : ∀ (v : Pos n → Trit) (x : Pos n) → sumX (λ x₀ → sumFin (λ i → (((v x₀) ⊗ (w x₀ i)) ⊗ (ra ρ i x)))) ≡
                sumX (λ x₀ → sumFin (λ i → ((v x₀) ⊗ ((w x₀ i) ⊗ (ra ρ i x)))))
  s2 v x = sumFin-cong (λ p → sumFin-cong (λ q →
             sumFin-cong (λ i → ⊗-assoc (v (p , q)) (w (p , q) i) (ra ρ i x))))

  s3 : ∀ (v : Pos n → Trit) (x : Pos n) → sumX (λ x₀ → sumFin (λ i → ((v x₀) ⊗ ((w x₀ i) ⊗ (ra ρ i x))))) ≡
                sumX (λ x₀ → (v x₀) ⊗ sumFin (λ i → ((w x₀ i) ⊗ (ra ρ i x))))
  s3 v x = sumFin-cong (λ p → sumFin-cong (λ q →
             sumFin-scale₃ (v (p , q)) (λ i → w (p , q) i) (λ i → ra ρ i x)))

  s4 : ∀ (v : Pos n → Trit) (x : Pos n) → sumX (λ x₀ → (v x₀) ⊗ sumFin (λ i → ((w x₀ i) ⊗ (ra ρ i x)))) ≡
                sumX (λ x₀ → (v x₀) ⊗ (e x₀ x))
  s4 v x = sumFin-cong (λ p → sumFin-cong (λ q →
             cong (λ z → (v (p , q)) ⊗ z) (basis-in-span (p , q) x)))

  -- ★★ 一切函数都在张成里: Σ_i (t v i) ⊗ (a i x) ≡ v x
  span-full : ∀ v x → sumFin (λ i → ((t v i) ⊗ (ra ρ i x))) ≡ v x
  span-full v x = trans (s1 v x) (trans (s2 v x) (trans (s3 v x) (trans (s4 v x) (delta v x))))

  --------------------------------------------------------------------------------
  -- §4. 计数: 单射 Fin (3^(n²)) → Fin (3^r) ⟹ 3^(n²) ≤ 3^r
  --------------------------------------------------------------------------------

  -- 解码: Fin (3^(n²)) 上的系数 ↦ 函数(位置按 combine 编号)
  dec : Fin (3 ^ (n * n)) → Pos n → Trit
  dec kk x = toFun (n * n) kk (combine (proj₁ x) (proj₂ x))

  -- v ↦ 其坐标的编码; span-full 说它把 dec kk 送到一个原像上
  φ : Fin (3 ^ (n * n)) → Fin (3 ^ r)
  φ kk = fromFun r (t (dec kk))

  -- 单射: 坐标相同 ⟹ 函数逐点相同 ⟹ 编号全同 ⟹ 原下标相同
  φ-injective : Injective _≡_ _≡_ φ
  φ-injective {kk} {ll} h =
    trans (sym (fromFun-toFun (n * n) kk))
      (trans (fromFun-cong (n * n) (toFun (n * n) kk) (toFun (n * n) ll) all-eq)
             (fromFun-toFun (n * n) ll))
    where
    -- (1) 坐标逐点相同
    t-eq : ∀ i → (t (dec kk)) i ≡ (t (dec ll)) i
    t-eq i = trans (sym (toFun-fromFun r (t (dec kk)) i))
      (trans (cong (λ z → toFun r z i) h) (toFun-fromFun r (t (dec ll)) i))
    -- (2) 函数逐点相同(两边都是各自的原像)
    dec-eq : ∀ x → (dec kk) x ≡ (dec ll) x
    dec-eq x = trans (sym (span-full (dec kk) x))
      (trans (sumFin-cong (λ i → cong (λ z → (z ⊗ (ra ρ i x))) (t-eq i)))
             (span-full (dec ll) x))
    -- (3) 全部编号相同(combine 满)
    all-eq : ∀ c → toFun (n * n) kk c ≡ toFun (n * n) ll c
    all-eq c with combine-surjective c
    ... | j , l , hjl = trans (sym (cong (toFun (n * n) kk) hjl))
                              (trans (dec-eq (j , l)) (cong (toFun (n * n) ll) hjl))

  -- ★ 计数不等式
  count : 3 ^ (n * n) ≤ 3 ^ r
  count = injective⇒≤ φ-injective

--------------------------------------------------------------------------------
-- ★★ 展平下界
--------------------------------------------------------------------------------

rank-lower : ∀ n r → RankLE₃ n r → n * n ≤ r
rank-lower zero r ρ = z≤n
rank-lower (suc n′) r ρ = ≮⇒≥ contra
  where
  contra : r < suc n′ * suc n′ → ⊥
  contra hlt = <⇒≱ (3^-mono-< hlt) (Span.count (suc n′) r ρ fzero)

-- 对 M13 的实例: Strassen 分解满足 4 ≤ 7 (定理作用于库内真实的分解, 不是空转)
check-lower-strassen : 2 * 2 ≤ 7
check-lower-strassen = rank-lower 2 7 rank-strassen
