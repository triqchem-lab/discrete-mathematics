{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankPowGF3
-- M16-C: 秩相乘与取幂 —— GF(3) 上两个秩分解的张量积仍是秩分解; 由此 M13 给出每个尺寸 2^k 的见证
--
-- 数学背景
--   张量积 ⟨n,n,n⟩ ⊗ ⟨m,m,m⟩ = ⟨nm,nm,nm⟩: 位置按 combine 配对, 结构常数相乘
--     T_{nm}((x₁,x₂),(y₁,y₂),(z₁,z₂)) = T_n(x₁,y₁,z₁) ⊗ T_m(x₂,y₂,z₂)。
--   若 ⟨n⟩ 有 r 项分解、⟨m⟩ 有 s 项分解, 把系数按项配对相乘, 就得到 ⟨nm⟩ 的 r·s 项分解:
--     Σ_{i₁,i₂} (a₁a₂)(b₁b₂)(c₁c₂) = (Σ_{i₁} a₁b₁c₁) ⊗ (Σ_{i₂} a₂b₂c₂)。
--
-- 为什么有这一件
--   Lean 对应件 `MatrixExponent/RankPower.lean`: `rank_mul`(:12)、`rank_pow`(:15)。
--   （同文件另有 `rank_map`(:9), 沿环同态搬运分解; 本库的谓词只在 GF(3) 上, 没有可搬运的目标域, 不做。）
--   本库此前只有 n = 2 一个见证（M16-A 的 rank-strassen）; 本件之后每个尺寸 2^k 都有内核检查过的见证。
--
-- 内容
--   §1 sumFin 的左 / 右缩放、Fin (a + b) 的拆分、Fin (a · b) 按 combine 的重排
--   §2 oneIf 的三条引理: oneIf-yes / oneIf-no / oneIf-combine
--   §3 给定两个分解: ★ rank-eq×（张量积满足结构常数方程）
--   §4 ★ rank-mul / rank-one / ★ rank-pow / rank-strassen-pow / 有限证书 strassen-certificate
--   §5 与展平下界（TensorRankFlattenGF3）的组合: 每个张量幂见证都满足 n² ≤ r
--
-- 诚实边界
--   · 只对 GF(3); Lean 的陈述对任意域。
--   · strassen-certificate 是一条算术不等式 ((7 ^ k) ^ 6 ≤ (2 ^ k) ^ 17)。把它读成「GF(3) 上 ω ≤ 17/6」
--     是阅读层的 [手工论证·未验证]——本库没有 Lean `formalOmega` 那套定义, 这不是它的形式化推论。
--   · 本件**不**推进外部定理 ω₃-boundary（n^9 ≤ r^4）: 它给的是另一个方向（存在性）的见证。
--
-- 复用(先查后写): ⊗-4swap(Algebra/Jacobian/Matrix.agda:311) / sumFin·sumFin-cong(GF3LaplacianN) /
--   combine·remQuot 及往返引理(stdlib) / oneIf·mm·RankLE₃·rank-strassen(TensorRankGF3)。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankPowGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; m≤m+n; *-comm; ^-*-assoc; ^-monoˡ-≤)
open import Data.Fin using (Fin; combine; remQuot; _↑ˡ_; _↑ʳ_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; combine-injective; remQuot-combine; combine-remQuot)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; _⊕_; _⊗_; ⊕-identityˡ; ⊕-assoc; ⊗-assoc; ⊗-comm; ⊗-zeroʳ; ⊗-distribˡ-⊕)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3
  using (Pos; Out; oneIf; mm; RankLE₃; rank-strassen)
open import Sovereign.Algebra.Jacobian.Matrix using (⊗-4swap)

-- record 字段不随模块按名字导出, 本地打开 record 模块（不 public: 不转出口）
open RankLE₃ using (ra; rb; rc; rank-eq)

--------------------------------------------------------------------------------
-- §1. sumFin 的缩放与重排
--------------------------------------------------------------------------------

-- 左缩放: Σ (k ⊗ f i) ≡ k ⊗ Σ f
sumFin-⊗ˡ : ∀ {d} (k : Trit) (f : Fin d → Trit) →
  sumFin (λ i → (k ⊗ (f i))) ≡ k ⊗ sumFin f
sumFin-⊗ˡ {zero} k f = sym (⊗-zeroʳ k)
sumFin-⊗ˡ {suc d} k f =
  trans (cong (λ t → (k ⊗ (f fzero)) ⊕ t) (sumFin-⊗ˡ k (λ i → f (fsuc i))))
        (sym (⊗-distribˡ-⊕ k (f fzero) (sumFin (λ i → f (fsuc i)))))

-- 右缩放: Σ (f i ⊗ k) ≡ (Σ f) ⊗ k
sumFin-⊗ʳ : ∀ {d} (f : Fin d → Trit) (k : Trit) →
  sumFin (λ i → ((f i) ⊗ k)) ≡ (sumFin f) ⊗ k
sumFin-⊗ʳ f k =
  trans (sumFin-cong {g = λ i → ((f i) ⊗ k)} {h = λ i → (k ⊗ (f i))} (λ i → ⊗-comm (f i) k))
        (trans (sumFin-⊗ˡ k f) (⊗-comm k (sumFin f)))

-- uncurry combine 在配对上就是 combine 本身（stdlib 的 combine-remQuot 用 uncurry 写）
uncurry-combine-proj : ∀ {a b} (p : Fin a × Fin b) →
  (uncurry combine p) ≡ (combine (proj₁ p) (proj₂ p))
uncurry-combine-proj (i , j) = refl

-- Fin (a + b) 上的和拆成「低 b 个」⊕「高 a 个」
--   对 a 归纳; 零位: 高位部分为空, T₀ ⊕ Σ ≡ Σ
sumFin-↑ : ∀ (a b : ℕ) (G : Fin (a + b) → Trit) →
  sumFin G ≡ (sumFin (λ i → G (i ↑ˡ b))) ⊕ (sumFin (λ j → G (a ↑ʳ j)))
sumFin-↑ zero b G = sym (⊕-identityˡ (sumFin G))
sumFin-↑ (suc a) b G =
  trans (cong (λ t → (G fzero) ⊕ t) (sumFin-↑ a b (λ i → G (fsuc i))))
        (sym (⊕-assoc (G fzero) (sumFin (λ i → G (fsuc (i ↑ˡ b))))
                      (sumFin (λ j → G (fsuc (a ↑ʳ j))))))

-- Fin (a · b) 上的和按 combine 重排成双重和
--   suc a 位: combine fzero j = j ↑ˡ (a · b)（低段）, combine (fsuc i) j = b ↑ʳ (combine i j)（高段）
sumFin-combine : ∀ (a b : ℕ) (G : Fin (a * b) → Trit) →
  sumFin {a * b} G ≡ sumFin {a} (λ i → sumFin {b} (λ j → G (combine i j)))
sumFin-combine zero b G = refl
sumFin-combine (suc a) b G =
  trans (sumFin-↑ b (a * b) G)
        (cong (λ t → (sumFin {b} (λ j → G (j ↑ˡ (a * b)))) ⊕ t)
              (sumFin-combine a b (λ t → G (b ↑ʳ t))))

--------------------------------------------------------------------------------
-- §2. oneIf 的三条引理
--------------------------------------------------------------------------------

oneIf-yes : ∀ {d} (u v : Fin d) → u ≡ v → oneIf u v ≡ T₁
oneIf-yes u v e with u ≟ v
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p e)

oneIf-no : ∀ {d} (u v : Fin d) → u ≢ v → oneIf u v ≡ T₀
oneIf-no u v ne with u ≟ v
... | yes p = ⊥-elim (ne p)
... | no  _ = refl

-- 指示函数在 combine 下分解: [combine i i′ = combine j j′] ≡ [i = j] ⊗ [i′ = j′]
--   左右各按两个分量判定; 任一分量不同时, 用 combine 的单射性排除左边相等
oneIf-combine : ∀ {a b} (i j : Fin a) (i′ j′ : Fin b) →
  oneIf (combine i i′) (combine j j′) ≡ (oneIf i j) ⊗ (oneIf i′ j′)
oneIf-combine i j i′ j′ with i ≟ j | i′ ≟ j′
... | yes e | yes e′ =
  oneIf-yes (combine i i′) (combine j j′) (cong₂ combine e e′)
... | yes _ | no ¬ =
  oneIf-no (combine i i′) (combine j j′) (λ q → ¬ (proj₂ (combine-injective i i′ j j′ q)))
... | no ¬ | yes _ =
  oneIf-no (combine i i′) (combine j j′) (λ q → ¬ (proj₁ (combine-injective i i′ j j′ q)))
... | no ¬ | no  _ =
  oneIf-no (combine i i′) (combine j j′) (λ q → ¬ (proj₁ (combine-injective i i′ j j′ q)))

-- 六因子重排: (a₁ ⊗ a₂) ⊗ ((b₁ ⊗ b₂) ⊗ (c₁ ⊗ c₂)) ≡ (a₁ ⊗ (b₁ ⊗ c₁)) ⊗ (a₂ ⊗ (b₂ ⊗ c₂))
⊗-tensor : ∀ a₁ a₂ b₁ b₂ c₁ c₂ →
  ((a₁ ⊗ a₂) ⊗ ((b₁ ⊗ b₂) ⊗ (c₁ ⊗ c₂))) ≡ ((a₁ ⊗ (b₁ ⊗ c₁)) ⊗ (a₂ ⊗ (b₂ ⊗ c₂)))
⊗-tensor a₁ a₂ b₁ b₂ c₁ c₂ =
  trans (⊗-assoc a₁ a₂ ((b₁ ⊗ b₂) ⊗ (c₁ ⊗ c₂)))
    (trans (cong (λ t → a₁ ⊗ t) (cong (λ t → a₂ ⊗ t) (⊗-4swap b₁ b₂ c₁ c₂)))
      (trans (cong (λ t → a₁ ⊗ t) x)
             (sym (⊗-assoc a₁ (b₁ ⊗ c₁) (a₂ ⊗ (b₂ ⊗ c₂))))))
  where
  -- a₂ ⊗ (Q₁ ⊗ Q₂) ≡ Q₁ ⊗ (a₂ ⊗ Q₂), 其中 Q₁ = b₁ ⊗ c₁、Q₂ = b₂ ⊗ c₂
  x : (a₂ ⊗ ((b₁ ⊗ c₁) ⊗ (b₂ ⊗ c₂))) ≡ ((b₁ ⊗ c₁) ⊗ (a₂ ⊗ (b₂ ⊗ c₂)))
  x = trans (sym (⊗-assoc a₂ (b₁ ⊗ c₁) (b₂ ⊗ c₂)))
        (trans (cong (λ t → t ⊗ (b₂ ⊗ c₂)) (⊗-comm a₂ (b₁ ⊗ c₁)))
               (⊗-assoc (b₁ ⊗ c₁) a₂ (b₂ ⊗ c₂)))

--------------------------------------------------------------------------------
-- §3. 给定两个分解: 张量积满足结构常数方程
--------------------------------------------------------------------------------

module TensorProd (n r m s : ℕ) (ρ₁ : RankLE₃ n r) (ρ₂ : RankLE₃ m s) where

  -- 位置下标拆开: Fin (n · m) ≃ Fin n × Fin m
  plt : Fin (n * m) → Fin n
  plt p = proj₁ (remQuot {n} m p)

  pht : Fin (n * m) → Fin m
  pht p = proj₂ (remQuot {n} m p)

  pLo : Pos (n * m) → Pos n
  pLo X = (plt (proj₁ X) , plt (proj₂ X))

  pHi : Pos (n * m) → Pos m
  pHi X = (pht (proj₁ X) , pht (proj₂ X))

  -- 项下标拆开: Fin (r · s) ≃ Fin r × Fin s
  tL : Fin (r * s) → Fin r
  tL t = proj₁ (remQuot {r} s t)

  tR : Fin (r * s) → Fin s
  tR t = proj₂ (remQuot {r} s t)

  -- 张量积分解的三组系数
  ra× : Fin (r * s) → Pos (n * m) → Trit
  ra× t X = (ra ρ₁ (tL t) (pLo X)) ⊗ (ra ρ₂ (tR t) (pHi X))

  rb× : Fin (r * s) → Pos (n * m) → Trit
  rb× t Y = (rb ρ₁ (tL t) (pLo Y)) ⊗ (rb ρ₂ (tR t) (pHi Y))

  rc× : Fin (r * s) → Out (n * m) → Trit
  rc× t Z = (rc ρ₁ (tL t) (pLo Z)) ⊗ (rc ρ₂ (tR t) (pHi Z))

  -- 系数在 combine 下拆开
  ra×-combine : ∀ (i : Fin r) (j : Fin s) (X : Pos (n * m)) →
    ra× (combine i j) X ≡ (ra ρ₁ i (pLo X)) ⊗ (ra ρ₂ j (pHi X))
  ra×-combine i j X =
    cong (λ u → (ra ρ₁ (proj₁ u) (pLo X)) ⊗ (ra ρ₂ (proj₂ u) (pHi X))) (remQuot-combine i j)

  rb×-combine : ∀ (i : Fin r) (j : Fin s) (Y : Pos (n * m)) →
    rb× (combine i j) Y ≡ (rb ρ₁ i (pLo Y)) ⊗ (rb ρ₂ j (pHi Y))
  rb×-combine i j Y =
    cong (λ u → (rb ρ₁ (proj₁ u) (pLo Y)) ⊗ (rb ρ₂ (proj₂ u) (pHi Y))) (remQuot-combine i j)

  rc×-combine : ∀ (i : Fin r) (j : Fin s) (Z : Out (n * m)) →
    rc× (combine i j) Z ≡ (rc ρ₁ i (pLo Z)) ⊗ (rc ρ₂ j (pHi Z))
  rc×-combine i j Z =
    cong (λ u → (rc ρ₁ (proj₁ u) (pLo Z)) ⊗ (rc ρ₂ (proj₂ u) (pHi Z))) (remQuot-combine i j)

  -- 两个分解各自的因子
  P₁ : Pos (n * m) → Pos (n * m) → Out (n * m) → Fin r → Trit
  P₁ X Y Z i = (ra ρ₁ i (pLo X)) ⊗ ((rb ρ₁ i (pLo Y)) ⊗ (rc ρ₁ i (pLo Z)))

  P₂ : Pos (n * m) → Pos (n * m) → Out (n * m) → Fin s → Trit
  P₂ X Y Z j = (ra ρ₂ j (pHi X)) ⊗ ((rb ρ₂ j (pHi Y)) ⊗ (rc ρ₂ j (pHi Z)))

  -- 单项: 配对相乘的一项 = P₁ ⊗ P₂
  term : ∀ (i : Fin r) (j : Fin s) (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    ((ra× (combine i j) X) ⊗ ((rb× (combine i j) Y) ⊗ (rc× (combine i j) Z))) ≡
    ((P₁ X Y Z i) ⊗ (P₂ X Y Z j))
  term i j X Y Z =
    trans (cong₂ _⊗_ (ra×-combine i j X)
                     (cong₂ _⊗_ (rb×-combine i j Y) (rc×-combine i j Z)))
          (⊗-tensor (ra ρ₁ i (pLo X)) (ra ρ₂ j (pHi X)) (rb ρ₁ i (pLo Y)) (rb ρ₂ j (pHi Y))
                    (rc ρ₁ i (pLo Z)) (rc ρ₂ j (pHi Z)))

  -- 六步链, 每步单独给类型
  s1 : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    sumFin {r * s} (λ t → ((ra× t X) ⊗ ((rb× t Y) ⊗ (rc× t Z)))) ≡
    sumFin {r} (λ i → sumFin {s} (λ j → ((ra× (combine i j) X) ⊗ ((rb× (combine i j) Y) ⊗ (rc× (combine i j) Z)))))
  s1 X Y Z = sumFin-combine r s (λ t → ((ra× t X) ⊗ ((rb× t Y) ⊗ (rc× t Z))))

  s2 : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    sumFin {r} (λ i → sumFin {s} (λ j → ((ra× (combine i j) X) ⊗ ((rb× (combine i j) Y) ⊗ (rc× (combine i j) Z))))) ≡
    sumFin {r} (λ i → sumFin {s} (λ j → ((P₁ X Y Z i) ⊗ (P₂ X Y Z j))))
  s2 X Y Z =
    sumFin-cong {n = r} {g = λ i → sumFin {s} (λ j → ((ra× (combine i j) X) ⊗ ((rb× (combine i j) Y) ⊗ (rc× (combine i j) Z))))}
                {h = λ i → sumFin {s} (λ j → ((P₁ X Y Z i) ⊗ (P₂ X Y Z j)))}
                (λ i → sumFin-cong {n = s}
                          {g = λ j → ((ra× (combine i j) X) ⊗ ((rb× (combine i j) Y) ⊗ (rc× (combine i j) Z)))}
                          {h = λ j → ((P₁ X Y Z i) ⊗ (P₂ X Y Z j))} (λ j → term i j X Y Z))

  s3 : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    sumFin {r} (λ i → sumFin {s} (λ j → ((P₁ X Y Z i) ⊗ (P₂ X Y Z j)))) ≡
    sumFin {r} (λ i → ((P₁ X Y Z i) ⊗ (sumFin (P₂ X Y Z))))
  s3 X Y Z =
    sumFin-cong {n = r} {g = λ i → sumFin {s} (λ j → ((P₁ X Y Z i) ⊗ (P₂ X Y Z j)))}
                {h = λ i → ((P₁ X Y Z i) ⊗ (sumFin (P₂ X Y Z)))}
                (λ i → sumFin-⊗ˡ (P₁ X Y Z i) (P₂ X Y Z))

  s4 : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    sumFin {r} (λ i → ((P₁ X Y Z i) ⊗ (sumFin (P₂ X Y Z)))) ≡
    (sumFin {r} (P₁ X Y Z)) ⊗ (sumFin {s} (P₂ X Y Z))
  s4 X Y Z = sumFin-⊗ʳ (P₁ X Y Z) (sumFin {s} (P₂ X Y Z))

  s5 : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    (sumFin {r} (P₁ X Y Z)) ⊗ (sumFin {s} (P₂ X Y Z)) ≡
    (mm n (pLo X) (pLo Y) (pLo Z)) ⊗ (mm m (pHi X) (pHi Y) (pHi Z))
  s5 X Y Z = cong₂ _⊗_ (rank-eq ρ₁ (pLo X) (pLo Y) (pLo Z)) (rank-eq ρ₂ (pHi X) (pHi Y) (pHi Z))

  -- 位置下标拆回去
  recomb : ∀ u → (combine (plt u) (pht u)) ≡ u
  recomb u = trans (uncurry-combine-proj (remQuot {n} m u)) (combine-remQuot {n} m u)

  -- 指示函数在位置下标上分解: [u = v] ≡ [u低 = v低] ⊗ [u高 = v高]
  oneIf-split : ∀ (u v : Fin (n * m)) →
    oneIf u v ≡ (oneIf (plt u) (plt v)) ⊗ (oneIf (pht u) (pht v))
  oneIf-split u v =
    trans (cong₂ oneIf (sym (recomb u)) (sym (recomb v)))
          (oneIf-combine (plt u) (plt v) (pht u) (pht v))

  -- 结构常数相乘: T_n(低) ⊗ T_m(高) ≡ T_{nm}
  mm-split : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    ((mm n (pLo X) (pLo Y) (pLo Z)) ⊗ (mm m (pHi X) (pHi Y) (pHi Z))) ≡ mm (n * m) X Y Z
  mm-split X Y Z = sym split
    where
    split : (mm (n * m) X Y Z) ≡
            ((mm n (pLo X) (pLo Y) (pLo Z)) ⊗ (mm m (pHi X) (pHi Y) (pHi Z)))
    split =
      trans (cong₂ _⊗_ (oneIf-split (proj₁ X) (proj₁ Z))
                       (cong₂ _⊗_ (oneIf-split (proj₂ X) (proj₁ Y))
                                  (oneIf-split (proj₂ Y) (proj₂ Z))))
            (⊗-tensor (oneIf (plt (proj₁ X)) (plt (proj₁ Z)))
                      (oneIf (pht (proj₁ X)) (pht (proj₁ Z)))
                      (oneIf (plt (proj₂ X)) (plt (proj₁ Y)))
                      (oneIf (pht (proj₂ X)) (pht (proj₁ Y)))
                      (oneIf (plt (proj₂ Y)) (plt (proj₂ Z)))
                      (oneIf (pht (proj₂ Y)) (pht (proj₂ Z))))

  -- ★ 张量积满足结构常数方程
  rank-eq× : ∀ (X : Pos (n * m)) (Y : Pos (n * m)) (Z : Out (n * m)) →
    sumFin {r * s} (λ t → ((ra× t X) ⊗ ((rb× t Y) ⊗ (rc× t Z)))) ≡ mm (n * m) X Y Z
  rank-eq× X Y Z =
    trans (s1 X Y Z)
      (trans (s2 X Y Z)
        (trans (s3 X Y Z)
          (trans (s4 X Y Z)
            (trans (s5 X Y Z) (mm-split X Y Z)))))

--------------------------------------------------------------------------------
-- §4. 秩相乘 / 单位 / 取幂 / M13 的张量幂 / 有限证书
--------------------------------------------------------------------------------

-- ★ 两个秩分解的张量积仍是秩分解（镜像 Lean `RankPower.lean:12 rank_mul`）
rank-mul : ∀ {n r m s} → RankLE₃ n r → RankLE₃ m s → RankLE₃ (n * m) (r * s)
rank-mul {n} {r} {m} {s} ρ₁ ρ₂ =
  record
    { ra = TensorProd.ra× n r m s ρ₁ ρ₂
    ; rb = TensorProd.rb× n r m s ρ₁ ρ₂
    ; rc = TensorProd.rc× n r m s ρ₁ ρ₂
    ; rank-eq = TensorProd.rank-eq× n r m s ρ₁ ρ₂
    }

-- ⟨1⟩ 的 1 项分解（全 1 系数）
rank-one : RankLE₃ 1 1
rank-one =
  record
    { ra = λ i x → T₁
    ; rb = λ i y → T₁
    ; rc = λ i z → T₁
    ; rank-eq = λ { (fzero , fzero) (fzero , fzero) (fzero , fzero) → refl }
    }

-- ★ 取幂（镜像 Lean `RankPower.lean:15 rank_pow`）
rank-pow : ∀ {n r} → RankLE₃ n r → ∀ k → RankLE₃ (n ^ k) (r ^ k)
rank-pow ρ zero = rank-one
rank-pow ρ (suc k) = rank-mul ρ (rank-pow ρ k)

-- ★ M13 的张量幂: 每个尺寸 2^k 都有一个 7^k 项的分解
rank-strassen-pow : ∀ k → RankLE₃ (2 ^ k) (7 ^ k)
rank-strassen-pow k = rank-pow rank-strassen k

-- 第一个非平凡实例: ⟨4,4,4⟩ 有 49 项分解
rank-strassen² : RankLE₃ 4 49
rank-strassen² = rank-mul rank-strassen rank-strassen

-- 基数: 7^6 = 117649 ≤ 131072 = 2^17
cert-base : 7 ^ 6 ≤ 2 ^ 17
cert-base = m≤m+n (7 ^ 6) 13423

-- 有限证书: (7 ^ k) ^ 6 ≤ (2 ^ k) ^ 17（由 cert-base 两边取 k 次幂）
strassen-certificate : ∀ k → (7 ^ k) ^ 6 ≤ (2 ^ k) ^ 17
strassen-certificate k =
  ≤-trans (≤-reflexive e1)
    (≤-trans (^-monoˡ-≤ k cert-base) (≤-reflexive (sym e2)))
  where
  e1 : (7 ^ k) ^ 6 ≡ (7 ^ 6) ^ k
  e1 = trans (^-*-assoc 7 k 6) (trans (cong (λ t → 7 ^ t) (*-comm k 6)) (sym (^-*-assoc 7 6 k)))
  e2 : (2 ^ k) ^ 17 ≡ (2 ^ 17) ^ k
  e2 = trans (^-*-assoc 2 k 17) (trans (cong (λ t → 2 ^ t) (*-comm k 17)) (sym (^-*-assoc 2 17 k)))

-- 每个尺寸 2^k: 一个 7^k 项的分解 + 证书
strassen-upper : ∀ k → RankLE₃ (2 ^ k) (7 ^ k) × ((7 ^ k) ^ 6 ≤ (2 ^ k) ^ 17)
strassen-upper k = rank-strassen-pow k , strassen-certificate k

--------------------------------------------------------------------------------
-- §5. 与展平下界的组合
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3 using (rank-lower)

-- 每个尺寸 2^k 的张量幂见证都满足展平下界: (2^k)² ≤ 7^k
rank-lower-pow : ∀ k → (2 ^ k) * (2 ^ k) ≤ 7 ^ k
rank-lower-pow k = rank-lower (2 ^ k) (7 ^ k) (rank-strassen-pow k)

-- 第一个非平凡实例: 16 ≤ 49（内核算出）
rank-lower-strassen² : 4 * 4 ≤ 49
rank-lower-strassen² = rank-lower 4 49 rank-strassen²
