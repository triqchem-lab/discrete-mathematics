{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankSparseLawsGF3
-- M21: 稀疏定律的有限口径——DensityBound / CellBound / DegreeBound 的 Saving 型陈述层
-- （立项 B-T3 + B-T4 的代理定义, 2026-11-27）
--
-- 数学背景
--   Lean 的上界机器里有三条关于加权矩形积的定律（w : Fin i → Fin j → Fin k → F, r 项分解）:
--     DensityBound（Rectangle/Weights.lean:19）:
--       supportSize w · exp(exponent F (log i) (log j) (log k)) ≤ i·j·k·r
--     CellBound（Rectangle/Mask.lean:17）:
--       exp(exponent F (short i j |u|) (log |u| − short i j |u|) (log k)) ≤ r
--     DegreeBound（Rectangle/Sparse/Law.lean:332）:
--       |U| · exp(exponent F (log I) (log J) (log K)) ≤ 432·I·J·K·r
--   三条里的 exp(exponent F (log I) (log J) (log K)) 是整数格式 (I,J,K) 的「体积项」E(I,J,K),
--   它由两族有理斜率夹出: E = inf{ (IJK)^σ : σ 上斜率 } = sup{ (IJK)^τ : τ 下斜率 }。
--
-- 为什么是这个形状
--   宪法排除 ℝ, E 一般是无理数, 写不进库。但「|U|·E ≤ C」等价于对每个下斜率 τ = p/q 的
--   纯 ℕ 不等式 |U|^q·(IJK)^p ≤ C^q——分数对 (p,q) 替代实数指数（M16-D 的 Saving 型先例）。
--   本件把三条定律写成这个形状（无居民）, 并证它们与库内两半（ω₃-boundary / Strassen）衔接。
--
-- 内容
--   §1 矩形加权词汇: wmmRect / WeightedRankLERect / supportSizeᵣ / suppRowsᵣ / suppColsᵣ /
--      suppInnerᵣ / 格集计数 card₃ card₂（M19/M20 的方形版是 i = j = k 的实例, 定义性相同）
--   §2 指数的离散代理: 下斜率 LowerSlopeᵣ（一切分解）与上斜率 UpperSlopeᵣ（存在分解, 无常数）
--   §3 三条定律的有限口径（陈述, 无居民）: DensityBound₃ / CellBound₃ / DegreeBound₃
--   §4 衔接定理: ★ lower-slope-boundary（下半 ⟹ 方格式的下斜率 3/4）、
--      ★ upper-slope-strassen（Strassen ⟹ (2,2,2) 的上斜率 15/16）、
--      ★ upper-lower-slope（同格式的上斜率 ≥ 下斜率）、
--      ★★ degree-law-boundary（DegreeBound₃ + 下半 ⟹ 支撑数⁴·n⁹ ≤ (432·n³·r)⁴）
--
-- 诚实边界
--   · CellBound₃ 只是**平方输出集实例**（|u| = A·A, A ≤ i, A ≤ j）: 一般 |u| 下 Lean 的
--     short i j |u| = min(log i, log j, log|u|/2) 给出实数边长, 格式不是整数格式;
--     其证明核心 width（Sparse/Degree.lean:562）是熵型实数量 [边界标注]。
--   · 三条定律本身**不证**: 它们在 Lean 里是定理（coeff_density / coeff_cells / coeff_degrees）,
--     证明走 Character 定价层（exponent_le_of_characters）, 本库没有 Character 对象。
--   · §2 的斜率代理与 Lean 的 exponent 之间的等价（E = inf 上斜率 = sup 下斜率）是外部事实,
--     需要 ℝ 上的稠密性论证 [阅读判断·外部], 本库不陈述不证明。
--   · 上斜率的无条件非空性（schoolbook ⟹ 斜率 1 对一切格式可容）本件**未做**:
--     需要一般格式的 schoolbook 矩形分解, 库内只有 1×1 的电路哨兵 [未做]。
--
-- 复用(先查后写): RankLERect / mmRect / rankLE₃→rect / sumℕ（M18）、WeightedRankLE₃ / suppInd /
--   supportSize₃（M19）、ω₃-boundary（M16）、rank-strassen-pow（TensorRankPowGF3）、
--   pow-exp-mono / 1≤pow（TensorRankUpperGF3）。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankSparseLawsGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; ≰⇒>; ≤⇒≯; <-≤-trans; ≤-<-trans; m≤n⇒m≤1+n; m≤m+n; m<n+m
       ; *-comm; *-assoc; *-identityʳ; *-monoˡ-≤; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤
       ; +-identityʳ; ^-monoˡ-≤; ^-*-assoc)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; ⊗-identityˡ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin)
open import Sovereign.Algebra.LinearAlgebra.TensorRankCircuitGF3
  using (RankLERect; mmRect; rankLE₃→rect; sumℕ)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3 using (RankLE₃; ω₃-boundary)
open import Sovereign.Algebra.LinearAlgebra.TensorRankSparseGF3
  using (WeightedRankLE₃; suppInd; supportSize₃)
open import Sovereign.Algebra.LinearAlgebra.TensorRankPowGF3 using (rank-strassen-pow)
open import Sovereign.Algebra.LinearAlgebra.TensorRankUpperGF3 using (pow-exp-mono; 1≤pow)

--------------------------------------------------------------------------------
-- §1 矩形加权词汇
--------------------------------------------------------------------------------

-- 加权矩形结构常数: 条件成立处取 w(i,j,k)（x₁ = i, y₂ = j, x₂ = k）, 其余 T₀
wmmRect : (i j k : ℕ) → (Fin i → Fin j → Fin k → Trit) →
          (Fin i × Fin k) → (Fin k × Fin j) → (Fin i × Fin j) → Trit
wmmRect i j k w x y z = (w (proj₁ x) (proj₂ y) (proj₂ x)) ⊗ (mmRect i j k x y z)

-- ★ 加权矩形积的 r 项分解（镜像 Lean Weights.lean:8 WeightedRankLE）
record WeightedRankLERect (i j k r : ℕ) (w : Fin i → Fin j → Fin k → Trit) : Set where
  field
    ra : Fin r → (Fin i × Fin k) → Trit
    rb : Fin r → (Fin k × Fin j) → Trit
    rc : Fin r → (Fin i × Fin j) → Trit
    wrank-eq : ∀ x y z →
      sumFin (λ l → (ra l x) ⊗ ((rb l y) ⊗ (rc l z))) ≡ wmmRect i j k w x y z

-- 方形加权分解就是矩形版的 (n,n,n) 实例
weighted₃→rect : ∀ n r w → WeightedRankLE₃ n r w → WeightedRankLERect n n n r w
weighted₃→rect n r w W = record
  { ra = WeightedRankLE₃.ra W
  ; rb = WeightedRankLE₃.rb W
  ; rc = WeightedRankLE₃.rc W
  ; wrank-eq = WeightedRankLE₃.wrank-eq W }

-- 矩形 (n,n,n) 的秩分解回到方形谓词（M18 只有另一个方向 rankLE₃→rect）
rect→RankLE₃ : ∀ n r → RankLERect n n n r → RankLE₃ n r
rect→RankLE₃ n r R = record
  { ra = RankLERect.ra R
  ; rb = RankLERect.rb R
  ; rc = RankLERect.rc R
  ; rank-eq = RankLERect.rank-eq R }

-- 支撑数 / 三个方向的完成集计数（矩形版; i = j = k = n 时与 M19/M20 定义性相同）
supportSizeᵣ : (i j k : ℕ) → (Fin i → Fin j → Fin k → Trit) → ℕ
supportSizeᵣ i j k w =
  sumℕ {i} (λ a → sumℕ {j} (λ b → sumℕ {k} (λ c → suppInd (w a b c))))

suppRowsᵣ : (i j k : ℕ) → (Fin i → Fin j → Fin k → Trit) → Fin i → Fin j → Fin k → ℕ
suppRowsᵣ i j k w a b c = sumℕ {i} (λ x → suppInd (w x b c))

suppColsᵣ : (i j k : ℕ) → (Fin i → Fin j → Fin k → Trit) → Fin i → Fin j → Fin k → ℕ
suppColsᵣ i j k w a b c = sumℕ {j} (λ y → suppInd (w a y c))

suppInnerᵣ : (i j k : ℕ) → (Fin i → Fin j → Fin k → Trit) → Fin i → Fin j → Fin k → ℕ
suppInnerᵣ i j k w a b c = sumℕ {k} (λ z → suppInd (w a b z))

-- 布尔指示与格集计数（镜像 Finset.card）
indB : Bool → ℕ
indB false = zero
indB true = suc zero

card₃ : (i j k : ℕ) → (Fin i → Fin j → Fin k → Bool) → ℕ
card₃ i j k u = sumℕ {i} (λ a → sumℕ {j} (λ b → sumℕ {k} (λ c → indB (u a b c))))

card₂ : (i j : ℕ) → (Fin i → Fin j → Bool) → ℕ
card₂ i j u = sumℕ {i} (λ a → sumℕ {j} (λ b → indB (u a b)))

-- ℕ 和的逐点合同（嵌套三层要用三次）
sumℕ-cong : ∀ {n} (f g : Fin n → ℕ) → (∀ i → f i ≡ g i) → sumℕ {n} f ≡ sumℕ {n} g
sumℕ-cong {zero} f g h = refl
sumℕ-cong {suc n} f g h =
  trans (cong (f fzero +_) (sumℕ-cong (λ i → f (fsuc i)) (λ i → g (fsuc i)) (λ i → h (fsuc i))))
        (cong (_+ sumℕ {n} (λ i → g (fsuc i))) (h fzero))

-- 逐项有界 ⟹ 和有界: Σ f ≤ n·c
sumℕ≤ : ∀ (n : ℕ) (f : Fin n → ℕ) (c : ℕ) → (∀ i → f i ≤ c) → sumℕ {n} f ≤ n * c
sumℕ≤ zero f c h = z≤n
sumℕ≤ (suc n) f c h =
  ≤-trans (+-monoˡ-≤ (sumℕ {n} (λ i → f (fsuc i))) (h fzero))
          (+-monoʳ-≤ c (sumℕ≤ n (λ i → f (fsuc i)) c (λ i → h (fsuc i))))

--------------------------------------------------------------------------------
-- §2 指数的离散代理: 格式 (I,J,K) 上的斜率 p/q（体积 = I·J·K）
--------------------------------------------------------------------------------

-- 下斜率（Saving 型）: 格式的每个幂的**每个**分解都满足 体积^{(p/q)·幂} ≤ 项数
LowerSlopeᵣ : (I J K p q : ℕ) → Set
LowerSlopeᵣ I J K p q =
  ∀ (m : ℕ) (ρ : ℕ) → RankLERect (I ^ m) (J ^ m) (K ^ m) ρ → (I * J * K) ^ (p * m) ≤ ρ ^ q

-- 上斜率（无常数可容）: 格式的每个幂**存在**项数 ≤ 体积^{(p/q)·幂} 的分解
UpperSlopeᵣ : (I J K p q : ℕ) → Set
UpperSlopeᵣ I J K p q =
  ∀ (m : ℕ) →
  Σ ℕ (λ ρ → RankLERect (I ^ m) (J ^ m) (K ^ m) ρ × (ρ ^ q ≤ (I * J * K) ^ (p * m)))

--------------------------------------------------------------------------------
-- §3 三条定律的有限口径（陈述, 无居民）
--------------------------------------------------------------------------------

-- ★ DensityBound: 对格式 (i,j,k) 的每个下斜率 p/q,
--   supportSize w · (ijk)^{p/q} ≤ i·j·k·r
DensityBound₃ : Set
DensityBound₃ =
  ∀ i j k r → 0 < i → 0 < j → 0 < k →
  ∀ (w : Fin i → Fin j → Fin k → Trit) p q →
  WeightedRankLERect i j k r w → LowerSlopeᵣ i j k p q →
  (supportSizeᵣ i j k w) ^ q * (i * j * k) ^ p ≤ (i * j * k * r) ^ q

-- ★ DegreeBound: 对格式 (I,J,K) 的每个下斜率 p/q, 支撑里每个格的三个完成集计数
--   分别 ≤ I、J、K 的格集 U 满足 |U| · (IJK)^{p/q} ≤ 432·I·J·K·r
DegreeBound₃ : Set
DegreeBound₃ =
  ∀ i j k I J K r → 0 < I → 0 < J → 0 < K →
  ∀ (w : Fin i → Fin j → Fin k → Trit) (u : Fin i → Fin j → Fin k → Bool) p q →
  (∀ a b c → u a b c ≡ true → ¬ (w a b c ≡ T₀)) →
  (∀ a b c → u a b c ≡ true → suppRowsᵣ i j k w a b c ≤ I) →
  (∀ a b c → u a b c ≡ true → suppColsᵣ i j k w a b c ≤ J) →
  (∀ a b c → u a b c ≡ true → suppInnerᵣ i j k w a b c ≤ K) →
  WeightedRankLERect i j k r w → LowerSlopeᵣ I J K p q →
  (card₃ i j k u) ^ q * (I * J * K) ^ p ≤ (432 * I * J * K * r) ^ q

-- ★ CellBound——**平方输出集实例**: w 的支撑恰是输出格集 u（|u| = A·A, A ≤ i, A ≤ j）时
--   Lean 的 short i j |u| = log A, 格式 (A,A,k) 是整数格式, 律即 (A·A·k)^{p/q} ≤ r
CellBound₃ : Set
CellBound₃ =
  ∀ i j k A r → 0 < i → 0 < j → 0 < k → 0 < A → A ≤ i → A ≤ j →
  ∀ (w : Fin i → Fin j → Fin k → Trit) (u : Fin i → Fin j → Bool) p q →
  (∀ a b c → (u a b ≡ true → ¬ (w a b c ≡ T₀)) × (¬ (w a b c ≡ T₀) → u a b ≡ true)) →
  card₂ i j u ≡ A * A →
  WeightedRankLERect i j k r w → LowerSlopeᵣ A A k p q →
  (A * A * k) ^ p ≤ r ^ q

--------------------------------------------------------------------------------
-- §4 衔接定理
--------------------------------------------------------------------------------

-- n·n·n = n³（n ^ 3 按定义是 n · (n · (n · 1))）
cubeₙ : ∀ n → n * n * n ≡ n ^ 3
cubeₙ n = trans (*-assoc n n n) (cong (λ t → n * t) (sym (cong (λ t → n * t) (*-identityʳ n))))

-- 2 ≤ n ⟹ 2 ≤ n ^ suc m
2≤n^m : ∀ n m → 2 ≤ n → 2 ≤ n ^ suc m
2≤n^m n m hn =
  ≤-trans (≤-trans hn (≤-reflexive (sym (*-identityʳ n))))
          (pow-exp-mono n 1 (suc m) (≤-trans (s≤s z≤n) hn) (s≤s z≤n))

-- 0 < n, 由 2 ≤ n
0<n : ∀ n → 2 ≤ n → 0 < n
0<n n hn = ≤-trans (s≤s z≤n) hn

-- 1×1×1 的分解至少 1 项: 0 项时对角线处 sumFin {0} = T₀, 而 mmRect 处 = T₁
T₀≠T₁ : T₀ ≡ T₁ → ⊥
T₀≠T₁ ()

rank≥1 : ∀ ρ → RankLERect 1 1 1 ρ → 1 ≤ ρ
rank≥1 zero R =
  ⊥-elim (T₀≠T₁ (RankLERect.rank-eq R (fzero , fzero) (fzero , fzero) (fzero , fzero)))
rank≥1 (suc ρ) R = s≤s z≤n

-- ★ 下半 ⟹ 方格式的下斜率 3/4: (n·n·n)^(3m) = (n^m)⁹ ≤ ρ⁴
lower-slope-boundary : ω₃-boundary → ∀ n → 2 ≤ n → LowerSlopeᵣ n n n 3 4
lower-slope-boundary B n hn zero ρ R = 1≤pow ρ 4 (rank≥1 ρ R)
lower-slope-boundary B n hn (suc m) ρ R =
  ≤-trans (≤-reflexive e) (B (n ^ suc m) ρ (2≤n^m n m hn) (rect→RankLE₃ (n ^ suc m) ρ R))
  where
  e : (n * n * n) ^ (3 * suc m) ≡ (n ^ suc m) ^ 9
  e = trans (cong (λ t → t ^ (3 * suc m)) (cubeₙ n))
      (trans (^-*-assoc n 3 (3 * suc m))
      (trans (cong (n ^_) (sym (*-assoc 3 3 (suc m))))
      (trans (cong (n ^_) (*-comm 9 (suc m)))
             (sym (^-*-assoc n (suc m) 9)))))

-- 数值由 oracle 给出（整数核对）: 7^16 = 33232930569601, 8^15 = 35184372088832,
--   差 1951441519231; 7^15 ≤ 8^14 不成立, 所以 15/16 是这组分母下最紧的见证。
cert-7¹⁶≤8¹⁵ : 7 ^ 16 ≤ 8 ^ 15
cert-7¹⁶≤8¹⁵ = m≤m+n (7 ^ 16) 1951441519231

-- ★ Strassen ⟹ (2,2,2) 格式的上斜率 15/16: (7^m)^16 = (7^16)^m ≤ (8^15)^m = 8^(15m)
upper-slope-strassen : UpperSlopeᵣ 2 2 2 15 16
upper-slope-strassen m =
  (7 ^ m) , rankLE₃→rect (2 ^ m) (7 ^ m) (rank-strassen-pow m) , le
  where
  le : (7 ^ m) ^ 16 ≤ (2 * 2 * 2) ^ (15 * m)
  le = ≤-trans (≤-reflexive e)
         (≤-trans (^-monoˡ-≤ m cert-7¹⁶≤8¹⁵)
                  (≤-reflexive (^-*-assoc 8 15 m)))
    where
    e : (7 ^ m) ^ 16 ≡ (7 ^ 16) ^ m
    e = trans (^-*-assoc 7 m 16) (trans (cong (7 ^_) (*-comm m 16)) (sym (^-*-assoc 7 16 m)))

-- 底 ≥ 2 时幂对指数严格单调: a < b ⟹ V^a < V^b
pow-step-< : ∀ V a → 2 ≤ V → V ^ a < V ^ suc a
pow-step-< V a h = <-≤-trans lt1 (*-monoˡ-≤ (V ^ a) h)
  where
  pos : 0 < V ^ a
  pos = 1≤pow V a (≤-trans (s≤s z≤n) h)
  lt1 : V ^ a < 2 * V ^ a
  lt1 = <-≤-trans (m<n+m (V ^ a) pos)
                  (≤-reflexive (sym (cong (V ^ a +_) (+-identityʳ (V ^ a)))))

pow-exp-strict : ∀ V a b → 2 ≤ V → a < b → V ^ a < V ^ b
pow-exp-strict V zero (suc zero) h (s≤s z≤n) =
  <-≤-trans h (≤-reflexive (sym (*-identityʳ V)))
pow-exp-strict V zero (suc (suc b)) h (s≤s z≤n) =
  <-≤-trans (pow-exp-strict V zero (suc b) h (s≤s z≤n))
            (pow-exp-mono V (suc b) (suc (suc b)) (≤-trans (s≤s z≤n) h) (s≤s (m≤n⇒m≤1+n ≤-refl)))
pow-exp-strict V (suc a) (suc (suc b)) h (s≤s (s≤s p)) =
  ≤-<-trans le (pow-step-< V (suc b) h)
  where
  h1 : 1 ≤ V
  h1 = ≤-trans (s≤s z≤n) h
  le : V ^ suc a ≤ V ^ suc b
  le = ≤-trans (≤-reflexive (*-comm V (V ^ a)))
         (≤-trans (*-monoˡ-≤ V (pow-exp-mono V a b h1 p))
                  (≤-reflexive (*-comm (V ^ b) V)))

-- 底 ≥ 2 时幂可以约去指数: V^a ≤ V^b ⟹ a ≤ b
pow-cancel : ∀ V a b → 2 ≤ V → V ^ a ≤ V ^ b → a ≤ b
pow-cancel V a b h le with a ≤? b
... | yes p = p
... | no np = ⊥-elim (≤⇒≯ le (pow-exp-strict V b a h (≰⇒> np)))

-- ★ 同格式的上斜率 ≥ 下斜率: p′/q′ ≤ p/q（交叉相乘）
upper-lower-slope : ∀ I J K p q p′ q′ → 2 ≤ I * J * K →
  UpperSlopeᵣ I J K p q → LowerSlopeᵣ I J K p′ q′ → p′ * q ≤ p * q′
upper-lower-slope I J K p q p′ q′ hV U L =
  pow-cancel (I * J * K) (p′ * q) (p * q′) hV (≤-trans e1 (≤-trans (≤-reflexive e2) e3))
  where
  ρ : ℕ
  ρ = proj₁ (U 1)

  R : RankLERect (I ^ 1) (J ^ 1) (K ^ 1) ρ
  R = proj₁ (proj₂ (U 1))

  up′ : ρ ^ q ≤ (I * J * K) ^ p
  up′ = ≤-trans (proj₂ (proj₂ (U 1))) (≤-reflexive (cong ((I * J * K) ^_) (*-identityʳ p)))

  low′ : (I * J * K) ^ p′ ≤ ρ ^ q′
  low′ = ≤-trans (≤-reflexive (sym (cong ((I * J * K) ^_) (*-identityʳ p′)))) (L 1 ρ R)

  -- V^(p′q) = (V^p′)^q ≤ (ρ^q′)^q = ρ^(q′q)
  e1 : (I * J * K) ^ (p′ * q) ≤ ρ ^ (q′ * q)
  e1 = ≤-trans (≤-reflexive (sym (^-*-assoc (I * J * K) p′ q)))
         (≤-trans (^-monoˡ-≤ q low′) (≤-reflexive (^-*-assoc ρ q′ q)))

  e2 : ρ ^ (q′ * q) ≡ ρ ^ (q * q′)
  e2 = cong (ρ ^_) (*-comm q′ q)

  -- ρ^(qq′) = (ρ^q)^q′ ≤ (V^p)^q′ = V^(pq′)
  e3 : ρ ^ (q * q′) ≤ (I * J * K) ^ (p * q′)
  e3 = ≤-trans (≤-reflexive (sym (^-*-assoc ρ q q′)))
         (≤-trans (^-monoˡ-≤ q′ up′) (≤-reflexive (^-*-assoc (I * J * K) p q′)))

-- 支撑的布尔指示与格数
suppB : Trit → Bool
suppB T₀ = false
suppB T₁ = true
suppB T₂ = true

suppInd≡indB : ∀ t → suppInd t ≡ indB (suppB t)
suppInd≡indB T₀ = refl
suppInd≡indB T₁ = refl
suppInd≡indB T₂ = refl

supportB : ∀ n (w : Fin n → Fin n → Fin n → Trit) →
  card₃ n n n (λ a b c → suppB (w a b c)) ≡ supportSize₃ n w
supportB n w = sumℕ-cong fb gb hb
  where
  fb : Fin n → ℕ
  fb a = sumℕ {n} (λ b → sumℕ {n} (λ c → indB (suppB (w a b c))))

  gb : Fin n → ℕ
  gb a = sumℕ {n} (λ b → sumℕ {n} (λ c → suppInd (w a b c)))

  hb : ∀ a → fb a ≡ gb a
  hb a = sumℕ-cong fc gc hc
    where
    fc : Fin n → ℕ
    fc b = sumℕ {n} (λ c → indB (suppB (w a b c)))

    gc : Fin n → ℕ
    gc b = sumℕ {n} (λ c → suppInd (w a b c))

    hc : ∀ b → fc b ≡ gc b
    hc b = sumℕ-cong (λ c → indB (suppB (w a b c))) (λ c → suppInd (w a b c))
                     (λ c → sym (suppInd≡indB (w a b c)))

inU→supp : ∀ (t : Trit) → suppB t ≡ true → ¬ (t ≡ T₀)
inU→supp T₀ ()
inU→supp T₁ refl ()
inU→supp T₂ refl ()

suppInd≤1 : ∀ t → suppInd t ≤ 1
suppInd≤1 T₀ = z≤n
suppInd≤1 T₁ = ≤-refl
suppInd≤1 T₂ = ≤-refl

rows≤n : ∀ n w a b c → suppRowsᵣ n n n w a b c ≤ n
rows≤n n w a b c =
  ≤-trans (sumℕ≤ n (λ x → suppInd (w x b c)) 1 (λ x → suppInd≤1 (w x b c)))
          (≤-reflexive (*-identityʳ n))

cols≤n : ∀ n w a b c → suppColsᵣ n n n w a b c ≤ n
cols≤n n w a b c =
  ≤-trans (sumℕ≤ n (λ y → suppInd (w a y c)) 1 (λ y → suppInd≤1 (w a y c)))
          (≤-reflexive (*-identityʳ n))

inner≤n : ∀ n w a b c → suppInnerᵣ n n n w a b c ≤ n
inner≤n n w a b c =
  ≤-trans (sumℕ≤ n (λ z → suppInd (w a b z)) 1 (λ z → suppInd≤1 (w a b z)))
          (≤-reflexive (*-identityʳ n))

-- ★★ DegreeBound₃ + 下半 ⟹ 支撑数⁴·n⁹ ≤ (432·n³·r)⁴
--   取 I = J = K = n（支撑里每个格的三个完成集计数天然 ≤ n）、U = 整个支撑、下斜率 3/4
--   （lower-slope-boundary）。这就是「密度下界」的 ℕ 形态:
--   r ≥ 支撑数^{1/4}·n^{9/4} / (432·n³)^{1/4}。
degree-law-boundary : DegreeBound₃ → ω₃-boundary → ∀ n r → 2 ≤ n →
  ∀ w → WeightedRankLE₃ n r w →
  (supportSize₃ n w) ^ 4 * (n * n * n) ^ 3 ≤ (432 * n * n * n * r) ^ 4
degree-law-boundary D B n r hn w W =
  ≤-trans (≤-reflexive (cong (λ t → t ^ 4 * (n * n * n) ^ 3) (sym (supportB n w))))
          (D n n n n n n r (0<n n hn) (0<n n hn) (0<n n hn) w (λ a b c → suppB (w a b c)) 3 4
             (λ a b c h → inU→supp (w a b c) h)
             (λ a b c _ → rows≤n n w a b c)
             (λ a b c _ → cols≤n n w a b c)
             (λ a b c _ → inner≤n n w a b c)
             (weighted₃→rect n r w W)
             (lower-slope-boundary B n hn))
