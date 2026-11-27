{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Algebra.LinearAlgebra.TensorRankIndexGF3
-- M22: 指标集泛型的秩分解 + 结构引理（拉回 / 不变性 / 线性限制 / 对称）+ Bläser 2003 在 n = 3 的陈述
--
-- 数学背景
--   TensorRankGF3 的 RankLE₃ n r 把指标集写死成 Pos n / Out n, 把张量写死成 mm n。
--   下界证明的每一步都要动这两样东西:
--     · 限制(monotonicity): 把第一个变元限制到一个子空间 S, 秩不会升高——限制后的张量换了指标集;
--     · 不变性(invariance): 第一变元上的可逆线性变换不改变秩——结构常数换了基。
--   Wang 的自动框架(arXiv:2603.07280 §3.1 命题 1)把这两条列为全部下界技术的前提;
--   Bläser 的替换法证明(R(⟨n,m,n⟩) ≥ 2mn + 2n − m − 2, m ≥ n ≥ 3, 任意域; 2003,
--   «On the complexity of the multiplication of matrices of small formats»; n = m = 3 即 19)
--   同样是沿子空间做归纳。所以先把谓词写成指标集泛型的:
--     X Y Z 是任意三个集合(第一、第二、第三变元的坐标集), T : X → Y → Z → Trit 是结构常数。
--
-- 内容
--   §1 泛型谓词 RankLE; 与 RankLE₃ 的往返; 见证哨兵(Laderman 23 项分解在泛型谓词下的类型)
--   §2 ★ rank-pull   沿任意映射 g : X' → X 拉回(换元)
--      ★ rank-invar  g 有左逆 h 时, 沿 g 拉回后的分解经 h 搬回原张量 ⟹ 可逆换元保持可分解性
--   §3 ★ rank-restrict 线性限制: 子空间的基由 s : Fin k → Fin m 给出时,
--                        限制后的结构常数 Σ_x s j x ⊗ T x y z 仍有 r 项分解(「约束只会降低秩」)
--   §4 ★ rank-swap / ★ rank-rot 两个输入对换 / 三个变元轮回
--   §5 Bläser 2003 在 n = 3 的实例 bläser₃-boundary(陈述, 无居民)与它蕴含的展平下界
--
-- 诚实边界
--   · 本件**不改进任何下界数字**: 库内 n = 3 的下界仍是展平界 r ≥ 9; Bläser 的 19 只是陈述。
--     它交付的是以后任何一条下界证明(替换法 / 证书内核化)都要用的结构事实。
--   · rank-restrict 的第一坐标集取 Fin m(要对坐标求和); 第二、第三坐标集任意。
--     库内的 Pos n 是 Fin n × Fin n, 要先用 rank-pull 或另写一个按 sumX 求和的版本。
--   · 一般线性换元的「不变性」(s 可逆时 T 与 T∘s 互相分解)本件只给了「沿映射拉回」这一半
--     (rank-pull)与其经左逆的回搬(rank-invar); 「(T∘s)∘s⁻¹ ≡ T」那一步结构等式未做。
--   · 只对 GF(3)。
--
-- 复用(先查后写): sumFin / sumFin-cong(GF3LaplacianN)、sumFin-scale₃ / sumFin-swap₃ / ⊗-rot
--   (TensorRankFlattenGF3)、RankLE₃ / Pos / Out / mm(TensorRankGF3)、
--   rank-laderman(TensorRankLadermanGF3)、≤-trans / m≤m+n(stdlib Data.Nat.Properties)。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankIndexGF3 where

open import Data.Nat using (ℕ; _≤_)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Data.Nat.Properties using (≤-trans; m≤m+n)

open import Sovereign.Base.Trit using (Trit; T₁; _⊗_; ⊗-comm; ⊗-assoc; ⊗-identityʳ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong)
open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3
  using (sumFin-scale₃; sumFin-swap₃; ⊗-rot)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3 using (Pos; Out; mm; RankLE₃)
open import Sovereign.Algebra.LinearAlgebra.TensorRankLadermanGF3 using (rank-laderman)

--------------------------------------------------------------------------------
-- §1. 指标集泛型的谓词
--------------------------------------------------------------------------------

-- ★ r 项秩分解: T(x,y,z) = Σ_i a i x ⊗ (b i y ⊗ c i z)
--   与 RankLE₃ 逐字段同形; RankLE₃ n r 就是它取 X = Y = Pos n、Z = Out n、T = mm n 的特例。
record RankLE (X Y Z : Set) (T : X → Y → Z → Trit) (r : ℕ) : Set where
  field
    ra : Fin r → X → Trit
    rb : Fin r → Y → Trit
    rc : Fin r → Z → Trit
    rank-eq : ∀ x y z → sumFin (λ i → (ra i x) ⊗ ((rb i y) ⊗ (rc i z))) ≡ T x y z

-- record 字段不随模块按名字导出: 本地打开泛型 record(不转出口); RankLE₃ 的字段一律带限定名。
open RankLE using (ra; rb; rc; rank-eq)

-- 往返: 两个谓词在方阵情形是同一个东西
rankLE₃→idx : ∀ n r → RankLE₃ n r → RankLE (Pos n) (Pos n) (Out n) (mm n) r
rankLE₃→idx n r ρ = record
  { ra = RankLE₃.ra ρ
  ; rb = RankLE₃.rb ρ
  ; rc = RankLE₃.rc ρ
  ; rank-eq = RankLE₃.rank-eq ρ
  }

idx→rankLE₃ : ∀ n r → RankLE (Pos n) (Pos n) (Out n) (mm n) r → RankLE₃ n r
idx→rankLE₃ n r ρ = record
  { ra = ra ρ
  ; rb = rb ρ
  ; rc = rc ρ
  ; rank-eq = rank-eq ρ
  }

-- 哨兵: Laderman 的 23 项分解在泛型谓词下的类型(与 rank-laderman 经桥得到的是同一组系数)
sentinel-laderman : RankLE (Pos 3) (Pos 3) (Out 3) (mm 3) 23
sentinel-laderman = rankLE₃→idx 3 23 rank-laderman

--------------------------------------------------------------------------------
-- §2. 换元: 沿映射拉回; 有左逆时搬回
--------------------------------------------------------------------------------

-- ★ 沿 g : X' → X 拉回: T ∘ (g × id × id) 仍有 r 项分解。证明就是把 a 复合 g。
rank-pull : (X' : Set) → ∀ {X Y Z r} (T : X → Y → Z → Trit) (g : X' → X) →
  RankLE X Y Z T r → RankLE X' Y Z (λ x' y z → T (g x') y z) r
rank-pull X' T g ρ = record
  { ra = λ i x' → ra ρ i (g x')
  ; rb = rb ρ
  ; rc = rc ρ
  ; rank-eq = λ x' y z → rank-eq ρ (g x') y z
  }

-- ★ 不变性(一半): 若 h : X → X' 是 g 的左逆(g ∘ h ≡ id), 则拉回后的分解经 h 搬回原张量。
--   与 rank-pull 合起来: 沿「有左逆的映射」拉回保持可分解性(可逆换元不改变秩)。
rank-invar : (X' : Set) → ∀ {X Y Z r} (T : X → Y → Z → Trit) (g : X' → X) (h : X → X') →
  (∀ x → g (h x) ≡ x) →
  RankLE X' Y Z (λ x' y z → T (g x') y z) r → RankLE X Y Z T r
rank-invar X' T g h g∘h ρ = record
  { ra = λ i x → ra ρ i (h x)
  ; rb = rb ρ
  ; rc = rc ρ
  ; rank-eq = λ x y z → trans (rank-eq ρ (h x) y z) (cong (λ v → T v y z) (g∘h x))
  }

-- 哨兵: 把 Laderman 分解拉回到一个点的坐标集(Fin 1), 恒取位置 (0,0)
sentinel-pull : RankLE (Fin 1) (Pos 3) (Out 3) (λ _ y z → mm 3 (fzero , fzero) y z) 23
sentinel-pull = rank-pull (Fin 1) (mm 3) (λ _ → fzero , fzero) (rankLE₃→idx 3 23 rank-laderman)

-- 哨兵: 拉回到一点再搬回去——g 是常值、h 任意时 g ∘ h ≡ id 不成立, 所以这里用恒等映射验证回搬这一半
sentinel-invar : RankLE (Pos 3) (Pos 3) (Out 3) (mm 3) 23
sentinel-invar = rank-invar (Pos 3) (mm 3) (λ x → x) (λ x → x) (λ x → refl) sentinel-laderman

--------------------------------------------------------------------------------
-- §3. 线性限制: 约束只会降低秩
--------------------------------------------------------------------------------

-- 核心等式: Σ_i (Σ_x s j x ⊗ a i x) ⊗ (b i y ⊗ c i z) ≡ Σ_x s j x ⊗ T x y z
--   读法: a 复合 s 之后, 原分解就给出限制张量的分解。
restrict-eq : ∀ {k m r} {Y Z : Set} (T : Fin m → Y → Z → Trit) (ρ : RankLE (Fin m) Y Z T r) →
  (s : Fin k → Fin m → Trit) (j : Fin k) (y : Y) (z : Z) →
  sumFin (λ i → (sumFin (λ x → (s j x) ⊗ (ra ρ i x))) ⊗ ((rb ρ i y) ⊗ (rc ρ i z))) ≡
  sumFin (λ x → (s j x) ⊗ (T x y z))
-- 隐式变量要显式绑成模式, 函数体里才用得到 m / r(类型签名里的隐式量不进作用域)
restrict-eq {m = m} {r = r} T ρ s j y z =
  let
    -- 记号: lhs i = Σ_x s j x ⊗ a i x(a 复合 s), bc i = b i y ⊗ c i z
    lhs : Fin r → Trit
    lhs i = sumFin (λ x → (s j x) ⊗ (ra ρ i x))

    bc : Fin r → Trit
    bc i = (rb ρ i y) ⊗ (rc ρ i z)

    g : Fin m → Fin r → Trit
    g x i = (bc i) ⊗ ((s j x) ⊗ (ra ρ i x))

    -- 每个项: 对调两个因子, 再把 bc 分配进对 x 的求和
    stepA : ∀ i → (lhs i) ⊗ (bc i) ≡ sumFin (λ x → g x i)
    stepA i = trans (⊗-comm (lhs i) (bc i)) (sym (sumFin-scale₃ (bc i) (s j) (ra ρ i)))

    -- 两个和交换的三步: 补单位元 T₁ → sumFin-swap₃ → 去掉单位元
    stepB1 : sumFin (λ i → sumFin (λ q → g q i)) ≡
             sumFin (λ i → (sumFin (λ q → g q i)) ⊗ T₁)
    stepB1 = sumFin-cong (λ i → sym (⊗-identityʳ (sumFin (λ q → g q i))))

    stepB2 : sumFin (λ i → (sumFin (λ q → g q i)) ⊗ T₁) ≡
             sumFin (λ q → sumFin (λ i → (g q i) ⊗ T₁))
    stepB2 = sumFin-swap₃ _ _ g (λ _ → T₁)

    stepB3 : sumFin (λ q → sumFin (λ i → (g q i) ⊗ T₁)) ≡ sumFin (λ q → sumFin (λ i → g q i))
    stepB3 = sumFin-cong (λ q → sumFin-cong (λ i → ⊗-identityʳ (g q i)))

    -- 三因子重排: bc ⊗ (s ⊗ a) ≡ s ⊗ (a ⊗ bc)
    stepC1 : ∀ x i → (bc i) ⊗ ((s j x) ⊗ (ra ρ i x)) ≡ (s j x) ⊗ ((ra ρ i x) ⊗ (bc i))
    stepC1 x i =
      trans (⊗-comm (bc i) ((s j x) ⊗ (ra ρ i x)))
            (⊗-assoc (s j x) (ra ρ i x) (bc i))

    -- 每个 x: 重排, 提公因子 s j x, 再用原分解
    stepC : ∀ x → sumFin (λ i → g x i) ≡ (s j x) ⊗ (T x y z)
    stepC x =
      trans (sumFin-cong (λ i → stepC1 x i))
            (trans (sumFin-scale₃ (s j x) (λ i → ra ρ i x) bc)
                  (cong (λ v → (s j x) ⊗ v) (rank-eq ρ x y z)))
  in
  trans (sumFin-cong stepA)
        (trans stepB1 (trans stepB2 (trans stepB3 (sumFin-cong stepC))))

-- ★ 线性限制: 子空间 span{s 0, …, s (k−1)} 上的结构常数 Σ_x s j x ⊗ T x y z 仍有 r 项分解。
--   这就是 Wang 框架 §3.1 命题 1 的「monotonicity」: 对第一个变元再加约束, 秩不升。
rank-restrict : ∀ {k m r} {Y Z : Set} (T : Fin m → Y → Z → Trit) (s : Fin k → Fin m → Trit) →
  RankLE (Fin m) Y Z T r →
  RankLE (Fin k) Y Z (λ j y z → sumFin (λ x → (s j x) ⊗ (T x y z))) r
rank-restrict T s ρ = record
  { ra = λ i j → sumFin (λ x → (s j x) ⊗ (ra ρ i x))
  ; rb = rb ρ
  ; rc = rc ρ
  ; rank-eq = restrict-eq T ρ s
  }

--------------------------------------------------------------------------------
-- §4. 对称: 两个输入对换; 三个变元轮回
--------------------------------------------------------------------------------

-- 前两个因子对换: b ⊗ (a ⊗ c) ≡ a ⊗ (b ⊗ c)
⊗-swap₁₂ : ∀ a b c → (b ⊗ (a ⊗ c)) ≡ (a ⊗ (b ⊗ c))
⊗-swap₁₂ a b c =
  trans (⊗-rot b a c) (trans (cong (λ v → c ⊗ v) (⊗-comm b a)) (sym (⊗-rot a b c)))

-- ★ 两个输入对换: Tᵗ(y,x,z) = T(x,y,z) 有分解, 只要把 a 与 b 互换
rank-swap : ∀ {X Y Z r} (T : X → Y → Z → Trit) →
  RankLE X Y Z T r → RankLE Y X Z (λ y x z → T x y z) r
rank-swap T ρ = record
  { ra = rb ρ
  ; rb = ra ρ
  ; rc = rc ρ
  ; rank-eq = λ y x z → trans (sumFin-cong (λ i → ⊗-swap₁₂ (ra ρ i x) (rb ρ i y) (rc ρ i z)))
                              (rank-eq ρ x y z)
  }

-- ★ 三个变元轮回: T′(y,z,x) = T(x,y,z) 有分解, 系数 (b, c, a)
rank-rot : ∀ {X Y Z r} (T : X → Y → Z → Trit) →
  RankLE X Y Z T r → RankLE Y Z X (λ y z x → T x y z) r
rank-rot T ρ = record
  { ra = rb ρ
  ; rb = rc ρ
  ; rc = ra ρ
  ; rank-eq = λ y z x → trans (sumFin-cong (λ i → ⊗-rot (rb ρ i y) (rc ρ i z) (ra ρ i x)))
                             (rank-eq ρ x y z)
  }

-- 哨兵: ⟨3,3,3⟩ 的转置对称与轮回对称在 Laderman 分解下的类型
sentinel-swap : RankLE (Pos 3) (Pos 3) (Out 3) (λ y x z → mm 3 x y z) 23
sentinel-swap = rank-swap (mm 3) (rankLE₃→idx 3 23 rank-laderman)

sentinel-rot : RankLE (Pos 3) (Out 3) (Pos 3) (λ y z x → mm 3 x y z) 23
sentinel-rot = rank-rot (mm 3) (rankLE₃→idx 3 23 rank-laderman)

--------------------------------------------------------------------------------
-- §5. Bläser 2003 在 n = 3 的实例（陈述, 无居民）
--------------------------------------------------------------------------------

-- R(⟨n,m,n⟩) ≥ 2mn + 2n − m − 2 (m ≥ n ≥ 3), 任意域, 秩(不是边界秩):
--   Bläser 2003, «On the complexity of the multiplication of matrices of small formats»。
--   n = m = 3: 2·9 + 6 − 3 − 2 = 19。
--   出处核对: arXiv:2603.07280v11 引言(«R(⟨n,m,n⟩) ≥ 2mn + 2n − m − 2 for m ≥ n ≥ 3 [8] over
--   arbitrary fields, which implies R(⟨3,3,3⟩) ≥ 19»; 同处注明 [8] 即上文 2003 年论文)。
--   GF(3) 是「任意域」的实例, 所以这个陈述是它的形式实例; 本库不证、无居民。
--   ⚠ 它不是「17 与 19 矛盾」: 17 是搜索给出的较弱证书, 真实的秩 ≥ 19。
bläser₃-boundary : Set
bläser₃-boundary = ∀ r → RankLE₃ 3 r → 19 ≤ r

-- 相容性: Bläser 的界蕴含库内已有的展平下界(n = 3 时 r ≥ 9)。
--   这一条只是说明陈述没有写反、也没有比已有的界更弱; 不是新结果。
bläser₃→flatten : bläser₃-boundary → ∀ r → RankLE₃ 3 r → 9 ≤ r
bläser₃→flatten B r ρ = ≤-trans (m≤m+n 9 10) (B r ρ)

-- 相容性: Laderman 的 23 项分解落在 Bläser 界之上
sentinel-compatible : bläser₃-boundary → 19 ≤ 23
sentinel-compatible B = B 23 rank-laderman
