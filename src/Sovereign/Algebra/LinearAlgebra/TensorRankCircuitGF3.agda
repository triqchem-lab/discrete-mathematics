{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankCircuitGF3
-- M18: 电路模型与双线性归约——Lean `Bilinearize.lean:111` 的陈述层镜像
--
-- 数学背景
--   M16/M17 的秩分解见证（Strassen 七门、Laderman 23 门）都是**作为表**给出的;
--   Lean 那边秩分解还能从**算法**生产: 一个算出矩阵乘法的电路, 乘法门数 m,
--   就给出一个 2m 项的秩分解（Bilinearize.lean:111 bilinearize）。
--   机制: 在泛点（有理函数域 Rat F）上追踪每条线的混合偏导 ∂²x/∂A∂B;
--   乘积法则让每个门至多新增两个外积（mixed_mul 的两项 cross）,
--   输出端的混合偏导恰是矩阵单位（mixed_output）, 于是
--   「一切线的混合偏导落进 ≤ 2m 个外积的张成」⟹ 秩 ≤ 2m。
--
--   本件把这一环的**陈述层**镜像进库: 电路模型（表达式树）、乘法门计数、
--   Computes（正确性）、双线性归约的陈述（无居民）。
--
-- 诚实边界（本件是陈述层; 与 Lean 原件的三处系数环差距, 逐条如实标注）
--   · Lean 原件的秩落在 **Rat F**（泛点）上——这是它的关键技巧（免极化、免 char-2 问题）。
--     本件的 `bilinearize` 把秩落在 **GF(3)（Trit）原生**上; 这一步在 Lean 里不存在,
--     其真伪未证 [直觉·未验证]——有限域上「函数恒等 ⟹ 多项式恒等」会失效（Fermat:
--     A³ = A）, 是潜在障碍。带 ⊥ 型防护: 若不可证, 陈述本身无害（类型无居民）。
--   · Lean 的 Build 是 DAG 序列且带除法门（泛点上处理）; 本件是**表达式树**、无除法门
--     （GF(3) 矩阵乘法不需要除法）。树口径下 mulCount 会计入共享子表达式 [边界标注]。
--   · 因子 2 的语义: Lean 的 mixed_mul 每门两个 cross 项; 本件如实保留 2 * m。
--
-- 内容
--   §1 电路模型 Cir（inA/inB/const/add/sub/mul）、mulCount、eval
--   §2 Computes（正确性: 输出线在一切输入处取值 = 乘积条目）
--   §3 矩形秩谓词 RankLERect（镜像 Lean `Rectangle.Model` 的 RankLE I J K; 本库此前只有方形）
--      + 方阵桥 rankLE₃→rect
--   §4 ★ bilinearize（陈述, 无居民）+ 方形版 bilinearize-square
--   §5 模型哨兵: 1×1 schoolbook 的 Computes 居民（refl 可证）与 mulCount 哨兵
--
-- 复用(先查后写): RankLE₃ / oneIf / mm（TensorRankGF3）、sumFin（GF3LaplacianN）。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankCircuitGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; _⊕_; _⊗_; negate; ⊕-identityʳ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3
  using (RankLE₃; mm; oneIf; Pos; Out)

--------------------------------------------------------------------------------
-- §1. 电路模型（表达式树; 无除法门）
--------------------------------------------------------------------------------

-- 电路: 对 I×K 左输入、K×J 右输入、输出条目级的三元表达式
data Cir (I J K : ℕ) : Set where
  inA   : (Fin I × Fin K) → Cir I J K
  inB   : (Fin K × Fin J) → Cir I J K
  const : Trit → Cir I J K
  add   : Cir I J K → Cir I J K → Cir I J K
  sub   : Cir I J K → Cir I J K → Cir I J K
  mul   : Cir I J K → Cir I J K → Cir I J K

-- 乘法门计数（add/sub/const/inA/inB 不计; 镜像 Lean 的代价口径: 只数乘法门）
mulCount : ∀ {I J K} → Cir I J K → ℕ
mulCount (inA _) = zero
mulCount (inB _) = zero
mulCount (const _) = zero
mulCount (add x y) = mulCount x + mulCount y
mulCount (sub x y) = mulCount x + mulCount y
mulCount (mul x y) = suc (mulCount x + mulCount y)

-- 取值（GF(3) 上的普通算术）
eval : ∀ {I J K} → Cir I J K → (Fin I × Fin K → Trit) → (Fin K × Fin J → Trit) → Trit
eval (inA p) A B = A p
eval (inB p) A B = B p
eval (const t) A B = t
eval (add x y) A B = eval x A B ⊕ eval y A B
eval (sub x y) A B = eval x A B ⊕ negate (eval y A B)
eval (mul x y) A B = eval x A B ⊗ eval y A B

--------------------------------------------------------------------------------
-- §2. Computes: 一族输出线算出矩阵乘法
--------------------------------------------------------------------------------

-- 矩形输出位置（库里 Out n 是方形口径; 这里要 I×J）
OutR : ℕ → ℕ → Set
OutR I J = Fin I × Fin J

-- 输出线族 E 算出 I×J 输出: 每个输出位置在一切输入处取值 = (A·B) 的条目
record Computes (I J K : ℕ) (E : OutR I J → Cir I J K) : Set where
  field
    correct : ∀ (A : Fin I × Fin K → Trit) (B : Fin K × Fin J → Trit) (p : OutR I J) →
      eval (E p) A B ≡ sumFin (λ k → A (proj₁ p , k) ⊗ B (k , proj₂ p))

--------------------------------------------------------------------------------
-- §3. 矩形秩谓词（镜像 Lean `Rectangle` 的 RankLE I J K; 本库此前只有方形 RankLE₃）
--------------------------------------------------------------------------------

-- 矩形结构常数: x = 左输入位置 (i,k), y = 右输入位置 (k,j), z = 输出位置 (i,j)
mmRect : (I J K : ℕ) → (Fin I × Fin K) → (Fin K × Fin J) → (Fin I × Fin J) → Trit
mmRect I J K x y z =
  (oneIf (proj₁ x) (proj₁ z)) ⊗ ((oneIf (proj₂ x) (proj₁ y)) ⊗ (oneIf (proj₂ y) (proj₂ z)))

record RankLERect (I J K r : ℕ) : Set where
  field
    ra : Fin r → (Fin I × Fin K) → Trit
    rb : Fin r → (Fin K × Fin J) → Trit
    rc : Fin r → (Fin I × Fin J) → Trit
    rank-eq : ∀ x y z → sumFin (λ l → (ra l x) ⊗ ((rb l y) ⊗ (rc l z))) ≡ mmRect I J K x y z

-- 方阵桥: RankLE₃ n r 就是矩形版的 (n, n, n) 实例（mm 与 mmRect 逐字同构）
rankLE₃→rect : ∀ n r → RankLE₃ n r → RankLERect n n n r
rankLE₃→rect n r R = record
  { ra = RankLE₃.ra R
  ; rb = RankLE₃.rb R
  ; rc = RankLE₃.rc R
  ; rank-eq = RankLE₃.rank-eq R
  }

--------------------------------------------------------------------------------
-- §4. ★ 双线性归约的陈述（无居民; 见诚实边界）
--------------------------------------------------------------------------------

-- ℕ 上的有限和（gateTotal 用; sumFin 是 Trit 版的）
sumℕ : ∀ {n} → (Fin n → ℕ) → ℕ
sumℕ {zero} f = zero
sumℕ {suc n} f = f fzero + sumℕ {n} (λ i → f (fsuc i))

-- 输出线族的乘法门总数（树口径: 计入共享子表达式）
gateTotal : ∀ {I J K} → (OutR I J → Cir I J K) → ℕ
gateTotal {I} {J} {K} E = sumℕ {I} (λ i → sumℕ {J} (λ j → mulCount (E (i , j))))

-- ★ 陈述: 算出 I×J 乘积的电路给出 2m 项矩形秩分解（镜像 Bilinearize.lean:111）
--   Lean 原件在 Rat F 上是定理; 本处系数环换成 GF(3)（Trit 原生）——未证 [直觉·未验证]。
bilinearize : (I J K : ℕ) → Set
bilinearize I J K =
  ∀ (E : OutR I J → Cir I J K) → Computes I J K E → RankLERect I J K (2 * gateTotal E)

-- 方形版（与我们的 Saving₃/ω 线衔接的形状）
bilinearize-square : (n : ℕ) → Set
bilinearize-square n = bilinearize n n n

--------------------------------------------------------------------------------
-- §5. 模型哨兵: 1×1 schoolbook
--------------------------------------------------------------------------------

-- 1×1 schoolbook: 输出线 = mul (inA (z,z)) (inB (z,z))
schoolbook : OutR 1 1 → Cir 1 1 1
schoolbook p = mul (inA (fzero , fzero)) (inB (fzero , fzero))

-- mulCount 哨兵: 单门 = 1
schoolbook-mulCount : mulCount (schoolbook (fzero , fzero)) ≡ 1
schoolbook-mulCount = refl

-- gateTotal 哨兵: 1×1 输出族共 1 门
schoolbook-gateTotal : gateTotal (schoolbook) ≡ 1
schoolbook-gateTotal = refl

-- ★ Computes 居民（具名引理; sumFin {1} 尾部多一层 ⊕ T₀, 用 ⊕-identityʳ 收掉）
schoolbook-correct : ∀ (A : Fin 1 × Fin 1 → Trit) (B : Fin 1 × Fin 1 → Trit)
  (p : OutR 1 1) →
  eval (schoolbook p) A B ≡ sumFin (λ k → A (proj₁ p , k) ⊗ B (k , proj₂ p))
schoolbook-correct A B (fzero , fzero) =
  sym (⊕-identityʳ (A (fzero , fzero) ⊗ B (fzero , fzero)))

schoolbook-computes : Computes 1 1 1 schoolbook
Computes.correct schoolbook-computes = schoolbook-correct

-- mm 侧哨兵: 1×1 结构常数在 (z,z,z) 处是 T₁
mm-1-1-sentinel : mm 1 (fzero , fzero) (fzero , fzero) (fzero , fzero) ≡ T₁
mm-1-1-sentinel = refl
