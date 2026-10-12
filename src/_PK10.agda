{-# OPTIONS --rewriting --guardedness #-}

-- | _PK10
-- K(E10) 截断商小片：E10/截断理想的不忠实（截断核见证）
--
-- ⚠ **边界句（强制）**：本件证「**E10/截断理想**（截断词代数商 T_d = U/I_d）的不忠实」——
--   **非 E10 本身**（后者需 PBW 基 + 核元素独立工作）；一切结论限定于截断商，
--   不得外推为 E10 全形表示不忠实。
--
-- 数学背景：广义 Cartan 矩阵 g(A) 的包络代数 U 中，截断理想 I_d = 词长 > d 的词
--   张成的双边理想；商代数 T_d = U/I_d 的表示 ρ 若存在非零元映为零，则 ρ 不忠实。
--   本件在截断词代数上构造 2×2 GF(3) 矩阵表示与截断核见证（深度 2 实例）。
--
-- 核心原则：
--   1. 截断理想入定义（TAlg data 形——tzero 承载 I_d 坍缩）
--   2. 表示 = 乘积扩展（ρw g w = 生成元矩阵按词序乘积——一般 hom 立界，实例级核对）
--   3. 核见证 = 构造性（w* ≢ tzero 且 ρ w* ≡ 0M——构造子相异 + refl 级）
--   4. E10 衔接 = GACM 条件形（KacMoodyPresentation 注记面）+ 零型对选点
--
-- 包含：GACM · TAlg 截断词代数 · Mat2/⋆/ρw · ker-witness · 零型对核对 · 边界层

module _PK10 where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≤?_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- ────────────────────────────────────────────────────────────────────
-- ① GACM（广义 Cartan 条件形——KacMoodyPresentation 注记衔接）
--    E10 面 = n 10 的实例（具体 10×10 表 = 常数面，随 PBW 全形批立界）；
--    本小片以 A₃ 链实例承载条件形核对。
-- ────────────────────────────────────────────────────────────────────

record GACM : Set where
  field
    n      : ℕ
    a      : ℕ → ℕ → ℤ
    diag-2 : ∀ i → i < n → a i i ≡ + 2
    sym-0  : ∀ i j → a i j ≡ + 0 → a j i ≡ + 0

-- A₃ 链实例：节点 0—1—2（链），aᵢⱼ = 2（对角）/ -1（邻接）/ 0（其余）
-- （3+ 节点尾段常值零面——镜像递归会造假邻接，具象 14 子句全覆盖）
a₃ : ℕ → ℕ → ℤ
a₃ zero zero                        = + 2
a₃ zero (suc zero)                  = -[1+ 0 ]
a₃ zero (suc (suc _))               = + 0
a₃ (suc zero) zero                  = -[1+ 0 ]
a₃ (suc zero) (suc zero)            = + 2
a₃ (suc zero) (suc (suc zero))      = -[1+ 0 ]
a₃ (suc zero) (suc (suc (suc _)))   = + 0
a₃ (suc (suc _)) zero               = + 0
a₃ (suc (suc zero)) (suc zero)      = -[1+ 0 ]
a₃ (suc (suc (suc _))) (suc zero)   = + 0
a₃ (suc (suc zero)) (suc (suc zero)) = + 2
a₃ (suc (suc zero)) (suc (suc (suc _))) = + 0
a₃ (suc (suc (suc _))) (suc (suc zero)) = + 0
a₃ (suc (suc (suc _))) (suc (suc (suc _))) = + 0

a₃-diag : ∀ i → i < 3 → a₃ i i ≡ + 2
a₃-diag zero _ = refl
a₃-diag (suc zero) _ = refl
a₃-diag (suc (suc zero)) _ = refl
a₃-diag (suc (suc (suc i))) (s≤s (s≤s (s≤s ())))

a₃-sym-0 : ∀ i j → a₃ i j ≡ + 0 → a₃ j i ≡ + 0
a₃-sym-0 zero (suc (suc _)) _ = refl
a₃-sym-0 (suc zero) (suc (suc (suc _))) _ = refl
a₃-sym-0 (suc (suc zero)) zero _ = refl
a₃-sym-0 (suc (suc zero)) (suc (suc (suc _))) _ = refl
a₃-sym-0 (suc (suc (suc _))) zero _ = refl
a₃-sym-0 (suc (suc (suc _))) (suc zero) _ = refl
a₃-sym-0 (suc (suc (suc _))) (suc (suc zero)) _ = refl
a₃-sym-0 (suc (suc (suc i))) (suc (suc (suc j))) _ = refl
a₃-sym-0 zero zero ()
a₃-sym-0 zero (suc zero) ()
a₃-sym-0 (suc zero) zero ()
a₃-sym-0 (suc zero) (suc zero) ()
a₃-sym-0 (suc zero) (suc (suc zero)) ()
a₃-sym-0 (suc (suc zero)) (suc zero) ()
a₃-sym-0 (suc (suc zero)) (suc (suc zero)) ()

gacm-a₃ : GACM
gacm-a₃ = record { n = 3 ; a = a₃ ; diag-2 = λ i → a₃-diag i ; sym-0 = a₃-sym-0 }

-- 零型对核对：(0,2) 非邻接（E10 面的零型对选点先例）
zp-02 : a₃ zero (suc (suc zero)) ≡ + 0
zp-02 = refl

-- ────────────────────────────────────────────────────────────────────
-- ② TAlg（截断词代数 T_d = U/I_d——截断理想 I_d 入定义）
--    tzero 承载 I_d 坍缩（词长 > d 的词归零）；word 承载 ≤ d 词基。
-- ────────────────────────────────────────────────────────────────────

data TAlg (d : ℕ) : Set where
  tzero : TAlg d
  word  : (w : List ℕ) → length w ≤ d → TAlg d

-- 截断拼接（代数乘法面：词拼接超深则坍缩入 I_d）
catW : (d : ℕ) → List ℕ → List ℕ → TAlg d
catW d w₁ w₂ with length (w₁ ++ w₂) ≤? d
... | yes p = word (w₁ ++ w₂) p
... | no _  = tzero

-- ────────────────────────────────────────────────────────────────────
-- ③ Mat2（GF(3) 2×2 矩阵）+ 表示面
-- ────────────────────────────────────────────────────────────────────

record Mat2 : Set where
  constructor mk2
  field
    m00 m01 m10 m11 : Trit

_⋆_ : Mat2 → Mat2 → Mat2
mk2 a00 a01 a10 a11 ⋆ mk2 b00 b01 b10 b11 =
  mk2 ((a00 ⊗ b00) ⊕ (a01 ⊗ b10)) ((a00 ⊗ b01) ⊕ (a01 ⊗ b11))
      ((a10 ⊗ b00) ⊕ (a11 ⊗ b10)) ((a10 ⊗ b01) ⊕ (a11 ⊗ b11))

0M : Mat2
0M = mk2 T₀ T₀ T₀ T₀

1M : Mat2
1M = mk2 T₁ T₀ T₀ T₁

-- 生成元表示：g : 节点索引 → Mat2（Mat2 = End(FAb 2) 的矩阵形）
ρw : (g : ℕ → Mat2) → List ℕ → Mat2
ρw g []       = 1M
ρw g (x ∷ w)  = g x ⋆ ρw g w

ρ-gen : {d : ℕ} (g : ℕ → Mat2) → TAlg d → Mat2
ρ-gen g tzero      = 0M
ρ-gen g (word w _) = ρw g w

-- ────────────────────────────────────────────────────────────────────
-- ④ 核非平凡元素（截断核见证——深度 2 实例）
--    生成元矩阵：g 0 = M0（秩 1 投影），g 1 = M1（下三角幂零）⇒ M0 ⋆ M1 = 0M
--    见证词 w* = 0 ∷ 1 ∷ []（长度 2 ≤ 2——零型对词，Serre 深度 3 不触及）
-- ────────────────────────────────────────────────────────────────────

M0 M1 : Mat2
M0 = mk2 T₁ T₀ T₀ T₀
M1 = mk2 T₀ T₀ T₁ T₀

g₁₀ : ℕ → Mat2
g₁₀ zero            = M0
g₁₀ (suc zero)      = M1
g₁₀ (suc (suc _))   = 0M

w* : List ℕ
w* = zero ∷ suc zero ∷ []

len-w* : length w* ≤ 2
len-w* = s≤s (s≤s z≤n)

w*t : TAlg 2
w*t = word w* len-w*

-- 主见证①：ρ(w*) = 0M（refl 级——M0 ⋆ M1 逐分量 T₀ 归约）
ker-w* : ρ-gen g₁₀ w*t ≡ 0M
ker-w* = refl

-- 主见证②：w* ≢ tzero（构造子相异——截断代数中非零）
w*-nz : w*t ≢ tzero
w*-nz ()

-- 不忠实定义（NotFaithful 形——TrivialRepUnfaithful 口径迁移：核含非零元）
NotFaithfulT : {d : ℕ} → (TAlg d → Mat2) → Set
NotFaithfulT {d} ρ = Σ (TAlg d) (λ x → x ≢ tzero × ρ x ≡ 0M)

-- 主定理：深度 2 截断商上 ρ-gen g₁₀ 不忠实
ker-witness : NotFaithfulT (ρ-gen g₁₀)
ker-witness = w*t , w*-nz , ker-w*

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 核对层（值面 refl 级）
-- ────────────────────────────────────────────────────────────────────

-- M0 ⋆ M1 逐分量展开核对（与 ker-w* 同形自证）
check-mul-01 : M0 ⋆ M1 ≡ 0M
check-mul-01 = refl

-- ρ 空词 = 单位（nilT 具名钉 d）
nilT : TAlg 2
nilT = word [] z≤n

check-rho-nil : ρ-gen g₁₀ nilT ≡ 1M
check-rho-nil = refl

-- 见证词乘积展开（ρw 定义形核对：ρw [0,1] = M0 ⋆ (M1 ⋆ 1M)）
check-rho-w* : ρw g₁₀ w* ≡ M0 ⋆ (M1 ⋆ 1M)
check-rho-w* = refl

-- 零型对核对（GACM 面）
check-zp-02 : a₃ zero (suc (suc zero)) ≡ + 0
check-zp-02 = refl

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 边界层（立界注记——无空壳签名）
--    (i) 一般 hom 定理 ρw (w₁++w₂) ≡ ρw w₁ ⋆ ρw w₂（Mat2 ⋆-assoc 承载——
--        常数推导 8 项和面，与 Mat3/Laurent 线同类立界）
--    (ii) E10 具体 10×10 Cartan 表（常数面——随 PBW 全形批）
--    (iii) Serre 关系全族与真截断商 U(g(E10))/I_d 的对应（零型对词 eᵢeⱼ 在
--        Serre 深度 3 关系下不可消——注记级；形式化需 KacMoodyPresentation
--        关系字段扩展）
--    (iv) E10 本身不忠实（PBW 基 + 核元素——独立深件，边界句已锚）
-- ────────────────────────────────────────────────────────────────────
