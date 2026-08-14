{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.YangMills.YM_SpectralGap
-- 单 plaquette Wilson 转移矩阵的精确谱与质量间隙（严格化 YM_L3 的平凡 gap）
--
-- 数学背景：
--   单 plaquette、C₃ 规范群的 Wilson 转移矩阵（真空+共轭对双扇区）:
--     T = A·I + B·(R + R²)，R = 3-循环置换（C₃ 的平移表示）。
--   取 A=2, B=1:  T = [[2,1,1],[1,2,1],[1,1,2]]。
--   谱（精确整数，无连续统）:
--     λ₀ = A+2B = 4  真空（平凡表示，重数 1，刚性）
--     λ₁ = A−B  = 1  共轭对扇区（ω,ω² 退化，重数 2）
--   质量间隙 Δ = λ₀ − λ₁ = 3B = 3 > 0。
--   一致性: tr(T) = 3A = 6 = λ₀ + λ₁ + λ₁；det(T) = λ₀λ₁² = 4。
--
-- 本模块证明（0 postulate，全部 ℤ 算术 refl + λ()）:
--   §1 真空特征向量（重数 1）
--   §2 共轭对扇区: 两个退化特征向量 + C₃ 旋转下无实不动模（无刚性真空）
--   §3 质量间隙公式与正性
--   §4 谱一致性（迹 = 特征值之和；det = 特征值之积）
--   §5 2×2 Wilson 圈完整谱（全部 4 类构型）: Klein 四元群 V₄ = {I, σₓ, σ_z, σₓσ_z}，
--      类4 谱 {α,−α} ⊂ GF(9)（Frobenius 共轭对, 无 GF(3) 特征值 — 刚性）
--   §6 一般 A,B 参数的符号证明: λ₀=A+2B, λ₁=A−B, Δ=3B, tr=3A（ℤ 符号链）

module Sovereign.Problem.YangMills.YM_SpectralGap where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties
  using (+-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ;
         *-comm; *-assoc; *-identityˡ; *-identityʳ; *-distribˡ-+; *-distribʳ-+;
         neg-distrib-+; neg-involutive; *-zeroˡ; *-zeroʳ)
open import Data.Nat using (_≤_; z≤n; s≤s) renaming (_*_ to _*ℕ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.GF9
  using (GF3; GF9; alpha; gf9-one; galoisConjugate; sigma-alpha; embed-gf3;
         _+gf9_; _*gf9_; +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
         *gf9-identityˡ; *gf9-identityʳ; *gf9-comm)
open import Sovereign.RootMath.Eisenstein using (neg-*-l; neg-*-r)

infixl 20 _-₉_

-- 3 维整数状态空间（单 plaquette 的 C₃ 扇区），右嵌套元组
Vec3 : Set
Vec3 = ℤ × ℤ × ℤ

-- 转移矩阵: T = 2·I + (R + R²)
T : Vec3 → Vec3
T (x , (y , z)) =
  ((x + x) + y + z ,
   ((y + y) + x + z ,
    ((z + z) + x + y)))

-- C₃ 循环置换 R: (x,y,z) ↦ (y,z,x)
R : Vec3 → Vec3
R (x , (y , z)) = (y , (z , x))

R² : Vec3 → Vec3
R² v = R (R v)

------------------------------------------------------------------------------
-- §1. 真空（平凡表示）: λ₀ = 4，重数 1
------------------------------------------------------------------------------

vacuum : Vec3
vacuum = (+ 1 , (+ 1 , + 1))

-- T·vacuum = 4·vacuum
vacuum-eigen : T vacuum ≡ (+ 4 , (+ 4 , + 4))
vacuum-eigen = refl

------------------------------------------------------------------------------
-- §2. 共轭对扇区: λ₁ = 1，重数 2（ω,ω² 退化对）
------------------------------------------------------------------------------

mode1 : Vec3
mode1 = (+ 1 , (-[1+ 0 ] , + 0))    -- (1,−1,0)

mode2 : Vec3
mode2 = (+ 1 , (+ 0 , -[1+ 0 ]))    -- (1,0,−1)

-- T·mode1 = 1·mode1
mode1-eigen : T mode1 ≡ mode1
mode1-eigen = refl

-- T·mode2 = 1·mode2
mode2-eigen : T mode2 ≡ mode2
mode2-eigen = refl

-- 两个退化模线性独立（不同向量）
mode1≢mode2 : mode1 ≢ mode2
mode1≢mode2 = λ ()

-- 刚性判据: C₃ 旋转在共轭对扇区无实不动模
mode1-not-R-fixed : R mode1 ≢ mode1
mode1-not-R-fixed = λ ()

mode1-not-R²-fixed : R² mode1 ≢ mode1
mode1-not-R²-fixed = λ ()

-- C₃ 三次回到自身（旋转轨道闭合）
R-mode1-cycles : R (R (R mode1)) ≡ mode1
R-mode1-cycles = refl

------------------------------------------------------------------------------
-- §3. 质量间隙: Δ = λ₀ − λ₁ = 3B > 0
------------------------------------------------------------------------------

-- 间隙公式: 4 − 1 = 3
gap-formula : (+ 4) - (+ 1) ≡ + 3
gap-formula = refl

-- 间隙正性（ℕ 形式）: 0 < 3
gap-positive : 1 ≤ 3
gap-positive = s≤s z≤n

-- 间隙的一般公式（注释为证）:
--   Δ = (A+2B) − (A−B) = 3B。B=1 ⟹ Δ=3。
-- 质量间隙为正 ⟺ 耦合 B > 0 —— 与平凡构型 det(W)≠0（YM_L3）一致。

------------------------------------------------------------------------------
-- §4. 谱一致性
------------------------------------------------------------------------------

-- 迹 = 特征值之和: tr(T) = 2+2+2 = 6 = 4+1+1
trace-consistency : (+ 2 + + 2 + + 2) ≡ (+ 4 + + 1 + + 1)
trace-consistency = refl

-- 行列式 = 特征值之积: det(T) = 4 = λ₀·λ₁·λ₁
-- det[[2,1,1],[1,2,1],[1,1,2]] = 2(4−1) − 1(2−1) + 1(1−2) = 6 − 1 − 1 = 4
det-T-formula : (+ 2 * (+ 2 * + 2 - + 1 * + 1))
              - (+ 1 * (+ 1 * + 2 - + 1 * + 1))
              + (+ 1 * (+ 1 * + 1 - + 2 * + 1)) ≡ + 4
det-T-formula = refl

-- 行列式非零: det(T) ≢ 0 ⟹ 无零特征值 ⟹ 谱完全离散且正
det-nonzero : (+ 2 * (+ 2 * + 2 - + 1 * + 1))
            - (+ 1 * (+ 1 * + 2 - + 1 * + 1))
            + (+ 1 * (+ 1 * + 1 - + 2 * + 1)) ≢ + 0
det-nonzero = λ ()

------------------------------------------------------------------------------
-- §5. 2×2 Wilson 圈完整谱（全部 4 类构型）
------------------------------------------------------------------------------

-- 2×2 Wilson 圈: 单格点方环的规范不变 holonomy 分类。
-- 构型类 = Klein 四元群 V₄ = {I, σₓ, σ_z, σₓσ_z}（Pauli 矩阵 GF(3) 版, det 均非零）:
--   类1 I      = [[1,0],[0,1]]  det=1 tr=2  谱 {1,1}   ⊂ GF(3)  间隙 0   （平凡圈）
--   类2 σₓ     = [[0,1],[1,0]]  det=2 tr=0  谱 {1,2}   ⊂ GF(3)  间隙 2
--   类3 σ_z    = [[1,0],[0,2]]  det=2 tr=0  谱 {1,2}   ⊂ GF(3)  间隙 2
--   类4 σₓσ_z  = [[0,2],[1,0]]  det=1 tr=0  谱 {α,−α}  ⊂ GF(9)  间隙 2α
-- 类4 是 2×2 版的"共轭对扇区"（对照 §2 的 ω/ω²）: 谱在 GF(9) 中, 无 GF(3) 特征值 —
-- 与 galoisFixedPoint 的刚性论述一致（α² = −1 = 2）。

Mat2 : Set
Mat2 = GF9 × GF9 × GF9 × GF9

0₉ : GF9
0₉ = (T₀ , T₀)

2₉ : GF9
2₉ = (T₂ , T₀)

neg9 : GF9 → GF9
neg9 (x , y) = (negate x) , (negate y)

_-₉_ : GF9 → GF9 → GF9
x -₉ y = x +gf9 neg9 y

-- 2×2 矩阵作用 / 标量作用 / 迹 / 行列式 / 特征多项式 λ² − tr·λ + det
apply2 : Mat2 → GF9 × GF9 → GF9 × GF9
apply2 (a , (b , (c , d))) (x , y) = ((a *gf9 x) +gf9 (b *gf9 y)) , ((c *gf9 x) +gf9 (d *gf9 y))

scalar2 : GF9 → GF9 × GF9 → GF9 × GF9
scalar2 s (x , y) = (s *gf9 x) , (s *gf9 y)

tr2 : Mat2 → GF9
tr2 (a , (b , (c , d))) = a +gf9 d

det2 : Mat2 → GF9
det2 (a , (b , (c , d))) = (a *gf9 d) +gf9 (neg9 (b *gf9 c))

charpoly2 : Mat2 → GF9 → GF9
charpoly2 M r = ((r *gf9 r) +gf9 (neg9 ((tr2 M) *gf9 r))) +gf9 det2 M

-- 4 类构型
class1 : Mat2
class1 = (gf9-one , (0₉ , (0₉ , gf9-one)))        -- I

class2 : Mat2
class2 = (0₉ , (gf9-one , (gf9-one , 0₉)))        -- σₓ

class3 : Mat2
class3 = (gf9-one , (0₉ , (0₉ , 2₉)))             -- σ_z

class4 : Mat2
class4 = (0₉ , (2₉ , (gf9-one , 0₉)))             -- σₓσ_z = [[0,2],[1,0]]

-- 类1 (I): 双重特征值 1 — 全空间真空, 间隙 0
class1-eigen-e1 : apply2 class1 (gf9-one , 0₉) ≡ scalar2 gf9-one (gf9-one , 0₉)
class1-eigen-e1 = refl

class1-eigen-e2 : apply2 class1 (0₉ , gf9-one) ≡ scalar2 gf9-one (0₉ , gf9-one)
class1-eigen-e2 = refl

class1-tr : tr2 class1 ≡ gf9-one +gf9 gf9-one
class1-tr = refl

class1-det : det2 class1 ≡ gf9-one *gf9 gf9-one
class1-det = refl

class1-gap : gf9-one -₉ gf9-one ≡ 0₉
class1-gap = refl

-- 类2 (σₓ): 谱 {1,2} ⊂ GF(3), 特征向量 (1,1) 与 (1,−1)
class2-eigen-1 : apply2 class2 (gf9-one , gf9-one) ≡ scalar2 gf9-one (gf9-one , gf9-one)
class2-eigen-1 = refl

class2-eigen-2 : apply2 class2 (gf9-one , 2₉) ≡ scalar2 2₉ (gf9-one , 2₉)
class2-eigen-2 = refl

class2-tr : tr2 class2 ≡ gf9-one +gf9 2₉
class2-tr = refl

class2-det : det2 class2 ≡ gf9-one *gf9 2₉
class2-det = refl

class2-charpoly-1 : charpoly2 class2 gf9-one ≡ 0₉
class2-charpoly-1 = refl

class2-charpoly-2 : charpoly2 class2 2₉ ≡ 0₉
class2-charpoly-2 = refl

class2-gap : gf9-one -₉ 2₉ ≡ 2₉
class2-gap = refl

class2-gap-nontrivial : 2₉ ≢ 0₉
class2-gap-nontrivial = λ ()

-- 类3 (σ_z): 谱 {1,2} ⊂ GF(3), 特征向量 (1,0) 与 (0,1)
class3-eigen-1 : apply2 class3 (gf9-one , 0₉) ≡ scalar2 gf9-one (gf9-one , 0₉)
class3-eigen-1 = refl

class3-eigen-2 : apply2 class3 (0₉ , gf9-one) ≡ scalar2 2₉ (0₉ , gf9-one)
class3-eigen-2 = refl

class3-tr : tr2 class3 ≡ gf9-one +gf9 2₉
class3-tr = refl

class3-det : det2 class3 ≡ gf9-one *gf9 2₉
class3-det = refl

class3-gap : gf9-one -₉ 2₉ ≡ 2₉
class3-gap = refl

-- 类4 (σₓσ_z): 谱 {α,−α} ⊂ GF(9) — Frobenius 共轭对, 特征向量 (α,1) 与 (−α,1)
class4-eigen-alpha : apply2 class4 (alpha , gf9-one) ≡ scalar2 alpha (alpha , gf9-one)
class4-eigen-alpha = refl

class4-eigen-negalpha : apply2 class4 (neg9 alpha , gf9-one)
                        ≡ scalar2 (neg9 alpha) (neg9 alpha , gf9-one)
class4-eigen-negalpha = refl

class4-tr : tr2 class4 ≡ alpha +gf9 neg9 alpha
class4-tr = refl

class4-det : det2 class4 ≡ alpha *gf9 (neg9 alpha)
class4-det = refl

class4-charpoly-alpha : charpoly2 class4 alpha ≡ 0₉
class4-charpoly-alpha = refl

class4-charpoly-negalpha : charpoly2 class4 (neg9 alpha) ≡ 0₉
class4-charpoly-negalpha = refl

class4-gap : alpha -₉ neg9 alpha ≡ (T₀ , T₂)
class4-gap = refl

class4-gap-nontrivial : (T₀ , T₂) ≢ 0₉
class4-gap-nontrivial = λ ()

-- 类4 谱为共轭对: σ(α) = −α（σ = Frobenius）
class4-spectrum-conjugate : galoisConjugate alpha ≡ neg9 alpha
class4-spectrum-conjugate = sigma-alpha

-- 类4 无 GF(3) 特征值（刚性）: 若 GF(3) 嵌入向量是特征向量, 则该向量必为零。
-- 27-case 穷举: 谱 {α,−α} ∩ GF(3) = ∅。
class4-no-gf3-eigen : ∀ (x y r : GF3) →
  apply2 class4 (embed-gf3 x , embed-gf3 y)
    ≡ scalar2 (embed-gf3 r) (embed-gf3 x , embed-gf3 y)
  → (x ≡ T₀) × (y ≡ T₀)
class4-no-gf3-eigen T₀ T₀ _ p = refl , refl
class4-no-gf3-eigen T₀ T₁ T₀ ()
class4-no-gf3-eigen T₀ T₁ T₁ ()
class4-no-gf3-eigen T₀ T₁ T₂ ()
class4-no-gf3-eigen T₀ T₂ T₀ ()
class4-no-gf3-eigen T₀ T₂ T₁ ()
class4-no-gf3-eigen T₀ T₂ T₂ ()
class4-no-gf3-eigen T₁ T₀ T₀ ()
class4-no-gf3-eigen T₁ T₀ T₁ ()
class4-no-gf3-eigen T₁ T₀ T₂ ()
class4-no-gf3-eigen T₁ T₁ T₀ ()
class4-no-gf3-eigen T₁ T₁ T₁ ()
class4-no-gf3-eigen T₁ T₁ T₂ ()
class4-no-gf3-eigen T₁ T₂ T₀ ()
class4-no-gf3-eigen T₁ T₂ T₁ ()
class4-no-gf3-eigen T₁ T₂ T₂ ()
class4-no-gf3-eigen T₂ T₀ T₀ ()
class4-no-gf3-eigen T₂ T₀ T₁ ()
class4-no-gf3-eigen T₂ T₀ T₂ ()
class4-no-gf3-eigen T₂ T₁ T₀ ()
class4-no-gf3-eigen T₂ T₁ T₁ ()
class4-no-gf3-eigen T₂ T₁ T₂ ()
class4-no-gf3-eigen T₂ T₂ T₀ ()
class4-no-gf3-eigen T₂ T₂ T₁ ()
class4-no-gf3-eigen T₂ T₂ T₂ ()

-- 非平凡类（2/3/4）的质量间隙均非零; 平凡类（1）间隙为 0 — 完整谱分类
nontrivial-gap-all : (2₉ ≢ 0₉) × (2₉ ≢ 0₉) × ((T₀ , T₂) ≢ 0₉)
nontrivial-gap-all = (λ ()) , ((λ ()) , (λ ()))

------------------------------------------------------------------------------
-- §6. 一般 A,B 参数: 间隙公式 Δ=3B（符号证明）
------------------------------------------------------------------------------

-- 一般参数转移矩阵: T = A·I + B·(R + R²)
-- （§1-§4 为特例 A=2, B=1; 本节对任意 ℤ 参数 A,B 作符号证明）
T-sym : ℤ → ℤ → Vec3 → Vec3
T-sym A B (x , (y , z)) =
  (A * x + B * (y + z) ,
   (A * y + B * (x + z) ,
    (A * z + B * (x + y))))

0ℤ : ℤ
0ℤ = + 0

double : ∀ B → (+ 2) * B ≡ B + B
double B = begin
  (+ 2) * B
    ≡⟨⟩
  ((+ 1) + (+ 1)) * B
    ≡⟨ *-distribʳ-+ B (+ 1) (+ 1) ⟩
  (+ 1) * B + (+ 1) * B
    ≡⟨ cong₂ _+_ (*-identityˡ B) (*-identityˡ B) ⟩
  B + B
  ∎

-- λ₀ = A + 2B（真空, 符号版）
vacuum-eigen-sym : ∀ A B →
  T-sym A B vacuum ≡ ((A + (B + B)) , ((A + (B + B)) , (A + (B + B))))
vacuum-eigen-sym A B = cong₂ _,_ comp1 (cong₂ _,_ comp1 comp1)
  where
    comp1 : A * (+ 1) + B * ((+ 1) + (+ 1)) ≡ A + (B + B)
    comp1 = begin
      A * (+ 1) + B * ((+ 1) + (+ 1))
        ≡⟨ cong (λ t → t + B * ((+ 1) + (+ 1))) (*-identityʳ A) ⟩
      A + B * ((+ 1) + (+ 1))
        ≡⟨ cong (λ t → A + t) (trans (*-comm B (+ 2)) (double B)) ⟩
      A + (B + B)
      ∎

-- λ₁ = A − B（共轭对扇区 mode1, 符号版）: T·mode1 = (A−B)·mode1
mode1-eigen-sym : ∀ A B →
  T-sym A B mode1 ≡ ((A - B) , ((- (A + (- B))) , 0ℤ))
mode1-eigen-sym A B = cong₂ _,_ comp1 (cong₂ _,_ comp2 comp3)
  where
    comp1 : A * (+ 1) + B * ((- (+ 1)) + (+ 0)) ≡ A - B
    comp1 = begin
      A * (+ 1) + B * ((- (+ 1)) + (+ 0))
        ≡⟨ cong (λ t → A * (+ 1) + B * t) (+-identityʳ (- (+ 1))) ⟩
      A * (+ 1) + B * (- (+ 1))
        ≡⟨ cong₂ _+_ (*-identityʳ A) (neg-*-r B (+ 1)) ⟩
      A + (- (B * (+ 1)))
        ≡⟨ cong (λ t → A + (- t)) (*-identityʳ B) ⟩
      A + (- B)
      ∎
    comp2 : A * (- (+ 1)) + B * ((+ 1) + (+ 0)) ≡ - (A + (- B))
    comp2 = begin
      A * (- (+ 1)) + B * ((+ 1) + (+ 0))
        ≡⟨ cong₂ _+_ (neg-*-r A (+ 1)) (cong (λ t → B * t) (+-identityʳ (+ 1))) ⟩
      (- (A * (+ 1))) + B * (+ 1)
        ≡⟨ cong₂ _+_ (cong -_ (*-identityʳ A)) (*-identityʳ B) ⟩
      (- A) + B
        ≡⟨ trans (cong (λ t → (- A) + t) (sym (neg-involutive B)))
                 (sym (neg-distrib-+ A (- B))) ⟩
      - (A + (- B))
      ∎
    comp3 : A * (+ 0) + B * ((+ 1) + (- (+ 1))) ≡ 0ℤ
    comp3 = begin
      A * (+ 0) + B * ((+ 1) + (- (+ 1)))
        ≡⟨ cong₂ _+_ (*-zeroʳ A) (cong (λ t → B * t) (+-inverseʳ (+ 1))) ⟩
      0ℤ + B * (+ 0)
        ≡⟨ cong (λ t → 0ℤ + t) (*-zeroʳ B) ⟩
      0ℤ + 0ℤ
        ≡⟨⟩
      0ℤ
      ∎

-- λ₁ = A − B（共轭对扇区 mode2, 符号版）: T·mode2 = (A−B)·mode2
mode2-eigen-sym : ∀ A B →
  T-sym A B mode2 ≡ ((A - B) , (0ℤ , (- (A + (- B)))))
mode2-eigen-sym A B = cong₂ _,_ comp1 (cong₂ _,_ comp3 comp2)
  where
    comp1 : A * (+ 1) + B * ((+ 0) + (- (+ 1))) ≡ A - B
    comp1 = begin
      A * (+ 1) + B * ((+ 0) + (- (+ 1)))
        ≡⟨ cong (λ t → A * (+ 1) + B * t) (+-identityˡ (- (+ 1))) ⟩
      A * (+ 1) + B * (- (+ 1))
        ≡⟨ cong₂ _+_ (*-identityʳ A) (neg-*-r B (+ 1)) ⟩
      A + (- (B * (+ 1)))
        ≡⟨ cong (λ t → A + (- t)) (*-identityʳ B) ⟩
      A + (- B)
      ∎
    comp2 : A * (- (+ 1)) + B * ((+ 1) + (+ 0)) ≡ - (A + (- B))
    comp2 = begin
      A * (- (+ 1)) + B * ((+ 1) + (+ 0))
        ≡⟨ cong₂ _+_ (neg-*-r A (+ 1)) (cong (λ t → B * t) (+-identityʳ (+ 1))) ⟩
      (- (A * (+ 1))) + B * (+ 1)
        ≡⟨ cong₂ _+_ (cong -_ (*-identityʳ A)) (*-identityʳ B) ⟩
      (- A) + B
        ≡⟨ trans (cong (λ t → (- A) + t) (sym (neg-involutive B)))
                 (sym (neg-distrib-+ A (- B))) ⟩
      - (A + (- B))
      ∎
    comp3 : A * (+ 0) + B * ((+ 1) + (- (+ 1))) ≡ 0ℤ
    comp3 = begin
      A * (+ 0) + B * ((+ 1) + (- (+ 1)))
        ≡⟨ cong₂ _+_ (*-zeroʳ A) (cong (λ t → B * t) (+-inverseʳ (+ 1))) ⟩
      0ℤ + B * (+ 0)
        ≡⟨ cong (λ t → 0ℤ + t) (*-zeroʳ B) ⟩
      0ℤ + 0ℤ
        ≡⟨⟩
      0ℤ
      ∎

-- 注: 符号版行列式一致性 det(T) = λ₀·λ₁·λ₁ 的代数恒等
--   A(AA−BB) − B(BA−BB) + B(BB−AB) = (A+2B)(A−B)²
-- 两侧均展开为 A³ − 3AB² + 2B³（Python 符号验证通过）; 形式化需
-- *-assoc 变量乘积的 +0 包裹模式（同 Eisenstein *ᵉ-assoc comp2）,
-- 留待后续轮次（0 postulate, 不以公理驻留）。

-- 间隙公式（符号版）: Δ = λ₀ − λ₁ = (A+2B) − (A−B) = 3B
gap-formula-sym : ∀ A B → (A + (B + B)) - (A + (- B)) ≡ (B + B) + B
gap-formula-sym A B = begin
  (A + (B + B)) - (A + (- B))
    ≡⟨⟩
  (A + (B + B)) + (- (A + (- B)))
    ≡⟨ cong (λ t → (A + (B + B)) + t) (neg-distrib-+ A (- B)) ⟩
  (A + (B + B)) + ((- A) + (- (- B)))
    ≡⟨ cong (λ t → (A + (B + B)) + ((- A) + t)) (neg-involutive B) ⟩
  (A + (B + B)) + ((- A) + B)
    ≡⟨ cong (λ t → (A + (B + B)) + t) (+-comm (- A) B) ⟩
  (A + (B + B)) + (B + (- A))
    ≡⟨ sym (+-assoc (A + (B + B)) B (- A)) ⟩
  ((A + (B + B)) + B) + (- A)
    ≡⟨ cong (λ t → t + (- A)) (+-assoc A (B + B) B) ⟩
  (A + ((B + B) + B)) + (- A)
    ≡⟨ +-assoc A ((B + B) + B) (- A) ⟩
  A + (((B + B) + B) + (- A))
    ≡⟨ cong (λ t → A + t) (+-comm ((B + B) + B) (- A)) ⟩
  A + ((- A) + ((B + B) + B))
    ≡⟨ sym (+-assoc A (- A) ((B + B) + B)) ⟩
  (A + (- A)) + ((B + B) + B)
    ≡⟨ cong (λ t → t + ((B + B) + B)) (+-inverseʳ A) ⟩
  0ℤ + ((B + B) + B)
    ≡⟨ +-identityˡ ((B + B) + B) ⟩
  (B + B) + B
  ∎

-- 迹一致性（符号版）: tr(T) = 3A = λ₀ + λ₁ + λ₁
trace-sym : ∀ A B → (A + (B + B)) + (A - B) + (A - B) ≡ A + A + A
trace-sym A B = begin
  (A + (B + B)) + (A - B) + (A - B)
    ≡⟨⟩
  (A + (B + B)) + (A + (- B)) + (A + (- B))
    ≡⟨ +-assoc (A + (B + B)) (A + (- B)) (A + (- B)) ⟩
  (A + (B + B)) + ((A + (- B)) + (A + (- B)))
    ≡⟨ cong (λ t → (A + (B + B)) + t) (shuffle-2as A B) ⟩
  (A + (B + B)) + ((A + A) + ((- B) + (- B)))
    ≡⟨ cong (λ t → (A + (B + B)) + ((A + A) + t)) (sym (neg-distrib-+ B B)) ⟩
  (A + (B + B)) + ((A + A) + (- (B + B)))
    ≡⟨ cong (λ t → (A + (B + B)) + t) (+-comm (A + A) (- (B + B))) ⟩
  (A + (B + B)) + ((- (B + B)) + (A + A))
    ≡⟨ +-assoc A (B + B) ((- (B + B)) + (A + A)) ⟩
  A + ((B + B) + ((- (B + B)) + (A + A)))
    ≡⟨ cong (λ t → A + t) (sym (+-assoc (B + B) (- (B + B)) (A + A))) ⟩
  A + (((B + B) + (- (B + B))) + (A + A))
    ≡⟨ cong (λ t → A + (t + (A + A))) (+-inverseʳ (B + B)) ⟩
  A + (0ℤ + (A + A))
    ≡⟨ cong (λ t → A + t) (+-identityˡ (A + A)) ⟩
  A + (A + A)
    ≡⟨ sym (+-assoc A A A) ⟩
  A + A + A
  ∎ where
    shuffle-2as : ∀ A B → (A + (- B)) + (A + (- B)) ≡ (A + A) + ((- B) + (- B))
    shuffle-2as A B = begin
      (A + (- B)) + (A + (- B))
        ≡⟨ sym (+-assoc (A + (- B)) A (- B)) ⟩
      ((A + (- B)) + A) + (- B)
        ≡⟨ cong (λ t → t + (- B)) (+-assoc A (- B) A) ⟩
      (A + ((- B) + A)) + (- B)
        ≡⟨ cong (λ t → (A + t) + (- B)) (+-comm (- B) A) ⟩
      (A + (A + (- B))) + (- B)
        ≡⟨ +-assoc A (A + (- B)) (- B) ⟩
      A + ((A + (- B)) + (- B))
        ≡⟨ cong (λ t → A + t) (+-assoc A (- B) (- B)) ⟩
      A + (A + ((- B) + (- B)))
        ≡⟨ sym (+-assoc A A ((- B) + (- B))) ⟩
      (A + A) + ((- B) + (- B))
      ∎

------------------------------------------------------------------------------
-- 总结: 单 plaquette Wilson 转移矩阵的完整精确谱
--   §1-§4 特例 A=2,B=1: λ₀=4（真空，刚性平凡表示），λ₁=1（重数 2，ω/ω² 共轭对扇区）
--     质量间隙 Δ=3>0，tr=6，det=4。
--   §5 2×2 Wilson 圈 4 类构型（V₄）: 谱 {1,1} / {1,2} / {1,2} / {α,−α}，
--     类4 无 GF(3) 特征值（刚性），间隙 0 / 2 / 2 / 2α。
--   §6 一般 A,B 符号: λ₀=A+2B, λ₁=A−B（重数 2）, Δ=3B, tr=3A — 全 ℤ 符号链。
-- 与 GF(9) Frobenius 共轭的对应: 退化扇区 = 共轭对 (ω,ω²)，真空扇区 = 不动点
--   （刚性）——与 galoisFixedPoint 同构; 2×2 类4 的 {α,−α} 是同一结构的二维版。
------------------------------------------------------------------------------
