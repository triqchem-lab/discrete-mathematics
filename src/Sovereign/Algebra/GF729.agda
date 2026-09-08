{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GF729
-- GF(3⁶) = GF(729) 与 T⁶ 格点的连接
--
-- 核心定理:
--   ① GF(729) 的加法群 ≅ (Z/3Z)⁶ — T⁶ 格点的加法结构
--   ② 729 = 3⁶ 的分解: 9×81, 27×27, 3×243
--   ③ T6Lattice = Vec (Fin 3) 6 = GF729Vec (定义等式)
--   ④ 涡旋塔: 3⁶ = 729 vs 12⁶ = 2985984 = 729 × 4096
--   ⑤ Burnside 轨道算术: 54 × 14 = 756 = 729 + 27
--
-- 数学背景:
--   T⁶ = (Z/3Z)⁶ 有 3⁶ = 729 个格点
--   GF(729) = GF(3⁶) 是 GF(3) 的 6 次扩张, 有 729 个元素
--   作为集合, 两者等势; 作为加法群, GF(729)⁺ ≅ (Z/3Z)⁶
--   T⁶ 是 GF(729) 加法群的"展开"——向量空间表示
--   GF(729) 的乘法结构 (域) 太复杂, 本模块只形式化加法群
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.GF729 where

open import Data.Nat using (ℕ; _+_; _*_) renaming (_^_ to _^ℕ_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; zipWith)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
         tritToFin3; fin3ToTrit; tr-to-f3-to-tr; f3-to-tr-to-f3;
         ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse;
         ⊗-identityʳ; ⊗-zeroʳ;
         negate; negate²)

open import Sovereign.Structology.T6
  using (T6Lattice; GF3; t6Cardinality; toℕ-sum)

-- 展示群相位源: GF(9) = GF(3)[α]/(α²+1) 与 90° 旋转群 ⟨α⟩ ≅ C₄
open import Sovereign.Algebra.GF9
  using (GF9; alpha; galoisConjugate; _*gf9_)
open import Sovereign.Algebra.GroupTheory.DuodecClock
  using (AlphaPower; mulAlpha)
  renaming (a0 to p0; a1 to p1; a2 to p2; a3 to p3)

--------------------------------------------------------------------------------
-- §1. GF(3) 在 Fin 3 上的加法群结构
--
-- Fin 3 = {0, 1, 2} 与 Trit = {T₀, T₁, T₂} 通过 tritToFin3/fin3ToTrit 双射
-- GF(3) 加法 (mod 3) 在 Fin 3 上的直接定义
-- 所有群公理由有限穷举 refl 证明
--------------------------------------------------------------------------------

-- GF(3) 加法 on Fin 3 (mod 3, 与 Trit ⊕ 通过桥接对齐)
_+₃_ : Fin 3 → Fin 3 → Fin 3
zero           +₃ y            = y
suc zero       +₃ zero         = suc zero
suc zero       +₃ suc zero     = suc (suc zero)
suc zero       +₃ suc (suc zero) = zero
suc (suc zero) +₃ zero         = suc (suc zero)
suc (suc zero) +₃ suc zero     = zero
suc (suc zero) +₃ suc (suc zero) = suc zero

-- GF(3) 取反 on Fin 3 (-0=0, -1=2, -2=1)
neg₃ : Fin 3 → Fin 3
neg₃ zero           = zero
neg₃ (suc zero)     = suc (suc zero)
neg₃ (suc (suc zero)) = suc zero

-- GF(3) 零元
gf3-zero : Fin 3
gf3-zero = zero

--------------------------------------------------------------------------------
-- §1b. GF(3) 群公理 — 有限穷举 refl
--------------------------------------------------------------------------------

-- 加法单位元
+₃-identityˡ : ∀ (x : Fin 3) → gf3-zero +₃ x ≡ x
+₃-identityˡ zero           = refl
+₃-identityˡ (suc zero)     = refl
+₃-identityˡ (suc (suc zero)) = refl

+₃-identityʳ : ∀ (x : Fin 3) → x +₃ gf3-zero ≡ x
+₃-identityʳ zero           = refl
+₃-identityʳ (suc zero)     = refl
+₃-identityʳ (suc (suc zero)) = refl

-- 加法交换律 (9 case)
+₃-comm : ∀ (x y : Fin 3) → x +₃ y ≡ y +₃ x
+₃-comm zero           zero           = refl
+₃-comm zero           (suc zero)     = refl
+₃-comm zero           (suc (suc zero)) = refl
+₃-comm (suc zero)     zero           = refl
+₃-comm (suc zero)     (suc zero)     = refl
+₃-comm (suc zero)     (suc (suc zero)) = refl
+₃-comm (suc (suc zero)) zero           = refl
+₃-comm (suc (suc zero)) (suc zero)     = refl
+₃-comm (suc (suc zero)) (suc (suc zero)) = refl

-- 加法结合律 (27 case)
+₃-assoc : ∀ (x y z : Fin 3) → (x +₃ y) +₃ z ≡ x +₃ (y +₃ z)
+₃-assoc zero           y            z            = refl
+₃-assoc (suc zero)     zero         z            = refl
+₃-assoc (suc zero)     (suc zero)   zero         = refl
+₃-assoc (suc zero)     (suc zero)   (suc zero)   = refl
+₃-assoc (suc zero)     (suc zero)   (suc (suc zero)) = refl
+₃-assoc (suc zero)     (suc (suc zero)) zero     = refl
+₃-assoc (suc zero)     (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc zero)     (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) zero         z         = refl
+₃-assoc (suc (suc zero)) (suc zero)   zero       = refl
+₃-assoc (suc (suc zero)) (suc zero)   (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc zero)   (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) zero   = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

-- 加法逆元
+₃-inverse : ∀ (x : Fin 3) → x +₃ neg₃ x ≡ gf3-zero
+₃-inverse zero           = refl
+₃-inverse (suc zero)     = refl
+₃-inverse (suc (suc zero)) = refl

-- 取反对合
neg₃² : ∀ (x : Fin 3) → neg₃ (neg₃ x) ≡ x
neg₃² zero           = refl
neg₃² (suc zero)     = refl
neg₃² (suc (suc zero)) = refl

--------------------------------------------------------------------------------
-- §1c. Fin 3 加法与 Trit ⊕ 的桥接一致性
--
-- tritToFin3 (a ⊕ b) ≡ tritToFin3 a +₃ tritToFin3 b
-- 即双射保持加法结构 (群同态)
--------------------------------------------------------------------------------

⊕-+₃-hom : ∀ (a b : Trit) → tritToFin3 (a ⊕ b) ≡ tritToFin3 a +₃ tritToFin3 b
⊕-+₃-hom T₀ T₀ = refl; ⊕-+₃-hom T₀ T₁ = refl; ⊕-+₃-hom T₀ T₂ = refl
⊕-+₃-hom T₁ T₀ = refl; ⊕-+₃-hom T₁ T₁ = refl; ⊕-+₃-hom T₁ T₂ = refl
⊕-+₃-hom T₂ T₀ = refl; ⊕-+₃-hom T₂ T₁ = refl; ⊕-+₃-hom T₂ T₂ = refl

-- 反向桥接也保持加法
+₃-⊕-hom : ∀ (x y : Fin 3) → fin3ToTrit (x +₃ y) ≡ fin3ToTrit x ⊕ fin3ToTrit y
+₃-⊕-hom zero           zero           = refl
+₃-⊕-hom zero           (suc zero)     = refl
+₃-⊕-hom zero           (suc (suc zero)) = refl
+₃-⊕-hom (suc zero)     zero           = refl
+₃-⊕-hom (suc zero)     (suc zero)     = refl
+₃-⊕-hom (suc zero)     (suc (suc zero)) = refl
+₃-⊕-hom (suc (suc zero)) zero           = refl
+₃-⊕-hom (suc (suc zero)) (suc zero)     = refl
+₃-⊕-hom (suc (suc zero)) (suc (suc zero)) = refl

--------------------------------------------------------------------------------
-- §2. GF(3⁶) = (Z/3Z)⁶ — 6 维向量空间上的加法群
--
-- GF729Vec = Vec (Fin 3) 6 — 与 T6Lattice 定义等式
-- 加法: 逐分量 GF(3) 加法
-- 零元: 全零向量
-- 逆元: 逐分量取反
--------------------------------------------------------------------------------

-- GF(3⁶) 的载体: 6 维 GF(3) 向量
-- 注意: 这与 T6Lattice = Vec GF3 6 = Vec (Fin 3) 6 定义等式
GF729Vec : Set
GF729Vec = Vec (Fin 3) 6

-- 零向量 (加法单位元)
gf729-zero : GF729Vec
gf729-zero = zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []

-- 逐分量 GF(3) 加法
_+gf729_ : GF729Vec → GF729Vec → GF729Vec
(a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) +gf729 (b5 ∷ b4 ∷ b3 ∷ b2 ∷ b1 ∷ b0 ∷ []) =
  (a5 +₃ b5) ∷ (a4 +₃ b4) ∷ (a3 +₃ b3) ∷ (a2 +₃ b2) ∷ (a1 +₃ b1) ∷ (a0 +₃ b0) ∷ []

-- 逐分量取反 (加法逆元)
neg729 : GF729Vec → GF729Vec
neg729 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) =
  neg₃ a5 ∷ neg₃ a4 ∷ neg₃ a3 ∷ neg₃ a2 ∷ neg₃ a1 ∷ neg₃ a0 ∷ []

--------------------------------------------------------------------------------
-- §3. GF(3⁶) 加法群公理 — 逐分量从 GF(3) 提升
--
-- 策略: 每个公理在 6 个分量上独立成立 (由 §1b 的 refl 证明)
-- 用 cong₂ _∷_ 链逐分量组装
--------------------------------------------------------------------------------

-- 加法单位元 (左)
+gf729-identityˡ : ∀ (x : GF729Vec) → gf729-zero +gf729 x ≡ x
+gf729-identityˡ (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ []) =
  cong₂ _∷_ (+₃-identityˡ x5) (
  cong₂ _∷_ (+₃-identityˡ x4) (
  cong₂ _∷_ (+₃-identityˡ x3) (
  cong₂ _∷_ (+₃-identityˡ x2) (
  cong₂ _∷_ (+₃-identityˡ x1) (
  cong₂ _∷_ (+₃-identityˡ x0) refl)))))

-- 加法单位元 (右)
+gf729-identityʳ : ∀ (x : GF729Vec) → x +gf729 gf729-zero ≡ x
+gf729-identityʳ (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ []) =
  cong₂ _∷_ (+₃-identityʳ x5) (
  cong₂ _∷_ (+₃-identityʳ x4) (
  cong₂ _∷_ (+₃-identityʳ x3) (
  cong₂ _∷_ (+₃-identityʳ x2) (
  cong₂ _∷_ (+₃-identityʳ x1) (
  cong₂ _∷_ (+₃-identityʳ x0) refl)))))

-- 加法交换律
+gf729-comm : ∀ (x y : GF729Vec) → x +gf729 y ≡ y +gf729 x
+gf729-comm (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ [])
            (y5 ∷ y4 ∷ y3 ∷ y2 ∷ y1 ∷ y0 ∷ []) =
  cong₂ _∷_ (+₃-comm x5 y5) (
  cong₂ _∷_ (+₃-comm x4 y4) (
  cong₂ _∷_ (+₃-comm x3 y3) (
  cong₂ _∷_ (+₃-comm x2 y2) (
  cong₂ _∷_ (+₃-comm x1 y1) (
  cong₂ _∷_ (+₃-comm x0 y0) refl)))))

-- 加法结合律
+gf729-assoc : ∀ (x y z : GF729Vec) → (x +gf729 y) +gf729 z ≡ x +gf729 (y +gf729 z)
+gf729-assoc (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ [])
             (y5 ∷ y4 ∷ y3 ∷ y2 ∷ y1 ∷ y0 ∷ [])
             (z5 ∷ z4 ∷ z3 ∷ z2 ∷ z1 ∷ z0 ∷ []) =
  cong₂ _∷_ (+₃-assoc x5 y5 z5) (
  cong₂ _∷_ (+₃-assoc x4 y4 z4) (
  cong₂ _∷_ (+₃-assoc x3 y3 z3) (
  cong₂ _∷_ (+₃-assoc x2 y2 z2) (
  cong₂ _∷_ (+₃-assoc x1 y1 z1) (
  cong₂ _∷_ (+₃-assoc x0 y0 z0) refl)))))

-- 加法逆元
+gf729-inverse : ∀ (x : GF729Vec) → x +gf729 neg729 x ≡ gf729-zero
+gf729-inverse (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ []) =
  cong₂ _∷_ (+₃-inverse x5) (
  cong₂ _∷_ (+₃-inverse x4) (
  cong₂ _∷_ (+₃-inverse x3) (
  cong₂ _∷_ (+₃-inverse x2) (
  cong₂ _∷_ (+₃-inverse x1) (
  cong₂ _∷_ (+₃-inverse x0) refl)))))

-- 取反对合
neg729² : ∀ (x : GF729Vec) → neg729 (neg729 x) ≡ x
neg729² (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ []) =
  cong₂ _∷_ (neg₃² x5) (
  cong₂ _∷_ (neg₃² x4) (
  cong₂ _∷_ (neg₃² x3) (
  cong₂ _∷_ (neg₃² x2) (
  cong₂ _∷_ (neg₃² x1) (
  cong₂ _∷_ (neg₃² x0) refl)))))

--------------------------------------------------------------------------------
-- §4. 729 的分解 — 算术验证
--
-- 729 = 3⁶ 是 T⁶ 格点总数
-- 分解路径:
--   729 = 3 × 243 = 3 × 3⁵
--   729 = 9 × 81  = 3² × 3⁴  (GF(9) × GF(3⁴) 加法群)
--   729 = 27 × 27 = 3³ × 3³  (对称分解)
--------------------------------------------------------------------------------

-- 3⁶ = 729 (与 T6.t6Cardinality 一致)
pow-3-6 : 3 ^ℕ 6 ≡ 729
pow-3-6 = refl

-- 729 = 3 × 243
decomp-3×243 : 3 * 243 ≡ 729
decomp-3×243 = refl

-- 729 = 9 × 81 (GF(9) 加法群 × GF(3⁴) 加法群)
decomp-9×81 : 9 * 81 ≡ 729
decomp-9×81 = refl

-- 729 = 27 × 27 (对称分解: GF(3³) × GF(3³))
decomp-27×27 : 27 * 27 ≡ 729
decomp-27×27 = refl

-- 幂次链: 3⁰=1, 3¹=3, 3²=9, 3³=27, 3⁴=81, 3⁵=243, 3⁶=729
pow-3-0 : 3 ^ℕ 0 ≡ 1   ; pow-3-0 = refl
pow-3-1 : 3 ^ℕ 1 ≡ 3   ; pow-3-1 = refl
pow-3-2 : 3 ^ℕ 2 ≡ 9   ; pow-3-2 = refl
pow-3-3 : 3 ^ℕ 3 ≡ 27  ; pow-3-3 = refl
pow-3-4 : 3 ^ℕ 4 ≡ 81  ; pow-3-4 = refl
pow-3-5 : 3 ^ℕ 5 ≡ 243 ; pow-3-5 = refl

-- 指数加法: 3^(a+b) = 3^a × 3^b 的实例
-- 3⁶ = 3² × 3⁴ = 9 × 81
exp-add-2+4 : 3 ^ℕ 2 * 3 ^ℕ 4 ≡ 3 ^ℕ 6
exp-add-2+4 = refl

-- 3⁶ = 3³ × 3³ = 27 × 27
exp-add-3+3 : 3 ^ℕ 3 * 3 ^ℕ 3 ≡ 3 ^ℕ 6
exp-add-3+3 = refl

--------------------------------------------------------------------------------
-- §5. 与 T⁶ 的连接
--
-- T6Lattice = Vec GF3 6 = Vec (Fin 3) 6 = GF729Vec
-- 这是定义等式——不需要证明, 它们是同一个类型
--
-- 数学含义:
--   T⁶ 格点 = GF(729) 加法群的元素
--   T⁶ 上的平移 = GF(729) 的加法
--   t6Cardinality 证明 |T6Lattice| = 729
--------------------------------------------------------------------------------

-- T6Lattice 与 GF729Vec 的定义等式
-- 两者都是 Vec (Fin 3) 6, 无需证明
t6-is-gf729 : T6Lattice ≡ GF729Vec
t6-is-gf729 = refl

-- T⁶ 格点基数 = 729 (从 T6.agda 导入)
-- t6Cardinality : (3 ^ℕ 6) ≡ 729
-- 本模块的 pow-3-6 与之独立验证一致
t6-card-verify : t6Cardinality ≡ pow-3-6
t6-card-verify = refl

-- GF(729) 加法群的零元就是 T⁶ 的原点
gf729-zero-is-origin : gf729-zero ≡ (zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ [])
gf729-zero-is-origin = refl

--------------------------------------------------------------------------------
-- §5b. GF(3⁶) 加法群的维度分解
--
-- (Z/3Z)⁶ ≅ (Z/3Z)² × (Z/3Z)⁴  (前2维 × 后4维)
-- 对应 729 = 9 × 81
--
-- (Z/3Z)⁶ ≅ (Z/3Z)³ × (Z/3Z)³  (前3维 × 后3维)
-- 对应 729 = 27 × 27
--------------------------------------------------------------------------------

-- 前 2 维投影
proj-first2 : GF729Vec → Vec (Fin 3) 2
proj-first2 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = a5 ∷ a4 ∷ []

-- 后 4 维投影
proj-last4 : GF729Vec → Vec (Fin 3) 4
proj-last4 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = a3 ∷ a2 ∷ a1 ∷ a0 ∷ []

-- 前 3 维投影
proj-first3 : GF729Vec → Vec (Fin 3) 3
proj-first3 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = a5 ∷ a4 ∷ a3 ∷ []

-- 后 3 维投影
proj-last3 : GF729Vec → Vec (Fin 3) 3
proj-last3 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = a2 ∷ a1 ∷ a0 ∷ []

-- 2+4 分解: 前2维投影保持加法 (逐分量)
proj-first2-add : ∀ (x y : GF729Vec) →
  proj-first2 (x +gf729 y) ≡ zipWith _+₃_ (proj-first2 x) (proj-first2 y)
proj-first2-add (x5 ∷ x4 ∷ x3 ∷ x2 ∷ x1 ∷ x0 ∷ [])
                (y5 ∷ y4 ∷ y3 ∷ y2 ∷ y1 ∷ y0 ∷ []) = refl

-- 维度分解的基数验证
-- |Vec (Fin 3) 2| = 3² = 9
card-vec2 : 3 ^ℕ 2 ≡ 9
card-vec2 = refl

-- |Vec (Fin 3) 4| = 3⁴ = 81
card-vec4 : 3 ^ℕ 4 ≡ 81
card-vec4 = refl

-- |Vec (Fin 3) 3| = 3³ = 27
card-vec3 : 3 ^ℕ 3 ≡ 27
card-vec3 = refl

-- 9 × 81 = 729 (2+4 分解的基数)
card-2+4 : 3 ^ℕ 2 * 3 ^ℕ 4 ≡ 729
card-2+4 = refl

-- 27 × 27 = 729 (3+3 分解的基数)
card-3+3 : 3 ^ℕ 3 * 3 ^ℕ 3 ≡ 729
card-3+3 = refl

--------------------------------------------------------------------------------
-- §6. 与涡旋塔的连接
--
-- 涡旋根 123: 3 → 6 → 12 是倍频量子纠缠链
-- 3⁶ = 729 是 GF(3) 的 6 次扩张的阶
-- 12⁶ = 2985984 是十二律体系的 6 维展开
--
-- 关键关系: 12⁶ = 3⁶ × 4⁶ = 729 × 4096
-- 即十二律的 6 维空间 = GF(3)⁶ × (Z/4Z)⁶
-- 3-部分 (GF(3)⁶) 和 4-部分 (Z/4Z)⁶ 正交分解
--------------------------------------------------------------------------------

-- 12⁶ = 2985984
pow-12-6 : 12 ^ℕ 6 ≡ 2985984
pow-12-6 = refl

-- 4⁶ = 4096
pow-4-6 : 4 ^ℕ 6 ≡ 4096
pow-4-6 = refl

-- 12⁶ = 3⁶ × 4⁶ (正交分解: 3-部分 × 4-部分)
-- (3×4)⁶ = 3⁶ × 4⁶
pow-12-split : 12 ^ℕ 6 ≡ 3 ^ℕ 6 * 4 ^ℕ 6
pow-12-split = refl

-- 729 × 4096 = 2985984 (数值验证)
gf729×4096 : 729 * 4096 ≡ 2985984
gf729×4096 = refl

-- 涡旋塔中 3ⁿ 的位置
-- 3¹ = 3   (GF(3), 基频)
-- 3² = 9   (GF(9), 二次扩张)
-- 3³ = 27  (GF(27), 三次扩张)
-- 3⁶ = 729 (GF(729), 六次扩张 = T⁶ 格点)
vortex-tower-3n : 3 ^ℕ 1 * 3 ^ℕ 2 * 3 ^ℕ 3 ≡ 729
vortex-tower-3n = refl

-- 倍频链: 3 → 6 → 12 → 24
-- 3 × 2 = 6
double-3 : 3 * 2 ≡ 6
double-3 = refl

-- 6 × 2 = 12
double-6 : 6 * 2 ≡ 12
double-6 = refl

-- 12 × 2 = 24
double-12 : 12 * 2 ≡ 24
double-12 = refl

-- 24 的数字根 = 6 (回绕)
-- 2 + 4 = 6
digital-root-24 : 2 + 4 ≡ 6
digital-root-24 = refl

--------------------------------------------------------------------------------
-- §7. Burnside 轨道算术
--
-- T⁶ 的 729 个格点在群 G (|G|=54) 作用下的轨道分解
--
-- Burnside 引理: |轨道数| = (1/|G|) Σ_{g∈G} |Fix(g)|
--
-- 已知:
--   |G| = 54 = 27 × 2 = 3³ × 2
--   轨道数 = 14
--   Σ|Fix(g)| = 54 × 14 = 756
--   恒等元固定 729 点
--   其余 53 个元素共固定 756 - 729 = 27 点
--
-- 验证: 54 × 14 = 756 = 729 + 27
--------------------------------------------------------------------------------

-- 群阶
burnside-G-order : ℕ
burnside-G-order = 54

-- 群阶分解: 54 = 27 × 2 = 3³ × 2
G-order-decomp : 27 * 2 ≡ 54
G-order-decomp = refl

-- 轨道数
burnside-orbit-count : ℕ
burnside-orbit-count = 14

-- Burnside 和: Σ|Fix(g)| = |G| × |轨道数|
burnside-sum : ℕ
burnside-sum = 756

-- Burnside 等式: 54 × 14 = 756
burnside-equation : burnside-G-order * burnside-orbit-count ≡ burnside-sum
burnside-equation = refl

-- 恒等元固定所有 729 点
burnside-fix-identity : ℕ
burnside-fix-identity = 729

-- 非恒等元共固定 27 点
burnside-fix-nonidentity : ℕ
burnside-fix-nonidentity = 27

-- 756 = 729 + 27 (恒等 + 非恒等)
burnside-sum-split : burnside-fix-identity + burnside-fix-nonidentity ≡ burnside-sum
burnside-sum-split = refl

-- 完整 Burnside 验证: 54 × 14 = 729 + 27
burnside-full : burnside-G-order * burnside-orbit-count ≡ 729 + 27
burnside-full = refl

-- 27 = 3³ — 非恒等固定点数是 3 的幂
burnside-fix-27-is-3³ : burnside-fix-nonidentity ≡ 3 ^ℕ 3
burnside-fix-27-is-3³ = refl

--------------------------------------------------------------------------------
-- §8. GF(9) → GF(729) 扩张塔
--
-- GF(3) ⊂ GF(9) ⊂ GF(729)
-- [GF(729):GF(3)] = 6
-- [GF(9):GF(3)] = 2
-- [GF(729):GF(9)] = 3  (因为 6 = 2 × 3)
--
-- 加法群:
--   GF(3)⁺  ≅ (Z/3Z)¹  — 3 个元素
--   GF(9)⁺  ≅ (Z/3Z)²  — 9 个元素
--   GF(729)⁺ ≅ (Z/3Z)⁶  — 729 个元素
--
-- 维度关系: 6 = 2 × 3
-- GF(729) 作为 GF(9)-向量空间是 3 维的
--------------------------------------------------------------------------------

-- 扩张次数: [GF(729):GF(3)] = 6
extension-degree-729-3 : ℕ
extension-degree-729-3 = 6

-- 扩张次数: [GF(9):GF(3)] = 2
extension-degree-9-3 : ℕ
extension-degree-9-3 = 2

-- 扩张次数: [GF(729):GF(9)] = 3
extension-degree-729-9 : ℕ
extension-degree-729-9 = 3

-- 次数乘法: [GF(729):GF(3)] = [GF(729):GF(9)] × [GF(9):GF(3)]
-- 6 = 3 × 2
tower-law : extension-degree-729-9 * extension-degree-9-3 ≡ extension-degree-729-3
tower-law = refl

-- 加法群基数验证
-- |GF(3)⁺| = 3¹ = 3
gf3-additive-card : 3 ^ℕ 1 ≡ 3
gf3-additive-card = refl

-- |GF(9)⁺| = 3² = 9
gf9-additive-card : 3 ^ℕ 2 ≡ 9
gf9-additive-card = refl

-- |GF(729)⁺| = 3⁶ = 729
gf729-additive-card : 3 ^ℕ 6 ≡ 729
gf729-additive-card = refl

-- GF(729) 作为 GF(9)-向量空间: 3 维
-- |GF(9)³| = 9³ = 729
gf9-vector-space : 9 ^ℕ 3 ≡ 729
gf9-vector-space = refl

-- 9³ = 3⁶ (因为 9 = 3², 所以 9³ = (3²)³ = 3⁶)
nine-cubed-eq-three-sixth : 9 ^ℕ 3 ≡ 3 ^ℕ 6
nine-cubed-eq-three-sixth = refl

--------------------------------------------------------------------------------
-- §9. 总结 — GF(729) 与 T⁶ 的结构对应
--
-- 定理: GF(729) 的加法群 ≅ (Z/3Z)⁶ = T⁶ 格点加法群
--
-- 证明:
--   GF729Vec = Vec (Fin 3) 6 = T6Lattice (定义等式)
--   +gf729 是逐分量 GF(3) 加法 (构造)
--   群公理由 GF(3) 的群公理逐分量提升 (§3)
--   基数 = 3⁶ = 729 (§4, 与 t6Cardinality 一致)
--
-- 注意: GF(729) 还有乘法结构 (域), 但构造 GF(729) 的乘法
-- 需要选择 GF(3) 上的 6 次不可约多项式, 本模块不处理。
-- 加法群同构不依赖于不可约多项式的选择。
--------------------------------------------------------------------------------

-- 加法群同构的总结记录
record AdditiveGroup (Carrier : Set) : Set where
  field
    _·+_       : Carrier → Carrier → Carrier
    ε          : Carrier
    inv        : Carrier → Carrier
    identityˡ  : ∀ x → ε ·+ x ≡ x
    identityʳ  : ∀ x → x ·+ ε ≡ x
    comm       : ∀ x y → x ·+ y ≡ y ·+ x
    assoc      : ∀ x y z → (x ·+ y) ·+ z ≡ x ·+ (y ·+ z)
    inverse    : ∀ x → x ·+ inv x ≡ ε

-- GF(729) 加法群的实例化
gf729-additive-group : AdditiveGroup GF729Vec
gf729-additive-group = record
  { _·+_      = _+gf729_
  ; ε         = gf729-zero
  ; inv       = neg729
  ; identityˡ = +gf729-identityˡ
  ; identityʳ = +gf729-identityʳ
  ; comm      = +gf729-comm
  ; assoc     = +gf729-assoc
  ; inverse   = +gf729-inverse
  }

--------------------------------------------------------------------------------
-- §10. 展示群相位对齐: GF729 上的 90° 旋转周期 (2026-09-08)
--
-- 本源: GF729 = GF(3⁶) 视作 GF(9)-向量空间 GF9³ ([GF729:GF9]=3, 即 6=2×3).
-- GF9⟨α⟩ (α² = -1, 90° 旋转相位源) 是 GF729 内嵌的子域相位.
-- 本节把"乘 α"这一 90° 旋转实现为加法群上的几何作用:
--   每块 GF9 (u,v) ↦ (neg v, u)  (α(a+bα) = aα + bα² = -b + aα, α² = -1)
-- 相位周期由结构给出 (非算术判定):
--   αRotate⁴ = id  (90°×4 = 360° 几何回位)
--   αRotate² = neg729 (180° 翻转; 90° 与 180° 两步不塌缩为一步)
--   αRotate 与加法相容 (旋转线性)
--   AlphaPower ⟨α⟩ 的 mulAlpha 群作用经 act 同态实现 (C₄ 作用忠实)
--   GF9 → GF729 的嵌入把 GF9 的乘 α 旋转带到 αRotate (相位源对齐)
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

-- GF(3) 分量取反对加法的分配 (旋转线性用, 9 case)
neg₃-add : ∀ u v → neg₃ (u +₃ v) ≡ neg₃ u +₃ neg₃ v
neg₃-add zero zero = refl
neg₃-add zero (suc zero) = refl
neg₃-add zero (suc (suc zero)) = refl
neg₃-add (suc zero) zero = refl
neg₃-add (suc zero) (suc zero) = refl
neg₃-add (suc zero) (suc (suc zero)) = refl
neg₃-add (suc (suc zero)) zero = refl
neg₃-add (suc (suc zero)) (suc zero) = refl
neg₃-add (suc (suc zero)) (suc (suc zero)) = refl

-- Trit 取反 ↔ Fin 3 取反 的桥接 (Trit 层 GF9 系数旋转到 Fin3 层)
trit-neg-bridge : ∀ t → tritToFin3 (negate t) ≡ neg₃ (tritToFin3 t)
trit-neg-bridge T₀ = refl
trit-neg-bridge T₁ = refl
trit-neg-bridge T₂ = refl

-- 90° 旋转: 3 个 GF9 块各自乘 α — (u,v) ↦ (neg v, u)
alphaRotate : GF729Vec → GF729Vec
alphaRotate (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) =
  neg₃ a4 ∷ a5 ∷ neg₃ a2 ∷ a3 ∷ neg₃ a0 ∷ a1 ∷ []

-- 两次旋转 = 180° 翻转 = 逐分量取反 (α² = -1 在加法层的实现)
alphaRotate-flip : ∀ x → alphaRotate (alphaRotate x) ≡ neg729 x
alphaRotate-flip (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = refl

-- 四次旋转几何回位 (α⁴ = 1; 90° 周期闭合)
alphaRotate-4 : ∀ x → alphaRotate (alphaRotate (alphaRotate (alphaRotate x))) ≡ x
alphaRotate-4 x =
  trans (alphaRotate-flip (alphaRotate (alphaRotate x)))
        (trans (cong neg729 (alphaRotate-flip x)) (neg729² x))

-- 旋转与加法相容: 旋转是加法群的自同构 (线性)
alphaRotate-add : ∀ x y →
  alphaRotate (x +gf729 y) ≡ alphaRotate x +gf729 alphaRotate y
alphaRotate-add (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ [])
                (b5 ∷ b4 ∷ b3 ∷ b2 ∷ b1 ∷ b0 ∷ []) =
  cong₂ _∷_ (neg₃-add a4 b4)
    (cong₂ _∷_ refl
      (cong₂ _∷_ (neg₃-add a2 b2)
        (cong₂ _∷_ refl
          (cong₂ _∷_ (neg₃-add a0 b0)
            (cong₂ _∷_ refl refl)))))

-- GF9 乘 α 旋转 (相位源上的 90°): (a,b) ↦ (neg b, a)
gf9-rotate : GF9 → GF9
gf9-rotate (a , b) = (negate b , a)

-- 锚定: gf9-rotate 就是真实的域乘法 x *gf9 α (非坐标断言 — 由 GF9 乘法定义化简)
-- 这是相位旋转的数学根据: 90° 旋转 = 乘 α, α² = -1 出自 x²+1 约化
gf9-rotate-is-mul : ∀ x → gf9-rotate x ≡ x *gf9 alpha
gf9-rotate-is-mul (a , b) = cong₂ _,_
  (sym (trans (cong₂ (λ u v → u ⊕ negate v) (⊗-zeroʳ a) (⊗-identityʳ b))
              (⊕-identityˡ (negate b))))
  (sym (trans (cong₂ _⊕_ (⊗-identityʳ a) (⊗-zeroʳ b)) (⊕-identityʳ a)))

-- 推论: 乘 α 再乘 α = 乘 α² = -1 作用 (α² = -1, 两次 90° = 180° 翻转)
gf9-rotate²-is-neg : ∀ x → gf9-rotate (gf9-rotate x) ≡ (negate (proj₁ x) , negate (proj₂ x))
gf9-rotate²-is-neg (a , b) = refl

-- GF9 相位源 → GF729 的嵌入 (GF9 落入第 1 块, 其余块为 0)
embed-9-729 : GF9 → GF729Vec
embed-9-729 (a , b) = tritToFin3 a ∷ tritToFin3 b ∷ zero ∷ zero ∷ zero ∷ zero ∷ []

-- 嵌入保旋转: GF9 的乘 α 在嵌入下正是 GF729 的 alphaRotate (相位源对齐)
embed-rotate : ∀ x → embed-9-729 (gf9-rotate x) ≡ alphaRotate (embed-9-729 x)
embed-rotate (a , b) = cong₂ _∷_ (trit-neg-bridge b)
  (cong₂ _∷_ refl
    (cong₂ _∷_ refl (cong₂ _∷_ refl (cong₂ _∷_ refl (cong₂ _∷_ refl refl)))))

-- 推论: 嵌入的 α 旋转一次落到嵌入的 α² (90° 走一步 = 相位乘 α)
embed-α-rotates : alphaRotate (embed-9-729 alpha) ≡ embed-9-729 (T₂ , T₀)
embed-α-rotates = refl

-- AlphaPower ⟨α⟩ 的群作用: pᵢ 作为 90°×i 旋转作用在 GF729 加法群上
-- p0 = α⁰ = 1   ↦ 恒等
-- p1 = α        ↦ alphaRotate (90°)
-- p2 = α² = -1  ↦ 两次旋转 (180°, = neg729)
-- p3 = α³ = -α  ↦ 三次旋转 (270°)
act : AlphaPower → GF729Vec → GF729Vec
act p0 x = x
act p1 x = alphaRotate x
act p2 x = alphaRotate (alphaRotate x)
act p3 x = alphaRotate (alphaRotate (alphaRotate x))

-- act 是乘法作用: act (a·b) x ≡ act a (act b x) — C₄ 周期由 ⟨α⟩ 乘法表驱动 (16 case)
act-hom : ∀ a b x → act (mulAlpha a b) x ≡ act a (act b x)
-- a = p0: mulAlpha p0 b = b (单位)
act-hom p0 b x = refl
-- a = p1 (乘 α: 一步旋转)
act-hom p1 p0 x = refl
act-hom p1 p1 x = refl
act-hom p1 p2 x = refl
act-hom p1 p3 x = sym (alphaRotate-4 x)
-- a = p2 (乘 α²: 两步旋转)
act-hom p2 p0 x = refl
act-hom p2 p1 x = refl
act-hom p2 p2 x = sym (alphaRotate-4 x)
act-hom p2 p3 x = sym (alphaRotate-4 (alphaRotate x))
-- a = p3 (乘 α³: 三步旋转)
act-hom p3 p0 x = refl
act-hom p3 p1 x = sym (alphaRotate-4 x)
act-hom p3 p2 x = sym (alphaRotate-4 (alphaRotate x))
act-hom p3 p3 x = sym (alphaRotate-4 (alphaRotate (alphaRotate x)))

-- 每步旋转都是加法自同构 (群作用的线性)
act-add : ∀ a x y → act a (x +gf729 y) ≡ act a x +gf729 act a y
act-add p0 x y = refl
act-add p1 x y = alphaRotate-add x y
act-add p2 x y =
  trans (cong alphaRotate (alphaRotate-add x y))
        (alphaRotate-add (alphaRotate x) (alphaRotate y))
act-add p3 x y =
  trans (cong alphaRotate (act-add p2 x y))
        (alphaRotate-add (alphaRotate (alphaRotate x))
                         (alphaRotate (alphaRotate y)))

-- 相位共轭 (Frobenius 在 GF9 相位源的形态): 每块 GF9 (u,v) ↦ (u, neg v)
-- 即 α ↦ -α 复共轭沿 3 块同时作用 — 展示群 galoisConjugate 的宿主扩展
gf729-conj : GF729Vec → GF729Vec
gf729-conj (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) =
  a5 ∷ neg₃ a4 ∷ a3 ∷ neg₃ a2 ∷ a1 ∷ neg₃ a0 ∷ []

-- 共轭是对合 (两次共轭回位)
gf729-conj² : ∀ x → gf729-conj (gf729-conj x) ≡ x
gf729-conj² (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) =
  cong₂ _∷_ refl
    (cong₂ _∷_ (neg₃² a4)
      (cong₂ _∷_ refl
        (cong₂ _∷_ (neg₃² a2)
          (cong₂ _∷_ refl
            (cong₂ _∷_ (neg₃² a0) refl)))))

-- 共轭是加法自同构
gf729-conj-add : ∀ x y →
  gf729-conj (x +gf729 y) ≡ gf729-conj x +gf729 gf729-conj y
gf729-conj-add (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ [])
               (b5 ∷ b4 ∷ b3 ∷ b2 ∷ b1 ∷ b0 ∷ []) =
  cong₂ _∷_ refl
    (cong₂ _∷_ (neg₃-add a4 b4)
      (cong₂ _∷_ refl
        (cong₂ _∷_ (neg₃-add a2 b2)
          (cong₂ _∷_ refl
            (cong₂ _∷_ (neg₃-add a0 b0) refl)))))

-- 嵌入保共轭: GF9 的 galoisConjugate 在嵌入下正是 gf729-conj (相位源对齐)
embed-conj : ∀ x → embed-9-729 (galoisConjugate x) ≡ gf729-conj (embed-9-729 x)
embed-conj (a , b) = cong₂ _∷_ refl
  (cong₂ _∷_ (trit-neg-bridge b)
    (cong₂ _∷_ refl (cong₂ _∷_ refl (cong₂ _∷_ refl (cong₂ _∷_ refl refl)))))

-- 共轭夹住旋转翻转方向: conj∘R∘conj = R³ (几何: 共轭把 90° 周期方向反转)
-- 逐块验证: 每块 GF9 上 (u,v) ↦ (neg v, u) 与共轭 (u,v) ↦ (u, neg v) 组合
conj-rot-conj : ∀ x →
  gf729-conj (alphaRotate (gf729-conj x)) ≡
  alphaRotate (alphaRotate (alphaRotate x))
conj-rot-conj (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = refl

-- 坐标读出与 Fin 3 不等判定 (忠实性证明用)
c0 : GF729Vec → Fin 3
c0 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = a5

c1 : GF729Vec → Fin 3
c1 (a5 ∷ a4 ∷ a3 ∷ a2 ∷ a1 ∷ a0 ∷ []) = a4

-- Fin 3 显式命名值 (钉住隐式索引, 避免 Fin 层级 meta 阻塞)
f0 : Fin 3
f0 = zero
f1 : Fin 3
f1 = suc zero
f2 : Fin 3
f2 = suc (suc zero)

fin0≠1 : ¬ (f0 ≡ f1)
fin0≠1 ()

fin0≠2 : ¬ (f0 ≡ f2)
fin0≠2 ()

fin1≠2 : ¬ (f1 ≡ f2)
fin1≠2 ()

-- act 的忠实性 (4 阶群作用非退化): 4 个相位步长作用在 α 上互不相同
-- 检验点 = 嵌入的 α, 其轨道长度恰为 4 (周期不塌缩为 1 或 2)
act-witness : GF729Vec
act-witness = embed-9-729 alpha


-- α⁰ 作用 = 恒等 (0,1)
act-p0-witness : act p0 act-witness ≡ act-witness
act-p0-witness = refl

-- α¹ 作用: (0,1) ↦ (2,0)  — 第 1 分量 0↦2
act-p1-witness : c0 (act p1 act-witness) ≡ suc (suc zero)
act-p1-witness = refl

-- α² 作用: (0,1) ↦ (0,2)  — 第 1 分量 0 (但第 2 分量变 2, 非恒等)
act-p2-witness : c1 (act p2 act-witness) ≡ suc (suc zero)
act-p2-witness = refl

-- α³ 作用: (0,1) ↦ (1,0)  — 第 1 分量 1
act-p3-witness : c0 (act p3 act-witness) ≡ suc zero
act-p3-witness = refl

-- 忠实性: 四个作用在检验点上给出四个不同结果 (0,1)/(2,0)/(0,2)/(1,0)
-- α⁰ 的第 1 分量 = 0
c0-p0 : c0 (act p0 act-witness) ≡ zero
c0-p0 = refl

-- α⁰ 的第 2 分量 = 1
c1-p0 : c1 (act p0 act-witness) ≡ suc zero
c1-p0 = refl

-- α¹ 与 α⁰ 不同 (第 1 分量 2 ≠ 0): zero ≡ suc (suc zero)
act-faithful-p1 : ¬ (act p1 act-witness ≡ act p0 act-witness)
act-faithful-p1 h = fin0≠2 (trans (sym c0-p0) (trans (sym (cong c0 h)) act-p1-witness))

-- α² 与 α⁰ 不同 (第 2 分量 2 ≠ 1): suc zero ≡ suc (suc zero)
act-faithful-p2 : ¬ (act p2 act-witness ≡ act p0 act-witness)
act-faithful-p2 h = fin1≠2 (trans (sym c1-p0) (trans (sym (cong c1 h)) act-p2-witness))

-- α³ 与 α⁰ 不同 (第 1 分量 1 ≠ 0): zero ≡ suc zero
act-faithful-p3 : ¬ (act p3 act-witness ≡ act p0 act-witness)
act-faithful-p3 h = fin0≠1 (trans (sym c0-p0) (trans (sym (cong c0 h)) act-p3-witness))
