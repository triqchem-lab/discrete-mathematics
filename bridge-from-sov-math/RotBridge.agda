{-# OPTIONS --rewriting --guardedness #-}

-- | RotBridge — 相位 C₄ 的几何实现桥：Rot ≅ ⟨α⟩（**全程 GF(3)，标准三进制 {0,1,2}**）
--
-- 修正记录：初版用 ℤ 与 {−1,0,1}（平衡三进制）表示旋转矩阵，**违反宪法**
--   （本项目基底是标准三进制 {0,1,2} = GF(3)，不是平衡三进制）。
--   本版所有矩阵元取 `Trit`，加法/乘法用 GF(3) 的 `⊕`/`⊗`：
--     R = [[0, 2], [1, 0]]   （2 ≡ −1 mod 3）
--   R² = [[2,0],[0,2]] = 2I = −I (mod 3)，R⁴ = I。
--
-- 数学内容：
--   ① Rot-hom       : Rot (a·b) ≡ Rot a · Rot b      （16 个 refl case）
--   ② Rot-injective : Rot a ≡ Rot b → a ≡ b          （经 decode 左逆）
--   ③ R²≡2I, R⁴≡I                                    （排除 V₄：V₄ 每元素平方为 I）
--   ④ 3D ℓ=1 三重态骨架：rot3 = [[0,2,0],[1,0,0],[0,0,1]] 的固定轴/子空间/阶
--
-- 0 postulate / 0 hole。
module RotBridge where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊕-identityˡ; ⊗-identityˡ)
open import Sovereign.Algebra.GroupTheory.DuodecClock using (AlphaPower; a0; a1; a2; a3; mulAlpha)

--------------------------------------------------------------------------------
-- §1. 2×2 GF(3) 矩阵
--------------------------------------------------------------------------------

record Mat2 : Set where
  constructor mat
  field
    m00 m01 m10 m11 : Trit
open Mat2 public

mulM : Mat2 → Mat2 → Mat2
mulM A B = mat ((m00 A ⊗ m00 B) ⊕ (m01 A ⊗ m10 B))
               ((m00 A ⊗ m01 B) ⊕ (m01 A ⊗ m11 B))
               ((m10 A ⊗ m00 B) ⊕ (m11 A ⊗ m10 B))
               ((m10 A ⊗ m01 B) ⊕ (m11 A ⊗ m11 B))

idM : Mat2
idM = mat T₁ T₀ T₀ T₁

-- 2I = 「−I」在 GF(3) 中的写法
negIM : Mat2
negIM = mat T₂ T₀ T₀ T₂

-- 90° 旋转: R = [[0,2],[1,0]]  (2 ≡ −1)
R : Mat2
R = mat T₀ T₂ T₁ T₀

-- 2R
negRM : Mat2
negRM = mat T₀ T₁ T₂ T₀

--------------------------------------------------------------------------------
-- §2. Rot : ⟨α⟩ → ⟨R⟩
--------------------------------------------------------------------------------

Rot : AlphaPower → Mat2
Rot a0 = idM
Rot a1 = R
Rot a2 = negIM
Rot a3 = negRM

--------------------------------------------------------------------------------
-- §3. 群同态（16 个 refl —— GF(3) 运算在类型检查器里规范化）
--------------------------------------------------------------------------------

Rot-hom : ∀ (a b : AlphaPower) → Rot (mulAlpha a b) ≡ mulM (Rot a) (Rot b)
Rot-hom a0 a0 = refl
Rot-hom a0 a1 = refl
Rot-hom a0 a2 = refl
Rot-hom a0 a3 = refl
Rot-hom a1 a0 = refl
Rot-hom a1 a1 = refl
Rot-hom a1 a2 = refl
Rot-hom a1 a3 = refl
Rot-hom a2 a0 = refl
Rot-hom a2 a1 = refl
Rot-hom a2 a2 = refl
Rot-hom a2 a3 = refl
Rot-hom a3 a0 = refl
Rot-hom a3 a1 = refl
Rot-hom a3 a2 = refl
Rot-hom a3 a3 = refl

--------------------------------------------------------------------------------
-- §4. 单射（decode 左逆；4 个矩阵互不相同）
--------------------------------------------------------------------------------

decode : Mat2 → Maybe (Fin 4)
decode (mat T₁ T₀ T₀ T₁) = just zero
decode (mat T₀ T₂ T₁ T₀) = just (suc zero)
decode (mat T₂ T₀ T₀ T₂) = just (suc (suc zero))
decode (mat T₀ T₁ T₂ T₀) = just (suc (suc (suc zero)))
decode _ = nothing

toFin : AlphaPower → Fin 4
toFin a0 = zero
toFin a1 = suc zero
toFin a2 = suc (suc zero)
toFin a3 = suc (suc (suc zero))

decode-Rot : ∀ (a : AlphaPower) → decode (Rot a) ≡ just (toFin a)
decode-Rot a0 = refl
decode-Rot a1 = refl
decode-Rot a2 = refl
decode-Rot a3 = refl

Rot-injective : ∀ (a b : AlphaPower) → Rot a ≡ Rot b → a ≡ b
Rot-injective a0 a0 _ = refl
Rot-injective a1 a1 _ = refl
Rot-injective a2 a2 _ = refl
Rot-injective a3 a3 _ = refl

--------------------------------------------------------------------------------
-- §5. 阶恰为 4
--------------------------------------------------------------------------------

R²≡2I : mulM R R ≡ negIM
R²≡2I = refl

R⁴≡I : mulM (mulM R R) (mulM R R) ≡ idM
R⁴≡I = refl

--------------------------------------------------------------------------------
-- §6. 3D：ℓ=1 三重态 (m = −1, 0, +1) 的骨架（GF(3) 表示）
--
--   rot3 = [[0,2,0],[1,0,0],[0,0,1]]
--   ① m=0 轴 (0,0,1) 固定  ② z=0 子空间退化为 §1 的 R  ③ rot3² = diag(2,2,1)
--------------------------------------------------------------------------------

record Mat3 : Set where
  constructor mat3
  field
    n00 n01 n02 n10 n11 n12 n20 n21 n22 : Trit
open Mat3 public

record Vec3 : Set where
  constructor vec3
  field
    vx vy vz : Trit
open Vec3 public

mulM3 : Mat3 → Mat3 → Mat3
mulM3 A B = mat3
  ((n00 A ⊗ n00 B) ⊕ ((n01 A ⊗ n10 B) ⊕ (n02 A ⊗ n20 B)))
  ((n00 A ⊗ n01 B) ⊕ ((n01 A ⊗ n11 B) ⊕ (n02 A ⊗ n21 B)))
  ((n00 A ⊗ n02 B) ⊕ ((n01 A ⊗ n12 B) ⊕ (n02 A ⊗ n22 B)))
  ((n10 A ⊗ n00 B) ⊕ ((n11 A ⊗ n10 B) ⊕ (n12 A ⊗ n20 B)))
  ((n10 A ⊗ n01 B) ⊕ ((n11 A ⊗ n11 B) ⊕ (n12 A ⊗ n21 B)))
  ((n10 A ⊗ n02 B) ⊕ ((n11 A ⊗ n12 B) ⊕ (n12 A ⊗ n22 B)))
  ((n20 A ⊗ n00 B) ⊕ ((n21 A ⊗ n10 B) ⊕ (n22 A ⊗ n20 B)))
  ((n20 A ⊗ n01 B) ⊕ ((n21 A ⊗ n11 B) ⊕ (n22 A ⊗ n21 B)))
  ((n20 A ⊗ n02 B) ⊕ ((n21 A ⊗ n12 B) ⊕ (n22 A ⊗ n22 B)))

idM3 : Mat3
idM3 = mat3 T₁ T₀ T₀ T₀ T₁ T₀ T₀ T₀ T₁

rot3 : Mat3
rot3 = mat3 T₀ T₂ T₀
             T₁ T₀ T₀
             T₀ T₀ T₁

apply3 : Mat3 → Vec3 → Vec3
apply3 A v = vec3 ((n00 A ⊗ vx v) ⊕ ((n01 A ⊗ vy v) ⊕ (n02 A ⊗ vz v)))
                  ((n10 A ⊗ vx v) ⊕ ((n11 A ⊗ vy v) ⊕ (n12 A ⊗ vz v)))
                  ((n20 A ⊗ vx v) ⊕ ((n21 A ⊗ vy v) ⊕ (n22 A ⊗ vz v)))

-- ① m=0 轴固定
fixed-m0 : apply3 rot3 (vec3 T₀ T₀ T₁) ≡ vec3 T₀ T₀ T₁
fixed-m0 = refl

-- ② z=0 子空间：R 的作用 (1,0) ↦ (0,1) ↦ (2,0) ↦ (0,2) ↦ (1,0)
m±1-step1 : apply3 rot3 (vec3 T₁ T₀ T₀) ≡ vec3 T₀ T₁ T₀
m±1-step1 = refl

m±1-step2 : apply3 rot3 (vec3 T₀ T₁ T₀) ≡ vec3 T₂ T₀ T₀
m±1-step2 = refl

m±1-step3 : apply3 rot3 (vec3 T₂ T₀ T₀) ≡ vec3 T₀ T₂ T₀
m±1-step3 = refl

m±1-step4 : apply3 rot3 (vec3 T₀ T₂ T₀) ≡ vec3 T₁ T₀ T₀
m±1-step4 = refl

-- ③ 阶与平方
rot3⁴≡id : mulM3 (mulM3 rot3 rot3) (mulM3 rot3 rot3) ≡ idM3
rot3⁴≡id = refl

rot3²≡diag : mulM3 rot3 rot3 ≡ mat3 T₂ T₀ T₀
                                     T₀ T₂ T₀
                                     T₀ T₀ T₁
rot3²≡diag = refl

--------------------------------------------------------------------------------
-- §6.5 R ∈ SL(2,3) = 2A₄（双重覆盖），而不是 A₄
--
-- 结构事实（库内已形式化）：
--   · S² 12 胞腔（正十二面体）的对称群是 A₄（阶 12），A₄ **没有 4 阶元**
--     —— 见 Synthesis/A4/BinaryTetrahedral.agda: 4 阶元只出现在双重覆盖 2A₄ 中
--        (`q8-i⁴ : qi⁴ ≡ q1`, 以及 BinaryTetrahedralDefiningRep 的 orderOf g3 = 4)。
--   · 相位 C₄ 的矩阵实现 R = [[0,2],[1,0]] 的行列式 = 1 (mod 3) ⇒ R ∈ SL(2,3) = 2A₄。
-- 所以相位作用在 ℓ=1 的**双双态**（spinor 覆盖）上，而不是置换 12 个胞腔 ——
-- 这解释了「A₄ 有 12 个元素但装不下 4 阶相位」这一表面矛盾。
--------------------------------------------------------------------------------

detM : Mat2 → Trit
detM A = (m00 A ⊗ m11 A) ⊕ negate (m01 A ⊗ m10 A)

R-det-is-1 : detM R ≡ T₁
R-det-is-1 = refl

-- R 的阶为 4（§5 已证 R⁴≡I 且 R²≡2I≠I），det = 1 ⇒ R ∈ SL(2,3) = 2A₄

--------------------------------------------------------------------------------
-- §7. 结论
--------------------------------------------------------------------------------

Rot-isomorphism : (∀ a b → Rot (mulAlpha a b) ≡ mulM (Rot a) (Rot b))
                × (∀ a b → Rot a ≡ Rot b → a ≡ b)
                × (mulM (mulM R R) (mulM R R) ≡ idM)
                × (mulM R R ≡ negIM)
Rot-isomorphism = Rot-hom , Rot-injective , R⁴≡I , R²≡2I
