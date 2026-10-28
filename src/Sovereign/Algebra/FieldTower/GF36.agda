{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.GF36 —— GF(3⁶) 三进制统一域（六 trit 寄存器）
--
-- == 定位（三进制计算机 L1 的统一语义域）
--
-- GF(3ᵈ) ⊆ GF(3ᵏ) ⟺ d∣k ⇒ **6** 是同时容纳 d = 1, 2, 3 的最小扩张次数：
-- GF(3), GF(9), GF(27) 全部是 GF(3⁶) 的子域，且 |GF(3⁶)| = 3⁶ = 729 = T⁶ 格点数。
-- 一个六 trit 寄存器因此同时承载三塔算术——这是三进制 ISA 标量寄存器宽度的
-- 代数判据。
--
-- 域构造：GF(3⁶) = GF(3)[θ]/(θ⁶ + θ + 2)。θ⁶ + θ + 2 的不可约性不由外部断言
-- 给出，而由本模块的**子域计数定理**枚举地确立（若可约，σᵈ 固定点数必然
-- 爆炸——例如 3+3 分裂时 fixed(σ³) = 729 ≠ 27）：
--
--   · fixed(σ)  = 3      —— GF(3)   驻留（x³ = x）
--   · fixed(σ²) = 9      —— GF(9)   驻留（x⁹ = x）
--   · fixed(σ³) = 27     —— GF(27)  驻留（x²⁷ = x）
--   · fixed(σ⁶) = 729    —— σ⁶ = id（全域）
--
-- 即 **d∣6 判据在本域上的完整实例**（Intercept/Authority 的 baseResident
-- 推广）；三个驻留谓词（subfield1/2/3）就是 ISA 子域驻留拦截指令的语义。
--
-- == 嵌入种子（子域嵌入的存在性 witnesses）
--
--   · β = θ + 2θ² + θ³ + θ⁴：β² = 2（x² + 1 的根 → GF(9) 嵌入种子），
--     被 σ² 固定 ✓
--   · γ = θ² + 2θ³ + θ⁴：γ³ = γ + 2（θ³ + 2θ + 1 的根 → GF(27) 嵌入种子），
--     被 σ³ 固定 ✓
--   完整同态映射（a + bα₉ ↦ a + bβ 等）与其函子性证明留待下一卷。
--
-- == 生成口径（防算术冒充）
--
-- all729 枚举与 σ 闭式由脚本机械生成：σ 在全部 729² = 531441 对上保乘法、
-- σ⁶ 矩阵 = I、四个固定点计数独立核对后才落盘；本模块 pin 与该脚本互为
-- 交叉验证。dedup36 pin 拦截「枚举表重复/漏项」缺陷类（Intercept all27
-- 曾中招）。
--
-- v1 范围：塔结构 + 子域判据 + 嵌入种子。留待后续：C₇₂₈ 循环群生成元、
-- 乘法结合律、嵌入映射的完整同态证明。
module Sovereign.Algebra.FieldTower.GF36 where

open import Data.Bool
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; _∷_; []; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- 类型与基本元：GF(3⁶) = GF(3)[θ]/(θ⁶ + θ + 2)，θ⁶ = 2θ + 1
--------------------------------------------------------------------------------

GF36 : Set
GF36 = Trit × Trit × Trit × Trit × Trit × Trit  -- a₀ + a₁θ + … + a₅θ⁵

gf36-zero : GF36
gf36-zero = T₀ , T₀ , T₀ , T₀ , T₀ , T₀

gf36-one : GF36
gf36-one = T₁ , T₀ , T₀ , T₀ , T₀ , T₀

embed-gf3-gf36 : Trit → GF36
embed-gf3-gf36 a = a , T₀ , T₀ , T₀ , T₀ , T₀

theta36 : GF36  -- θ
theta36 = T₀ , T₁ , T₀ , T₀ , T₀ , T₀

--------------------------------------------------------------------------------
-- 加法：(Z/3)⁶ 逐分量
--------------------------------------------------------------------------------

infixl 6 _+gf36_
_+gf36_ : GF36 → GF36 → GF36
(a₀ , a₁ , a₂ , a₃ , a₄ , a₅) +gf36 (b₀ , b₁ , b₂ , b₃ , b₄ , b₅) =
  (a₀ ⊕ b₀) , (a₁ ⊕ b₁) , (a₂ ⊕ b₂) , (a₃ ⊕ b₃) , (a₄ ⊕ b₄) , (a₅ ⊕ b₅)

--------------------------------------------------------------------------------
-- 乘法：多项式乘 (度 ≤ 10) 后按 θ⁶ = 2θ + 1 约化
--   θ⁶→(2θ+1), θ⁷→(2θ²+θ), θ⁸→(2θ³+θ²), θ⁹→(2θ⁴+θ³), θ¹⁰→(2θ⁵+θ⁴)
--------------------------------------------------------------------------------

infixl 7 _*gf36_
_*gf36_ : GF36 → GF36 → GF36
(a₀ , a₁ , a₂ , a₃ , a₄ , a₅) *gf36 (b₀ , b₁ , b₂ , b₃ , b₄ , b₅) =
    r₀ , r₁ , r₂ , r₃ , r₄ , r₅
  where
    p₀ = a₀ ⊗ b₀
    p₁ = (a₀ ⊗ b₁) ⊕ (a₁ ⊗ b₀)
    p₂ = (a₀ ⊗ b₂) ⊕ ((a₁ ⊗ b₁) ⊕ (a₂ ⊗ b₀))
    p₃ = (a₀ ⊗ b₃) ⊕ ((a₁ ⊗ b₂) ⊕ ((a₂ ⊗ b₁) ⊕ (a₃ ⊗ b₀)))
    p₄ = (a₀ ⊗ b₄) ⊕ ((a₁ ⊗ b₃) ⊕ ((a₂ ⊗ b₂) ⊕ ((a₃ ⊗ b₁) ⊕ (a₄ ⊗ b₀))))
    p₅ = (a₀ ⊗ b₅) ⊕ ((a₁ ⊗ b₄) ⊕ ((a₂ ⊗ b₃) ⊕ ((a₃ ⊗ b₂) ⊕ ((a₄ ⊗ b₁) ⊕ (a₅ ⊗ b₀)))))
    p₆ = (a₁ ⊗ b₅) ⊕ ((a₂ ⊗ b₄) ⊕ ((a₃ ⊗ b₃) ⊕ ((a₄ ⊗ b₂) ⊕ (a₅ ⊗ b₁))))
    p₇ = (a₂ ⊗ b₅) ⊕ ((a₃ ⊗ b₄) ⊕ ((a₄ ⊗ b₃) ⊕ (a₅ ⊗ b₂)))
    p₈ = (a₃ ⊗ b₅) ⊕ ((a₄ ⊗ b₄) ⊕ (a₅ ⊗ b₃))
    p₉ = (a₄ ⊗ b₅) ⊕ (a₅ ⊗ b₄)
    p₁⁰ = a₅ ⊗ b₅
    r₀ = p₀ ⊕ p₆
    r₁ = (p₁ ⊕ p₇) ⊕ negate p₆  -- p1 + p7 + 2p6，2t = negate t
    r₂ = (p₂ ⊕ p₈) ⊕ negate p₇
    r₃ = (p₃ ⊕ p₉) ⊕ negate p₈
    r₄ = (p₄ ⊕ p₁⁰) ⊕ negate p₉
    r₅ = p₅ ⊕ negate p₁⁰

--------------------------------------------------------------------------------
-- Frobenius σ: x ↦ x³（GF(3)-线性；σ(θⁱ) = θ³ⁱ 的列生成）
--   σ(a₀,…,a₅) = (a₀⊕a₂⊕a₄, 2a₂⊕a₄, a₄, a₁⊕a₃⊕a₅, 2a₃⊕a₅, a₅)
--   （(a₀,a₂,a₄) 与 (a₁,a₃,a₅) 两块解耦）
--------------------------------------------------------------------------------

frobenius36 : GF36 → GF36
frobenius36 (a₀ , a₁ , a₂ , a₃ , a₄ , a₅) =
    ((a₀ ⊕ a₂) ⊕ a₄)
  , ((negate a₂) ⊕ a₄)
  , a₄
  , ((a₁ ⊕ a₃) ⊕ a₅)
  , ((negate a₃) ⊕ a₅)
  , a₅

--------------------------------------------------------------------------------
-- 枚举与工具（Bool 版，供计数 pin；脚本机械生成）
--------------------------------------------------------------------------------

_==ᵗ⁶_ : Trit → Trit → Bool
T₀ ==ᵗ⁶ T₀ = true
T₁ ==ᵗ⁶ T₁ = true
T₂ ==ᵗ⁶ T₂ = true
_  ==ᵗ⁶ _  = false

_==³⁶_ : GF36 → GF36 → Bool
(a₀ , a₁ , a₂ , a₃ , a₄ , a₅) ==³⁶ (b₀ , b₁ , b₂ , b₃ , b₄ , b₅) =
  ((a₀ ==ᵗ⁶ b₀) ∧ (a₁ ==ᵗ⁶ b₁)) ∧ ((a₂ ==ᵗ⁶ b₂) ∧ (a₃ ==ᵗ⁶ b₃)) ∧ ((a₄ ==ᵗ⁶ b₄) ∧ (a₅ ==ᵗ⁶ b₅))

keepIf36 : (GF36 → Bool) → List GF36 → List GF36
keepIf36 p [] = []
keepIf36 p (x ∷ xs) = if p x then x ∷ keepIf36 p xs else keepIf36 p xs

elem36 : GF36 → List GF36 → Bool
elem36 _ [] = false
elem36 x (y ∷ ys) = (x ==³⁶ y) ∨ elem36 x ys

dedup36 : List GF36 → List GF36
dedup36 [] = []
dedup36 (x ∷ xs) = if elem36 x xs then dedup36 xs else x ∷ dedup36 xs

-- 3⁶ = 729 全量枚举（脚本生成；去重守卫见 pin-36-nodup）
all729 : List GF36
all729 =
  (T₀ , T₀ , T₀ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₀ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₀ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₀ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₀ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₀ , T₀ , T₀) ∷
  (T₀ , T₀ , T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₁ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₁ , T₀ , T₀ , T₀) ∷ (T₀ , T₁ , T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₁ , T₁ , T₀ , T₀ , T₀) ∷ (T₂ , T₁ , T₁ , T₀ , T₀ , T₀) ∷ (T₀ , T₂ , T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₂ , T₁ , T₀ , T₀ , T₀) ∷ (T₂ , T₂ , T₁ , T₀ , T₀ , T₀) ∷
  (T₀ , T₀ , T₂ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₂ , T₀ , T₀ , T₀) ∷ (T₀ , T₁ , T₂ , T₀ , T₀ , T₀) ∷ (T₁ , T₁ , T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₁ , T₂ , T₀ , T₀ , T₀) ∷ (T₀ , T₂ , T₂ , T₀ , T₀ , T₀) ∷ (T₁ , T₂ , T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₂ , T₂ , T₀ , T₀ , T₀) ∷
  (T₀ , T₀ , T₀ , T₁ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁ , T₀ , T₀) ∷
  (T₀ , T₀ , T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₀ , T₁ , T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₁ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₁ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₁ , T₁ , T₀ , T₀) ∷ (T₀ , T₂ , T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₂ , T₁ , T₁ , T₀ , T₀) ∷ (T₂ , T₂ , T₁ , T₁ , T₀ , T₀) ∷
  (T₀ , T₀ , T₂ , T₁ , T₀ , T₀) ∷ (T₁ , T₀ , T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₂ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₂ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₂ , T₁ , T₀ , T₀) ∷ (T₀ , T₂ , T₂ , T₁ , T₀ , T₀) ∷ (T₁ , T₂ , T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₂ , T₂ , T₁ , T₀ , T₀) ∷
  (T₀ , T₀ , T₀ , T₂ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₂ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₂ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₂ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₂ , T₀ , T₀) ∷
  (T₀ , T₀ , T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₀ , T₁ , T₂ , T₀ , T₀) ∷ (T₂ , T₀ , T₁ , T₂ , T₀ , T₀) ∷ (T₀ , T₁ , T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₁ , T₁ , T₂ , T₀ , T₀) ∷ (T₂ , T₁ , T₁ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₁ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₁ , T₂ , T₀ , T₀) ∷
  (T₀ , T₀ , T₂ , T₂ , T₀ , T₀) ∷ (T₁ , T₀ , T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₀ , T₂ , T₂ , T₀ , T₀) ∷ (T₀ , T₁ , T₂ , T₂ , T₀ , T₀) ∷ (T₁ , T₁ , T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₁ , T₂ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₂ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₂ , T₂ , T₀ , T₀) ∷
  (T₀ , T₀ , T₀ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₀ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₁ , T₀ , T₀ , T₁ , T₀) ∷ (T₁ , T₁ , T₀ , T₀ , T₁ , T₀) ∷ (T₂ , T₁ , T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₂ , T₀ , T₀ , T₁ , T₀) ∷ (T₁ , T₂ , T₀ , T₀ , T₁ , T₀) ∷ (T₂ , T₂ , T₀ , T₀ , T₁ , T₀) ∷
  (T₀ , T₀ , T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₀ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₀ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₀ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₀ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₀ , T₁ , T₀) ∷
  (T₀ , T₀ , T₂ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₂ , T₀ , T₁ , T₀) ∷ (T₀ , T₁ , T₂ , T₀ , T₁ , T₀) ∷ (T₁ , T₁ , T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₁ , T₂ , T₀ , T₁ , T₀) ∷ (T₀ , T₂ , T₂ , T₀ , T₁ , T₀) ∷ (T₁ , T₂ , T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₂ , T₂ , T₀ , T₁ , T₀) ∷
  (T₀ , T₀ , T₀ , T₁ , T₁ , T₀) ∷ (T₁ , T₀ , T₀ , T₁ , T₁ , T₀) ∷ (T₂ , T₀ , T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₀ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₀ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₂ , T₀ , T₁ , T₁ , T₀) ∷ (T₁ , T₂ , T₀ , T₁ , T₁ , T₀) ∷ (T₂ , T₂ , T₀ , T₁ , T₁ , T₀) ∷
  (T₀ , T₀ , T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁ , T₁ , T₀) ∷
  (T₀ , T₀ , T₂ , T₁ , T₁ , T₀) ∷ (T₁ , T₀ , T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₀ , T₂ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₂ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₂ , T₁ , T₁ , T₀) ∷ (T₀ , T₂ , T₂ , T₁ , T₁ , T₀) ∷ (T₁ , T₂ , T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₂ , T₂ , T₁ , T₁ , T₀) ∷
  (T₀ , T₀ , T₀ , T₂ , T₁ , T₀) ∷ (T₁ , T₀ , T₀ , T₂ , T₁ , T₀) ∷ (T₂ , T₀ , T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₁ , T₀ , T₂ , T₁ , T₀) ∷ (T₁ , T₁ , T₀ , T₂ , T₁ , T₀) ∷ (T₂ , T₁ , T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₀ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₀ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₀ , T₂ , T₁ , T₀) ∷
  (T₀ , T₀ , T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₂ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₂ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₂ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₂ , T₁ , T₀) ∷
  (T₀ , T₀ , T₂ , T₂ , T₁ , T₀) ∷ (T₁ , T₀ , T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₀ , T₂ , T₂ , T₁ , T₀) ∷ (T₀ , T₁ , T₂ , T₂ , T₁ , T₀) ∷ (T₁ , T₁ , T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₁ , T₂ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₂ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₂ , T₂ , T₁ , T₀) ∷
  (T₀ , T₀ , T₀ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₀ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₁ , T₀ , T₀ , T₂ , T₀) ∷ (T₁ , T₁ , T₀ , T₀ , T₂ , T₀) ∷ (T₂ , T₁ , T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₂ , T₀ , T₀ , T₂ , T₀) ∷ (T₁ , T₂ , T₀ , T₀ , T₂ , T₀) ∷ (T₂ , T₂ , T₀ , T₀ , T₂ , T₀) ∷
  (T₀ , T₀ , T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₁ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₁ , T₀ , T₂ , T₀) ∷ (T₀ , T₁ , T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₁ , T₁ , T₀ , T₂ , T₀) ∷ (T₂ , T₁ , T₁ , T₀ , T₂ , T₀) ∷ (T₀ , T₂ , T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₂ , T₁ , T₀ , T₂ , T₀) ∷ (T₂ , T₂ , T₁ , T₀ , T₂ , T₀) ∷
  (T₀ , T₀ , T₂ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₀ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₀ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₀ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₀ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₀ , T₂ , T₀) ∷
  (T₀ , T₀ , T₀ , T₁ , T₂ , T₀) ∷ (T₁ , T₀ , T₀ , T₁ , T₂ , T₀) ∷ (T₂ , T₀ , T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₀ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₀ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₂ , T₀ , T₁ , T₂ , T₀) ∷ (T₁ , T₂ , T₀ , T₁ , T₂ , T₀) ∷ (T₂ , T₂ , T₀ , T₁ , T₂ , T₀) ∷
  (T₀ , T₀ , T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₀ , T₁ , T₁ , T₂ , T₀) ∷ (T₂ , T₀ , T₁ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₁ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₁ , T₁ , T₂ , T₀) ∷ (T₀ , T₂ , T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₂ , T₁ , T₁ , T₂ , T₀) ∷ (T₂ , T₂ , T₁ , T₁ , T₂ , T₀) ∷
  (T₀ , T₀ , T₂ , T₁ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁ , T₂ , T₀) ∷
  (T₀ , T₀ , T₀ , T₂ , T₂ , T₀) ∷ (T₁ , T₀ , T₀ , T₂ , T₂ , T₀) ∷ (T₂ , T₀ , T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₁ , T₀ , T₂ , T₂ , T₀) ∷ (T₁ , T₁ , T₀ , T₂ , T₂ , T₀) ∷ (T₂ , T₁ , T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₀ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₀ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₀ , T₂ , T₂ , T₀) ∷
  (T₀ , T₀ , T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₀ , T₁ , T₂ , T₂ , T₀) ∷ (T₂ , T₀ , T₁ , T₂ , T₂ , T₀) ∷ (T₀ , T₁ , T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₁ , T₁ , T₂ , T₂ , T₀) ∷ (T₂ , T₁ , T₁ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₁ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₁ , T₂ , T₂ , T₀) ∷
  (T₀ , T₀ , T₂ , T₂ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₂ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₂ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₂ , T₂ , T₀) ∷
  (T₀ , T₀ , T₀ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₀ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₀ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₀ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₀ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₀ , T₀ , T₁) ∷
  (T₀ , T₀ , T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₁ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₁ , T₀ , T₀ , T₁) ∷ (T₀ , T₁ , T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₁ , T₁ , T₀ , T₀ , T₁) ∷ (T₂ , T₁ , T₁ , T₀ , T₀ , T₁) ∷ (T₀ , T₂ , T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₂ , T₁ , T₀ , T₀ , T₁) ∷ (T₂ , T₂ , T₁ , T₀ , T₀ , T₁) ∷
  (T₀ , T₀ , T₂ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₂ , T₀ , T₀ , T₁) ∷ (T₀ , T₁ , T₂ , T₀ , T₀ , T₁) ∷ (T₁ , T₁ , T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₁ , T₂ , T₀ , T₀ , T₁) ∷ (T₀ , T₂ , T₂ , T₀ , T₀ , T₁) ∷ (T₁ , T₂ , T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₂ , T₂ , T₀ , T₀ , T₁) ∷
  (T₀ , T₀ , T₀ , T₁ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₁ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₁ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₁ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₁ , T₀ , T₁) ∷
  (T₀ , T₀ , T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₀ , T₁ , T₁ , T₀ , T₁) ∷ (T₂ , T₀ , T₁ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₁ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₁ , T₁ , T₀ , T₁) ∷ (T₀ , T₂ , T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₂ , T₁ , T₁ , T₀ , T₁) ∷ (T₂ , T₂ , T₁ , T₁ , T₀ , T₁) ∷
  (T₀ , T₀ , T₂ , T₁ , T₀ , T₁) ∷ (T₁ , T₀ , T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₀ , T₂ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₂ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₂ , T₁ , T₀ , T₁) ∷ (T₀ , T₂ , T₂ , T₁ , T₀ , T₁) ∷ (T₁ , T₂ , T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₂ , T₂ , T₁ , T₀ , T₁) ∷
  (T₀ , T₀ , T₀ , T₂ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂ , T₀ , T₁) ∷
  (T₀ , T₀ , T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₀ , T₁ , T₂ , T₀ , T₁) ∷ (T₂ , T₀ , T₁ , T₂ , T₀ , T₁) ∷ (T₀ , T₁ , T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₁ , T₁ , T₂ , T₀ , T₁) ∷ (T₂ , T₁ , T₁ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₁ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₁ , T₂ , T₀ , T₁) ∷
  (T₀ , T₀ , T₂ , T₂ , T₀ , T₁) ∷ (T₁ , T₀ , T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₀ , T₂ , T₂ , T₀ , T₁) ∷ (T₀ , T₁ , T₂ , T₂ , T₀ , T₁) ∷ (T₁ , T₁ , T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₁ , T₂ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₂ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₂ , T₂ , T₀ , T₁) ∷
  (T₀ , T₀ , T₀ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₀ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₁ , T₀ , T₀ , T₁ , T₁) ∷ (T₁ , T₁ , T₀ , T₀ , T₁ , T₁) ∷ (T₂ , T₁ , T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₂ , T₀ , T₀ , T₁ , T₁) ∷ (T₁ , T₂ , T₀ , T₀ , T₁ , T₁) ∷ (T₂ , T₂ , T₀ , T₀ , T₁ , T₁) ∷
  (T₀ , T₀ , T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₀ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₀ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₀ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₀ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₀ , T₁ , T₁) ∷
  (T₀ , T₀ , T₂ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₂ , T₀ , T₁ , T₁) ∷ (T₀ , T₁ , T₂ , T₀ , T₁ , T₁) ∷ (T₁ , T₁ , T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₁ , T₂ , T₀ , T₁ , T₁) ∷ (T₀ , T₂ , T₂ , T₀ , T₁ , T₁) ∷ (T₁ , T₂ , T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₂ , T₂ , T₀ , T₁ , T₁) ∷
  (T₀ , T₀ , T₀ , T₁ , T₁ , T₁) ∷ (T₁ , T₀ , T₀ , T₁ , T₁ , T₁) ∷ (T₂ , T₀ , T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₀ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₀ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₂ , T₀ , T₁ , T₁ , T₁) ∷ (T₁ , T₂ , T₀ , T₁ , T₁ , T₁) ∷ (T₂ , T₂ , T₀ , T₁ , T₁ , T₁) ∷
  (T₀ , T₀ , T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₁ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₁ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₁ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₁ , T₁ , T₁) ∷
  (T₀ , T₀ , T₂ , T₁ , T₁ , T₁) ∷ (T₁ , T₀ , T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₀ , T₂ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₂ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₂ , T₁ , T₁ , T₁) ∷ (T₀ , T₂ , T₂ , T₁ , T₁ , T₁) ∷ (T₁ , T₂ , T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₂ , T₂ , T₁ , T₁ , T₁) ∷
  (T₀ , T₀ , T₀ , T₂ , T₁ , T₁) ∷ (T₁ , T₀ , T₀ , T₂ , T₁ , T₁) ∷ (T₂ , T₀ , T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₁ , T₀ , T₂ , T₁ , T₁) ∷ (T₁ , T₁ , T₀ , T₂ , T₁ , T₁) ∷ (T₂ , T₁ , T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₀ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₀ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₀ , T₂ , T₁ , T₁) ∷
  (T₀ , T₀ , T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂ , T₁ , T₁) ∷
  (T₀ , T₀ , T₂ , T₂ , T₁ , T₁) ∷ (T₁ , T₀ , T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₀ , T₂ , T₂ , T₁ , T₁) ∷ (T₀ , T₁ , T₂ , T₂ , T₁ , T₁) ∷ (T₁ , T₁ , T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₁ , T₂ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₂ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₂ , T₂ , T₁ , T₁) ∷
  (T₀ , T₀ , T₀ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₀ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₁ , T₀ , T₀ , T₂ , T₁) ∷ (T₁ , T₁ , T₀ , T₀ , T₂ , T₁) ∷ (T₂ , T₁ , T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₂ , T₀ , T₀ , T₂ , T₁) ∷ (T₁ , T₂ , T₀ , T₀ , T₂ , T₁) ∷ (T₂ , T₂ , T₀ , T₀ , T₂ , T₁) ∷
  (T₀ , T₀ , T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₁ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₁ , T₀ , T₂ , T₁) ∷ (T₀ , T₁ , T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₁ , T₁ , T₀ , T₂ , T₁) ∷ (T₂ , T₁ , T₁ , T₀ , T₂ , T₁) ∷ (T₀ , T₂ , T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₂ , T₁ , T₀ , T₂ , T₁) ∷ (T₂ , T₂ , T₁ , T₀ , T₂ , T₁) ∷
  (T₀ , T₀ , T₂ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₀ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₀ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₀ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₀ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₀ , T₂ , T₁) ∷
  (T₀ , T₀ , T₀ , T₁ , T₂ , T₁) ∷ (T₁ , T₀ , T₀ , T₁ , T₂ , T₁) ∷ (T₂ , T₀ , T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₀ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₀ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₂ , T₀ , T₁ , T₂ , T₁) ∷ (T₁ , T₂ , T₀ , T₁ , T₂ , T₁) ∷ (T₂ , T₂ , T₀ , T₁ , T₂ , T₁) ∷
  (T₀ , T₀ , T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₀ , T₁ , T₁ , T₂ , T₁) ∷ (T₂ , T₀ , T₁ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₁ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₁ , T₁ , T₂ , T₁) ∷ (T₀ , T₂ , T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₂ , T₁ , T₁ , T₂ , T₁) ∷ (T₂ , T₂ , T₁ , T₁ , T₂ , T₁) ∷
  (T₀ , T₀ , T₂ , T₁ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₁ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₁ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₁ , T₂ , T₁) ∷
  (T₀ , T₀ , T₀ , T₂ , T₂ , T₁) ∷ (T₁ , T₀ , T₀ , T₂ , T₂ , T₁) ∷ (T₂ , T₀ , T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₁ , T₀ , T₂ , T₂ , T₁) ∷ (T₁ , T₁ , T₀ , T₂ , T₂ , T₁) ∷ (T₂ , T₁ , T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₀ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₀ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₀ , T₂ , T₂ , T₁) ∷
  (T₀ , T₀ , T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₀ , T₁ , T₂ , T₂ , T₁) ∷ (T₂ , T₀ , T₁ , T₂ , T₂ , T₁) ∷ (T₀ , T₁ , T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₁ , T₁ , T₂ , T₂ , T₁) ∷ (T₂ , T₁ , T₁ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₁ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₁ , T₂ , T₂ , T₁) ∷
  (T₀ , T₀ , T₂ , T₂ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂ , T₂ , T₁) ∷
  (T₀ , T₀ , T₀ , T₀ , T₀ , T₂) ∷ (T₁ , T₀ , T₀ , T₀ , T₀ , T₂) ∷ (T₂ , T₀ , T₀ , T₀ , T₀ , T₂) ∷ (T₀ , T₁ , T₀ , T₀ , T₀ , T₂) ∷ (T₁ , T₁ , T₀ , T₀ , T₀ , T₂) ∷ (T₂ , T₁ , T₀ , T₀ , T₀ , T₂) ∷ (T₀ , T₂ , T₀ , T₀ , T₀ , T₂) ∷ (T₁ , T₂ , T₀ , T₀ , T₀ , T₂) ∷ (T₂ , T₂ , T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀ , T₀ , T₂) ∷ (T₁ , T₀ , T₁ , T₀ , T₀ , T₂) ∷ (T₂ , T₀ , T₁ , T₀ , T₀ , T₂) ∷ (T₀ , T₁ , T₁ , T₀ , T₀ , T₂) ∷ (T₁ , T₁ , T₁ , T₀ , T₀ , T₂) ∷ (T₂ , T₁ , T₁ , T₀ , T₀ , T₂) ∷ (T₀ , T₂ , T₁ , T₀ , T₀ , T₂) ∷ (T₁ , T₂ , T₁ , T₀ , T₀ , T₂) ∷ (T₂ , T₂ , T₁ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀ , T₀ , T₂) ∷ (T₁ , T₀ , T₂ , T₀ , T₀ , T₂) ∷ (T₂ , T₀ , T₂ , T₀ , T₀ , T₂) ∷ (T₀ , T₁ , T₂ , T₀ , T₀ , T₂) ∷ (T₁ , T₁ , T₂ , T₀ , T₀ , T₂) ∷ (T₂ , T₁ , T₂ , T₀ , T₀ , T₂) ∷ (T₀ , T₂ , T₂ , T₀ , T₀ , T₂) ∷ (T₁ , T₂ , T₂ , T₀ , T₀ , T₂) ∷ (T₂ , T₂ , T₂ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₀ , T₁ , T₀ , T₂) ∷ (T₁ , T₀ , T₀ , T₁ , T₀ , T₂) ∷ (T₂ , T₀ , T₀ , T₁ , T₀ , T₂) ∷ (T₀ , T₁ , T₀ , T₁ , T₀ , T₂) ∷ (T₁ , T₁ , T₀ , T₁ , T₀ , T₂) ∷ (T₂ , T₁ , T₀ , T₁ , T₀ , T₂) ∷ (T₀ , T₂ , T₀ , T₁ , T₀ , T₂) ∷ (T₁ , T₂ , T₀ , T₁ , T₀ , T₂) ∷ (T₂ , T₂ , T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₁ , T₀ , T₂) ∷ (T₁ , T₀ , T₁ , T₁ , T₀ , T₂) ∷ (T₂ , T₀ , T₁ , T₁ , T₀ , T₂) ∷ (T₀ , T₁ , T₁ , T₁ , T₀ , T₂) ∷ (T₁ , T₁ , T₁ , T₁ , T₀ , T₂) ∷ (T₂ , T₁ , T₁ , T₁ , T₀ , T₂) ∷ (T₀ , T₂ , T₁ , T₁ , T₀ , T₂) ∷ (T₁ , T₂ , T₁ , T₁ , T₀ , T₂) ∷ (T₂ , T₂ , T₁ , T₁ , T₀ , T₂) ∷
  (T₀ , T₀ , T₂ , T₁ , T₀ , T₂) ∷ (T₁ , T₀ , T₂ , T₁ , T₀ , T₂) ∷ (T₂ , T₀ , T₂ , T₁ , T₀ , T₂) ∷ (T₀ , T₁ , T₂ , T₁ , T₀ , T₂) ∷ (T₁ , T₁ , T₂ , T₁ , T₀ , T₂) ∷ (T₂ , T₁ , T₂ , T₁ , T₀ , T₂) ∷ (T₀ , T₂ , T₂ , T₁ , T₀ , T₂) ∷ (T₁ , T₂ , T₂ , T₁ , T₀ , T₂) ∷ (T₂ , T₂ , T₂ , T₁ , T₀ , T₂) ∷
  (T₀ , T₀ , T₀ , T₂ , T₀ , T₂) ∷ (T₁ , T₀ , T₀ , T₂ , T₀ , T₂) ∷ (T₂ , T₀ , T₀ , T₂ , T₀ , T₂) ∷ (T₀ , T₁ , T₀ , T₂ , T₀ , T₂) ∷ (T₁ , T₁ , T₀ , T₂ , T₀ , T₂) ∷ (T₂ , T₁ , T₀ , T₂ , T₀ , T₂) ∷ (T₀ , T₂ , T₀ , T₂ , T₀ , T₂) ∷ (T₁ , T₂ , T₀ , T₂ , T₀ , T₂) ∷ (T₂ , T₂ , T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₂ , T₀ , T₂) ∷ (T₁ , T₀ , T₁ , T₂ , T₀ , T₂) ∷ (T₂ , T₀ , T₁ , T₂ , T₀ , T₂) ∷ (T₀ , T₁ , T₁ , T₂ , T₀ , T₂) ∷ (T₁ , T₁ , T₁ , T₂ , T₀ , T₂) ∷ (T₂ , T₁ , T₁ , T₂ , T₀ , T₂) ∷ (T₀ , T₂ , T₁ , T₂ , T₀ , T₂) ∷ (T₁ , T₂ , T₁ , T₂ , T₀ , T₂) ∷ (T₂ , T₂ , T₁ , T₂ , T₀ , T₂) ∷
  (T₀ , T₀ , T₂ , T₂ , T₀ , T₂) ∷ (T₁ , T₀ , T₂ , T₂ , T₀ , T₂) ∷ (T₂ , T₀ , T₂ , T₂ , T₀ , T₂) ∷ (T₀ , T₁ , T₂ , T₂ , T₀ , T₂) ∷ (T₁ , T₁ , T₂ , T₂ , T₀ , T₂) ∷ (T₂ , T₁ , T₂ , T₂ , T₀ , T₂) ∷ (T₀ , T₂ , T₂ , T₂ , T₀ , T₂) ∷ (T₁ , T₂ , T₂ , T₂ , T₀ , T₂) ∷ (T₂ , T₂ , T₂ , T₂ , T₀ , T₂) ∷
  (T₀ , T₀ , T₀ , T₀ , T₁ , T₂) ∷ (T₁ , T₀ , T₀ , T₀ , T₁ , T₂) ∷ (T₂ , T₀ , T₀ , T₀ , T₁ , T₂) ∷ (T₀ , T₁ , T₀ , T₀ , T₁ , T₂) ∷ (T₁ , T₁ , T₀ , T₀ , T₁ , T₂) ∷ (T₂ , T₁ , T₀ , T₀ , T₁ , T₂) ∷ (T₀ , T₂ , T₀ , T₀ , T₁ , T₂) ∷ (T₁ , T₂ , T₀ , T₀ , T₁ , T₂) ∷ (T₂ , T₂ , T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀ , T₁ , T₂) ∷ (T₁ , T₀ , T₁ , T₀ , T₁ , T₂) ∷ (T₂ , T₀ , T₁ , T₀ , T₁ , T₂) ∷ (T₀ , T₁ , T₁ , T₀ , T₁ , T₂) ∷ (T₁ , T₁ , T₁ , T₀ , T₁ , T₂) ∷ (T₂ , T₁ , T₁ , T₀ , T₁ , T₂) ∷ (T₀ , T₂ , T₁ , T₀ , T₁ , T₂) ∷ (T₁ , T₂ , T₁ , T₀ , T₁ , T₂) ∷ (T₂ , T₂ , T₁ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀ , T₁ , T₂) ∷ (T₁ , T₀ , T₂ , T₀ , T₁ , T₂) ∷ (T₂ , T₀ , T₂ , T₀ , T₁ , T₂) ∷ (T₀ , T₁ , T₂ , T₀ , T₁ , T₂) ∷ (T₁ , T₁ , T₂ , T₀ , T₁ , T₂) ∷ (T₂ , T₁ , T₂ , T₀ , T₁ , T₂) ∷ (T₀ , T₂ , T₂ , T₀ , T₁ , T₂) ∷ (T₁ , T₂ , T₂ , T₀ , T₁ , T₂) ∷ (T₂ , T₂ , T₂ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₀ , T₁ , T₁ , T₂) ∷ (T₁ , T₀ , T₀ , T₁ , T₁ , T₂) ∷ (T₂ , T₀ , T₀ , T₁ , T₁ , T₂) ∷ (T₀ , T₁ , T₀ , T₁ , T₁ , T₂) ∷ (T₁ , T₁ , T₀ , T₁ , T₁ , T₂) ∷ (T₂ , T₁ , T₀ , T₁ , T₁ , T₂) ∷ (T₀ , T₂ , T₀ , T₁ , T₁ , T₂) ∷ (T₁ , T₂ , T₀ , T₁ , T₁ , T₂) ∷ (T₂ , T₂ , T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₀ , T₁ , T₁ , T₁ , T₂) ∷ (T₁ , T₀ , T₁ , T₁ , T₁ , T₂) ∷ (T₂ , T₀ , T₁ , T₁ , T₁ , T₂) ∷ (T₀ , T₁ , T₁ , T₁ , T₁ , T₂) ∷ (T₁ , T₁ , T₁ , T₁ , T₁ , T₂) ∷ (T₂ , T₁ , T₁ , T₁ , T₁ , T₂) ∷ (T₀ , T₂ , T₁ , T₁ , T₁ , T₂) ∷ (T₁ , T₂ , T₁ , T₁ , T₁ , T₂) ∷ (T₂ , T₂ , T₁ , T₁ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₁ , T₁ , T₂) ∷ (T₁ , T₀ , T₂ , T₁ , T₁ , T₂) ∷ (T₂ , T₀ , T₂ , T₁ , T₁ , T₂) ∷ (T₀ , T₁ , T₂ , T₁ , T₁ , T₂) ∷ (T₁ , T₁ , T₂ , T₁ , T₁ , T₂) ∷ (T₂ , T₁ , T₂ , T₁ , T₁ , T₂) ∷ (T₀ , T₂ , T₂ , T₁ , T₁ , T₂) ∷ (T₁ , T₂ , T₂ , T₁ , T₁ , T₂) ∷ (T₂ , T₂ , T₂ , T₁ , T₁ , T₂) ∷
  (T₀ , T₀ , T₀ , T₂ , T₁ , T₂) ∷ (T₁ , T₀ , T₀ , T₂ , T₁ , T₂) ∷ (T₂ , T₀ , T₀ , T₂ , T₁ , T₂) ∷ (T₀ , T₁ , T₀ , T₂ , T₁ , T₂) ∷ (T₁ , T₁ , T₀ , T₂ , T₁ , T₂) ∷ (T₂ , T₁ , T₀ , T₂ , T₁ , T₂) ∷ (T₀ , T₂ , T₀ , T₂ , T₁ , T₂) ∷ (T₁ , T₂ , T₀ , T₂ , T₁ , T₂) ∷ (T₂ , T₂ , T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₀ , T₁ , T₂ , T₁ , T₂) ∷ (T₁ , T₀ , T₁ , T₂ , T₁ , T₂) ∷ (T₂ , T₀ , T₁ , T₂ , T₁ , T₂) ∷ (T₀ , T₁ , T₁ , T₂ , T₁ , T₂) ∷ (T₁ , T₁ , T₁ , T₂ , T₁ , T₂) ∷ (T₂ , T₁ , T₁ , T₂ , T₁ , T₂) ∷ (T₀ , T₂ , T₁ , T₂ , T₁ , T₂) ∷ (T₁ , T₂ , T₁ , T₂ , T₁ , T₂) ∷ (T₂ , T₂ , T₁ , T₂ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₂ , T₁ , T₂) ∷ (T₁ , T₀ , T₂ , T₂ , T₁ , T₂) ∷ (T₂ , T₀ , T₂ , T₂ , T₁ , T₂) ∷ (T₀ , T₁ , T₂ , T₂ , T₁ , T₂) ∷ (T₁ , T₁ , T₂ , T₂ , T₁ , T₂) ∷ (T₂ , T₁ , T₂ , T₂ , T₁ , T₂) ∷ (T₀ , T₂ , T₂ , T₂ , T₁ , T₂) ∷ (T₁ , T₂ , T₂ , T₂ , T₁ , T₂) ∷ (T₂ , T₂ , T₂ , T₂ , T₁ , T₂) ∷
  (T₀ , T₀ , T₀ , T₀ , T₂ , T₂) ∷ (T₁ , T₀ , T₀ , T₀ , T₂ , T₂) ∷ (T₂ , T₀ , T₀ , T₀ , T₂ , T₂) ∷ (T₀ , T₁ , T₀ , T₀ , T₂ , T₂) ∷ (T₁ , T₁ , T₀ , T₀ , T₂ , T₂) ∷ (T₂ , T₁ , T₀ , T₀ , T₂ , T₂) ∷ (T₀ , T₂ , T₀ , T₀ , T₂ , T₂) ∷ (T₁ , T₂ , T₀ , T₀ , T₂ , T₂) ∷ (T₂ , T₂ , T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀ , T₂ , T₂) ∷ (T₁ , T₀ , T₁ , T₀ , T₂ , T₂) ∷ (T₂ , T₀ , T₁ , T₀ , T₂ , T₂) ∷ (T₀ , T₁ , T₁ , T₀ , T₂ , T₂) ∷ (T₁ , T₁ , T₁ , T₀ , T₂ , T₂) ∷ (T₂ , T₁ , T₁ , T₀ , T₂ , T₂) ∷ (T₀ , T₂ , T₁ , T₀ , T₂ , T₂) ∷ (T₁ , T₂ , T₁ , T₀ , T₂ , T₂) ∷ (T₂ , T₂ , T₁ , T₀ , T₂ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀ , T₂ , T₂) ∷ (T₁ , T₀ , T₂ , T₀ , T₂ , T₂) ∷ (T₂ , T₀ , T₂ , T₀ , T₂ , T₂) ∷ (T₀ , T₁ , T₂ , T₀ , T₂ , T₂) ∷ (T₁ , T₁ , T₂ , T₀ , T₂ , T₂) ∷ (T₂ , T₁ , T₂ , T₀ , T₂ , T₂) ∷ (T₀ , T₂ , T₂ , T₀ , T₂ , T₂) ∷ (T₁ , T₂ , T₂ , T₀ , T₂ , T₂) ∷ (T₂ , T₂ , T₂ , T₀ , T₂ , T₂) ∷
  (T₀ , T₀ , T₀ , T₁ , T₂ , T₂) ∷ (T₁ , T₀ , T₀ , T₁ , T₂ , T₂) ∷ (T₂ , T₀ , T₀ , T₁ , T₂ , T₂) ∷ (T₀ , T₁ , T₀ , T₁ , T₂ , T₂) ∷ (T₁ , T₁ , T₀ , T₁ , T₂ , T₂) ∷ (T₂ , T₁ , T₀ , T₁ , T₂ , T₂) ∷ (T₀ , T₂ , T₀ , T₁ , T₂ , T₂) ∷ (T₁ , T₂ , T₀ , T₁ , T₂ , T₂) ∷ (T₂ , T₂ , T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₀ , T₁ , T₁ , T₂ , T₂) ∷ (T₁ , T₀ , T₁ , T₁ , T₂ , T₂) ∷ (T₂ , T₀ , T₁ , T₁ , T₂ , T₂) ∷ (T₀ , T₁ , T₁ , T₁ , T₂ , T₂) ∷ (T₁ , T₁ , T₁ , T₁ , T₂ , T₂) ∷ (T₂ , T₁ , T₁ , T₁ , T₂ , T₂) ∷ (T₀ , T₂ , T₁ , T₁ , T₂ , T₂) ∷ (T₁ , T₂ , T₁ , T₁ , T₂ , T₂) ∷ (T₂ , T₂ , T₁ , T₁ , T₂ , T₂) ∷
  (T₀ , T₀ , T₂ , T₁ , T₂ , T₂) ∷ (T₁ , T₀ , T₂ , T₁ , T₂ , T₂) ∷ (T₂ , T₀ , T₂ , T₁ , T₂ , T₂) ∷ (T₀ , T₁ , T₂ , T₁ , T₂ , T₂) ∷ (T₁ , T₁ , T₂ , T₁ , T₂ , T₂) ∷ (T₂ , T₁ , T₂ , T₁ , T₂ , T₂) ∷ (T₀ , T₂ , T₂ , T₁ , T₂ , T₂) ∷ (T₁ , T₂ , T₂ , T₁ , T₂ , T₂) ∷ (T₂ , T₂ , T₂ , T₁ , T₂ , T₂) ∷
  (T₀ , T₀ , T₀ , T₂ , T₂ , T₂) ∷ (T₁ , T₀ , T₀ , T₂ , T₂ , T₂) ∷ (T₂ , T₀ , T₀ , T₂ , T₂ , T₂) ∷ (T₀ , T₁ , T₀ , T₂ , T₂ , T₂) ∷ (T₁ , T₁ , T₀ , T₂ , T₂ , T₂) ∷ (T₂ , T₁ , T₀ , T₂ , T₂ , T₂) ∷ (T₀ , T₂ , T₀ , T₂ , T₂ , T₂) ∷ (T₁ , T₂ , T₀ , T₂ , T₂ , T₂) ∷ (T₂ , T₂ , T₀ , T₂ , T₂ , T₂) ∷
  (T₀ , T₀ , T₁ , T₂ , T₂ , T₂) ∷ (T₁ , T₀ , T₁ , T₂ , T₂ , T₂) ∷ (T₂ , T₀ , T₁ , T₂ , T₂ , T₂) ∷ (T₀ , T₁ , T₁ , T₂ , T₂ , T₂) ∷ (T₁ , T₁ , T₁ , T₂ , T₂ , T₂) ∷ (T₂ , T₁ , T₁ , T₂ , T₂ , T₂) ∷ (T₀ , T₂ , T₁ , T₂ , T₂ , T₂) ∷ (T₁ , T₂ , T₁ , T₂ , T₂ , T₂) ∷ (T₂ , T₂ , T₁ , T₂ , T₂ , T₂) ∷
  (T₀ , T₀ , T₂ , T₂ , T₂ , T₂) ∷ (T₁ , T₀ , T₂ , T₂ , T₂ , T₂) ∷ (T₂ , T₀ , T₂ , T₂ , T₂ , T₂) ∷ (T₀ , T₁ , T₂ , T₂ , T₂ , T₂) ∷ (T₁ , T₁ , T₂ , T₂ , T₂ , T₂) ∷ (T₂ , T₁ , T₂ , T₂ , T₂ , T₂) ∷ (T₀ , T₂ , T₂ , T₂ , T₂ , T₂) ∷ (T₁ , T₂ , T₂ , T₂ , T₂ , T₂) ∷ (T₂ , T₂ , T₂ , T₂ , T₂ , T₂) ∷ []

--------------------------------------------------------------------------------
-- 子域驻留谓词（ISA 拦截指令语义：x ∈ GF(3ᵈ) ⟺ x^(3ᵈ) = x）
--------------------------------------------------------------------------------

subfield1 : GF36 → Bool  -- GF(3) 驻留
subfield1 x = frobenius36 x ==³⁶ x

subfield2 : GF36 → Bool  -- GF(9) 驻留
subfield2 x = frobenius36 (frobenius36 x) ==³⁶ x

subfield3 : GF36 → Bool  -- GF(27) 驻留
subfield3 x = frobenius36 (frobenius36 (frobenius36 x)) ==³⁶ x

--------------------------------------------------------------------------------
-- 嵌入种子
--------------------------------------------------------------------------------

beta36 : GF36  -- β = θ + 2θ² + θ³ + θ⁴；β² = 2；被 σ² 固定（GF(9) 嵌入种子）
beta36 = T₀ , T₁ , T₂ , T₁ , T₁ , T₀

gamma36 : GF36  -- γ = θ² + 2θ³ + θ⁴；γ³ = γ + 2；被 σ³ 固定（GF(27) 嵌入种子）
gamma36 = T₀ , T₀ , T₁ , T₂ , T₁ , T₀

--------------------------------------------------------------------------------
-- 枚举完备性守卫（all27 缺陷类的回归测试）
--------------------------------------------------------------------------------

pin-36-length : length all729 ≡ 729
pin-36-length = refl

pin-36-nodup : length (dedup36 all729) ≡ 729
pin-36-nodup = refl

--------------------------------------------------------------------------------
-- 子域计数定理：d∣6 判据的完整实例（不可约性的枚举确立）
--------------------------------------------------------------------------------

pin-36-fix-σ : length (keepIf36 subfield1 all729) ≡ 3
pin-36-fix-σ = refl

pin-36-fix-σ² : length (keepIf36 subfield2 all729) ≡ 9
pin-36-fix-σ² = refl

pin-36-fix-σ³ : length (keepIf36 subfield3 all729) ≡ 27
pin-36-fix-σ³ = refl

pin-36-fix-σ⁶ : length (keepIf36 (λ x →
  frobenius36 (frobenius36 (frobenius36 (frobenius36 (frobenius36 (frobenius36 x))))) ==³⁶ x)
  all729) ≡ 729
pin-36-fix-σ⁶ = refl

--------------------------------------------------------------------------------
-- 嵌入种子定义式与 σ-乘法一致性
--------------------------------------------------------------------------------

pin-36-beta-sq : beta36 *gf36 beta36 ≡ embed-gf3-gf36 T₂
pin-36-beta-sq = refl

pin-36-gamma-cube :
  (gamma36 *gf36 gamma36) *gf36 gamma36 ≡ gamma36 +gf36 embed-gf3-gf36 T₂
pin-36-gamma-cube = refl

pin-36-beta-σ²-fixed : subfield2 beta36 ≡ true
pin-36-beta-σ²-fixed = refl

pin-36-gamma-σ³-fixed : subfield3 gamma36 ≡ true
pin-36-gamma-σ³-fixed = refl

-- σ 保乘法抽查（θ² 上；与脚本 729² 全对互证）
pin-36-σ-mul-theta :
  frobenius36 (theta36 *gf36 theta36)
  ≡ frobenius36 theta36 *gf36 frobenius36 theta36
pin-36-σ-mul-theta = refl

-- θ⁶ = 2θ + 1（约化式的域内回读：θ³·θ³ = 1 + 2θ）
pin-36-theta-⁶ :
  ((theta36 *gf36 theta36) *gf36 theta36) *gf36 ((theta36 *gf36 theta36) *gf36 theta36)
  ≡ embed-gf3-gf36 T₁ +gf36 (embed-gf3-gf36 T₂ *gf36 theta36)
pin-36-theta-⁶ = refl
