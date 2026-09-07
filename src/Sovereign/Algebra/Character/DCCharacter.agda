{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Character.DCCharacter
-- DC（代数核）的特征: 同态性、反射作用
--
-- ⚠️ 关键区分:
--   - Doz（十二进制位值记数法）= 以 12 为底的数字系统
--   - DC（DuodecClock）= Trit × AlphaPower = 3 × 4 = 恰好 12 个元素
--   - 特征函数 χ_(u,v) 定义在 DC 上（12 个元素），不是整个 Doz 数系
--
-- 【载体裁定 2026-09-07 审计】
--   草稿原版把特征值放在 Sqrt3 = ℚ(√3)（全实域）:
--     ζ₃ = -1/2 + (1/2)√3 的三次幂 = -5/4 + (3/4)√3 ≠ 1 (计算否证);
--     全实域容不下任何非平凡单位根。
--   正确载体: Z12Sys = ℚ(ζ₁₂) 的 4 维 ℚ-基表示
--     (a,b,c,d) ↦ a + b·i + c·γ + d·iγ,  i² = -1, γ² = -3, iγ = γi
--     ζ₃ = -1/2 + (1/2)γ,  ζ₄ = i,  ζ₃³ = 1 与 i² = -1 均为 refl 可验。
--   坐标全部 ∈ ℚ (定点整数比, 宪法禁浮点), 0 postulate, 0 hole。
--
-- 【草稿另两处已修正】
--   - 相位特征映射草稿写 aₖ ↦ ζ₃^k, 应为 ζ₄^k = i^k, 已修正。
--   - 正交性/自内积/Parseval 需要 Z12Sys 分配律与几何级数引理（符号和操作，
--     非逐点 refl 可达），属下一层工作; hole 函数已删除不留洞。

module Sovereign.Algebra.Character.DCCharacter where

open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Rational using (ℚ; mkℚ; _+_; _-_; _*_; _/_; -_)
open import Data.Rational.Solver
open import Data.Integer using (+_; -[1+_]; +0; +[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; tritToFin3)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; mixedOp; mulAlpha; alphaInv; rho; alphaToFin4)

--------------------------------------------------------------------------------
-- §1. 载体: Z12Sys = ℚ(ζ₁₂), (a,b,c,d) ↦ a + b·i + c·γ + d·iγ
--------------------------------------------------------------------------------

record Z12Sys : Set where
  constructor _+z_+z_+z_
  field
    re   : ℚ   -- 1 分量
    icpt : ℚ   -- i 分量
    gam  : ℚ   -- γ = √-3 分量
    igm  : ℚ   -- iγ 分量

z0 : Z12Sys
z0 = (+ 0 / 1) +z (+ 0 / 1) +z (+ 0 / 1) +z (+ 0 / 1)

z1 : Z12Sys
z1 = (+ 1 / 1) +z (+ 0 / 1) +z (+ 0 / 1) +z (+ 0 / 1)

negq : ℚ → ℚ
negq q = (+ 0 / 1) - q

-- 乘法: i² = -1, γ² = -3, iγ = γi 双线性展开
--   1  分量: aa' - bb' - 3cc' + 3dd'
--   i  分量: ab' + ba' - 3(cd' + dc')
--   γ  分量: ac' + ca' - (bd' + db')
--   iγ 分量: ad' + da' + bc' + cb'
_*ᶻ_ : Z12Sys → Z12Sys → Z12Sys
_*ᶻ_ (a +z b +z c +z d) (a' +z b' +z c' +z d') =
  (((a * a') - (b * b')) + ((+ 3 / 1) * ((d * d') - (c * c'))))
  +z (((a * b') + (b * a')) - ((+ 3 / 1) * ((c * d') + (d * c'))))
  +z (((a * c') + (c * a')) - ((b * d') + (d * b')))
  +z (((a * d') + (d * a')) + ((b * c') + (c * b')))

-- 加法 (分量式)
_+ᶻ_ : Z12Sys → Z12Sys → Z12Sys
_+ᶻ_ (a +z b +z c +z d) (a' +z b' +z c' +z d') =
  (a + a') +z (b + b') +z (c + c') +z (d + d')

-- 复共轭 (域自同构): i ↦ -i, γ ↦ -γ; conj ζ₃ = ζ₃², conj i = i³ = -i
-- 共轭用一元 -_ (与 stdlib neg-distrib-* 引理族直接对接;
-- 所有 conjᶻ 使用点均为 refl 证明, 定义变更零级联)
conjᶻ : Z12Sys → Z12Sys
conjᶻ (a +z b +z c +z d) = a +z (- b) +z (- c) +z d

-- 单位根
ζ₃ : Z12Sys   -- 三次单位根: -1/2 + γ/2
ζ₃ = (-[1+ 0 ] / 2) +z (+ 0 / 1) +z (+ 1 / 2) +z (+ 0 / 1)

ζ₃² : Z12Sys
ζ₃² = (-[1+ 0 ] / 2) +z (+ 0 / 1) +z (negq (+ 1 / 2)) +z (+ 0 / 1)

zi : Z12Sys    -- 四次单位根 i
zi = (+ 0 / 1) +z (+ 1 / 1) +z (+ 0 / 1) +z (+ 0 / 1)

zi² : Z12Sys
zi² = (-[1+ 0 ] / 1) +z (+ 0 / 1) +z (+ 0 / 1) +z (+ 0 / 1)

zi³ : Z12Sys
zi³ = (+ 0 / 1) +z (negq (+ 1 / 1)) +z (+ 0 / 1) +z (+ 0 / 1)

-- 载体验证 (refl 可验, 替代草稿中错误的 Sqrt3 断言)
zeta3-cubed : ((ζ₃ *ᶻ ζ₃) *ᶻ ζ₃) ≡ z1
zeta3-cubed = refl

i-squared : (zi *ᶻ zi) ≡ zi²
i-squared = refl

conj-zeta3 : conjᶻ ζ₃ ≡ ζ₃²
conj-zeta3 = refl

--------------------------------------------------------------------------------
-- §2. 特征索引: (u,v) ∈ F₃ × C₄, 共 12 个特征
--------------------------------------------------------------------------------

CharacterIndex : Set
CharacterIndex = Trit × AlphaPower

charIndexToNat : CharacterIndex → ℕ
charIndexToNat (u , v) = (toℕ (tritToFin3 u) *ℕ 4) +ℕ toℕ (alphaToFin4 v)

--------------------------------------------------------------------------------
-- §3. 特征函数: χ_(u,v)(t, aₖ) = ζ₃^(u·t) · ζ₄^(v∘k)
--     损益通道用 ζ₃, 相位通道用 ζ₄ = i (草稿误写 ζ₃, 已修正)
--------------------------------------------------------------------------------

tritToZ : Trit → Z12Sys
tritToZ T₀ = z1
tritToZ T₁ = ζ₃
tritToZ T₂ = ζ₃²

alphaToZ : AlphaPower → Z12Sys
alphaToZ a0 = z1
alphaToZ a1 = zi
alphaToZ a2 = zi²
alphaToZ a3 = zi³

-- 相位指数的乘法: (α^k)^v = α^{k·v} — 特征需要指数相乘 (乘法), 不是 mulAlpha (加法)
-- 草稿此处用 mulAlpha v a, 导致 χ(p·q) = χ(p)χ(q) 失败 (i ≠ i·i); 已修正
alpha-pow : AlphaPower → AlphaPower → AlphaPower
alpha-pow a0 _ = a0
alpha-pow a1 a = a
alpha-pow a2 a = mulAlpha a a
alpha-pow a3 a = mulAlpha a (mulAlpha a a)

dc-character : CharacterIndex → DuodecPoint → Z12Sys
dc-character (u , v) (t , a) = (tritToZ (u ⊗ t)) *ᶻ (alphaToZ (alpha-pow v a))

--------------------------------------------------------------------------------
-- §4. 特征是群同态: χ(p·q) = χ(p)·χ(q) (12 × 12 × 12 = 1728 case refl)
--------------------------------------------------------------------------------

dc-character-hom : ∀ (idx : CharacterIndex) (p q : DuodecPoint) →
  dc-character idx (mixedOp p q) ≡ dc-character idx p *ᶻ dc-character idx q
dc-character-hom (T₀ , a0) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a0) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a1) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a2) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₀ , a3) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a0) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a1) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a2) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₁ , a3) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a0) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a1) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a2) (T₂ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₀ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₁ , a3) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a0) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a1) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a2) (T₂ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₀ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₀ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₀ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₀ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₁ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₁ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₁ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₁ , a3) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₂ , a0) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₂ , a1) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₂ , a2) = refl
dc-character-hom (T₂ , a3) (T₂ , a3) (T₂ , a3) = refl

--------------------------------------------------------------------------------
-- §5. 反射 ρ 把特征映到复共轭: χ(ρ p) = conj χ(p) (144 case refl)
--------------------------------------------------------------------------------

rho-character : ∀ (idx : CharacterIndex) (p : DuodecPoint) →
  dc-character idx (rho p) ≡ conjᶻ (dc-character idx p)
rho-character (T₀ , a0) (T₀ , a0) = refl
rho-character (T₀ , a0) (T₀ , a1) = refl
rho-character (T₀ , a0) (T₀ , a2) = refl
rho-character (T₀ , a0) (T₀ , a3) = refl
rho-character (T₀ , a0) (T₁ , a0) = refl
rho-character (T₀ , a0) (T₁ , a1) = refl
rho-character (T₀ , a0) (T₁ , a2) = refl
rho-character (T₀ , a0) (T₁ , a3) = refl
rho-character (T₀ , a0) (T₂ , a0) = refl
rho-character (T₀ , a0) (T₂ , a1) = refl
rho-character (T₀ , a0) (T₂ , a2) = refl
rho-character (T₀ , a0) (T₂ , a3) = refl
rho-character (T₀ , a1) (T₀ , a0) = refl
rho-character (T₀ , a1) (T₀ , a1) = refl
rho-character (T₀ , a1) (T₀ , a2) = refl
rho-character (T₀ , a1) (T₀ , a3) = refl
rho-character (T₀ , a1) (T₁ , a0) = refl
rho-character (T₀ , a1) (T₁ , a1) = refl
rho-character (T₀ , a1) (T₁ , a2) = refl
rho-character (T₀ , a1) (T₁ , a3) = refl
rho-character (T₀ , a1) (T₂ , a0) = refl
rho-character (T₀ , a1) (T₂ , a1) = refl
rho-character (T₀ , a1) (T₂ , a2) = refl
rho-character (T₀ , a1) (T₂ , a3) = refl
rho-character (T₀ , a2) (T₀ , a0) = refl
rho-character (T₀ , a2) (T₀ , a1) = refl
rho-character (T₀ , a2) (T₀ , a2) = refl
rho-character (T₀ , a2) (T₀ , a3) = refl
rho-character (T₀ , a2) (T₁ , a0) = refl
rho-character (T₀ , a2) (T₁ , a1) = refl
rho-character (T₀ , a2) (T₁ , a2) = refl
rho-character (T₀ , a2) (T₁ , a3) = refl
rho-character (T₀ , a2) (T₂ , a0) = refl
rho-character (T₀ , a2) (T₂ , a1) = refl
rho-character (T₀ , a2) (T₂ , a2) = refl
rho-character (T₀ , a2) (T₂ , a3) = refl
rho-character (T₀ , a3) (T₀ , a0) = refl
rho-character (T₀ , a3) (T₀ , a1) = refl
rho-character (T₀ , a3) (T₀ , a2) = refl
rho-character (T₀ , a3) (T₀ , a3) = refl
rho-character (T₀ , a3) (T₁ , a0) = refl
rho-character (T₀ , a3) (T₁ , a1) = refl
rho-character (T₀ , a3) (T₁ , a2) = refl
rho-character (T₀ , a3) (T₁ , a3) = refl
rho-character (T₀ , a3) (T₂ , a0) = refl
rho-character (T₀ , a3) (T₂ , a1) = refl
rho-character (T₀ , a3) (T₂ , a2) = refl
rho-character (T₀ , a3) (T₂ , a3) = refl
rho-character (T₁ , a0) (T₀ , a0) = refl
rho-character (T₁ , a0) (T₀ , a1) = refl
rho-character (T₁ , a0) (T₀ , a2) = refl
rho-character (T₁ , a0) (T₀ , a3) = refl
rho-character (T₁ , a0) (T₁ , a0) = refl
rho-character (T₁ , a0) (T₁ , a1) = refl
rho-character (T₁ , a0) (T₁ , a2) = refl
rho-character (T₁ , a0) (T₁ , a3) = refl
rho-character (T₁ , a0) (T₂ , a0) = refl
rho-character (T₁ , a0) (T₂ , a1) = refl
rho-character (T₁ , a0) (T₂ , a2) = refl
rho-character (T₁ , a0) (T₂ , a3) = refl
rho-character (T₁ , a1) (T₀ , a0) = refl
rho-character (T₁ , a1) (T₀ , a1) = refl
rho-character (T₁ , a1) (T₀ , a2) = refl
rho-character (T₁ , a1) (T₀ , a3) = refl
rho-character (T₁ , a1) (T₁ , a0) = refl
rho-character (T₁ , a1) (T₁ , a1) = refl
rho-character (T₁ , a1) (T₁ , a2) = refl
rho-character (T₁ , a1) (T₁ , a3) = refl
rho-character (T₁ , a1) (T₂ , a0) = refl
rho-character (T₁ , a1) (T₂ , a1) = refl
rho-character (T₁ , a1) (T₂ , a2) = refl
rho-character (T₁ , a1) (T₂ , a3) = refl
rho-character (T₁ , a2) (T₀ , a0) = refl
rho-character (T₁ , a2) (T₀ , a1) = refl
rho-character (T₁ , a2) (T₀ , a2) = refl
rho-character (T₁ , a2) (T₀ , a3) = refl
rho-character (T₁ , a2) (T₁ , a0) = refl
rho-character (T₁ , a2) (T₁ , a1) = refl
rho-character (T₁ , a2) (T₁ , a2) = refl
rho-character (T₁ , a2) (T₁ , a3) = refl
rho-character (T₁ , a2) (T₂ , a0) = refl
rho-character (T₁ , a2) (T₂ , a1) = refl
rho-character (T₁ , a2) (T₂ , a2) = refl
rho-character (T₁ , a2) (T₂ , a3) = refl
rho-character (T₁ , a3) (T₀ , a0) = refl
rho-character (T₁ , a3) (T₀ , a1) = refl
rho-character (T₁ , a3) (T₀ , a2) = refl
rho-character (T₁ , a3) (T₀ , a3) = refl
rho-character (T₁ , a3) (T₁ , a0) = refl
rho-character (T₁ , a3) (T₁ , a1) = refl
rho-character (T₁ , a3) (T₁ , a2) = refl
rho-character (T₁ , a3) (T₁ , a3) = refl
rho-character (T₁ , a3) (T₂ , a0) = refl
rho-character (T₁ , a3) (T₂ , a1) = refl
rho-character (T₁ , a3) (T₂ , a2) = refl
rho-character (T₁ , a3) (T₂ , a3) = refl
rho-character (T₂ , a0) (T₀ , a0) = refl
rho-character (T₂ , a0) (T₀ , a1) = refl
rho-character (T₂ , a0) (T₀ , a2) = refl
rho-character (T₂ , a0) (T₀ , a3) = refl
rho-character (T₂ , a0) (T₁ , a0) = refl
rho-character (T₂ , a0) (T₁ , a1) = refl
rho-character (T₂ , a0) (T₁ , a2) = refl
rho-character (T₂ , a0) (T₁ , a3) = refl
rho-character (T₂ , a0) (T₂ , a0) = refl
rho-character (T₂ , a0) (T₂ , a1) = refl
rho-character (T₂ , a0) (T₂ , a2) = refl
rho-character (T₂ , a0) (T₂ , a3) = refl
rho-character (T₂ , a1) (T₀ , a0) = refl
rho-character (T₂ , a1) (T₀ , a1) = refl
rho-character (T₂ , a1) (T₀ , a2) = refl
rho-character (T₂ , a1) (T₀ , a3) = refl
rho-character (T₂ , a1) (T₁ , a0) = refl
rho-character (T₂ , a1) (T₁ , a1) = refl
rho-character (T₂ , a1) (T₁ , a2) = refl
rho-character (T₂ , a1) (T₁ , a3) = refl
rho-character (T₂ , a1) (T₂ , a0) = refl
rho-character (T₂ , a1) (T₂ , a1) = refl
rho-character (T₂ , a1) (T₂ , a2) = refl
rho-character (T₂ , a1) (T₂ , a3) = refl
rho-character (T₂ , a2) (T₀ , a0) = refl
rho-character (T₂ , a2) (T₀ , a1) = refl
rho-character (T₂ , a2) (T₀ , a2) = refl
rho-character (T₂ , a2) (T₀ , a3) = refl
rho-character (T₂ , a2) (T₁ , a0) = refl
rho-character (T₂ , a2) (T₁ , a1) = refl
rho-character (T₂ , a2) (T₁ , a2) = refl
rho-character (T₂ , a2) (T₁ , a3) = refl
rho-character (T₂ , a2) (T₂ , a0) = refl
rho-character (T₂ , a2) (T₂ , a1) = refl
rho-character (T₂ , a2) (T₂ , a2) = refl
rho-character (T₂ , a2) (T₂ , a3) = refl
rho-character (T₂ , a3) (T₀ , a0) = refl
rho-character (T₂ , a3) (T₀ , a1) = refl
rho-character (T₂ , a3) (T₀ , a2) = refl
rho-character (T₂ , a3) (T₀ , a3) = refl
rho-character (T₂ , a3) (T₁ , a0) = refl
rho-character (T₂ , a3) (T₁ , a1) = refl
rho-character (T₂ , a3) (T₁ , a2) = refl
rho-character (T₂ , a3) (T₁ , a3) = refl
rho-character (T₂ , a3) (T₂ , a0) = refl
rho-character (T₂ , a3) (T₂ , a1) = refl
rho-character (T₂ , a3) (T₂ , a2) = refl
rho-character (T₂ , a3) (T₂ , a3) = refl

--------------------------------------------------------------------------------
-- §6. 求和与傅里叶框架 (定义层; 正交性/Parseval 见 §7 裁定)
--------------------------------------------------------------------------------

DCFunction : Set → Set
DCFunction A = DuodecPoint → A

_+ᶻ-sum_ : Z12Sys → Z12Sys → Z12Sys
x +ᶻ-sum y = x +ᶻ y

-- DC 的 12 个元素的求和 (右结合展开)
sum-over-DC : (DuodecPoint → Z12Sys) → Z12Sys
sum-over-DC f =
  (f (T₀ , a0) +ᶻ (f (T₀ , a1) +ᶻ (f (T₀ , a2) +ᶻ (f (T₀ , a3) +ᶻ
  (f (T₁ , a0) +ᶻ (f (T₁ , a1) +ᶻ (f (T₁ , a2) +ᶻ (f (T₁ , a3) +ᶻ
  (f (T₂ , a0) +ᶻ (f (T₂ , a1) +ᶻ (f (T₂ , a2) +ᶻ f (T₂ , a3))))))))))))

-- DC 的 12 点枚举 (与 sum-over-DC 字面序逐位一致; 使字面和 = sumF{12})
dc-points : Fin 12 → DuodecPoint
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) = (T₂ , a3)
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = (T₂ , a2)
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (T₂ , a1)
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (T₂ , a0)
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (T₁ , a3)
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (T₁ , a2)
dc-points (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = (T₁ , a1)
dc-points (fsuc (fsuc (fsuc (fsuc fzero)))) = (T₁ , a0)
dc-points (fsuc (fsuc (fsuc fzero))) = (T₀ , a3)
dc-points (fsuc (fsuc fzero)) = (T₀ , a2)
dc-points (fsuc fzero) = (T₀ , a1)
dc-points fzero = (T₀ , a0)


-- 归纳求和算子: 对 Fin n 结构归纳 (依赖类型论: 以结构而非字面穷举发展理论)
-- sumF {n} f = f fzero +ᶻ (f (fsuc fzero) +ᶻ ... +ᶻ f (fromℕ (n-1)))
-- 使 Parseval 所需性质 (线性性/交换/conj 穿入) 成为结构归纳定理, 免 144 项字面树重排
sumF : ∀ {n : ℕ} → (Fin n → Z12Sys) → Z12Sys
sumF {zero} f = z0
sumF {suc n} f = f fzero +ᶻ sumF (λ i → f (fsuc i))


-- 12 个特征上的求和 (对偶正交性 / Parseval RHS 用)
sum-over-characters : (CharacterIndex → Z12Sys) → Z12Sys
sum-over-characters g =
  (g (T₀ , a0) +ᶻ (g (T₀ , a1) +ᶻ (g (T₀ , a2) +ᶻ (g (T₀ , a3) +ᶻ
  (g (T₁ , a0) +ᶻ (g (T₁ , a1) +ᶻ (g (T₁ , a2) +ᶻ (g (T₁ , a3) +ᶻ
  (g (T₂ , a0) +ᶻ (g (T₂ , a1) +ᶻ (g (T₂ , a2) +ᶻ g (T₂ , a3))))))))))))

--------------------------------------------------------------------------------
-- §5′. 正交性与自内积 (2026-09-07 第二层: 逐索引 refl 穷举)
--
-- 关键观察: 具体索引 (u,v) 下, 12 项求和的每一项都归约为具体 Z12Sys 值,
-- 故无需符号环引理, 逐 (u,v)(u',v') 穷举即可.
-- 非对角 132 case: 12 项和 = z0 (refl 可验, 如 z1+ζ₃+ζ₃² 通道求和 = 0);
-- 对角 24 case (12×2): 假设 neq : u≢u' ⊎ v≢v' 在对角上为空, ⊥-elim 消解.
--------------------------------------------------------------------------------

orthogonality : ∀ u v u' v' →
  (u ≢ u' ⊎ v ≢ v') →
  sum-over-DC (λ x → dc-character (u , v) x *ᶻ conjᶻ (dc-character (u' , v') x))
  ≡ z0
orthogonality T₀ a0 T₀ a0 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₀ a0 T₀ a0 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₀ a0 T₀ a1 neq = refl
orthogonality T₀ a0 T₀ a2 neq = refl
orthogonality T₀ a0 T₀ a3 neq = refl
orthogonality T₀ a0 T₁ a0 neq = refl
orthogonality T₀ a0 T₁ a1 neq = refl
orthogonality T₀ a0 T₁ a2 neq = refl
orthogonality T₀ a0 T₁ a3 neq = refl
orthogonality T₀ a0 T₂ a0 neq = refl
orthogonality T₀ a0 T₂ a1 neq = refl
orthogonality T₀ a0 T₂ a2 neq = refl
orthogonality T₀ a0 T₂ a3 neq = refl
orthogonality T₀ a1 T₀ a0 neq = refl
orthogonality T₀ a1 T₀ a1 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₀ a1 T₀ a1 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₀ a1 T₀ a2 neq = refl
orthogonality T₀ a1 T₀ a3 neq = refl
orthogonality T₀ a1 T₁ a0 neq = refl
orthogonality T₀ a1 T₁ a1 neq = refl
orthogonality T₀ a1 T₁ a2 neq = refl
orthogonality T₀ a1 T₁ a3 neq = refl
orthogonality T₀ a1 T₂ a0 neq = refl
orthogonality T₀ a1 T₂ a1 neq = refl
orthogonality T₀ a1 T₂ a2 neq = refl
orthogonality T₀ a1 T₂ a3 neq = refl
orthogonality T₀ a2 T₀ a0 neq = refl
orthogonality T₀ a2 T₀ a1 neq = refl
orthogonality T₀ a2 T₀ a2 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₀ a2 T₀ a2 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₀ a2 T₀ a3 neq = refl
orthogonality T₀ a2 T₁ a0 neq = refl
orthogonality T₀ a2 T₁ a1 neq = refl
orthogonality T₀ a2 T₁ a2 neq = refl
orthogonality T₀ a2 T₁ a3 neq = refl
orthogonality T₀ a2 T₂ a0 neq = refl
orthogonality T₀ a2 T₂ a1 neq = refl
orthogonality T₀ a2 T₂ a2 neq = refl
orthogonality T₀ a2 T₂ a3 neq = refl
orthogonality T₀ a3 T₀ a0 neq = refl
orthogonality T₀ a3 T₀ a1 neq = refl
orthogonality T₀ a3 T₀ a2 neq = refl
orthogonality T₀ a3 T₀ a3 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₀ a3 T₀ a3 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₀ a3 T₁ a0 neq = refl
orthogonality T₀ a3 T₁ a1 neq = refl
orthogonality T₀ a3 T₁ a2 neq = refl
orthogonality T₀ a3 T₁ a3 neq = refl
orthogonality T₀ a3 T₂ a0 neq = refl
orthogonality T₀ a3 T₂ a1 neq = refl
orthogonality T₀ a3 T₂ a2 neq = refl
orthogonality T₀ a3 T₂ a3 neq = refl
orthogonality T₁ a0 T₀ a0 neq = refl
orthogonality T₁ a0 T₀ a1 neq = refl
orthogonality T₁ a0 T₀ a2 neq = refl
orthogonality T₁ a0 T₀ a3 neq = refl
orthogonality T₁ a0 T₁ a0 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₁ a0 T₁ a0 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₁ a0 T₁ a1 neq = refl
orthogonality T₁ a0 T₁ a2 neq = refl
orthogonality T₁ a0 T₁ a3 neq = refl
orthogonality T₁ a0 T₂ a0 neq = refl
orthogonality T₁ a0 T₂ a1 neq = refl
orthogonality T₁ a0 T₂ a2 neq = refl
orthogonality T₁ a0 T₂ a3 neq = refl
orthogonality T₁ a1 T₀ a0 neq = refl
orthogonality T₁ a1 T₀ a1 neq = refl
orthogonality T₁ a1 T₀ a2 neq = refl
orthogonality T₁ a1 T₀ a3 neq = refl
orthogonality T₁ a1 T₁ a0 neq = refl
orthogonality T₁ a1 T₁ a1 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₁ a1 T₁ a1 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₁ a1 T₁ a2 neq = refl
orthogonality T₁ a1 T₁ a3 neq = refl
orthogonality T₁ a1 T₂ a0 neq = refl
orthogonality T₁ a1 T₂ a1 neq = refl
orthogonality T₁ a1 T₂ a2 neq = refl
orthogonality T₁ a1 T₂ a3 neq = refl
orthogonality T₁ a2 T₀ a0 neq = refl
orthogonality T₁ a2 T₀ a1 neq = refl
orthogonality T₁ a2 T₀ a2 neq = refl
orthogonality T₁ a2 T₀ a3 neq = refl
orthogonality T₁ a2 T₁ a0 neq = refl
orthogonality T₁ a2 T₁ a1 neq = refl
orthogonality T₁ a2 T₁ a2 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₁ a2 T₁ a2 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₁ a2 T₁ a3 neq = refl
orthogonality T₁ a2 T₂ a0 neq = refl
orthogonality T₁ a2 T₂ a1 neq = refl
orthogonality T₁ a2 T₂ a2 neq = refl
orthogonality T₁ a2 T₂ a3 neq = refl
orthogonality T₁ a3 T₀ a0 neq = refl
orthogonality T₁ a3 T₀ a1 neq = refl
orthogonality T₁ a3 T₀ a2 neq = refl
orthogonality T₁ a3 T₀ a3 neq = refl
orthogonality T₁ a3 T₁ a0 neq = refl
orthogonality T₁ a3 T₁ a1 neq = refl
orthogonality T₁ a3 T₁ a2 neq = refl
orthogonality T₁ a3 T₁ a3 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₁ a3 T₁ a3 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₁ a3 T₂ a0 neq = refl
orthogonality T₁ a3 T₂ a1 neq = refl
orthogonality T₁ a3 T₂ a2 neq = refl
orthogonality T₁ a3 T₂ a3 neq = refl
orthogonality T₂ a0 T₀ a0 neq = refl
orthogonality T₂ a0 T₀ a1 neq = refl
orthogonality T₂ a0 T₀ a2 neq = refl
orthogonality T₂ a0 T₀ a3 neq = refl
orthogonality T₂ a0 T₁ a0 neq = refl
orthogonality T₂ a0 T₁ a1 neq = refl
orthogonality T₂ a0 T₁ a2 neq = refl
orthogonality T₂ a0 T₁ a3 neq = refl
orthogonality T₂ a0 T₂ a0 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₂ a0 T₂ a0 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₂ a0 T₂ a1 neq = refl
orthogonality T₂ a0 T₂ a2 neq = refl
orthogonality T₂ a0 T₂ a3 neq = refl
orthogonality T₂ a1 T₀ a0 neq = refl
orthogonality T₂ a1 T₀ a1 neq = refl
orthogonality T₂ a1 T₀ a2 neq = refl
orthogonality T₂ a1 T₀ a3 neq = refl
orthogonality T₂ a1 T₁ a0 neq = refl
orthogonality T₂ a1 T₁ a1 neq = refl
orthogonality T₂ a1 T₁ a2 neq = refl
orthogonality T₂ a1 T₁ a3 neq = refl
orthogonality T₂ a1 T₂ a0 neq = refl
orthogonality T₂ a1 T₂ a1 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₂ a1 T₂ a1 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₂ a1 T₂ a2 neq = refl
orthogonality T₂ a1 T₂ a3 neq = refl
orthogonality T₂ a2 T₀ a0 neq = refl
orthogonality T₂ a2 T₀ a1 neq = refl
orthogonality T₂ a2 T₀ a2 neq = refl
orthogonality T₂ a2 T₀ a3 neq = refl
orthogonality T₂ a2 T₁ a0 neq = refl
orthogonality T₂ a2 T₁ a1 neq = refl
orthogonality T₂ a2 T₁ a2 neq = refl
orthogonality T₂ a2 T₁ a3 neq = refl
orthogonality T₂ a2 T₂ a0 neq = refl
orthogonality T₂ a2 T₂ a1 neq = refl
orthogonality T₂ a2 T₂ a2 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₂ a2 T₂ a2 (inj₂ neq) = ⊥-elim (neq refl)
orthogonality T₂ a2 T₂ a3 neq = refl
orthogonality T₂ a3 T₀ a0 neq = refl
orthogonality T₂ a3 T₀ a1 neq = refl
orthogonality T₂ a3 T₀ a2 neq = refl
orthogonality T₂ a3 T₀ a3 neq = refl
orthogonality T₂ a3 T₁ a0 neq = refl
orthogonality T₂ a3 T₁ a1 neq = refl
orthogonality T₂ a3 T₁ a2 neq = refl
orthogonality T₂ a3 T₁ a3 neq = refl
orthogonality T₂ a3 T₂ a0 neq = refl
orthogonality T₂ a3 T₂ a1 neq = refl
orthogonality T₂ a3 T₂ a2 neq = refl
orthogonality T₂ a3 T₂ a3 (inj₁ neq) = ⊥-elim (neq refl)
orthogonality T₂ a3 T₂ a3 (inj₂ neq) = ⊥-elim (neq refl)

self-inner-product : ∀ u v →
  sum-over-DC (λ x → dc-character (u , v) x *ᶻ conjᶻ (dc-character (u , v) x))
  ≡ ((+ 12 / 1) +z (+ 0 / 1) +z (+ 0 / 1) +z (+ 0 / 1))
self-inner-product T₀ a0 = refl
self-inner-product T₀ a1 = refl
self-inner-product T₀ a2 = refl
self-inner-product T₀ a3 = refl
self-inner-product T₁ a0 = refl
self-inner-product T₁ a1 = refl
self-inner-product T₁ a2 = refl
self-inner-product T₁ a3 = refl
self-inner-product T₂ a0 = refl
self-inner-product T₂ a1 = refl
self-inner-product T₂ a2 = refl
self-inner-product T₂ a3 = refl

-- 离散傅里叶变换: f̂(u,v) = Σ_x f(x) · conj(χ_(u,v)(x))
dc-dft : DCFunction Z12Sys → CharacterIndex → Z12Sys
dc-dft f idx = sum-over-DC (λ x → f x *ᶻ conjᶻ (dc-character idx x))

--------------------------------------------------------------------------------
-- §5″. Z12Sys 环定律 + 对偶正交性 (2026-09-07 第三层: Parseval 地基)
--------------------------------------------------------------------------------

module _ where
  open import Data.Rational.Properties
    using (+-comm; +-assoc; *-comm; *-assoc; *-distribˡ-+; *-distribʳ-+; neg-distrib-+;
           +-identityˡ; +-identityʳ; neg-distribˡ-*; neg-distribʳ-*; *-zeroˡ; *-zeroʳ)
  open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; module ≡-Reasoning)

  -- 记录延拓: 分量相等则值相等 (单构造子记录)
  zext : ∀ {a b c d a' b' c' d' : ℚ} →
    a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' →
    (a +z b +z c +z d) ≡ (a' +z b' +z c' +z d')
  zext refl refl refl refl = refl

  -- 加法交换/结合 (分量式, ℚ 引理直推)
  +ᶻ-comm : ∀ x y → x +ᶻ y ≡ y +ᶻ x
  +ᶻ-comm (a +z b +z c +z d) (a' +z b' +z c' +z d') =
    zext (+-comm a a') (+-comm b b') (+-comm c c') (+-comm d d')

  +ᶻ-assoc : ∀ x y z → (x +ᶻ y) +ᶻ z ≡ x +ᶻ (y +ᶻ z)
  +ᶻ-assoc (a +z b +z c +z d) (a' +z b' +z c' +z d') (a'' +z b'' +z c'' +z d'') =
    zext (+-assoc a a' a'') (+-assoc b b' b'') (+-assoc c c' c'') (+-assoc d d' d'')

  -- 乘法交换
  *ᶻ-comm : ∀ x y → x *ᶻ y ≡ y *ᶻ x
  *ᶻ-comm (a +z b +z c +z d) (a' +z b' +z c' +z d') =
    zext real i compg iγ
    where
      real : (((a * a') - (b * b')) + ((+ 3 / 1) * ((d * d') - (c * c'))))
            ≡ (((a' * a) - (b' * b)) + ((+ 3 / 1) * ((d' * d) - (c' * c))))
      real = cong₂ _+_ (cong₂ _-_ (*-comm a a') (*-comm b b'))
                       (cong ((+ 3 / 1) *_) (cong₂ _-_ (*-comm d d') (*-comm c c')))
      -- 双因子互换 = 两次 *-comm + 和内交换
      i : (((a * b') + (b * a')) - ((+ 3 / 1) * ((c * d') + (d * c'))))
          ≡ (((a' * b) + (b' * a)) - ((+ 3 / 1) * ((c' * d) + (d' * c))))
      i = cong₂ _-_ (trans (cong₂ _+_ (*-comm a b') (*-comm b a')) (+-comm (b' * a) (a' * b)))
                    (cong ((+ 3 / 1) *_)
                      (trans (cong₂ _+_ (*-comm c d') (*-comm d c')) (+-comm (d' * c) (c' * d))))
      compg : (((a * c') + (c * a')) - ((b * d') + (d * b')))
              ≡ (((a' * c) + (c' * a)) - ((b' * d) + (d' * b)))
      compg = cong₂ _-_ (trans (cong₂ _+_ (*-comm a c') (*-comm c a')) (+-comm (c' * a) (a' * c)))
                        (trans (cong₂ _+_ (*-comm b d') (*-comm d b')) (+-comm (d' * b) (b' * d)))
      iγ : (((a * d') + (d * a')) + ((b * c') + (c * b')))
           ≡ (((a' * d) + (d' * a)) + ((b' * c) + (c' * b)))
      iγ = cong₂ _+_ (trans (cong₂ _+_ (*-comm a d') (*-comm d a')) (+-comm (d' * a) (a' * d)))
                     (trans (cong₂ _+_ (*-comm b c') (*-comm c b')) (+-comm (c' * b) (b' * c)))
  -- ── 分配律 (手写分量链) ──
  -- ℚ 求解器不可用: gcd 不定义归约, refl 卡在 mkℚ (0 / gcd 0 1);
  -- 改用 stdlib ℚ 环定理 (*-distribʳ-+ / *-distribˡ-+ / neg-distrib-+) 手写分量链。
  -- 注: Parseval 组装只需分配律 (+ᶻ 交换/结合), 不需 *ᶻ-assoc。

  trans-refl : ∀ {A : Set} (x : A) → x ≡ x
  trans-refl x = refl

  pair-shuffle : ∀ p q r t → (p + q) + (r + t) ≡ (p + r) + (q + t)
  pair-shuffle p q r t =
    trans (+-assoc p q (r + t))
      (trans (cong (\x → p + x)
                (trans (sym (+-assoc q r t))
                  (trans (cong (\y → y + t) (+-comm q r)) (+-assoc r q t))))
        (sym (+-assoc p r (q + t))))

  minus-shuffle : ∀ p q r t → ((p + q) - (r + t)) ≡ ((p - r) + (q - t))
  minus-shuffle p q r t =
    trans (cong (\x → (p + q) + x) (neg-distrib-+ r t))
          (pair-shuffle p q (Data.Rational.- r) (Data.Rational.- t))

  *ᶻ-distribˡ : ∀ x y z → (x +ᶻ y) *ᶻ z ≡ (x *ᶻ z) +ᶻ (y *ᶻ z)
  *ᶻ-distribˡ (a +z b +z c +z d) (a' +z b' +z c' +z d') (u +z v +z w +z s) =
    zext real i compg iγ
    where
      m3 = (+ 3 / 1)
      real : (((a + a') * u - (b + b') * v) + m3 * ((d + d') * s - (c + c') * w))
             ≡ (((a * u - b * v) + m3 * (d * s - c * w))
                + ((a' * u - b' * v) + m3 * (d' * s - c' * w)))
      real =
        trans (cong₂ _+_
          (trans (cong₂ _-_ (*-distribʳ-+ u a a') (*-distribʳ-+ v b b'))
                 (minus-shuffle (a * u) (a' * u) (b * v) (b' * v)))
          (trans (cong (\x → m3 * x)
                   (trans (cong₂ _-_ (*-distribʳ-+ s d d') (*-distribʳ-+ w c c'))
                          (minus-shuffle (d * s) (d' * s) (c * w) (c' * w))))
                 (*-distribˡ-+ m3 (d * s - c * w) (d' * s - c' * w))))
        (pair-shuffle (a * u - b * v) (a' * u - b' * v)
                      (m3 * (d * s - c * w)) (m3 * (d' * s - c' * w)))
      -- 子步骤分离 (≤3 层 trans): 先展开+重排, 再保持减号结构
      i-step1 : (a + a') * v + (b + b') * u ≡ (a * v + b * u) + (a' * v + b' * u)
      i-step1 = trans (cong₂ _+_ (*-distribʳ-+ v a a') (*-distribʳ-+ u b b'))
                      (pair-shuffle (a * v) (a' * v) (b * u) (b' * u))

      i-step2 : m3 * ((c + c') * s + (d + d') * w)
                ≡ m3 * (c * s + d * w) + m3 * (c' * s + d' * w)
      i-step2 = trans (cong (\x → m3 * x)
                       (trans (cong₂ _+_ (*-distribʳ-+ s c c') (*-distribʳ-+ w d d'))
                              (pair-shuffle (c * s) (c' * s) (d * w) (d' * w))))
                      (*-distribˡ-+ m3 (c * s + d * w) (c' * s + d' * w))

      i : (((a + a') * v + (b + b') * u) - m3 * ((c + c') * s + (d + d') * w))
          ≡ (((a * v + b * u) - m3 * (c * s + d * w))
             + ((a' * v + b' * u) - m3 * (c' * s + d' * w)))
      i = trans (cong (\x → (a + a') * v + (b + b') * u - x) i-step2)
          (trans (cong (\y → y - (m3 * (c * s + d * w) + m3 * (c' * s + d' * w))) i-step1)
                 (minus-shuffle (a * v + b * u) (a' * v + b' * u)
                                (m3 * (c * s + d * w)) (m3 * (c' * s + d' * w))))

      compg-step1 : (a + a') * w + (c + c') * u ≡ (a * w + c * u) + (a' * w + c' * u)
      compg-step1 = trans (cong₂ _+_ (*-distribʳ-+ w a a') (*-distribʳ-+ u c c'))
                          (pair-shuffle (a * w) (a' * w) (c * u) (c' * u))

      compg-step2 : (b + b') * s + (d + d') * v ≡ (b * s + d * v) + (b' * s + d' * v)
      compg-step2 = trans (cong₂ _+_ (*-distribʳ-+ s b b') (*-distribʳ-+ v d d'))
                          (pair-shuffle (b * s) (b' * s) (d * v) (d' * v))

      compg : (((a + a') * w + (c + c') * u) - ((b + b') * s + (d + d') * v))
              ≡ (((a * w + c * u) - (b * s + d * v))
                 + ((a' * w + c' * u) - (b' * s + d' * v)))
      compg = trans (cong (\x → (a + a') * w + (c + c') * u - x) compg-step2)
          (trans (cong (\y → y - ((b * s + d * v) + (b' * s + d' * v))) compg-step1)
                 (minus-shuffle (a * w + c * u) (a' * w + c' * u)
                                (b * s + d * v) (b' * s + d' * v)))

      iγ : (((a + a') * s + (d + d') * u) + ((b + b') * w + (c + c') * v))
           ≡ (((a * s + d * u) + (b * w + c * v))
              + ((a' * s + d' * u) + (b' * w + c' * v)))
      iγ =
        trans (cong₂ _+_
          (trans (cong₂ _+_ (*-distribʳ-+ s a a') (*-distribʳ-+ u d d'))
                 (pair-shuffle (a * s) (a' * s) (d * u) (d' * u)))
          (trans (cong₂ _+_ (*-distribʳ-+ w b b') (*-distribʳ-+ v c c'))
                 (pair-shuffle (b * w) (b' * w) (c * v) (c' * v))))
        (pair-shuffle (a * s + d * u) (a' * s + d' * u)
                      (b * w + c * v) (b' * w + c' * v))

  *ᶻ-distribʳ : ∀ x y z → z *ᶻ (x +ᶻ y) ≡ (z *ᶻ x) +ᶻ (z *ᶻ y)
  *ᶻ-distribʳ x y z =
    trans (*ᶻ-comm z (x +ᶻ y))
      (trans (*ᶻ-distribˡ x y z)
             (cong₂ (λ r t → r +ᶻ t) (*ᶻ-comm x z) (*ᶻ-comm y z)))

  -- ── 共轭引理族 (conjᶻ 与 +ᶻ/*ᶻ 交换; Parseval 组装必需) ──

  -- ℚ 双重取负 (Properties 无 ℚ 版; -_ 是构造子级符号翻转, 3-case refl)
  neg-involutive-ℚ : ∀ p → - (- p) ≡ p
  neg-involutive-ℚ (mkℚ +[1+ n ] d _) = refl
  neg-involutive-ℚ (mkℚ +0 d _) = refl
  neg-involutive-ℚ (mkℚ -[1+ n ] d _) = refl

  -- (−p)(−q) = pq
  negneg-mul : ∀ p q → (- p) * (- q) ≡ p * q
  negneg-mul p q =
    trans (sym (neg-distribˡ-* p (- q)))
      (trans (cong Data.Rational.-_ (sym (neg-distribʳ-* p q)))
             (neg-involutive-ℚ (p * q)))

  -- p − (−q) = p + q
  p-minus-minus : ∀ p q → p - (- q) ≡ p + q
  p-minus-minus p q = cong (\w → p + w) (neg-involutive-ℚ q)

  -- −(X − Y) = (−X) + Y
  neg-minus : ∀ X Y → - (X - Y) ≡ (- X) + Y
  neg-minus X Y =
    trans (neg-distrib-+ X (- Y))
          (cong (\w → (- X) + w) (neg-involutive-ℚ Y))

  conj-+ᶻ : ∀ x y → conjᶻ (x +ᶻ y) ≡ conjᶻ x +ᶻ conjᶻ y
  conj-+ᶻ (a +z b +z c +z d) (a' +z b' +z c' +z d') =
    zext refl (neg-distrib-+ b b') (neg-distrib-+ c c') refl

  conj-involutive : ∀ x → conjᶻ (conjᶻ x) ≡ x
  conj-involutive (a +z b +z c +z d) =
    zext refl (neg-involutive-ℚ b) (neg-involutive-ℚ c) refl

  -- conj 与 *ᶻ 交换: 两侧各归约到规范形再组合 (每分量独立命名引理)
  conj-real : ∀ a a' b b' c c' d d' →
    ((a * a' - b * b') + (+ 3 / 1) * (d * d' - c * c'))
    ≡ ((a * a' - (- b) * (- b')) + (+ 3 / 1) * (d * d' - (- c) * (- c')))
  conj-real a a' b b' c c' d d' =
    cong₂ _+_
      (sym (cong (\w → a * a' - w) (negneg-mul b b')))
      (sym (cong (\w → (+ 3 / 1) * (d * d' - w)) (negneg-mul c c')))

  conj-i-L : ∀ a b a' b' c d c' d' →
    - (((a * b') + (b * a')) - (+ 3 / 1) * ((c * d') + (d * c')))
    ≡ ((- (a * b')) + (- (b * a'))) + (+ 3 / 1) * ((c * d') + (d * c'))
  conj-i-L a b a' b' c d c' d' =
    trans (neg-minus ((a * b') + (b * a')) ((+ 3 / 1) * ((c * d') + (d * c'))))
          (cong (\w → w + (+ 3 / 1) * ((c * d') + (d * c')))
                (neg-distrib-+ (a * b') (b * a')))

  conj-i-R-sub : ∀ c d c' d' →
    (+ 3 / 1) * (((- c) * d') + d * (- c'))
    ≡ - ((+ 3 / 1) * ((c * d') + (d * c')))
  conj-i-R-sub c d c' d' =
    trans (cong (\x → (+ 3 / 1) * x) inner)
          (sym (neg-distribʳ-* (+ 3 / 1) ((c * d') + (d * c'))))
    where
      inner : ((- c) * d') + d * (- c') ≡ (- ((c * d') + (d * c')))
      inner =
        trans (cong₂ _+_ (sym (neg-distribˡ-* c d')) (sym (neg-distribʳ-* d c')))
              (sym (neg-distrib-+ (c * d') (d * c')))

  conj-i-R : ∀ a b a' b' c d c' d' →
    ((a * (- b') + (- b) * a')
     - (+ 3 / 1) * (((- c) * d') + d * (- c')))
    ≡ ((- (a * b')) + (- (b * a'))) + (+ 3 / 1) * ((c * d') + (d * c'))
  conj-i-R a b a' b' c d c' d' =
    trans (cong (\w → (a * (- b') + (- b) * a') - w)
                (conj-i-R-sub c d c' d'))
    (trans (p-minus-minus (a * (- b') + (- b) * a')
                          ((+ 3 / 1) * ((c * d') + (d * c'))))
           (cong (\w → w + (+ 3 / 1) * ((c * d') + (d * c')))
                 (cong₂ _+_ (sym (neg-distribʳ-* a b')) (sym (neg-distribˡ-* b a')))))

  conj-i : ∀ a b a' b' c d c' d' →
    - (((a * b') + (b * a')) - (+ 3 / 1) * ((c * d') + (d * c')))
    ≡ ((a * (- b') + (- b) * a')
       - (+ 3 / 1) * (((- c) * d') + d * (- c')))
  conj-i a b a' b' c d c' d' =
    trans (conj-i-L a b a' b' c d c' d') (sym (conj-i-R a b a' b' c d c' d'))

  conj-γ-L : ∀ a c a' c' b d b' d' →
    - (((a * c') + (c * a')) - ((b * d') + (d * b')))
    ≡ ((- (a * c')) + (- (c * a'))) + ((b * d') + (d * b'))
  conj-γ-L a c a' c' b d b' d' =
    trans (neg-minus ((a * c') + (c * a')) ((b * d') + (d * b')))
          (cong (\w → w + ((b * d') + (d * b')))
                (neg-distrib-+ (a * c') (c * a')))

  conj-γ-R : ∀ a c a' c' b d b' d' →
    ((a * (- c') + (- c) * a')
     - (((- b) * d') + d * (- b')))
    ≡ ((- (a * c')) + (- (c * a'))) + ((b * d') + (d * b'))
  conj-γ-R a c a' c' b d b' d' =
    trans (cong (\w → (a * (- c') + (- c) * a') - w)
                (conj-γ-R-sub b d b' d'))
    (trans (p-minus-minus (a * (- c') + (- c) * a') ((b * d') + (d * b')))
           (cong (\w → w + ((b * d') + (d * b')))
                 (cong₂ _+_ (sym (neg-distribʳ-* a c')) (sym (neg-distribˡ-* c a')))))
    where
      conj-γ-R-sub : ∀ b d b' d' →
        ((- b) * d') + d * (- b') ≡ - ((b * d') + (d * b'))
      conj-γ-R-sub b d b' d' =
        trans (cong₂ _+_ (sym (neg-distribˡ-* b d')) (sym (neg-distribʳ-* d b')))
              (sym (neg-distrib-+ (b * d') (d * b')))

  conj-γ : ∀ a c a' c' b d b' d' →
    - (((a * c') + (c * a')) - ((b * d') + (d * b')))
    ≡ ((a * (- c') + (- c) * a') - (((- b) * d') + d * (- b')))
  conj-γ a c a' c' b d b' d' =
    trans (conj-γ-L a c a' c' b d b' d') (sym (conj-γ-R a c a' c' b d b' d'))

  conj-iγ : ∀ a d a' d' b c b' c' →
    ((a * d') + (d * a')) + ((b * c') + (c * b'))
    ≡ ((a * d') + (d * a')) + (((- b) * (- c')) + ((- c) * (- b')))
  conj-iγ a d a' d' b c b' c' =
    cong (\w → ((a * d') + (d * a')) + w)
         (cong₂ _+_ (sym (negneg-mul b c')) (sym (negneg-mul c b')))

  conj-*ᶻ : ∀ x y → conjᶻ (x *ᶻ y) ≡ conjᶻ x *ᶻ conjᶻ y
  conj-*ᶻ (a +z b +z c +z d) (a' +z b' +z c' +z d') =
    zext (conj-real a a' b b' c c' d d')
         (conj-i a b a' b' c d c' d')
         (conj-γ a c a' c' b d b' d')
         (conj-iγ a d a' d' b c b' c')

  -- 零元族 (求和结构引理地基; ℚ +-identity 分量直推)
  zidˡ : ∀ x → z0 +ᶻ x ≡ x
  zidˡ (a +z b +z c +z d) =
    zext (+-identityˡ a) (+-identityˡ b) (+-identityˡ c) (+-identityˡ d)

  zidʳ : ∀ x → x +ᶻ z0 ≡ x
  zidʳ (a +z b +z c +z d) =
    zext (+-identityʳ a) (+-identityʳ b) (+-identityʳ c) (+-identityʳ d)

  -- 归纳: 全零函数的和为零 (基步 refl, 归纳步 zidˡ)
  sumF-zero : ∀ {n : ℕ} → sumF (λ (_ : Fin n) → z0) ≡ z0
  sumF-zero {zero} = refl
  sumF-zero {suc n} = trans (zidˡ (sumF (λ (_ : Fin n) → z0))) (sumF-zero {n})

  -- ℚ 常数归零小引理 (0±0=0, 3*0=0; 具体字面 refl)
  q0m : (+ 0 / 1) - (+ 0 / 1) ≡ (+ 0 / 1)
  q0m = refl
  q0p : (+ 0 / 1) + (+ 0 / 1) ≡ (+ 0 / 1)
  q0p = refl
  q·0s : ∀ p q → p ≡ (+ 0 / 1) → q ≡ (+ 0 / 1) → p - q ≡ (+ 0 / 1)
  q·0s p q ep eq = trans (cong₂ _-_ ep eq) q0m
  q·0p : ∀ p q → p ≡ (+ 0 / 1) → q ≡ (+ 0 / 1) → p + q ≡ (+ 0 / 1)
  q·0p p q ep eq = trans (cong₂ _+_ ep eq) q0p
  q·0z : ∀ X → X ≡ (+ 0 / 1) → (+ 3 / 1) * X ≡ (+ 0 / 1)
  q·0z X eX = trans (cong ((+ 3 / 1) *_) eX) (*-zeroʳ (+ 3 / 1))

  -- 右零元: x *ᶻ z0 = z0 (各分量归零; 用 a*0=0 使符号系数归常数)
  *ᶻ-zeroʳ : ∀ x → x *ᶻ z0 ≡ z0
  *ᶻ-zeroʳ (a +z b +z c +z d) = zext real i compg iγ
    where
      p·0 : ∀ p → p * (+ 0 / 1) ≡ (+ 0 / 1)
      p·0 p = *-zeroʳ p
      real : ((a * (+ 0 / 1)) - (b * (+ 0 / 1)))
             + ((+ 3 / 1) * ((d * (+ 0 / 1)) - (c * (+ 0 / 1))))
             ≡ (+ 0 / 1)
      real = q·0p ((a * (+ 0 / 1)) - (b * (+ 0 / 1)))
                  ((+ 3 / 1) * ((d * (+ 0 / 1)) - (c * (+ 0 / 1))))
                  (q·0s (a * (+ 0 / 1)) (b * (+ 0 / 1)) (p·0 a) (p·0 b))
                  (q·0z ((d * (+ 0 / 1)) - (c * (+ 0 / 1)))
                        (q·0s (d * (+ 0 / 1)) (c * (+ 0 / 1)) (p·0 d) (p·0 c)))
      i : ((a * (+ 0 / 1)) + (b * (+ 0 / 1)))
          - ((+ 3 / 1) * ((c * (+ 0 / 1)) + (d * (+ 0 / 1))))
          ≡ (+ 0 / 1)
      i = q·0s ((a * (+ 0 / 1)) + (b * (+ 0 / 1)))
               ((+ 3 / 1) * ((c * (+ 0 / 1)) + (d * (+ 0 / 1))))
               (q·0p (a * (+ 0 / 1)) (b * (+ 0 / 1)) (p·0 a) (p·0 b))
               (q·0z ((c * (+ 0 / 1)) + (d * (+ 0 / 1)))
                     (q·0p (c * (+ 0 / 1)) (d * (+ 0 / 1)) (p·0 c) (p·0 d)))
      compg : ((a * (+ 0 / 1)) + (c * (+ 0 / 1)))
              - ((b * (+ 0 / 1)) + (d * (+ 0 / 1)))
              ≡ (+ 0 / 1)
      compg = q·0s ((a * (+ 0 / 1)) + (c * (+ 0 / 1)))
                   ((b * (+ 0 / 1)) + (d * (+ 0 / 1)))
                   (q·0p (a * (+ 0 / 1)) (c * (+ 0 / 1)) (p·0 a) (p·0 c))
                   (q·0p (b * (+ 0 / 1)) (d * (+ 0 / 1)) (p·0 b) (p·0 d))
      iγ : ((a * (+ 0 / 1)) + (d * (+ 0 / 1)))
           + ((b * (+ 0 / 1)) + (c * (+ 0 / 1)))
           ≡ (+ 0 / 1)
      iγ = q·0p ((a * (+ 0 / 1)) + (d * (+ 0 / 1)))
                ((b * (+ 0 / 1)) + (c * (+ 0 / 1)))
                (q·0p (a * (+ 0 / 1)) (d * (+ 0 / 1)) (p·0 a) (p·0 d))
                (q·0p (b * (+ 0 / 1)) (c * (+ 0 / 1)) (p·0 b) (p·0 c))

  -- 左因子穿过归纳求和 (结构归纳: 基步 *ᶻ-zeroʳ, 归纳步 *ᶻ-distribʳ + 递归)
  sumF-mull : ∀ {n : ℕ} (A : Z12Sys) (f : Fin n → Z12Sys) →
    A *ᶻ sumF f ≡ sumF (λ i → A *ᶻ f i)
  sumF-mull {zero} A f = *ᶻ-zeroʳ A
  sumF-mull {suc n} A f =
    trans (*ᶻ-distribʳ (f fzero) (sumF (λ i → f (fsuc i))) A)
          (cong (λ w → (A *ᶻ f fzero) +ᶻ w) (sumF-mull A (λ i → f (fsuc i))))

  -- 共轭穿过归纳求和 (基步 conjᶻ z0 = z0 refl, 归纳步 conj-+ᶻ + 递归)
  conj-sumF : ∀ {n : ℕ} (f : Fin n → Z12Sys) →
    conjᶻ (sumF f) ≡ sumF (λ i → conjᶻ (f i))
  conj-sumF {zero} f = refl
  conj-sumF {suc n} f =
    trans (conj-+ᶻ (f fzero) (sumF (λ i → f (fsuc i))))
          (cong (λ w → conjᶻ (f fzero) +ᶻ w) (conj-sumF (λ i → f (fsuc i))))

  -- ── 减法分配工具箱 (*ᶻ-assoc 各分量展开的基础, 隔离验证通过) ──

  -- ℚ 减法与加负号定义性一致 (p - q = p + (-q))
  q-minus-def : ∀ p q → p - q ≡ p + (Data.Rational.- q)
  q-minus-def p q = refl

  -- (p - q) * r ≡ (p*r) - (q*r)    右分配对减法
  mul-sub-r : ∀ p q r → (p - q) * r ≡ (p * r) - (q * r)
  mul-sub-r p q r = begin
    (p - q) * r              ≡⟨⟩
    (p + (- q)) * r          ≡⟨ *-distribʳ-+ r p (- q) ⟩
    p * r + ((- q) * r)      ≡⟨ cong (λ w → p * r + w) (sym (neg-distribˡ-* q r)) ⟩
    p * r + (- (q * r))      ≡⟨⟩
    p * r - (q * r)          ∎
    where open ≡-Reasoning

  -- p * (r - s) ≡ (p*r) - (p*s)    左分配对减法
  mul-sub-l : ∀ p r s → p * (r - s) ≡ (p * r) - (p * s)
  mul-sub-l p r s =
    trans (*-comm p (r - s))                          -- p*(r-s) ≡ (r-s)*p
          (trans (mul-sub-r r s p)
                 (cong₂ _-_ (*-comm r p) (*-comm s p)))

  mul-add-r : ∀ p q r → (p + q) * r ≡ (p * r) + (q * r)
  mul-add-r p q r = *-distribʳ-+ r p q

  mul-add-l : ∀ p r s → p * (r + s) ≡ (p * r) + (p * s)
  mul-add-l p r s =
    trans (*-comm p (r + s))
          (trans (mul-add-r r s p)
                 (cong₂ _+_ (*-comm r p) (*-comm s p)))

  -- 4 项加法重排: (x1+x2)+(x3+x4) ≡ (x1+x3)+(x2+x4)
  add4-swap : ∀ x1 x2 x3 x4 → (x1 + x2) + (x3 + x4) ≡ (x1 + x3) + (x2 + x4)
  add4-swap x1 x2 x3 x4 = begin
    (x1 + x2) + (x3 + x4)   ≡⟨ +-assoc x1 x2 (x3 + x4) ⟩
    x1 + (x2 + (x3 + x4))   ≡⟨ cong (λ w → x1 + w) (sym (+-assoc x2 x3 x4)) ⟩
    x1 + ((x2 + x3) + x4)   ≡⟨ cong (λ w → x1 + (w + x4)) (+-comm x2 x3) ⟩
    x1 + ((x3 + x2) + x4)   ≡⟨ cong (λ w → x1 + w) (+-assoc x3 x2 x4) ⟩
    x1 + (x3 + (x2 + x4))   ≡⟨ sym (+-assoc x1 x3 (x2 + x4)) ⟩
    (x1 + x3) + (x2 + x4)   ∎ where open ≡-Reasoning


  -- ── Gaussian ℚ[i] 结合律 (Z12Sys = ℚ[i]⊗ℚ[γ] 分层基块; 草稿验证后移植) ──

  gm-real : ∀ a b c d e f →
    ((a * c - b * d) * e) - ((a * d + b * c) * f)
    ≡ (a * (c * e - d * f)) - (b * (c * f + d * e))
  gm-real a b c d e f = begin
    ((a * c - b * d) * e) - ((a * d + b * c) * f)
      ≡⟨ cong₂ _-_ (mul-sub-r (a * c) (b * d) e) (mul-add-r (a * d) (b * c) f) ⟩
    ((a * c) * e - (b * d) * e) - ((a * d) * f + (b * c) * f)
      ≡⟨ cong₂ _-_
           (cong₂ _-_ (*-assoc a c e) (*-assoc b d e))
           (cong₂ _+_ (*-assoc a d f) (*-assoc b c f)) ⟩
    (a * (c * e) - b * (d * e)) - (a * (d * f) + b * (c * f))
      ≡⟨ cong (λ w → (a * (c * e) + (- (b * (d * e)))) + w)
             (neg-distrib-+ (a * (d * f)) (b * (c * f))) ⟩
    (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + (- (b * (c * f))))
      ≡⟨ add4-swap (a * (c * e)) (- (b * (d * e))) (- (a * (d * f))) (- (b * (c * f))) ⟩
    (a * (c * e) + (- (a * (d * f)))) + ((- (b * (d * e))) + (- (b * (c * f))))
      ≡⟨ cong (λ w → (a * (c * e) + (- (a * (d * f)))) + w)
             (+-comm (- (b * (d * e))) (- (b * (c * f)))) ⟩
    (a * (c * e) + (- (a * (d * f)))) + ((- (b * (c * f))) + (- (b * (d * e))))
      ≡⟨ cong (λ w → (a * (c * e)) + (- (a * (d * f))) + w)
             (sym (neg-distrib-+ (b * (c * f)) (b * (d * e)))) ⟩
    (a * (c * e) + (- (a * (d * f)))) + (- ((b * (c * f)) + (b * (d * e))))
      ≡⟨ cong (λ w → (a * (c * e) + (- (a * (d * f)))) + (- w))
             (sym (mul-add-l b (c * f) (d * e))) ⟩
    (a * (c * e) + (- (a * (d * f)))) + (- (b * (c * f + d * e)))
      ≡⟨⟩
    ((a * (c * e)) - (a * (d * f))) - (b * (c * f + d * e))
      ≡⟨ cong₂ _-_ (sym (mul-sub-l a (c * e) (d * f))) refl ⟩
    (a * (c * e - d * f)) - (b * (c * f + d * e))
    ∎ where open ≡-Reasoning

  gm-imag : ∀ a b c d e f →
    ((a * d + b * c) * e) + ((a * c - b * d) * f)
    ≡ (a * (d * e + c * f)) + (b * (c * e - d * f))
  gm-imag a b c d e f = begin
    ((a * d + b * c) * e) + ((a * c - b * d) * f)
      ≡⟨ cong₂ _+_ (mul-add-r (a * d) (b * c) e) (mul-sub-r (a * c) (b * d) f) ⟩
    ((a * d) * e + (b * c) * e) + ((a * c) * f - (b * d) * f)
      ≡⟨ cong₂ _+_
           (cong₂ _+_ (*-assoc a d e) (*-assoc b c e))
           (cong₂ _-_ (*-assoc a c f) (*-assoc b d f)) ⟩
    (a * (d * e) + b * (c * e)) + (a * (c * f) - b * (d * f))
      ≡⟨⟩
    (a * (d * e) + b * (c * e)) + (a * (c * f) + (- (b * (d * f))))
      ≡⟨ add4-swap (a * (d * e)) (b * (c * e)) (a * (c * f)) (- (b * (d * f))) ⟩
    (a * (d * e) + a * (c * f)) + (b * (c * e) + (- (b * (d * f))))
      ≡⟨ cong₂ _+_
           (sym (mul-add-l a (d * e) (c * f)))
           (sym (mul-sub-l b (c * e) (d * f))) ⟩
    a * ((d * e) + (c * f)) + b * ((c * e) - (d * f))
      ≡⟨⟩
    (a * (d * e + c * f)) + (b * (c * e - d * f))
    ∎ where open ≡-Reasoning


  -- 同值函数求和相等 (点等 → 和等; 归纳: cong₂ _+ᶻ_)
  sumF-ext : ∀ {n : ℕ} {f g : Fin n → Z12Sys} → (∀ i → f i ≡ g i) → sumF f ≡ sumF g
  sumF-ext {zero} {f} {g} h = refl
  sumF-ext {suc n} {f} {g} h =
    cong₂ (λ u v → u +ᶻ v) (h fzero) (sumF-ext {n} (λ i → h (fsuc i)))

  -- 四项重排: (x+ᶻy)+ᶻ(z+ᶻw) ≡ (x+ᶻz)+ᶻ(y+ᶻw) (分量 ℚ pair-shuffle)
  +ᶻ-shuffle4 : ∀ x y z w → (x +ᶻ y) +ᶻ (z +ᶻ w) ≡ (x +ᶻ z) +ᶻ (y +ᶻ w)
  +ᶻ-shuffle4 (a +z b +z c +z d) (a' +z b' +z c' +z d')
               (a'' +z b'' +z c'' +z d'') (a''' +z b''' +z c''' +z d''') =
    zext (pair-shuffle a a' a'' a''')
         (pair-shuffle b b' b'' b''')
         (pair-shuffle c c' c'' c''')
         (pair-shuffle d d' d'' d''')

  -- 加法线性: Σ(a+ᶻb) ≡ (Σa)+ᶻ(Σb) (基步 sym zid, 归纳步 shuffle4)
  sumF-+ : ∀ {n : ℕ} (a b : Fin n → Z12Sys) →
    sumF (λ j → a j +ᶻ b j) ≡ sumF a +ᶻ sumF b
  sumF-+ {zero} a b = sym (zidˡ z0)
  sumF-+ {suc n} a b =
    trans (cong (λ w → (a fzero +ᶻ b fzero) +ᶻ w)
                (sumF-+ {n} (λ j → a (fsuc j)) (λ j → b (fsuc j))))
          (+ᶻ-shuffle4 (a fzero) (b fzero)
                       (sumF (λ j → a (fsuc j))) (sumF (λ j → b (fsuc j))))

  -- 双和交换: Σ_i Σ_j g i j ≡ Σ_j Σ_i g i j (归纳; 配 sumF-+/sumF-comm2 递归)
  sumF-comm2 : ∀ {m n : ℕ} (g : Fin m → Fin n → Z12Sys) →
    sumF (λ i → sumF (λ j → g i j)) ≡ sumF (λ j → sumF (λ i → g i j))
  sumF-comm2 {zero} {n} g = sym (sumF-zero {n})
  sumF-comm2 {suc m} {n} g =
    trans (cong (λ w → sumF (λ j → g fzero j) +ᶻ w)
                (sumF-comm2 {m} (λ i j → g (fsuc i) j)))
          (sym (sumF-+ (λ j → g fzero j) (λ j → sumF (λ i → g (fsuc i) j))))

  -- ── real 分量组装的 4 个积木块 (*ᶻ-assoc real 用; 各块独立验证) ──

  rblock : ∀ a b c d a₂ b₂ c₂ d₂ u →
    (((a * a₂ - b * b₂) + ((+ 3 / 1) * ((d * d₂) - (c * c₂)))) * u)
    ≡ ((a * a₂ * u - b * b₂ * u)
       + (((+ 3 / 1) * (d * d₂ * u)) - ((+ 3 / 1) * (c * c₂ * u))))
  rblock a b c d a₂ b₂ c₂ d₂ u = begin
    (((a * a₂ - b * b₂) + ((+ 3 / 1) * ((d * d₂) - (c * c₂)))) * u)
      ≡⟨ mul-add-r (a * a₂ - b * b₂) ((+ 3 / 1) * ((d * d₂) - (c * c₂))) u ⟩
    ((a * a₂ - b * b₂) * u) + (((+ 3 / 1) * ((d * d₂) - (c * c₂))) * u)
      ≡⟨ cong₂ _+_ (mul-sub-r (a * a₂) (b * b₂) u)
           (*-assoc (+ 3 / 1) ((d * d₂) - (c * c₂)) u) ⟩
    ((a * a₂ * u) - (b * b₂ * u)) + ((+ 3 / 1) * (((d * d₂) - (c * c₂)) * u))
      ≡⟨ cong (λ w → ((a * a₂ * u) - (b * b₂ * u)) + ((+ 3 / 1) * w))
           (mul-sub-r (d * d₂) (c * c₂) u) ⟩
    ((a * a₂ * u) - (b * b₂ * u)) + ((+ 3 / 1) * ((d * d₂ * u) - (c * c₂ * u)))
      ≡⟨ cong (λ w → ((a * a₂ * u) - (b * b₂ * u)) + w)
           (mul-sub-l (+ 3 / 1) (d * d₂ * u) (c * c₂ * u)) ⟩
    ((a * a₂ * u) - (b * b₂ * u))
      + (((+ 3 / 1) * (d * d₂ * u)) - ((+ 3 / 1) * (c * c₂ * u)))
    ∎ where open ≡-Reasoning

  iblk : ∀ a b a₂ b₂ c d c₂ d₂ v →
    (((a * b₂ + b * a₂) - ((+ 3 / 1) * ((c * d₂) + (d * c₂)))) * v)
    ≡ ((a * b₂ * v + b * a₂ * v)
       - (((+ 3 / 1) * (c * d₂ * v)) + ((+ 3 / 1) * (d * c₂ * v))))
  iblk a b a₂ b₂ c d c₂ d₂ v = begin
    (((a * b₂ + b * a₂) - ((+ 3 / 1) * ((c * d₂) + (d * c₂)))) * v)
      ≡⟨ mul-sub-r (a * b₂ + b * a₂) ((+ 3 / 1) * ((c * d₂) + (d * c₂))) v ⟩
    ((a * b₂ + b * a₂) * v) - (((+ 3 / 1) * ((c * d₂) + (d * c₂))) * v)
      ≡⟨ cong₂ _-_ (mul-add-r (a * b₂) (b * a₂) v)
           (*-assoc (+ 3 / 1) ((c * d₂) + (d * c₂)) v) ⟩
    ((a * b₂ * v + b * a₂ * v)) - ((+ 3 / 1) * (((c * d₂) + (d * c₂)) * v))
      ≡⟨ cong (λ w → ((a * b₂ * v + b * a₂ * v)) - ((+ 3 / 1) * w))
           (mul-add-r (c * d₂) (d * c₂) v) ⟩
    ((a * b₂ * v + b * a₂ * v)) - ((+ 3 / 1) * ((c * d₂ * v) + (d * c₂ * v)))
      ≡⟨ cong (λ w → ((a * b₂ * v + b * a₂ * v)) - w)
           (mul-add-l (+ 3 / 1) (c * d₂ * v) (d * c₂ * v)) ⟩
    ((a * b₂ * v + b * a₂ * v))
      - (((+ 3 / 1) * (c * d₂ * v)) + ((+ 3 / 1) * (d * c₂ * v)))
    ∎ where open ≡-Reasoning

  hblk : ∀ a d a₂ d₂ b c b₂ c₂ s →
    (((a * d₂ + d * a₂) + (b * c₂ + c * b₂)) * s)
    ≡ ((a * d₂ * s + d * a₂ * s) + (b * c₂ * s + c * b₂ * s))
  hblk a d a₂ d₂ b c b₂ c₂ s = begin
    (((a * d₂ + d * a₂) + (b * c₂ + c * b₂)) * s)
      ≡⟨ mul-add-r (a * d₂ + d * a₂) (b * c₂ + c * b₂) s ⟩
    ((a * d₂ + d * a₂) * s) + ((b * c₂ + c * b₂) * s)
      ≡⟨ cong₂ _+_ (mul-add-r (a * d₂) (d * a₂) s) (mul-add-r (b * c₂) (c * b₂) s) ⟩
    ((a * d₂ * s + d * a₂ * s)) + ((b * c₂ * s + c * b₂ * s))
    ∎ where open ≡-Reasoning

  gblk : ∀ a c a₂ c₂ b d b₂ d₂ w →
    (((a * c₂ + c * a₂) - (b * d₂ + d * b₂)) * w)
    ≡ ((a * c₂ * w + c * a₂ * w) - (b * d₂ * w + d * b₂ * w))
  gblk a c a₂ c₂ b d b₂ d₂ w = begin
    (((a * c₂ + c * a₂) - (b * d₂ + d * b₂)) * w)
      ≡⟨ mul-sub-r (a * c₂ + c * a₂) (b * d₂ + d * b₂) w ⟩
    ((a * c₂ + c * a₂) * w) - ((b * d₂ + d * b₂) * w)
      ≡⟨ cong₂ _-_ (mul-add-r (a * c₂) (c * a₂) w) (mul-add-r (b * d₂) (d * b₂) w) ⟩
    ((a * c₂ * w + c * a₂ * w)) - ((b * d₂ * w + d * b₂ * w))
    ∎ where open ≡-Reasoning


dual-self : ∀ (t : Trit) (a : AlphaPower) →
  sum-over-characters (λ idx → dc-character idx (t , a) *ᶻ conjᶻ (dc-character idx (t , a)))
  ≡ ((+ 12 / 1) +z (+ 0 / 1) +z (+ 0 / 1) +z (+ 0 / 1))
dual-self T₀ a0 = refl
dual-self T₀ a1 = refl
dual-self T₀ a2 = refl
dual-self T₀ a3 = refl
dual-self T₁ a0 = refl
dual-self T₁ a1 = refl
dual-self T₁ a2 = refl
dual-self T₁ a3 = refl
dual-self T₂ a0 = refl
dual-self T₂ a1 = refl
dual-self T₂ a2 = refl
dual-self T₂ a3 = refl

dual-orthogonality : ∀ (t : Trit) (a : AlphaPower) (t' : Trit) (a' : AlphaPower) →
  (t ≢ t' ⊎ a ≢ a') →
  sum-over-characters (λ idx → dc-character idx (t , a) *ᶻ conjᶻ (dc-character idx (t' , a')))
  ≡ z0
dual-orthogonality T₀ a0 T₀ a0 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a0 T₀ a0 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a0 T₀ a1 neq = refl
dual-orthogonality T₀ a0 T₀ a2 neq = refl
dual-orthogonality T₀ a0 T₀ a3 neq = refl
dual-orthogonality T₀ a0 T₁ a0 neq = refl
dual-orthogonality T₀ a0 T₁ a1 neq = refl
dual-orthogonality T₀ a0 T₁ a2 neq = refl
dual-orthogonality T₀ a0 T₁ a3 neq = refl
dual-orthogonality T₀ a0 T₂ a0 neq = refl
dual-orthogonality T₀ a0 T₂ a1 neq = refl
dual-orthogonality T₀ a0 T₂ a2 neq = refl
dual-orthogonality T₀ a0 T₂ a3 neq = refl
dual-orthogonality T₀ a1 T₀ a0 neq = refl
dual-orthogonality T₀ a1 T₀ a1 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a1 T₀ a1 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a1 T₀ a2 neq = refl
dual-orthogonality T₀ a1 T₀ a3 neq = refl
dual-orthogonality T₀ a1 T₁ a0 neq = refl
dual-orthogonality T₀ a1 T₁ a1 neq = refl
dual-orthogonality T₀ a1 T₁ a2 neq = refl
dual-orthogonality T₀ a1 T₁ a3 neq = refl
dual-orthogonality T₀ a1 T₂ a0 neq = refl
dual-orthogonality T₀ a1 T₂ a1 neq = refl
dual-orthogonality T₀ a1 T₂ a2 neq = refl
dual-orthogonality T₀ a1 T₂ a3 neq = refl
dual-orthogonality T₀ a2 T₀ a0 neq = refl
dual-orthogonality T₀ a2 T₀ a1 neq = refl
dual-orthogonality T₀ a2 T₀ a2 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a2 T₀ a2 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a2 T₀ a3 neq = refl
dual-orthogonality T₀ a2 T₁ a0 neq = refl
dual-orthogonality T₀ a2 T₁ a1 neq = refl
dual-orthogonality T₀ a2 T₁ a2 neq = refl
dual-orthogonality T₀ a2 T₁ a3 neq = refl
dual-orthogonality T₀ a2 T₂ a0 neq = refl
dual-orthogonality T₀ a2 T₂ a1 neq = refl
dual-orthogonality T₀ a2 T₂ a2 neq = refl
dual-orthogonality T₀ a2 T₂ a3 neq = refl
dual-orthogonality T₀ a3 T₀ a0 neq = refl
dual-orthogonality T₀ a3 T₀ a1 neq = refl
dual-orthogonality T₀ a3 T₀ a2 neq = refl
dual-orthogonality T₀ a3 T₀ a3 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a3 T₀ a3 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₀ a3 T₁ a0 neq = refl
dual-orthogonality T₀ a3 T₁ a1 neq = refl
dual-orthogonality T₀ a3 T₁ a2 neq = refl
dual-orthogonality T₀ a3 T₁ a3 neq = refl
dual-orthogonality T₀ a3 T₂ a0 neq = refl
dual-orthogonality T₀ a3 T₂ a1 neq = refl
dual-orthogonality T₀ a3 T₂ a2 neq = refl
dual-orthogonality T₀ a3 T₂ a3 neq = refl
dual-orthogonality T₁ a0 T₀ a0 neq = refl
dual-orthogonality T₁ a0 T₀ a1 neq = refl
dual-orthogonality T₁ a0 T₀ a2 neq = refl
dual-orthogonality T₁ a0 T₀ a3 neq = refl
dual-orthogonality T₁ a0 T₁ a0 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a0 T₁ a0 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a0 T₁ a1 neq = refl
dual-orthogonality T₁ a0 T₁ a2 neq = refl
dual-orthogonality T₁ a0 T₁ a3 neq = refl
dual-orthogonality T₁ a0 T₂ a0 neq = refl
dual-orthogonality T₁ a0 T₂ a1 neq = refl
dual-orthogonality T₁ a0 T₂ a2 neq = refl
dual-orthogonality T₁ a0 T₂ a3 neq = refl
dual-orthogonality T₁ a1 T₀ a0 neq = refl
dual-orthogonality T₁ a1 T₀ a1 neq = refl
dual-orthogonality T₁ a1 T₀ a2 neq = refl
dual-orthogonality T₁ a1 T₀ a3 neq = refl
dual-orthogonality T₁ a1 T₁ a0 neq = refl
dual-orthogonality T₁ a1 T₁ a1 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a1 T₁ a1 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a1 T₁ a2 neq = refl
dual-orthogonality T₁ a1 T₁ a3 neq = refl
dual-orthogonality T₁ a1 T₂ a0 neq = refl
dual-orthogonality T₁ a1 T₂ a1 neq = refl
dual-orthogonality T₁ a1 T₂ a2 neq = refl
dual-orthogonality T₁ a1 T₂ a3 neq = refl
dual-orthogonality T₁ a2 T₀ a0 neq = refl
dual-orthogonality T₁ a2 T₀ a1 neq = refl
dual-orthogonality T₁ a2 T₀ a2 neq = refl
dual-orthogonality T₁ a2 T₀ a3 neq = refl
dual-orthogonality T₁ a2 T₁ a0 neq = refl
dual-orthogonality T₁ a2 T₁ a1 neq = refl
dual-orthogonality T₁ a2 T₁ a2 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a2 T₁ a2 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a2 T₁ a3 neq = refl
dual-orthogonality T₁ a2 T₂ a0 neq = refl
dual-orthogonality T₁ a2 T₂ a1 neq = refl
dual-orthogonality T₁ a2 T₂ a2 neq = refl
dual-orthogonality T₁ a2 T₂ a3 neq = refl
dual-orthogonality T₁ a3 T₀ a0 neq = refl
dual-orthogonality T₁ a3 T₀ a1 neq = refl
dual-orthogonality T₁ a3 T₀ a2 neq = refl
dual-orthogonality T₁ a3 T₀ a3 neq = refl
dual-orthogonality T₁ a3 T₁ a0 neq = refl
dual-orthogonality T₁ a3 T₁ a1 neq = refl
dual-orthogonality T₁ a3 T₁ a2 neq = refl
dual-orthogonality T₁ a3 T₁ a3 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a3 T₁ a3 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₁ a3 T₂ a0 neq = refl
dual-orthogonality T₁ a3 T₂ a1 neq = refl
dual-orthogonality T₁ a3 T₂ a2 neq = refl
dual-orthogonality T₁ a3 T₂ a3 neq = refl
dual-orthogonality T₂ a0 T₀ a0 neq = refl
dual-orthogonality T₂ a0 T₀ a1 neq = refl
dual-orthogonality T₂ a0 T₀ a2 neq = refl
dual-orthogonality T₂ a0 T₀ a3 neq = refl
dual-orthogonality T₂ a0 T₁ a0 neq = refl
dual-orthogonality T₂ a0 T₁ a1 neq = refl
dual-orthogonality T₂ a0 T₁ a2 neq = refl
dual-orthogonality T₂ a0 T₁ a3 neq = refl
dual-orthogonality T₂ a0 T₂ a0 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a0 T₂ a0 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a0 T₂ a1 neq = refl
dual-orthogonality T₂ a0 T₂ a2 neq = refl
dual-orthogonality T₂ a0 T₂ a3 neq = refl
dual-orthogonality T₂ a1 T₀ a0 neq = refl
dual-orthogonality T₂ a1 T₀ a1 neq = refl
dual-orthogonality T₂ a1 T₀ a2 neq = refl
dual-orthogonality T₂ a1 T₀ a3 neq = refl
dual-orthogonality T₂ a1 T₁ a0 neq = refl
dual-orthogonality T₂ a1 T₁ a1 neq = refl
dual-orthogonality T₂ a1 T₁ a2 neq = refl
dual-orthogonality T₂ a1 T₁ a3 neq = refl
dual-orthogonality T₂ a1 T₂ a0 neq = refl
dual-orthogonality T₂ a1 T₂ a1 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a1 T₂ a1 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a1 T₂ a2 neq = refl
dual-orthogonality T₂ a1 T₂ a3 neq = refl
dual-orthogonality T₂ a2 T₀ a0 neq = refl
dual-orthogonality T₂ a2 T₀ a1 neq = refl
dual-orthogonality T₂ a2 T₀ a2 neq = refl
dual-orthogonality T₂ a2 T₀ a3 neq = refl
dual-orthogonality T₂ a2 T₁ a0 neq = refl
dual-orthogonality T₂ a2 T₁ a1 neq = refl
dual-orthogonality T₂ a2 T₁ a2 neq = refl
dual-orthogonality T₂ a2 T₁ a3 neq = refl
dual-orthogonality T₂ a2 T₂ a0 neq = refl
dual-orthogonality T₂ a2 T₂ a1 neq = refl
dual-orthogonality T₂ a2 T₂ a2 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a2 T₂ a2 (inj₂ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a2 T₂ a3 neq = refl
dual-orthogonality T₂ a3 T₀ a0 neq = refl
dual-orthogonality T₂ a3 T₀ a1 neq = refl
dual-orthogonality T₂ a3 T₀ a2 neq = refl
dual-orthogonality T₂ a3 T₀ a3 neq = refl
dual-orthogonality T₂ a3 T₁ a0 neq = refl
dual-orthogonality T₂ a3 T₁ a1 neq = refl
dual-orthogonality T₂ a3 T₁ a2 neq = refl
dual-orthogonality T₂ a3 T₁ a3 neq = refl
dual-orthogonality T₂ a3 T₂ a0 neq = refl
dual-orthogonality T₂ a3 T₂ a1 neq = refl
dual-orthogonality T₂ a3 T₂ a2 neq = refl
dual-orthogonality T₂ a3 T₂ a3 (inj₁ neq) = ⊥-elim (neq refl)
dual-orthogonality T₂ a3 T₂ a3 (inj₂ neq) = ⊥-elim (neq refl)

--------------------------------------------------------------------------------
-- §7. 【裁定】正交性 / 自内积 / Parseval —— 未形式化, 不留 hole
--
--   正交性与自内积已在 §5′ 完成 (逐索引 refl 穷举: 132+24 与 12 case)。
--   仍余 Parseval: 需要对符号 f 的双重求和交换 + Z12Sys 分配律
--   (ℚ 系数重排), 是下一层任务。草稿的 hole 已按宪法 (0 hole) 删除。
--
--   依赖侧标注: 载体 Z12Sys 与特征同态/反射定理 (§1-§5) 完全本地形式化
--   (ℚ 定点坐标 + DuodecClock 分量运算); §6/§7 的求和框架仅是定义。
--------------------------------------------------------------------------------

-- §8. 总结
--   1. 12 个独立特征, 由 (u,v) ∈ F₃ × C₄ 索引
--   2. 特征是群同态 (dc-character-hom, 1728 case)
--   3. 反射 ρ 把特征映到其复共轭 (rho-character, 144 case)
--   4. 载体验证 ζ₃³=1, i²=-1, conj ζ₃=ζ₃² 全部 refl (§1)
--   5. DC = DuodecPoint (12 元素代数核), 不是无穷的 Doz 数系
