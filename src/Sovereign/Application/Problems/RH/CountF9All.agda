{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.CountF9All
-- F₉ 全称化: GF(9) 上的 18 条 #E（M4 · A4.1）
--
-- 数学背景:
--   GF(9) = GF(3)[α]/(α²+1)（α² = −1；特征 3 下 x²+1 无根，见 WeilRigidity 勘误）。
--   元素 (a,b) := a + bα；乘法 (a,b)(c,d) = (ac − bd, ad + bc)（α² = −1 吸收 bd 项）。
--   与 oracle `f9mul`（(ac+2bd, ad+bc) mod 3）一致：2 ≡ −1 (mod 3)。
--   #E(F₉) = 1 + Σ_{x∈F₉} #{y∈F₉ : y² = rhs(x)}（9×9 全枚举，oracle emit9 冻结，
--   本文件 pe9 表逐字生成于 emit9；`oracle_rh_tables.py check` 对账）。
--   与旧件交叉一致: E₁=c011 ↦ 16、E₂=c021 ↦ 7、E₆=c022 ↦ 7（WeilRigidity 的
--   bsd-identity-E1-9/E2-9/E6-9）。
--
-- 本模块（0 postulate，§1-§4 定义层 + §5 全 refl）:
--   §1 F9 载体（GF(3)[α]/(α²+1)）: f9add / f9mul / t2f9（F₃ 嵌入）
--   §2 相等判定: tritEq / f9eq（Bool 承载, 计数用）
--   §3 枚举: f9at（9 元素, 与 oracle 同序; 越界退化归 (0,0)）
--   §4 计数: b2n / ysq / nsol9 / rhs9 / pointsE9
--   §5 18 条 pe9（非奇异; 逐字生成于 oracle emit9）

module Sovereign.Application.Problems.RH.CountF9All where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Application.Problems.RH.CurveF3

--------------------------------------------------------------------------------
-- §1. F9 载体: GF(3)[α]/(α²+1)
--------------------------------------------------------------------------------

record F9 : Set where
  constructor mkF9
  field
    re im : Trit

-- 加法: (a+bα) + (c+dα) = (a+c) + (b+d)α
f9add : F9 → F9 → F9
f9add (mkF9 a b) (mkF9 c d) = mkF9 (a ⊕ c) (b ⊕ d)

-- 乘法: (a+bα)(c+dα) = (ac − bd) + (ad+bc)α（α² = −1）
f9mul : F9 → F9 → F9
f9mul (mkF9 a b) (mkF9 c d) =
  mkF9 ((a ⊗ c) ⊕ negate (b ⊗ d)) ((a ⊗ d) ⊕ (b ⊗ c))

-- F₃ 嵌入: t ↦ t + 0α
t2f9 : Trit → F9
t2f9 T₀ = mkF9 T₀ T₀
t2f9 T₁ = mkF9 T₁ T₀
t2f9 T₂ = mkF9 T₂ T₀

--------------------------------------------------------------------------------
-- §2. 相等判定（Bool 承载, 计数用; 非命题层）
--------------------------------------------------------------------------------

tritEq : Trit → Trit → Bool
tritEq T₀ T₀ = true
tritEq T₁ T₁ = true
tritEq T₂ T₂ = true
tritEq _  _  = false

f9eq : F9 → F9 → Bool
f9eq (mkF9 a b) (mkF9 c d) = tritEq a c ∧ tritEq b d

--------------------------------------------------------------------------------
-- §3. 枚举: f9at（与 oracle F9 = [(a,b) for a in F3 for b in F3] 同序）
--------------------------------------------------------------------------------

f9at : ℕ → F9
f9at zero = mkF9 T₀ T₀
f9at (suc zero) = mkF9 T₀ T₁
f9at (suc (suc zero)) = mkF9 T₀ T₂
f9at (suc (suc (suc zero))) = mkF9 T₁ T₀
f9at (suc (suc (suc (suc zero)))) = mkF9 T₁ T₁
f9at (suc (suc (suc (suc (suc zero))))) = mkF9 T₁ T₂
f9at (suc (suc (suc (suc (suc (suc zero)))))) = mkF9 T₂ T₀
f9at (suc (suc (suc (suc (suc (suc (suc zero))))))) = mkF9 T₂ T₁
f9at (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = mkF9 T₂ T₂
-- 越界退化（索引 ≥9 不进入任何求和）
f9at (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))) = mkF9 T₀ T₀

--------------------------------------------------------------------------------
-- §4. 计数层
--------------------------------------------------------------------------------

b2n : Bool → ℕ
b2n true = 1
b2n false = 0

-- y 的平方（§3 枚举索引上）
ysq : ℕ → F9
ysq i = f9mul (f9at i) (f9at i)

-- 9 索引封闭值（8 = suc⁸ zero; 只在 0..8 调用, 越界分支仅为全定义）
eight : ℕ
eight = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

-- 单项命中: 索引 k 处 y² = v ?（1/0）
sqHit : F9 → ℕ → ℕ
sqHit v k = b2n (f9eq (ysq k) v)

-- #{y ∈ F₉ : y² = v}（0..8 递归求和, 封闭归约）
nsol9at : F9 → ℕ → ℕ
nsol9at v zero = sqHit v zero + zero
nsol9at v (suc k) = sqHit v (suc k) + nsol9at v k

nsol9 : F9 → ℕ
nsol9 v = nsol9at v eight

-- rhs E x = x³ + a₂x² + a₄x + a₆（F₉ 系数嵌入）
rhs9 : CurveF3 → F9 → F9
rhs9 (mkC a₂ a₄ a₆) x =
  f9add (f9add (f9add (f9mul (f9mul x x) x) (f9mul (t2f9 a₂) (f9mul x x)))
             (f9mul (t2f9 a₄) x))
        (t2f9 a₆)

-- 单列: 索引 k 处的仿射点数
col9 : CurveF3 → ℕ → ℕ
col9 E k = nsol9 (rhs9 E (f9at k))

-- 9 列递归求和（0..8）
sum9at : CurveF3 → ℕ → ℕ
sum9at E zero = col9 E zero + zero
sum9at E (suc k) = col9 E (suc k) + sum9at E k

-- #E(F₉) = 1（无穷远点）+ 9 列之和
pointsE9 : CurveF3 → ℕ
pointsE9 E = suc (sum9at E eight)

--------------------------------------------------------------------------------
-- §5. 18 条 pe9（非奇异; 逐字生成于 oracle emit9, 2026-11-24）
--------------------------------------------------------------------------------

pe9-c010 : pointsE9 c010 ≡ 16
pe9-c010 = refl
pe9-c011 : pointsE9 c011 ≡ 16
pe9-c011 = refl
pe9-c012 : pointsE9 c012 ≡ 16
pe9-c012 = refl
pe9-c020 : pointsE9 c020 ≡ 16
pe9-c020 = refl
pe9-c021 : pointsE9 c021 ≡ 7
pe9-c021 = refl
pe9-c022 : pointsE9 c022 ≡ 7
pe9-c022 = refl
pe9-c101 : pointsE9 c101 ≡ 12
pe9-c101 = refl
pe9-c102 : pointsE9 c102 ≡ 15
pe9-c102 = refl
pe9-c111 : pointsE9 c111 ≡ 12
pe9-c111 = refl
pe9-c112 : pointsE9 c112 ≡ 15
pe9-c112 = refl
pe9-c120 : pointsE9 c120 ≡ 12
pe9-c120 = refl
pe9-c121 : pointsE9 c121 ≡ 15
pe9-c121 = refl
pe9-c201 : pointsE9 c201 ≡ 15
pe9-c201 = refl
pe9-c202 : pointsE9 c202 ≡ 12
pe9-c202 = refl
pe9-c211 : pointsE9 c211 ≡ 15
pe9-c211 = refl
pe9-c212 : pointsE9 c212 ≡ 12
pe9-c212 = refl
pe9-c220 : pointsE9 c220 ≡ 12
pe9-c220 = refl
pe9-c222 : pointsE9 c222 ≡ 15
pe9-c222 = refl
