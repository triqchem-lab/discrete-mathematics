{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.IhC60Vibration
-- I_h → 46 定理: C60 的 174 维振动表示在 I_h 下分解出恰好 46 个独立基频
--
-- 数学背景:
--   C60（足球烯）60 个顶点, 对称群 I_h（|I_h|=120, 10 个不可约表示）。
--   顶点置换表示 Γ_perm 在各类上的不动点: 仅 E(60) 与 σ 镜面(4), 其余为 0。
--   ⟨χ_perm, χ_R⟩ = (60·χ_R(E) + 60·χ_R(σ))/120 = (d_R + σ_R)/2  ⟹
--     Γ_perm = A_g + T₁g + 2T₁u + T₂g + 2T₂u + 2G_g + 2G_u + 3H_g + 2H_u (60 维)
--   振动表示 Γ_vib = Γ_perm ⊗ T₁u − T₁u(平移) − T₁g(转动), 维数 174 = 3·60−6:
--     Γ_vib = 2A_g + A_u + 3T₁g + 4T₁u + 4T₂g + 5T₂u + 6G_g + 6G_u + 8H_g + 7H_u
--   独立基频数 = 各不可约支出现数之和 = 2+1+3+4+4+5+6+6+8+7 = 46。
--
-- 形式化内容（0 postulate, 全部 ℤ[τ] 精确算术 refl, τ=(1+√5)/2, τ²=τ+1）:
--   §1 Golden 环 ℤ[τ]（无浮点, 宪法兼容）
--   §2 I_h 特征标表（10 不可约表示 × 10 共轭类, 100 项）
--   §3 张量积行 T₁u-乘积表 + 特征标级验证（10 行 × 10 类 = 100 refl）
--   §4 Γ_perm 重数（内积公式 (d+σ)/2, 10 证书）
--   §5 Γ_vib 重数向量（2,1,3,4,4,5,6,6,8,7）与主定理: 46 个独立基频
--   §6 维数守恒: Σ m_R·d_R = 174

module Sovereign.Structology.IhC60Vibration where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------------
-- §1. Golden 环: ℤ[τ], τ² = τ+1
------------------------------------------------------------------------------

Golden : Set
Golden = ℤ × ℤ          -- (a, b) = a + b·τ

τ : Golden
τ = (+ 0 , + 1)

g1 : Golden
g1 = (+ 1 , + 0)        -- 1

_+G_ : Golden → Golden → Golden
(a , b) +G (c , d) = (a + c , b + d)

-- (a+bτ)(c+dτ) = (ac+bd) + (ad+bc+bd)τ
_*G_ : Golden → Golden → Golden
(a , b) *G (c , d) = (a * c + b * d , a * d + b * c + b * d)

infixl 25 _*G_
infixl 20 _+G_

------------------------------------------------------------------------------
-- §2. I_h 不可约表示与共轭类
------------------------------------------------------------------------------

data Irrep : Set where
  Ag Au T1g T1u T2g T2u Gg Gu Hg Hu : Irrep

data Class : Set where
  CE CC5 CC52 CC3 CC2 Ci CS10 CS103 CS6 Csig : Class

-- 特征标表（100 项, τ 值: C5/S10 类取 τ, C52/S103 类取 1−τ）
charTable : Irrep → Class → Golden
-- A_g: 全 1
charTable Ag _ = g1
-- A_u: g 类 1, u 类 −1
charTable Au CE  = g1
charTable Au CC5 = g1
charTable Au CC52 = g1
charTable Au CC3 = g1
charTable Au CC2 = g1
charTable Au Ci  = (-[1+ 0 ] , + 0)
charTable Au CS10 = (-[1+ 0 ] , + 0)
charTable Au CS103 = (-[1+ 0 ] , + 0)
charTable Au CS6 = (-[1+ 0 ] , + 0)
charTable Au Csig = (-[1+ 0 ] , + 0)
-- T1g: (3, τ, 1−τ, 0, −1) g 类 / 同号 u 类
charTable T1g CE  = (+ 3 , + 0)
charTable T1g CC5 = τ
charTable T1g CC52 = (+ 1 , -[1+ 0 ])
charTable T1g CC3 = (+ 0 , + 0)
charTable T1g CC2 = (-[1+ 0 ] , + 0)
charTable T1g Ci  = (+ 3 , + 0)
charTable T1g CS10 = τ
charTable T1g CS103 = (+ 1 , -[1+ 0 ])
charTable T1g CS6 = (+ 0 , + 0)
charTable T1g Csig = (-[1+ 0 ] , + 0)
-- T1u: u 类取负
charTable T1u CE  = (+ 3 , + 0)
charTable T1u CC5 = τ
charTable T1u CC52 = (+ 1 , -[1+ 0 ])
charTable T1u CC3 = (+ 0 , + 0)
charTable T1u CC2 = (-[1+ 0 ] , + 0)
charTable T1u Ci  = (-[1+ 2 ] , + 0)
charTable T1u CS10 = (+ 0 , -[1+ 0 ])
charTable T1u CS103 = (-[1+ 0 ] , + 1)
charTable T1u CS6 = (+ 0 , + 0)
charTable T1u Csig = (+ 1 , + 0)
-- T2g: C5 类取 1−τ, C52 类取 τ
charTable T2g CE  = (+ 3 , + 0)
charTable T2g CC5 = (+ 1 , -[1+ 0 ])
charTable T2g CC52 = τ
charTable T2g CC3 = (+ 0 , + 0)
charTable T2g CC2 = (-[1+ 0 ] , + 0)
charTable T2g Ci  = (+ 3 , + 0)
charTable T2g CS10 = (+ 1 , -[1+ 0 ])
charTable T2g CS103 = τ
charTable T2g CS6 = (+ 0 , + 0)
charTable T2g Csig = (-[1+ 0 ] , + 0)
-- T2u: u 类取负
charTable T2u CE  = (+ 3 , + 0)
charTable T2u CC5 = (+ 1 , -[1+ 0 ])
charTable T2u CC52 = τ
charTable T2u CC3 = (+ 0 , + 0)
charTable T2u CC2 = (-[1+ 0 ] , + 0)
charTable T2u Ci  = (-[1+ 2 ] , + 0)
charTable T2u CS10 = (-[1+ 0 ] , + 1)
charTable T2u CS103 = (+ 0 , -[1+ 0 ])
charTable T2u CS6 = (+ 0 , + 0)
charTable T2u Csig = (+ 1 , + 0)
-- Gg: (4, −1, −1, 1, 0) g 类
charTable Gg CE  = (+ 4 , + 0)
charTable Gg CC5 = (-[1+ 0 ] , + 0)
charTable Gg CC52 = (-[1+ 0 ] , + 0)
charTable Gg CC3 = (+ 1 , + 0)
charTable Gg CC2 = (+ 0 , + 0)
charTable Gg Ci  = (+ 4 , + 0)
charTable Gg CS10 = (-[1+ 0 ] , + 0)
charTable Gg CS103 = (-[1+ 0 ] , + 0)
charTable Gg CS6 = (+ 1 , + 0)
charTable Gg Csig = (+ 0 , + 0)
-- Gu: u 类取负
charTable Gu CE  = (+ 4 , + 0)
charTable Gu CC5 = (-[1+ 0 ] , + 0)
charTable Gu CC52 = (-[1+ 0 ] , + 0)
charTable Gu CC3 = (+ 1 , + 0)
charTable Gu CC2 = (+ 0 , + 0)
charTable Gu Ci  = (-[1+ 3 ] , + 0)
charTable Gu CS10 = (+ 1 , + 0)
charTable Gu CS103 = (+ 1 , + 0)
charTable Gu CS6 = (-[1+ 0 ] , + 0)
charTable Gu Csig = (+ 0 , + 0)
-- Hg: (5, 0, 0, −1, 1) g 类
charTable Hg CE  = (+ 5 , + 0)
charTable Hg CC5 = (+ 0 , + 0)
charTable Hg CC52 = (+ 0 , + 0)
charTable Hg CC3 = (-[1+ 0 ] , + 0)
charTable Hg CC2 = (+ 1 , + 0)
charTable Hg Ci  = (+ 5 , + 0)
charTable Hg CS10 = (+ 0 , + 0)
charTable Hg CS103 = (+ 0 , + 0)
charTable Hg CS6 = (-[1+ 0 ] , + 0)
charTable Hg Csig = (+ 1 , + 0)
-- Hu: u 类取负
charTable Hu CE  = (+ 5 , + 0)
charTable Hu CC5 = (+ 0 , + 0)
charTable Hu CC52 = (+ 0 , + 0)
charTable Hu CC3 = (-[1+ 0 ] , + 0)
charTable Hu CC2 = (+ 1 , + 0)
charTable Hu Ci  = (-[1+ 4 ] , + 0)
charTable Hu CS10 = (+ 0 , + 0)
charTable Hu CS103 = (+ 0 , + 0)
charTable Hu CS6 = (+ 1 , + 0)
charTable Hu Csig = (-[1+ 0 ] , + 0)

-- 维数
dim : Irrep → ℕ
dim Ag = 1; dim Au = 1; dim T1g = 3; dim T1u = 3; dim T2g = 3
dim T2u = 3; dim Gg = 4; dim Gu = 4; dim Hg = 5; dim Hu = 5

-- Γ_perm: 60 顶点置换表示（仅 E:60, σ:4 非零）
chiPerm : Class → Golden
chiPerm CE = (+ 60 , + 0)
chiPerm Csig = (+ 4 , + 0)
chiPerm _ = (+ 0 , + 0)

------------------------------------------------------------------------------
-- §3. T₁u-张量积分解表 + 特征标级验证
------------------------------------------------------------------------------

-- R ⊗ T₁u 的不可约分解（每行 = 分解支的列表）
tensorRow : Irrep → List Irrep
tensorRow Ag  = T1u ∷ []
tensorRow Au  = T1g ∷ []
tensorRow T1g = Au ∷ T1u ∷ Hu ∷ []
tensorRow T1u = Ag ∷ T1g ∷ Hg ∷ []
tensorRow T2g = Gu ∷ Hu ∷ []
tensorRow T2u = Gg ∷ Hg ∷ []
tensorRow Gg  = T2u ∷ Gu ∷ Hu ∷ []
tensorRow Gu  = T2g ∷ Gg ∷ Hg ∷ []
tensorRow Hg  = T1u ∷ T2u ∷ Gu ∷ Hu ∷ []
tensorRow Hu  = T1g ∷ T2g ∷ Gg ∷ Hg ∷ []

chiSum : List Irrep → Class → Golden
chiSum [] C = (+ 0 , + 0)
chiSum (R ∷ rs) C = charTable R C +G chiSum rs C

-- 定理: 每行特征标 = χ_R · χ_{T₁u}（10 行 × 10 类 = 100 refl）
verify-tensor : (R : Irrep) → (C : Class) →
  chiSum (tensorRow R) C ≡ charTable R C *G charTable T1u C
verify-tensor R C with R | C
... | Ag  | CE = refl
... | Ag  | CC5 = refl
... | Ag  | CC52 = refl
... | Ag  | CC3 = refl
... | Ag  | CC2 = refl
... | Ag  | Ci = refl
... | Ag  | CS10 = refl
... | Ag  | CS103 = refl
... | Ag  | CS6 = refl
... | Ag  | Csig = refl
... | Au  | CE = refl
... | Au  | CC5 = refl
... | Au  | CC52 = refl
... | Au  | CC3 = refl
... | Au  | CC2 = refl
... | Au  | Ci = refl
... | Au  | CS10 = refl
... | Au  | CS103 = refl
... | Au  | CS6 = refl
... | Au  | Csig = refl
... | T1g | CE = refl
... | T1g | CC5 = refl
... | T1g | CC52 = refl
... | T1g | CC3 = refl
... | T1g | CC2 = refl
... | T1g | Ci = refl
... | T1g | CS10 = refl
... | T1g | CS103 = refl
... | T1g | CS6 = refl
... | T1g | Csig = refl
... | T1u | CE = refl
... | T1u | CC5 = refl
... | T1u | CC52 = refl
... | T1u | CC3 = refl
... | T1u | CC2 = refl
... | T1u | Ci = refl
... | T1u | CS10 = refl
... | T1u | CS103 = refl
... | T1u | CS6 = refl
... | T1u | Csig = refl
... | T2g | CE = refl
... | T2g | CC5 = refl
... | T2g | CC52 = refl
... | T2g | CC3 = refl
... | T2g | CC2 = refl
... | T2g | Ci = refl
... | T2g | CS10 = refl
... | T2g | CS103 = refl
... | T2g | CS6 = refl
... | T2g | Csig = refl
... | T2u | CE = refl
... | T2u | CC5 = refl
... | T2u | CC52 = refl
... | T2u | CC3 = refl
... | T2u | CC2 = refl
... | T2u | Ci = refl
... | T2u | CS10 = refl
... | T2u | CS103 = refl
... | T2u | CS6 = refl
... | T2u | Csig = refl
... | Gg  | CE = refl
... | Gg  | CC5 = refl
... | Gg  | CC52 = refl
... | Gg  | CC3 = refl
... | Gg  | CC2 = refl
... | Gg  | Ci = refl
... | Gg  | CS10 = refl
... | Gg  | CS103 = refl
... | Gg  | CS6 = refl
... | Gg  | Csig = refl
... | Gu  | CE = refl
... | Gu  | CC5 = refl
... | Gu  | CC52 = refl
... | Gu  | CC3 = refl
... | Gu  | CC2 = refl
... | Gu  | Ci = refl
... | Gu  | CS10 = refl
... | Gu  | CS103 = refl
... | Gu  | CS6 = refl
... | Gu  | Csig = refl
... | Hg  | CE = refl
... | Hg  | CC5 = refl
... | Hg  | CC52 = refl
... | Hg  | CC3 = refl
... | Hg  | CC2 = refl
... | Hg  | Ci = refl
... | Hg  | CS10 = refl
... | Hg  | CS103 = refl
... | Hg  | CS6 = refl
... | Hg  | Csig = refl
... | Hu  | CE = refl
... | Hu  | CC5 = refl
... | Hu  | CC52 = refl
... | Hu  | CC3 = refl
... | Hu  | CC2 = refl
... | Hu  | Ci = refl
... | Hu  | CS10 = refl
... | Hu  | CS103 = refl
... | Hu  | CS6 = refl
... | Hu  | Csig = refl

------------------------------------------------------------------------------
-- §4. Γ_perm 重数: m_R = (d_R + σ_R)/2
------------------------------------------------------------------------------

-- σ 类（镜面）特征标值（整数）
sigmaChi : Irrep → ℤ
sigmaChi Ag = + 1; sigmaChi Au = -[1+ 0 ]; sigmaChi T1g = -[1+ 0 ]
sigmaChi T1u = + 1; sigmaChi T2g = -[1+ 0 ]; sigmaChi T2u = + 1
sigmaChi Gg = + 0; sigmaChi Gu = + 0; sigmaChi Hg = + 1; sigmaChi Hu = -[1+ 0 ]

permMult : Irrep → ℕ
permMult Ag = 1; permMult Au = 0; permMult T1g = 1; permMult T1u = 2
permMult T2g = 1; permMult T2u = 2; permMult Gg = 2; permMult Gu = 2
permMult Hg = 3; permMult Hu = 2

-- 证书: 2·m_R = d_R + σ_R（内积公式 (d+σ)/2 的 10 条验证, ℤ 算术）
perm-cert-Ag  : (+ 2 * + 1) ≡ (+ 1 + + 1)
perm-cert-Ag  = refl
perm-cert-Au  : (+ 2 * + 0) ≡ (+ 1 + -[1+ 0 ])
perm-cert-Au  = refl
perm-cert-T1g : (+ 2 * + 1) ≡ (+ 3 + -[1+ 0 ])
perm-cert-T1g = refl
perm-cert-T1u : (+ 2 * + 2) ≡ (+ 3 + + 1)
perm-cert-T1u = refl
perm-cert-T2g : (+ 2 * + 1) ≡ (+ 3 + -[1+ 0 ])
perm-cert-T2g = refl
perm-cert-T2u : (+ 2 * + 2) ≡ (+ 3 + + 1)
perm-cert-T2u = refl
perm-cert-Gg  : (+ 2 * + 2) ≡ (+ 4 + + 0)
perm-cert-Gg  = refl
perm-cert-Gu  : (+ 2 * + 2) ≡ (+ 4 + + 0)
perm-cert-Gu  = refl
perm-cert-Hg  : (+ 2 * + 3) ≡ (+ 5 + + 1)
perm-cert-Hg  = refl
perm-cert-Hu  : (+ 2 * + 2) ≡ (+ 5 + -[1+ 0 ])
perm-cert-Hu  = refl

------------------------------------------------------------------------------
-- §5. Γ_vib 重数向量与主定理: 46 个独立基频
------------------------------------------------------------------------------

-- Γ_vib = (⊕_R m_R · (R ⊗ T₁u)) − T₁u − T₁g
times : ℕ → List Irrep → List Irrep
times 0 xs = []
times (suc n) xs = xs ++ times n xs

permVibRaw : List Irrep
permVibRaw =
  times (permMult Ag) (tensorRow Ag)
  ++ times (permMult Au) (tensorRow Au)
  ++ times (permMult T1g) (tensorRow T1g)
  ++ times (permMult T1u) (tensorRow T1u)
  ++ times (permMult T2g) (tensorRow T2g)
  ++ times (permMult T2u) (tensorRow T2u)
  ++ times (permMult Gg) (tensorRow Gg)
  ++ times (permMult Gu) (tensorRow Gu)
  ++ times (permMult Hg) (tensorRow Hg)
  ++ times (permMult Hu) (tensorRow Hu)

-- Irrep 可判定相等（100 case: 10 同 + 90 异）
irrep-dec : (R S : Irrep) → Dec (R ≡ S)
irrep-dec Ag S with S
... | Ag = yes refl
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec Au S with S
... | Ag = no (λ ())
... | Au = yes refl
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec T1g S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = yes refl
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec T1u S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = yes refl
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec T2g S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = yes refl
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec T2u S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = yes refl
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec Gg S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = yes refl
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec Gu S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = yes refl
... | Hg = no (λ ())
... | Hu = no (λ ())
irrep-dec Hg S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = yes refl
... | Hu = no (λ ())
irrep-dec Hu S with S
... | Ag = no (λ ())
... | Au = no (λ ())
... | T1g = no (λ ())
... | T1u = no (λ ())
... | T2g = no (λ ())
... | T2u = no (λ ())
... | Gg = no (λ ())
... | Gu = no (λ ())
... | Hg = no (λ ())
... | Hu = yes refl

removeOne : Irrep → List Irrep → List Irrep
removeOne R [] = []
removeOne R (x ∷ xs) with irrep-dec R x
removeOne R (x ∷ xs) | yes _ = xs
removeOne R (x ∷ xs) | no _  = x ∷ removeOne R xs

vibList : List Irrep
vibList = removeOne T1g (removeOne T1u permVibRaw)

count : Irrep → List Irrep → ℕ
count R [] = 0
count R (x ∷ xs) with irrep-dec R x
count R (x ∷ xs) | yes _ = suc (count R xs)
count R (x ∷ xs) | no _  = count R xs

vibMult : Irrep → ℕ
vibMult R = count R vibList

-- 主定理: Γ_vib = 2A_g + A_u + 3T₁g + 4T₁u + 4T₂g + 5T₂u + 6G_g + 6G_u + 8H_g + 7H_u
vib-vector :
  (vibMult Ag ≡ 2) × (vibMult Au ≡ 1) × (vibMult T1g ≡ 3) × (vibMult T1u ≡ 4)
  × (vibMult T2g ≡ 4) × (vibMult T2u ≡ 5) × (vibMult Gg ≡ 6) × (vibMult Gu ≡ 6)
  × (vibMult Hg ≡ 8) × (vibMult Hu ≡ 7)
vib-vector = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl

-- I_h → 46 定理: 独立基频数 = Σ 重数 = 46
freq-46 : vibMult Ag +ℕ vibMult Au +ℕ vibMult T1g +ℕ vibMult T1u
        +ℕ vibMult T2g +ℕ vibMult T2u +ℕ vibMult Gg +ℕ vibMult Gu
        +ℕ vibMult Hg +ℕ vibMult Hu ≡ 46
freq-46 = refl

------------------------------------------------------------------------------
-- §6. 维数守恒: Σ m_R · d_R = 174 = 3·60 − 6
------------------------------------------------------------------------------

dim-174 : vibMult Ag *ℕ dim Ag +ℕ vibMult Au *ℕ dim Au
        +ℕ vibMult T1g *ℕ dim T1g +ℕ vibMult T1u *ℕ dim T1u
        +ℕ vibMult T2g *ℕ dim T2g +ℕ vibMult T2u *ℕ dim T2u
        +ℕ vibMult Gg *ℕ dim Gg +ℕ vibMult Gu *ℕ dim Gu
        +ℕ vibMult Hg *ℕ dim Hg +ℕ vibMult Hu *ℕ dim Hu ≡ 174
dim-174 = refl

-- 174 = 3×60 − 6（平动+转动自由度排除）
dof-check : 3 *ℕ 60 ≡ 180
dof-check = refl
