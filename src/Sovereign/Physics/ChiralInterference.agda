{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.ChiralInterference
-- 手征干涉层: C3 旋转 → 场论驻波的缺失中间层 (0 postulate, 无洞)
--
-- 元理论对析评审指定三大缺口之首。焊接内容:
--   §1 干涉规则: T₁⊕T₂=T₀ (相消, 左右旋抵至寂止), T₁⊕T₁=T₂ / T₂⊕T₂=T₁
--      (相长, 同旋叠加为反旋) — 全部由 Base/Trit 的 ⊕ 表 refl 闭合。
--   §2 逐点场: 任意 SpinField 干涉的交换性 (符号, ⊕-comm)。
--   §3 反向传播波: waveCW (相位 = k) 与 waveCCW (相位 = −k) 逐点干涉
--      相消为寂止场 (符号, ⊕-inverse); 同向双波相长为反向波
--      (符号, double-neg + negate²)。
--   §4 驻波: Standing = kShift 不变; 相消干涉场处处 T₀ → 恒为驻波
--      (符号, wave-cancel 两实例 trans)。
--   §5 Frobenius 稳定性: GF(3) 上 x³=x (Fermat, 3 情形 refl) →
--      驻波在 Frobenius 时间演化下稳定 (符号)。
--
-- 诚实边界:
--   1) 非平凡 Frobenius 是 GF(9) 上的 σ(a+bα)=a−bα (阶 2,
--      Algebra/GaloisBridge.agda 已证); GF(3) 上 Frobenius 平凡,
--      故 §5 的 3 态稳定性是重言式 — 该节的意义是把"稳定性"接口
--      焊接到已证的 C₂ 事实, 不是新物理。
--   2) 干涉规则本身逐点、与维数无关; 本模块场取 (Fin 3)³ 空间截面
--      (EM 层的 Point3D), T⁶ = 3 空间 + 2 手征 + 1 规范相位的显式
--      分解见 T6FiveDimensionalProjection (后续模块)。
--   3) "光子→驻波→质量"的完整证明链需再接 massEmergence 层
--      (Physics/EntropySpin), 本模块只焊 C3→场论桥。

module Sovereign.Physics.ChiralInterference where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; fin3ToTrit; ⊕-comm; ⊕-inverse; negate²)
open import Sovereign.Physics.DiscreteEMField3D using (Point3D; next)

--------------------------------------------------------------------------------
-- §1. 干涉规则 (闭合表, 语义命名)
--   cw = T₁ (左旋 CW), ccw = T₂ (右旋 CCW), rest = T₀ (寂止/不动点)
--------------------------------------------------------------------------------

cw ccw rest : Trit
cw   = T₁
ccw  = T₂
rest = T₀

interfere : Trit → Trit → Trit
interfere x y = x ⊕ y

-- 相消: 左旋 ⊕ 右旋 = 寂止 (共轭回流抵消 → T₀ 不动点)
cw-ccw-cancel : interfere cw ccw ≡ rest
cw-ccw-cancel = refl

ccw-cw-cancel : interfere ccw cw ≡ rest
ccw-cw-cancel = refl

-- 相长: 同旋叠加为反旋 (T₁⊕T₁=T₂, T₂⊕T₂=T₁; GF(3) 中 2x = −x)
cw-cw-construct : interfere cw cw ≡ ccw
cw-cw-construct = refl

ccw-ccw-construct : interfere ccw ccw ≡ cw
ccw-ccw-construct = refl

-- 寂止中性: T₀ ⊕ x = x (⊕-identityˡ 的语义封装)
rest-neutral : ∀ x → interfere rest x ≡ x
rest-neutral x = refl

-- 相长的符号一般形式: x ⊕ x = −x (GF(3) 中 2x ≡ −x)
double-neg : ∀ x → x ⊕ x ≡ negate x
double-neg T₀ = refl
double-neg T₁ = refl
double-neg T₂ = refl

--------------------------------------------------------------------------------
-- §2. 逐点场与干涉交换性 (符号证明, 任意场)
--------------------------------------------------------------------------------

SpinField : Set
SpinField = Point3D → Trit

interfere-fields : SpinField → SpinField → SpinField
interfere-fields f g p = interfere (f p) (g p)

-- 逐点干涉交换: 左旋场 + 右旋场 = 右旋场 + 左旋场 (⊕-comm, 任意场)
interfere-comm : ∀ f g p → interfere-fields f g p ≡ interfere-fields g f p
interfere-comm f g p = ⊕-comm (f p) (g p)

-- 常值场 (CW 全场 / CCW 全场 / 寂止全场)
cwField ccwField restField : SpinField
cwField   p = cw
ccwField  p = ccw
restField p = rest

-- 全场相消: CW 场与 CCW 场逐点干涉为寂止场 (闭合)
cw-ccw-field-cancel : ∀ p → interfere-fields cwField ccwField p ≡ rest
cw-ccw-field-cancel p = refl

--------------------------------------------------------------------------------
-- §3. 反向传播波的干涉 (符号证明)
--   waveCW 相位沿 k 递增 (fin3ToTrit k), waveCCW 相位反向 (−k);
--   二者逐点相消为寂止 — 康普顿式反向波对 → 驻波的第一半。
--------------------------------------------------------------------------------

waveCW : SpinField
waveCW (i , j , k) = fin3ToTrit k

waveCCW : SpinField
waveCCW (i , j , k) = negate (fin3ToTrit k)

-- 反向波对相消: waveCW ⊕ waveCCW ≡ rest (逐点 ⊕-inverse, 符号)
wave-cancel : ∀ p → interfere-fields waveCW waveCCW p ≡ rest
wave-cancel (i , j , k) = ⊕-inverse (fin3ToTrit k)

-- 同向双 CW 波相长为 CCW 波 (逐点 double-neg: x ⊕ x = −x, 符号)
wave-cw-construct : ∀ p → interfere-fields waveCW waveCW p ≡ waveCCW p
wave-cw-construct (i , j , k) = double-neg (fin3ToTrit k)

-- 同向双 CCW 波相长为 CW 波 (double-neg + negate², 符号)
wave-ccw-construct : ∀ p → interfere-fields waveCCW waveCCW p ≡ waveCW p
wave-ccw-construct (i , j , k) =
  trans (double-neg (negate (fin3ToTrit k))) (negate² (fin3ToTrit k))

--------------------------------------------------------------------------------
-- §4. 驻波: kShift 不变性
--   相消干涉场处处为 T₀ → 恒为驻波 (周期点集 = 全空间)。
--------------------------------------------------------------------------------

kShift : Point3D → Point3D
kShift (i , j , k) = (i , j , next k)

Standing : SpinField → Set
Standing φ = ∀ p → φ p ≡ φ (kShift p)

-- 寂止场是驻波 (闭合)
rest-standing : Standing restField
rest-standing p = refl

-- 常值场皆驻波 (符号)
const-standing : ∀ t → Standing (λ _ → t)
const-standing t p = refl

-- 反向波对的相消干涉构成驻波 (wave-cancel 两实例 trans, 符号)
wave-cancel-forms-standing : Standing (interfere-fields waveCW waveCCW)
wave-cancel-forms-standing p =
  trans (wave-cancel p) (sym (wave-cancel (kShift p)))

--------------------------------------------------------------------------------
-- §5. Frobenius 稳定性 (诚实边界)
--   GF(3) Frobenius x ↦ x³ 是恒等 (Fermat: 3 情形穷举) → 驻波在
--   Frobenius 演化下稳定。非平凡 C₂ 作用在 GF(9) (GaloisBridge 已证,
--   此处不重复), 本节的稳定性因此是 3 态层的重言式接口。
--------------------------------------------------------------------------------

cube : Trit → Trit
cube x = x ⊗ (x ⊗ x)

frob3-identity : ∀ x → cube x ≡ x
frob3-identity T₀ = refl
frob3-identity T₁ = refl
frob3-identity T₂ = refl

-- 驻波在 Frobenius 时间演化下保持驻波 (frob3-identity + Standing, 符号)
frob-stability : ∀ φ → Standing φ → Standing (λ p → cube (φ p))
frob-stability φ st p =
  trans (trans (frob3-identity (φ p)) (st p))
        (sym (frob3-identity (φ (kShift p))))

-- 0 postulate.
