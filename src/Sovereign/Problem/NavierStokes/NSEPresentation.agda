{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEPresentation
-- 离散 N-S 的**展示群**表述 (无信息丢失)
--
-- 定位: 取代 NSEOnT6 的纯 GF(3) 幅度载体。按 `docs/duodecimal/11-type-theory-presentation.md`
-- 的八要素定义, 逐项给出**无截断**的表述。
--
-- ═══════════════════════════════════════════════════════════════
-- 八要素对照 (NSEOnT6 → NSEPresentation)
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      NSEOnT6: Torus6 → Trit (纯幅度, ❌ 相位截断)
--              本模块: Torus6 → DuodecPoint = Trit × AlphaPower (✅ 幅度 × 相位)
--  ② 生成元    shift3 (坐标) + diffA (幅度) + phaseDiff (相位) —— 三类生成元齐全
--  ③ 关系      mixedOp 群律 (引用 DuodecClock) + 本模块的差分律
--  ④ 相位      C₄ = ⟨α⟩ 四位置 (a0/a1/a2/a3), 每格点不可约携带
--  ⑤ 时钟      mixedOp 迭代 (12 步走钟一圈, 引用 mixedOp-12-cycle)
--  ⑥ 归零      ⊕³ (加法) / α⁴ (相位) / mixedOp¹² (联合) —— 三层归零
--  ⑦ 刚性      Frobenius 共轭 phaseConjugate (C₄ 的 C₂ 自同构)
--  ⑧ 核对      refl 确认定义自洽 (不产生结构)
--
-- ═══════════════════════════════════════════════════════════════
-- Q5 修复 (轴覆盖)
-- ═══════════════════════════════════════════════════════════════
--  NSEOnT6 的 C3 = Fin 3 只有 3 个轴, 而 T⁶ 有 6 个方向 —— 轴信息截断。
--  本模块: Axis6 = Fin 6, shiftAt 覆盖 x₁..x₆ 全部六个坐标。
--
-- 依赖: Base.Trit, Algebra.GroupTheory.DuodecClock (已证群律)
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEPresentation where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _^_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; +-mono-≤; *-mono-≤)
open import Data.Fin using (Fin; zero; suc; fromℕ<) renaming (toℕ to finToℕ)
open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ<; toℕ<n; pigeonhole)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; fin3ToTrit; tritToFin3;
   ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse; negate²)
-- ⚠ 故意不加 using: REWRITE 规则必须**整模块导入**才生效 (div3k/mod3k)
open import Sovereign.Structology.T6Rewrite
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ; *-comm; +-comm; +-cancelˡ-≡; *-cancelʳ-≡; *-zeroʳ; +-mono-<; *-monoʳ-<)
open import Data.Nat.DivMod using (+-distrib-/-∣ˡ; m*n/n≡m; [m+kn]%n≡m%n; m%n<n; m<n⇒m%n≡m; m≡m%n+[m/n]*n; m<n*o⇒m/o<n; m<n⇒m/n≡0)
open import Data.Nat.Divisibility using (divides-refl)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3;
   mulAlpha; alphaInv; mixedOp; duodec-e;
   mulAlpha-identityˡ; mixedOp-identityˡ; mixedOp-12-cycle)

--------------------------------------------------------------------------------
-- ① 载体: T⁶ 上的展示群场 (幅度 × 相位, 无截断)
--------------------------------------------------------------------------------

-- 坐标 (Z/3)
C3 : Set
C3 = Fin 3

-- 轴索引: **六个轴** (Q5 修复)
Axis6 : Set
Axis6 = Fin 6

-- T⁶ = (Z/3)⁶ 格点
Torus6 : Set
Torus6 = C3 × C3 × C3 × C3 × C3 × C3

-- 展示群场: 每格点携带 DuodecPoint = 幅度(Trit) × 相位(AlphaPower)
PresField : Set
PresField = Torus6 → DuodecPoint

-- 两个不可约分量投影 (相位不可约性: 二者不可互相约化)
amp : PresField → Torus6 → Trit
amp ψ x = proj₁ (ψ x)

ph : PresField → Torus6 → AlphaPower
ph ψ x = proj₂ (ψ x)

-- 构造
mk : (Torus6 → Trit) → (Torus6 → AlphaPower) → PresField
mk f g x = f x , g x

-- 投影-构造往返 (无信息丢失的核对: 两个分量都还原)
amp-ph-mk : ∀ f g x → amp (mk f g) x ≡ f x
amp-ph-mk f g x = refl

ph-mk : ∀ f g x → ph (mk f g) x ≡ g x
ph-mk f g x = refl

-- 分量外延: 两个分量都相等 ⇒ 场相等 (无信息丢失的判据)
ext : ∀ {ψ φ : PresField} → (∀ x → amp ψ x ≡ amp φ x)
    → (∀ x → ph ψ x ≡ ph φ x) → ∀ x → ψ x ≡ φ x
ext p q x = cong₂ _,_ (p x) (q x)

--------------------------------------------------------------------------------
-- ② 生成元
--------------------------------------------------------------------------------

-- 坐标移位 (循环 0→1→2→0)
shift3 : C3 → C3
shift3 zero = suc zero
shift3 (suc zero) = suc (suc zero)
shift3 (suc (suc zero)) = zero

shift3-cubed : ∀ x → shift3 (shift3 (shift3 x)) ≡ x
shift3-cubed zero = refl
shift3-cubed (suc zero) = refl
shift3-cubed (suc (suc zero)) = refl

-- 6 轴格点移位 (覆盖 x₁..x₆)
shiftAt : Axis6 → Torus6 → Torus6
shiftAt zero                    (x1 , x2 , x3 , x4 , x5 , x6) = shift3 x1 , x2 , x3 , x4 , x5 , x6
shiftAt (suc zero)              (x1 , x2 , x3 , x4 , x5 , x6) = x1 , shift3 x2 , x3 , x4 , x5 , x6
shiftAt (suc (suc zero))        (x1 , x2 , x3 , x4 , x5 , x6) = x1 , x2 , shift3 x3 , x4 , x5 , x6
shiftAt (suc (suc (suc zero)))  (x1 , x2 , x3 , x4 , x5 , x6) = x1 , x2 , x3 , shift3 x4 , x5 , x6
shiftAt (suc (suc (suc (suc zero)))) (x1 , x2 , x3 , x4 , x5 , x6) = x1 , x2 , x3 , x4 , shift3 x5 , x6
shiftAt (suc (suc (suc (suc (suc zero))))) (x1 , x2 , x3 , x4 , x5 , x6) = x1 , x2 , x3 , x4 , x5 , shift3 x6

-- 三次移位回归 (6 case)
shiftAt-cubed : ∀ i x → shiftAt i (shiftAt i (shiftAt i x)) ≡ x
shiftAt-cubed zero (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → z , x2 , x3 , x4 , x5 , x6) (shift3-cubed x1)
shiftAt-cubed (suc zero) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , z , x3 , x4 , x5 , x6) (shift3-cubed x2)
shiftAt-cubed (suc (suc zero)) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , z , x4 , x5 , x6) (shift3-cubed x3)
shiftAt-cubed (suc (suc (suc zero))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , z , x5 , x6) (shift3-cubed x4)
shiftAt-cubed (suc (suc (suc (suc zero)))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , x4 , z , x6) (shift3-cubed x5)
shiftAt-cubed (suc (suc (suc (suc (suc zero))))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , x4 , x5 , z) (shift3-cubed x6)

-- 幅度生成元: 前向差分 D_i^amp ψ(x) = ψ(x+e_i) ⊖ ψ(x)
diffAmp : Axis6 → PresField → Torus6 → Trit
diffAmp i ψ x = amp ψ (shiftAt i x) ⊕ negate (amp ψ x)

-- 相位生成元: C₄ 左不变差商 D_i^ph ψ(x) = ψ(x+e_i) · ψ(x)⁻¹
diffPh : Axis6 → PresField → Torus6 → AlphaPower
diffPh i ψ x = mulAlpha (ph ψ (shiftAt i x)) (alphaInv (ph ψ x))

-- 混合生成元 (展示群核心): 幅度差分 × 相位差商
diffMix : Axis6 → PresField → Torus6 → DuodecPoint
diffMix i ψ x = diffAmp i ψ x , diffPh i ψ x

--------------------------------------------------------------------------------
-- ③④ 关系与相位: C₄ 相位结构
--------------------------------------------------------------------------------

-- 相位是 4 阶的 (C₄ 闭合)
phase-order-4 : mulAlpha a1 (mulAlpha a1 (mulAlpha a1 a1)) ≡ a0
phase-order-4 = refl

-- 相位不可约: α² ≠ α (C₄ → C₂ 的非忠实商不合法)
phase-irreducible : a2 ≢ a1
phase-irreducible ()

-- 相位逆元律
mulAlpha-invʳ : ∀ a → mulAlpha a (alphaInv a) ≡ a0
mulAlpha-invʳ a0 = refl
mulAlpha-invʳ a1 = refl
mulAlpha-invʳ a2 = refl
mulAlpha-invʳ a3 = refl

-- 常数相位 ⇒ 相位差商为 1 (无转动)
diffPh-const : ∀ i (a : AlphaPower) x →
  diffPh i (λ _ → (T₀ , a)) x ≡ a0
diffPh-const i a x = mulAlpha-invʳ a

--------------------------------------------------------------------------------
-- ⑤ 时钟: mixedOp 迭代 (12 步走钟一圈)
--------------------------------------------------------------------------------

-- 时钟读数: 从单位元出发迭代 k 步
clock : ℕ → DuodecPoint
clock zero = duodec-e
clock (suc k) = mixedOp (T₁ , a1) (clock k)

-- 时钟周期 12 (引用 DuodecClock 已证定理)
clock-12 : clock 12 ≡ duodec-e
clock-12 = mixedOp-12-cycle duodec-e

-- 场的逐点时钟: 每格点独立走钟
clockAt : PresField → ℕ → PresField
clockAt ψ k x = mixedOp (clock k) (ψ x)

-- 走钟一圈回到原场 (12 步)
clockAt-12 : ∀ ψ x → clockAt ψ 12 x ≡ ψ x
clockAt-12 ψ x = trans (cong (λ p → mixedOp p (ψ x)) clock-12)
                       (mixedOp-identityˡ (ψ x))

--------------------------------------------------------------------------------
-- ⑥ 归零: 三层归零机制
--------------------------------------------------------------------------------

-- 第一层: 加法归零 (⊕³ = id)
add-cycle : ∀ t → (t ⊕ t) ⊕ t ≡ T₀
add-cycle T₀ = refl
add-cycle T₁ = refl
add-cycle T₂ = refl

-- 第二层: 相位归零 (α⁴ = a0) —— 见 phase-order-4

-- 第三层: 联合归零 (mixedOp¹² = id) —— 见 clock-12 / clockAt-12

-- 三周期求和归零 (幅度层, 构造性): f(x) ⊕ f(x+e) ⊕ f(x+2e) 的 ⊕³ 结构
-- 这是 ⊕³ = id 在差分上的体现 (库内 ProjectionDifferential.Δ³≡0 的同一机制)
triple-sum-zero : ∀ (a b c : Trit) → (((a ⊕ b) ⊕ c) ⊕ ((a ⊕ b) ⊕ c)) ⊕ ((a ⊕ b) ⊕ c) ≡ T₀
triple-sum-zero a b c = add-cycle ((a ⊕ b) ⊕ c)

--------------------------------------------------------------------------------
-- ⑦ 刚性: Frobenius 共轭 (C₄ 的 C₂ 自同构)
--------------------------------------------------------------------------------

-- 相位共轭: α^k ↦ α^{-k}
phaseConjugate : AlphaPower → AlphaPower
phaseConjugate a0 = a0
phaseConjugate a1 = a3
phaseConjugate a2 = a2
phaseConjugate a3 = a1

phaseConjugate² : ∀ a → phaseConjugate (phaseConjugate a) ≡ a
phaseConjugate² a0 = refl
phaseConjugate² a1 = refl
phaseConjugate² a2 = refl
phaseConjugate² a3 = refl

phaseConjugate-hom : ∀ a b →
  phaseConjugate (mulAlpha a b) ≡ mulAlpha (phaseConjugate a) (phaseConjugate b)
phaseConjugate-hom a0 b = refl
phaseConjugate-hom a1 a0 = refl
phaseConjugate-hom a1 a1 = refl
phaseConjugate-hom a1 a2 = refl
phaseConjugate-hom a1 a3 = refl
phaseConjugate-hom a2 a0 = refl
phaseConjugate-hom a2 a1 = refl
phaseConjugate-hom a2 a2 = refl
phaseConjugate-hom a2 a3 = refl
phaseConjugate-hom a3 a0 = refl
phaseConjugate-hom a3 a1 = refl
phaseConjugate-hom a3 a2 = refl
phaseConjugate-hom a3 a3 = refl

phaseConjugate-nontrivial : phaseConjugate a1 ≢ a1
phaseConjugate-nontrivial ()

-- 场级共轭 (保持两个分量)
conjugateField : PresField → PresField
conjugateField ψ x = amp ψ x , phaseConjugate (ph ψ x)

conjugateField² : ∀ ψ x → conjugateField (conjugateField ψ) x ≡ ψ x
conjugateField² ψ x = cong₂ _,_ refl (phaseConjugate² (ph ψ x))

--------------------------------------------------------------------------------
-- ⑧ 核对: 分量还原 (无信息丢失的最终判据)
--------------------------------------------------------------------------------

-- 场重构: 幅度 + 相位 完全决定场 (无截断)
reconstruct : ∀ ψ → ∀ x → mk (amp ψ) (ph ψ) x ≡ ψ x
reconstruct ψ x = refl

-- 信息不丢失判据: 若两个场在所有点、两个分量上都相等, 则它们相等
no-info-loss : ∀ {ψ φ : PresField}
             → (∀ x → amp ψ x ≡ amp φ x)
             → (∀ x → ph ψ x ≡ ph φ x)
             → ∀ x → ψ x ≡ φ x
no-info-loss = ext

--------------------------------------------------------------------------------
-- 审计总结 (本模块相对 NSEOnT6 的改进)
--------------------------------------------------------------------------------
{-
  NSEOnT6 的信息截断 (已在本模块修复):
    ① 载体只含 Trit (无 AlphaPower)  → 本模块 PresField = Torus6 → Trit × AlphaPower
    ④ 无相位层                       → 本模块 diffPh (C₄ 左不变差商) + phase-order-4
    ⑤ 无时钟                         → 本模块 clockAt (12 步走钟) + clockAt-12
    ⑦ 刚性弱 (仅有限性)              → 本模块 phaseConjugate (Frobenius 诱导, 16 case 同态)
    Q5 C3 = Fin 3 只有 3 轴           → 本模块 Axis6 = Fin 6 + shiftAt 覆盖 x₁..x₆

  诚实边界 (未证 / 不声称):
    ✗ 未证: 离散 Leray 投影的无条件存在性 (NSEOnT6 §4d 已构造性证否)
    ✗ 未证: 「相位刚性 ⇒ 系统无爆聚」(缺演化时间步定义)
    ✗ 不声称: 工业 CFD 可用性; 真实 Navier-Stokes 的解; 连续统极限
    ⚠ 待补: div/advection 在本载体上的完整定义 (需把速度场分量映射到 6 轴)
-}

--------------------------------------------------------------------------------
-- §9. 速度场与散度/对流 (新载体, 分量↔轴 1-1 对应)
--
-- Q5 修复的关键: NSEOnT6 的 div 用 3 轴对应 6 个分量 (轴 0,1,2 各重复两次),
-- 是**轴信息截断**。本模块的映射是干净的 1-1:
--     分量 i ↔ 轴 (i-1)      (i = 1..6, 轴 = 0..5)
--------------------------------------------------------------------------------

-- 速度场: 6 个分量场, 每个分量是 PresField (幅度 × 相位)
VelField : Set
VelField = PresField × PresField × PresField × PresField × PresField × PresField

-- 分量投影
v1 v2 v3 v4 v5 v6 : VelField → PresField
v1 (a , _) = a
v2 (_ , b , _) = b
v3 (_ , _ , c , _) = c
v4 (_ , _ , _ , d , _) = d
v5 (_ , _ , _ , _ , e , _) = e
v6 (_ , _ , _ , _ , _ , f) = f

-- 构造
mkVel : PresField → PresField → PresField → PresField → PresField → PresField → VelField
mkVel a b c d e f = a , b , c , d , e , f

-- 分量 → 轴 (1-1)
axisOf : Axis6 → Axis6
axisOf = λ i → i

-- 散度: div v = Σ_{i=1..6} D_{i-1}^amp (v_i)
-- 六个轴各不相同 (Q5 修复); 结果是幅度层标量场
div : VelField → Torus6 → Trit
div v x =
  diffAmp zero (v1 v) x
    ⊕ (diffAmp (suc zero) (v2 v) x
      ⊕ (diffAmp (suc (suc zero)) (v3 v) x
        ⊕ (diffAmp (suc (suc (suc zero))) (v4 v) x
          ⊕ (diffAmp (suc (suc (suc (suc zero)))) (v5 v) x
            ⊕ diffAmp (suc (suc (suc (suc (suc zero))))) (v6 v) x))))

-- 不可压条件
Incompressible : VelField → Set
Incompressible v = ∀ x → div v x ≡ T₀

-- 零速度场
zeroVel : VelField
zeroVel = mkVel (λ _ → (T₀ , a0)) (λ _ → (T₀ , a0)) (λ _ → (T₀ , a0))
                (λ _ → (T₀ , a0)) (λ _ → (T₀ , a0)) (λ _ → (T₀ , a0))

-- 零场不可压 (构造性)
zeroVel-incompressible : Incompressible zeroVel
zeroVel-incompressible x = refl

-- 对流项: adv_i = Σ_j (amp v_j ⊗ D_j^amp (v_i))
-- 6 路分派 (每个轴用对应的分量), 避免依赖类型匹配的复杂性
advSum : PresField → VelField → Torus6 → Trit
advSum vi v x =
  (amp (v1 v) x ⊗ diffAmp zero vi x)
    ⊕ ((amp (v2 v) x ⊗ diffAmp (suc zero) vi x)
      ⊕ ((amp (v3 v) x ⊗ diffAmp (suc (suc zero)) vi x)
        ⊕ ((amp (v4 v) x ⊗ diffAmp (suc (suc (suc zero))) vi x)
          ⊕ ((amp (v5 v) x ⊗ diffAmp (suc (suc (suc (suc zero)))) vi x)
            ⊕ (amp (v6 v) x ⊗ diffAmp (suc (suc (suc (suc (suc zero))))) vi x)))))

-- 六个分量各自的 adv
adv1 : VelField → Torus6 → Trit
adv1 v x = advSum (v1 v) v x
adv2 : VelField → Torus6 → Trit
adv2 v x = advSum (v2 v) v x
adv3 : VelField → Torus6 → Trit
adv3 v x = advSum (v3 v) v x
adv4 : VelField → Torus6 → Trit
adv4 v x = advSum (v4 v) v x
adv5 : VelField → Torus6 → Trit
adv5 v x = advSum (v5 v) v x
adv6 : VelField → Torus6 → Trit
adv6 v x = advSum (v6 v) v x

-- 对流速度场 (幅度层; 相位层独立)
advField : VelField → Torus6 → (Trit × Trit × Trit × Trit × Trit × Trit)
advField v x = adv1 v x , adv2 v x , adv3 v x , adv4 v x , adv5 v x , adv6 v x

-- 注: 相位层的对流输运待补 (C₄ 上的 adv 需要定义"速度×相位差"的乘法)

{-
  诚实边界:
  ✓ 已定义: div (6 轴 1-1 对应), advSum/adv1..adv6 (6 路分派), zeroVel-incompressible
  ⚠ 待补: 相位层对流; nsStep / Leray 投影在新载体上的完整链条
  ✗ 不声称: 工业 CFD 可用性; 真实 N-S 的解
-}

--------------------------------------------------------------------------------
-- §10. 新载体上的离散 N-S 步 (幅度层 + 相位层耦合)
--
-- 幅度层: v +F grad(p) —— 与 NSEOnT6 同构, 但轴是 1-1 对应的 6 轴
-- 相位层: θ → mulAlpha θ (Qphase θ) —— C₄ 演化, 由量子势驱动
--
-- 关键: 相位层的演化是 **C₄ 群作用**, 故有周期 4 (而非连续统的无限细分)。
--------------------------------------------------------------------------------

-- 幅度层: 场加法
addAmp : PresField → PresField → PresField
addAmp ψ φ x = amp ψ x ⊕ amp φ x , mulAlpha (ph ψ x) (ph φ x)

-- 相位量子势 (C₄): 六轴相位差商的乘积, 过 Frobenius 共轭
Qphase : PresField → Torus6 → AlphaPower
Qphase ψ x =
  phaseConjugate
    (mulAlpha (diffPh zero ψ x)
      (mulAlpha (diffPh (suc zero) ψ x)
        (mulAlpha (diffPh (suc (suc zero)) ψ x)
          (mulAlpha (diffPh (suc (suc (suc zero))) ψ x)
            (mulAlpha (diffPh (suc (suc (suc (suc zero)))) ψ x)
              (diffPh (suc (suc (suc (suc (suc zero))))) ψ x))))))

-- 相位演化步: θ ↦ θ · Qphase(θ)   (C₄ 左乘, 群作用)
phaseStep : PresField → PresField
phaseStep ψ x = amp ψ x , mulAlpha (ph ψ x) (Qphase ψ x)

-- 相位步的四步回归 (C₄ 阶 4 的推论) —— 见下方 mulAlpha-4-cycle
-- 固定相位乘子的四步回归 (构造性)
mulAlpha-4-cycle : ∀ (a b : AlphaPower) →
  mulAlpha a (mulAlpha a (mulAlpha a (mulAlpha a b))) ≡ b
mulAlpha-4-cycle a0 b = refl
mulAlpha-4-cycle a1 a0 = refl
mulAlpha-4-cycle a1 a1 = refl
mulAlpha-4-cycle a1 a2 = refl
mulAlpha-4-cycle a1 a3 = refl
mulAlpha-4-cycle a2 a0 = refl
mulAlpha-4-cycle a2 a1 = refl
mulAlpha-4-cycle a2 a2 = refl
mulAlpha-4-cycle a2 a3 = refl
mulAlpha-4-cycle a3 a0 = refl
mulAlpha-4-cycle a3 a1 = refl
mulAlpha-4-cycle a3 a2 = refl
mulAlpha-4-cycle a3 a3 = refl

-- 相位演化的周期上界 4
phaseStep-period : ∀ (a b : AlphaPower) →
  mulAlpha a (mulAlpha a (mulAlpha a (mulAlpha a b))) ≡ b
phaseStep-period = mulAlpha-4-cycle

{-
  诚实边界 (O3 现状):
  ✓ 已定义: phaseStep (C₄ 群作用), Qphase (六轴 + Frobenius)
  ✓ 已证:   固定乘子的四步回归 (phaseStep-period)
  ⚠ 未证:   「Qphase 在演化中稳定 ⇒ 系统无爆聚」—— 需要先证明 Qphase 的
            演化不变性 (或衰减), 这依赖幅度层的动力学, 本模块未建。
  ✗ 不声称: 工业 CFD 可用性; 真实 N-S 的解; 连续统极限。
-}

--------------------------------------------------------------------------------
-- §11. 幅度层演化 + 有限性 ⇒ 轨道最终周期
--
-- 状态空间: 速度场 = 6 个 PresField, 每个格点 12 个状态 (Trit × C₄)。
--   |State| = 12^729 —— **有限**。
-- 故任何确定性演化 (自映射) 的轨道最终周期 —— 这是离散意义下的"无爆聚"。
--
-- 复用: Sovereign.Analysis.FiniteDynamics.orbit-eventually-periodic
--       (已证: Fin N 上任意自映射的轨道最终周期)
--------------------------------------------------------------------------------

-- 速度场状态 (有限)
VelState : Set
VelState = VelField

-- 幅度层演化步: v ↦ v +F grad(div(adv v)) 的幅度分量
-- (相位层由 §10 的 phaseStep 给出)
-- 这里给出**抽象演化算子**的形式: 任意 VelState → VelState
NSMap : Set
NSMap = VelState → VelState

-- 有限性 ⇒ 最终周期的**证明骨架** (待闭合):
-- ① 状态编码: VelState → Fin N  (12^729 混合基数)
-- ② 推前映射 g : Fin N → Fin N, g i = code (f (decode i))
-- ③ 交换引理: code (iter f k x₀) ≡ iter g k (code x₀)
-- ④ 应用 FiniteDynamics.orbit-eventually-periodic 得 g 的最终周期
-- ⑤ 用 code 注入性拉回
--
-- ⚠ 步骤 ① 是本项目的历史卡点 (NSEOnT6 §7c 与 NSEPhaseField §7b 均未闭合):
--    12^729 的混合基数编码需要 729 层递归, Agda 归一化开销过大。
--    可能的绕法: 用已编译模块的编码设施 (Structology.T6.toℕ-sum + 其注入性),
--    或改用「轨道直接比较」而非「全域编码」(只需 12^729+1 步内的碰撞)。
--
-- 本模块因此**不声称**最终周期性; 只给出: 状态空间有限 (VelState, 12^729) +
-- 演化是自映射 (NSMap) —— 这是最终周期性的**必要结构**, 不是充分证明。

{-
  诚实边界:
  ✓ 已证: 展示群八要素 / 6 轴 1-1 / div/adv / phaseStep / 四步回归
  ⚠ 未证: 最终周期性 (卡在状态编码注入性)
  ✗ 不声称: 工业 CFD 可用性; 真实 N-S 的解; 连续统极限
-}

--------------------------------------------------------------------------------
-- §12. 状态编码 (复用已编译模块) + 最终周期性
--
-- 复用: Structology.T6 的 toℕ-sum / finToT6 / toℕ-sum-injective (T⁶ ↔ Fin 729, 已证)
--       Analysis.FiniteDynamics.orbit-eventually-periodic (Fin N 轨道最终周期, 已证)
--
-- 编码策略 (避免 12^729 的 729 层递归):
--   ① 单分量场 (幅度层): (Fin 729 → Fin 3) 的**逐点编码** —— 注入性定义性可得
--   ② 速度场: 6 个分量 → 嵌套积 (Σ-类型) —— 分量编码
--   ③ 状态空间: 注入 Fin N —— 鸽巢可达
--
-- 关键: 不需要把 (Fin 729 → Fin 3) 编码为单个 Fin —— 只需**注入性**,
--       而注入性由「逐点相等 ⇒ 由 T6 双射得点相等 ⇒ 场相等」定义性给出。
--------------------------------------------------------------------------------

-- 点编码: Torus6 → ℕ (base-3 位值; 上界见 §12b, 注入性见下)
pointCode : Torus6 → ℕ
pointCode (x1 , x2 , x3 , x4 , x5 , x6) =
  finToℕ x1 + 3 * (finToℕ x2 + 3 * (finToℕ x3 + 3 * (finToℕ x4
    + 3 * (finToℕ x5 + 3 * finToℕ x6))))

-- 幅度值编码: Trit → Fin 3 (已证注入)
ampCode : Trit → Fin 3
ampCode = tritToFin3

ampCode-injective : ∀ a b → ampCode a ≡ ampCode b → a ≡ b
ampCode-injective T₀ T₀ p = refl
ampCode-injective T₀ T₁ ()
ampCode-injective T₀ T₂ ()
ampCode-injective T₁ T₀ ()
ampCode-injective T₁ T₁ p = refl
ampCode-injective T₁ T₂ ()
ampCode-injective T₂ T₀ ()
ampCode-injective T₂ T₁ ()
ampCode-injective T₂ T₂ p = refl

{-
  诚实边界 (§12 现状):
  ✓ 已证: 幅度值编码注入 (ampCode-injective)
  ⚠ 待补: pointCode 的上界 (728) 与注入性 —— 可从 NSEOnT6 复用证明结构
  ✗ 不声称: 最终周期性的完整证明
-}

--------------------------------------------------------------------------------
-- §12b. pointCode 的上界与注入性 (从 NSEOnT6 复用证明结构)
--------------------------------------------------------------------------------

-- div3-fin3: Fin 3 元素除以 3 为零
div3-fin3 : ∀ (a : Fin 3) → finToℕ a / 3 ≡ 0
div3-fin3 zero = refl
div3-fin3 (suc zero) = refl
div3-fin3 (suc (suc zero)) = refl

-- 除以 3 提取尾部: **移植 T6.div3-add 的代码库标准模式**
-- 关键: 因式分解成 3 * b, 再用 +-distrib-/-∣ˡ + m*n/n≡m + div3-fin3
div3-add : ∀ (a : Fin 3) b → (finToℕ a + 3 * b) / 3 ≡ b
div3-add a b = begin
  (finToℕ a + 3 * b) / 3
    ≡⟨ cong (λ x → x / 3) (+-comm (finToℕ a) (3 * b)) ⟩
  (3 * b + finToℕ a) / 3
    ≡⟨ cong (λ x → (x + finToℕ a) / 3) (*-comm 3 b) ⟩
  (b * 3 + finToℕ a) / 3
    ≡⟨ +-distrib-/-∣ˡ (finToℕ a) (divides-refl b) ⟩
  (b * 3) / 3 + finToℕ a / 3
    ≡⟨ cong (λ x → x + finToℕ a / 3) (m*n/n≡m b 3) ⟩
  b + finToℕ a / 3
    ≡⟨ cong (λ x → b + x) (div3-fin3 a) ⟩
  b + 0
    ≡⟨ +-identityʳ b ⟩
  b ∎
  where open ≡-Reasoning

-- 模 3 提取首位
mod3-of : ∀ (a : Fin 3) k → (finToℕ a + k * 3) % 3 ≡ finToℕ a % 3
mod3-of a k = [m+kn]%n≡m%n (finToℕ a) k 3

-- 数字 ≤ 2 (Fin 3 的坐标值)
fin3≤2 : ∀ (a : Fin 3) → finToℕ a ≤ 2
fin3≤2 zero = z≤n
fin3≤2 (suc zero) = s≤s z≤n
fin3≤2 (suc (suc zero)) = s≤s (s≤s z≤n)

-- 上界: pointCode ≤ 728 (逐项 ≤ 2, 加权和)
pc-bound : ∀ a b c d e f → finToℕ a + 3 * finToℕ b + 9 * finToℕ c + 27 * finToℕ d
             + 81 * finToℕ e + 243 * finToℕ f ≤ 728
pc-bound a b c d e f =
  ≤-trans
    (+-mono-≤
      (+-mono-≤
        (+-mono-≤
          (+-mono-≤
            (+-mono-≤ (fin3≤2 a) (*-mono-≤ (≤-refl {3}) (fin3≤2 b)))
            (*-mono-≤ (≤-refl {9}) (fin3≤2 c)))
          (*-mono-≤ (≤-refl {27}) (fin3≤2 d)))
        (*-mono-≤ (≤-refl {81}) (fin3≤2 e)))
      (*-mono-≤ (≤-refl {243}) (fin3≤2 f)))
    (≤-refl {728})

--------------------------------------------------------------------------------
-- §12c. 最终周期性 (复用 FiniteDynamics 的鸽巢, 不经全域编码)
--
-- 关键洞察: 不需要把状态空间编码成单个 Fin N。
--   FiniteDynamics.pigeonhole-fin 只需要一个「注入 Fin (suc n) → Fin n」的**碰撞**。
--   而我们只需: 对**轨道序列**取前 N+1 项, 用 pointCode + ampCode 逐点区分。
--
-- 更简洁的复用: FiniteDynamics.orbit-eventually-periodic 已给出
--   ∀ N (f : Fin N → Fin N) (x₀ : Fin N) → EventuallyPeriodic (orbit f x₀)
-- 我们只需把状态空间**当作** Fin N —— 这要求状态空间 ≅ Fin N 的双射。
-- 由于状态空间基数 = 3^(6*729), 双射存在但构造开销大。
--
-- 本模块采取**诚实的分层**: 把「有限性 ⇒ 最终周期」作为**结构定理**陈述,
-- 证明其充分条件 (状态有限 + 自映射), 而把「具体编码」列为已文档化的工程缺口。
--------------------------------------------------------------------------------

-- 结构定理 (有限状态空间 + 自映射 ⇒ 轨道最终周期):
-- 抽象形式: 若存在注入 code : S → Fin N, 则任意自映射 f 的轨道最终周期。
--
-- 证明策略 (5 步, 复用 FiniteDynamics):
--   ① 定义 decode : Fin N → S (由 code 注入性 + 有限性)
--   ② 推前映射 g : Fin N → Fin N, g i = code (f (decode i))
--   ③ 交换引理: code (iter f k x₀) ≡ iter g k (code x₀)   (对 k 归纳)
--   ④ 应用 FiniteDynamics.orbit-eventually-periodic N g (code x₀)
--   ⑤ 用 code 注入性把 Fin N 上的周期拉回 S
--
-- ⚠ 本模块未闭合此证明。卡点是**步骤 ①/②的构造性编码算术**:
--   pointCode 的 mod3/div3 提取在本环境反复卡在归一化
--   (`mod-helper`/`div-helper` 对符号参数不归约; stdlib 的 [m+kn]%n≡m%n
--    与 Agda 的 `3 * n` 规范化形式不匹配)。
--   这是**工具链限制**, 不是数学困难 —— 见 prover_limits 记录。
--
-- 已证的部分 (§12b): pc-bound (pointCode ≤ 728) + ampCode-injective
--
-- 绕法候选 (供后续):
--   (a) 用 REWRITE 规则 (库内 T6.agda 的 div3k/mod3k 模式) 让 mod/div 归约
--   (b) 改用 Vec 型载体, 直接复用 T6.toℕ-sum + toℕ-sum-injective
--   (c) 改用「轨道直接比较」: 在 Fin 729 上做碰撞 (避免全域编码)

{-
  诚实边界 (§12):
  ✓ 已证: 展示群八要素 / 6 轴 1-1 / div/adv / phaseStep / 四步回归 /
          pc-bound / ampCode-injective
  ⚠ 未证: 最终周期性 (卡在编码算术的工具链限制)
  ✗ 不声称: 工业 CFD 可用性; 真实 N-S 的解; 连续统极限
-}

--------------------------------------------------------------------------------
-- §12d. pointCode 的注入性 (T6 模式的直接应用)
--
-- 关键: pointCode 定义为 finToℕ x1 + 3*(...), 因式分解成 3 * tail 后用 div3-add。
--------------------------------------------------------------------------------

-- 层 1: pointCode / 3 = 内层 (用 div3-add)
-- 层 1: pointCode / 3 = 内层 (用 div3-add)
pc/3-1 : ∀ a b c d e f →
  pointCode (a , b , c , d , e , f) / 3
    ≡ finToℕ b + 3 * (finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)))
pc/3-1 a b c d e f = div3-add a (finToℕ b + 3 * (finToℕ c + 3 * (finToℕ d
                       + 3 * (finToℕ e + 3 * finToℕ f))))

-- 模 3 提取首位: (a + 3*k) % 3 = a (对 a : Fin 3)
mod3-idem : ∀ (a : Fin 3) → finToℕ a % 3 ≡ finToℕ a
mod3-idem zero = refl
mod3-idem (suc zero) = refl
mod3-idem (suc (suc zero)) = refl

mod3-add : ∀ (a : Fin 3) k → (finToℕ a + 3 * k) % 3 ≡ finToℕ a
mod3-add a k =
  trans (trans (cong (_% 3) (cong (_+_ (finToℕ a)) (*-comm 3 k)))
               ([m+kn]%n≡m%n (finToℕ a) k 3))
        (mod3-idem a)

-- 层 1: pointCode 的模 3 = 首位
pc%3-1 : ∀ a b c d e f → pointCode (a , b , c , d , e , f) % 3 ≡ finToℕ a
pc%3-1 a b c d e f = mod3-add a (finToℕ b + 3 * (finToℕ c + 3 * (finToℕ d
                       + 3 * (finToℕ e + 3 * finToℕ f))))

-- fin3 相等判据
fin3-eq : ∀ {a b : Fin 3} → finToℕ a ≡ finToℕ b → a ≡ b
fin3-eq = toℕ-injective

--------------------------------------------------------------------------------
-- §12e. pointCode 注入性 (6 层剥离, 复用 div3-add + mod3-add)
--
-- 结构: 对每层 i, 提取 (pointCode / 3^i) % 3, 用 fin3-eq 得第 i 个分量相等。
-- 前 5 层用 div3-add, 第 6 层用 mod3-add。
--------------------------------------------------------------------------------

-- 层 2: 尾部 (5 项)
pc/3-2 : ∀ a b c d e f →
  (pointCode (a , b , c , d , e , f) / 3) / 3
    ≡ finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))
pc/3-2 a b c d e f =
  trans (cong (_/ 3) (pc/3-1 a b c d e f))
        (div3-add b (finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))))

-- 层 3
pc/3-3 : ∀ a b c d e f →
  ((pointCode (a , b , c , d , e , f) / 3) / 3) / 3
    ≡ finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)
pc/3-3 a b c d e f =
  trans (cong (_/ 3) (pc/3-2 a b c d e f))
        (div3-add c (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)))

-- 层 4
pc/3-4 : ∀ a b c d e f →
  (((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) / 3
    ≡ finToℕ e + 3 * finToℕ f
pc/3-4 a b c d e f =
  trans (cong (_/ 3) (pc/3-3 a b c d e f))
        (div3-add d (finToℕ e + 3 * finToℕ f))

-- 层 5
pc/3-5 : ∀ a b c d e f →
  ((((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) / 3) / 3
    ≡ finToℕ f
pc/3-5 a b c d e f =
  trans (cong (_/ 3) (pc/3-4 a b c d e f))
        (div3-add e (finToℕ f))

-- 各层的模 3 提取
pc%3-2 : ∀ a b c d e f → (pointCode (a , b , c , d , e , f) / 3) % 3 ≡ finToℕ b
pc%3-2 a b c d e f = trans (cong (_% 3) (pc/3-1 a b c d e f))
                           (mod3-add b (finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))))

pc%3-3 : ∀ a b c d e f → ((pointCode (a , b , c , d , e , f) / 3) / 3) % 3 ≡ finToℕ c
pc%3-3 a b c d e f = trans (cong (_% 3) (pc/3-2 a b c d e f))
                           (mod3-add c (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)))

pc%3-4 : ∀ a b c d e f → (((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) % 3 ≡ finToℕ d
pc%3-4 a b c d e f = trans (cong (_% 3) (pc/3-3 a b c d e f))
                           (mod3-add d (finToℕ e + 3 * finToℕ f))

pc%3-5 : ∀ a b c d e f → ((((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) / 3) % 3 ≡ finToℕ e
pc%3-5 a b c d e f = trans (cong (_% 3) (pc/3-4 a b c d e f))
                           (mod3-add e (finToℕ f))

-- 主定理: pointCode 注入
pointCode-injective : ∀ x y → pointCode x ≡ pointCode y → x ≡ y
pointCode-injective (a , b , c , d , e , f) (a' , b' , c' , d' , e' , f') eq =
  cong₂ (λ p q → p , q) (fin3-eq e1) (tail5-inj eq1)
  where
    e1 : finToℕ a ≡ finToℕ a'
    e1 = trans (sym (pc%3-1 a b c d e f))
             (trans (cong (_% 3) eq) (pc%3-1 a' b' c' d' e' f'))
    eq1 : pointCode (a , b , c , d , e , f) / 3 ≡ pointCode (a' , b' , c' , d' , e' , f') / 3
    eq1 = cong (_/ 3) eq
    tail5-inj : pointCode (a , b , c , d , e , f) / 3 ≡ pointCode (a' , b' , c' , d' , e' , f') / 3
              → (b , c , d , e , f) ≡ (b' , c' , d' , e' , f')
    tail5-inj eq' = cong₂ (λ p q → p , q) (fin3-eq e2) (tail4-inj eq2)
      where
        e2 : finToℕ b ≡ finToℕ b'
        e2 = trans (sym (pc%3-2 a b c d e f))
               (trans (cong (_% 3) eq') (pc%3-2 a' b' c' d' e' f'))
        eq2 = cong (_/ 3) eq'
        tail4-inj : _ → (c , d , e , f) ≡ (c' , d' , e' , f')
        tail4-inj eq'' = cong₂ (λ p q → p , q) (fin3-eq e3) (tail3-inj eq3)
          where
            e3 : finToℕ c ≡ finToℕ c'
            e3 = trans (sym (pc%3-3 a b c d e f))
                   (trans (cong (_% 3) eq'') (pc%3-3 a' b' c' d' e' f'))
            eq3 = cong (_/ 3) eq''
            tail3-inj : _ → (d , e , f) ≡ (d' , e' , f')
            tail3-inj eq''' = cong₂ (λ p q → p , q) (fin3-eq e4) (tail2-inj eq4)
              where
                e4 : finToℕ d ≡ finToℕ d'
                e4 = trans (sym (pc%3-4 a b c d e f))
                       (trans (cong (_% 3) eq''') (pc%3-4 a' b' c' d' e' f'))
                eq4 = cong (_/ 3) eq'''
                tail2-inj : _ → (e , f) ≡ (e' , f')
                tail2-inj eq'''' = cong₂ (λ p q → p , q) (fin3-eq e5) (fin3-eq e6)
                  where
                    e5 : finToℕ e ≡ finToℕ e'
                    e5 = trans (sym (pc%3-5 a b c d e f))
                           (trans (cong (_% 3) eq'''') (pc%3-5 a' b' c' d' e' f'))
                    e6 : finToℕ f ≡ finToℕ f'
                    e6 = trans (sym (pc/3-5 a b c d e f))
                           (trans (cong (_/ 3) eq'''') (pc/3-5 a' b' c' d' e' f'))

--------------------------------------------------------------------------------
-- §12f. 分量编码与状态编码
--------------------------------------------------------------------------------

-- 因式分解形式的界 (与 pointCode 定义精确匹配)
fac-bound : ∀ a b c d e f → finToℕ a + 3 * (finToℕ b + 3 * (finToℕ c
            + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)))) ≤ 728
fac-bound a b c d e f =
  ≤-trans
    (+-mono-≤ (fin3≤2 a)
      (*-mono-≤ (≤-refl {3})
        (≤-trans
          (+-mono-≤ (fin3≤2 b)
            (*-mono-≤ (≤-refl {3})
              (≤-trans
                (+-mono-≤ (fin3≤2 c)
                  (*-mono-≤ (≤-refl {3})
                    (≤-trans
                      (+-mono-≤ (fin3≤2 d)
                        (*-mono-≤ (≤-refl {3})
                          (≤-trans
                            (+-mono-≤ (fin3≤2 e)
                              (*-mono-≤ (≤-refl {3}) (fin3≤2 f)))
                            (≤-refl {2 + 3 * 2}))))
                      (≤-refl {2 + 3 * (2 + 3 * 2)}))))
                (≤-refl {2 + 3 * (2 + 3 * (2 + 3 * 2))}))))
          (≤-refl {2 + 3 * (2 + 3 * (2 + 3 * (2 + 3 * 2)))}))))
    (≤-refl {728})

-- pointCode < 729
pc<729 : ∀ x → pointCode x < 729
pc<729 (a , b , c , d , e , f) = s≤s (fac-bound a b c d e f)

-- 点编码: Torus6 → Fin 729
encodePt : Torus6 → Fin 729
encodePt x = fromℕ< (pc<729 x)

-- 点编码注入性
-- 关键: toℕ (fromℕ< p) ≡ pointCode x (stdlib: toℕ-fromℕ<)
encodePt-injective : ∀ x y → encodePt x ≡ encodePt y → x ≡ y
encodePt-injective x y eq =
  pointCode-injective x y
    (trans (sym (toℕ-encodePt x)) (trans (cong finToℕ eq) (toℕ-encodePt y)))
  where
    toℕ-encodePt : ∀ x → finToℕ (encodePt x) ≡ pointCode x
    toℕ-encodePt x = toℕ-fromℕ< (pc<729 x)

--------------------------------------------------------------------------------
-- §12g. 分量场编码注入性 → 状态编码注入性 → 最终周期性
--------------------------------------------------------------------------------

-- 分量场编码: 逐点取幅度 (用 encodePt 索引) —— 需要 Torus6 的解码器
-- decodePt : Fin 729 → Torus6 (由 pointCode 的数字提取构造)
-- encodeComp : PresField → (Fin 729 → Fin 3)
-- encodeComp ψ i = ampCode (amp ψ (decodePt i))
--
-- 注入性: 若 encodeComp ψ ≡ encodeComp φ, 则对任意 i 有
--   ampCode (amp ψ (decodePt i)) ≡ ampCode (amp φ (decodePt i))
-- 由 ampCode-injective 得 amp ψ (decodePt i) ≡ amp φ (decodePt i);
-- 再由 decodePt 的**满射性** (∀ x, ∃ i, decodePt i ≡ x) 得 ∀ x, amp ψ x ≡ amp φ x。
--
-- ⚠ 需要: decodePt 的定义 + 其满射性 (pointCode 的数字提取 + roundtrip)
--         或改用 Vec 载体 (见下)。

{-
  §12g 结论: 链条已推进到「点编码注入」这一步 (pointCode-injective / encodePt-injective 已证)。
  下一步的瓶颈是 **decodePt : Fin 729 → Torus6** 的构造:
    - 需要从 Fin 729 的数字提取出 6 个 Fin 3 分量 (div/mod 逐层)
    - 或改用 Vec (Fin 3) 6 载体, 直接复用 T6.finToT6 (已编译)
    - 或改用「轨道直接比较」(不需要解码器)

  ✓ 本模块已证: 展示群八要素 / 6 轴 1-1 / div/adv / phaseStep /
                pc-bound / fac-bound / pc<729 / pointCode-injective /
                encodePt / encodePt-injective / ampCode-injective
  ✗ 未证: 最终周期性 (瓶颈: decodePt 的构造)
-}

--------------------------------------------------------------------------------
-- §12f'. 逐层 Horner 值函数 (shift 友好, 为往返引理准备)
--
-- 关键设计: 用**逐层**的值函数 val1..val5, 每层的 shift 关系都是 refl。
-- 这避开了单一 val6 的嵌套归一化问题。
--------------------------------------------------------------------------------

val1 : ℕ → ℕ
val1 x1 = x1

val2 : ℕ × ℕ → ℕ
val2 (x1 , x2) = x1 + val1 x2 * 3

val3 : ℕ × ℕ × ℕ → ℕ
val3 (x1 , x2 , x3) = x1 + val2 (x2 , x3) * 3

val4 : ℕ × ℕ × ℕ × ℕ → ℕ
val4 (x1 , x2 , x3 , x4) = x1 + val3 (x2 , x3 , x4) * 3

val5 : ℕ × ℕ × ℕ × ℕ × ℕ → ℕ
val5 (x1 , x2 , x3 , x4 , x5) = x1 + val4 (x2 , x3 , x4 , x5) * 3

-- 尾零引理 (逐层)
tail2 : ∀ x → val2 (x , 0) ≡ x
tail2 x = trans (cong (x +_) (*-zeroʳ 3)) (+-identityʳ x)

tail3 : ∀ x → val3 (x , 0 , 0) ≡ x
tail3 x = trans (cong (x +_) (cong (_* 3) (tail2 0)))
                (trans (cong (x +_) (*-zeroʳ 3)) (+-identityʳ x))

tail4 : ∀ x → val4 (x , 0 , 0 , 0) ≡ x
tail4 x = trans (cong (x +_) (cong (_* 3) (tail3 0)))
                (trans (cong (x +_) (*-zeroʳ 3)) (+-identityʳ x))

tail5 : ∀ x → val5 (x , 0 , 0 , 0 , 0) ≡ x
tail5 x = trans (cong (x +_) (cong (_* 3) (tail4 0)))
                (trans (cong (x +_) (*-zeroʳ 3)) (+-identityʳ x))

-- shift 关系 (全部 refl)
val5-shift : ∀ x d1 d2 d3 d4 →
  val5 (x , d1 , d2 , d3 , d4) ≡ x + val4 (d1 , d2 , d3 , d4) * 3
val5-shift x d1 d2 d3 d4 = refl

-- 5 元组解码器
decode5 : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
decode5 n zero = n % 3 , 0 , 0 , 0 , 0
decode5 n (suc k) with decode5 (n / 3) k
... | (x1 , x2 , x3 , x4 , x5) = n % 3 , x1 , x2 , x3 , x4

--------------------------------------------------------------------------------
-- §12g'. 代码库范式: Horner 形式 + divExtract/modExtract (LCM.agda 模式)
--
-- 关键发现 (查代码库 Coupling/LCM.agda:149-158):
--   代码库的编码一律用 **Horner 形式** `v + q * 3` (因子在**右**),
--   配合 divExtract/modExtract 用 `m≡m%n+[m/n]*n` + 消去律, **不依赖算术归一化**。
--   这正好绕开 `3 * c ≡ c + (c + c)` 的 Nat 乘法规范化问题。
--------------------------------------------------------------------------------

-- Horner 形式的点值 (因子在右)
valH : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ
valH (x1 , x2 , x3 , x4 , x5 , x6) =
  x1 + (x2 + (x3 + (x4 + (x5 + x6 * 3) * 3) * 3) * 3) * 3

-- 尾零化简 (x1 < 3, 3 case)
tail0 : ∀ x1 → x1 < 3 → valH (x1 , 0 , 0 , 0 , 0 , 0) ≡ x1
tail0 zero p = refl
tail0 (suc zero) p = refl
tail0 (suc (suc zero)) p = refl
tail0 (suc (suc (suc x))) (s≤s (s≤s (s≤s ())))

-- modExtract (LCM 范式)
modExtract : ∀ v q → v < 3 → (v + q * 3) % 3 ≡ v
modExtract v q v<3 = trans ([m+kn]%n≡m%n v q 3) (m<n⇒m%n≡m v<3)

-- divExtract (LCM 范式, 不依赖算术归一化)
divExtract : ∀ v q → v < 3 → (v + q * 3) / 3 ≡ q
divExtract v q v<3 =
  let n = v + q * 3
      n%3≡v : n % 3 ≡ v
      n%3≡v = modExtract v q v<3
      eq : n ≡ n % 3 + (n / 3) * 3
      eq = m≡m%n+[m/n]*n n 3
      eq2 : v + q * 3 ≡ v + (n / 3) * 3
      eq2 = trans eq (cong (λ x → x + (n / 3) * 3) n%3≡v)
      eq3 : q * 3 ≡ (n / 3) * 3
      eq3 = +-cancelˡ-≡ v _ _ eq2
  in sym (*-cancelʳ-≡ q (n / 3) 3 eq3)

--------------------------------------------------------------------------------
-- §12h. 点解码器 decodePt : Fin 729 → Torus6 (数字提取)
--
-- 用 pointCode 的因式分解形式: pc = x1 + 3*(x2 + 3*(x3 + 3*(x4 + 3*(x5 + 3*x6))))
-- 故逐层取 %3 与 /3 即可还原 x1..x6。
--------------------------------------------------------------------------------

-- 从 ℕ 提取第 k 位 (k = 0..5)
digit : ℕ → ℕ → Fin 3
digit n zero = fromℕ< (mod3<3 n)
  where
    mod3<3 : ∀ m → m % 3 < 3
    mod3<3 m = m%n<n m 3
digit n (suc k) = digit (n / 3) k

-- 注: digit 用 fromℕ< 构造 Fin 3; 需证明 n % 3 < 3 (stdlib m%n<n)。
-- 完整解码器需要 6 层嵌套的 digit 调用。
--
-- ⚠ 这里的 digit 对 k 递归, 但 k ≤ 5 (常数层数), 不会触发大递归归一化。

-- 点解码器
decodePt : Fin 729 → Torus6
decodePt i =
  digit (finToℕ i) zero
    , digit (finToℕ i) (suc zero)
    , digit (finToℕ i) (suc (suc zero))
    , digit (finToℕ i) (suc (suc (suc zero)))
    , digit (finToℕ i) (suc (suc (suc (suc zero))))
    , digit (finToℕ i) (suc (suc (suc (suc (suc zero)))))

-- 辅助: 用给定层数解码
decodeAux : ℕ → ℕ → Torus6
decodeAux n zero = fromℕ< (mod3<3 n) , zero , zero , zero , zero , zero
  where
    mod3<3 : ∀ m → m % 3 < 3
    mod3<3 m = m%n<n m 3
decodeAux n (suc k) with decodeAux (n / 3) k
... | (x1 , x2 , x3 , x4 , x5 , x6) =
      fromℕ< (mod3<3 n) , x1 , x2 , x3 , x4 , x5
  where
    mod3<3 : ∀ m → m % 3 < 3
    mod3<3 m = m%n<n m 3

-- 解码-编码往返: 用 n = n%3 + 3*(n/3) 逐层展开
-- 需要 Agda 归约 mod-helper/div-helper —— 对**具体 n** 可归约, 对符号 n 用 stdlib 引理
{-
  待补: decode-encode 的完整证明。
  已定位的最后一个障碍是**算术归一化**, 不是数学:
    · 目标涉及 `val (shift (n%3) (decodeN (n/3) k)) ≡ n%3 + 3 * val (decodeN (n/3) k)`
    · 展开后需证 `x5 + (x6 + (x6 + x6)) ≡ x5 + 3 * x6` (即 3*c ≡ c+(c+c))
    · 但 `*-suc`/`*-comm` 在符号参数上给出 `c * 2` 而非 `c + c`,
      Agda 的 Nat 乘法规范化 (左递归 suc) 与 `3 * c` 的展开不匹配
  绕法候选:
    (a) 用 `*-distribˡ-+` + `*-identityˡ` 显式展开 `3 * c ≡ 1*c + (1*c + 1*c)`
    (b) 把 val 的定义改成**左结合** `((((x1*3+x2)*3+x3)*3+...` 匹配 Horner 形式
    (c) 直接用 `fromℕ<` 的 `toℕ-fromℕ<` 性质, 避免展开 val

  ✓ 已证: pointCode-injective (6 层) / fac-bound / pc<729 / encodePt /
          encodePt-injective / ampCode-injective / decodePt / digit / decodeAux
  ⚠ 未证: decode-encode 往返 (算术归一化) → encodeComp 注入 → 状态编码 → 最终周期
-}

--------------------------------------------------------------------------------
-- §13. 解码-编码往返 (算术障碍已解除: 改用按位数递归的 Val/valN/decN)
--
-- 历史障碍: 早前用**分层** val1..val5 + decode5 试图证明
--   val5 (decode5 n k) ≡ n % 3^k,
-- 但 (a) `NonZero (3 ^ k)` 无法被 Agda 的 instance 搜索找到 (3^k 对变量 k 不归约),
--     (b) val5 的第 5 位永远被丢弃, 与 val4 不 definitionally 相等。
--
-- 解法 (本段): 值函数与解码器**按位数递归**, 用依值类型 Val k 精确控制层数:
--   Val 0 = ℕ,  Val (suc k) = ℕ × Val k
--   valN (suc k) (x , d) = x + valN k d * 3
--   decN (suc k) n = n % 3 , decN k (n / 3)
-- 往返引理 valN-decN 于是是**纯 refl + cong**, 完全避开 mod/div 归一化与 3^k。
--
-- 再由 n < 3^k ⟹ remN k n ≡ n (对 k 归纳, 用 m<n*o⇒m/o<n + m≡m%n+[m/n]*n)
-- 得到 pointCode 的往返: decN 6 (pointCode x) 与 x 的 6 位数字一致。
--------------------------------------------------------------------------------

Val : ℕ → Set
Val zero = ℕ
Val (suc k) = ℕ × Val k

valN : ∀ k → Val k → ℕ
valN zero x = x
valN (suc k) (x , d) = x + valN k d * 3

decN : ∀ k → ℕ → Val k
decN zero n = zero
decN (suc k) n = n % 3 , decN k (n / 3)

remN : ℕ → ℕ → ℕ
remN zero n = zero
remN (suc k) n = n % 3 + remN k (n / 3) * 3

-- 核心往返引理 (无任何算术引理依赖)
valN-decN : ∀ k n → valN k (decN k n) ≡ remN k n
valN-decN zero n = refl
valN-decN (suc k) n = cong (λ z → n % 3 + z * 3) (valN-decN k (n / 3))

-- n < 1 ⟹ n ≡ 0
<1⇒0 : ∀ n → n < 1 → n ≡ 0
<1⇒0 zero p = refl
<1⇒0 (suc n) (s≤s ())

-- 主引理: n < 3^k ⟹ remN k n ≡ n  (即低 k 位就是 n 本身)
remN-full : ∀ k n → n < 3 ^ k → remN k n ≡ n
remN-full zero n n<1 = sym (<1⇒0 n n<1)
remN-full (suc k) n n<3k =
  trans (cong (λ z → n % 3 + z * 3) (remN-full k (n / 3) n/3<3k))
        (sym (m≡m%n+[m/n]*n n 3))
  where
    n<3*3k : n < 3 * 3 ^ k
    n<3*3k = subst (λ z → n < z) (sym 3*3k≡3^suck) n<3k
      where
        3*3k≡3^suck : 3 * 3 ^ k ≡ 3 ^ suc k
        3*3k≡3^suck = refl
    n<3k*3 : n < 3 ^ k * 3
    n<3k*3 = subst (λ z → n < z) (sym (*-comm (3 ^ k) 3)) n<3*3k
    n/3<3k : n / 3 < 3 ^ k
    n/3<3k = m<n*o⇒m/o<n {n = 3 ^ k} {o = 3} n<3k*3

-- 数值往返: 6 位解码的值就是原数 (n < 729 = 3⁶)
remN6-full : ∀ n → n < 729 → remN 6 n ≡ n
remN6-full n n<729 = remN-full 6 n (subst (λ z → n < z) 3^6≡729 n<729)
  where
    3^6≡729 : 3 ^ 6 ≡ 729
    3^6≡729 = refl

-- pointCode 的往返: 6 位解码器作用于 pointCode 得到原值
pointCode-roundtrip : ∀ x → valN 6 (decN 6 (pointCode x)) ≡ pointCode x
pointCode-roundtrip x =
  trans (valN-decN 6 (pointCode x)) (remN6-full (pointCode x) (pc<729 x))

-- decN 6 ∘ pointCode 注入
decN6-pointCode-injective : ∀ x y → decN 6 (pointCode x) ≡ decN 6 (pointCode y) → x ≡ y
decN6-pointCode-injective x y eq =
  pointCode-injective x y
    (trans (sym (pointCode-roundtrip x)) (trans (cong (valN 6) eq) (pointCode-roundtrip y)))

{-
  §13 结论 (往返链已闭合):
  ✓ valN-decN   : 按位数递归的值函数与解码器往返 (纯 refl/cong)
  ✓ remN-full   : n < 3^k ⟹ 低 k 位值 = n
  ✓ pointCode-roundtrip : valN 6 (decN 6 (pointCode x)) ≡ pointCode x
  ✓ decN6-pointCode-injective : 6 位解码注入 (独立于 encodePt-injective 的第二条注入路径)
  ⚠ 仍未做: 状态编码 (VelState → Fin N) 的完整注入 + 最终周期性
-}

--------------------------------------------------------------------------------
-- §14. 相位编码 (C₄ → Fin 4) —— 状态编码的相位分量
--
-- 状态空间 PresField = Torus6 → DuodecPoint 是**有限**的 (|Torus6| = 729,
-- |DuodecPoint| = 12)。有限性 ⇒ 任何确定性自映射的轨道最终周期
-- (离散意义下的"无爆聚")。
--
-- 编码方案 (注入, 不需要解码器):
--   stateEnc : PresField → (Fin 729 → Fin 3 × Fin 4)
--   stateEnc ψ i = ampCode (amp ψ (decodePt i)) , phCode (ph ψ (decodePt i))
-- 注入性由 ampCode-injective + phCode-injective + ext 给出 —— **但**需要
-- decodePt (encodePt x) ≡ x (§13 的往返引理可给, 尚未接线)。
--
-- ⚠ 待接线 (诚实边界): decodePt-roundtrip : ∀ x → decodePt (encodePt x) ≡ x
--   由 §13 的 pointCode-roundtrip (valN 6 (decN 6 (pointCode x)) ≡ pointCode x)
--   + pointCode-injective 可得, 但 decodePt 用 digit/decodeAux 定义, 与
--   decN 的对应关系尚未形式化 (需要 digit n k ≡ 第 k 位数字 的引理)。
--------------------------------------------------------------------------------

-- 相位编码: AlphaPower ≅ C₄ → Fin 4
phCode : AlphaPower → Fin 4
phCode a0 = zero
phCode a1 = suc zero
phCode a2 = suc (suc zero)
phCode a3 = suc (suc (suc zero))

phCode-injective : ∀ a b → phCode a ≡ phCode b → a ≡ b
phCode-injective a0 a0 p = refl
phCode-injective a0 a1 ()
phCode-injective a0 a2 ()
phCode-injective a0 a3 ()
phCode-injective a1 a0 ()
phCode-injective a1 a1 p = refl
phCode-injective a1 a2 ()
phCode-injective a1 a3 ()
phCode-injective a2 a0 ()
phCode-injective a2 a1 ()
phCode-injective a2 a2 p = refl
phCode-injective a2 a3 ()
phCode-injective a3 a0 ()
phCode-injective a3 a1 ()
phCode-injective a3 a2 ()
phCode-injective a3 a3 p = refl

-- 分量场编码: 逐点取 (幅度, 相位) 的 Fin 编码
compEnc : PresField → (Torus6 → Fin 3 × Fin 4)
compEnc ψ x = ampCode (amp ψ x) , phCode (ph ψ x)

-- 分量场编码的**逐点**注入性 (不需要解码器, 也不需要函数外延)
-- 注: 结论是逐点相等而非函数相等 ψ ≡ φ —— 后者需要 funExt, 本库 (非 cubical) 无此公理。
compEnc-injective : ∀ {ψ φ} → (∀ x → compEnc ψ x ≡ compEnc φ x) → ∀ x → ψ x ≡ φ x
compEnc-injective {ψ} {φ} eq =
  ext (λ x → ampCode-injective (amp ψ x) (amp φ x) (cong proj₁ (eq x)))
      (λ x → phCode-injective (ph ψ x) (ph φ x) (cong proj₂ (eq x)))

{-
  §14 结论:
  ✓ phCode / phCode-injective : C₄ 相位 → Fin 4 注入
  ✓ compEnc / compEnc-injective : 逐点 (幅度, 相位) 编码注入 (不需要解码器)
  ⚠ 待接线: decodePt-roundtrip (使 stateEnc 用 decodePt 索引成立)
  ⚠ 待做: 把 (Torus6 → Fin 3 × Fin 4) 注入 Fin N, 再调用
          FiniteDynamics.orbit-eventually-periodic-fin 得最终周期性
-}

--------------------------------------------------------------------------------
-- §15. 解码-编码往返闭合（decodePt ∘ encodePt ≡ id）
--
-- 用 codeToPoint（6 层 digit 提取）与 §13 的 pointCode-roundtrip 闭合：
--   codeToPoint (pointCode x) ≡ x
-- 从而 decodePt (encodePt x) ≡ x（decodePt 与 codeToPoint 定义同构）。
--
-- 关键引理（都是字面量除数 3，不用 3^k）：
--   mod3f : f3 (toℕ a + 3 * t) ≡ a
--   div3f : (toℕ a + 3 * t) / 3 ≡ t
--------------------------------------------------------------------------------

-- 六层剥离的提取引理: (finToℕ a + 3 * t) / 3 ≡ t
div3f : ∀ (a : Fin 3) (t : ℕ) → (finToℕ a + 3 * t) / 3 ≡ t
div3f a t =
  trans (cong (λ z → z / 3) (+-comm (finToℕ a) (3 * t)))
        (trans (cong (λ z → (z + finToℕ a) / 3) (*-comm 3 t))
               (div3' (finToℕ a) t (toℕ<n a)))
  where
    div3' : ∀ a t → a < 3 → (t * 3 + a) / 3 ≡ t
    div3' a t a<3 = trans (+-distrib-/-∣ˡ {m = t * 3} a {d = 3} (divides-refl t))
      (trans (cong (λ z → z + a / 3) (m*n/n≡m t 3))
      (trans (cong (λ z → t + z) (m<n⇒m/n≡0 {a} {3} a<3)) (+-identityʳ t)))

-- 模提取: f3 (finToℕ a + 3 * t) ≡ a
mod3f : ∀ (a : Fin 3) (t : ℕ) → fromℕ< (m%n<n (finToℕ a + 3 * t) 3) ≡ a
mod3f a t = toℕ-injective (trans (toℕ-fromℕ< _)
  (trans (cong (λ z → (finToℕ a + z) % 3) (*-comm 3 t))
  (trans ([m+kn]%n≡m%n (finToℕ a) t 3) (m<n⇒m%n≡m (toℕ<n a)))))

-- 顶层 f3（供 codeToPoint 与往返引理共用）
f3 : ℕ → Fin 3
f3 m = fromℕ< (m%n<n m 3)

-- 点码 → 6 坐标（与 decodePt 定义同构）
codeToPoint : ℕ → Torus6
codeToPoint n =
  f3 n , f3 (n / 3) , f3 ((n / 3) / 3) , f3 (((n / 3) / 3) / 3)
  , f3 ((((n / 3) / 3) / 3) / 3) , f3 (((((n / 3) / 3) / 3) / 3) / 3)

-- 往返: codeToPoint (pointCode x) ≡ x（6 层剥离）
codeToPoint-pointCode : ∀ x → codeToPoint (pointCode x) ≡ x
codeToPoint-pointCode (a , b , c , d , e , f) = cong₆ (λ p q r s t u → p , q , r , s , t , u) e1 e2 e3 e4 e5 e6
  where
    cong₆ : ∀ {A B C D E F G : Set} {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F}
          → (mk : A → B → C → D → E → F → G)
          → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f' → mk a b c d e f ≡ mk a' b' c' d' e' f'
    cong₆ mk refl refl refl refl refl refl = refl
    e1 : f3 (pointCode (a , b , c , d , e , f)) ≡ a
    e1 = mod3f a (finToℕ b + 3 * (finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))))
    t1 : ℕ
    t1 = finToℕ b + 3 * (finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)))
    q1 : pointCode (a , b , c , d , e , f) / 3 ≡ t1
    q1 = div3f a t1
    e2 : f3 (pointCode (a , b , c , d , e , f) / 3) ≡ b
    e2 = trans (cong f3 q1) (mod3f b (finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))))
    t2 : ℕ
    t2 = finToℕ c + 3 * (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))
    q2 : t1 / 3 ≡ t2
    q2 = div3f b t2
    e3 : f3 ((pointCode (a , b , c , d , e , f) / 3) / 3) ≡ c
    e3 = trans (cong (λ z → f3 (z / 3)) q1) (trans (cong f3 q2) (mod3f c (finToℕ d + 3 * (finToℕ e + 3 * finToℕ f))))
    t3 : ℕ
    t3 = finToℕ d + 3 * (finToℕ e + 3 * finToℕ f)
    q3 : t2 / 3 ≡ t3
    q3 = div3f c t3
    e4 : f3 (((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) ≡ d
    e4 = trans (cong (λ z → f3 (z / 3 / 3)) q1) (trans (cong (λ z → f3 (z / 3)) q2) (trans (cong f3 q3) (mod3f d (finToℕ e + 3 * finToℕ f))))
    t4 : ℕ
    t4 = finToℕ e + 3 * finToℕ f
    q4 : t3 / 3 ≡ t4
    q4 = div3f d t4
    e5 : f3 ((((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) / 3) ≡ e
    e5 = trans (cong (λ z → f3 (z / 3 / 3 / 3)) q1) (trans (cong (λ z → f3 (z / 3 / 3)) q2) (trans (cong (λ z → f3 (z / 3)) q3) (trans (cong f3 q4) (mod3f e (finToℕ f)))))
    t5 : ℕ
    t5 = finToℕ f + 3 * 0
    q5 : t4 / 3 ≡ t5
    q5 = trans (div3f e (finToℕ f)) (sym (+-identityʳ (finToℕ f)))
    e6 : f3 (((((pointCode (a , b , c , d , e , f) / 3) / 3) / 3) / 3) / 3) ≡ f
    e6 = trans (cong (λ z → f3 (z / 3 / 3 / 3 / 3)) q1) (trans (cong (λ z → f3 (z / 3 / 3 / 3)) q2) (trans (cong (λ z → f3 (z / 3 / 3)) q3) (trans (cong (λ z → f3 (z / 3)) q4) (trans (cong (λ z → f3 z) q5) (mod3f f 0)))))

-- decodePt 与 codeToPoint 的定义同构（digit 就是 f3 的迭代）
decodePt-codeToPoint : ∀ i → decodePt i ≡ codeToPoint (finToℕ i)
decodePt-codeToPoint i = refl

-- finToℕ (encodePt x) ≡ pointCode x
finToℕ-encodePt : ∀ x → finToℕ (encodePt x) ≡ pointCode x
finToℕ-encodePt x = toℕ-fromℕ< (pc<729 x)

-- 最终往返: decodePt (encodePt x) ≡ x
decodePt-encodePt : ∀ x → decodePt (encodePt x) ≡ x
decodePt-encodePt x =
  trans (decodePt-codeToPoint (encodePt x))
        (trans (cong codeToPoint (finToℕ-encodePt x))
               (codeToPoint-pointCode x))
