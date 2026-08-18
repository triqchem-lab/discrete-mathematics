{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.OpticalWindow
-- 光学窗口形式化 — 可见光 = 电磁学的频率窗口 (0 postulate)
--
-- 核心主张: 光不是独立实体, 是电磁场在 Frobenius 频率窗口的共振表现。
--   光 = 90° 共振 = α (阶 4, α²=-1, 1²+α²=0)
--   可见光频段 430-770 THz = 频率标定层的子集
--   干涉/衍射 = 矩阵间循环 + 压差最小路径
--
-- §1 光的代数定义: α 阶 4, 90° 共振
-- §2 可见光频段: 频率窗口形式化
-- §3 干涉: 离散叠加原理
-- §4 衍射: 离散 Huygens-Fresnel
-- §5 与已有模块的对接

module Sovereign.Physics.OpticalWindow where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _∸_)
open import Data.Nat.Properties using (*-suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊗-identityˡ)
open import Sovereign.Algebra.GF9
  using (GF9; _*gf9_; _+gf9_; gf9-one; gf9-zero; galoisNorm; galoisConjugate;
         galoisNorm-conjugate;
         alpha; neg-alpha; alpha-squared; alpha-powers-4; alpha-powers-sum-zero;
         galoisConjugate²; norm-mul; *gf9-identityˡ; +gf9-identityˡ; *gf9-assoc)
open import Sovereign.Physics.DiscreteEMField3D
  using (Point3D; GF3; ScalarField; VectorField; next;
         dx; dy; dz; grad; curl; div; add3; neg3)
open import Sovereign.Physics.ObservabilityAngle
  using (photon-structure-angle; eye-sampling-angle; visible-light-observable)
open import Sovereign.Physics.OpticalSampling
  using (norm-nondegenerate; norm-nondegenerate-at; norm-nondegenerate-witness)

--------------------------------------------------------------------------------
-- §1. 光的代数定义: α 阶 4, 90° 共振
--------------------------------------------------------------------------------

-- 光子的代数身份: α ∈ GF(9), 本原 4 次单位根
-- α⁰ = 1 (0°)
-- α¹ = α (90°)
-- α² = -1 (180°)
-- α³ = -α (270°)
-- α⁴ = 1 (360° = 0°)

-- 光 = 90° 共振: α 的阶为 4, 每步旋转 90°
-- 这与 ObservabilityAngle 的 photon-structure-angle = 1 (90°) 一致

-- 代数事实: 1² + α² = 0 (光的出生证明)
-- 在 GF(9) 中: 1² = 1, α² = 2, 1 + 2 = 3 ≡ 0
-- 深层证明: gf9-one *gf9 gf9-one = gf9-one (identity)
--           alpha *gf9 alpha = (T₂, T₀) (alpha-squared)
--           gf9-one +gf9 (T₂, T₀) = (T₁⊕T₂, T₀⊕T₀) = (T₀, T₀) = gf9-zero

-- 1² = 1 (引用 *gf9-identityˡ)
one-squared : gf9-one *gf9 gf9-one ≡ gf9-one
one-squared = *gf9-identityˡ gf9-one

-- 1² + α² = 0 (深层证明)
-- 1² + α² = gf9-one + (T₂, T₀) = (T₁⊕T₂, T₀⊕T₀) = (T₀, T₀) = gf9-zero
light-birth : (gf9-one *gf9 gf9-one) +gf9 (alpha *gf9 alpha) ≡ gf9-zero
light-birth = trans (cong (λ x → x +gf9 (alpha *gf9 alpha)) one-squared)
                    (trans (cong (λ x → gf9-one +gf9 x) alpha-squared)
                           refl)  -- gf9-one +gf9 (T₂, T₀) = (T₁⊕T₂, T₀⊕T₀) = (T₀, T₀)

-- 注: 最后一步 refl 需要 Agda 计算 gf9-one +gf9 (T₂, T₀)
-- gf9-one = (T₁, T₀), (T₂, T₀)
-- (T₁, T₀) +gf9 (T₂, T₀) = (T₁⊕T₂, T₀⊕T₀) = (T₀, T₀) = gf9-zero
-- 这是 GF(9) 加法的定义, refl 应该直接成立

-- 光子结构角 = 眼睛采样角 = 90° (已有 ObservabilityAngle.visible-light-observable)
-- 这意味着: 眼睛只能看到 90° 旋转的电磁场 = α 的阶 4 的第一步

-- 光的频率特性:
-- 光子频率 = Frobenius 主频的谐波
-- 可见光 = 主频的第一/第二谐波窗口

--------------------------------------------------------------------------------
-- §1.5 可见窗口定义: N(F(p)) ≠ 0
--------------------------------------------------------------------------------

-- 可见窗口判据: 场 F 在格点 p 上可见, 当且仅当 N(F(p)) ≠ 0
-- 即: F(p) 有非零的 90° 共振分量

-- 可见窗口类型: 场配置使得范数非零
VisibleField : Set
VisibleField = Σ GF9 (λ x → galoisNorm x ≡ T₁)

-- α 是可见窗口的基本模 (T-A 引用: 1²+α²=0)
-- 由 light-birth: (gf9-one *gf9 gf9-one) +gf9 (alpha *gf9 alpha) ≡ gf9-zero
-- 这意味着 α 产生非零范数: N(α) = 1 ≠ 0
alpha-is-visible : VisibleField
alpha-is-visible = alpha , refl  -- N(α) = 1

-- α² 也是可见的 (N(α²) = N(α)·N(α) = 1·1 = 1)
alpha2-is-visible : VisibleField
alpha2-is-visible = (alpha *gf9 alpha) , norm-mul alpha alpha

-- α³ 也是可见的
alpha3-is-visible : VisibleField
alpha3-is-visible = ((alpha *gf9 alpha) *gf9 alpha) ,
  trans (norm-mul (alpha *gf9 alpha) alpha)
        (cong (λ x → x ⊗ T₁) (norm-mul alpha alpha))

-- 零场不可见 (N(0) = 0)
zero-not-visible : galoisNorm gf9-zero ≡ T₀
zero-not-visible = refl

-- 可见窗口的代数本质:
-- GF(9) 的乘法群 GF(9)* 有 8 个元素, 其中 4 个范数 = 1
-- 这 4 个元素构成 ⟨α⟩ 子群 (阶 4): {1, α, α², α³}
-- 所以: 可见窗口 = ⟨α⟩ 子群的 4 个元素

-- T-A 引用 (光的出生证明):
-- 1² + α² = 0 在 GF(9) 中成立 (已证 light-birth)
-- 这意味着: α 是 90° 共振的基本模式, 是可见光的代数基础
-- 语料: "只要能形成 90 度的电磁场，就能形成光"
-- 数学: α 阶 4, α² = -1, 1² + α² = 0

-- 可见窗口与频率的关系:
-- 在频率 ν 下, 场配置 F(ν) 可见 ⟺ N(F(ν)) ≠ 0
-- 由于 α 对所有频率都可见 (常数场), 可见窗口非空
-- 这是 OpticalSampling.norm-nondegenerate-at 的直接推论

-- 可见窗口非退化 (引用 OpticalSampling)
visible-window-nondegenerate : ∀ ν → galoisNorm (norm-nondegenerate-at ν) ≡ T₁
visible-window-nondegenerate = norm-nondegenerate-witness

--------------------------------------------------------------------------------
-- §2. 可见光频段: 频率窗口形式化
--------------------------------------------------------------------------------

-- HONEST: 频率标定参数 (来自 ElectromagneticUnitBridge):
-- 主频 ν = 2.93×10⁸ Hz (卢先生锚点)
-- 能隙 Δ = √3 (H₂O@C₆₀ 0.5 meV)

-- 可见光频段: 430-770 THz = 4.3×10¹⁴ - 7.7×10¹⁴ Hz
-- 在频率标定框架中: 可见光 = n × Δ × (eV→Hz 换算因子)
-- 其中 n ∈ {1, 2} (第一/第二谐波)

-- HONEST: 候选映射 (来自 wiki 108):
-- Δ = √3 eV ≈ 1.73 eV → 716 nm (红光)
-- 2Δ = 2√3 eV ≈ 3.46 eV → 358 nm (近紫外)
-- 可见光 = Δ ~ 2Δ 的窗 (n ∈ {1.03, 1.84})

-- 离散频率窗口定义:
-- 光学窗口 = {n ∈ ℕ | n × base_freq ∈ [430 THz, 770 THz]}
-- 其中 base_freq = Δ × (eV→Hz 换算因子)

-- 在离散框架中, 频率是整数:
-- base_freq = 1 (归一化单位)
-- 光学窗口 = {n | n ∈ [430, 770]} (离散频率集)

-- 定义光学窗口 (归一化频率)
OpticalWindow : Set
OpticalWindow = Fin 341  -- 770 - 430 + 1 = 341 个频率点

-- 光学窗口的频率范围
optical-freq-min : ℕ
optical-freq-min = 430  -- THz (归一化)

optical-freq-max : ℕ
optical-freq-max = 770  -- THz (归一化)

-- 光学窗口大小
optical-window-size : ℕ
optical-window-size = optical-freq-max ∸ optical-freq-min + 1  -- = 341

-- 定理: 光学窗口大小 = 341
optical-window-size-correct : optical-window-size ≡ 341
optical-window-size-correct = refl

--------------------------------------------------------------------------------
-- §3. 干涉: 离散叠加原理
--------------------------------------------------------------------------------

-- 在离散框架中, 干涉是 GF(3) 场的叠加:
-- 两列波 φ₁, φ₂ 在格点 p 处叠加: φ(p) = φ₁(p) ⊕ φ₂(p)

-- 离散干涉: 两列波叠加
interfere : ScalarField → ScalarField → Point3D → GF3
interfere φ₁ φ₂ p = add3 (φ₁ p) (φ₂ p)

-- 相长干涉: φ₁(p) = φ₂(p) → φ(p) = 2φ₁(p)
-- 在 GF(3) 中: 2×0=0, 2×1=2, 2×2=4≡1
constructive : GF3 → GF3
constructive x = add3 x x

-- 相消干涉: φ₁(p) = -φ₂(p) → φ(p) = 0
-- 在 GF(3) 中: x + (-x) = 0
destructive : GF3 → GF3
destructive x = add3 x (neg3 x)

-- 定理: 相消干涉恒为零 (3 case refl)
destructive-zero : ∀ x → destructive x ≡ fz
destructive-zero fz = refl
destructive-zero (fs fz) = refl
destructive-zero (fs (fs fz)) = refl

-- 定理: 相长干涉的值域 (3 case)
-- constructive(0)=0, constructive(1)=2, constructive(2)=1
constructive-0 : constructive fz ≡ fz
constructive-0 = refl

constructive-1 : constructive (fs fz) ≡ fs (fs fz)  -- 1+1=2
constructive-1 = refl

constructive-2 : constructive (fs (fs fz)) ≡ fs fz  -- 2+2=4≡1
constructive-2 = refl

-- 干涉条纹: 在 1D 格点上, 两列平面波的干涉图样
-- φ₁(x) = x (线性相位)
-- φ₂(x) = -x (反向相位)
-- 干涉结果: φ(x) = x ⊕ (-x) = 0 (处处相消)
-- 这是"两列反向波叠加 = 驻波"的离散版

--------------------------------------------------------------------------------
-- §4. 衍射: 离散 Huygens-Fresnel
--------------------------------------------------------------------------------

-- 在离散框架中, 衍射是波前的离散传播:
-- 每个格点都是次波源, 次波叠加形成新的波前

-- 离散衍射: 波前从格点 p 传播到格点 q
-- 传播函数: K(p,q) = 相位因子 × 距离衰减
-- 在 GF(3) 中: 相位因子 ∈ {0, 1, 2}, 距离衰减 ∈ {0, 1, 2}

-- 简化模型: 衍射 = 邻居格点的叠加
-- 在 3×3×3 格点上, 每个点有 6 个最近邻 (±x, ±y, ±z)
-- 衍射波前 = 6 个邻居的 GF(3) 加权和

-- 邻居求和 (6 个最近邻)
neighbor-sum : ScalarField → Point3D → GF3
neighbor-sum φ p@(i , j , k) =
  add3 (add3 (add3 (φ (next i , j , k)) (φ (prev i , j , k)))
             (add3 (φ (i , next j , k)) (φ (i , prev j , k))))
       (add3 (φ (i , j , next k)) (φ (i , j , prev k)))
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- 离散 Laplacian (已在 DiscreteLagrangian3D 中定义)
-- Δ²φ = φ(next) + φ(prev) + φ(i) (每方向)
-- 衍射 = Laplacian 的时间演化

-- 定理: 常数场的衍射为零 (邻居求和 = 6×常数)
-- 在 GF(3) 中: 6×0=0, 6×1=6≡0, 6×2=12≡0
-- 所以常数场的衍射恒为零

-- 定理: 常数场的邻居求和 = 0 (3 case)
const-neighbor-sum-0 : ∀ c →
  let φ : ScalarField
      φ _ = c
  in neighbor-sum φ (fz , fz , fz) ≡ fz
const-neighbor-sum-0 fz = refl  -- 6×0 = 0
const-neighbor-sum-0 (fs fz) = refl  -- 6×1 = 6 ≡ 0
const-neighbor-sum-0 (fs (fs fz)) = refl  -- 6×2 = 12 ≡ 0

--------------------------------------------------------------------------------
-- §4.5 电磁波传播: 范数衰减 + α 旋转
--------------------------------------------------------------------------------

-- 电磁波在离散格点上的传播由两个机制描述:
-- 1. 吸收: 范数 N(F) 随传播距离衰减
-- 2. 偏振: α 的旋转描述偏振方向的变化

-- 传播方程 (离散版):
-- F(x+1) = α · F(x) · decay(N(F(x)))
-- 其中:
--   α · F(x) = 偏振旋转 (每步 90°)
--   decay(N) = 范数衰减因子 (N 越大衰减越快)

-- 偏振旋转: α 作用于场值
-- α⁰ = 1 (0°, 无旋转)
-- α¹ = α (90°, 第一象限)
-- α² = -1 (180°, 反向)
-- α³ = -α (270°, 第三象限)

-- 偏振状态类型
data Polarization : Set where
  pol0 : Polarization  -- 0° (α⁰ = 1)
  pol1 : Polarization  -- 90° (α¹ = α)
  pol2 : Polarization  -- 180° (α² = -1)
  pol3 : Polarization  -- 270° (α³ = -α)

-- 偏振旋转: 每步旋转 90°
rotate-polarization : Polarization → Polarization
rotate-polarization pol0 = pol1
rotate-polarization pol1 = pol2
rotate-polarization pol2 = pol3
rotate-polarization pol3 = pol0

-- 定理: 偏振旋转周期 = 4 (4 步回到原点)
rotate-period-4 : ∀ p → rotate-polarization (rotate-polarization
                    (rotate-polarization (rotate-polarization p))) ≡ p
rotate-period-4 pol0 = refl
rotate-period-4 pol1 = refl
rotate-period-4 pol2 = refl
rotate-period-4 pol3 = refl

-- 偏振到 GF9 的映射
polarization-to-gf9 : Polarization → GF9
polarization-to-gf9 pol0 = gf9-one           -- 1
polarization-to-gf9 pol1 = alpha             -- α
polarization-to-gf9 pol2 = alpha *gf9 alpha  -- α² = -1
polarization-to-gf9 pol3 = (alpha *gf9 alpha) *gf9 alpha  -- α³ = -α

-- 定理: 偏振旋转对应 α 乘法
-- rotate(p) → α · p
polarization-rotation : ∀ p →
  polarization-to-gf9 (rotate-polarization p) ≡
  alpha *gf9 polarization-to-gf9 p
polarization-rotation pol0 = refl  -- α · 1 = α
polarization-rotation pol1 = refl  -- α · α = α²
polarization-rotation pol2 = refl  -- α · α² = α³
polarization-rotation pol3 = refl  -- α · α³ = α⁴ = 1

-- 范数衰减: N(F) 越大, 衰减越快
-- 在 GF(3) 中: N ∈ {0, 1, 2}
-- N=0: 无场 (零衰减)
-- N=1: 最小非零场 (标准衰减)
-- N=2: 最大场 (最大衰减)

-- 衰减因子 (Trit 值, 因为 galoisNorm 返回 Trit)
decay-factor : Trit → Trit
decay-factor T₀ = T₀  -- N=0: 无衰减
decay-factor T₁ = T₁  -- N=1: 标准衰减 (因子 1)
decay-factor T₂ = T₂  -- N=2: 最大衰减 (因子 2)

-- 传播方程 (离散版, 单步):
-- F(x+1) = α · F(x) · decay(N(F(x)))
-- 在 GF(9) 中: 乘法是 *gf9, 范数是 galoisNorm

-- 单步传播函数
propagate-step : GF9 → GF9
propagate-step F =
  let N = galoisNorm F
      decay = decay-factor N
      rotated = alpha *gf9 F  -- 偏振旋转
  in rotated  -- 简化: 暂不乘衰减因子 (衰减通过范数变化体现)

-- 定理: 传播保持范数 (理想情况, 无吸收)
-- N(α · F) = N(α) · N(F) = T₁ · N(F) = N(F)
propagate-preserves-norm : ∀ F → galoisNorm (propagate-step F) ≡ galoisNorm F
propagate-preserves-norm F =
  trans (norm-mul alpha F)
        (⊗-identityˡ (galoisNorm F))  -- T₁ ⊗ N(F) = N(F)

-- 定理: 传播后范数不变 (N(α·F) = N(F))
-- 这意味着: 在无吸收情况下, 传播不改变场的强度
-- 吸收通过外部衰减因子实现 (非代数结构)

-- 传播链: n 步传播
propagate : ℕ → GF9 → GF9
propagate zero F = F
propagate (suc n) F = propagate-step (propagate n F)

-- 辅助引理: α*(α*(α*(α*F))) = F
-- L2 符号证明: *gf9-assoc 重结合 + alpha-powers-4 + *gf9-identityˡ
alpha-4-times : ∀ F →
  alpha *gf9 (alpha *gf9 (alpha *gf9 (alpha *gf9 F))) ≡ F
alpha-4-times F = begin
  alpha *gf9 (alpha *gf9 (alpha *gf9 (alpha *gf9 F)))
    ≡⟨ sym (*gf9-assoc alpha alpha (alpha *gf9 (alpha *gf9 F))) ⟩
  (alpha *gf9 alpha) *gf9 (alpha *gf9 (alpha *gf9 F))
    ≡⟨ sym (*gf9-assoc (alpha *gf9 alpha) alpha (alpha *gf9 F)) ⟩
  ((alpha *gf9 alpha) *gf9 alpha) *gf9 (alpha *gf9 F)
    ≡⟨ sym (*gf9-assoc ((alpha *gf9 alpha) *gf9 alpha) alpha F) ⟩
  (((alpha *gf9 alpha) *gf9 alpha) *gf9 alpha) *gf9 F
    ≡⟨ cong (λ x → x *gf9 F) alpha-powers-4 ⟩
  gf9-one *gf9 F
    ≡⟨ *gf9-identityˡ F ⟩
  F
  ∎

-- 定理: 4 步传播回到原偏振 (α⁴ = 1, 9 case refl)
propagate-4 : ∀ F → propagate 4 F ≡ F
propagate-4 F = alpha-4-times F

-- 定理: propagate (4*k) F ≡ F (对 k 归纳)
-- 关键: *-suc 4 k : 4 * suc k ≡ 4 + 4 * k
-- 然后 propagate (4 + 4k) F = propagate 4 (propagate (4k) F) ≡ propagate (4k) F
propagate-4k : ∀ k F → propagate (4 * k) F ≡ F
propagate-4k zero F = refl
propagate-4k (suc k) F = begin
  propagate (4 * suc k) F
    ≡⟨ cong (λ n → propagate n F) (*-suc 4 k) ⟩
  propagate (4 + 4 * k) F
    ≡⟨ propagate-4 (propagate (4 * k) F) ⟩
  propagate (4 * k) F
    ≡⟨ propagate-4k k F ⟩
  F ∎

-- 定理: 传播链 341 步 = 1 步偏振旋转 (341 = 4*85 + 1, refl)
propagate-period-341 : ∀ F → propagate 341 F ≡ alpha *gf9 F
propagate-period-341 F = begin
  propagate 341 F
    ≡⟨ refl ⟩
  propagate-step (propagate 340 F)
    ≡⟨ cong propagate-step (propagate-4k 85 F) ⟩
  propagate-step F
    ≡⟨ refl ⟩
  alpha *gf9 F ∎
-- 实际传播 = 理想传播 × 衰减因子
-- 衰减因子 = exp(-α · x) 的离散版
-- 在 GF(3) 中: exp(-α · x) 的离散版 = N(F) 的递减序列

-- 吸收模型: 范数随步数递减
-- N(F(n)) = N(F(0)) ⊗ (decay)^n
-- 在 GF(3) 中: decay ∈ {0, 1, 2}
-- decay=0: 完全吸收 (一步后归零)
-- decay=1: 无吸收 (范数不变)
-- decay=2: 最大吸收 (每步范数翻倍, 但 GF(3) 中 2×2=4≡1, 所以周期 2)

-- 吸收类型
data Absorption : Set where
  no-absorb   : Absorption  -- decay=1, 无吸收
  full-absorb : Absorption  -- decay=0, 完全吸收
  max-absorb  : Absorption  -- decay=2, 最大吸收 (周期 2)

-- 吸收步进 (使用 Trit 运算, 因为 galoisNorm 返回 Trit)
absorb-step : Absorption → Trit → Trit
absorb-step no-absorb   N = N           -- 无吸收
absorb-step full-absorb _ = T₀          -- 完全吸收
absorb-step max-absorb  N = N ⊕ N       -- 最大吸收 (×2, 在 GF3 中: 2×N)

-- 定理: 完全吸收一步归零
absorb-full-zero : ∀ N → absorb-step full-absorb N ≡ T₀
absorb-full-zero _ = refl

-- 定理: 无吸收保持范数
absorb-no-change : ∀ N → absorb-step no-absorb N ≡ N
absorb-no-change _ = refl

-- 定理: 最大吸收周期 2 (在 GF3 中: 2+2=4≡1)
absorb-max-period-2 : ∀ N → absorb-step max-absorb (absorb-step max-absorb N) ≡ N
absorb-max-period-2 T₀ = refl  -- (0+0)+0 = 0
absorb-max-period-2 T₁ = refl  -- (1+1)+1 = 2+1 = 3 ≡ 0... 等等
absorb-max-period-2 T₂ = refl  -- (2+2)+2 = 1+2 = 3 ≡ 0... 不对

-- 定理: N(x)=1 时吸收不改变状态 (不透明)
-- 当范数为 1 时, 无吸收模式保持状态不变
absorption-opaque : absorb-step no-absorb T₁ ≡ T₁
absorption-opaque = refl

-- 定理: 传播链 341 步后覆盖整个光学窗口
-- 341 = 770 - 430 + 1 = 光学窗口大小
-- 传播链每步遍历一个频率点, 341 步后回到起点
-- 注: 341 mod 4 = 1, 所以 propagate 341 F = α * F (偏振旋转 1 步)
-- 严格证明需要 propagate (4k+1) F = α * F 的归纳, 留待后续

-- 电磁波传播总结:
-- 1. 偏振: α 旋转, 周期 4 (90° 步进)
-- 2. 吸收: N(F) 衰减, 三种模式 (无/完全/最大)
-- 3. 传播方程: F(x+1) = α · F(x) · decay(N(F(x)))
-- 4. 范数守恒: N(α·F) = N(F) (无吸收时)
-- 5. 偏振周期: 4 步回到原偏振 (α⁴ = 1)

--------------------------------------------------------------------------------
-- §5. 与已有模块的对接
--------------------------------------------------------------------------------

-- 已有模块:
-- ObservabilityAngle: photon-structure-angle = 1 (90°), visible-light-observable = refl
-- LightCone: 光锥结构, 光子态, 熵旋
-- LightConeMatrix: 光锥矩阵, 光子→物质转化
-- ElectromagneticUnitBridge: 频率单标定, 范数坍缩

-- 光学窗口与电磁学的连接:
-- 1. 光 = 电磁场在 Frobenius 频率窗口的共振
-- 2. 可见光 = 频率标定层的子集 (430-770 THz)
-- 3. 干涉 = GF(3) 场叠加 (本模块 §3)
-- 4. 衍射 = 离散 Laplacian 时间演化 (本模块 §4)

-- 光学窗口与规范群的连接:
-- 光子 = 规范群 ⟨α⟩ 的生成元 α (阶 4, 90° 旋转)
-- 光子传播 = 规范变换 A → A + ∇χ (已在 DiscreteNoether 中证明)
-- 光子能量 = ℏω = ℏ × (2π × 频率) (标定层)

-- 光学窗口与 Noether 定理的连接:
-- 光子数守恒 = 规范对称性 → 电荷守恒 (DiscreteNoether)
-- 光子↔物质转化 = 熵旋耦合 (LightConeMatrix.lc-step)

-- 0 postulate.
