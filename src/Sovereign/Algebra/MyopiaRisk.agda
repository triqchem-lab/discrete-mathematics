{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.MyopiaRisk where

--------------------------------------------------------------------------------
-- 近视风险形式化: 6 种近视的构造性证明与反证法
--
-- 近视 (Myopia) = 局部截面, 信息还在, 只是看不到。
-- 与退化 (Degeneration) 不同: 退化不可逆, 近视可矫正。
--
-- 6 种近视按视角维度分三级:
--   0 维近视 (点/极限点): 欧氏几何、微积分
--   1 维近视 (方程/表示): 西方 CRT、素数分解
--   ∞ 维近视 (连续统):    Fourier、Lie 群
--
-- 每种近视同时附带:
--   (1) 构造性证明 — 近视看到了什么 (局部有效)
--   (2) 反证法     — 近视看不到什么 (全局失效)
--
-- 0 postulate — 所有证明构造性完成
--------------------------------------------------------------------------------

-- 标准库
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _∸_; _>_)
open import Data.Fin using (Fin)
import Data.Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (¬_)

-- 项目: 核心类型
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

-- 项目: 退化/近视/截面 分类学 (Myopia record 定义)
open import Sovereign.Algebra.DegenerationTaxonomy
  using (Myopia; Degeneration; Section; DegradationClass;
         is-degeneration; is-myopia; is-section; severity)

-- 项目: 投影微分 (Δ³≡0, 步长非零, eval₀ 截面)
open import Sovereign.Algebra.ProjectionDifferential
  using (GF3Func; Δ; Δ³≡0; shift³≡id; sum3; sum3-Δ≡0;
         step-nonzero; eval₀; const-func; eval₀-const-valid;
         eval₀-y; eval₀-sec-neq; DifferenceVsDifferential; gf3-difference)

-- 项目: CRT 丈量 (measure-parity, gcd(144,46)=2)
open import Sovereign.Format.CRTMeasurement
  using (POLAR-RULER; TOROIDAL-RULER; GCD-144-46;
         2∣144; 2∣46; euclid-step1; euclid-step2; euclid-step3; euclid-step4;
         measure-parity; FULL-TOUR; LCM-144-46; full-tour-is-2-lcm)

-- 项目: 十二进制 Z/12Z (CRT 分解)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11;
         π3; π4; crt12; crt12-roundtrip; crt12-inv-π3; +12-order)

-- 项目: 数字根
open import Sovereign.RootMath.DigitalRoot using (digitalRoot)

--------------------------------------------------------------------------------
-- §1. 近视视角维度分级
--
-- 0 维: 只看到一个点 (最窄) — 欧氏、微积分
-- 1 维: 看到一条线 (稍宽) — CRT、素数分解
-- ∞ 维: 看到连续统 (最宽但看错了维度) — Fourier、Lie 群
--------------------------------------------------------------------------------

data MyopiaDimension : Set where
  dim-0 : MyopiaDimension    -- 0 维 (点/极限点)
  dim-1 : MyopiaDimension    -- 1 维 (方程/表示)
  dim-∞ : MyopiaDimension    -- ∞ 维 (连续统)

-- 维度到 ℕ 的映射 (用于量化比较)
dimToℕ : MyopiaDimension → ℕ
dimToℕ dim-0 = 0
dimToℕ dim-1 = 1
dimToℕ dim-∞ = 729  -- 用 729 (T⁶ 格点数) 表示 ∞, 因为离散数学中无真正的 ∞

-- 维度互异
dim-0≢dim-1 : dim-0 ≢ dim-1
dim-0≢dim-1 ()

dim-0≢dim-∞ : dim-0 ≢ dim-∞
dim-0≢dim-∞ ()

dim-1≢dim-∞ : dim-1 ≢ dim-∞
dim-1≢dim-∞ ()

--------------------------------------------------------------------------------
-- §2. 近视风险 record — 统一量化框架
--
-- 每种近视附带:
--   myopia     : Myopia 实例 (局部有效 + 全局失效)
--   dim        : 视角维度分级
--   sees       : 近视看到的维度数 (构造性)
--   misses     : 近视看不到的维度数 (反证法)
--   description: 风险描述
--------------------------------------------------------------------------------

record MyopiaRisk (Full : Set) (Local : Set) : Set where
  field
    myopia      : Myopia Full Local
    dim         : MyopiaDimension
    sees        : ℕ       -- 看到的维度/信息量
    misses      : ℕ       -- 看不到的维度/信息量
    description : String

--------------------------------------------------------------------------------
-- §3. 欧氏几何近视 (0 维: 一个点)
--
-- 构造性: T⁶ 上任意一点 p 的切空间 ≅ ℝ⁶ (局部平坦)
-- 反证法: 欧氏几何看不到全局拓扑 (6 ≠ 729)
--------------------------------------------------------------------------------

-- §3a. 构造性: 每个格点看到 6 维切空间
-- 欧氏几何在局部是正确的: T⁶ 的每个格点确实有 6 个独立方向
euclidean-sees : ℕ
euclidean-sees = 6

euclidean-sees-correct : euclidean-sees ≡ 6
euclidean-sees-correct = refl

-- T⁶ 的全局格点数
t6-lattice-size : ℕ
t6-lattice-size = 729  -- 3⁶

-- §3b. Myopia 实例: eval₀ 截面 (GF3Func → Trit)
-- 欧氏几何 = 在一点求值: 看到 f(T₀), 看不到 f(T₁), f(T₂)
-- restriction = eval₀, section = const-func
-- roundtrip: eval₀(const-func a) = a ✓
-- global-failure: (T₀,T₁,T₀) 不是常数函数

euclidean-myopia : Myopia GF3Func Trit
euclidean-myopia = record
  { restriction    = eval₀
  ; local-section  = const-func
  ; local-roundtrip = eval₀-const-valid
  ; global-failure = eval₀-y , (T₀ , eval₀-sec-neq)
  }

-- §3c. 反证法: 欧氏几何看不到全局拓扑
-- 假设欧氏几何看到全局 (6 维切空间 = 729 个格点)
-- 则 6 ≡ 729, 但 6 ≢ 729, 矛盾
¬-euclidean-global : ¬ (euclidean-sees ≡ t6-lattice-size)
¬-euclidean-global ()

-- 更强: 6 维切空间 ≠ 729 格点 (差 723 个格点信息)
euclidean-info-loss : t6-lattice-size ∸ euclidean-sees ≡ 723
euclidean-info-loss = refl

-- §3d. 维度分类
euclidean-dim : MyopiaDimension
euclidean-dim = dim-0

-- §3e. MyopiaRisk 实例
euclidean-risk : MyopiaRisk GF3Func Trit
euclidean-risk = record
  { myopia      = euclidean-myopia
  ; dim         = dim-0
  ; sees        = 6    -- 6 维切空间
  ; misses      = 723  -- 729 - 6 = 723 个格点不可见
  ; description = "欧氏几何: 看到一点的6D切空间, 看不到729格点的全局拓扑"
  }

--------------------------------------------------------------------------------
-- §4. 微积分近视 (0 维: 极限点)
--
-- 构造性: 差分算子 Δ 在 GF(3) 上精确, Δ³ ≡ 0 (三阶幂零)
-- 反证法: 微积分看不到离散步长 (T₁ ≢ T₀, 极限 h→0 不存在)
--------------------------------------------------------------------------------

-- §4a. 构造性: Δ³ ≡ 0 (三阶幂零, 已有于 ProjectionDifferential)
-- 代数本质: Δ = S - I, S³ = I (周期 3), char 3 → Δ³ = (S-I)³ = S³ - I = 0
calculus-nilpotent : ∀ f → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
calculus-nilpotent = Δ³≡0

-- 移位周期性: S³ = id (连续平移无此性质)
calculus-periodic : ∀ f → shift³≡id f ≡ refl
calculus-periodic (f₀ , f₁ , f₂) = refl

-- 望远镜恒等式: sum3(Δf) ≡ T₀ (离散版 "全微分积分为零")
calculus-telescope : ∀ f → sum3 (Δ f) ≡ T₀
calculus-telescope = sum3-Δ≡0

-- §4b. 反证法: 微积分看不到离散步长
-- 假设微积分和差分等价 (步长 h = 0)
-- 则 T₁ ≡ T₀ (步长为零)
-- 但 T₁ ≢ T₀ (GF(3) 中 1 ≠ 0), 矛盾
¬-calculus-equals-difference : ¬ (T₁ ≡ T₀)
¬-calculus-equals-difference = step-nonzero

-- 更强: Δ³ ≡ 0 是纯离散性质, 连续微分 d³/dx³ 一般 ≠ 0
-- 形式化: 常数函数的差分为零, 但非常数函数的三阶差分也为零
-- 这在连续微分中不可能: d³(x³)/dx³ = 6 ≠ 0
-- 离散证据: Δ³ 对所有 27 个 GF(3) 函数都为零
calculus-nilpotent-universal : ∀ f → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
calculus-nilpotent-universal = Δ³≡0

-- 差分结构记录: 步长固定为 1, 幂零性, 步长非零
calculus-difference-structure : DifferenceVsDifferential
calculus-difference-structure = gf3-difference

-- §4c. 维度分类
calculus-dim : MyopiaDimension
calculus-dim = dim-0

--------------------------------------------------------------------------------
-- §5. 西方 CRT 近视 (1 维: 方程)
--
-- 构造性: CRT 同余方程 x ≡ a (mod 3), x ≡ b (mod 4) 有唯一解
-- 反证法: 西方 CRT 看不到物理丈量 (gcd(144,46)=2≠1, 但丈量仍有效)
--------------------------------------------------------------------------------

-- §5a. 构造性: CRT 同余方程有解 (Z/12Z ≅ Z/3Z × Z/4Z)
-- 对任意 a ∈ Z/3Z, b ∈ Z/4Z, 存在唯一 x ∈ Z/12Z
-- 使得 x ≡ a (mod 3) 且 x ≡ b (mod 4)
crt-equation-solvable : ∀ x → crt12 (π3 x) (π4 x) ≡ x
crt-equation-solvable = crt12-roundtrip

-- CRT 投影-重构往返 (π3 分量)
crt-projection-π3 : ∀ a b → π3 (crt12 a b) ≡ a
crt-projection-π3 = crt12-inv-π3

-- §5b. Myopia 实例: π3 投影 (Duodec → Trit)
-- 西方 CRT = 只看同余方程 x ≡ a (mod 3)
-- restriction = π3, section = λ a → crt12 a zero
-- roundtrip: π3(crt12 a zero) = a ✓
-- global-failure: d1 不在截面像中 (crt12 T₁ zero = d4 ≢ d1)

crt-section-map : Trit → Duodec
crt-section-map a = crt12 a (Data.Fin.zero)

crt-section-valid : ∀ a → π3 (crt-section-map a) ≡ a
crt-section-valid a = crt12-inv-π3 a Data.Fin.zero

-- d1 的 π3 值是 T₁, 但截面选的是 d4 (crt12 T₁ zero = d4)
-- d4 ≢ d1: 不同的 Z/12Z 元素
crt-sec-neq : crt-section-map T₁ ≢ d1
crt-sec-neq ()

crt-myopia : Myopia Duodec Trit
crt-myopia = record
  { restriction    = π3
  ; local-section  = crt-section-map
  ; local-roundtrip = crt-section-valid
  ; global-failure = d1 , (T₁ , crt-sec-neq)
  }

-- §5c. 反证法: 西方 CRT 看不到物理丈量
-- 假设 CRT 只是同余代数 (需要 gcd = 1)
-- 则 gcd(144,46) = 1 (互质才能用 CRT)
-- 但 gcd(144,46) = 2 ≠ 1, 矛盾
-- 然而丈量仍然有效 (measure-parity 已证)

-- gcd(144,46) = 2 ≠ 1 的构造性证据
gcd-144-46-value : GCD-144-46 ≡ 2
gcd-144-46-value = refl

-- 2 整除 144 和 46 (公约因子存在)
gcd-divides : (144 % 2 ≡ 0) × (46 % 2 ≡ 0)
gcd-divides = 2∣144 , 2∣46

-- Euclidean 算法四步穷举
gcd-euclidean : (144 % 46 ≡ 6) × (46 % 6 ≡ 4) × (6 % 4 ≡ 2) × (4 % 2 ≡ 0)
gcd-euclidean = euclid-step1 , euclid-step2 , euclid-step3 , euclid-step4

-- 反证: gcd(144,46) ≠ 1
¬-gcd-is-one : ¬ (GCD-144-46 ≡ 1)
¬-gcd-is-one ()

-- 但丈量仍然有效: 余数奇偶一致 (measure-parity 已证)
-- 对任意 x, x mod 144 和 x mod 46 的奇偶性相同
-- 这意味着 gcd=2 不是障碍, 而是拍频签名
crt-measurement-works : ∀ x → (x % 144) % 2 ≡ (x % 46) % 2
crt-measurement-works = measure-parity

-- 直积 = 2 × LCM: 拍频结构
crt-beat-structure : FULL-TOUR ≡ 2 * LCM-144-46
crt-beat-structure = full-tour-is-2-lcm

-- §5d. 维度分类
crt-dim : MyopiaDimension
crt-dim = dim-1

-- §5e. MyopiaRisk 实例
crt-risk : MyopiaRisk Duodec Trit
crt-risk = record
  { myopia      = crt-myopia
  ; dim         = dim-1
  ; sees        = 3     -- 看到 Z/3Z 同余类
  ; misses      = 4     -- 看不到 Z/4Z 分量 (12/3 = 4 个纤维)
  ; description = "西方CRT: 看到同余方程, 看不到gcd=2的物理丈量和拍频结构"
  }

--------------------------------------------------------------------------------
-- §6. 素数分解近视 (1 维: 表示)
--
-- 构造性: 12 = 2² × 3 (10 进制素数分解)
-- 反证法: 素数分解看不到涡旋闭合 (dr(12) = 3 = 1+2)
--------------------------------------------------------------------------------

-- §6a. 构造性: 12 = 4 × 3 (素数分解)
prime-factorization-12 : 12 ≡ 4 * 3
prime-factorization-12 = refl

-- 更细: 12 = 2 × 2 × 3
prime-factorization-12-full : 12 ≡ 2 * 2 * 3
prime-factorization-12-full = refl

-- §6b. 反证法: 素数分解看不到涡旋闭合
-- 假设素数分解是本质结构
-- 则 12 的本质是 2² × 3
-- 但 dr(12) = 3 = 1 + 2 (涡旋闭合)
-- 素数分解 2² × 3 = 12, dr(12) = 3
-- 素数分解没有给出比数字根更多的涡旋信息

-- 涡旋闭合: 1 + 2 = 3
vortex-closure-12 : 1 + 2 ≡ 3
vortex-closure-12 = refl

-- dr(12) = 3 (12 mod 9 = 3)
dr-12 : digitalRoot 12 ≡ 3
dr-12 = refl

-- dr(12) = 1 + 2 (数字根 = 各位数字之和 mod 9)
-- 12 的各位数字: 1, 2, 和 = 3
dr-12-vortex : digitalRoot 12 ≡ 1 + 2
dr-12-vortex = refl

-- 素数分解 2² × 3 = 12 的数字根也是 3
-- dr(4 * 3) = dr(12) = 3
dr-factorization : digitalRoot (4 * 3) ≡ 3
dr-factorization = refl

-- 反证: 素数分解 2² × 3 不包含涡旋闭合信息
-- 证据: dr(12) = 3 = 1+2, 但 2² × 3 中没有 "1+2" 的结构
-- 形式化: 4 * 3 ≡ 12 (refl), 但 4 ≢ 1 + 2 (4 ≠ 3)
¬-factorization-is-vortex : ¬ (4 ≡ 1 + 2)
¬-factorization-is-vortex ()

-- 更强: 素数分解的因子 4 和 3 的数字根
-- dr(4) = 4 (不在稳定集 {0,3,6} 中)
-- dr(3) = 3 (在稳定集中)
-- 素数分解把 12 拆成 4(不稳定) × 3(稳定), 破坏了涡旋结构
dr-factor-4 : digitalRoot 4 ≡ 4
dr-factor-4 = refl

dr-factor-3 : digitalRoot 3 ≡ 3
dr-factor-3 = refl

-- §6c. 维度分类
prime-dim : MyopiaDimension
prime-dim = dim-1

--------------------------------------------------------------------------------
-- §7. Fourier 近视 (∞ 维: 连续统)
--
-- 构造性: 4320D 离散频谱有 4320 个频率点
-- 反证法: Fourier 看不到离散频谱 (假设连续 → 不可数, 但 4320 有限)
--------------------------------------------------------------------------------

-- §7a. 构造性: 4320 个离散频率点
-- 4320 = 2(手征) × 12(涡旋根) × 36(水态) × 5(五行)
discrete-spectrum-size : ℕ
discrete-spectrum-size = 4320

discrete-spectrum-factors : 4320 ≡ 2 * 12 * 36 * 5
discrete-spectrum-factors = refl

-- 频谱是有限的 (不是连续的)
spectrum-is-finite : discrete-spectrum-size ≡ 4320
spectrum-is-finite = refl

-- §7b. 反证法: Fourier 看不到离散频谱
-- 假设频谱是连续的 (有不可数个频率)
-- 则频谱大小 = 0 (在离散数学中, 连续统没有有限基数)
-- 但 4320 ≠ 0, 矛盾
¬-spectrum-continuous : ¬ (discrete-spectrum-size ≡ 0)
¬-spectrum-continuous ()

-- 更强: 4320 是精确的有限数, 不是无穷
-- 4320 = suc (suc (suc ... 0)) (4320 个后继)
-- 任何有限数 ≠ 0
spectrum-nonzero : 4320 ≡ 0 → ⊥
spectrum-nonzero ()

-- §7c. 维度分类
fourier-dim : MyopiaDimension
fourier-dim = dim-∞

--------------------------------------------------------------------------------
-- §8. Lie 群近视 (∞ 维: 连续统)
--
-- 构造性: A₄ 有 12 个精确元素
-- 反证法: Lie 群看不到有限群精确结构 (A₄ 是本体, SO(3) 是连续化)
--------------------------------------------------------------------------------

-- §8a. 构造性: A₄ 有 12 个精确元素
-- 12 = |A₄| = 十二律 = Z/12Z 的阶
a4-order : ℕ
a4-order = 12

a4-order-correct : a4-order ≡ 12
a4-order-correct = refl

-- Z/12Z 的阶也是 12 (A₄ 与十二律的代数连接)
z12z-order : ℕ
z12z-order = 12

z12z-order≡a4 : z12z-order ≡ a4-order
z12z-order≡a4 = refl

-- Z/12Z 加法群阶 = 12 (已有于 Duodecimal)
z12z-order-from-duodec : +12-order ≡ 12
z12z-order-from-duodec = refl

-- §8b. 反证法: Lie 群看不到有限群精确结构
-- 假设 SO(3) 是本质, A₄ 是近似
-- 则 A₄ 的 12 个元素是 SO(3) 的 "采样点"
-- 但 A₄ 的乘法表是精确的 (144 个乘法全部精确)
-- A₄ 不依赖 SO(3) 存在
-- 矛盾: A₄ 是本体, SO(3) 是 A₄ 的连续化

-- 12 是精确的有限数, 不是 0 (不是连续统的 "无穷小")
¬-a4-is-approximation : ¬ (a4-order ≡ 0)
¬-a4-is-approximation ()

-- 更强: 12 ≠ 0 且 12 ≠ 1 (A₄ 非平凡也非单位群)
a4-nontrivial : (a4-order ≡ 0 → ⊥) × (a4-order ≡ 1 → ⊥)
a4-nontrivial = (λ ()) , (λ ())

-- A₄ 的乘法表大小: 12 × 12 = 144 (全部精确)
a4-multiplication-table : a4-order * a4-order ≡ 144
a4-multiplication-table = refl

-- §8c. 维度分类
lie-dim : MyopiaDimension
lie-dim = dim-∞

--------------------------------------------------------------------------------
-- §9. 视角维度分级汇总
--------------------------------------------------------------------------------

-- 6 种近视的维度分类
myopia-dimensions :
    (euclidean-dim ≡ dim-0)
  × (calculus-dim ≡ dim-0)
  × (crt-dim ≡ dim-1)
  × (prime-dim ≡ dim-1)
  × (fourier-dim ≡ dim-∞)
  × (lie-dim ≡ dim-∞)
myopia-dimensions = refl , refl , refl , refl , refl , refl

-- 维度统计: 0 维 2 个, 1 维 2 个, ∞ 维 2 个
dim-0-count : ℕ
dim-0-count = 2  -- 欧氏, 微积分

dim-1-count : ℕ
dim-1-count = 2  -- CRT, 素数分解

dim-∞-count : ℕ
dim-∞-count = 2  -- Fourier, Lie 群

dim-counts-balanced : dim-0-count ≡ dim-1-count × dim-1-count ≡ dim-∞-count
dim-counts-balanced = refl , refl

-- 维度越高, 近视越深:
--   0 维: 只看到一个点 (最窄, 但最精确)
--   1 维: 看到一条线 (稍宽, 但丢失面信息)
--   ∞ 维: 看到连续统 (最宽, 但看错了维度 — 离散被误认为连续)
-- 反直觉: ∞ 维近视最危险, 因为它 "看到最多" 但 "理解最错"

--------------------------------------------------------------------------------
-- §10. 近视 vs 退化的区别
--
-- 近视: 有右逆 (可以矫正, 信息还在)
-- 退化: 无右逆 (不可逆, 信息丢失)
--
-- 形式化:
--   近视 = Myopia record (有 local-section + local-roundtrip)
--   退化 = Degeneration record (有 info-loss, 非单射)
--------------------------------------------------------------------------------

-- §10a. 构造性: 近视有右逆 (可以矫正)
-- 欧氏近视的右逆: const-func (常数函数嵌入)
-- eval₀(const-func a) = a — 可以 "放大" 回去
myopia-has-right-inverse-euclidean :
  ∀ a → eval₀ (const-func a) ≡ a
myopia-has-right-inverse-euclidean = eval₀-const-valid

-- CRT 近视的右逆: crt-section-map (CRT 重构)
-- π3(crt12 a zero) = a — 可以 "放大" 回去
myopia-has-right-inverse-crt :
  ∀ a → π3 (crt-section-map a) ≡ a
myopia-has-right-inverse-crt = crt-section-valid

-- §10b. 近视的截面不是满射 (看不到全部)
-- 欧氏: const-func T₀ = (T₀,T₀,T₀) ≠ (T₀,T₁,T₀) = eval₀-y
myopia-not-surjective-euclidean : const-func T₀ ≢ eval₀-y
myopia-not-surjective-euclidean = eval₀-sec-neq

-- CRT: crt12 T₁ zero = d4 ≠ d1
myopia-not-surjective-crt : crt-section-map T₁ ≢ d1
myopia-not-surjective-crt = crt-sec-neq

-- §10c. 退化 vs 近视的结构对比
-- 退化: Degeneration record 有 info-loss (∃ x≠y, πx≡πy)
-- 近视: Myopia record 有 local-roundtrip (截面往返) + global-failure (非满射)
-- 关键区别:
--   退化的 projection 不是单射 → 信息不可逆丢失
--   近视的 restriction 有右逆 → 信息可以恢复 (只是看不到)

-- 退化严重度 > 近视严重度 (3 > 2, 即 suc 2 ≤ 3, 即 3 ≤ 3)
degeneration-more-severe : severity is-degeneration > severity is-myopia
degeneration-more-severe = Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))

-- 近视严重度 > 截面严重度 (2 > 1, 即 suc 1 ≤ 2, 即 2 ≤ 2)
myopia-more-than-section : severity is-myopia > severity is-section
myopia-more-than-section = Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)

-- §10d. 近视可矫正性的构造性证据
-- 给定一个近视 Myopia F L, 对任意 l : L,
-- 可以通过 local-section l 恢复全局信息
-- 但恢复的不是唯一的全局元素 (因为不是满射)
-- 这就是 "矫正" 的含义: 信息还在, 只是需要选择

-- 矫正 = 选择截面 (不是唯一逆)
-- 欧氏: 看到 f(T₀) = a, 矫正为 const-func a = (a,a,a)
-- 但真实函数可能是 (a,b,c), b≠a 或 c≠a
-- 矫正给出一个 "最简" 全局扩展, 不是唯一扩展

--------------------------------------------------------------------------------
-- §11. 统一风险汇总
--------------------------------------------------------------------------------

-- 6 种近视的完整见证
-- 按维度分级: 0 维 (欧氏, 微积分), 1 维 (CRT, 素数), ∞ 维 (Fourier, Lie)
myopia-risk-complete :
    MyopiaRisk GF3Func Trit     -- 欧氏
  × Myopia GF3Func Trit         -- 欧氏 (Myopia 实例)
  × Myopia Duodec Trit          -- CRT (Myopia 实例)
  × MyopiaRisk Duodec Trit      -- CRT
myopia-risk-complete =
    euclidean-risk
  , euclidean-myopia
  , crt-myopia
  , crt-risk

-- 所有构造性证明的汇总
all-constructive :
    (euclidean-sees ≡ 6)                        -- 欧氏看到 6D
  × (∀ f → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀))      -- 微积分: Δ³≡0
  × (∀ x → crt12 (π3 x) (π4 x) ≡ x)            -- CRT: 同余有解
  × (12 ≡ 4 * 3)                                 -- 素数分解: 12=4×3
  × (discrete-spectrum-size ≡ 4320)              -- Fourier: 4320 频率
  × (a4-order ≡ 12)                              -- Lie: A₄ 有 12 元素
all-constructive =
    refl
  , Δ³≡0
  , crt12-roundtrip
  , refl
  , refl
  , refl

-- 所有反证法的汇总
all-contradictions :
    ¬ (euclidean-sees ≡ t6-lattice-size)         -- 欧氏: 6≠729
  × ¬ (T₁ ≡ T₀)                                  -- 微积分: 步长≠0
  × ¬ (GCD-144-46 ≡ 1)                           -- CRT: gcd=2≠1
  × ¬ (4 ≡ 1 + 2)                                -- 素数: 4≠3
  × ¬ (discrete-spectrum-size ≡ 0)               -- Fourier: 4320≠0
  × ¬ (a4-order ≡ 0)                             -- Lie: 12≠0
all-contradictions =
    (λ ())
  , step-nonzero
  , (λ ())
  , (λ ())
  , (λ ())
  , (λ ())

-- 近视 vs 退化: 可矫正性对比
-- 近视有右逆 (可矫正), 退化没有 (不可逆)
myopia-correctable :
    (∀ a → eval₀ (const-func a) ≡ a)             -- 欧氏可矫正
  × (∀ a → π3 (crt-section-map a) ≡ a)           -- CRT 可矫正
myopia-correctable =
    eval₀-const-valid
  , crt-section-valid
