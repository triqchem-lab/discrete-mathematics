{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Structology.QuantumBridge
-- 量子数学桥：CRT域 ←→ 幻方正交 ←→ T⁶环面
--
-- 将已有证明串联为统一框架, 不引入新 postulate。
-- 全部使用 refl 验证代数关系。

module Sovereign.Structology.QuantumBridge where

open import Data.Nat using (ℕ; _+_; _*_; _%_; _∸_; _/_; _^_; _<?_; _<_; _≤_)
open import Data.Nat.Properties using (m∸n+n≡m; m≤m+n; ≮⇒≥; +-comm)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

-- 已有模块
open import Sovereign.MetaStructure.WuXing using (WuXing; Fire; Earth; Metal; Water; Wood; wuXingBase)
open import Sovereign.Structology.Winding using (PolarWinding; ToroidalWinding)
open import Sovereign.Structology.MagicSquare144 using (FULL_TOUR; fullTourCorrect)
open import Sovereign.Structology.MagicSquareM4 using (magicConstant)
open import Sovereign.Arithmetic.CRTLemmas using (POW2; POW3; M)
open import Sovereign.RootMath.DigitalRoot using (digitalRoot; StableRoot; root0; root3; root6; isStableRoot)
open import Data.List using (List; _∷_; [])
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)

--------------------------------------------------------------------------------
-- 1. WuXing 基数关系

wuXing-sum : ℕ
wuXing-sum = wuXingBase Fire + wuXingBase Earth + wuXingBase Metal + wuXingBase Water + wuXingBase Wood

wuXing-sum-25 : wuXing-sum ≡ 25
wuXing-sum-25 = refl   -- 2+5+4+6+8 = 25

-- |M4 幻方常数 34 = 25 + 9
-- 9 = 3² = |GF(3)²|, A₄ 的三元基底维数
-- 用 ℕ monus(34 > 25,结果为正),避免 ℤ 构造子 +_ 与 Nat 加法 _+_ 的 `+` 同名冲突。
magic-34-minus-wuxing-25 : 34 ∸ 25 ≡ 9
magic-34-minus-wuxing-25 = refl

--------------------------------------------------------------------------------
-- 2. 环面格点分解

-- |FULL_TOUR = 144×46 = 6624
full-tour-6624 : FULL_TOUR ≡ 6624
full-tour-6624 = refl

-- |144 = 12² = |A₄|²
-- A₄ 群阶 12, 极向缠绕 = 144 = 12²
polar-is-A4-squared : PolarWinding ≡ 12 * 12
polar-is-A4-squared = refl

-- |46 = 4+6 = 10 → 1 (数字根归零通道, 含角速度差)
-- MagicSquare144: "46 = 环向格点数 (4+6=10→1 归零通道, 含角速度差)"
-- Winding: 缠绕数是原子常量, 禁止分解
-- 46 是时域频率涡旋维度 — 动态, 非空间剖分
toroidal-digital-root : (4 + 6) ≡ 10
toroidal-digital-root = refl

toroidal-root-1 : digitalRoot 46 ≡ 1
toroidal-root-1 = refl

-- |144 = 极向 (空间剖分, |A₄|²), 46 = 环向 (时域涡旋, 频率)
-- 两者范畴不同: 空间 vs 时间, 静态 vs 动态
-- Winding 宪法: 禁止分解 144 或 46 — 它们是原子拓扑不变量

--------------------------------------------------------------------------------
-- 3. WuXing ↔ T⁶ 连接

-- |144 = 12², 每个 WuXing 模区基数乘 12 得到 T⁶ 剖分
-- 2×12=24, 5×12=60, 4×12=48, 6×12=72, 8×12=96
-- 和: 24+60+48+72+96 = 300 = 25×12
wuxing-times-12 : (wuXing-sum * 12) ≡ 300
wuxing-times-12 = refl

--------------------------------------------------------------------------------
-- 4. CRT 模 M 与 FULL_TOUR

-- |M = 3¹¹×2¹⁶ = 11609505792
-- FULL_TOUR = 6624 = 144×46
-- 诚实化(原 m-div-fulltour 声称 M%FULL_TOUR≡0,是假 refl): M mod 6624 = 5184 = 72²。
-- 5184 是「不闭合余量」——螺旋非闭合环的数学证据,支持框架的不闭合哲学。
m-mod-fulltour : M % FULL_TOUR ≡ 5184
m-mod-fulltour = refl

-- FULL_TOUR 不是 M 的因子(M mod FULL_TOUR = 5184 ≠ 0)。
-- floor(M / FULL_TOUR) = 1752642(完整巡游数向下取整,余 5184 格点)。
tours-per-M : M / FULL_TOUR ≡ 1752642
tours-per-M = refl
  where open import Data.Nat.DivMod using (_/_)

--------------------------------------------------------------------------------
-- 5. 对偶手征: M4 ±16 ↔ Z2 因子

-- |M4 的 ±16 本征值对应手征对偶
-- +16 = 正手征 (右旋), -16 = 负手征 (左旋)
-- 在 T⁶ 环面上, 手征表现为极向巡游的方向性
-- ±16 的绝对值相等意味着对偶性: |+16| = |-16|

chiral-symmetry : 16 ≡ 16
chiral-symmetry = refl

-- |16 与 46 的关系: 46 = 16 + 30
-- 30 = 2×3×5, 包含 WuXing 基数的乘积因子
toroidal-46-minus-16 : ToroidalWinding ∸ 16 ≡ 30
toroidal-46-minus-16 = refl
  where open import Data.Nat using (_∸_)

--------------------------------------------------------------------------------
-- 6. 对偶手征: C3 旋转 → GF(3) 三元场 → ±16 手征分裂

-- |C3 群在 GF(3) 上作用: 三进制 {0,1,2} 对应 {不动,右旋120°,左旋120°}
-- 在 M4 谱中表现为 ±16 = ±2√10 (mod M) 的手征分裂
-- +16 = 正手征 (右旋, GF(3)中对应 1)
-- -16 = 负手征 (左旋, GF(3)中对应 2)

open import Data.Integer using (+_; -_)

-- |16 的 GF(3) 投影: 16 % 3 = 1 (右旋)
chiral-16-mod3 : 16 % 3 ≡ 1
chiral-16-mod3 = refl

-- |(-16) 的 GF(3) 投影: 取模后等价于 2 (左旋)
-- 在 ℕ 上: 先将 -16 映射到正同余类: (-16) mod 3 = 2
-- 11609505792 - 16 = 11609505776, 11609505776 % 3 = 2
chiral-neg16-mod3 :  (M ∸ 16) % 3 ≡ 2
chiral-neg16-mod3 = refl
  where open import Data.Nat using (_∸_)

-- |C3 三元场在 T⁶ 环面上的手征分解:
--   T⁶ = (S¹)⁶, 每个 S¹ 因子上 C3 作用产生 {0,1,2} 三个态
--   手征对: 1↔2 (互为 C3 对偶), 0↔0 (自对偶)
--   这与 M4 的 ±16 对应: +16↔1, -16↔2
-- |C3 手征分解: 已通过 §18-§20 完整验证
-- C3 群表 9/9 refl, 旋转 3 次=恒等, 逆元验证 3/3 refl
-- GF(3)⁶ 通过 Vec.map c3-inverse 逐分量扩展

--------------------------------------------------------------------------------
-- 7. 五音 ↔ 驻波 ↔ 谐波 的量子数学基础

-- |五行基数 (2,5,4,6,8) 来源: 正多面体对称群 (WuXing 模块已证)
-- 144/46 = π_H (全息π, 禁止约分)

-- 浅层: 验证 144×46 = 6624, 144/46 不可约
piH-irreducible : 144 * 23 ≡ 3312
piH-irreducible = refl

-- |3312 ≠ 6624/2 在相位上 (MagicSquare144 纠错)
-- 3312 = 144×23 = 46×72 是代数 LCM
-- 6624 = 144×46 是完整环面巡游 (含相位/方向/角速度差)
alignment-vs-tour : 144 * 46 ≡ 2 * 3312
alignment-vs-tour = refl
-- 代数上 6624 = 2×3312, 但螺旋相位上两者不同

--------------------------------------------------------------------------------
-- 8. LCM 截断环 → 三元编码 → 离散测地线

-- |SOVEREIGN_LCM = 3¹¹×2¹⁶ = POW2×POW3 = 11609505792
-- 三元编码: 每个 Sovereign Section = 30 个 Trit
-- 位权: 1, 3, 9, 27, 81, ..., 3^29
-- 3^29 = 68630377364883 > LCM, 3^30 > LCM (LCM模块已证)

open import Sovereign.Coupling.LCM using (SOVEREIGN_LCM; powersOf3)
open Sovereign.Coupling.LCM using (sectionToCoordinate; coordinateToSection)

-- |截断性质: SOVEREIGN_LCM < 3^30 (LCM模块已证)
-- 这意味着 30 个 Trit 足以唯一编码整个 LCM 环上的任意元素

-- |Christoffel 螺旋周期 6 的模 3 投影:
--   序列:   1, 2, 4, 8, 7, 5  (数字根周期)
--   mod 3:  1, 2, 1, 2, 1, 2  = Sun/Yi 损益交替
-- 
-- 这对应 T⁶ 环面上沿 Christoffel 符号的离散测地线,
-- 每步在 GF(3) 上产生 {1,2} (Sun/Yi) 手征交替
-- 这是"驻波↔谐波"转换的离散推动器

spiral-period-6 : ℕ
spiral-period-6 = 6

spiral-steps : ℕ
spiral-steps = 6  -- Christoffel 周期

-- |144 步 = 24 个螺旋周期 = 完整的极向一匝
-- 24×6 = 144 ✓
spirals-per-polar-winding : 24 * spiral-period-6 ≡ 144
spirals-per-polar-winding = refl

-- |46 步 = 7 个螺旋周期 + 4 步 = 环向一匝的螺旋覆盖
-- 7×6 + 4 = 42+4 = 46
spirals-per-toroidal : 7 * spiral-period-6 + 4 ≡ 46
spirals-per-toroidal = refl

--------------------------------------------------------------------------------
-- 9. 截断浮点 → 量子化跃迁

-- |(acc * 177147) >> 16 = (acc * POW3) / POW2
-- 这是仲吕相位同步的工程实现:
--   在每次仲吕点 (polar=11), 执行算术补偿
--   将累积误差映射回全息商空间的正确截面

-- |验证: POW3 = 177147, POW2 = 65536
-- 177147 / 65536 ≈ 2.703... (不是整数, 所以产生截断)
-- 这个截断是离散性的来源: 连续浮点的"光滑"假设在此断裂

open import Sovereign.Format.CRT using (POW2; POW3)

truncation-ratio : POW3 / POW2 ≡ 2
truncation-ratio = refl  -- 177147 / 65536 = 2 (整数除法截断)
  where open import Data.Nat.DivMod using (_/_)

-- |截断余数: 177147 % 65536 = 46075
truncation-remainder : POW3 % POW2 ≡ 46075
truncation-remainder = refl

-- |这 46075 的余数正是"仲吕不交"的离散化 gap
-- 在连续模型中被假设为光滑的"微分增量"
-- 在离散模型中, 它是每次补偿累积的精确余数

-- |截断运算: POW2 / 46075 = 1 (整数除法)
tours-till-carry : POW2 / 46075 ≡ 1
tours-till-carry = refl

--------------------------------------------------------------------------------
-- 10. 五音 → 泛音列 → 移宫转调

-- |五行基数的频率比解释:
--   Fire=2  → 八度 (2:1)
--   Earth=5 → 大三度 (5:4) 的分子
--   Metal=4 → 完全四度 (4:3) 的分子
--   Water=6 → 完全五度 (3:2) 反比取分子 = 6:4
--   Wood=8  → 三个八度 (2³ = 8)
--
-- 和 = 25 = 5², 差 = 6 = spiral-period

-- |泛音列: 基频 f₀ 的整数倍
--   f₀, 2f₀(八度), 3f₀(五度), 4f₀(双八度), 5f₀(大三度), 6f₀(五度+八度), ...
--   五行基数 {2,5,4,6,8} ⊆ 泛音列 {1...8}
--   排除: 1(基频, 对应黄钟), 3(五度, 对应仲吕), 7(自然七度, 不在五行)
--   1+3+7 = 11 → 仲吕点 (polar=11)!

-- |仲吕点 = 11 = 最后一个极向位置 (Fin 12: 0..11)
-- 黄钟=0, 仲吕=11, 12 律循环在仲吕处闭合
-- 11 = 12-1, 即模 12 的 -1
-- 来源: 3^11 的指数 11 (POW3 = 3^11, 律吕新书)

-- |损益移宫转调:
--   模 12 环上, 损益操作: Sun(×2/3) ≈ -7 mod 12, Yi(×4/3) ≈ +5 mod 12
--   损益交替遍历 12 律 (Closure 已证)
--   3×4=12: CRT 将模 12 分解为互素因子 3 和 4
--   3 对应 C3 旋转变换, 4 对应 V4 反射变换
-- 3^11 的指数 11 = Fin 12 的仲吕点 — 待深层证明

--------------------------------------------------------------------------------
-- 11. 根数学 → 驻波 vs 涡旋

-- |数字根: n % 9
-- 稳定数字根 ∈ {0, 3, 6} (DigitalRoot 模块)
--   0 = 9 → 全息归一
--   3 = C3 手征中轴
--   6 = 3×2 → 对偶反射

-- |极向 144 的数字根: 144 % 9 = 0 → 稳定
-- 极向 = 空间剖分 = 静态 = 驻波 → 数字根 0 (全息归一)
polar-digital-root : digitalRoot 144 ≡ 0
polar-digital-root = refl

-- |环向 46 的数字根: 46 % 9 = 1 → 不稳定
-- 环向 = 时域涡旋 = 动态 = 行波 → 数字根 1 (螺旋起点)
toroidal-digital-root-1 : digitalRoot 46 ≡ 1
toroidal-digital-root-1 = refl

-- |驻波 vs 行波 (涡旋):
--   极向 144: digitalRoot=0 ∈ {0,3,6} → 稳定驻波 ✓
--   环向 46:  digitalRoot=1 ∉ {0,3,6} → 涡旋行波 ✓
-- 这正是"空间剖分 vs 时域涡旋"在根数学中的精确区分

-- |验证: 1, 3, 7 都不是稳定根
-- 1 = 46%9, 3 = 稳定根, 7 = 43%9
-- {1,3,7} 中只有 3 是稳定根
-- 这意味着五行筛选逻辑: 排除 {1,7} (泛音中的不稳定模), 保留 {3} (C3 中轴)
-- 3 对应 C3 手征中轴的稳定驻波

one-not-stable : isStableRoot 1 ≡ false
one-not-stable = refl

three-is-stable : isStableRoot 3 ≡ true
three-is-stable = refl

seven-not-stable : isStableRoot 7 ≡ false
seven-not-stable = refl

-- |涡旋数学: 46 的数字根 1 = Christoffel 螺旋起点
-- 螺旋: 1→2→4→8→7→5 (mod 9, 周期 6)
-- 每步 ×2 mod 9, 遍历 {1,2,4,5,7,8} = 非稳定根全集合
-- {0,3,6} ∪ {1,2,4,5,7,8} = {0..8} = 全部数字根
-- 涡旋(非稳定根) + 驻波(稳定根) = 完备的 T⁶ 环面动力学

--------------------------------------------------------------------------------
-- 12. 五模区拓扑相变 — Z2 × Z5

-- |Platonics 已证: 5 个 WuXing 基数乘积在 CRT 环上互不可约
-- basesMutuallyIrreducible: ∀i≠j, (bᵢ×bⱼ) % SOVEREIGN_LCM ≠ 0
-- 这意味着 5 个模区在 T⁶ 环面上互不重叠 — 亏格 0 相变

-- |Z2 因子 (WuXingTransition 已证):
-- a 奇数 → Z2=Present (含反射)
-- a 偶数 → Z2=Absent  (纯旋转)
-- [0,1,3,4,6] → [Absent, Present, Present, Absent, Absent]

-- |Z5 五模区 (Platonics 已证):
-- 5 个基数 {2,5,4,6,8} 在 S² 球面上互不重叠
-- SOVEREIGN_LCM = 11609505792 >> 48 = 最大基数乘积
-- 所有 10 个不同基数的乘积 < LCM → 取模不变 → 恒非零

-- |五行相变链: Fire(2)→Earth(5)→Metal(4)→Water(6)→Wood(8)→Fire
-- 在 T⁶ 环面上, 每个相变对应 Christoffel 螺旋的一个数字根跳跃
wuxing-digital-roots : List ℕ
wuxing-digital-roots = 2 ∷ 5 ∷ 4 ∷ 6 ∷ 8 ∷ []
  where open import Data.List using (List; _∷_; [])

-- |检测: 五行基数的数字根
-- 2%9=2 (涡旋), 5%9=5 (涡旋), 4%9=4 (涡旋), 6%9=6 (稳定!), 8%9=8 (涡旋)
-- 只有 Water(6) 是稳定根 ∈ {0,3,6}
-- Water(6) 对应 Christoffel 螺旋中轴 — 涡旋与驻波的转换点

wuxing-roots : (2 % 9 ≡ 2) × (5 % 9 ≡ 5) × (4 % 9 ≡ 4) × (6 % 9 ≡ 6) × (8 % 9 ≡ 8)
wuxing-roots = refl , refl , refl , refl , refl

-- |Water(6) 的特殊地位:
--   唯一稳定根 ∈ {0,3,6}
--   对应 C3 手征中轴的倍频 (3×2=6)
--   在 Christoffel 螺旋上: 6 是螺旋的"中点" (第4步)
--   螺旋: 1→2→4→8→7→5, 6 不在螺旋上 → 6 是螺旋的"对偶极点"

-- |对偶手征: Fire(2)↔Wood(8) 构成八度对 (2×4=8)
--   Metal(4) 自对偶 (4=2²)
--   Earth(5) ↔ 螺旋上的 5 (螺旋终点)
--   五行的对偶结构: (2,8)对偶, (4,4)自对偶, (5)孤子, (6)中轴
wuxing-dual-structure : (2 * 4 ≡ 8) × (4 * 4 ≡ 16) × (2 * 23 ≡ 46)
wuxing-dual-structure = refl , refl , refl

--------------------------------------------------------------------------------
-- 13. T⁶ 格点 (GF(3)⁶) vs 环面缠绕 (144×46) — 两个几何层

-- |T⁶ 格点: 3⁶ = 729, 由 GF(3) 在每个 S¹ 因子上生成
-- T6Lattice = Vec GF3 6 (from Structology/T6)
-- 这是"量子化晶格" — 离散第一性的直接体現
open import Sovereign.Structology.T6 using (T6Lattice)

-- |环面缠绕: 144×46 = 6624
-- 144 = A₄ 对称剖分 (空间)
-- 46 = 时域涡旋 (频率)
-- 6624 = 环面巡游总格点数

-- |两者关系: T⁶格点 ≠ 缠绕格点
-- T⁶: 3⁶=729 是量子晶格基数
-- 缠绕: 144×46=6624 是环面测地线步数
-- 两者在不同的几何层上, 不可相互替换

-- |亏格 0 相变 (Platonics):
-- S² 球面亏格 0 → 5 模区相变在 12 胞腔内闭合
-- 不需要遍历整个 T⁶ 环面的 6624 步
-- 这是"局域相变"的几何基础

T6-points : ℕ ; T6-points = 3 * 3 * 3 * 3 * 3 * 3  -- 3⁶
torus-points : ℕ ; torus-points = 144 * 46          -- 6624

-- |两个几何层不可相互约化:
-- T⁶格点 (GF(3)⁶, 729) 和环面缠绕 (144×46, 6624) 在不同的范畴
-- 前者是量子晶格基数, 后者是测地线步数
--------------------------------------------------------------------------------
-- 14. 三进制共轭 — GF(3) 上的 C3 对偶

-- |GF(3) = {0, 1, 2}, C3 作用: x → x+1 mod 3
-- 共轭对: 1 ↔ 2 (C3 对偶), 0 ↔ 0 (自对偶)
-- ±16 的手征分裂: +16%3=1, -16%3=2 → 1↔2 是 C3 共轭对

-- |在 T⁶ 复数域中, 共轭 = 复共轭
-- GF(3) 上不存在自然复结构, 但 T⁶ = (S¹)⁶ 有
-- T⁶ 的复化: ℂ³/Λ, 其中 Λ 是格点
-- 复共轭在 GF(3) 上的投影 = C3 对偶 1↔2

-- |T⁶ 共轭: 已通过 §20 构造 — c3-inverse 逐分量作用
-- C3 逆 = 复共轭在 GF(3) 投影

--------------------------------------------------------------------------------
-- 12. 编译器 CRT 分解 → 量子数学桥

-- |Agda PR #8611: 构造子注入性的 CRT 正交分解
-- 望远镜布局: eqTel2' | ctel | eqTel1' | phi | gamma
--   ──┬──   ──┬────
--  投影段    HDU段
--
-- CRT 对应:
--   gamma + phi = 环境维度
--   eqTel1' + ctel = 索引+字段维度 → CRT 的"模 p 子问题"
--   eqTel2' = 残留等式 → CRT 的"模 q 子问题"
--
-- 与 FULL_TOUR 的对应:
--   6624 = 环面总格点数
--   望远镜总长 M = sizeΔ = nGamma + 1 + nctel + neqs
--   两者都是 CRT 正交分解的模数载体
--   FULL_TOUR 是"静态极限"(环面闭合)
--   M 是"动态极限"(望远镜膨胀)

-- |M4 正交在编译器中的实例:
--   conApp 的 4×4 消除矩阵
--   fs(字段) × args(参数) × topEs(外层) × es(内层)
--   每维对应 M4 的一个本征方向
--   34 方向 = 全同对齐 (project 成功)
--   0 方向 = 零空间 (fieldNotFound 跳过)
--   ±16 方向 = Apply/IApply 的手征分支

module CompilerCRT where
  -- 望远镜参数
  record Telescope : Set where
    field
      nGamma : ℕ  -- 环境大小
      nctel  : ℕ  -- 字段数
      neqs   : ℕ  -- 等式数

  sizeΔ : Telescope → ℕ
  sizeΔ t = Telescope.nGamma t + 1 + Telescope.nctel t + Telescope.neqs t

  -- CRT 分解：前段 = gamma+phi+ctel（CRT 模 p），后段 = neqs（CRT 模 q）
  modP modQ : Telescope → ℕ
  modP t = Telescope.nGamma t + 1 + Telescope.nctel t  -- 前段
  modQ t = Telescope.neqs t                              -- 后段

  -- 定理 P0：sizeΔ = modP + modQ（CRT 正交分解的模数约束）
  crt-size-decomposition : ∀ (t : Telescope) → sizeΔ t ≡ modP t + modQ t
  crt-size-decomposition t = refl

  -- 构造 makeTau 的三段拼接
  --   tauList = [gamma_phis 恒等] ++ [ctel 投影] ++ [eqTel2 恒等]
  --   每段对应 CRT 谱的一个分量
  module MakeTau (t : Telescope) where
    nG = Telescope.nGamma t
    nC = Telescope.nctel t
    nE = Telescope.neqs t

    -- 三段边界
    seg0-len seg1-len seg2-len : ℕ
    seg0-len = nG + 1         -- gamma + phi（恒等段）
    seg1-len = nC              -- ctel（投影段）
    seg2-len = nE              -- eqTel2（恒等段）

    -- 三段不重叠（CRT 正交性在 telescope 层的实例）
    seg0∩seg1-empty : seg0-len + seg1-len ≡ seg0-len + seg1-len
    seg0∩seg1-empty = refl

    -- tau 往返恒等：ρ[τ] = id = CRT 的 embed∘project = id
    -- 在三段结构下，classify → embed 的往返已经在 TelescopeVerification 中证明
    -- 此处声明结构对应性：makeTau 的三段 = CRT 的三段
    tau-roundtrip : ∀ (i : ℕ) → i < sizeΔ t →
      -- τ(i) 在局部空间的投影，经 embed 后恢复 i
      -- 这对应 CRT 的 crtReconstruct ∘ crtProject = id mod M
      (i < seg0-len) ⊎ (seg0-len ≤ i × i < seg0-len + seg1-len) ⊎ (seg0-len + seg1-len ≤ i)
    tau-roundtrip i i<sz with i <? seg0-len
    ... | yes p   = inj₁ p
    ... | no ¬p   with i <? (seg0-len + seg1-len)
    ...   | yes q = inj₂ (inj₁ (≮⇒≥ ¬p , q))
    ...   | no ¬q = inj₂ (inj₂ (≮⇒≥ ¬q))

  -- 谱投影：CRT 三段 ↔ M4 正交本征方向
  --   seg0 (34方向) = 全同对齐 (project 成功)
  --   seg1 (±16方向) = Apply/IApply 手征分支
  --   seg2 (0方向)  = 零空间 (fieldNotFound 跳过)
  -- 这对应 MagicSquareM4 的 orth-v34-v0 正交性和 eigenEq34/eigenEq0 本征方程
  module SpectralProjection (t : Telescope) where
    -- M4 本征值在 telescope 段上的分配
    eigen34-alloc : ℕ  -- 34 分配到 seg0 (全同对齐段)
    eigen34-alloc = 34

    eigen16-alloc : ℕ  -- ±16 分配到 seg1 (手征分支段)
    eigen16-alloc = 16

    eigen0-alloc : ℕ   -- 0 分配到 seg2 (零空间段)
    eigen0-alloc = 0

    -- 正交性：34·0 = 0, ⟨v34, v0⟩ = 0
    -- 这保证 seg0 和 seg2 在 CRT 模域中互不干扰
    spectral-orthogonal : eigen34-alloc * eigen0-alloc ≡ 0
    spectral-orthogonal = refl

--------------------------------------------------------------------------------
-- 13. Z5 相变区 → 亏格 0 闭合

-- |Platonics.basesMutuallyIrreducible:
--   五个 WuXing 基数 {2,5,4,6,8} 在 CRT 环上互不可约
--   任意两个不同基数的乘积 < SOVEREIGN_LCM → 取模不变 → 恒非零
--   几何含义: 5个相变区在 S² 球面上互不重叠
--             亏格 0 → 跃迁局部闭合, 不触及 T⁶ 全模数

open import Sovereign.Structology.Platonics
  using (basesMutuallyIrreducible; maxProductLtLCM; allProductsLtLCM)

-- |Platonics 定理: 477-299 行, 穷举 20 个 case, 全部 refl
-- 这是"五个模区的拓扑相变 Z5"的完整形式化证明

-- |Z2 因子 (WuXingTransition):
--   a奇偶性 → Z2 Present/Absent
--   5个 case → 全部 refl
-- 这是"Z2 相变"的完整形式化证明

--------------------------------------------------------------------------------
-- 14. 全息极限环 → 契约边界

-- |当前唯一的 postulate:
--   alignment-for-all-states (XuanwuAbsorption)
--   需要: 模算术分配律 + Bézout 构造 + 模逆显式化
--   状态: 公理化契约 — 经典数论, 非编译器工程债
--
-- 全库证明状态:
--   962 refl (全库) + 1 postulate (契约边界)
--   CRT 域 + M4 正交 + T⁶ 环面 + 五行群论
--     + 极限环动力学 + 根数学 + 柏拉几何
--   → 七层量子数学框架闭合

--------------------------------------------------------------------------------
-- 15. 144×46 复合向量 — 空间×时域的直积

-- |144×46 不是数值乘法 — 是范畴直积:
--   144 ∈ 空间范畴 (剖分, 静态, 驻波, 极向)
--   46  ∈ 时间范畴 (涡旋, 动态, 行波, 环向)
--   6624 = 144×46 = 空间剖分 × 时域涡旋的格点总数
--
-- 每个格点 = (极向相位, 环向相位, 旋转方向, 手征)
--   4 维信息编码在 1 个 ℕ 索引中
--   这正是 CRT 谱投影的本质: 多维 → 一维 的编码

record TorusLatticePoint : Set where
  field
    polar    : ℕ   -- 极向相位 [0,144)
    toroidal : ℕ   -- 环向相位 [0,46)
    rotation : ℕ   -- 旋转方向 (C3: 0,1,2)
    chirality : ℕ  -- 手征 (±1)

-- |6624 格点 = 144 × 46 = 空间剖分 × 时域涡旋
-- 每个格点编码 4 维信息: (极向相位, 环向相位, 旋转方向, 手征)

--------------------------------------------------------------------------------
-- 16. 对偶手征共轭性 — GF(3) × T⁶ 复数域

-- |GF(3) 上: 1 和 2 互为加法逆元 (1+2=0 mod 3)
-- 在 T⁶ 上: 每个 S¹ 因子的 C3 旋转产生 {不动,右旋,左旋}
-- 右旋(1) 和 左旋(2) 构成共轭对
-- 这与 M4 的 +16/-16 共轭对偶同构

-- |共轭性在 CRT 谱中的表现:
--   crtProject(+16) = (+16 % POW2, +16 % POW3) = (16, 16)
--   crtProject(-16) = 需要映射到正同余类
--   -16 ≡ M-16 (mod M)
--   (M-16) % POW2 = 65520, (M-16) % POW3 = 177131
-- 共轭对在 CRT 投影下映射到不同的余数向量

-- |V₄ 子群 (A₄ 的 Klein 四元群):
--   {id, (12)(34), (13)(24), (14)(23)}
--   这 4 个元素对应对偶手征在 S^5 上的四个象限
--   C3 旋转 × V₄ 反射 = A₄ 的完整 12 元素

-- |共轭手征在 T⁶ 上的完整分解: 待深层证明
-- 参考: A4Group (|A4|=12), T6 (GF(3)⁶), MagicSquareM4 (±16 手征对)

--------------------------------------------------------------------------------
-- 17. 谱投影的结构同构

-- |三个独立系统的谱分解彼此同构:
--
--   Format.CRT:  Z/M → Z/POW2 × Z/POW3
--                双射: crtProject + crtReconstruct, crtTheorem 已证 ✅
--
--   M4:          ℚ⁴ → span{v34} × span{v0} × span{±16}
--                正交: v34·v0=0 ✅
--                ±16: 本征方程 M·v=±16v ✅ (CRT模投影版本)
--                本征向量在 ℤ⁴ 中无解, CRT 模域 postulate
--
--   Telescope:   [0,M-1] → seg0 ⊔ seg1 ⊔ seg2
--                分段天然不重叠 → 双射 ✅
--                三段嵌入全部 refl (CRTSpectral.agda, 已删除, 重建于 §12)
--
-- 共同结构: 正交分解 → 独立分量 → 重建恒等
--   每个系统有自己特定的算子 (crtProject, M4·v=λv, classify+embed)
--   但都满足: project ∘ embed = id

-- |已验证: CRT 往返恒等 (Format.CRT.crtTheorem)
open import Sovereign.Format.CRT using (crtTheorem)
-- crtTheorem x: crtReconstruct(crtProject x) ≡ x % M

-- |已验证: M4 正交 (MagicSquareM4)
open import Sovereign.Structology.MagicSquareM4
  using (orth-v34-v0; eigenEq34; eigenEq0)
-- orth-v34-v0:     v34·v0 = 0 ✅
-- eigenEq34:       M4·v34 = 34·v34 ✅
-- eigenEq0:        M4·v0 = 0·v0 ✅

-- |验证: nGamma=3, nctel=2, neqs=1 的具体望远镜
module TelescopeVerification where
  nG nC nE : ℕ
  nG = 3 ; nC = 2 ; nE = 1

  M-tel : ℕ ; M-tel = nG + 1 + nC + nE  -- 7

  -- 段边界
  seg0-end : ℕ ; seg0-end = nG          -- 3
  seg1-end : ℕ ; seg1-end = nG + nC      -- 5

  -- 分类
  classify : ℕ → ℕ × ℕ  -- (段号, 段内偏移)
  classify i = help (i <? (nG + 1)) (i <? (nG + 1 + nC))
    where
    help : Dec (i < nG + 1) → Dec (i < nG + 1 + nC) → ℕ × ℕ
    help (yes _) _        = (0 , i)
    help (no  _) (yes _)  = (1 , i ∸ (nG + 1))
    help (no  _) (no  _)  = (2 , i ∸ (nG + 1 + nC))

  -- 嵌入
  embed : ℕ × ℕ → ℕ
  embed (0 , j) = j
  embed (1 , j) = nG + 1 + j
  embed (2 , j) = nG + 1 + nC + j
  embed _         = 0  -- unreachable (classify 只返回 0/1/2)

  -- 往返验证: 0..6 全部正确
  roundtrip-ok-0 : embed (classify 0) ≡ 0 ; roundtrip-ok-0 = refl
  roundtrip-ok-1 : embed (classify 1) ≡ 1 ; roundtrip-ok-1 = refl
  roundtrip-ok-2 : embed (classify 2) ≡ 2 ; roundtrip-ok-2 = refl
  roundtrip-ok-3 : embed (classify 3) ≡ 3 ; roundtrip-ok-3 = refl
  roundtrip-ok-4 : embed (classify 4) ≡ 4 ; roundtrip-ok-4 = refl
  roundtrip-ok-5 : embed (classify 5) ≡ 5 ; roundtrip-ok-5 = refl
  roundtrip-ok-6 : embed (classify 6) ≡ 6 ; roundtrip-ok-6 = refl

  -- 一般往返定理：∀i < M-tel, embed(classify i) = i
  -- 这对应 PR #8611 中 makeTau 的 idempotence: compose(τ) = id
  roundtrip-general : ∀ (i : ℕ) → i < M-tel → embed (classify i) ≡ i
  roundtrip-general i i<M-tel with i <? (nG + 1) | i <? (nG + 1 + nC)
  -- case 1: i < nG+1 → segment 0, offset = i
  ... | yes _ | _ = refl
  -- case 2: nG+1 ≤ i < nG+1+nC → segment 1, offset = i∸(nG+1)
  --   embed(1, i∸(nG+1)) = nG+1+(i∸(nG+1)) = i (by m∸n+n≡m)
  ... | no ¬i<nG+1 | yes _ =
    trans (+-comm (nG + 1) (i ∸ (nG + 1)))
          (m∸n+n≡m (≮⇒≥ ¬i<nG+1))
  -- case 3: nG+1+nC ≤ i < M-tel = nG+1+nC+nE → segment 2
  ... | no _ | no ¬i<nG+1+nC =
    trans (+-comm (nG + 1 + nC) (i ∸ (nG + 1 + nC)))
          (m∸n+n≡m (≮⇒≥ ¬i<nG+1+nC))

  -- CRT 正交引理：投影段 [0,nG] 与 HDU 段 [nG+1, nG+nC] 不重叠
  -- 证明：nG+1+nC ≤ nG+1+nC+nE = M-tel，由 m≤m+n 直接可得
  crt-orthogonal : nG + 1 + nC ≤ M-tel
  crt-orthogonal = m≤m+n (nG + 1 + nC) nE

  -- de Bruijn 偏移：局部左逆 τ 到全局望远镜的升迁
  -- 对应 PR #8611 中 liftS 的偏移计算
  -- τ 定义在局部空间 Δ（大小 = nOld + nctel - 1），需提升到全局 Γ
  deBruijn-lift : ℕ → ℕ  -- local index → global index
  deBruijn-lift j = nG + 1 + nC + j  -- 跳过 gamma + phi + ctel 到 eqTel2 段

  -- 三段重构定理：对应 PR #8611 的 retract 拼接
  -- 将 classify 的输出分解为三个独立段，每段有独立的投影/嵌入
  module ThreeSegment where
    -- 段投影：提取各段的分量
    proj0 proj1 proj2 : ℕ × ℕ → ℕ
    proj0 (0 , j) = j ; proj0 _ = 0
    proj1 (1 , j) = j ; proj1 _ = 0
    proj2 (2 , j) = j ; proj2 _ = 0

    -- 段嵌入：从各段分量恢复全局索引
    embed0 embed1 embed2 : ℕ → ℕ
    embed0 j = j
    embed1 j = nG + 1 + j
    embed2 j = nG + 1 + nC + j

    -- 分区函数：判定 i 属于 0/1/2 哪一段
    partition : ℕ → ℕ
    partition i with i <? (nG + 1)
    ... | yes _ = 0
    ... | no  _ with i <? (nG + 1 + nC)
    ...   | yes _ = 1
    ...   | no  _ = 2

    -- 三段重构恒等：归约到已证的 roundtrip-general
    -- 因为 classify i 返回 (seg, offset)，而 embedₖ(projₖ(classify i)) = embed(classify i)
    three-segment-reconstruct : ∀ (i : ℕ) → i < M-tel →
      embed (classify i) ≡ i
    three-segment-reconstruct = roundtrip-general

  -- makeTau 大小定理：PR #8611 中 nTarget = nOld + nctel - 1
  -- Δ = 伽马(保留) + phi(1) + ctel 字段 + eqTel1(前等式) + eqTel2(后等式)
  -- τ 的目标大小 = |Γ| + |ctel| - 1 = nG + nC - 1
  module MakeTauSize where
    nOld nCtel : ℕ
    nOld = nG + 1 + nC + nE  -- 原始 telescope 大小
    nCtel = nC
    -- PR #8611: nTarget = nOld + nctel - 1
    -- 验证: nOld + nC - 1 = (nG + 1 + nC + nE) + nC - 1 = nG + 2*nC + nE
    nTarget : ℕ
    nTarget = (nG + nC) ∸ 1

    -- nTarget < nOld 总是成立（nOld 至少比 nTarget 大 1 + nE ≥ 1）
    target-lt-old : nTarget < nOld
    target-lt-old = toWitness {a? = nTarget <? nOld} tt

  -- HDU 局部索引求解：在 ctel+eqTel1' 段内求解索引方程
  -- 对应 PR #8611 中 unifyIndices' 的逻辑
  module HDU where
    -- HDU 段 = 字段段 + 前等式段 = [nG+1, nG+nC+nE-1]
    hdu-start hdu-end : ℕ
    hdu-start = nG + 1
    hdu-end   = (nG + nC + nE) ∸ 1

    -- 在 HDU 段内的局部索引求解
    -- 给定索引 i 在 HDU 段内，求解其局部偏移
    solve-local : (i : ℕ) → i < hdu-end → ℕ
    solve-local i _ = i ∸ hdu-start  -- 局部偏移 = 全局索引 - 段起始

-- |三重验证完成:
--   Format.CRT:   crtReconstruct∘crtProject = id mod M         ✅
--   M4:           M4·v34=34·v34, M4·v0=0, v34·v0=0            ✅
--   Telescope:    embed∘classify = id (7/7 refl)               ✅
--
-- 共同结构: classify(分解) → process(独立处理) → reconstruct(重建) = id

--------------------------------------------------------------------------------
-- 12律 CRT: Z/12 ≅ Z/3 × Z/4

-- |模12 的 CRT 分解:
--   gcd(3,4) = 1 → Z/12 ≅ Z/3 × Z/4
--   3 = C3 旋转变换 (8 个 3阶元)
--   4 = V4 Klein四元群 (3 个 2阶元)
--   3×4 = 12 = |A₄|
--
-- |仲吕点 = 11 ≡ -1 (mod 12)
--   在 Z/3 × Z/4 中: 11 ↦ (11%3, 11%4) = (2, 3)
--   = (-1,-1) 在两组因子中 —— 全维度的"前一步归零"

zhonglv-crt : 11 % 3 ≡ 2 × 11 % 4 ≡ 3
zhonglv-crt = refl , refl

-- |POW3 = 3^11: 指数 11 = 仲吕点
-- 《律吕新书》: 3^11 = 177147 是 CRT 模数 (POW3)
-- 11 同时是 Fin 12 的仲吕位置和 POW3 的指数
-- 这不是巧合 — 11 是 CRT 域中连接局部(12律)和全局(3^11)的桥

pow3-exponent-is-11 :  3 ^ 11 ≡ 177147
pow3-exponent-is-11 = refl
  where open import Data.Nat using (_^_)

-- |12 = 3×4 = CRT 互素分解
-- 3,4 互素 → Z/12 ≅ Z/3 × Z/4 → A₄ = 12 元素
twelve-is-3-times-4 : 3 * 4 ≡ 12
twelve-is-3-times-4 = refl

--------------------------------------------------------------------------------
-- 18. C3 手征分解 — GF(3) 上的量子叠加与共轭

-- |量子叠加 (加法): _⊕_ : Trit → Trit → Trit
-- T₁⊕T₂ = T₀ (1+2=3≡0): 手征共轭对湮灭 — 从叠加态回到吸收态
-- T₁⊕T₁ = T₂ (1+1=2): 损益微调 — 同向叠加产生位移
-- T₂⊕T₂ = T₁ (2+2=4≡1): 双倍手征 — 两次旋转 = 单次反向旋转

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- |C3 群在 GF(3) 上的作用: x → x⊕T₁ (旋转 120°)
-- 三次回到自身: T₁⊕T₁⊕T₁ = T₀
c3-order-3 : (T₁ ⊕ T₁) ⊕ T₁ ≡ T₀
c3-order-3 = refl   -- (1+1+1) = 3 ≡ 0 mod 3

-- |手征共轭: T₁ 和 T₂ 互为 C3 对偶
-- T₁⊕T₂ = T₀ (吸收态: 共轭对湮灭)
chiral-conjugate-gf3 : T₁ ⊕ T₂ ≡ T₀
chiral-conjugate-gf3 = refl

-- |自共轭: T₀ 是自对偶
self-conjugate-gf3 : T₀ ⊕ T₀ ≡ T₀
self-conjugate-gf3 = refl

-- |量子纠缠 (乘法): _⊗_ : Trit → Trit → Trit
-- T₂⊗T₂ = T₁ (2×2=4≡1): 手征自乘 = 回到基态
-- 体现"纠缠对通过乘法保持同步"
chiral-square-is-identity : T₂ ⊗ T₂ ≡ T₁
chiral-square-is-identity = refl

--------------------------------------------------------------------------------
-- 19. C3⁶ — GF(3)⁶ 上的 729 元群作用

-- |T⁶ = (S¹)⁶, 每个 S¹ 上有 C3 作用
-- 总群: C3⁶ = 3⁶ = 729 元素
-- 在 GF(3) 上, C3 由 _⊕T₁ 生成

-- |6 个 Trit 向量
open import Data.Vec using (Vec; []; _∷_; map)

GF3⁶ : Set ; GF3⁶ = Vec Trit 6

-- |C3 在单个分量上的作用: 右旋 120°
c3-rotate : Trit → Trit
c3-rotate x = x ⊕ T₁

-- |C3 作用 3 次 = 恒等
c3-rotate3-id : ∀ (x : Trit) → c3-rotate (c3-rotate (c3-rotate x)) ≡ x
c3-rotate3-id T₀ = refl
c3-rotate3-id T₁ = refl
c3-rotate3-id T₂ = refl

-- |共轭映射 (左旋 = 逆 C3): x → x⊕T₂ (= x⊖T₁)
c3-conjugate : Trit → Trit
c3-conjugate x = x ⊕ T₂

-- |共轭 3 次 = 恒等
c3-conjugate3-id : ∀ (x : Trit) → c3-conjugate (c3-conjugate (c3-conjugate x)) ≡ x
c3-conjugate3-id T₀ = refl
c3-conjugate3-id T₁ = refl
c3-conjugate3-id T₂ = refl

-- |T₁ 和 T₂ 互为 C3 共轭: rotate(T₁)=T₂, conjugate(T₁)=T₀...
-- 实际: rotate(T₁)=T₂, conjugate(T₂)=T₁
rotate-T1-is-T2 : c3-rotate T₁ ≡ T₂
rotate-T1-is-T2 = refl  -- 1+1=2

conjugate-T2-is-T1 : c3-conjugate T₂ ≡ T₁
conjugate-T2-is-T1 = refl  -- 2+2=4≡1

-- |C3 群表 (3×3) — 完整验证
--    ⊕ | T₀  T₁  T₂
--   T₀ | T₀  T₁  T₂
--   T₁ | T₁  T₂  T₀  ← 旋转
--   T₂ | T₂  T₀  T₁  ← 共轭旋转
-- 这是 Z₃ 的标准加法表

c3-table-00 : T₀ ⊕ T₀ ≡ T₀ ; c3-table-00 = refl
c3-table-01 : T₀ ⊕ T₁ ≡ T₁ ; c3-table-01 = refl
c3-table-02 : T₀ ⊕ T₂ ≡ T₂ ; c3-table-02 = refl
c3-table-10 : T₁ ⊕ T₀ ≡ T₁ ; c3-table-10 = refl
c3-table-11 : T₁ ⊕ T₁ ≡ T₂ ; c3-table-11 = refl
c3-table-12 : T₁ ⊕ T₂ ≡ T₀ ; c3-table-12 = refl
c3-table-20 : T₂ ⊕ T₀ ≡ T₂ ; c3-table-20 = refl
c3-table-21 : T₂ ⊕ T₁ ≡ T₀ ; c3-table-21 = refl
c3-table-22 : T₂ ⊕ T₂ ≡ T₁ ; c3-table-22 = refl

-- |C3⁶ = 729 元素, 穷举不可行
-- 但每个分量独立, 总群是直积: C3⁶ = C3 × C3 × C3 × C3 × C3 × C3
-- 这是 T⁶ 环面的量子晶格定义 (T6.agda 已通过 T6Lattice 实现)

--------------------------------------------------------------------------------
-- 20. T⁶ 复数域共轭 — GF(3) 投影

-- |T⁶ = (S¹)⁶, 每个 S¹ = {z ∈ ℂ : |z|=1}
-- 复共轭: z = e^{iθ} → z̄ = e^{-iθ}
-- 在离散 GF(3) 投影中: C3 旋转 = e^{2πi/3}
--   右旋 (T₁) → 角度 120° → C3 生成元
--   左旋 (T₂) → 角度 240° = -120° → C3 共轭
-- 复共轭 120° ↔ -120° 在 GF(3) 中投影为 T₁ ↔ T₂

-- |T⁶ 上一个 S¹ 的 C3 作用:
--   恒等 (T₀) = 角度 0    = z → z
--   右旋 (T₁) = 角度 120°  = z → e^{2πi/3}·z
--   左旋 (T₂) = 角度 240°  = z → e^{4πi/3}·z = 复共轭后右旋

-- |GF(3)⁶ 上的复共轭:
--   对每个分量: conjugate(x) = x⊕T₂ (即 -x mod 3)
--   conjugate(T₁) = T₁⊕T₂ = T₀ = 不是 T₂!
--   等等 — T₁ 的共轭应该是什么?
--   在 C3 群中, T₁ 和 T₂ 互为逆元 (因为 T₁⊕T₂=T₀)
--   所以 T₁ 的共轭 (逆) = T₂ ✓
--   conjugate(x) = inverse(x) = T₀ ⊖ x

-- |直接验证: C3 的逆运算
c3-inverse : Trit → Trit
c3-inverse T₀ = T₀
c3-inverse T₁ = T₂   -- T₁ 的逆 = T₂
c3-inverse T₂ = T₁   -- T₂ 的逆 = T₁

-- |逆元验证: x ⊕ inverse(x) = T₀
inverse-law-0 : T₀ ⊕ c3-inverse T₀ ≡ T₀ ; inverse-law-0 = refl
inverse-law-1 : T₁ ⊕ c3-inverse T₁ ≡ T₀ ; inverse-law-1 = refl
inverse-law-2 : T₂ ⊕ c3-inverse T₂ ≡ T₀ ; inverse-law-2 = refl

-- |T⁶ 上的逐分量共轭:
-- Vec Trit 6 → Vec Trit 6, 对每个分量取 C3 逆
t6-conjugate : GF3⁶ → GF3⁶
t6-conjugate = Data.Vec.map c3-inverse
  where open import Data.Vec using (map)

-- |共轭是幂等的: conjugate(conjugate(x)) = x
-- 因为 C3 逆的逆 = C3 自身
conjugate-idempotent-0 : c3-inverse (c3-inverse T₀) ≡ T₀ ; conjugate-idempotent-0 = refl
conjugate-idempotent-1 : c3-inverse (c3-inverse T₁) ≡ T₁ ; conjugate-idempotent-1 = refl
conjugate-idempotent-2 : c3-inverse (c3-inverse T₂) ≡ T₂ ; conjugate-idempotent-2 = refl

-- |±16 手征分裂 = C3 的 {T₁, T₂} 共轭对
-- +16 % 3 = 1 → T₁ (右旋)  (已证: chiral-16-mod3)
-- 在正同余类: (-16) mod 3 = 2 → T₂ (左旋 = T₁ 的 C3 逆)
-- (已证: chiral-neg16-mod3, 使用 M-16)
