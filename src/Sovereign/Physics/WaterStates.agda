{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.WaterStates
-- 水的 8 种状态 → T⁶ 离散框架建模
--
-- 语料锚 (PPT 层, ≥7 处逐字坐实):
--   "水是标准的等离子结构，不止只有三态，还有：超临界流体、超固体、
--    超流体、费米子凝聚态、等离子态。合计8种状态。"
--
-- 数据来源:
--   PPT 层: 8 种状态 + 温度阈值 + 两种排布 (百度百科可验)
--   口述层: 5 种状态 (待验证, 不入库)
--   维度层: 6/7/8 三变体 (语料内部, 不入库)
--
-- 形式化策略:
--   §1 水的 8 种状态 = T⁶ 的 8 个特定态
--   §2 温度阈值 = T⁶ 相变点
--   §3 两种排布 = GF(3) 手征 (T₀ 无序 vs T₁/T₂ 有序)
--   §4 4⁹/9⁴ 旋转力学 = DuodecClock 通道
--
-- 0 postulate.

module Sovereign.Physics.WaterStates where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _^_)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9
  using (GF9; gf9-one; gf9-zero; alpha; _*gf9_; _+gf9_; galoisConjugate)
open import Sovereign.Structology.T6 using (T6Lattice; GF3)

--------------------------------------------------------------------------------
-- §1. 水的 8 种状态 (T⁶ 编码)
--------------------------------------------------------------------------------

-- 语料: "合计8种状态"
-- 固态、液态、气态 + 超临界流体、超固体、超流体、费米子凝聚态、等离子态

-- 8 种状态的数据类型
data WaterState : Set where
  Solid            : WaterState  -- 固态
  Liquid           : WaterState  -- 液态
  Gas              : WaterState  -- 气态
  Supercritical    : WaterState  -- 超临界流体
  Supersolid       : WaterState  -- 超固体
  Superfluid       : WaterState  -- 超流体
  FermionCondensate : WaterState  -- 费米子凝聚态
  Plasma           : WaterState  -- 等离子态

-- 8 种状态
water-state-count : ℕ
water-state-count = 8

-- T⁶ 编码: 用前 3 个分量编码 8 种状态
-- (x, y, z) ∈ GF(3)³ = 27 个态, 取前 8 个
state-to-t6 : WaterState → GF3 × GF3 × GF3
state-to-t6 Solid             = (fz , fz , fz)   -- (0,0,0) 零态
state-to-t6 Liquid            = (fs fz , fz , fz)  -- (1,0,0)
state-to-t6 Gas               = (fs (fs fz) , fz , fz)  -- (2,0,0)
state-to-t6 Supercritical     = (fz , fs fz , fz)  -- (0,1,0)
state-to-t6 Supersolid        = (fz , fs (fs fz) , fz)  -- (0,2,0)
state-to-t6 Superfluid        = (fz , fz , fs fz)  -- (0,0,1)
state-to-t6 FermionCondensate = (fz , fz , fs (fs fz))  -- (0,0,2)
state-to-t6 Plasma            = (fs fz , fs fz , fs fz)  -- (1,1,1)

-- 固态 = T⁶ 零态 (有序结晶)
solid-is-zero : state-to-t6 Solid ≡ (fz , fz , fz)
solid-is-zero = refl

-- 等离子态 = 全分量激发 (电离)
plasma-is-full : state-to-t6 Plasma ≡ (fs fz , fs fz , fs fz)
plasma-is-full = refl

--------------------------------------------------------------------------------
-- §2. 温度阈值 (T⁶ 相变点)
--------------------------------------------------------------------------------

-- 语料数据 (PPT 层, 百度百科可验):
--   第二临界点: -45℃ / 227.7K (有序结晶)
--   均质形核温度: -41℃ / 232K (开始结冰)
--   无人区: 150K ~ 232K
--   ±4℃: 无序结晶/密度最大

-- 温度阈值 (开尔文, 整数近似)
temp-second-critical : ℕ
temp-second-critical = 228  -- ≈ 227.7K

temp-homogeneous-nucleation : ℕ
temp-homogeneous-nucleation = 232  -- TH

temp-no-mans-land-low : ℕ
temp-no-mans-land-low = 136  -- 玻璃化温度

temp-density-max : ℕ
temp-density-max = 277  -- ±4℃ ≈ 277K

-- 相变路径 (T⁶ 分量跳变):
--   固态 (0,0,0) → 液态 (1,0,0): 第一分量 +1
--   液态 (1,0,0) → 气态 (2,0,0): 第一分量 +1
--   气态 (2,0,0) → 等离子 (1,1,1): 全分量激发

-- 固态→液态: 第一分量 T₀→T₁
solid-to-liquid : T₀ ⊕ T₁ ≡ T₁
solid-to-liquid = refl

-- 液态→气态: 第一分量 T₁→T₂
liquid-to-gas : T₁ ⊕ T₁ ≡ T₂
liquid-to-gas = refl

-- 气态→等离子: 全分量激发 (特征 3 归零后重新分配)
-- 这不是简单的加法, 而是相变 (分量跳变)

--------------------------------------------------------------------------------
-- §3. 两种排布 (GF(3) 手征)
--------------------------------------------------------------------------------

-- 语料:
--   密排无序: 密度高, ±4℃ 无序结晶
--   正四面体有序: 密度低, -45℃ 有序结晶, 超导属性

-- 在 GF(3) 中:
--   T₀ = 无手征 (无序)
--   T₁ = 左旋 (有序)
--   T₂ = 右旋 (有序)

-- 密排无序 → T₀ (无手征)
dense-disordered : Trit
dense-disordered = T₀

-- 正四面体有序 → T₁ 或 T₂ (有手征)
tetrahedral-ordered-l : Trit
tetrahedral-ordered-l = T₁

tetrahedral-ordered-r : Trit
tetrahedral-ordered-r = T₂

-- 手征翻转: T₁ ↔ T₂
chiral-flip : T₁ ⊕ T₂ ≡ T₀
chiral-flip = refl  -- 1+2=3≡0 (mod 3)

-- 密排无序是手征对消态
dense-is-chiral-cancel : T₁ ⊕ T₂ ≡ dense-disordered
dense-is-chiral-cancel = refl

--------------------------------------------------------------------------------
-- §4. 4⁹/9⁴ 旋转力学 (DuodecClock 通道)
--------------------------------------------------------------------------------

-- 语料:
--   顺时针 = 4⁹ (二进制通道)
--   逆时针 = 9⁴ (三进制通道)
--   水的力学 = 两种通道的叠加

-- 4⁹ = 2¹⁸ = 262144
val-4-to-9 : ℕ
val-4-to-9 = 4 ^ 9

-- 9⁴ = 3⁸ = 6561
val-9-to-4 : ℕ
val-9-to-4 = 9 ^ 4

-- 验证
val-4-to-9-is : val-4-to-9 ≡ 262144
val-4-to-9-is = refl

val-9-to-4-is : val-9-to-4 ≡ 6561
val-9-to-4-is = refl

-- 4⁹ = 2¹⁸ (二进制通道)
four-to-nine-is-two-to-eighteen : 4 ^ 9 ≡ 2 ^ 18
four-to-nine-is-two-to-eighteen = refl

-- 9⁴ = 3⁸ (三进制通道)
nine-to-four-is-three-to-eight : 9 ^ 4 ≡ 3 ^ 8
nine-to-four-is-three-to-eight = refl

-- 与 DuodecClock 的关系:
--   顺时针 4⁹ = 2¹⁸ → 2 的幂次 (GF(9)* 的生成, α 阶 4)
--   逆时针 9⁴ = 3⁸ → 3 的幂次 (GF(3) 的特征, char=3)
--   水的力学 = 两种通道的叠加 = DuodecClock 的加乘联合

-- 4⁹ × 9⁴ = 2¹⁸ × 3⁸
combined : ℕ
combined = val-4-to-9 * val-9-to-4

combined-is : combined ≡ 1719926784
combined-is = refl

--------------------------------------------------------------------------------
-- §5. 等离子水 (H₃O₂) — 争议标注
--------------------------------------------------------------------------------

-- 语料:
--   H₃O₂ (第四相): 270nm 紫外吸收峰, 3μm 红外诱发
--   折射率/密度比普通水高 10%, 带负电荷
--
-- 状态: 争议概念, 主流学术界视为未经证实的假说
-- 在框架中标注为 "待验证/非主流"
-- 不进入证明层, 仅作注释

-- H₃O₂ = H₂O + H (额外氢)
-- 在 GF(9) 共轭框架中: 额外氢 = 共轭分量的翻转
-- 即: σ(a,b) = (a, -b), 额外氢改变了虚部符号

-- 化学式系列 (语料):
--   H₂O (物质态)
--   H₃O₂ (血液系统, 结构化水)
--   H₃O (淋巴系统)
--   H₄O (头部, 通神琼浆)

-- 0 postulate.
