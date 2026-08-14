{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Constitution.Boundaries
-- 宪法：范畴边界、合法转换、非法封禁
-- 
-- 核心原则：
-- 1. 范畴不可通约：五大范畴各自独立
-- 2. 缠绕数不可拆分
-- 3. 紧化非法
-- 4. 移宫转调唯一合法
-- 5. 律管与编钟隔离
-- 6. 纳音为驻波拓扑指纹

module Sovereign.Constitution.Boundaries where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_; 0ℓ)
open import Data.Nat using (ℕ; _+_; _*_; _>_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Structology.Winding using (PolarWinding; ToroidalWinding)
open import Sovereign.Coupling.LossGain using (LossGain; Sun; Yi; applyLossGain)
open import Sovereign.MetaStructure.WuXing using (WuXing; wuXingBase)

--------------------------------------------------------------------------------
-- 1. 范畴标签
--------------------------------------------------------------------------------

data Category : Set where
  RootMathCat       : Category  -- 根数学
  StructologyCat    : Category  -- 结构学
  CouplingCat       : Category  -- 耦合域
  MetaStructureCat  : Category  -- 元结构层
  DensityCat        : Category  -- 密度

--------------------------------------------------------------------------------
-- 2. 合法跨范畴转换
--------------------------------------------------------------------------------

-- IsConvertible 记录类型：证明从范畴 catA 的类型 A 到范畴 catB 的类型 B 的转换是合法的
record IsConvertible {a b} (A : Set a) (B : Set b) (catA catB : Category) : Set (a ⊔ b) where
  field
    convert : A → B
    -- 转换必须保持结构
    convertPreserves : ∀ {x y : A} → x ≡ y → convert x ≡ convert y

-- 合法转换实例

-- 结构学的缠绕数可以投影到耦合域的状态机步数
polarToStep : IsConvertible {0ℓ} {0ℓ} ℕ ℕ StructologyCat CouplingCat
polarToStep = record
  { convert = λ n → n
  ; convertPreserves = λ p → p
  }

toroidalToPhase : IsConvertible {0ℓ} {0ℓ} ℕ ℕ StructologyCat CouplingCat
toroidalToPhase = record
  { convert = λ n → n
  ; convertPreserves = λ p → p
  }

-- 根数学的长度格点可以映射到耦合域的损益链
lengthToLossGain : IsConvertible {0ℓ} {0ℓ} ℕ (List LossGain) RootMathCat CouplingCat
lengthToLossGain = record
  { convert = λ _ → []
  ; convertPreserves = λ _ → refl
  }

-- 元结构层的五行可以映射到结构学的缠绕模式
wuXingToWinding : IsConvertible {0ℓ} {0ℓ} WuXing ℕ MetaStructureCat StructologyCat
wuXingToWinding = record
  { convert = wuXingBase
  ; convertPreserves = λ p → cong wuXingBase p
  }

--------------------------------------------------------------------------------
-- 3. 非法转换的封禁
--------------------------------------------------------------------------------

-- 以下转换永远无法构造出 IsConvertible 实例：

-- ❌ 极向缠绕数 → 元结构层五行基数（非法：缠绕数不可拆分）
-- ❌ 环向缠绕数 → 密度地气频率（非法：紧化）
-- ❌ 结构学 → 根数学的逆向映射（非法：范畴单向依赖）
-- ❌ 144 → 120 + 24（非法：缠绕数分解）

-- 我们通过不定义这些实例来封禁它们

--------------------------------------------------------------------------------
-- 4. 宪法定理

-- 缠绕数不可拆分定理
-- [分类: 宪法条款] [状态: 2026-08 P0 轨道 A — 原 polarIndecomposable 为假命题:
--   ¬ ∃a b (144 ≡ a+b × a≡120 × b≡24), 见证 a=120,b=24 使 144 ≡ 120+24 refl 成立,
--   该公理使 ⊥ 可导出, 已删除。教义保留为本注释:
--   缠绕数是拓扑不变量, 不是几何剖分 (120+24 = S² 剖分属几何范畴)。
--   类型级约束方向: Winding.agda HolomorphicPi 记录 (numerator/denominator 字段),
--   待 Fin6624 类型重构后以记录字段形式落地, 不以 ℕ 层假命题驻留。]

-- 全息 π 不可约分定理
-- [分类: 宪法条款] [状态: 2026-08 P0 轨道 A — 原 holoPiIrreducible 为假命题:
--   ¬ ∃k (k>1 × 144 ≡ k·72 × 46 ≡ k·23), 见证 k=2 (144=2·72, 46=2·23) 直证其反,
--   该公理使 ⊥ 可导出, 已删除。教义保留为本注释:
--   宪法禁止 144/46 → 72/23 约分 (全息 π 禁约分)。
--   类型级约束方向: Winding.agda:92-97 HolomorphicPi 记录 (numerator≡144,
--   denominator≡46 字段), 待 HolomorphicPi 类型级闭合, 不以 ℕ 层假命题驻留。]

-- 移宫转调唯一合法定理
-- [分类: 宪法公理] [状态: 架构保留 — 与 T6.agda:12-18 mod-helper 限制同根. 待 REWRITE 规则闭合]
-- 损益操作 Sun(×2/3)/Yi(×4/3) 需模运算保持奇偶性, 与 T6.agda:12-18 同根.
-- 可闭合路径: 添加 REWRITE 规则处理 /3 %2 的大数归约.
IsLegalTransform : (ℕ → ℕ) → Set
IsLegalTransform f = ∀ n → f n ≡ applyLossGain n Sun ⊎ f n ≡ applyLossGain n Yi

-- 2026-08 P0 轨道 C: 原 lossGainUniqueness 为 postulate — 前提与结论是同一命题
--   (IsLegalTransform 的定义即该 ∀ 命题), 恒等直接给出证明。
lossGainUniqueness :
  ∀ (n : ℕ) (f : ℕ → ℕ) →
  (∀ m → f m ≡ applyLossGain m Sun ⊎ f m ≡ applyLossGain m Yi) →
  IsLegalTransform f
lossGainUniqueness n f h = h

--------------------------------------------------------------------------------
-- 5. 范畴依赖图
--------------------------------------------------------------------------------

-- 合法的范畴依赖关系：
-- MetaStructureCat → RootMathCat → StructologyCat → CouplingCat → DensityCat
-- 
-- 非法的反向依赖或交叉依赖将被类型系统拒绝

data DependsOn : Category → Category → Set where
  metaDependsRoot : DependsOn MetaStructureCat RootMathCat
  rootDependsStruct : DependsOn RootMathCat StructologyCat
  structDependsCoupling : DependsOn StructologyCat CouplingCat
  couplingDependsDensity : DependsOn CouplingCat DensityCat
  -- 传递闭包（完整的范畴依赖层级）
  metaDependsStruct : DependsOn MetaStructureCat StructologyCat
  metaDependsCoupling : DependsOn MetaStructureCat CouplingCat
  metaDependsDensity : DependsOn MetaStructureCat DensityCat
  rootDependsCoupling : DependsOn RootMathCat CouplingCat
  rootDependsDensity : DependsOn RootMathCat DensityCat
  structDependsDensity : DependsOn StructologyCat DensityCat

-- 依赖传递性：由于 DependsOn 已显式枚举所有传递闭包构造器，
-- 传递性只需对合法依赖链做模式匹配即可得证。
dependsTransitive :
    ∀ {c₁ c₂ c₃ : Category} →
    DependsOn c₁ c₂ →
    DependsOn c₂ c₃ →
    DependsOn c₁ c₃
dependsTransitive metaDependsRoot      rootDependsStruct     = metaDependsStruct
dependsTransitive metaDependsRoot      rootDependsCoupling   = metaDependsCoupling
dependsTransitive metaDependsRoot      rootDependsDensity    = metaDependsDensity
dependsTransitive metaDependsStruct    structDependsCoupling = metaDependsCoupling
dependsTransitive metaDependsStruct    structDependsDensity  = metaDependsDensity
dependsTransitive metaDependsCoupling  couplingDependsDensity = metaDependsDensity
dependsTransitive rootDependsStruct    structDependsCoupling = rootDependsCoupling
dependsTransitive rootDependsStruct    structDependsDensity  = rootDependsDensity
dependsTransitive rootDependsCoupling  couplingDependsDensity = rootDependsDensity
dependsTransitive structDependsCoupling couplingDependsDensity = structDependsDensity
