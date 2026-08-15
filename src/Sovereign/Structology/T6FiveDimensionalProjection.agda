{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Structology.T6FiveDimensionalProjection
-- T⁶ 五维物理投影: 六枚坐标的显式维度标注 (0 postulate, 无洞)
--
--   T⁶ = (x, y, z, cL, cR, g)
--      = 三个空间维 (Space3) × 两个手征维 (Chiral2) × 一个规范相位维 (Gauge1)
--
--   五维物理投影 FiveD = Space3 × Chiral2 (3+2), 规范相位为纤维方向:
--   fiveOf 对相位不敏感 (fiveOf-gauge-independent), 相位承载 Z₃ 规范圈。
--
-- 语义标注 (dimTag, 6 例 refl):
--   坐标 0,1,2 → Space (x, y, z); 坐标 3,4 → Chiral (cL, cR); 坐标 5 → Gauge (g)
-- 手征语义 (spinLabel, 3 例 refl, 与 ChiralInterference.cw/ccw/rest 对齐):
--   0 → rest (静止), 1 → cw (右旋), 2 → ccw (左旋)  — 两列反向波叠加 → 驻波
--
-- 与 T6.agda 的 729 双射对接: project729 = decompose ∘ finToT6
-- 为后续物理模块提供维度框架 (本体层 PhysicalOntology: 5D 以太 = T⁶ + GF(9))。

module Sovereign.Structology.T6FiveDimensionalProjection where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Structology.T6 using (T6Lattice; GF3; finToT6)

--------------------------------------------------------------------------------
-- §1. 维度类型 (3 空间 + 2 手征 + 1 相位 = 6)
--------------------------------------------------------------------------------

Space3 : Set
Space3 = GF3 × GF3 × GF3

Chiral2 : Set
Chiral2 = GF3 × GF3

Gauge1 : Set
Gauge1 = GF3

-- 五维物理投影: 3 空间 + 2 手征 (相位维剥离后留下的 5 维)
FiveD : Set
FiveD = Space3 × Chiral2

-- 维度标签 (显式标注)
data DimTag : Set where
  Space  : DimTag
  Chiral : DimTag
  Gauge  : DimTag

-- 第 i 枚坐标的维度标注: 0,1,2 → Space; 3,4 → Chiral; 5 → Gauge
dimTag : Fin 6 → DimTag
dimTag fz                 = Space
dimTag (fs fz)            = Space
dimTag (fs (fs fz))       = Space
dimTag (fs (fs (fs fz)))  = Chiral
dimTag (fs (fs (fs (fs fz))))  = Chiral
dimTag (fs (fs (fs (fs (fs fz))))) = Gauge

-- 手征语义标签 (与 ChiralInterference.cw/ccw/rest 对齐)
data Spin : Set where
  cw ccw rest : Spin

spinLabel : GF3 → Spin
spinLabel fz        = rest   -- 0 → 静止
spinLabel (fs fz)   = cw     -- 1 → 右旋
spinLabel (fs (fs fz)) = ccw -- 2 → 左旋

--------------------------------------------------------------------------------
-- §2. 分解与重组 (3+2+1 ↔ 6 坐标, 全部 refl)
--------------------------------------------------------------------------------

decompose : T6Lattice → FiveD × Gauge1
decompose (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = (((x , y , z) , (cL , cR)) , g)

recompose : FiveD × Gauge1 → T6Lattice
recompose (((x , y , z) , (cL , cR)) , g) = x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []

decompose∘recompose : ∀ w → decompose (recompose w) ≡ w
decompose∘recompose (((x , y , z) , (cL , cR)) , g) = refl

recompose∘decompose : ∀ v → recompose (decompose v) ≡ v
recompose∘decompose (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = refl

--------------------------------------------------------------------------------
-- §3. 分量投影与显式坐标访问
--------------------------------------------------------------------------------

spaceOf : T6Lattice → Space3
spaceOf (x ∷ y ∷ z ∷ _ ∷ _ ∷ _ ∷ []) = (x , y , z)

chiralOf : T6Lattice → Chiral2
chiralOf (_ ∷ _ ∷ _ ∷ cL ∷ cR ∷ _ ∷ []) = (cL , cR)

gaugeOf : T6Lattice → Gauge1
gaugeOf (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ g ∷ []) = g

fiveOf : T6Lattice → FiveD
fiveOf v = (spaceOf v , chiralOf v)

xOf yOf zOf cLOf cROf gOf : T6Lattice → GF3
xOf  (x ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) = x
yOf  (_ ∷ y ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) = y
zOf  (_ ∷ _ ∷ z ∷ _ ∷ _ ∷ _ ∷ []) = z
cLOf (_ ∷ _ ∷ _ ∷ cL ∷ _ ∷ _ ∷ []) = cL
cROf (_ ∷ _ ∷ _ ∷ _ ∷ cR ∷ _ ∷ []) = cR
gOf  (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ g ∷ []) = g

-- 标注一致性: 六坐标经标注后重组等于原向量
recompose∘labels : ∀ v → recompose (((xOf v , yOf v , zOf v) , (cLOf v , cROf v)) , gOf v) ≡ v
recompose∘labels (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = refl

--------------------------------------------------------------------------------
-- §4. 相位纤维: 五维投影对规范相位不敏感
--------------------------------------------------------------------------------

setGauge : T6Lattice → Gauge1 → T6Lattice
setGauge (x ∷ y ∷ z ∷ cL ∷ cR ∷ _ ∷ []) g = x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []

fiveOf-gauge-independent : ∀ v g → fiveOf (setGauge v g) ≡ fiveOf v
fiveOf-gauge-independent (x ∷ y ∷ z ∷ cL ∷ cR ∷ _ ∷ []) g = refl

gaugeOf-setGauge : ∀ v g → gaugeOf (setGauge v g) ≡ g
gaugeOf-setGauge (x ∷ y ∷ z ∷ cL ∷ cR ∷ _ ∷ []) g = refl

--------------------------------------------------------------------------------
-- §5. 手征对合: 两枚手征坐标互换 (cL ↔ cR), 空间与相位不动
--------------------------------------------------------------------------------

chiralFlip : T6Lattice → T6Lattice
chiralFlip (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = x ∷ y ∷ z ∷ cR ∷ cL ∷ g ∷ []

chiralFlip-involutive : ∀ v → chiralFlip (chiralFlip v) ≡ v
chiralFlip-involutive (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = refl

chiralFlip-preserves-space : ∀ v → spaceOf (chiralFlip v) ≡ spaceOf v
chiralFlip-preserves-space (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = refl

chiralFlip-preserves-gauge : ∀ v → gaugeOf (chiralFlip v) ≡ gaugeOf v
chiralFlip-preserves-gauge (x ∷ y ∷ z ∷ cL ∷ cR ∷ g ∷ []) = refl

--------------------------------------------------------------------------------
-- §6. 与 T⁶ ≃ Fin 729 双射对接
--------------------------------------------------------------------------------

project729 : Fin 729 → FiveD × Gauge1
project729 i = decompose (finToT6 i)

-- 0 postulate.
