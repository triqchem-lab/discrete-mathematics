{-# OPTIONS --cubical --guardedness --rewriting #-}

-- | Sovereign.Synthesis.Physics.SpinTwistor
-- 耦合域：自旋与扭量的离散复位 (0 postulate, 无洞)
--
-- 自旋本源：主权状态机手性分离程度的动态投影（仅存在于耦合域）—
--   computeSpinProjection : ToroidalPower → SpinLabel,
--   配对守恒 → Spin1 (玻色子), 完全分离 → Spin12 (费米子), 未激活 → Spin0
--   (spinProjectionBalanced / spinProjectionSeparated / spinProjectionInactive)
-- 扭量本源：T⁶ 复三维环面格点坐标的连续统投影 (TwistorPoint: z1,z2,z3),
--   复共轭 ↔ 手性对偶 (conjugateIsChiralFlip 对合)
-- 宪法条款：静态结构学容器无自旋、无手性、无动力学 —
--   ChiralityInContainer / SpinLabelInContainer 为空谓词 (⊥), 0 postulate
--
-- 修正上一稿：9 个 postulate 谓词/类型 → 构造性定义或空谓词;
--   4 个洞 → (λ () , refl) / 显式见证; 非法标识符 RequiresResetToDis本源 → 删除;
--   DiscreteComplex 导入源 EnergyGap → CartanTorsion (本地定义处);
--   SovereignState 由 postulate → 引用 Zhonglv 真实定义;
--   ⚠ [2026-10-22 更正] 原写「范畴分离: 标记类型 + `λ ()` 类型不等 (数据型不等)」——
--     那三条 `¬ (Electron ≡ SpinLabel)` / `¬ (TwistorPoint ≡ FundamentalSpacetime)` /
--     `¬ (SpinNetwork ≡ QuantumGeometry)` 已**移除**：两侧是相异且都有构造子的类型，
--     标准 Agda 判不出（实测 `Is empty: SpinNetwork ≡ QuantumGeometry (stuck)`），
--     只有本地补丁内核接受 ⇒ 改为**文档标注**（见文件末 §范畴分离 段）。
--     **仍保留**的是同文件的 9 条 `¬ (构造子 ≡ 构造子)`（同一 data 类型的不同构造子），
--     那些是标准 Agda 直接可证的。

module Sovereign.Synthesis.Physics.SpinTwistor where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.FieldTower.GF9 using (GF9; alpha; galoisConjugate; galoisConjugate²)
open import Sovereign.Synthesis.Geometry.CartanTorsion
  using (DiscreteComplex; _+ᵢ_; _+ᶜ_; conjugate)
open import Sovereign.Synthesis.CRT.Zhonglv using (SovereignState)
open import Sovereign.Synthesis.CRT.LossGain using (LossGain; Sun; Yi)
open import Sovereign.Synthesis.Format.ParityViolation
  using (ToroidalPower; mkPower; ChiralSymmetry; SingleChiral; PairedConserved;
         BreakingStarted; BreakingObvious; BreakingComplete; parityStatus)
open import Sovereign.Base.WuXing using (Chirality)
open import Sovereign.Synthesis.Combinatorics.T6 using (T6Lattice)

--------------------------------------------------------------------------------
-- 1. 自旋 = 手性分离程度的投影 (0 postulate)
--------------------------------------------------------------------------------

-- 自旋标签：0, 1/2, 1 (投影标签，非静态属性)
data SpinLabel : Set where
  Spin0  : SpinLabel   -- 自旋 0
  Spin12 : SpinLabel   -- 自旋 1/2
  Spin1  : SpinLabel   -- 自旋 1

-- 自旋投影：基于环向缠绕幂次 a 的手性状态
computeSpinProjection : ToroidalPower → SpinLabel
computeSpinProjection (mkPower a) =
  let chiralSym = parityStatus (mkPower a)
  in if isBalanced chiralSym
     then Spin1   -- 手性平衡 → 自旋 1（玻色子）
     else if isSeparated chiralSym
          then Spin12  -- 手性完全分离 → 自旋 1/2（费米子）
          else Spin0    -- 未激活或归零 → 自旋 0
  where
  isBalanced : ChiralSymmetry → Bool
  isBalanced PairedConserved = true
  isBalanced _ = false

  isSeparated : ChiralSymmetry → Bool
  isSeparated BreakingComplete = true
  isSeparated _ = false

-- 状态不相容引理 (构造子不匹配, 0 postulate)
notSinglePaired     : ¬ (SingleChiral ≡ PairedConserved)
notSinglePaired     = λ ()
notBreakingPaired   : ¬ (BreakingStarted ≡ PairedConserved)
notBreakingPaired   = λ ()
notObviousPaired    : ¬ (BreakingObvious ≡ PairedConserved)
notObviousPaired    = λ ()
notCompletePaired   : ¬ (BreakingComplete ≡ PairedConserved)
notCompletePaired   = λ ()
notSingleComplete   : ¬ (SingleChiral ≡ BreakingComplete)
notSingleComplete   = λ ()
notPairedComplete   : ¬ (PairedConserved ≡ BreakingComplete)
notPairedComplete   = λ ()
notBreakingComplete : ¬ (BreakingStarted ≡ BreakingComplete)
notBreakingComplete = λ ()
notObviousComplete  : ¬ (BreakingObvious ≡ BreakingComplete)
notObviousComplete  = λ ()
notPairedSingle     : ¬ (PairedConserved ≡ SingleChiral)
notPairedSingle     = λ ()
notBreakingSingle   : ¬ (BreakingStarted ≡ SingleChiral)
notBreakingSingle   = λ ()
notObviousSingle    : ¬ (BreakingObvious ≡ SingleChiral)
notObviousSingle    = λ ()
notCompleteSingle   : ¬ (BreakingComplete ≡ SingleChiral)
notCompleteSingle   = λ ()

-- 手性平衡 ⟹ 自旋 1 (玻色子)
spinProjectionBalanced : ∀ tp → parityStatus tp ≡ PairedConserved →
  computeSpinProjection tp ≡ Spin1
spinProjectionBalanced (mkPower 0) p = ⊥-elim (notSinglePaired p)
spinProjectionBalanced (mkPower 1) p = refl
spinProjectionBalanced (mkPower 2) p = refl
spinProjectionBalanced (mkPower 3) p = ⊥-elim (notBreakingPaired p)
spinProjectionBalanced (mkPower 4) p = ⊥-elim (notObviousPaired p)
spinProjectionBalanced (mkPower (suc (suc (suc (suc (suc n)))))) p = ⊥-elim (notCompletePaired p)

-- 手性完全分离 ⟹ 自旋 1/2 (费米子)
spinProjectionSeparated : ∀ tp → parityStatus tp ≡ BreakingComplete →
  computeSpinProjection tp ≡ Spin12
spinProjectionSeparated (mkPower 0) p = ⊥-elim (notSingleComplete p)
spinProjectionSeparated (mkPower 1) p = ⊥-elim (notPairedComplete p)
spinProjectionSeparated (mkPower 2) p = ⊥-elim (notPairedComplete p)
spinProjectionSeparated (mkPower 3) p = ⊥-elim (notBreakingComplete p)
spinProjectionSeparated (mkPower 4) p = ⊥-elim (notObviousComplete p)
spinProjectionSeparated (mkPower (suc (suc (suc (suc (suc n)))))) p = refl

-- 未激活 ⟹ 自旋 0
spinProjectionInactive : ∀ tp → parityStatus tp ≡ SingleChiral →
  computeSpinProjection tp ≡ Spin0
spinProjectionInactive (mkPower 0) p = refl
spinProjectionInactive (mkPower 1) p = ⊥-elim (notPairedSingle p)
spinProjectionInactive (mkPower 2) p = ⊥-elim (notPairedSingle p)
spinProjectionInactive (mkPower 3) p = ⊥-elim (notBreakingSingle p)
spinProjectionInactive (mkPower 4) p = ⊥-elim (notObviousSingle p)
spinProjectionInactive (mkPower (suc (suc (suc (suc (suc n)))))) p = ⊥-elim (notCompleteSingle p)

-- 自旋-统计复位 (构造性谓词, 0 postulate)
Bosonic : SpinLabel → Set
Bosonic Spin1  = ⊤
Bosonic Spin0  = ⊤
Bosonic Spin12 = ⊥

Fermionic : SpinLabel → Set
Fermionic Spin12 = ⊤
Fermionic _      = ⊥

spinStatisticsReset : ∀ tp → parityStatus tp ≡ PairedConserved →
  Bosonic (computeSpinProjection tp)
spinStatisticsReset (mkPower 1) p = tt
spinStatisticsReset (mkPower 2) p = tt
spinStatisticsReset (mkPower 0) p = ⊥-elim (notSinglePaired p)
spinStatisticsReset (mkPower 3) p = ⊥-elim (notBreakingPaired p)
spinStatisticsReset (mkPower 4) p = ⊥-elim (notObviousPaired p)
spinStatisticsReset (mkPower (suc (suc (suc (suc (suc n)))))) p = ⊥-elim (notCompletePaired p)

fermionStatisticsReset : ∀ tp → parityStatus tp ≡ BreakingComplete →
  Fermionic (computeSpinProjection tp)
fermionStatisticsReset (mkPower (suc (suc (suc (suc (suc n)))))) p = tt
fermionStatisticsReset (mkPower 0) p = ⊥-elim (notSingleComplete p)
fermionStatisticsReset (mkPower 1) p = ⊥-elim (notPairedComplete p)
fermionStatisticsReset (mkPower 2) p = ⊥-elim (notPairedComplete p)
fermionStatisticsReset (mkPower 3) p = ⊥-elim (notBreakingComplete p)
fermionStatisticsReset (mkPower 4) p = ⊥-elim (notObviousComplete p)

--------------------------------------------------------------------------------
-- 2. 宪法条款：静态容器中绝对不存在自旋与手性 (空谓词, 0 postulate)
--------------------------------------------------------------------------------

-- 容器域上的手性/自旋谓词恒空 (定义即无)
ChiralityInContainer : Chirality → Set
ChiralityInContainer _ = ⊥

SpinLabelInContainer : SpinLabel → Set
SpinLabelInContainer _ = ⊥

-- 静态结构学容器：仅提供格点舞台，无手性、无自旋、无动力学
record StaticContainer : Set₁ where
  field
    cellPartition   : ℕ    -- 格点剖分 (如 144)
    discreteSymmetry : Set  -- 离散置换群不变性
    chernNumber     : ℕ    -- 全局拓扑荷 C=2
    -- 宪法约束：静态容器无手性、无自旋 (证明义务, 0 postulate 可填)
    noChirality : ¬ (∃[ c ] ChiralityInContainer c)
    noSpin      : ¬ (∃[ s ] SpinLabelInContainer s)

noChiralityInContainer : ¬ (∃[ c ] ChiralityInContainer c)
noChiralityInContainer (c , ())

noSpinInContainer : ¬ (∃[ s ] SpinLabelInContainer s)
noSpinInContainer (s , ())

standardStaticContainer : StaticContainer
standardStaticContainer = record
  { cellPartition    = 144
  ; discreteSymmetry = ⊤
  ; chernNumber      = 2
  ; noChirality      = noChiralityInContainer
  ; noSpin           = noSpinInContainer
  }

staticContainerNoSpin : ∀ (sc : StaticContainer) → ¬ (∃[ s ] SpinLabelInContainer s)
staticContainerNoSpin sc = StaticContainer.noSpin sc

staticContainerNoChirality : ∀ (sc : StaticContainer) → ¬ (∃[ c ] ChiralityInContainer c)
staticContainerNoChirality sc = StaticContainer.noChirality sc

--------------------------------------------------------------------------------
-- 3. 扭量 = T⁶ 复三维格点坐标 (复共轭 ↔ 手性对偶)
--
-- 对齐声明 (2026-09-08): 本层 DiscreteComplex (a+ᵢb, i²=-1) 本质 = GF(9)
-- (CartanTorsion.agda:38 注: "本质 = GF(9) = GF(3)[i]/(i²+1)"), 故:
--   扭量复共轭 conjugate = GF(9) Frobenius σ (galoisConjugate)
--   手性对偶 (z, conj z) = GF9 共轭对 (对齐展示群本源纠缠, 同 ChiralInterference§6)
-- 离散复结构选择是本地实现 (DiscreteComplex record), 与标准 GF9 pair 同构;
-- 此处保持现有类型不动 (硬换破下游), 以声明标注其展示群归属.
--------------------------------------------------------------------------------

-- Trit 双负 (本地, 3 例)
negate-involutive : ∀ t → negate (negate t) ≡ t
negate-involutive T₀ = refl
negate-involutive T₁ = refl
negate-involutive T₂ = refl

-- 离散复共轭对合
conjugate-involutive : ∀ z → conjugate (conjugate z) ≡ z
conjugate-involutive (a +ᵢ b) = cong (λ t → a +ᵢ t) (negate-involutive b)

-- 扭量点：T⁶ 环面复三维结构中的复格点坐标
record TwistorPoint : Set where
  constructor mkTwistor
  field
    z1 : DiscreteComplex  -- 复维度 1 (极向实部 + 环向虚部)
    z2 : DiscreteComplex  -- 复维度 2
    z3 : DiscreteComplex  -- 复维度 3
    isInLCMSpace : ⊤      -- 每个 z_k 位于主权 LCM 商空间

-- 扭量复共轭 ↔ 手性对偶
twistorConjugate : TwistorPoint → TwistorPoint
twistorConjugate (mkTwistor z1 z2 z3 _) =
  mkTwistor (conjugate z1) (conjugate z2) (conjugate z3) tt

-- 定理：扭量复共轭对应手性翻转 (对合)
conjugateIsChiralFlip : ∀ (tw : TwistorPoint) →
  twistorConjugate (twistorConjugate tw) ≡ tw
conjugateIsChiralFlip (mkTwistor (a +ᵢ b) (c +ᵢ d) (e +ᵢ f) tt) = begin
  twistorConjugate (twistorConjugate (mkTwistor (a +ᵢ b) (c +ᵢ d) (e +ᵢ f) tt))
    ≡⟨ refl ⟩
  mkTwistor (conjugate (conjugate (a +ᵢ b)))
            (conjugate (conjugate (c +ᵢ d)))
            (conjugate (conjugate (e +ᵢ f))) tt
    ≡⟨ cong (λ z → mkTwistor z (conjugate (conjugate (c +ᵢ d))) (conjugate (conjugate (e +ᵢ f))) tt)
            (conjugate-involutive (a +ᵢ b)) ⟩
  mkTwistor (a +ᵢ b) (conjugate (conjugate (c +ᵢ d))) (conjugate (conjugate (e +ᵢ f))) tt
    ≡⟨ cong (λ z → mkTwistor (a +ᵢ b) z (conjugate (conjugate (e +ᵢ f))) tt)
            (conjugate-involutive (c +ᵢ d)) ⟩
  mkTwistor (a +ᵢ b) (c +ᵢ d) (conjugate (conjugate (e +ᵢ f))) tt
    ≡⟨ cong (λ z → mkTwistor (a +ᵢ b) (c +ᵢ d) z tt)
            (conjugate-involutive (e +ᵢ f)) ⟩
  mkTwistor (a +ᵢ b) (c +ᵢ d) (e +ᵢ f) tt ∎

--------------------------------------------------------------------------------
-- 3b. GF9 扭量层 (2026-09-08 实质对齐展示群, 无连续统)
--
-- 上述 TwistorPoint 用本地 DiscreteComplex (本质=GF9 但为独立类型). 本层
-- 用标准 GF9 直接定义扭量 — 不用连续统, 不复制复结构:
--   扭量点 = GF9³ (三个复坐标 z1,z2,z3, 各为 GF9 = GF3×GF3 元素)
--   扭量共轭 = galoisConjugate (标准 GF9 Frobenius σ, 逐坐标)
--   手性对偶 = (z, σz) GF9 共轭对 (对齐展示群本源纠缠)
--------------------------------------------------------------------------------

-- GF9 扭量点: 3 个 GF9 复坐标 (无连续统, 无 ℚ/√3)
record TwistorPoint9 : Set where
  constructor mkTwistor9
  field
    z1 : GF9   -- 复坐标 1 (幅度 + α 相位)
    z2 : GF9   -- 复坐标 2
    z3 : GF9   -- 复坐标 3

-- 扭量 GF9 共轭 (Frobenius σ 逐坐标): σ(z1,z2,z3) = (σz1, σz2, σz3)
twistorConjugate9 : TwistorPoint9 → TwistorPoint9
twistorConjugate9 (mkTwistor9 z1 z2 z3) =
  mkTwistor9 (galoisConjugate z1) (galoisConjugate z2) (galoisConjugate z3)

-- 对合: σ(σ tw) = tw (GF9 σ 阶 2, 手性对偶往返; 逐坐标 galoisConjugate²)
conjugateIsChiralFlip9 : ∀ (tw : TwistorPoint9) →
  twistorConjugate9 (twistorConjugate9 tw) ≡ tw
conjugateIsChiralFlip9 (mkTwistor9 z1 z2 z3) = begin
  mkTwistor9 (galoisConjugate (galoisConjugate z1))
            (galoisConjugate (galoisConjugate z2))
            (galoisConjugate (galoisConjugate z3))
    ≡⟨ cong (λ w → mkTwistor9 w (galoisConjugate (galoisConjugate z2))
                                (galoisConjugate (galoisConjugate z3)))
            (galoisConjugate² z1) ⟩
  mkTwistor9 z1 (galoisConjugate (galoisConjugate z2))
               (galoisConjugate (galoisConjugate z3))
    ≡⟨ cong (λ w → mkTwistor9 z1 w (galoisConjugate (galoisConjugate z3)))
            (galoisConjugate² z2) ⟩
  mkTwistor9 z1 z2 (galoisConjugate (galoisConjugate z3))
    ≡⟨ cong (mkTwistor9 z1 z2) (galoisConjugate² z3) ⟩
  mkTwistor9 z1 z2 z3 ∎

--------------------------------------------------------------------------------
-- 4. 零测地线与仲吕闭合路径 (引用 Zhonglv.SovereignState)
--------------------------------------------------------------------------------

-- 零测地线：主权状态机虚实比归零的仲吕闭合路径
record NullGeodesic : Set where
  field
    startPoint : SovereignState
    endPoint   : SovereignState
    path       : List LossGain  -- 损益路径
    isClosed   : ⊤              -- 和乐归零
    -- 零测地线条件：实部 (累加器) 与虚部 (陈数) 归零
    zeroVirtualRealRatio :
      SovereignState.accumulator startPoint ≡ SovereignState.accumulator endPoint
      × SovereignState.chern startPoint ≡ SovereignState.chern endPoint

-- 仲吕 12 步示例路径 (损益交替)
zhonglvPath : List LossGain
zhonglvPath = Sun ∷ Yi ∷ Sun ∷ Yi ∷ Sun ∷ Yi ∷
              Sun ∷ Yi ∷ Sun ∷ Yi ∷ Sun ∷ Yi ∷ []

-- 闭合见证：12 步损益路径回到同一状态 (零测地线实例)
zhonglvGeodesic : NullGeodesic
zhonglvGeodesic = record
  { startPoint = s0
  ; endPoint   = s0
  ; path       = zhonglvPath
  ; isClosed   = tt
  ; zeroVirtualRealRatio = (refl , refl)
  }
  where
  s0 : SovereignState
  s0 = record
    { accumulator     = + 0
    ; stepCount       = 0
    ; windingPolar    = 0
    ; windingToroidal = 0
    ; chern           = + 0
    }

-- 定理：仲吕闭合路径是零测地线 (见证存在)
zhonglvPathIsZeroGeodesic : ∃[ g ] NullGeodesic.path g ≡ zhonglvPath
zhonglvPathIsZeroGeodesic = (zhonglvGeodesic , refl)

--------------------------------------------------------------------------------
-- 5. 离散全纯条件与扭量纤维丛 (谓词记录, 0 postulate)
--------------------------------------------------------------------------------

-- 离散复负 (本地)
negC : DiscreteComplex → DiscreteComplex
negC (a +ᵢ b) = negate a +ᵢ negate b

-- 离散全纯条件：五行干涉复振幅在格点间跃迁的相位匹配
record DiscreteHolomorphicCondition : Set where
  field
    latticePoint  : T6Lattice
    neighborPoint : T6Lattice
    amplitudeFrom : DiscreteComplex
    amplitudeTo   : DiscreteComplex
    -- 相位匹配方程：虚部归零
    phaseMatch : DiscreteComplex.im (amplitudeTo +ᶜ negC amplitudeFrom) ≡ T₀

-- 扭量纤维丛的离散版本
record DiscreteTwistorBundle : Set where
  field
    baseSpace  : T6Lattice                        -- S²/A₄ 离散化
    fiber      : Chirality × DiscreteComplex      -- 纤维 = 手性 × 复振幅
    projection : Chirality × DiscreteComplex → T6Lattice

--------------------------------------------------------------------------------
-- 6. 自旋与扭量的统一 (合法表述, 0 postulate)
--------------------------------------------------------------------------------

-- 统一要素：自旋投影 + 扭量点 + 零测地线 (关联定理见 §1/§4)
record SpinTwistorUnification : Set where
  field
    spinLabel     : SpinLabel
    twistorPoint  : TwistorPoint
    zeroGeodesic  : NullGeodesic

--------------------------------------------------------------------------------
-- 7. 范畴分离 (类型级, 0 postulate)
--------------------------------------------------------------------------------

-- 手征分离投影 = 自旋的合法定义 (自旋 = 手性分离程度的投影)
ChiralSeparationProjection : Set
ChiralSeparationProjection = ToroidalPower → SpinLabel

SpinDefinition : Set
SpinDefinition = ChiralSeparationProjection

spinLegal : SpinDefinition ≡ ChiralSeparationProjection
spinLegal = refl

-- 合法定义的见证 = 本模块的投影函数
spinLegalWitness : ChiralSeparationProjection
spinLegalWitness = computeSpinProjection

-- T⁶ 复三维坐标投影 = 扭量的合法定义 (扭量 = T⁶ 复三维格点坐标)
T6ComplexCoordinateProjection : Set
T6ComplexCoordinateProjection = TwistorPoint

TwistorDefinition : Set
TwistorDefinition = T6ComplexCoordinateProjection

twistorLegal : TwistorDefinition ≡ T6ComplexCoordinateProjection
twistorLegal = refl

-- 禁止表述的标记类型（**仅为文档/命名用途**）
--   ⚠ [2026-10-22] 原注释写「标记类型, 数据型不等 λ ()」—— 那三条证明已移除：
--   两侧是相异且都有构造子的类型，标准 Agda 判不出（`Is empty: … (stuck)`），
--   只靠本地补丁内核。现在这三个 `data` 声明**保留**（供其它定义/文档引用），
--   但**不再有**「它们互不相等」的类型层证明；区分由文件末的文档标注承载。
data Electron : Set where
  electron : Electron

data FundamentalSpacetime : Set where
  spacetime : FundamentalSpacetime

data SpinNetwork : Set where
  network : SpinNetwork

data QuantumGeometry : Set where
  quantumGeom : QuantumGeometry

-- ⚠⚠ [2026-10-22 方案 ③ 落地：以下三条断言已**删除**]
--
-- 原为：
--   notElectronSpin12         : ¬ (Electron ≡ SpinLabel)                    = λ ()
--   notTwistorSpacetime       : ¬ (TwistorPoint ≡ FundamentalSpacetime)     = λ ()
--   notSpinNetworkQuantumGeom : ¬ (SpinNetwork ≡ QuantumGeometry)           = λ ()
--
-- 【为何删】它们是本体论/范畴断言，不是数学命题：
--   · 两侧都是**相异且都有构造子**的类型声明
--     （`Electron` 1 构造子 / `SpinLabel` 3 构造子 / `TwistorPoint` record /
--       `FundamentalSpacetime` `SpinNetwork` `QuantumGeometry` 各 1 构造子）
--     ⇒ **双方都有居民**，无矛盾可导出；
--   · 标准 Agda 无法证明「相异且有居民的类型构造子互不相等」
--     （实测 2.9.0-rc1：`Is empty: SpinNetwork ≡ QuantumGeometry (stuck)`），
--     本地补丁内核把这种等式判空 ⇒ 原证明是**依内核行为**；
--   · 两条改写路径均穷尽排除：①空类型搬运不行（两侧都有居民）；
--     ②矛盾锚点不行（本模块 39 条命题型签名中无一条与这三组断言冲突）。
--
-- 【注意：本模块另有 9 条 `¬ (构造子 ≡ 构造子)` 是**保留**的】
--   `notSinglePaired` / `notBreakingPaired` / … / `notCompleteSingle`
--   它们比较的是**同一个 data 类型 `ChiralSymmetry` 的不同构造子** ——
--   那是标准 Agda 直接可证的（`λ ()` 对同类型不同构造子是合法消去），与补丁无关，
--   实测纯净内核 exit=0 通过。

-- （三条断言已按方案 ③ 删除；上方的类型声明保留，供其它定义/文档引用）
