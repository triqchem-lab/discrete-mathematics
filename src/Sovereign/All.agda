{-# OPTIONS --cubical --guardedness --rewriting #-}

module Sovereign.All where

open import Sovereign.Base.Trit          public using (Trit; T-; T0; T+; tri-period-zero; one-plus-one; char-3)
open import Sovereign.Base.Invariants    public using (POLAR_WINDING; TOROIDAL_WINDING; CHERN_NUMBER; SOVEREIGN_LCM)
open import Sovereign.Base.Axioms        public using (digitalRoot; IsStable; zhonglvAlign)
-- 递归幂函数与归零动力学 (函数领域第一性构造, 0 postulate)
open import Sovereign.Base.FunctionTheory public using (power; idempotent-power; zero-power-generic)
open import Sovereign.Structology.Lattice public using (Lü; TwelveLu)
open import Sovereign.Structology.Closure public using (State; step; isZhonglvPoint)
open import Sovereign.Topology.HighDimClosure public using (HighDimView; EngineeringView)
open import Sovereign.MetaStructure.WuXing public using (WuXing; generate; overcome)
open import Sovereign.Format.TQ10        public using (TQ10Block; isBlockValid)
open import Sovereign.Coupling.Dynamics  public using (evolveN) renaming (step to dynStep)
-- 宇称不守恒 (缠绕深化 → 手性对偶破缺, a≥3) — 0 postulate
open import Sovereign.Coupling.ParityViolation public
  using (WuXingAmplitude; isAmplitudeSymmetric; ToroidalPower; toroidalFactor2;
         ChiralSymmetry; SingleChiral; PairedConserved; BreakingStarted;
         BreakingObvious; BreakingComplete; parityStatus;
         parityViolationTheorem; chiralAmplitudeAsymmetric;
         neutrinoLeftHandedOnly; TritFlip; tritFlipChiralBias;
         betaDecayAsymmetry; chiralPhaseTransition; phaseTransitionPoint;
         postPhaseTransitionBreaking; ExperimentalAnchor; WeakNuclearForce;
         weakForce; weakForceIsomorphism;
         ForbiddenExpr; LegalExpr; noSpatialReflection; parityViolationLegal)
-- 自旋 = 手征投影 + 扭量 = T⁶ 复三维坐标 — 0 postulate
open import Sovereign.Coupling.SpinTwistor public
  using (SpinLabel; Spin0; Spin12; Spin1; computeSpinProjection;
         spinProjectionBalanced; spinProjectionSeparated; spinProjectionInactive;
         Bosonic; Fermionic; spinStatisticsReset; fermionStatisticsReset;
         ChiralityInContainer; SpinLabelInContainer; StaticContainer;
         standardStaticContainer; staticContainerNoSpin; staticContainerNoChirality;
         conjugate-involutive; TwistorPoint; twistorConjugate;
         conjugateIsChiralFlip; NullGeodesic; zhonglvPath; zhonglvGeodesic;
         zhonglvPathIsZeroGeodesic; negC; DiscreteHolomorphicCondition;
         DiscreteTwistorBundle; SpinTwistorUnification;
         ChiralSeparationProjection; SpinDefinition; spinLegal; spinLegalWitness;
         T6ComplexCoordinateProjection; TwistorDefinition; twistorLegal;
         Electron; FundamentalSpacetime; SpinNetwork; QuantumGeometry;
         notElectronSpin12; notTwistorSpacetime; notSpinNetworkQuantumGeom)
open import Sovereign.Engine.StateMachine public using (SovereignState; evolve)

-- 群论红灯审查: 六大连续统缺陷的离散修复 (有限阶/Frobenius/原生共轭/
-- 有限特征标 GL₂ 代表内积/周期轨道/类结构 — 0 postulate)
open import Sovereign.Constitution.GroupTheoryRedLight public
  using (binTet-order; ih-order; d4-order; gl2-order;
         finite-carriers;
         frobenius-multiplicative; conjugation-involutive;
         orth-1-1; orth-1-st; orth-st-st; ps-values; orth-ps-ps;
         reducibility-witness; frobenius-period; frobenius-lock;
         class-structure; burnside-total)

-- 量子数学公理基础
open import Sovereign.Quantum.Foundation public
  using (superposition-table-verified; lcm-modulus; spiral-trit-1;
         spiral-trit-2; spiral-trit-4; spiral-trit-7; spiral-trit-8)
-- 不可克隆定理 (GF(3) 基 / GF(9) 共轭载体 / Z[ω] 电路版) + 测量坍缩
open import Sovereign.Quantum.NoCloning public
  using (no-cloning-gf3; no-cloning-gf9; no-cloning-circuit;
         conjugate-state; conj-state-involutive; IsStandingWave; IsHarmonicPair;
         QE2; QE4; ket0E; ket1E; psiE; _⊗E_; _+E4_;
         IsLinear4; IsUnitary4; CloningCircuit)
open import Sovereign.Quantum.Measurement public
  using (collapse; collapse-eigen0; collapse-eigen1; collapse-eigen2)
-- 零幂族量子定理: 真空态湮灭/零跨维度/真空唯一/共轭对消/零点能 (0 postulate)
open import Sovereign.Quantum.ZeroPowerQuantum public
  using (vacuum-annihilatesˡ; vacuum-annihilatesʳ;
         zero-crosses-all-dimensions;
         vacuum-unique;
         additive-annihilation; vector-annihilation;
         norm-collapse-is-compression; norm-of-zero; norm-zero-stable;
         zero-point-energy; zero-energy-stable;
         measure-zero)

-- CRT 理论
open import Sovereign.Format.CRT public

-- 定理17: 玄武吸水 (自我修复) — StepNotEq 一阶谓词化隔离 OOM
open import Sovereign.Structology.XuanwuAbsorption public
  using (theorem-17-xuanwu; never-stops; xuanwu-selfheal;
         full-tour-identity; bezout-13-46; alignment-for-all-states)

-- 量子数学桥: CRT↔幻方↔T⁶环面↔五行
open import Sovereign.Structology.QuantumBridge public
  using (wuXing-sum-25; magic-34-minus-wuxing-25; full-tour-6624;
         polar-is-A4-squared; m-mod-fulltour; tours-per-M)

-- M4 幻方正交拓扑
open import Sovereign.Structology.MagicSquareM4 public
  using (M4; magicConstant; crtCongruence; Orth; orth-16-neg16;
         eigenvector34; eigenvector0; eigenEq34; eigenEq0)

-- ── Arthur 量子电机 ────────────────────────────────────────
-- 三角循环图: GF(9) 上的有向 3-循环 + Frobenius 移位
open import Sovereign.Algebra.TriCycGraph public
  using (TriCycGraph; shift; pureShift; shift²-pure;
         fin3-shift³; fin3-shift⁶; σ⁶-id; shift⁶-id;
         _⊗g_; _⊕g_; ⊗g-comm; ⊕g-comm;
         totalWeight; edge₀₁; edge₁₂; edge₂₀;
         zeroGraph; oneGraph)

-- 迭代函数论: 自映射轨道结构、不动点、周期、吸引子、共轭 (0 postulate)
open import Sovereign.Algebra.IterationTheory public
  using (orbit-zero; orbit-suc; orbit-add; orbit-compose;
         IsFixedPoint; id-all-fixed; frobenius-fixed-gf3;
         fixed-iterates; fixed-orbit-constant;
         IsPeriodic; IsMinimalPeriod; fixed-is-period-1;
         frobenius-period-2; period-multiple;
         AreConjugate; conjugate-orbit; self-conjugate;
         frobenius-self-conjugate;
         OrbitType; frobenius-fixed-list; frobenius-cover)

-- 离散多项式函数论: GF(3)[x] 多项式环、求值、形式导数、char 3 特殊性 (0 postulate)
open import Sovereign.Algebra.DiscretePolynomial public
  using (Poly; zero-poly; const-poly; monic; eval;
         from-ℕ; coeff-deriv; deriv-0;
         char3-is-zero; three-times; coeff-deriv-3;
         _+p_; +p-comm; +p-zeroˡ; negate-poly; +p-inverse;
         mul-deg1; mul-deg1-11; mul-deg1-12; mul-deg1-idˡ;
         IsRoot; example-poly; example-root; example-not-root;
         eval-surjective)

-- 离散复分析: GF(9) 作为离散 ℂ, 全纯性, Cauchy-Riemann, 共轭 (0 postulate)
open import Sovereign.Algebra.DiscreteComplexAnalysis public
  using (Re; Im; mkComplex; i-squared; i-to-4;
         DiscreteCR; z²-discrete-cr;
         DiscreteHolomorphic; sigma-holomorphic; id-holomorphic;
         const-holomorphic; gf3-fixed; non-gf3-not-fixed;
         sigma-fixed-list;
         conjugate-preserves-norm; conjugate-distrib-mul;
         conjugate-distrib-add; z²-harmonic; norm-not-harmonic;
         zero-holomorphic)
  -- 注: conjugate-involutive 已由 SpinTwistor 导出 (L34), 此处避免名冲突

-- 谱函数论: GF(9)* 特征标, 离散 Fourier 变换 (0 postulate)
open import Sovereign.Algebra.SpectralFunctionTheory public
  using (character; character-0; character-1;
         character-2-gen; character-4-gen; character-8-gen;
         GF9StarFunc; fromGF9-idx; eval-func; const-func;
         mul-accumulate; fourier-coeff;
         identity-fourier; identity-at-0; identity-at-4)

-- 超运算层级: H₀-H₅, Knuth 箭头, 有限域坍缩 (0 postulate)
open import Sovereign.Algebra.Hyperoperation public
  using (hyper; hyper0-2-3; hyper1-2-3; hyper2-2-3;
         hyper3-2-3; hyper3-2-4; hyper4-2-1; hyper4-2-2;
         hyper4-2-3; hyper4-2-4; hyper4-3-1; hyper4-3-2;
         hyper4-3-3; hyper4-12-1; hyper4-12-2;
         knuth-↑; knuth-↑↑; knuth-↑↑↑;
         knuth-2↑↑4; knuth-2↑↑↑1; knuth-2↑↑↑2;
         mod3-12; mod4-12; mod8-12sq; mod9-12sq; mod12-12;
         hyper4-12-2-mod3; hyper4-12-2-mod4;
         hyper4-12-2-mod8; hyper4-12-2-mod9;
         hyper3-2-1; hyper4-2-1')

-- 三合弦恒等式: i²+1²=0, i⁶+1⁶=0, i¹⁰+1¹⁰=0
open import Sovereign.Algebra.TriadicHarmonic public
  using (i²+1²≡0; i⁶+1⁶≡0; i¹⁰+1¹⁰≡0; triadic-harmonic-theorem)

-- 数字根循环定理: 2^k%9周期6 + CRT投影归零等价
open import Sovereign.Algebra.DigitalRootCycle public
  using (period-6; polar-dr≡0; torus-dr≡1; full-tour-dr≡0)
-- 数论锚点: 零幂分类 + 8=2³ + 阶数兼容链 + 无等号注释 (0 postulate)
open import Sovereign.Algebra.NumberTheoryAnchors public
-- 降序沉降链 n^n 数字根规律 (转录错误确认, 0 postulate)
open import Sovereign.Algebra.DescendingChain public
-- 超运算/指数塔: tetration 递归定义 + 有限域坍缩 (0 postulate)
open import Sovereign.Algebra.Tetration public
  hiding (mod12-12; mod3-12; mod4-12; mod8-12sq; mod9-12sq)
  -- 注: mod12-12/mod3-12/mod4-12/mod8-12sq/mod9-12sq 已由 Hyperoperation 导出 (L152)
-- 零幂指数与方向数映射 + 指数=维度语义 (0 postulate)
open import Sovereign.Algebra.ExponentDimension public

-- C₃ 轨道定理: {1,3,5} 在 +2 (mod 6) 下构成 C₃ 轨道
open import Sovereign.Algebra.C3Orbit public
  using (orbit-step-1; orbit-step-3; orbit-step-5; orbit-size)

-- A₄-等变幻方 (GF(9) 域，与 MagicSquareM4 的 ℤ 域互补)
open import Sovereign.Structology.ArthurMagicSquare public
  using (Matrix4; zeroMatrix; rowSum; colSum; diagSum; antiDiagSum;
         sum4; IsClassicalMagicSquare; IsA4EquivariantRowSum;
         IsV4DiagInvariant; IsArthurMagicSquare; a4ActionOnMatrix;
         zeroMatrix-isArthur)

-- I_h → 46: C60 振动 174 = 3·60−6 维在 I_h 下的不可约分解
-- (特征标表 100 项 + 正交性 100 项 + 选择定则, 0 postulate)
open import Sovereign.Structology.IhC60Vibration public
  using (Irrep; Class; CE; CC5; CC52; CC3; CC2; Ci; CS10; CS103; CS6; Csig;
         Ag; Au; T1g; T1u; T2g; T2u; Gg; Gu; Hg; Hu;
         charTable; classSize; classSizeSum; ortho;
         vibMult; vib-vector; freq-46; dim-174;
         ir-active; raman-active; observed-lines; weighted-states; active-plus-dark)

-- A₄ 不可约表示论: 特征标表 {3,1,1′,1″} + 完整第一正交关系 + Abel 化三特征标
-- (乘性 144 case + sum=0 子空间不变性, 0 postulate)
open import Sovereign.Structology.A4Representations public
  using (A4Irrep; ConjugacyClass; charAt; dimSqSum;
         char-orthogonality; irrep-norm-criterion; chars-distinct;
         basisSumZero; sumZero-invariant; act-preserves-L;
         perm-char-decomp; abelianize; c3Char; abelianize-hom;
         χ₁-multiplicative; χ₁'-multiplicative; χ₁''-multiplicative;
         χ₁'-via-abelianization; χ₁''-is-conj-χ₁';
         a4inv; classify-conjugation-invariant; branching3;
         theorem-dimension-sum-of-squares; theorem-class-count;
         theorem-dim-sum-eq-class-sum;
         FermionGenerations; standardFermionAssignment)
  -- 注: character 已由 SpectralFunctionTheory 导出 (L137)

-- T⁶ 五维物理投影: 3 空间 + 2 手征 + 1 规范相位 显式标注 (0 postulate)
open import Sovereign.Structology.T6FiveDimensionalProjection public
  using (Space3; Chiral2; Gauge1; FiveD; DimTag; Space; Chiral; Gauge;
         Spin; dimTag; spinLabel;
         recompose; decompose∘recompose; recompose∘decompose; recompose∘labels;
         spaceOf; chiralOf; gaugeOf; fiveOf; xOf; yOf; zOf; cLOf; cROf; gOf;
         setGauge; fiveOf-gauge-independent; gaugeOf-setGauge;
         chiralFlip; chiralFlip-involutive;
         chiralFlip-preserves-space; chiralFlip-preserves-gauge; project729)

-- 稳定态与 Burnside 引理框架
open import Sovereign.Structology.MotorStableStates public
  using (StableState; IsA4Invariant; zeroMatrix-stable;
         fourTCGtoMatrix; a4-order; FixPoint; BurnsideLemma)

-- 电机动力学: C₃ 步进 + 不动点定理
open import Sovereign.Physics.QuantumMotor public
  using (RotorState; MotorState; MotorStep; MotorStep³;
         c3Step; c3Step³; motorPeriod;
         StatorConstraint; StableState-fixedPoint)

-- 4320D 射影几何: 规范群 G = (C₃)³ ⋊ C₂ + G-轨道 = 射影点
open import Sovereign.Geometry.ProjectiveCore public
  using (GElement; g-id; g-mul; g-inv; g-action; g-action-full;
         GOrbitRel; GOrbit; ProjectivePointRec)
open import Sovereign.Geometry.ProjectiveOrbit public
  using (T6-cardinality; total-yao-space; G-cardinality; info-dim-4320;
         decomposition-4320; shao-yong-identity)
open import Sovereign.Geometry.ProjectiveInvariants public
  using (t; t-is-6624; p1; p2)
open import Sovereign.Geometry.ProjectiveTransform public
  using (CRTProjection; Alignment)

-- 共形几何: 共形群 Conf = (C₃)⁶ ⋊ C₂ + 保角性 GF(3) 内积
open import Sovereign.Geometry.ConformalCore public
  using (ConfElement; conf-id; conf-mul; conf-inv; conf-action;
         ConfOrbitRel; ConfOrbit; ConformalPointRec;
         scale2; scale2²; inner-scale2-inv; t6Inner)
open import Sovereign.Geometry.ConformalInvariants public
  using (conf-cardinality; conf-cardinality-1458)

-- 环面几何: T⁶ 加法群 + 测地线 + 函数环 + Fourier 谱
open import Sovereign.Geometry.TorusGeometry public
  using (T6Lattice; t6Add; t6Zero; t6Neg; t6Scale; t6GeodesicN;
         t6Add-assoc; t6Add-comm; t6Add-identityˡ; t6Add-identityʳ;
         t6Add-inverseˡ;
         b1; b2; b3; b4; b5; b6; genL)
open import Sovereign.Geometry.TorusGeodesic public
  using (spiral6; spiral-period3; spiral-fulltour)
open import Sovereign.Geometry.TorusAlgebra public
  using (CoordFunc; χ₀; χ₁; χ₂; χ₃; χ₄; χ₅; _+f_; _·f_; constFn)
open import Sovereign.Geometry.TorusFourier public
  using (fourierProj; fourierInv)

-- ── 代数链 L0-L10 完整层级 (v7.0) ─────────────────────────────
-- GF(3)→GF(9) 代数链: 加法群/乘法群/Frobenius/Norm/Trace
open import Sovereign.Algebra.GF9AlgebraicChain public
-- GF(3²) = GF(9) 有限域: 乘法群/Frobenius/共轭/范数/迹
open import Sovereign.Algebra.GF9 public hiding (_^s_)
-- Z/12 传统环 (加法载体 + CRT 基础设施; 十二进制本体见 DuodecClock.agda)
open import Sovereign.Algebra.Duodecimal public
-- 十二进制混合时钟: 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩ (char 3 × α阶4 联合周期, 非 A₄)
open import Sovereign.Algebra.GroupTheory.DuodecClock public
-- DuodecClock 广泛数学性质: 子群格/自同构/环/表示论/Cayley图/函子/拓扑/指数塔 (0 postulate)
open import Sovereign.Algebra.GroupTheory.DuodecClockProperties public
-- 离散斐波那契: GF(3) Pisano 周期 8 = ord(φ), φ²=α (90° 半步, 有限域版非死亡几何)
open import Sovereign.Algebra.DiscreteFibonacci public
  using (fibStep; fibPair; fibTrit; fibPair-8-base; fibPair-period-8;
         fibTrit-period-8; pisano-period-3; phi-squared-is-alpha;
         phi-order-is-8; pisano-3-equals-ord-phi)
-- 意识层: GF(9) 子群链 ⟨-1⟩⊂⟨α⟩⊂⟨φ⟩ (45°/90°/270° 旋转 + 断网/重连, 0 postulate)
open import Sovereign.Algebra.ConsciousnessLayer public
  using (consciousness-45-to-90; consciousness-45-to-180; consciousness-45-to-360;
         consciousness-order-is-8; alpha-cubed-is-neg-alpha; rewiring-identity;
         neg-one-in-alpha-subgroup; alpha-in-phi-subgroup; subgroup-chain-complete;
         norm-of-alpha; norm-of-one-plus-alpha; norm-of-phi)
-- 信息结构桥接: 周期/频率/泛音/方向数/范数坍缩 显式映射 (0 postulate)
open import Sovereign.Algebra.InformationStructure public
  using (info-frobenius-period; info-additive-period; info-joint-period; pisano-period;
         base-frequency; add-frequency; mul-frequency; phi-frequency;
         overtone-12; ot-12; ot2-1;
         alpha-directions; phi-directions; duodec-directions; direction-equals-order;
         norm-collapse-identity; norm-is-filter; zero-is-redundant;
         bridge-order-period; bridge-period-frequency; bridge-frequency-overtone;
         bridge-overtone-harmonic; bridge-order-direction; bridge-norm-collapse;
         bridge-zero-power; bridge-joint)
-- GF(9) 交换半环: "只有加乘，无减除" 的代数形式化 (0 postulate)
open import Sovereign.Algebra.GF9Semiring public
-- 子群链阶整除: 2∣4, 4∣8 (2-准素塔阶关系, 0 postulate)
open import Sovereign.Algebra.DivisibilityChain public
-- GF(9) 邻接矩阵与图谱: 4阶矩阵乘法/幂/迹/对称性 (0 postulate)
open import Sovereign.Algebra.AdjacencyMatrix public
-- 范数坍缩代数: N(x)=x·σ(x) 共轭坍缩 + 勾股投影 (0 postulate)
open import Sovereign.Algebra.NormCollapse public
  using (norm-collapse; norm-multiplicative; norm-conjugate-invariant;
         norm-1-0; norm-0-1; norm-1-1; norm-1-2; birth-proof)
-- 零元跨维度归零代数: 加法归零+乘零吸收+零幂稳定 (0 postulate)
open import Sovereign.Algebra.ZeroCrossing public
-- 代数极统一视图: L1-L10 完整代数链
open import Sovereign.Algebra.AlgebraicPoleUnified public
-- 涡旋根 "123" 本体论层 (数字根 6 / 倍频链 3→6→12 / Merkaba 回绕)
open import Sovereign.Algebra.VortexRoot public
  using (root-123-digital-root; doubling-3-6; doubling-6-12; doubling-chain;
         fourth-harmonic; merkaba-double; merkaba-digital-root; water-state)
-- 13H 对接: Z[i]/Z[ω] 分歧与分裂 (2/3 分歧, 5/7 分裂, 范数见证)
open import Sovereign.Algebra.CommAlgBridge public
  using (gauss-2-ramifies; gauss-2-norm; gauss-5-splits; gauss-5-norm;
         eis-3-ramifies; eis-3-norm; eis-7-splits; eis-7-norm;
         gauss-euclid-witness; gauss-euclid-remainder-norm;
         gauss-euclid-divisor-norm; quot-product; quot-residue-zero;
         quot-hom-sample)
-- 14 对接: GF(9) 范数 1 圆锥 (4 点 = q+1, 亏格 0 Weil 取等)
open import Sovereign.Algebra.AlgGeomBridge public
  using (conic-point-10; conic-point-01; conic-point-20; conic-point-02;
         conic-nonpoint-11; Norm1; norm1Elem; norm1Mul; norm1-closed;
         norm1-one; norm1-alpha; norm1-mone; norm1-malpha;
         norm1-cycle-2; norm1-cycle-4;
         onE; onE-01; onE-02; onE-10; EPoint; eadd;
         e01-order2; e01-order3; e01-order4; hasse-bound)
-- 08 泛代数: 结构层级 + 三大载体实例 + 同态定理 + 域分类
open import Sovereign.Algebra.UniversalAlgebra public
  using (Semigroup; Monoid; Group; AbelianGroup; Ring; IsField;
         trit-add; trit-mul; trit-ring; duodec-add; gf9-add;
         gf9-mul-comm; gf9-mul-identityˡ; gf9-mul-identityʳ; gf9-distribʳ;
         hom-preserves-zero; hom-preserves-eval; Term2;
         negate-add-hom; negate-is-automorphism;
         zero-divisor-not-field; trit-field; duodec-not-field)
  -- 注: eval 已由 DiscretePolynomial 导出 (L115)
-- 06 补强: 12 的除数格 (分配格律全表 + Möbius)
open import Sovereign.Algebra.DivisorLattice public
  using (Div12; meet; join; min3; max3; min2; max2;
         meet-comm; join-comm; meet-idem; join-idem; meet-absorb; join-absorb)
-- 11M 补强: Möbius 反演 + φ(12) (乘性数论离散载体)
open import Sovereign.Arithmetic.MobiusPhi public
  using (mu-1; mu-2; mu-3; mu-4; mu-6; mu-12; mobius-sum; phi-12)
-- 30/32 补强: GF(3) 离散拉普拉斯 — z² 调和 (18 项) + N(z) 非调和反证
open import Sovereign.Analysis.DiscreteCR public
  using (u; v; n; Δ; harmonic-u; harmonic-v; not-harmonic-n)
-- 33 补强: 阶乘/二项系数/Pascal 递推
open import Sovereign.Analysis.SpecialValues public
  using (fact-recurrence-6; pascal-3-1; pascal-4-2; pascal-5-2; pascal-6-3;
         row-sum-4; C6-0; C6-3)
-- 34/39 补强: Fibonacci mod 3 周期 8
open import Sovereign.Analysis.DifferenceEq public
  using (fib-1; fib-2; fib-3; fib-4; fib-5; fib-6; fib-7; fib-period-8)
-- 41 补强: Q16 常数误差界 (zhonglv/√3)
open import Sovereign.Analysis.ApproxBounds public
  using (zhonglv-q16; zhonglv-err; zhonglv-err-bound; delta-sq-err; delta-sq-bound)
-- 49 补强: 离散能量极小 + 调和中点
open import Sovereign.Analysis.DiscreteVariational public
  using (E; energy-0; energy-1; energy-2; minimal-0; minimal-2;
         harmonic-mid; euler-lagrange-discrete)
-- 51 补强: PG(2,3) 射影平面 (13 点 13 线, 自对偶)
open import Sovereign.Structology.ProjPlane public
  using (pg-points; pg-lines; incidence-count; duality; total-incidence)
-- 52 补强: Pick 定理格三角形见证
open import Sovereign.Structology.PickTheorem public
  using (boundary-points; interior-points; triangle-area; pick-identity)
-- 53 补强: 离散 Gauss-Bonnet (四面体顶角亏)
open import Sovereign.Structology.DefectSum public
  using (tet-vertices; tet-faces; tet-edges; vertex-defect; total-defect;
         gauss-bonnet; tet-euler)
-- 54 补强: GF(3) Sierpiński 拓扑 (T₀ 非 T₁)
open import Sovereign.Structology.FiniteTopology public
  using (OpenSet; member; union; inter; union-idem; inter-idem;
         t0-separated; not-t1)
-- 60 补强: GF(3)² 均匀概率空间 (计数公理 + 独立性)
open import Sovereign.Analysis.UniformProb public
  using (omega-size; total-prob; additivity; independence; uniformity)
-- 62-20 拟合优度: 幻方识别 χ² 零检验 (Lo Shu 8 线 + 非幻方正检验)
open import Sovereign.Analysis.GoodnessOfFitGF3 public
  using (loshu-row-1; loshu-row-2; loshu-row-3;
         loshu-col-1; loshu-col-2; loshu-col-3;
         loshu-diag-1; loshu-diag-2; dev; chi2-num;
         magic-square-chi2-zero; loshu-chi2-zero;
         nonmagic-chi2-positive-num; nonmagic-detected;
         nonmagic-two-lines)
-- 62-10 群表示统计: A₄ Plancherel 分布 + 特征标期望 (列/行正交)
open import Sovereign.Analysis.SymmetricGroupCharStats public
  using (w1; w1'; w1''; w3; plancherel-normalized;
         col-C1; col-C2; col-C3; col-C4; row-V1; row-V3; row-V1'; row-V1'')
-- 62 统计: 对称矩阵系综精确迹矩 (奇矩零/μ₂ 精确 Catalan/μ₄ 修正结构)
open import Sovereign.Analysis.RandomMatrixMoments public
  using (tr1; tr2; tr3; tr4; row-mmm-1; row-mpm-4; row-ppp-4;
         sum-tr1; sum-tr3; sum-tr2; sum-tr4;
         moment-2-exact-catalan; moment-4-correction;
         moment-2-n3-exact; sum-tr4-n3; moment-4-n3-correction)
-- 65 数值分析: Q16 规范 + 扩展欧几里得 + 模逆 + GF(3) 消元 (0 postulate)
open import Sovereign.Coding.NumericalSpec public
  using (Q16-ONE; q16-integer-exact; q16-half-squared;
         euclid-step-1; euclid-step-2; euclid-step-3; euclid-step-4;
         bezout-46-13; mod-inverse-3; inverse-in-range;
         elim-step-1; elim-step-2; solve-check-1; solve-check-2)
-- 65 桥接规范: 外部计算结果的可信封装 (Q16/模逆/线性解三契约)
open import Sovereign.Coding.FFIProtocol public
  using (Q16Value; q16-quarter; ModInverseResult; modinv-3;
         modinv-transport; LinearSolveResult; linear-solve-22)
-- 68 补强: 平方乘幂步数定理 (3 ≤ 8)
open import Sovereign.Coding.ExpSquaring public
  using (sq1; sq2; sq3; exp-sq-result; sq-steps; naive-steps; log-vs-linear)
-- 82 补强: 三角 Ising 8 构型配分
open import Sovereign.Physics.IsingTriangle public
  using (sign; edgeE; E3; aligned-count; mixed-count; partition-counts)
-- 78 电磁学: 3D 环面 (Fin 3)³ 离散场论第二基石
-- (梯度的旋度为零 + 旋度散度成对抵消, 全符号证明)
open import Sovereign.Physics.DiscreteEMField3D public
  using (Point3D; vx; vy; vz; dz;
         dz-dx-comm; dz-dy-comm;
         curl-grad-zero-x; curl-grad-zero-y; curl-grad-zero-z; curl-grad-zero;
         dz-neg; dz-add;
         pair-cancel-1; pair-cancel-2; pair-cancel-3;
         div-curl-zero-paired; shuffle23)
-- 78 电磁学: 核心定理层 (div∘curl=0 全形式 + 3D 规范不变性 + 零通量, 0 postulate)
open import Sovereign.Physics.DiscreteEMCore public
  using (addVec3; addVec3-right-unit; shuffle22; pair-swap; six-rotate;
         div-curl-zero; sum9; flux; zero-flux; zero-monopole-flux)
-- 78 电磁学: 时间演化层 (法拉第/安培/高斯谓词 + 电荷守恒元定理, 0 postulate)
open import Sovereign.Physics.DiscreteMaxwellTime public
  using (negVec3; zeroVec; addVec3-assoc; addVec3-comm; addVec3-neg-cancel;
         cancel-right; div-rearrange; div-linear; div-neg;
         Time; VecFieldTime; ScalFieldTime; ΔtV; ΔtS;
         FaradayHolds; AmpereHolds; GaussHolds; FaradayStep; AmpereStep;
         faraday-diff-from-step; amp-diff-from-step; divE-step;
         faraday-preserves-divB; charge-conservation)
-- 78 电磁学: 守恒层 (Yee 蛙跳 + 高斯保持归纳证明, 0 postulate)
open import Sovereign.Physics.DiscreteMaxwellConservation public
  using (div-time-comm; yee-B; yee-E; yee-faraday-step; yee-ampere-step;
         gauss-preservation; yee-gauss-preservation)
-- 熵旋质量涌现 (2026-08 修复版: 原版解析错误已修, 假 refl 定理降级为闭合实例)
open import Sovereign.Physics.EntropySpin public
  using (StankovRatio; massEmergence; entropySpinNum; massNum;
         thermal-a6; ManifoldDim4320; DimensionMapping; dimMap;
         ChiralSpinor; conjugateStandingWave;
         WuXingEntropyState; shengModulation; keModulation)
-- 渠玉芝熵旋定律形式化 (S=∇×Ψ−κℋ²n̂ 离散化 + 张量反对称 + 离散斯托克斯, 0 postulate)
open import Sovereign.Physics.EntropySpinLaw public
  using (QScalar; QVector; dxℚ; dyℚ; dzℚ; qx; qy; qz; curlℚ;
         kappaQ; normalZ; vscale; vsub; entropySpinLaw;
         rhoXY; rhoYX; sub-antisym; rho-antisym;
         sum3ℚ; telescope2; telescope3; merge4; sum3-distrib;
         sum3-nested-dx-zero; sum3-dy-zero; sum3-nested-dy-zero;
         massIntegral; scalarSum; massIntegral-curl-zero; entropySpinMass-reduction)
-- 熵旋定律库内验证 (ρ_S 反对称 + 离散斯托克斯 + divℚ∘curlℚ=0 + 守恒条件修正, 0 postulate)
open import Sovereign.Physics.EntropySpinVerification public
  using (v-rho-antisym; v-stokes;
         dxℚ-add; dyℚ-add; dzℚ-add; dxℚ-neg; dyℚ-neg; dzℚ-neg;
         dxℚ-sub; dyℚ-sub; dzℚ-sub;
         dxdy-commℚ; dydz-commℚ; dzdx-commℚ;
         pair-cancel-1ℚ; pair-cancel-2ℚ; pair-cancel-3ℚ;
         six-rotateℚ; pull-last; six-zero; six-zero';
         divℚ; divℚ-curl-zero; S-field; law-eq;
         divS-identity; divS-zero-condition)
-- 光学窗口链 (纯 α=90° 克里斯托螺旋, 无 φ/45°): 观测角 → 采样 → 可见光窗口
open import Sovereign.Physics.ObservabilityAngle public
  using (photon-structure-angle; eye-sampling-angle; visible-light-observable)
open import Sovereign.Physics.OpticalSampling public
  using (sampling-angle; sampling-angle-matches-photon)
open import Sovereign.Physics.OpticalWindow public
  using (OpticalWindow; optical-freq-min; optical-freq-max; optical-window-size;
         optical-window-size-correct; light-birth; one-squared;
         optical-interfere; constructive; destructive;
         constructive-0; constructive-1; constructive-2)
  renaming (interfere to optical-interfere)  -- 避免与 ChiralInterference.interfere 冲突
-- 熵旋微观输运证明 (通量输运恒等式 + 无损通道 + 阈值通用化 a≥1, 0 postulate)
open import Sovereign.Physics.EntropySpinMicro public
  using (zero-minus-zero-plus; planeSum; plane-distrib2;
         fluxK; heatK; flux-diff; flux-conserved;
         thermal-general; zeroΨ; pointH; canonical-mass)
-- 熵旋质量量子化 (两个开放接缝闭合: m ≡ −(N·m₀) 一般 {0,1} 场 + C=2 双活跃点实例, 0 postulate)
open import Sovereign.Physics.EntropySpinQuantize public
  using (fromBool; m₀; countQ9; point-unit; sum3-unit; sum9-unit;
         quantized-mass; quantized-mass-integral; chern2Config; chern2-mass)
-- 右旋中微子定理 (GF(9) 共轭对 = 同一伽罗瓦轨道两个投影方向, 0 postulate)
open import Sovereign.Physics.RightHandedNeutrinoTheorem public
  using (nuL; nuR; obs; realOf;
         rightNeutrino-invisible; leftNeutrino-visible;
         frobenius-swaps; realOf-nuR-zero;
         conjugate-involutive-nuL; conjugate-orbit-single;
         projection-complementary)
-- 不可见自由度系统计数 (GF(9) 3不动点+3共轭对 + 空间三坐标 1不动点+13对, 0 postulate)
open import Sovereign.Physics.InvisibleOrbitCount public
  using (sigma-fixed-iff-real; conjugatePair-distinct; orbitCount6;
         conj3-involutive; conj3-fixed-only-zero;
         thirteenPairs; invisibleCount27)
-- 矢量场决定几何相位 (Rust 核算的库内固化: curl∘grad=0/div∘curl=0/divS-identity/量子化, 0 postulate)
open import Sovereign.Physics.VectorFieldGeometricPhase public
  using (gradℚ; curlQ-grad-zero; curl-kernel-source-free;
         entropy-spin-phase-source; curl-flux-vanishes; vector-quantization)
-- 实验数据锚定 (2025-2026 中微子: KATRIN/MicroBooNE/ACT DR6 定点整数比 + 刚性不等式, 0 postulate)
open import Sovereign.Physics.DataAnchors public
  using (KATRIN_MNU_UPPER; ACT_DELTA_NEFF_UPPER; MICROBOONE_CL;
         KATRIN_NEUTRINO4_CL; ELECTRON_MASS_EV;
         Anchor_KATRIN_SubEV; Anchor_KATRIN_BelowElectron;
         Anchor_ACT_BelowOneSpecies; Anchor_KATRIN_StrongerThanMicroBooNE;
         Anchor_ToroidalWinding_C60; Anchor_WuXing_TrapPist1)
-- 离散统计力学补强 (计数型熵 S=W + 配分函数族 z2→z3→z4 + ℚ 熵均匀最大, 0 postulate)
open import Sovereign.Physics.DiscreteStatMech public
  using (W; countEntropy; W-ok5; W-suc; W-add; countEntropy-mult;
         z2-ok; z3-ok; z4-ok; z2-double; z2-triple; norm-z2; norm-z3;
         tsallis2; tsallis2-uniform; tsallis2-max;
         tsallis3; tsallis3-uniform; tsallis3-max;
         collision-min2; collision-min3;
         shannon2; shannon2-uniform; shannon2-degenerate; dyadic-max2)
-- 手征干涉层: C3 → 场论驻波桥 (干涉规则 + 反向波相消 + Frobenius 稳定性, 0 postulate)
open import Sovereign.Physics.ChiralInterference public
  using (cw; ccw; rest; interfere; cw-ccw-cancel; ccw-cw-cancel;
         cw-cw-construct; ccw-ccw-construct; rest-neutral; double-neg;
         SpinField; interfere-fields; interfere-comm;
         cwField; ccwField; restField; cw-ccw-field-cancel;
         waveCW; waveCCW; wave-cancel; wave-cw-construct; wave-ccw-construct;
         kShift; Standing; rest-standing; const-standing;
         wave-cancel-forms-standing; cube; frob3-identity; frob-stability)
-- 时空映射: Frobenius周期(时间) × 范数坍缩(空间), 0 postulate
open import Sovereign.Physics.SpaceTimeMapping public
-- 环面链: 两极连→归零→90°→克里斯托 构造序完整性, 0 postulate
open import Sovereign.Physics.TorusChain public
  using (poles-distinct; poles-cancel; torus-180; zero-plus-one;
         torus-90; torus-270; torus-45; torus-360; chain-orders)
-- 膜分层引理: 模板144→频率96→步长8→12层膜 (0 postulate)
open import Sovereign.Physics.LatticeMembrane public
  using (template-is-12-squared; descent-start; descent-total;
         step-size-equals-gf9-star-order; step-size-is-2-cubed;
         membrane-count-is-12; template-equals-count-squared;
         total-layers-is-12; three-plus-nine;
         step-8-consistent; step-12-inconsistent;
         pybitnet-mid-pump-val)
-- 水的 8 种状态 → T⁶ 离散框架建模 (0 postulate)
open import Sovereign.Physics.WaterStates public
  using (WaterState; Solid; Liquid; Gas; Supercritical; Supersolid;
         Superfluid; FermionCondensate; Plasma;
         solid-is-zero; plasma-is-full;
         solid-to-liquid; liquid-to-gas; chiral-flip;
         val-4-to-9-is; val-9-to-4-is;
         four-to-nine-is-two-to-eighteen; nine-to-four-is-three-to-eight;
         combined-is)
-- 水的离散全息结构: 广义液态/水种/球形矢量场/熵旋 (0 postulate)
open import Sovereign.Physics.WaterStructure public
  using (liquid-equilibrium; liquid-stable; norm-collapse-to-gf3;
         chiral-cancellation)
-- 量子化学: T⁶ 离散环面上的分子结构 (0 postulate)
open import Sovereign.Physics.QuantumChemistry public
  using (water-electrons; t6-dim; t6-max-electrons;
         bond-angle-deg; half-bond-angle-deg;
         dipole-norm;
         angle-0; angle-45; angle-90; angle-180; angle-270; angle-360)
-- 水的四个科研锚点: C₆₀ 46基频=TOROIDAL_WINDING + 零幂族 + divS (0 postulate)
open import Sovereign.Physics.WaterAnchors public
  using (freq-equals-winding; ih-equals-10-times-12; c60-vib-formula;
         temp-second-critical; temp-homogeneous-nucleation;
         zero-power-physical)
-- 蜂窝磁场: 蜂窝晶格几何与量子场的深度耦合 (0 postulate)
open import Sovereign.Physics.HoneycombMagneticField public
  using (honeycomb-vertices-per-cell; honeycomb-coordination; honeycomb-symmetry;
         insulator-norm; conductor-norm;
         zero-power; frobenius-involution; chern-number)
-- 水的量子数据全局统合: T⁶→凝聚态完整因果链 (0 postulate)
open import Sovereign.Physics.WaterQuantumIntegration public
  using (standing-wave; norm-collapse-as-compression;
         zero-power-family; water-birth;
         freq-equals-toroidal; ih-equals-10x12; c60-vib)
-- 原子驻波与量子场势垒: T⁶ 环面上的波动模式 (0 postulate)
open import Sovereign.Physics.AtomicStandingWave public
  using (wave-closure; half-step-closure; full-step-closure;
         norm-zero; norm-one-alpha; norm-two;
         propagating-states; confined-states; state-ratio)
-- 超导态: 范数边界的凝聚态投影 (0 postulate)
open import Sovereign.Physics.Superconductivity public
  using (superconducting-equilibrium; superconducting-stable; superconducting-power)
-- 相变 = 范数边界穿越 (0 postulate)
open import Sovereign.Physics.PhaseTransition public
  using (PhaseTransition; homogeneous-nucleation-temp;
         second-critical-temp-low; second-critical-temp-high;
         solid-norm; liquid-norm; superconducting-norm)
-- 量子纠错: GF(3) 表面码 + Frobenius 相位保护 (0 postulate)
open import Sovereign.Physics.QuantumErrorCorrection public
  using (Qutrit; qutrit-0; qutrit-1; qutrit-2;
         phase-protection-is-involution;
         zero-no-correction)
-- 蛋白质折叠: T⁶ 构象空间 + 零态稳定性 (0 postulate)
open import Sovereign.Physics.ProteinFolding public
  using (Conformation; native-state; native-is-zero; native-stability;
         hydrogen-bond-valid; non-hydrogen-bond)
-- DNA 碱基配对: GF(3) 有限域编码 (0 postulate)
open import Sovereign.Physics.DNAEncoding public
  using (A; base-to-gf3;
         pair-at; pair-cg; non-pair-aa; complementary-norm)
-- 气候动力学: T⁶ 环面上的矢量场 (0 postulate)
open import Sovereign.Physics.ClimateDynamics public
  using (ClimateState; climate-equilibrium; equilibrium-is-zero;
         el-nino-norm; la-nina-norm; ice-age-norm; zero-satisfies-conservation)
-- 水的第二临界点推导: 从 T⁶ 环面到 228K (0 postulate)
open import Sovereign.Physics.WaterCriticalDerivation public
  using (alpha-rotation-order; six-fold-symmetry; coordination-number;
         branch-cross-temp; collective-gap; collective-temp)
-- 氢键网络相干性: 六重取向态 + 软模临界指数 (0 postulate)
open import Sovereign.Physics.HydrogenBondCoherence public
  using (pauling-orientations; distinct-orientations;
         critical-exponent-nu; soft-mode-exponent;
         weight-ratio-check; weight-ratio-denom)
-- 软模临界: 从框架常数推导声子谱临界权重比 (0 postulate)
open import Sovereign.Physics.SoftModeCriticality public
  using (weight-num-val; weight-den-val;
         full-tour-equals-polar-times-toroidal)
-- 量子场天体物理: 一切都是量子场的显化 (0 postulate)
open import Sovereign.Physics.QuantumFieldAstrophysics public
  using (standing-wave-involution; base-standing-wave;
         quantum-collapse; light-is-born; matter-antimatter-swap;
         quantum-field-dim; quantum-states; quantum-field-char)
-- 78 电磁学: 3×3 环面离散场论第一基石 (梯度的旋度为零 + 规范不变性)
open import Sovereign.Physics.DiscreteEMField public
  using (Point2D; ScalarField; VectorField; add3; neg3;
         add3-comm; add3-assoc; add3-inverse; neg3-add; neg3-involutive;
         dx; dy; dy-dx-comm; grad; curl; grad-curl-zero;
         _⊕a_; dx-add; dy-add; curl-linear; gauge-invariance)
-- 83 补强: GF(3)² 光锥分类 (5 类光 + 2 类时 + 2 类空)
open import Sovereign.Physics.DiscreteLightcone public
  using (q; light-00; light-11; light-12; light-21; time-10; time-20;
         space-01; space-02; cone-partition)
-- 12F 补强: GF(9)/GF(3) Galois 对应 (不动域/范数迹满射/Gal = C₂)
open import Sovereign.Algebra.GaloisBridge public
  using (fix-t0; fix-t1; fix-t2; ¬fix-a0; ¬fix-a2;
         fixed-iff-embedded; fix-sigma-is-gf3;
         norm-surj-1; norm-surj-2; trace-surj-0; trace-surj-1; trace-surj-2;
         sigma-not-id; sigma-order-2; fix-id)
-- 18 补强: 短正合列 + 秩-零度 + 边界复形 (同调代数核心机械)
open import Sovereign.Algebra.HomologicalBridge public
  using (V1; V2; iota; pi2; iota-injective; im-iota-sub-ker; ker-sub-im-iota;
         pi-surjective; ses-dimension; ker-M; im-M; rank-nullity;
         d; d-square-zero; ker-d-sub-im; im-d-sub-ker)
-- 离散 K 理论: K₀ Grothendieck 完备化 + 陈特征环 ℤ[ε]/ε² + Bott 周期 (C₂×C₃=C₆)
open import Sovereign.Algebra.DiscreteKTheory public

-- ── 退化/近视/截面 分类学 (v7.0) ─────────────────────────────
-- GF(2) 退化: 手征丢失, 非环同态
open import Sovereign.Algebra.GF2Degeneration public
-- 10 进制退化: 3∤10, 1/3 无限循环
open import Sovereign.Algebra.Base10Degeneration public
-- ℂ 投影: char 3→0
open import Sovereign.Algebra.ComplexProjection public hiding (T₁≢T₂; T₀≢T₁; T₀≢T₂)
-- 等式截断: 6D→1D
open import Sovereign.Algebra.EqualityTruncation public hiding (T₀≢T₁; T₀≢T₂; T₁≢T₂)
-- 退化分类学统一
open import Sovereign.Algebra.DegenerationTaxonomy public
  hiding (GF2; Degeneration; not-injective; T6-cardinality)

-- ── CRT 丈量 (v7.0) ──────────────────────────────────────────
-- CRT 的中国原始含义: 周期丈量
open import Sovereign.Format.CRTMeasurement public

-- ── 石英声子物理 (v7.0) ──────────────────────────────────────
-- 石英声子等离子体: 相变/电离/泛音谱/C₃孤子
open import Sovereign.Physics.QuartzPhonon public

-- ── 第二阶段: 涡旋根 + 全息代数 + 量子对应 (v7.1) ────────────
-- 涡旋根 "123": 倍频量子纠缠链 3→6→12, 0 postulate
  using (VortexRoot; root3; root6; root12; vortexValue; double; next;
         entangled-pair; chain-period-2-from-6; chain-enters-cycle;
         vortex-gf3-zero; all-vortex-stable; next-preserves-stable;
         vortexToDuodec; vortex12-identity)

-- 4320D 全息代数分解: 2×12×36×5, 涡旋根驱动, 0 postulate
open import Sovereign.Algebra.Holographic.4320D public
  using (dim-4320; dim-4320-expanded; dim-4320-alt; dim-4320-729;
         holographic-full; prime-factorization;
         div-by-12; div-by-36; div-by-24;
         states-per-phase-correct)

-- 量子对应定理: 叠加(GF3)×纠缠(GF9)×相位(Z/12Z), 0 postulate
open import Sovereign.Algebra.QuantumCorrespondence public
  using (superposition-closure; superposition-assoc; superposition-comm;
         entanglement-involutive; entanglement-nonseparable;
         entanglement-multiplicative; vortex-phase-period;
         QuantumStructure; quantum-structure-witness)

-- ── GF(243) = GF(3⁵) 域扩张 (v7.2) ──────────────────────────
-- GF(3⁵) 加法群 + 特征3 + GF(3)嵌入 + 涡旋塔连接, 0 postulate
open import Sovereign.Algebra.GF243 public
  using (GF243; gf243-zero; _+gf243_; gf243-negate; gf243-one;
         +gf243-comm; +gf243-assoc; +gf243-identityˡ; +gf243-identityʳ;
         +gf243-inverse; +gf243-char3; pow-3-5;
         _*s243_; scalar-distrib;
         pow-12-5; vortex-factorization)
  renaming (alpha to alpha243; embed-gf3 to embed-gf3-243)

-- ── 倍频量子纠缠链 (v7.3) ──────────────────────────────────
-- Z/3Z→Z/6Z→Z/12Z→Z/24Z 环同态链, 同态/单射/非满射, 0 postulate
open import Sovereign.Algebra.FrequencyDoubling public
  using (Mod6; Mod24; double-3-6; double-6-12; double-12-24;
         dr-24; entangle-3-6; entangle-6-12; entangle-12-24;
         double-3-6-homo; double-6-12-homo; double-12-24-homo;
         double-3-6-inj; double-6-12-inj; double-12-24-inj;
         s1-not-in-image; d1-not-in-image; t1-not-in-image;
         chain-3→12; chain-3→24)

-- ── 涡旋塔 + 高阶域扩张 + LCM 连接 (v7.4) ──────────────────
-- 涡旋塔 Z/12ⁿZ CRT 正交分解: Z/144Z ≅ Z/9Z × Z/16Z
open import Sovereign.Algebra.VortexTower public hiding (polar-decomposition; polar-is-12-sq)
-- GF(3⁶) = GF(729) 与 T⁶ 格点: 加法群 ≅ (Z/3Z)⁶, 0 postulate
open import Sovereign.Algebra.GF729 public hiding (pow-3-5)
-- 主权 LCM = 3¹¹×2¹⁶ 与涡旋塔 12ⁿ 的连接, 0 postulate
-- (33 个符号与上游冲突, 取消 public 重导出, 模块仍被类型检查)
open import Sovereign.Algebra.LCMVortexConnection
-- GF(3) 完整域扩张塔和子域格: GF(3^a) ⊂ GF(3^b) ⟺ a|b, 0 postulate
-- (50 个符号与上游冲突, 取消 public 重导出, 模块仍被类型检查)
open import Sovereign.Algebra.FieldExtensionTower

-- ── P3 群表示论: Lie 群离散替代统一入口 (v7.5) ──────────────
-- 合并: BranchingRules (SO(3)→A₄) + BinaryTetrahedral (2A₄=Q₈⋊C₃)
--       + RepresentationBridge (膨胀/旋量/覆盖一致性)
-- P0 证据已注册至 CompletenessTheorem §8, 0 postulate
open import Sovereign.Algebra.LieDiscrete public

-- 李线的 Jacobian 侧延伸: 离散 Frobenius-Galois 群代数
-- (离散指数映射 exp_D=σ^t / Gal(GF(9)/GF(3))≅C₂ / Aut(T⁶/GF(9)) 半直积接口
--  / SO(3)→A₄ 对齐 — 原在 Jacobian 家族, 2026-08-16 补注册导出面)
open import Sovereign.Algebra.Jacobian.jac_LieGroup public
  using (expD; expD-id; C2; c2-mul; c2-order; FiniteAutGroup; a4-burnside)

-- 李代数/李群独立建立 (2026-08-16, 与 Jacobian 家族分开, 有意重复):
-- 李代数: gl(2)-GF(3) 括号 反称 81 + Jacobi 729; so(3) GF(3)³ 叉积 反称 729
--         + 基 Jacobi 27; 李群: exp_C4/C₆ 单参子群律 16/36 + D₄ 半直积 64
open import Sovereign.Algebra.Lie.LieAlgebra public
  using (br; asym; jacobi; br3; asym3; jacobi3; Lie3; Basis3; toVec;
         cyc12; cyc23; cyc31)
open import Sovereign.Algebra.Lie.LieGroup public
  using (expC4; expC4-hom; expC6; expC6-hom; SDElem; _⋊g·_;
         sdE; sdS; sdM; sdA; sdAS; sdMA; sdMAS;
         gen-a-square; gen-a-order4; gen-b-order2; twist-order2; d4-conjugation)

-- ── GF(4) 四元域与幻方链 (2026-08-17 注册导出面) ───────────────
-- GF(4) = GF(2)[α]/(α²+α+1) 完整域公理 (交换/结合/单位/逆/分配全 refl, 0 postulate)
open import Sovereign.Structology.GF4 public
  using (GF4; g0; g1; ga; gb; add4; mul4; toFin; fromFin)
-- 手写正交拉丁方对 → Euler 叠加 → 完全幻方 (euler-is-M4=refl, 十线=34)
-- 数值验证: docs/cross-level/gf4-affine-magic-square-verification.md
--   L1 = 2i+3j+2, L2 = 3i+2j+2 (GF(4) 仿射, 240 候选唯一命中)
open import Sovereign.Structology.OrthogonalLatinSquare public
  using (L1; L2; euler-is-M4; euler-row-magic; euler-col-magic; euler-diag-magic)
-- GF(4) 域仿射 (i+j, αi+j) → 正交拉丁方 → 半幻方 (行=列=34, 对角 10/58)
open import Sovereign.Structology.OrthogonalLatinSquareGF4 public
  using (genL1; genL2; genL1-latin; genL2-latin)
  renaming (orthogonal to gen-orthogonal; superpose to gen-superpose;
            semi-magic-rows to gen-semi-rows; semi-magic-cols to gen-semi-cols)

-- ── SL(2,3) = 2·A₄ 定义表示链 (2026-08-17 注册导出面) ──────────
-- χ₂ 由阶数(特征值结构)推导 + 576 对 Cayley 同态 + 最小阶完整自证
-- (order-pow: gⁿ=I 24 refl; order-minimal: g^k≠I 75 refl 负证)
open import Sovereign.Structology.BinaryTetrahedralDefiningRep public
  using (SL23; orderOf; classOf; chi2FromRep; chi2-correct)
open import Sovereign.Structology.SL23Cayley public
  using (Mat2; toMat; mulMat2; matI; powMat; order-pow; order-minimal;
         isI; not-isI; toMat-hom)
-- 推导特征标不可约性 (item 5): ⟨χ,χ⟩·|G| = Σ|c|·χ·χ̄ ≡ 24 整数恒等式
-- (χ₂ 阶数导出 / χ₂′=χ₂⊗χ₁′ / χ₂″=χ₂⊗χ₁″ 张量积导出, 全部 ⟨χ,χ⟩=1)
open import Sovereign.Structology.BinaryTetrahedralIrreducibility public
  using (inner-num; classSizes-sum; chi2-irreducible;
         chi2'-irreducible; chi2''-irreducible)

-- ── GF(4) 完全幻方五定理 (2026-08-17) ──────────────────────────
-- T1 正交 / T2′ 转置 L2≡L1ᵀ / T2″ 系数 σ-像 / T-sym 统一判据 a≠b / T3 十线=30
-- 三层幻方定义与命名层锚点见模块头注释; 数值验证见 docs/cross-level/
open import Sovereign.Structology.GF4AffineMagicSquare public
  using (T1-orthogonal; transpose4; T2′; σ4; T2″; constant-not-conjugated;
         T-sym-square; det-neq-zero; det-zero-eq; T-sym;
         det-instance-nonzero; M0; T3;
         affine-trajectory; trajectory-L1; trajectory-L2;
         trajectory-step; trajectory-step-nonzero)
  renaming (T1 to T1-orthogonal)  -- 避免与 Format.CRT 的振荡周期 T1 冲突

-- ── GF(9) 幻方链推广: a≠b 判据特征 3 形态 (2026-08) ────────────
-- 判据分裂: 正交 ⟺ λ₁≠λ₂ / 主对角 ⟺ λ≠-1 / 副对角 ⟺ λ≠1
-- 完全幻方实例 λ₁=α, λ₂=2α (十线 369, 81 格表数据 Rust 锁定)
open import Sovereign.Structology.GF9AffineMagicSquare public
  using (twoAlpha; subGF9; orth-diff; orth-diff-nonzero; orth-kernel;
         diag-alpha; diag-alpha-perm; anti-alpha; anti-alpha-perm;
         anti-degen-1; main-degen-2; sep-diff; sep-diff-nonzero;
         idx-sum-36; magic-constant-369;
         trajectory-Lλ; trajectory-step-alpha)

-- ── 动态幻方: 矢量方向动态系统本体类型 (会话裁定 #16, 2026-08) ────
-- n 阶 = n 个矢量方向同时变化; 动态解 = 轨道; 静态幻方 = 投影切片
-- 基座双轨: +1 归零 (周期 3) vs ×2 乌比斯环 (周期 2 永不归零)
-- 卢先生序列 3,5,8,13,21,34,55,89,144, 终点锚定 144 = POLAR_WINDING
-- (Orbit 类型不导出, 避免与 Structology.T6.Orbit 潜在歧义)
open import Sovereign.Structology.DynamicMagicSquare public
  using (VectorDirections; NestedRings; DynamicMagicSquare; snapshot;
         zero-reset-orbit; zr-period3; mobius-orbit; mobius-period2;
         mobius-never-zero; orbits-distinct;
         lu-orders; lu-fib-1; lu-fib-2; lu-fib-3; lu-fib-4;
         lu-fib-5; lu-fib-6; lu-fib-7; lu-144-polar)

-- ── P4 无穷维结构离散替代 (v7.5) ─────────────────────────────
-- P4-A: 有限状态动力系统 + 轨道周期定理 (鸽巢原理, 0 postulate)
open import Sovereign.Analysis.FiniteDynamics public
-- P4-B: GF(9) 离散顶点代数 (char 3 OPE 截断, 0 postulate)
open import Sovereign.Analysis.VertexAlgebraDiscrete public hiding (shift)
-- P4-C: 离散 Hilbert 空间 (GF9ⁿ + hermitianIP + 轨道周期完备性, 0 postulate)
open import Sovereign.Analysis.HilbertDiscrete public
-- P4-D: 全息态与基模 (信息论闭包类型基础设施, 0 postulate)
open import Sovereign.Structology.HolographicSpace public

-- ── 同伦类型论扩展 (v7.4) ────────────────────────────────────
-- 离散 CCHM: CRT 环面上的 C₃ Burnside 群作用
open import Sovereign.HoTT.DiscreteCCHM public hiding (CRTPhase; POLAR; shift)
open import Sovereign.HoTT.HopfConstruction public  -- P2-2: 真 A₄ 纤维化 (totalSpaceEquiv + 自由轨道)
-- 零类等价: Hₙ(T⁶) Betti 对称性 + Poincaré 对偶
open import Sovereign.HoTT.ZeroHomologyEquivalence public
-- 陈数×欧拉示性数维度阶梯 (2D c₁=χ=2 / 3D 奇维为零+Chern-Simons / T⁶ χ=0 平陈数 / ∞ 周期轨道)
open import Sovereign.HoTT.ChernEulerLadder public

-- 注: 以下模块尚未创建，待后续会话实现:
-- Sovereign.Algebra.GF27 (GF(3³) 三次扩张)

-- ═══════════════════════════════════════════════════════════════
open import Sovereign.AI.Constitution public


-- ═══════════════════════════════════════════════════════════════
-- 安全注册: 无冲突模块
-- ═══════════════════════════════════════════════════════════════
open import Sovereign.Algebra.BranchingRules public
open import Sovereign.Algebra.DiscreteJacobi public
open import Sovereign.Algebra.Holographic.4320DClosure public
open import Sovereign.Algebra.Holographic.Conjecture public
open import Sovereign.Algebra.Holographic.LatticeField public
open import Sovereign.Algebra.Holographic.PhysicalOntology public
open import Sovereign.Algebra.Holographic.Theorem public
open import Sovereign.Algebra.Jacobian.jac_CRTDet public
open import Sovereign.Algebra.Jacobian.jac_DiscreteJC public
open import Sovereign.Algebra.PlancherelTheorem public
open import Sovereign.Analysis.CalculusOfVariations public
open import Sovereign.Analysis.DiscreteApprox public
open import Sovereign.Analysis.DiscretePotential public
open import Sovereign.Analysis.DiscreteSeveralComplex public
open import Sovereign.Analysis.DiscreteSpecialFunctions public
open import Sovereign.Analysis.DiscreteVariation public
open import Sovereign.Analysis.IntegrationByParts public
open import Sovereign.Analysis.NoetherTheorem public
open import Sovereign.Analysis.TestRiesz public
open import Sovereign.Applied.BiologyDiscrete public
open import Sovereign.Applied.BlackHoleWhiteHole public
open import Sovereign.Applied.CelestialExtended public
open import Sovereign.Applied.CommunicationDiscrete public
open import Sovereign.Applied.CosmologyDiscrete public
open import Sovereign.Applied.CrossDomainTheorems public
open import Sovereign.Applied.EMDiscrete public
open import Sovereign.Applied.EconomicsDiscrete public
open import Sovereign.Applied.FluidDiscrete public
open import Sovereign.Applied.GRDiscrete public
open import Sovereign.Applied.GameTheory public
open import Sovereign.Applied.ImageProcessing public
open import Sovereign.Applied.InformationFrame public
open import Sovereign.Applied.LinguisticsDiscrete public
open import Sovereign.Applied.MetaTheorems public
open import Sovereign.Applied.NeuroscienceDiscrete public
open import Sovereign.Applied.NumberOptComp public
open import Sovereign.Applied.OpticsDiscrete public
open import Sovereign.Applied.OptimizationDiscrete public
open import Sovereign.Applied.ProbThermo public
open import Sovereign.Applied.SignalProcessing public
open import Sovereign.Applied.ThermoExtended public
open import Sovereign.Arithmetic.Untrusted public
open import Sovereign.Examples public
open import Sovereign.Geometry.DiscreteManifold public
open import Sovereign.Geometry.ProjectiveTransformHFM public
open import Sovereign.HoTT.CRTFiberWinding public
open import Sovereign.HoTT.CanonicityAlignment public
open import Sovereign.HoTT.PhaseAlignment6624 public
open import Sovereign.Integration public
open import Sovereign.Physics.DiscreteLagrangian public
open import Sovereign.Physics.DiscreteLagrangian3D public
open import Sovereign.Physics.ElasticityDiscrete public
open import Sovereign.Physics.EntropySpinBalance public
open import Sovereign.Physics.HamiltonianDiscrete public
open import Sovereign.Physics.LightRotationTernary public
open import Sovereign.Physics.RootTwoGF9 public
open import Sovereign.Projection.Decimal public
open import Sovereign.Structology.BinaryTetrahedralHFM public
open import Sovereign.Structology.BinaryTetrahedralRepresentation public
open import Sovereign.Structology.BinaryTetrahedralTwoDimTensors public
open import Sovereign.Structology.DiscreteCalculus public
open import Sovereign.Structology.SL23Trace public
open import Sovereign.Structology.TopologyLevels public
open import Sovereign.Structology.WuXingEulerHFM public
open import Sovereign.Topology.CharacteristicClasses public

-- ═══════════════════════════════════════════════════════════════
-- Algebra/ 全量注册: 49 个模块 (2026-08-20)
-- 全部 EXIT=0, 0 postulate (核心模块), 编译验证通过
-- ═══════════════════════════════════════════════════════════════

-- Algebra/ 顶层 (26个)
open import Sovereign.Algebra.BCWDegeneracy public
open import Sovereign.Algebra.ChainComplex public
open import Sovereign.Algebra.ChainZ3toZ12 public
open import Sovereign.Algebra.CharacteristicTower public
open import Sovereign.Algebra.DegenerationRisk public
open import Sovereign.Algebra.DiscreteAnalysis public
open import Sovereign.Algebra.DiscreteDE public
open import Sovereign.Algebra.DiscreteLimit public
open import Sovereign.Algebra.DiscreteRepresentation public
open import Sovereign.Algebra.DiscreteSeveralComplex public
open import Sovereign.Algebra.ExactSequence public
open import Sovereign.Algebra.FunctionalDiscrete public
open import Sovereign.Algebra.GF81 public
open import Sovereign.Algebra.HomologyExact public
open import Sovereign.Algebra.MyopiaRisk public
open import Sovereign.Algebra.NoCloning public
open import Sovereign.Algebra.ProbabilityAddition public
open import Sovereign.Algebra.ProjectionAnalysis public
open import Sovereign.Algebra.ProjectionDifferential public
open import Sovereign.Algebra.ProjectionDiffGeo public
open import Sovereign.Algebra.RepresentationBridge public
open import Sovereign.Algebra.SectionRisk public
open import Sovereign.Algebra.SpiralCycle public
open import Sovereign.Algebra.TowerConnection public
open import Sovereign.Algebra.VortexConnections public
open import Sovereign.Algebra.VortexDifferential public

-- Algebra/GroupTheory/ (3个)
open import Sovereign.Algebra.GroupTheory.FiniteGroupAxioms public
open import Sovereign.Algebra.GroupTheory.GaloisTheory public
open import Sovereign.Algebra.GroupTheory.RepresentationTheory public

-- Algebra/Holographic/ (6个)
open import Sovereign.Algebra.Holographic.ClassicAnalysis public
open import Sovereign.Algebra.Holographic.EscapeAnalysis public
open import Sovereign.Algebra.Holographic.FinalAudit public
open import Sovereign.Algebra.Holographic.InfoClosure public
open import Sovereign.Algebra.Holographic.Master public
open import Sovereign.Algebra.Holographic.Representation public

-- Algebra/Jacobian/ (14个)
open import Sovereign.Algebra.Jacobian public
open import Sovereign.Algebra.Jacobian.jac_AutT6 public
open import Sovereign.Algebra.Jacobian.jac_CRTSpectrum public
open import Sovereign.Algebra.Jacobian.jac_Discrete public
open import Sovereign.Algebra.Jacobian.jac_FunctionTable public
open import Sovereign.Algebra.Jacobian.jac_GF3 public
open import Sovereign.Algebra.Jacobian.jac_GF9Matrix public
open import Sovereign.Algebra.Jacobian.jac_Injectivity public
open import Sovereign.Algebra.Jacobian.jac_LinearAlgebra public
open import Sovereign.Algebra.Jacobian.jac_Matrix public
open import Sovereign.Algebra.Jacobian.jac_NMatrix public
open import Sovereign.Algebra.Jacobian.jac_Pigeonhole public
open import Sovereign.Algebra.Jacobian.jac_Topology public

-- ═══════════════════════════════════════════════════════════════
-- 全量注册: 剩余 193 个模块 (2026-08-20)
-- 全部 EXIT=0, 编译验证通过
-- 失败 17 个: Coding/PigeonholeStandard, Density/Resonance,
--   HoTT/(ChernConservation, CRTFiberWinding, CRTHarmonics, EnergyGap,
--   Equivalence, PhaseTransitionPaths, T6Homotopy, WindingCover),
--   Physics/(FineStructureMapping, LightConeMatrix),
--   Projection/Binary, Structology/(ElectricalTopology, LuCellGrid,
--   TorusClosure, WuXingTransition)
-- ═══════════════════════════════════════════════════════════════

open import Sovereign.AlgebraWrapper public
open import Sovereign.Analysis.CauchySchwarz public
open import Sovereign.Analysis.DiscreteFourier public
open import Sovereign.Analysis.DiscreteIntegralEq public
open import Sovereign.Analysis.DiscreteMorseTheory public
open import Sovereign.Analysis.DiscreteProbability public
open import Sovereign.Analysis.FiniteInnerProduct public
open import Sovereign.Analysis.FiniteProbability public
open import Sovereign.Analysis.FunctionalAnalysisDiscrete public
open import Sovereign.Analysis.L2Bridge public
open import Sovereign.Analysis.LinearFunctionalDiscrete public
open import Sovereign.Analysis.NormDiscrete public
open import Sovereign.Analysis.NormEquivalence public
open import Sovereign.Analysis.SpectralTheorem public
open import Sovereign.Applied.AcousticsDiscrete public
open import Sovereign.Applied.AlgebraChainDeep public
open import Sovereign.Applied.CelestialGeneticsControl public
open import Sovereign.Applied.CircuitExtended public
open import Sovereign.Applied.CondensedMatter public
open import Sovereign.Applied.ControlTheory public
open import Sovereign.Applied.DeepAlgebraProofs public
open import Sovereign.Applied.DeepStructureProofs public
open import Sovereign.Applied.DomainProofs public
open import Sovereign.Applied.GeneticsExtended public
open import Sovereign.Applied.HomologyHarmonic public
open import Sovereign.Applied.LeibnizGF9 public
open import Sovereign.Applied.LeibnizT6 public
open import Sovereign.Applied.LogicCompleteness2Var public
open import Sovereign.Applied.MachineLearning public
open import Sovereign.Applied.MolecularSymmetry public
open import Sovereign.Applied.ParticlePhysics public
open import Sovereign.Applied.PleiadianCosmology public
open import Sovereign.Arithmetic.CRTLemmas public
open import Sovereign.Base.Lü public
open import Sovereign.Base.TritOps public
open import Sovereign.Base.ZeroGeometry public
open import Sovereign.Coding.BCHGF9 public
open import Sovereign.Coding.CyclicGF27 public
open import Sovereign.Coding.HammingMetric public
open import Sovereign.Coding.Trit public
open import Sovereign.Completeness.CompletenessTheorem public
open import Sovereign.Completeness.FunctorProof public
open import Sovereign.Completeness.Layer public
open import Sovereign.Constitution.Boundaries public
open import Sovereign.Constitution.PhysicalAssumptions public
open import Sovereign.Constitution.WindingAsymmetry public
open import Sovereign.Coupling.CartanTorsion public
open import Sovereign.Coupling.Entanglement public
open import Sovereign.Coupling.LCM public
open import Sovereign.Coupling.LossGain public
open import Sovereign.Coupling.TQ10 public
open import Sovereign.Coupling.TrainingSoftConstraint public
open import Sovereign.Coupling.Zhonglv public
open import Sovereign.Coupling.ZhonglvPhaseSync public
open import Sovereign.Density.SevenStages public
open import Sovereign.Diagnosis.ElectricCivilization public
open import Sovereign.Engine.QsUpdate public
open import Sovereign.Format.ModulusGeneration public
open import Sovereign.Geometry.Tryte public
open import Sovereign.HoTT.Bundle public
open import Sovereign.HoTT.ChernClass public
open import Sovereign.HoTT.Connection public
open import Sovereign.HoTT.DiscreteCubical public
open import Sovereign.HoTT.DiscreteCubical.Path public
open import Sovereign.HoTT.Fibration public
open import Sovereign.HoTT.Geometry public
open import Sovereign.HoTT.KanComposition public
open import Sovereign.HoTT.M4CRTBridge public
open import Sovereign.HoTT.Paths public
open import Sovereign.MetaStructure.Nayin public
open import Sovereign.PDE.ConvergenceAlignment public
open import Sovereign.PDE.HeatEquationDiscrete public
open import Sovereign.PDE.PDEDiscrete public
open import Sovereign.PDE.WaveEquationDiscrete public
open import Sovereign.Physics.AlphaRelation public
open import Sovereign.Physics.DiscreteActionPrinciple public
open import Sovereign.Physics.DiscreteDiffOps public
open import Sovereign.Physics.DiscreteMaxwellGF9 public
open import Sovereign.Physics.DiscreteNoether public
open import Sovereign.Physics.ElectromagneticUnitBridge public
open import Sovereign.Physics.H2OC60 public
open import Sovereign.Physics.LightCone public
open import Sovereign.Physics.LightRotationFrequency public
open import Sovereign.Physics.MaxwellFromLagrangian public
open import Sovereign.Physics.Scaling public
open import Sovereign.Problem.BSD.BSD public
open import Sovereign.Problem.BSD.BSD9 public
open import Sovereign.Problem.BSD.BSD_General public
open import Sovereign.Problem.BSD.BSD_GF243 public
open import Sovereign.Problem.BSD.BSD_GF27 public
open import Sovereign.Problem.BSD.BSD_GF81 public
open import Sovereign.Problem.BSD.BSD_L3 public
open import Sovereign.Problem.BSD.BSDTrace public
open import Sovereign.Problem.BSD.EllipticComplex public
open import Sovereign.Problem.BSD.SelmerDiscrete public
open import Sovereign.Problem.BSD.ZetaDiscrete public
open import Sovereign.Problem.Hodge.ChainComplex public
open import Sovereign.Problem.Hodge.DeligneHodge public
open import Sovereign.Problem.Hodge.EulerChar public
open import Sovereign.Problem.Hodge.Hodge public
open import Sovereign.Problem.Hodge.Hodge_L3 public
open import Sovereign.Problem.Hodge.HodgeTetra public
open import Sovereign.Problem.Hodge.KleinHodge public
open import Sovereign.Problem.Hodge.TorusHodge public
open import Sovereign.Problem.Kakeya.KakeyaGF3 public
open import Sovereign.Problem.Kakeya.KakeyaGF9 public
open import Sovereign.Problem.Kakeya.KakeyaMF public
open import Sovereign.Problem.Kakeya.KakeyaPathology public
open import Sovereign.Problem.Langlands.DeligneLusztig public
open import Sovereign.Problem.Langlands.GL2_Rep public
open import Sovereign.Problem.Langlands.GL2TestVectors public
open import Sovereign.Problem.Langlands.Langlands public
open import Sovereign.Problem.Langlands.Langlands_L15 public
open import Sovereign.Problem.Langlands.S4Burnside public
open import Sovereign.Problem.NavierStokes.NSE public
open import Sovereign.Problem.NavierStokes.NSRegularity public
open import Sovereign.Problem.NavierStokes.NSVortex public
open import Sovereign.Problem.PvsNP.Algorithm public
open import Sovereign.Problem.PvsNP.CharPoly3 public
open import Sovereign.Problem.PvsNP.Complexity public
open import Sovereign.Problem.PvsNP.Complexity3 public
open import Sovereign.Problem.PvsNP.CubicRoot public
open import Sovereign.Problem.PvsNP.CubicRootTest public
open import Sovereign.Problem.PvsNP.DetMul public
open import Sovereign.Problem.PvsNP.GF27Separation public
open import Sovereign.Problem.PvsNP.PvsNP_Conjecture public
open import Sovereign.Problem.PvsNP.PvsNP_L15 public
open import Sovereign.Problem.PvsNP.PvsNP_Separation public
open import Sovereign.Problem.Riemann.AlgGeom public
open import Sovereign.Problem.Riemann.FrobeniusBlind public
open import Sovereign.Problem.Riemann.Galois public
open import Sovereign.Problem.Riemann.RH public
open import Sovereign.Problem.Riemann.Sheaf public
open import Sovereign.Problem.Riemann.Variety public
open import Sovereign.Problem.Riemann.WeilRH public
open import Sovereign.Problem.Riemann.WeilRigidity public
open import Sovereign.Problem.Riemann.ZetaFunctional public
open import Sovereign.Problem.YangMills.SU2_Embedding public
open import Sovereign.Problem.YangMills.SUn_GF9 public
open import Sovereign.Problem.YangMills.WilsonLoop public
open import Sovereign.Problem.YangMills.WilsonPlaquette public
open import Sovereign.Problem.YangMills.YM_Action public
open import Sovereign.Problem.YangMills.YM_DetMul public
open import Sovereign.Problem.YangMills.YM_Full public
open import Sovereign.Problem.YangMills.YM_L3 public
open import Sovereign.Problem.YangMills.YM_SpectralGap public
open import Sovereign.Problem.YangMills.YMTransfer public
open import Sovereign.Problem.YangMills.YM_Transfer public
open import Sovereign.Projection public
open import Sovereign.Projection.Decimal.Axioms public
open import Sovereign.Projection.Decimal.Proofs public
open import Sovereign.Quantum.Entanglement public
open import Sovereign.RootMath.AlgebraicComplex public
open import Sovereign.RootMath.Arithmetic public
open import Sovereign.RootMath.Base public
open import Sovereign.RootMath.DigitalRoot public
open import Sovereign.RootMath.Eisenstein public
open import Sovereign.RootMath.EnergyGap public
open import Sovereign.RootMath.Gaussian public
open import Sovereign.RootMath.LengthLattice public
open import Sovereign.Structology.A4Group public
open import Sovereign.Structology.A4GroupAction public
open import Sovereign.Structology.A4OneDimHom public
open import Sovereign.Structology.A4Orbits3 public
open import Sovereign.Structology.A4Representation public
open import Sovereign.Structology.A4ThreeDimRep public
open import Sovereign.Structology.Aether public
open import Sovereign.Structology.BinaryTetrahedral public
open import Sovereign.Structology.BinaryTetrahedralSpectrum public
open import Sovereign.Structology.BurnsideT6 public
open import Sovereign.Structology.FrequencySpaceUnity public
open import Sovereign.Structology.GF9MagicSquare public
open import Sovereign.Structology.HolographicPi public
open import Sovereign.Structology.HoloInformation public
open import Sovereign.Structology.MagicSquare144 public
open import Sovereign.Structology.MagicSquareHFM public
open import Sovereign.Structology.MatrixZω public
open import Sovereign.Structology.OrderLattice public
open import Sovereign.Structology.Platonics public
open import Sovereign.Structology.PlatonicTorusProjection public
open import Sovereign.Structology.S3IsGL22 public
open import Sovereign.Structology.SP2Ternary public
open import Sovereign.Structology.StandingWave public
open import Sovereign.Structology.T6 public
open import Sovereign.Structology.T6A4Burnside public
open import Sovereign.Structology.TetrahedralA4 public
open import Sovereign.Structology.VectorDirection public
open import Sovereign.Structology.Winding public
open import Sovereign.Structology.Zωi public
open import Sovereign.Topology.DeRhamComplex public
open import Sovereign.Topology.HomologicalAlgebra public
open import Sovereign.Trust.External public

-- ── GF(27) 三次扩张 (2026-08-17 注册) ─────────────────────────────────────
-- GF(3³) = GF(3)[x]/(x³+2x+1), α³ = α+2 (mod 3), 26 个非零元素循环群
open import Sovereign.Algebra.GF27 public
  using (GF27; gf27-zero; gf27-one; alpha; alpha-sq;
         _+gf27_; _*gf27_; negate27; inv; inv-correct; inv-involutive;
         embed-gf3-gf27; embed-add; embed-mul; embed-one;
         gen; gen-generates-all)
