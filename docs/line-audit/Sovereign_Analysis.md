# 目录 `src/Sovereign/Analysis/` 逐模块审计记录

共 34 个模块。


## `src/Sovereign/Analysis/ApproxBounds.agda`

- **module**: `Sovereign.Analysis.ApproxBounds`
- **行数**: 37（代码 13 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.ApproxBounds
  - 41 逼近论补强 — Q16 常数的误差界 (0 postulate)
  - 律算 Q16 投影层的逼近质量 (人类可读投影, 不进入状态演化):
  - 仲吕 log10 增益 3.4541 ≈ ZHONGLV_LOG10_MULT_Q16/2^16 = 226372/65536
  - √3 ≈ DELTA_Q16/2^16 = 113506/65536
  - 误差界以 ℕ 差 + 饱和减法 (=0 ⟺ ≤) 的 refl 呈现
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (5)**: `zhonglv-q16`, `zhonglv-err`, `zhonglv-err-bound`, `delta-sq-err`, `delta-sq-bound`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Analysis/CalculusOfVariations.agda`

- **module**: `Sovereign.Analysis.CalculusOfVariations`
- **行数**: 122（代码 27 / 注释 69）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.CalculusOfVariations
  - 变分原理统一结构 (L3 深层证明)
  - 核心命题:
  - 将离散变分原理、Euler-Lagrange 方程、作用量统一为一个自洽的框架。
  - 证明策略:
  - §1 作用量定义 (离散拉格朗日密度)
  - §2 变分导数 (δS/δφ = Δ²φ)
  - §3 Euler-Lagrange 方程 (δS/δφ=0 ⟺ Δ²φ=0)
  - §4 变分原理应用 (Gauss 定律推导)
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteDiffOps`, `Sovereign.Physics.DiscreteLagrangian`
- **顶层签名 (2)**: `el-equivalence`, `el-constant`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Analysis/CauchySchwarz.agda`

- **module**: `Sovereign.Analysis.CauchySchwarz`
- **行数**: 420（代码 245 / 注释 141）
- **OPTIONS**: `--rewriting`
- **导入 (10)**: `Data.Nat`, `Data.Vec`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Relation.Nullary`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.FunctionalDiscrete`
- **data 类型**: `_`
- **顶层签名 (21)**: `≤T-refl`, `≤T-max`, `≤T-trans`, `norm-sq`, `norm-sq-T₀`, `norm-sq-T₁`, `norm-sq-T₂`, `norm-sq-≤₁`, `norm-sq-eq-T₀`, `norm-sq-is-abs`, `cauchy-schwarz-1`, `cauchy-schwarz-1-equality`, `no-isotropic-2`, `ip-zeroˡ`, `ip-zeroʳ`, `cauchy-schwarz-2`, `+v-zero-zero`, `triangle-inequality`, `cs-counterexample-lhs`, `cs-counterexample-rhs`, `cs-fails-at-3`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/Analysis/DifferenceEq.agda`

- **module**: `Sovereign.Analysis.DifferenceEq`
- **行数**: 33（代码 16 / 注释 8）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.DifferenceEq
  - 34/39 ODE/差分补强 — Fibonacci 递推 mod 3 的周期 8 轨道 (0 postulate)
  - y(n+2) = y(n+1) + y(n) (mod 3): 0,1,1,2,0,2,2,1,0,1,... — 周期 8
- **导入 (3)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (9)**: `step`, `fib-1`, `fib-2`, `fib-3`, `fib-4`, `fib-5`, `fib-6`, `fib-7`, `fib-period-8`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteApprox.agda`

- **module**: `Sovereign.Analysis.DiscreteApprox`
- **行数**: 46（代码 21 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteApprox — 离散逼近论 (MSC 41)
  - GF(3) 上的 L¹/L∞ 最佳逼近.
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (6)**: `l1-dist`, `approx-err`, `l∞-dist`, `cheb-err`, `sq-err`, `id-err`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteCR.agda`

- **module**: `Sovereign.Analysis.DiscreteCR`
- **行数**: 63（代码 37 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.DiscreteCR
  - 30/32 复分析补强 — GF(3) 离散拉普拉斯与调和性 (0 postulate)
  - 连续: f 全纯 ⟹ u = Re f, v = Im f 调和 (Δu = Δv = 0)
  - 离散 GF(3): f = z² (GF(9) 乘法) 的分量满足离散拉普拉斯方程
  - Δu(x,y) = u(x⊕1,y) ⊕ u(x⊖1,y) ⊕ u(x,y⊕1) ⊕ u(x,y⊖1) ⊕ u(x,y) = 0
  - (2 阶差分, 系数 1 求和 — GF(3) 中 1+1+1+1+... 精确)
  - 非调和见证: N(z) = z·σ(z) = x²+y² 不调和 (1 项反证)
- **导入 (3)**: `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`
- **顶层签名 (7)**: `u`, `v`, `Δ`, `harmonic-u`, `harmonic-v`, `n`, `not-harmonic-n`
- **质量**: `refl`×19；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteFourier.agda`

- **module**: `Sovereign.Analysis.DiscreteFourier`
- **行数**: 53（代码 26 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteFourier — 离散 Fourier 变换 (MSC 44)
  - T⁶ 上的有限 Fourier 变换: GF(3)ⁿ → GF(3)ⁿ 酉矩阵.
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Topology`
- **顶层签名 (7)**: `dft-apply`, `const-vec`, `dft-const`, `e0`, `dft-e0-0`, `dft-e0-1`, `dft-e0-2`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteIntegralEq.agda`

- **module**: `Sovereign.Analysis.DiscreteIntegralEq`
- **行数**: 50（代码 17 / 注释 20）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteIntegralEq — 离散积分方程 (MSC 45)
  - GF(3) 上的有限和方程: u = λKu + f, K 是 GF(3) 矩阵.
  - Fredholm 积分方程的离散对应.
  - 0 postulate.
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (5)**: `neg`, `solve-diag`, `v-solve`, `det-IλK₁`, `det-IλK₂`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteMorseTheory.agda`

- **module**: `Sovereign.Analysis.DiscreteMorseTheory`
- **行数**: 43（代码 17 / 注释 15）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteMorseTheory — 离散流形上的分析 (MSC 58)
  - T⁶ 上的离散 Morse 理论: 临界点 + Morse 不等式.
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (5)**: `f`, `grad01`, `grad21`, `morse0`, `morse1`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscretePotential.agda`

- **module**: `Sovereign.Analysis.DiscretePotential`
- **行数**: 37（代码 15 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscretePotential — 离散位势论 (MSC 31)
  - GF(3) 格点上的 Laplace 方程 Δu = f.
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (5)**: `laplace3`, `laplace-const`, `laplace-linear`, `laplace-quadratic`, `harmonic-const`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteProbability.agda`

- **module**: `Sovereign.Analysis.DiscreteProbability`
- **行数**: 56（代码 23 / 注释 19）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteProbability — 离散概率论 (MSC 62)
  - GF(3) 上的有限概率空间: 6 个事件的离散分布.
  - 0 postulate.
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (9)**: `uniform`, `uniform-norm`, `twoPoint`, `twoPoint-norm`, `expectation`, `id-expect-uniform`, `marginal`, `indep-prod`, `marginal-indep`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteSeveralComplex.agda`

- **module**: `Sovereign.Analysis.DiscreteSeveralComplex`
- **行数**: 33（代码 11 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteSeveralComplex — 离散多复变 (MSC 32)
  - ℂⁿ 被诊断 TypeError: 全纯域不可有限编码
  - 离散替代: GF(3)ⁿ 函数空间 + 有限复形 Cauchy-Riemann
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (2)**: `not-hol-xy`, `hol-const`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteSpecialFunctions.agda`

- **module**: `Sovereign.Analysis.DiscreteSpecialFunctions`
- **行数**: 34（代码 12 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteSpecialFunctions — 离散特殊函数 (MSC 33)
  - 连续统 TypeError: SpecialFunctionsViaContinuation
  - 离散替代: GF(3) 指数和、Gauss 和、二次特征
  - 0 postulate.
- **导入 (2)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (3)**: `χ-sum-zero`, `legendre-1`, `legendre-2`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteVariation.agda`

- **module**: `Sovereign.Analysis.DiscreteVariation`
- **行数**: 53（代码 18 / 注释 21）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteVariation — 离散变分法 (MSC 49)
  - 有限集上的极值问题: 离散 Euler-Lagrange 方程.
  - 替代连续泛函的 Gateaux 导数和 δ-变分.
  - 0 postulate.
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (6)**: `action2`, `freeL`, `δ-action`, `δ-free`, `stationary-const`, `nonstationary`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Analysis/DiscreteVariational.agda`

- **module**: `Sovereign.Analysis.DiscreteVariational`
- **行数**: 34（代码 13 / 注释 11）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.DiscreteVariational
  - 49 变分法补强 — 离散能量极小与调和中点 (0 postulate)
  - 端点固定的三点路径 (y₀=0, y₂=2), 中间值 y₁ ∈ {0,1,2}:
  - 能量 E(y) = y² + (2−y)² (ℤ 算术)
  - E(0) = 4, E(1) = 2, E(2) = 4 — 极小化元 y = 1 = 调和中点 (0+2)/2
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (8)**: `E`, `energy-0`, `energy-1`, `energy-2`, `minimal-0`, `minimal-2`, `harmonic-mid`, `euler-lagrange-discrete`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Analysis/FiniteDynamics.agda`

- **module**: `Sovereign.Analysis.FiniteDynamics`
- **行数**: 265（代码 169 / 注释 66）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.FiniteDynamics
  - 有限动力系统：轨道、周期性、鸽巢原理、GF(9) Frobenius 动力学
- **导入 (9)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **record 类型**: `EventuallyPeriodic`
- **顶层签名 (20)**: `orbit`, `orbit-step`, `orbit-cong`, `pigeonhole-fin`, `pigeonhole-collision`, `orbit-collision-propagates`, `arith-rearrange`, `orbit-eventually-periodic`, `orbit-period-bound`, `frobenius-orbit`, `frobenius-orbit-period`, `frobenius-eventually-periodic`, `frobenius-fixed-point`, `frobenius-fixed-iff`, `frobenius-nontrivial-orbit`, `gf9-to-fin9`, `fin9-to-gf9`, `gf9-fin9-roundtrip`, `gf9-orbit-period-bound`, `frobenius-period-tight`
- **质量**: `refl`×16；无 postulate / 无 hole

## `src/Sovereign/Analysis/FiniteInnerProduct.agda`

- **module**: `Sovereign.Analysis.FiniteInnerProduct`
- **行数**: 435（代码 236 / 注释 137）
- **OPTIONS**: `--rewriting`
- **导入 (10)**: `Data.Nat`, `Data.Empty`, `Data.Fin`, `Relation.Nullary`, `Data.Fin`, `Data.Product`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (33)**: `VectorSpace`, `gf9-zero`, `zeroVec`, `*gf9-zeroˡ`, `*gf9-zeroʳ`, `+gf9-swap-middle`, `negate-⊕-self`, `negate-⊗-negate-self`, `sumGF9`, `sumGF9-cong`, `sumGF9-const-zero`, `sumGF9-additive`, `sumGF9-scalar`, `conj-additive`, `conj-zero`, `conj-sum`, `hermitianIP`, `hermitian-conj-sym`, `hermitian-linearˡ`, `normSq`, `gf9-norm-real`, `galoisNorm-zero`, `normSq-of-zero`, `normSq-1-positive`, `Orthogonal`, `orth-sym`, `zero-orthogonalˡ`, `zero-orthogonalʳ`, `basisVec`, `basisVec-diag`, `basisVec-suc-at-zero`, `normSq-basisVec`, `basis-orthogonal`
- **质量**: `refl`×19；无 postulate / 无 hole

## `src/Sovereign/Analysis/FiniteProbability.agda`

- **module**: `Sovereign.Analysis.FiniteProbability`
- **行数**: 425（代码 332 / 注释 60）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.FiniteProbability
  - 有限概率空间: GF(3)ⁿ 均匀分布 + ℚ 有理期望 + Burnside 1/12 + Markov 平稳分布 (P1-3, wiki 60A)
  - 数学背景 (wiki 28-probability):
  - 概率 = 有限格点均匀计数比: P(A) = |A|/3ⁿ ∈ ℚ (无极限, 无连续分布)。
  - 期望 = (1/3ⁿ) Σ_{x∈GF3ⁿ} X(x) (有限和, 无 Lebesgue 积分)。
  - Burnside: A₄ 正则作用 (12 点自由传递) — 随机 (g,x) 不动概率 = 12/144 = 1/12;
  - 自然作用 (4 顶点) — 不动概率 = 12/48 = 1/4 (Σ_g|Fix g| = #轨道·|G| = 12)。
  - Markov: GF(3) 完全均匀链 (每步等概率跳 3 态) — 均匀分布 (1/3,1/3,1/3) 平稳。
  - 宪法原则:
  - 1. 全离散有理: 概率 = (分子, 分母) 整数对, 相等 = 交叉相乘 (无浮点)。
  - 2. GF(3)ⁿ 上的求和 = 前缀树递归 (3 叉), |GF3ⁿ| = 3ⁿ 由 ℕ 归纳。
  - 3. A₄ 作用表由 perm 置换表示生成 (144 项群表 + 不动点计数), 0 postulate。
  - 包含:
  - §1 有理概率 Rat + 相等/算术
  - §2 GF(3)ⁿ 均匀分布 + |GF3ⁿ| = 3ⁿ + 有理期望
  - §3 Burnside: A₄ 自然作用 (1/4) 与正则作用 (1/12)
  - §4 Markov: GF(3) 均匀链平稳分布 + 双重随机一般引理
- **导入 (7)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.A4Group`
- **顶层签名 (23)**: `Rat`, `_≐_`, `scalar`, `rat3`, `sumGF3`, `GF3ⁿ-size`, `uniform`, `uniform-norm`, `expectation`, `expect-const`, `expect-uniform`, `probability`, `fix4`, `fixR`, `mulA4`, `burnside-natural`, `prob-natural`, `burnside-regular`, `prob-regular`, `fixR-faithful`, `T`, `stationary`, `doubly-stochastic`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Analysis/FunctionalAnalysisDiscrete.agda`

- **module**: `Sovereign.Analysis.FunctionalAnalysisDiscrete`
- **行数**: 223（代码 101 / 注释 96）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Sovereign.Algebra.FunctionalDiscrete`, `Data.Nat`, `Data.Vec`, `Data.Product`, `Data.Unit`, `Data.Sum`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Completeness.Layer`
- **record 类型**: `FunctionalAnalysisDiscreteFramework`, `FACompletenessBridge`
- **顶层签名 (9)**: `fa-framework-2`, `fa-framework`, `FADiscreteCarrier`, `fa-witness`, `fa-completeness-bridge`, `riesz-2`, `nondeg-2`, `norm-2-two-valued`, `hb-collapse-2`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Analysis/GoodnessOfFitGF3.agda`

- **module**: `Sovereign.Analysis.GoodnessOfFitGF3`
- **行数**: 88（代码 31 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.GoodnessOfFitGF3
  - 62-20 拟合优度检验 — 幻方识别的 χ² 零检验 (0 postulate)
  - 骨架中的 ℚ 除法与序改用 ℕ 分子形式 (更诚实, 无实数分析):
  - χ² = Σ (Oᵢ−Eᵢ)²/Eᵢ, Eᵢ = 15 恒定 — 零检验 ⟺ 分子 Σ (Oᵢ−15)² = 0
  - 本模块只写可证的实例部分 (按"先算后写"纪律):
  - §1 Lo Shu 3×3 幻方: 8 线 (3 行+3 列+2 对角) 全 ≡ 15
  - §2 幻方零检验: chi2-num ≡ 0 (refl)
  - §3 非幻方正检验: 单线偏离 14 → chi2-num ≡ 1 ≢ 0
  - §4 小规模精确分布与 4×4/12×12 对接: 注释级 (数据提取留待, 不占位)
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`
- **顶层签名 (15)**: `loshu-row-1`, `loshu-row-2`, `loshu-row-3`, `loshu-col-1`, `loshu-col-2`, `loshu-col-3`, `loshu-diag-1`, `loshu-diag-2`, `dev`, `chi2-num`, `magic-square-chi2-zero`, `loshu-chi2-zero`, `nonmagic-chi2-positive-num`, `nonmagic-detected`, `nonmagic-two-lines`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Analysis/HilbertDiscrete.agda`

- **module**: `Sovereign.Analysis.HilbertDiscrete`
- **行数**: 151（代码 57 / 注释 60）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.HilbertDiscrete
  - 离散 Hilbert 空间: GF(9)ⁿ + Hermitian 内积 + 有限维完备性
  - 核心结构:
  - DiscreteHilbert n = VectorSpace n (GF9ⁿ 函数表示)
  - 内积: hermitianIP (共轭对称, 正定)
  - 范数: normSq = Σᵢ f(i)·σ(f(i))
  - 完备性: 有限集合上轨道最终周期 (来自 FiniteDynamics)
  - 顶点代数嵌入: Y(a)|0⟩ = a (创生公理)
  - 0 postulate — 全部构造性证明
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.FiniteInnerProduct`, `Sovereign.Analysis.FiniteDynamics`, `Sovereign.Analysis.VertexAlgebraDiscrete`
- **顶层签名 (14)**: `DiscreteHilbert`, `positive-definite`, `zero-norm`, `zero-orth`, `conj-symmetric`, `hilbert-complete-fin`, `frobenius-hilbert-cycle`, `embed-vertex`, `embed-vacuum-zero`, `basis`, `basis-self`, `hilbert-discrete-summary`, `basis-orth-2`, `embed-1`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Analysis/IntegrationByParts.agda`

- **module**: `Sovereign.Analysis.IntegrationByParts`
- **行数**: 99（代码 23 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.IntegrationByParts
  - 分部积分统一结构 (L3 深层证明)
  - 核心命题:
  - 将离散分部积分、Green 恒等式、散度定理统一为一个自洽的框架。
  - 证明策略:
  - §1 分部积分 (1D 离散版)
  - §2 分部积分推论 (差分求和为零)
  - §3 Green 恒等式 (离散版)
  - §4 散度定理 (离散版)
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteDiffOps`
- **顶层签名 (2)**: `integration-by-parts-theorem`, `diff-sum-zero`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Analysis/L2Bridge.agda`

- **module**: `Sovereign.Analysis.L2Bridge`
- **行数**: 442（代码 192 / 注释 198）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Nat`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.FunctionalDiscrete`
- **data 类型**: `NormClass`
- **record 类型**: `ContInnerProductSpace`, `L2Bridge`
- **顶层签名 (25)**: `n-mod3`, `gf3-inv`, `norm-factor`, `gf3-inv-T₁`, `gf3-inv-T₂`, `norm-factor-0`, `norm-factor-1`, `norm-factor-2`, `norm-factor-3`, `norm-factor-period3`, `normalized-inner`, `normalized-inner-sym`, `normalized-inner-linearˡ`, `l2-norm-sq`, `l2-norm-sq-zero`, `norm-class`, `norm-class-period3`, `t6-norm-class`, `n1-l2-identity`, `n3-l2-degenerate`, `t6-l2-degenerate`, `t6-l2-norm-degenerate`, `discrete-as-cont`, `identity-bridge`, `identity-bridge-sym`
- **质量**: `refl`×12；无 postulate / 无 hole

## `src/Sovereign/Analysis/LinearFunctionalDiscrete.agda`

- **module**: `Sovereign.Analysis.LinearFunctionalDiscrete`
- **行数**: 423（代码 269 / 注释 100）
- **OPTIONS**: `--rewriting`
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Function`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.FunctionalDiscrete`
- **record 类型**: `LinearFunctional`
- **顶层签名 (33)**: `gf9-zero`, `VectorSpace`, `basis9`, `*gf9-zeroˡ`, `*gf9-zeroʳ`, `scalar9-zero`, `+v9-identityˡ`, `+v9-identityʳ`, `+gf9-shuffle`, `inner9`, `inner9-zeroˡ`, `inner9-additiveˡ`, `inner9-homogeneousˡ`, `linear-combined`, `linear-preserves-zero9`, `zeroFunctional`, `functional-add`, `functional-scale`, `represent`, `tailFunctional`, `rieszVector`, `vec9-decompose`, `rieszCorrect`, `riesz-exists9`, `DualSpace`, `riesz-map`, `riesz-inverse`, `inner9-basis₀`, `inner9-zero-head`, `lemma-riesz-ext`, `riesz-represent-inv`, `represent-riesz-correct`, `dual-space-iso`
- **质量**: `refl`×31；无 postulate / 无 hole

## `src/Sovereign/Analysis/NoetherTheorem.agda`

- **module**: `Sovereign.Analysis.NoetherTheorem`
- **行数**: 105（代码 24 / 注释 59）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.NoetherTheorem
  - Noether 定理统一结构 (L3 深层证明)
  - 核心命题:
  - 将离散 Noether 定理、规范对称性、电荷守恒统一为一个自洽的框架。
  - 证明策略:
  - §1 规范对称性 (⟨α⟩ 规范群)
  - §2 Noether 恒等式 (变分导数与守恒流)
  - §3 电荷守恒 (div J + Δt ρ = 0)
  - §4 守恒律总结
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteActionPrinciple`, `Sovereign.Physics.DiscreteNoether`, `Sovereign.Physics.DiscreteMaxwellTime`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Analysis/NormDiscrete.agda`

- **module**: `Sovereign.Analysis.NormDiscrete`
- **行数**: 463（代码 320 / 注释 99）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Data.Nat`, `Data.Vec`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.LinearFunctionalDiscrete`
- **data 类型**: `_`
- **record 类型**: `NormEquiv`
- **顶层签名 (27)**: `normReal`, `maxT`, `normSup`, `≤t-refl`, `≤t-trans`, `≤t-antisym`, `≤t-total`, `maxT-ubˡ`, `maxT-ubʳ`, `galoisNorm-of-zero`, `maxT-zero`, `normSup-of-zero`, `normReal-of-zero`, `isotropic-example9`, `isotropic-nonzero9`, `galoisNorm-multiplicative`, `normReal-homogeneous`, `scalar9-zeroˡ-vec`, `normSup-zero-scalar`, `normSup-one-scalar`, `normEquiv-refl`, `normEquiv-sym`, `normEquiv-trans`, `normSup-determines-zero`, `normReal-zero-includes-zero`, `galoisNorm-values`, `normSup-values`
- **质量**: `refl`×120；无 postulate / 无 hole

## `src/Sovereign/Analysis/NormEquivalence.agda`

- **module**: `Sovereign.Analysis.NormEquivalence`
- **行数**: 462（代码 246 / 注释 167）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Data.Nat`, `Data.Vec`, `Data.Product`, `Data.Empty`, `Data.Sum`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.FunctionalDiscrete`
- **data 类型**: `_`
- **顶层签名 (28)**: `≤₃-refl`, `≤₃-trans`, `≤₃-antisym`, `≤₃-total`, `NormEquivalent`, `T₁≢T₀`, `T₂≢T₀`, `abs-gf3-multiplicative`, `abs-gf3-two-valued`, `sq-eq-abs`, `sq-negate`, `scalar-T₀-zero`, `Q-negate-invariant`, `Q-homogeneous`, `max-abs-scale`, `discrete-norm-homogeneous`, `OnUnitSphere`, `Q-definite-1`, `Q-on-sphere-1`, `Q-definite-2`, `Q-on-sphere-2`, `norm-equiv-1`, `norm-equiv-2`, `Q-not-norm-3`, `norm-equiv-fails-3`, `all-norms-topologically-equivalent`, `sup-Q-topo-equiv-1`, `sup-Q-topo-equiv-2`
- **质量**: `refl`×53；无 postulate / 无 hole

## `src/Sovereign/Analysis/RandomMatrixMoments.agda`

- **module**: `Sovereign.Analysis.RandomMatrixMoments`
- **行数**: 159（代码 96 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.RandomMatrixMoments
  - 62 统计学 (62-05/06/07 诚实版) — 对称矩阵系综的精确迹矩 (0 postulate)
  - 对"离散 Catalan 定理"的**计算验证后判定** (验证脚本: 全枚举):
  - ✓ 奇矩精确为零 (平衡二值系综 {±1} 中心化)
  - ✓ μ₂ 精确 = C₁·σ² = 1 (N=2,3)
  - ✗ μ₂ₖ = Cₖ 精确 (N ≥ 2k) — **不成立**: 有限 N 交叉配对修正不消失:
  - N=2: μ₄ = 3/2 = C₂ − 1/2;  N=3: μ₄ = 5/3 = C₂ − 1/3
  - 成立的是"极限 Catalan + 1/N 修正" — 本模块如实形式化修正结构,
  - 不以断言代替计算 (宪法: 先算后写)。
- **导入 (3)**: `Data.Nat`, `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (47)**: `_⊞_`, `_⊠_`, `tr1`, `tr2`, `tr3`, `tr4`, `row-mmm-1`, `row-mmm-2`, `row-mmm-3`, `row-mmm-4`, `row-mmp-1`, `row-mmp-2`, `row-mmp-3`, `row-mmp-4`, `row-mpm-1`, `row-mpm-2`, `row-mpm-3`, `row-mpm-4`, `row-mpp-1`, `row-mpp-2`, `row-mpp-3`, `row-mpp-4`, `row-pmm-1`, `row-pmm-2`, `row-pmm-3`, `row-pmm-4`, `row-pmp-1`, `row-pmp-2`, `row-pmp-3`, `row-pmp-4`, `row-ppm-1`, `row-ppm-2`, `row-ppm-3`, `row-ppm-4`, `row-ppp-1`, `row-ppp-2`, `row-ppp-3`, `row-ppp-4`, `sum-tr1`, `sum-tr3`, `sum-tr2`, `moment-2-exact-catalan`, `sum-tr4`, `moment-4-correction`, `moment-2-n3-exact`, `sum-tr4-n3`, `moment-4-n3-correction`
- **质量**: `refl`×42；无 postulate / 无 hole

## `src/Sovereign/Analysis/SpecialValues.agda`

- **module**: `Sovereign.Analysis.SpecialValues`
- **行数**: 71（代码 53 / 注释 8）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.SpecialValues
  - 33 特殊函数补强 — 阶乘/二项系数/Pascal 恒等式 (0 postulate)
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (47)**: `fact-0`, `fact-1`, `fact-2`, `fact-3`, `fact-4`, `fact-5`, `fact-6`, `fact-recurrence-6`, `C0-0`, `C1-0`, `C1-1`, `C2-0`, `C2-1`, `C2-2`, `C3-0`, `C3-1`, `C3-2`, `C3-3`, `C4-0`, `C4-1`, `C4-2`, `C4-3`, `C4-4`, `C5-0`, `C5-1`, `C5-2`, `C5-3`, `C5-4`, `C5-5`, `C6-0`, `C6-1`, `C6-2`, `C6-3`, `C6-4`, `C6-5`, `C6-6`, `pascal-3-1`, `pascal-3-2`, `pascal-4-1`, `pascal-4-2`, `pascal-5-1`, `pascal-5-2`, `pascal-5-3`, `pascal-6-1`, `pascal-6-2`, `pascal-6-3`, `row-sum-4`
- **质量**: `refl`×20；无 postulate / 无 hole

## `src/Sovereign/Analysis/SpectralTheorem.agda`

- **module**: `Sovereign.Analysis.SpectralTheorem`
- **行数**: 388（代码 219 / 注释 122）
- **OPTIONS**: `--rewriting`
- **导入 (7)**: `Data.Nat`, `Data.Vec`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.FunctionalDiscrete`
- **record 类型**: `SpectralDecomp2`
- **顶层签名 (27)**: `is-self-adjoint`, `IsEigenpair`, `inner-scalarˡ`, `inner-scalarʳ`, `eigenvector-orthogonal`, `linear-op-zero-1`, `spectral-1-go`, `spectral-1`, `inner-2`, `proj-op`, `proj-self-adjoint`, `proj-eigen-1`, `proj-eigen-0`, `proj-orth`, `proj-orth-thm`, `ones-op`, `ones-self-adjoint`, `ones-eigen-2`, `ones-eigen-0`, `ones-orth`, `ones-orth-thm`, `proj-spectral`, `ones-spectral`, `id-self-adjoint`, `zero-self-adjoint`, `id-eigen`, `zero-eigen`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Analysis/SymmetricGroupCharStats.agda`

- **module**: `Sovereign.Analysis.SymmetricGroupCharStats`
- **行数**: 117（代码 62 / 注释 32）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.SymmetricGroupCharStats
  - 62-10 群表示统计 — A₄ 的 Plancherel 分布与特征标期望 (0 postulate)
  - Plancherel 分布: P(λ) = (dim λ)²/|G| — 整数权重 w(λ) = dim λ²
  - 中心特征标期望 = 列正交关系 (第一正交关系):
  - E_planch[χ_λ(g)/dim λ] = Σ_λ dim λ·χ_λ(g)/|G| = δ(g=e)
  - (整数形式: Σ dim·χ(g) = |G| 于 e, = 0 于其余类)
  - 行正交 (第二正交关系实例): Σ_C |C|·χ(C)·conj(χ(C)) = |G| (每不可约)
  - 载体 = A₄ (类 1/4/4/3, 特征标值 ∈ Z[ω] — 1+ω+ω²=0 承载列正交)
- **导入 (7)**: `Data.Product`, `Data.Integer`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`, `Sovereign.Structology.A4Representations`, `Sovereign.RootMath.Eisenstein`
- **顶层签名 (9)**: `_⊞_`, `_⊠_`, `plancherel-normalized`, `col-C1`, `col-C2`, `col-C3`, `col-C4`, `row-V1`, `row-V3`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Analysis/TestRiesz.agda`

- **module**: `Sovereign.Analysis.TestRiesz`
- **行数**: 181（代码 69 / 注释 78）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.FunctionalDiscrete`
- **顶层签名 (22)**: `coord0`, `coord1`, `sum-func`, `coord0-linear`, `coord1-linear`, `sum-func-linear`, `test-riesz-coord0`, `test-riesz-sum`, `test-riesz-coord1`, `test-coord0-repr`, `test-sum-repr`, `test-coord1-repr`, `test-inner-e0-e0`, `test-inner-e1-e1`, `test-inner-e0-e1`, `test-inner-sum-sum`, `test-inner-orth`, `riesz-unique-2`, `coord0-exists`, `sum-exists`, `coord0-witness-is-e0`, `sum-witness-is-ones`
- **质量**: `refl`×16；无 postulate / 无 hole

## `src/Sovereign/Analysis/UniformProb.agda`

- **module**: `Sovereign.Analysis.UniformProb`
- **行数**: 38（代码 12 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.UniformProb
  - 60 概率论补强 — GF(3)² 均匀概率空间 (0 postulate)
  - Ω = Trit × Trit (9 点, 均匀测度): P(A) = |A|/9 — 计数承载的
  - 公理与独立性以 ℕ 计数 + 交叉相乘 refl 呈现 (无分数浮点)
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (7)**: `omega-size`, `event-a-size`, `event-b-size`, `total-prob`, `additivity`, `independence`, `uniformity`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Analysis/VertexAlgebraDiscrete.agda`

- **module**: `Sovereign.Analysis.VertexAlgebraDiscrete`
- **行数**: 370（代码 174 / 注释 125）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Analysis.VertexAlgebraDiscrete
  - GF(9) 离散顶点代数: char 3 截断使 OPE 模式有限化
  - 核心洞察: 在特征 3 域上, n! ≡ 0 (n ≥ 3),
  - 顶点算子的 OPE 自然截断为有限模式 (mode 0, 1, 2)。
  - GF(9)ⁿ 上的逐点乘法构成交换代数, 给出有限维顶点代数。
  - 0 postulate — 全部构造性证明
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Fin`, `Data.Product`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.FiniteInnerProduct`
- **data 类型**: `OPEMode`
- **顶层签名 (48)**: `*V-comm`, `*V-assoc`, `unitVec`, `*V-identityˡ`, `*V-identityʳ`, `*V-zeroˡ`, `*V-zeroʳ`, `VertexOp`, `Y`, `Y-pointwise`, `vacuum`, `vacuum-creation`, `vacuum-zero-op`, `Y-unit-id`, `Y-unit-idʳ`, `Y-assoc`, `locality`, `Y-fusion`, `vacuum-expectation`, `vacuum-orth-all`, `shift`, `shift₁-id`, `shift₂-swap-zero`, `shift₂-swap-suc`, `shift₂-involutive`, `trans-cov₁`, `trans-cov₂`, `fact-gf3`, `fact-0`, `fact-1`, `fact-2`, `fact-3`, `char3-fact-zero`, `ope-mode-count`, `mode-0-nonzero`, `mode-1-nonzero`, `mode-2-nonzero`, `mode-3-zero`, `Y₁-param`, `Y₁-param-pointwise`, `embedVec`, `embed-Op`, `σ-vec`, `frobenius-embed-commute`, `frobenius-id-commute`, `σ-vec-involutive`, `Y-additive`, `Y-additiveʳ`
- **质量**: `refl`×20；无 postulate / 无 hole
