# 目录 `src/Sovereign/Physics/` 逐模块审计记录

共 63 个模块。


## `src/Sovereign/Physics/AlphaRelation.agda`

- **module**: `Sovereign.Physics.AlphaRelation`
- **行数**: 57（代码 13 / 注释 32）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.AlphaRelation
  - 候选常数关系: α_wuxing ≡ 2³ · α_em  (偏差 0.135%, 待独立验证)
  - ⚠️ 本模块**不构成 0-postulate 核心定理**:
  - α_wuxing = 0.0583 是经验拟合值 (H₂O@C₆₀ 0.5 meV + 液态甲烷非谐性 +
  - JUNO 1.5σ), 比值 ≈ 8 = 2³ 是数值观察 (0.135% 偏差), 尚无 GF(3)/GF(9)
  - 底层推导。按项目纪律, 拟合关系不能写成 refl 定理, 只作「条件推演」
  - 的预留接口 — 所有假设显式化, 不污染核心库。
  - 若未来能从环向缠绕 46 / CRT 分解 / Christoffel 螺旋严格推出因子 2³,
  - 则把下面的假设 rel 升级为定理, 移入核心库。
  - 诚实边界 (完整见 docs/cross-level/quantitative-mapping-shnoll-th229.md):
  - 1) α_wuxing = 2³α_em 是候选对接 (0.135% 偏差), 非严格证明;
  - 2) 「17 巧合」(κ=17/20, 1/α_wuxing≈17.15) 偏差 0.9%, 仅开放观察;
  - 3) Th-229 8.36 eV ≈ 8 偏差 4.4%, 不作核心;
  - 4) 全部属框架解读层, 不进入证明链。
- **导入 (2)**: `Data.Rational`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (1)**: `two-cubed`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/AtomicStandingWave.agda`

- **module**: `Sovereign.Physics.AtomicStandingWave`
- **行数**: 216（代码 47 / 注释 124）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.AtomicStandingWave
  - 原子驻波与量子场势垒 — T⁶ 环面上的波动模式
  - 核心洞察:
  - 原子驻波 = T⁶ 环面上 GF(9) 矢量场的闭合相位轨道
  - 量子场势垒 = GF(9) 范数边界 (N=1 → N=2)
  - 穿越势垒 = 范数投影的相变 (温度驱动)
  - 六重态 = T⁶ 六维对称性的驻波模式副本
  - 因果链:
  - GF(9) 共轭 → 驻波条件 → 范数边界 → 相变 → 宏观物性
  - 与标准量子力学的区别:
  - 标准: 原子"隧穿"通过势垒 (连续)
  - 我们: GF(9) 矢量场从 N=1 模式投影到 N=2 模式 (离散)
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (12)**: `alpha-order`, `wave-closure`, `phi-order`, `half-step-closure`, `full-step-closure`, `norm-zero`, `norm-one-alpha`, `norm-one-neg-alpha`, `norm-two`, `propagating-states`, `confined-states`, `state-ratio`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Physics/ChiralInterference.agda`

- **module**: `Sovereign.Physics.ChiralInterference`
- **行数**: 170（代码 72 / 注释 62）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.ChiralInterference
  - 手征干涉层: C3 旋转 → 场论驻波的缺失中间层 (0 postulate, 无洞)
  - 元理论对析评审指定三大缺口之首。焊接内容:
  - §1 干涉规则: T₁⊕T₂=T₀ (相消, 左右旋抵至寂止), T₁⊕T₁=T₂ / T₂⊕T₂=T₁
  - (相长, 同旋叠加为反旋) — 全部由 Base/Trit 的 ⊕ 表 refl 闭合。
  - §2 逐点场: 任意 SpinField 干涉的交换性 (符号, ⊕-comm)。
  - §3 反向传播波: waveCW (相位 = k) 与 waveCCW (相位 = −k) 逐点干涉
  - 相消为寂止场 (符号, ⊕-inverse); 同向双波相长为反向波
  - (符号, double-neg + negate²)。
  - §4 驻波: Standing = kShift 不变; 相消干涉场处处 T₀ → 恒为驻波
  - (符号, wave-cancel 两实例 trans)。
  - §5 Frobenius 稳定性: GF(3) 上 x³=x (Fermat, 3 情形 refl) →
  - 驻波在 Frobenius 时间演化下稳定 (符号)。
  - 诚实边界:
  - 1) 非平凡 Frobenius 是 GF(9) 上的 σ(a+bα)=a−bα (阶 2,
  - Algebra/GaloisBridge.agda 已证); GF(3) 上 Frobenius 平凡,
  - 故 §5 的 3 态稳定性是重言式 — 该节的意义是把"稳定性"接口
  - 焊接到已证的 C₂ 事实, 不是新物理。
- **导入 (4)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`
- **顶层签名 (24)**: `interfere`, `cw-ccw-cancel`, `ccw-cw-cancel`, `cw-cw-construct`, `ccw-ccw-construct`, `rest-neutral`, `double-neg`, `SpinField`, `interfere-fields`, `interfere-comm`, `cw-ccw-field-cancel`, `waveCW`, `waveCCW`, `wave-cancel`, `wave-cw-construct`, `wave-ccw-construct`, `kShift`, `Standing`, `rest-standing`, `const-standing`, `wave-cancel-forms-standing`, `cube`, `frob3-identity`, `frob-stability`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Physics/ClimateDynamics.agda`

- **module**: `Sovereign.Physics.ClimateDynamics`
- **行数**: 111（代码 31 / 注释 55）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.ClimateDynamics
  - 气候动力学 — T⁶ 环面上的矢量场
  - 核心映射:
  - 气候状态 = T⁶ 环面上的 GF(9) 矢量场
  - 大气环流 = 熵旋矢量场的旋度部分 (无损耗)
  - 能量守恒 = ∂z(κH²·1) = 0
  - 气候相变 = 范数边界穿越
  - 诚实边界:
  - 气候系统的 T⁶ 环面模型是简化框架
  - 实际气候系统的复杂非线性效应未完全形式化
  - 守恒条件的精确验证需实验数据
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (7)**: `ClimateState`, `climate-equilibrium`, `equilibrium-is-zero`, `zero-satisfies-conservation`, `el-nino-norm`, `la-nina-norm`, `ice-age-norm`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Physics/DNAEncoding.agda`

- **module**: `Sovereign.Physics.DNAEncoding`
- **行数**: 104（代码 37 / 注释 44）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DNAEncoding
  - DNA 碱基配对 — GF(3) 有限域编码
  - 核心映射:
  - 碱基 → GF(3) 元素 (三态: 0, 1, 2)
  - 配对规则 = GF(3) 加法逆元
  - 双螺旋 = GF(9) 共轭对
  - 诚实边界:
  - 碱基到 GF(3) 的映射是候选编码, 非生物学推导
  - 表观遗传修饰的 GF(9) 二次扩张模型是简化假设
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **data 类型**: `Base`
- **顶层签名 (8)**: `base-to-gf3`, `ac-same`, `tg-same`, `pair-at`, `pair-cg`, `non-pair-aa`, `complementary-strand`, `complementary-norm`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Physics/DataAnchors.agda`

- **module**: `Sovereign.Physics.DataAnchors`
- **行数**: 155（代码 51 / 注释 73）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DataAnchors
  - 数据实证：理论模型与物理实验数据的锚定
  - 目标：
  - 证明律算系统的核心不变量（缠绕数 46, 能隙 √3）与真实世界观测数据（C60, H2O@C60）同构。
  - 这是律算合一从“数学真理”走向“物理现实”的关键一步。
- **导入 (9)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Integer`, `Data.Rational`, `Relation.Binary.PropositionalEquality`, `Data.Rational.Base`, `Sovereign.HoTT.Geometry`, `Sovereign.Physics.Scaling`, `Sovereign.Base.Invariants`
- **顶层签名 (17)**: `H2O_C60_SPLITTING`, `C60_FUNDAMENTAL_MODES`, `THEORETICAL_GAP_ENERGY`, `THEORETICAL_TOROIDAL_WINDING`, `Anchor_ToroidalWinding_C60`, `TRAPPIST_RATIO`, `THEORETICAL_WUXING_RATIO`, `Anchor_WuXing_TrapPist1`, `KATRIN_MNU_UPPER`, `ACT_DELTA_NEFF_UPPER`, `MICROBOONE_CL`, `KATRIN_NEUTRINO4_CL`, `ELECTRON_MASS_EV`, `Anchor_KATRIN_SubEV`, `Anchor_KATRIN_BelowElectron`, `Anchor_ACT_BelowOneSpecies`, `Anchor_KATRIN_StrongerThanMicroBooNE`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteActionPrinciple.agda`

- **module**: `Sovereign.Physics.DiscreteActionPrinciple`
- **行数**: 280（代码 149 / 注释 96）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteActionPrinciple
  - 离散作用量原理 — 离散规范群 + 场强定义 (0 postulate)
  - 本模块包含:
  - §1 离散规范群 ⟨α⟩ — 群公理全部 refl 验证 (浅层证明, 真)
  - §2 离散场强定义 — F_{ij} = Δ_i A_j - Δ_j A_i (定义, 与 curl 对接)
  - §3 离散拉格朗日密度 — L = N(E) - N(B) (定义, 用真实范数)
  - HONEST: 诚实边界:
  - §1 是深层证明 (穷举 refl, 真正验证了群公理, 包括结合律 40 case)
  - §2 是深层证明 (curl-is-field-strength refl 验证 curl ≡ F_{ij})
  - §3 是定义 (拉格朗日密度的 GF(3) 实现)
  - 变分导出 Maxwell: DiscreteLagrangian + DiscreteLagrangian3D (已证)
  - Noether 定理: DiscreteNoether (已证, §8 深层证明)
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`, `Sovereign.Physics.DiscreteDiffOps`
- **data 类型**: `GaugeGroup`
- **顶层签名 (17)**: `embedG`, `g-identityˡ`, `g-identityʳ`, `g-inv`, `g-inverseˡ`, `g-inverseʳ`, `embedG-hom`, `g-order-4`, `g-norm-is-1`, `g-assoc`, `Fyz`, `Fzx`, `Fxy`, `curl-is-field-strength`, `GF9ScalarField`, `GF9VectorField`, `dx9`
- **质量**: `refl`×92；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteDiffOps.agda`

- **module**: `Sovereign.Physics.DiscreteDiffOps`
- **行数**: 240（代码 122 / 注释 81）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteDiffOps
  - 离散差分算子 — 前向/后向差分 + 分部求和 (0 postulate)
  - §1 后向差分 ∇_μ (prev = next∘next)
  - §2 分部求和 (1D 三点, 穷举 refl)
  - §3 差分交换 (引用 DiscreteEMField3D)
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`
- **顶层签名 (19)**: `prev`, `prev-cubed`, `backwardDx`, `backwardDy`, `backwardDz`, `Δ1d`, `∇1d`, `mul3`, `sum3`, `sum-forward`, `sum-backward`, `mul3-comm`, `add3-cyclic`, `integration-by-parts-1d`, `diff-sum`, `integration-by-parts-zero`, `add-neg-zero`, `add3-swap-first`, `add3-swap-last`
- **质量**: `refl`×23；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteEMCore.agda`

- **module**: `Sovereign.Physics.DiscreteEMCore`
- **行数**: 327（代码 222 / 注释 75）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteEMCore
  - 78 电磁学 — 离散 Maxwell 核心定理层 (0 postulate, 无洞)
  - 定位: 建立在 DiscreteEMField (3×3 环面, 第一基石) 与 DiscreteEMField3D
  - ((Fin 3)³ 环面, 第二基石) 之上的"核心定理层"。GF(3) 域律、三对混合
  - 偏导交换性、差分可加性/负号引理均已在两基石中穷举/符号证明, 本模块
  - 直接复用 (open import), 不重复展开。
  - 本模块新增三个可证核心:
  - §1 div (curl A) ≡ 0 —— 旋度的散度为零 (全形式!)
  - 补完 DiscreteEMField3D §6 的诚实边界: 此前只证到"成对形式"
  - div-curl-zero-paired; 展开链 (dx/dy/dz-add + dx/dy/dz-neg) 与
  - 六项重排未收尾。本模块给出完整展开 + six-rotate 重排, 全程符号证明。
  - §2 curl (A + grad φ) ≡ curl A —— 3D 规范不变性
  - 旋度线性 curl-linear (三分量, shuffle22 重排) + curl-grad-zero
  - + 零元引理; 2D 版本在 DiscreteEMField, 3D 版本在此 (允许重复)。
  - §3 零场零通量 —— Chern 链接的可证部分
  - 通量 = 环绕平面 k = 0 的 9 个面上 B 的 z 分量有限求和 (具体表,
  - 非 postulate); 磁单极非平凡构型 (通量 = 陈数 ±2) 需要非平凡
  - U(1) 主丛, 对接 DiscreteKTheory — 诚实边界以注释给出, 不写虚假证明。
- **导入 (4)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Physics.DiscreteEMField3D`
- **顶层签名 (18)**: `addVec3`, `addVec3-right-unit`, `shuffle22`, `pair-swap`, `six-rotate`, `dx-dy-comm`, `dy-dz-comm`, `dx-dz-comm`, `div-curl-zero`, `curl-linear-x`, `curl-linear-y`, `curl-linear-z`, `curl-linear`, `gauge-invariance`, `sum9`, `flux`, `zero-flux`, `zero-monopole-flux`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteEMField.agda`

- **module**: `Sovereign.Physics.DiscreteEMField`
- **行数**: 339（代码 265 / 注释 39）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteEMField
  - 78 电磁学 — 3×3 周期环面上的离散场论第一基石 (0 postulate)
  - 对骨架的核心修正: "curl(grad φ) 对任意 φ 自动归约"不成立 —
  - add3/neg3 的表定义只在构造子上触发, 变量参数不归约; 9 格点模式
  - 只固定 p, φ 仍自由。正确路线 = 符号证明:
  - §1 GF(3) 域引理 (add3/neg3 全律穷举)
  - §2 差分算子 dx/dy (前向差分, 环面 next)
  - §3 混合偏导交换 dy∘dx ≡ dx∘dy (符号 ≡-链)
  - §4 grad/curl 与主定理 grad-curl-zero (梯度的旋度恒零)
  - §5 规范不变性: curl(A + grad φ) ≡ curl A (curl 线性 + 主定理)
- **导入 (3)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (25)**: `GF3`, `Point2D`, `add3`, `neg3`, `add3-comm`, `add3-assoc`, `add3-identity`, `add3-inverse`, `neg3-involutive`, `neg3-add`, `next`, `ScalarField`, `dx`, `dy`, `inner`, `dy-dx-comm`, `VectorField`, `grad`, `curl`, `grad-curl-zero`, `_⊕a_`, `dx-add`, `dy-add`, `curl-linear`, `gauge-invariance`
- **质量**: `refl`×48；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteEMField3D.agda`

- **module**: `Sovereign.Physics.DiscreteEMField3D`
- **行数**: 513（代码 416 / 注释 41）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteEMField3D
  - 78 电磁学 — 3D 环面 (Fin 3)³ 的离散场论第二基石 (0 postulate)
  - 对 3D 骨架的两处修正 (与 2D 同款, 已落 2D 模块注释):
  - 1) "展开后自动归约 refl"不成立 — add3/neg3 表定义只在构造子触发,
  - 变量参数不归约; 恒等式必须符号证明 (混合偏导交换 + 域引理)。
  - 2) div (A_x , A_y , A_z) 类型错误 — VectorField 是函数 (Point3D →
  - 三元组), 模式不能匹配三元组; 用分量投影 proj₁/proj₂。
  - 核心恒等式 (符号证明):
  - curl (grad φ) ≡ 0 (梯度的旋度为零 — 三对混合偏导交换)
  - div (curl A) ≡ 0 (旋度的散度为零 — 六项两两抵消 + 可加性/负号引理)
- **导入 (3)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (38)**: `GF3`, `Point3D`, `add3`, `neg3`, `add3-comm`, `add3-assoc`, `add3-identity`, `add3-inverse`, `neg3-involutive`, `neg3-add`, `next`, `ScalarField`, `dx`, `dy`, `dz`, `inner`, `dy-dx-comm`, `dz-dx-comm`, `dz-dy-comm`, `VectorField`, `grad`, `div`, `curl`, `curl-grad-zero-x`, `curl-grad-zero-y`, `curl-grad-zero-z`, `curl-grad-zero`, `dx-neg`, `dy-neg`, `dz-neg`, `dx-add`, `dy-add`, `dz-add`, `pair-cancel-1`, `pair-cancel-2`, `pair-cancel-3`, `div-curl-zero-paired`, `shuffle23`
- **质量**: `refl`×55；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteLagrangian.agda`

- **module**: `Sovereign.Physics.DiscreteLagrangian`
- **行数**: 162（代码 86 / 注释 48）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteLagrangian
  - 离散拉格朗日密度 — 真实 GF(3) 计算 + 变分推导 (0 postulate)
  - 深度证明 (全部 27 case 穷举 refl):
  - §1 δS-equals-Δ²: 变分导数 = 拉普拉斯 (27 case refl)
  - §2 Euler-Lagrange 等价: δS/δφ=0 ↔ Δ²φ=0
  - §3 验证: 常数场和线性场满足 EL
  - §4 连接 Maxwell: E=-∇φ → div E = -Δ²φ = 0 → Gauss 定律
  - 全部 0 postulate。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteDiffOps`
- **顶层签名 (16)**: `next1`, `prev1`, `Δf`, `Δb`, `δS`, `Δ²`, `satisfies-EL`, `is-critical`, `δS-equals-Δ²`, `variational-equals-laplacian`, `critical-to-el`, `el-to-critical`, `φ-const`, `el-const`, `φ-lin`, `el-lin`
- **质量**: `refl`×37；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteLagrangian3D.agda`

- **module**: `Sovereign.Physics.DiscreteLagrangian3D`
- **行数**: 343（代码 99 / 注释 180）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteLagrangian3D
  - 3D 离散拉格朗日密度 + 变分导出 Maxwell (0 postulate)
  - 从 DiscreteLagrangian (1D 三点) 推广到 3D 27 点:
  - §1 3D 拉普拉斯 = dx² + dy² + dz²
  - §2 3D 变分导数 = 拉普拉斯 (27 case 穷举 refl)
  - §3 电场变分: δS/δφ=0 → Δ²φ=0 → div E=0 (Gauss 定律)
  - §4 磁场变分: δS/δA=0 → curl(curl A)=0 → 安培定律
  - §5 无源 Maxwell: 从作用量 S = Σ(|E|²-|B|²) 导出全部四律
  - 全部 0 postulate, GF(3) 穷举 refl。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteLagrangian`
- **顶层签名 (17)**: `dxx`, `δSx-equals-Δ²x`, `δSx`, `Δ²x`, `δSx-equals-Δ²x-3D`, `δSy`, `Δ²y`, `δSy-equals-Δ²y`, `δSz`, `Δ²z`, `δSz-equals-Δ²z`, `neg2-is-1`, `three-x-zero`, `cancel-middle`, `two-is-neg1`, `example-magnetic`, `example-magnetic2`
- **质量**: `refl`×16；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteLightcone.agda`

- **module**: `Sovereign.Physics.DiscreteLightcone`
- **行数**: 40（代码 18 / 注释 10）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteLightcone
  - 83 相对论补强 — GF(3)² 闵氏形式与光锥分类 (0 postulate)
  - q(x,y) = x² − y² (GF(3)): 类光 q=0 (x=±y), 类时 q=1, 类空 q=2
  - 9 格点分类: 5 类光 + 2 类时 + 2 类空 — 离散光锥的完整结构
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (11)**: `q`, `light-00`, `light-11`, `light-22`, `light-12`, `light-21`, `time-10`, `time-20`, `space-01`, `space-02`, `cone-partition`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteMaxwellConservation.agda`

- **module**: `Sovereign.Physics.DiscreteMaxwellConservation`
- **行数**: 126（代码 63 / 注释 47）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteMaxwellConservation
  - 78 电磁学 — 离散 Maxwell 守恒层: Yee 蛙跳 + 高斯保持 (0 postulate, 无洞)
  - 先符号设计, 再落链。闭环的最后一环:
  - 静态恒等式 (DiscreteEMCore: div∘curl=0, 规范不变性)
  - → 动态演化 (DiscreteMaxwellTime: 四律谓词 + charge-conservation)
  - → 守恒律 (本模块: Yee 显式更新 + 归纳证明高斯律保持)
  - §1 div-time-comm: div ∘ Δt ≡ Δt ∘ div (散度与时间差分交换)
  - 直接由 div-linear + div-neg 落链, 呼应"安培两边取散度"的符号推演。
  - §2 Yee 蛙跳显式更新 yee-B / yee-E (构造性动力学, 时间递归定义):
  - B(t+1) = B(t) − curl E(t)
  - E(t+1) = E(t) + curl B(t) − J(t)
  - 步进式定义使 FaradayStep / AmpereStep 定义等价成立 (refl)。
  - §3 gauss-preservation: 安培步进 + 连续性 + 初始高斯 ⇒ ∀t 高斯保持
  - 对 t 做自然数结构归纳 (Agda 结构递归, 非 postulate), 归纳步
  - 用 divE-step (其内核是 div∘curl=0 消去项) + 连续性 + GF(3) 代数。
  - 诚实边界: 时间域取 ℕ (守恒定理的归纳需要自然数结构); Fin n 有限时间
  - 窗口可通过对 T ≤ n 的截取获得, 本模块不做 (与用户约定一致, 不写虚假)。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`, `Sovereign.Physics.DiscreteMaxwellTime`
- **顶层签名 (7)**: `div-time-comm`, `yee-B`, `yee-E`, `yee-faraday-step`, `yee-ampere-step`, `gauss-preservation`, `yee-gauss-preservation`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteMaxwellGF9.agda`

- **module**: `Sovereign.Physics.DiscreteMaxwellGF9`
- **行数**: 1116（代码 878 / 注释 114）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteMaxwellGF9
  - 78 电磁学 — GF(9) 共轭电磁学时间演化层 (0 postulate, 无洞)
  - 电场 E 与磁场 B 是一个 GF(9) 场 F = E + Bα 的实部与虚部。
  - GF(9) = GF(3)[x]/(x²+1), α² = -1。Frobenius 共轭 σ(a+bα) = a-bα
  - 在代数上实现「90° 相位差」——垂直性是 σ 的结构产物, 非外加几何条件。
  - 复用资产: Sovereign.Base.Trit (Trit/⊕/negate/c3-ccw),
  - Sovereign.Algebra.GF9 (GF9=Trit×Trit/_+gf9_/galoisConjugate)。
  - 核心 (0-postulate, 全部 refl/符号):
  - σ-time-comm      σ 与时间差分交换 (90° 相位差演化不变)
  - curl9 (共轭旋度)  实部=∇×B, 虚部=-∇×E
  - reVec-curl9 / imVec-curl9  投影定理 (定义直接给出 refl)
  - ampere-from-unified   实部投影 ⇒ 安培定律
  - faraday-from-unified  虚部投影 ⇒ 法拉第定律
  - 诚实边界: 与 DiscreteEMField3D 的 Fin 3 静态内核是两套格点表示
  - (Trit vs Fin 3), 本模块独立基于 Trit, 是离散第一性本体的相位升维层。
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Geometry.ProjectiveCore`
- **顶层签名 (105)**: `re`, `im`, `neg9`, `σ-neg`, `Time`, `Point`, `nextT`, `GF9Scal`, `GF9Vec`, `GF9ScalTime`, `GF9VecTime`, `addVec9`, `negVec9`, `Δt9`, `ΔtV9`, `σ-time-comm`, `TritScal`, `TritVec`, `dxT`, `dyT`, `dzT`, `vxT`, `vyT`, `vzT`, `addVecT`, `negVecT`, `curlT`, `reVec`, `imVec`, `realVec`, `imagVec`, `curl9`, `reVec-curl9`, `imVec-curl9`, `TritVecTime`, `ΔtVT`, `reVec-addVec9`, `reVec-negVec9`, `imVec-addVec9`, `imVec-negVec9`, `reVec-ΔtV9`, `imVec-ΔtV9`, `UnifiedMaxwellHolds`, `ampere-from-unified`, `faraday-from-unified`, `dx9`, `dy9`, `dz9`, `σ-dx-comm`, `σ-dy-comm`, `σ-dz-comm`, `vx9`, `vy9`, `vz9`, `σVec`, `σVecField`, `curl9std`, `curl-sigma-comm`, `div9`, `σ-div-comm`
  - … 其余 45 项
- **质量**: `refl`×70；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteMaxwellTime.agda`

- **module**: `Sovereign.Physics.DiscreteMaxwellTime`
- **行数**: 315（代码 218 / 注释 60）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteMaxwellTime
  - 78 电磁学 — 离散 Maxwell 时间演化层 (0 postulate, 无洞)
  - 先符号设计, 再落链。离散全息框架中时间是格点步进 t : ℕ, 时间差分
  - Δt F(t,p) = F(t+1,p) − F(t,p)   (GF(3) 上用 add3/neg3)
  - 四律的离散形式:
  - 法拉第  Δt B = −curl E
  - 安培    Δt E = curl B − J
  - 高斯    div E = ρ
  - 连续性  Δt ρ = −div J      (安培 + 高斯 的相容性推论)
  - 元定理 (符号证明, 对任意场成立, 无点态枚举):
  - divE-step   安培步进 ⇒ div E(t+1) = div E(t) − div J(t)   (div∘curl=0)
  - charge-conservation  安培步进 + 高斯 ⇒ Δt ρ = −div J
  - faraday-preserves-divB  法拉第步进 ⇒ div B 随时间守恒 (磁高斯自洽)
  - faraday/amp-diff-from-step  构造动力学 ⇒ 差分形式定律逐点成立
  - 修正上一稿三处类型缺陷:
  - 1) proj₃ 不存在 — 分量用 proj₁ / proj₁∘proj₂ / proj₂∘proj₂ 投影;
  - 2) "div (addVec3 (E t) ...) p" 类型错误 — div 吃场(函数), 不吃三元组;
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`
- **顶层签名 (25)**: `negVec3`, `zeroVec`, `addVec3-assoc`, `addVec3-comm`, `addVec3-neg-cancel`, `addVec3-left-identity`, `cancel-right`, `div-rearrange`, `div-linear`, `div-neg`, `Time`, `VecFieldTime`, `ScalFieldTime`, `ΔtV`, `ΔtS`, `FaradayHolds`, `AmpereHolds`, `GaussHolds`, `FaradayStep`, `AmpereStep`, `faraday-diff-from-step`, `amp-diff-from-step`, `divE-step`, `faraday-preserves-divB`, `charge-conservation`
- **质量**: `refl`×12；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteNoether.agda`

- **module**: `Sovereign.Physics.DiscreteNoether`
- **行数**: 437（代码 150 / 注释 220）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteNoether
  - 离散 Noether 定理 — 从规范对称性导出电荷守恒 (0 postulate)
  - 核心证明链:
  - §1 规范变换: A → A + ∇χ, φ → φ - Δtχ
  - §2 拉格朗日密度在规范变换下不变 (引用已证 gauge-invariance)
  - §3 源项耦合: L_source = A·J - φρ
  - §4 Noether 恒等式: δS/δχ = 0 → ∂ρ/∂t + ∇·J = 0
  - §5 与已有 charge-conservation 的对接
  - 全部 0 postulate。
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`, `Sovereign.Physics.DiscreteMaxwellTime`, `Sovereign.Physics.DiscreteLagrangian`
- **顶层签名 (9)**: `gauge-transform-A`, `gauge-transform-φ`, `diff-comm`, `neg-add-identity`, `add-neg-zero`, `neg-add-distrib`, `noether-1d-point0`, `noether-1d-point1`, `noether-1d-point2`
- **质量**: `refl`×106；无 postulate / 无 hole

## `src/Sovereign/Physics/DiscreteStatMech.agda`

- **module**: `Sovereign.Physics.DiscreteStatMech`
- **行数**: 407（代码 239 / 注释 91）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.DiscreteStatMech — 离散统计力学 (MSC 82)
  - 补强版 (2026-08), 七层, 0 postulate:
  - §1 计数型熵 S = W: n 位 GF(3) 寄存器的微态数 W(n) = 3ⁿ, 熵取微态数本身
  - (无对数计数型, GF(3) 上最自然的熵), 含乘法律 W(n+m) = W(n)·W(m).
  - §2 配分函数族 z2 → z3 → z4 (Trit 模 3 闭链, 全部 refl).
  - §3 Boltzmann 归一化 (模 3 周期闭合) + 特征 3 湮灭一般化 trit-triple-zero.
  - §4 ℚ 熵:
  - 诚实口径: ℚ 上无一般对数, 全定义域香农熵不可在 ℚ 内表达 —
  - (a) 以二阶 Tsallis(碰撞)熵 tsallis2/tsallis3 为 ℚ 代理,
  - 均匀分布熵最大定理对代理严格成立 (Fin 2 / Fin 3, 完整 ≤ 证明);
  - (b) 香农熵本体给出二进实例 (log₂ 仅在 {1, 1/2} 上定义):
  - H(1/2,1/2) = 1 最大, H(1,0) = 0.
  - §5 配分函数 = 状态和 (H≡0 桥接): Z = W, 复合系统乘法性, GF(3) 迹为零.
  - §6 内能: 二能级/三能级均匀系能量期望 (ℚ 精确, 均分形式 2U₂=1, 3U₃=2).
  - §7 T⁶ 微正则桥接: W 6 = 729 = T⁶ 格点数 (对齐 Structology.T6 t6≃fin729).
  - 方法: 多项式恒等式 (tsallis*-gap) 由 stdlib 验证过的环求解器
  - Data.Rational.Solver 落链 — 求解器产出真实证明项, 非 postulate;
  - 序关系部分手证 (平方非负 + 单调性), 无 with, 无 funext.
- **导入 (10)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Integer`, `Data.Sum`, `Relation.Binary.PropositionalEquality`, `Data.Rational`, `Data.Rational.Base`, `Data.Rational.Properties`, `Data.Rational.Solver`, `Sovereign.Base.Trit`
- **顶层签名 (61)**: `2ℚ`, `3ℚ`, `half`, `third`, `W`, `countEntropy`, `W-ok0`, `W-ok1`, `W-ok2`, `W-ok3`, `W-ok4`, `W-ok5`, `W-suc`, `W-add`, `countEntropy-mult`, `z2`, `z2-ok`, `z3`, `z3-ok`, `z4`, `z4-ok`, `z2-double`, `z2-triple`, `norm-z2`, `norm-z3`, `trit-triple-zero`, `0≤1`, `0≤2`, `negneg`, `neg-square`, `square-nonneg`, `sq-nonneg3`, `tsallis2`, `tsallis2-uniform`, `tsallis2-gap`, `tsallis2-gap-nonneg`, `tsallis2-max`, `collision-min2`, `tsallis3`, `tsallis3-uniform`, `tsallis3-gap`, `tsallis3-max`, `collision-min3`, `log2dy`, `shannon2`, `shannon2-uniform`, `shannon2-degenerate`, `dyadic-max2`, `Z`, `Z-is-W`, `Z-suc`, `Z-mult`, `U2`, `U3-level`, `U2-half`, `two-U2≡1`, `U3-two-thirds`, `three-U3≡2`, `W6-729`, `S-T6`
  - … 其余 1 项
- **质量**: `refl`×38；无 postulate / 无 hole

## `src/Sovereign/Physics/ElasticityDiscrete.agda`

- **module**: `Sovereign.Physics.ElasticityDiscrete`
- **行数**: 10（代码 6 / 注释 1）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - MSC 73 · GF(3)格点弹性
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (1)**: `zero-displacement`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Physics/ElectromagneticUnitBridge.agda`

- **module**: `Sovereign.Physics.ElectromagneticUnitBridge`
- **行数**: 439（代码 118 / 注释 249）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.ElectromagneticUnitBridge
  - 电磁学标定层 — 频率单标定 + 范数坍缩投影 (0 postulate)
  - 核心思想: 光是频率, 不是速度。空间是频率的逆平方投影, 时间是频率倒数。
  - 标定层只保留一个基本量: Frobenius 主频 ν。空间尺度由频率经范数坍缩
  - 的逆平方投影给出。所有电磁学结构定理已 0-postulate 闭合; 单位桥只做
  - 线性标定映射, 不改变任何已证关系。
  - 两个关键代数事实 (已证):
  - N(α) = 1          — 范数坍缩, α 的范数是 1 (不是 α²=2)
  - α² = 2            — 180° 翻转像, 不是范数
  - N(a+bα) = a²+b²  — 9 个 GF(9) 元素坍缩到 3 个 GF(3) 值
  - §1 EMUnitScale record (频率单标定: 2 个参数)
  - §2 频率→空间/时间投影 (Δx=C/ν², τ=1/ν, c_res=C/ν)
  - §3 GF9 范数坍缩 (N(α)=1, N(σ(α))=1, 值域 {0,1,2})
  - §4 离散场量→ℚ 映射
  - §5 结构定理保标定
  - §6 Maxwell 方程标定保持
  - HONEST: §7 命名层锚点 (注释级)
- **导入 (14)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Data.Rational`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`, `Sovereign.Physics.DiscreteMaxwellTime`, `Sovereign.Physics.DiscreteMaxwellGF9`, `Sovereign.Physics.DiscreteMaxwellConservation`, `Sovereign.Physics.DiscreteEMField3D`
- **record 类型**: `EMUnitScale`
- **顶层签名 (13)**: `norm-alpha`, `norm-sigma-alpha`, `alpha-square-is-2`, `norm-not-square`, `sigma-involutive`, `norm-surjective-0`, `norm-surjective-1`, `norm-surjective-2`, `norm-zero-is-zero`, `norm-zero-only-for-zero`, `norm-one-not-zero`, `norm-alpha-squared`, `norm-alpha-fourth`
- **质量**: `refl`×12；无 postulate / 无 hole

## `src/Sovereign/Physics/EntropySpin.agda`

- **module**: `Sovereign.Physics.EntropySpin`
- **行数**: 184（代码 50 / 注释 109）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.EntropySpin
  - 物理学：熵旋理论质量涌现机制与 4320D 流形映射
  - (2026-08 修复版: 原版有解析错误且未入库 — 见 §2b 修复注记)
  - 常数归属 (2026-08 三轮核查): 0.0268 的项目内归属 = 斯坦科夫驻波理论的
  - "斯坦科夫比例" (Stankov Ratio)。一手出处 = 项目内部文档
  - /data/trit/pyBitNet/docs/huntian/ (本地仓库, 未公开推送):
  - huntian_quantum_chemistry.py:  STANKOV = 0.0268  # 斯坦科夫比例
  - quantum_state_baoyuan.h:      H2O_C60_REDSHIFT = 0.0268f (斯坦科夫比例相关偏移)
  - 05-quantum-physics-reset.tex: "斯坦科夫驻波比 0.0268 为熵旋场的共轭回流提供标定"
  - HUNTIAN_4320D 白皮书:          STANKOV_RATIO 0.0268f + "基于渠玉芝教授的熵旋理论"
  - 公理文档 (ENTROPY_SPIN_MASS_EMERGENCE_THEORY.md) 的理论框架 =
  - "渠玉芝熵旋理论 | 斯坦科夫驻波理论 | 共轭回流模型" 三源组合:
  - 熵旋理论本体属渠玉芝, 比值常数按项目命名属斯坦科夫驻波理论。
  - wiki 侧: /data/work/docs/wiki/knowledge-graph.db constants 表同样记录
  - "斯坦科夫比例 | 0.0268，特征常数" (physical_meaning 空, 源 = HUNTIAN
  - 白皮书); wiki 18-lightcone-matrix-validation.md 的理论来源行另记
  - "渠玉芝熵旋定理 + 斯瓦鲁驻波谐波理论" (驻波谐波线索的又一称呼,
  - 未与数值 0.0268 绑定)。各方均无推导 — 特征常数/经验常数。
- **导入 (8)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Integer`, `Data.Rational`, `Data.Bool`, `Relation.Nullary.Decidable`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `ChiralSpinor`
- **record 类型**: `DimensionMapping`, `WuXingEntropyState`, `state`, `state`
- **顶层签名 (10)**: `ManifoldDim4320`, `dimMap`, `StankovRatio`, `massEmergence`, `entropySpinNum`, `massNum`, `thermal-a6`, `conjugateStandingWave`, `shengModulation`, `keModulation`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Physics/EntropySpinBalance.agda`

- **module**: `Sovereign.Physics.EntropySpinBalance`
- **行数**: 114（代码 49 / 注释 44）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.EntropySpinBalance
  - 渠玉芝熵旋平衡定理 (GF(9) 版) — 微观量子熵 → 宏观电磁学的贯通 (0 postulate)
  - 深度证明: 把「熵旋平衡」从浅层锚点深化为「旋度部分(磁场)无散 + 耗散
  - 梯度」的贯通推导。与 ℚ 版 (EntropySpinVerification.divS-identity /
  - divS-zero-condition) 平行, 但落在离散第一性 GF(9) 基座上。
  - GF(9) 熵旋: S9 F H = curl9 F + H²·α·ẑ
  - 旋度部分 curl9 F = 磁场 (无散, div-curl-zero-GF9)
  - 耗散部分 H²·α·ẑ 沿 z (α = √2 是 GF(9) 生成元, 90° 方向)
  - 贯通链:
  - divS9 = div9(curl9 F) + div9(耗散)       [div9 线性]
  - = 0 + dz9(H²·α)                    [div-curl-zero-GF9 吃掉旋度]
  - = dz9(H²·α)                        [divS9-identity]
  - 平衡 (dz9(H²·α)=0) ⟹ divS9 = 0          [entropy-spin-balance]
  - 平衡 ⟹ 磁场无源性 (div9(curl9 F)=0)      [balance-closes-chain]
  - 这就是「量子环面流体的熵旋平衡 ⟹ 电磁场的无源动力学」的实质推导 —
  - 生成链从微观(熵旋)到宏观(电磁)的闭合定理。
- **导入 (5)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Physics.DiscreteMaxwellGF9`
- **顶层签名 (8)**: `dissipation9`, `entropy-spin9`, `dx9-const-zero`, `dy9-const-zero`, `div9-dissipation`, `divS9-identity`, `entropy-spin-balance`, `balance-closes-chain`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Physics/EntropySpinLaw.agda`

- **module**: `Sovereign.Physics.EntropySpinLaw`
- **行数**: 326（代码 227 / 注释 64）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.EntropySpinLaw
  - 渠玉芝熵旋定律的形式化核心 (0 postulate, 无洞)
  - 定律原文 (项目公理文档 ESB-MASS-EMERGENCE-20260306,
  - pyBitNet/docs/huntian/quantum-physics/axioms/ENTROPY_SPIN_MASS_EMERGENCE_THEORY.md):
  - 熵旋矢量   S⃗ = ∇×Ψ⃗ − κ·ℋ²·n̂        (κ = 0.85, 理论值/经验常数)
  - 熵旋密度张量 ρ_S^{μν} = ∂S^μ/∂x^ν − ∂S^ν/∂x^μ  (反对称)
  - 质量涌现   m = ∮_C S⃗·dA⃗  (离散化: 环绕平面 k=0 的有限求和)
  - 环面闭合条件 ∮_{γ₁}S·dl + ∮_{γ₂}S·dl = 2πC (未形式化, 见诚实边界)
  - 本模块在 (Fin 3)³ 环面 + ℚ 系数上形式化定律的可证核心:
  - §1 定律定义 (离散化): curlℚ / κ / n̂=(0,0,1) / entropySpinLaw
  - §2 ρ_S^{μν} 反对称: ρ^{xy} + ρ^{yx} ≡ 0 (符号, ℚ 环律)
  - §3 离散斯托克斯: 质量积分的旋度项消失
  - massIntegral (curlℚ Ψ) ≡ 0ℚ (望远镜消去, 符号)
  - 推论: m(Ψ,H) ≡ −κ·Σℋ² — 质量积分只余 ℋ² 项
  - (公理文档 m = ∮S·dA 的代数内核: 旋度部分对环绕平面积分无贡献)
  - 诚实边界:
  - 1) κ = 0.85 是公理文档给出的"理论值", 无公开推导 — 经验常数。
- **导入 (7)**: `Data.Fin`, `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Rational`, `Data.Rational.Properties`, `Sovereign.Physics.DiscreteEMField3D`
- **顶层签名 (22)**: `QScalar`, `QVector`, `curlℚ`, `kappaQ`, `normalZ`, `vscale`, `vsub`, `entropySpinLaw`, `sub-antisym`, `rho-antisym`, `sum3ℚ`, `telescope2`, `telescope3`, `merge4`, `sum3-distrib`, `sum3-nested-dx-zero`, `sum3-dy-zero`, `sum3-nested-dy-zero`, `massIntegral`, `scalarSum`, `massIntegral-curl-zero`, `entropySpinMass-reduction`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Physics/EntropySpinMicro.agda`

- **module**: `Sovereign.Physics.EntropySpinMicro`
- **行数**: 182（代码 117 / 注释 43）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.EntropySpinMicro
  - 渠玉芝量子熵理论的微观输运证明 (0 postulate, 无洞)
  - 目标: 补齐"微观数学证明"层 — 熵旋有序通道为何低损耗、阈值为何跨界、
  - 质量如何量子化, 全部在 (Fin 3)³ 环面 + ℚ 系数上符号证明。
  - §1 通量算子: fluxK (熵旋流经平面 k) / heatK (ℋ² 流经平面 k)
  - §2 通量输运恒等式 (核心): fluxK(S)(k+1) − fluxK(S)(k) ≡ −(heatK(k+1) − heatK(k))
  - ⇒ 熵旋流的沿 z 变化完全由 ℋ² 项决定; 旋度部分(纯熵旋态)无损耗 —
  - "光超导低耗散通道"的微观数学证明。
  - §3 无损条件: heatK 沿 z 守恒 ⇒ fluxK 沿 z 守恒 (flux-conserved)
  - §4 阈值通用化: ∀ a ≥ 1, 质量涌现 < 1/1000 (thermal-general) —
  - 修正公理文档的 a≥6 边界: 公式层的跨界点实际在 a≥1。
  - §5 量子化闭合实例: 单点 ℋ²=1 构型的 m ≡ −(κ·1)·1 (canonical-mass);
  - 一般 {0,1} 场的整数量子化 (m ≡ −κ·N·1) 需 9 点布尔分支+分配律,
  - 留作开放项 — 诚实边界, 不写假证明。
- **导入 (10)**: `Data.Fin`, `Data.Nat`, `Data.Nat.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Rational`, `Data.Rational.Properties`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.EntropySpinLaw`, `Sovereign.Physics.EntropySpinVerification`
- **顶层签名 (11)**: `planeSum`, `zero-minus-zero-plus`, `plane-distrib2`, `fluxK`, `heatK`, `flux-diff`, `flux-conserved`, `thermal-general`, `zeroΨ`, `pointH`, `canonical-mass`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Physics/EntropySpinQuantize.agda`

- **module**: `Sovereign.Physics.EntropySpinQuantize`
- **行数**: 250（代码 161 / 注释 53）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.EntropySpinQuantize
  - 熵旋质量量子化: 两个开放接缝的闭合 (0 postulate, 无洞)
  - 接缝 1 (一般 {0,1} 场整数量子化) — 闭合:
  - quantized-mass : 对任意 {0,1} 布尔场 H,
  - m(H) = massIntegral (S-field zeroΨ (fromBool∘H))
  - ≡ −(countQ9 H · m₀),  m₀ = ((κ·1)·1)
  - 即: 质量 = 活跃点数 × 单位质量 — 一般量子化定律。
  - 方法 (依 proof-engineer 附录 9.8 / wiki index E.3 "禁用 with"):
  - 逐点 Bool 显式二分支 (point-unit) + 构造子实例化 (sum3-unit/sum9-unit),
  - 全程符号, 无 with, 无 funext。
  - 接缝 2 (V4: m = C·m₀) — 形式闭合 + 诚实边界:
  - chern2-mass : 双活跃点构型的 m ≡ −(2·m₀) — C=2 实例。
  - 陈数 C 与活跃点数 N 的一般对应是框架公理化
  - (Base/Invariants: CHERN_NUMBER = 2), 不由本模块导出 —
  - 本模块闭合的是"质量 = N·m₀ 整数量子化"这一代数定律。
- **导入 (11)**: `Data.Fin`, `Data.Bool`, `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Rational`, `Data.Rational.Properties`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.EntropySpinLaw`, `Sovereign.Physics.EntropySpinVerification`, `Sovereign.Physics.EntropySpinMicro`
- **顶层签名 (26)**: `2ℚ`, `fromBool`, `m₀`, `countQ9`, `sum3-neg`, `zero-minus`, `sum3-zero-minus`, `dzero-minus`, `sum3-dzero-minus`, `sum3-scale-r`, `falseTerm`, `point-unit`, `sum3-unit`, `sum9-unit`, `curlPlaneZero`, `zero-sub`, `kappaSum9`, `curlPlaneZeroS3`, `chern2Config`, `chern2-count`, `massQ`, `quantized-mass`, `chern2-mass`, `κterm`, `massCore`, `quantized-mass-integral`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Physics/EntropySpinVerification.agda`

- **module**: `Sovereign.Physics.EntropySpinVerification`
- **行数**: 473（代码 392 / 注释 45）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.EntropySpinVerification
  - 渠玉芝量子熵理论的库内验证 (0 postulate, 无洞)
  - 依据已完成的库, 对熵旋定律的结构断言逐条验证:
  - V1 ρ_S^{μν} 反对称        — rho-antisym 应用于 S 场 (复用, §1)
  - V2 m=∮S·dA 旋度项消失     — massIntegral-curl-zero (复用, §1)
  - V3 ∇·S=0 熵旋守恒        — 本模块新证: divℚ (curlℚ Ψ) ≡ 0 (§2),
  - 与 divS-identity: divℚ S ≡ −∂z(κ·ℋ²·1) (§3)
  - ⇒ 修正公理文档的"无条件 ∇·S=0": 守恒 ⟺ ∂z(κ·ℋ²·1) = 0
  - (如 ℋ² 沿 z 常值)。divS-zero-condition 落链该条件形式。
  - V4 量子化 ∮S·dA = C·m₀  — 未验证: 已证 m ≡ −Σ[(κ·ℋ²)·1], 与
  - C·m₀ 的匹配需要额外假设 (m₀ 定义/陈数量子化), 诚实边界。
  - 验证方式: (Fin 3)³ 环面 + ℚ 系数, 全部符号证明; 无 funext
  - (构造子实例化 + 环律链, 与 EntropySpinLaw 同法)。
- **导入 (9)**: `Data.Fin`, `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Rational`, `Data.Rational.Base`, `Data.Rational.Properties`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.EntropySpinLaw`
- **顶层签名 (27)**: `negneg`, `v-rho-antisym`, `v-stokes`, `dxℚ-add`, `dyℚ-add`, `dzℚ-add`, `dxℚ-neg`, `dyℚ-neg`, `dzℚ-neg`, `dxℚ-sub`, `dyℚ-sub`, `dzℚ-sub`, `dxdy-commℚ`, `dydz-commℚ`, `dzdx-commℚ`, `six-rotateℚ`, `pair-cancel-1ℚ`, `pair-cancel-2ℚ`, `pair-cancel-3ℚ`, `six-zero`, `divℚ`, `divℚ-curl-zero`, `S-field`, `law-eq`, `pull-last`, `divS-identity`, `divS-zero-condition`
- **质量**: `refl`×26；无 postulate / 无 hole

## `src/Sovereign/Physics/FineStructureMapping.agda`

- **module**: `Sovereign.Physics.FineStructureMapping`
- **行数**: 145（代码 72 / 注释 47）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.FineStructureMapping
  - 物理学：精细结构常数的律算高维映射
  - 核心定理：环面单值化定理
  - α_电 = α_律算 × (π_欧 / π_全息) × 1/8
  - 本模块消除了电性文明物理常数 (ħ, c, e, ε₀) 的依赖，
  - 将所有尺度比例替换为纯律算不变量。
- **导入 (6)**: `Data.Rational`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`, `Sovereign.Physics.Scaling`, `Data.Rational`
- **record 类型**: `CategoryPhaseSync`
- **顶层签名 (14)**: `PiHolographic`, `PiEuclidean`, `ToroidalLevelFactor`, `CurvatureDeviation`, `AlphaElectric`, `AlphaElectricApprox`, `BohrRadiusRatio`, `ComptonWavelengthRatio`, `ClassicalElectronRadius`, `RydbergEnergyRatio`, `FineStructureSplitting`, `AnomalousMagneticMoment`, `NoContinuousConstants`, `standardPhaseSync`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Physics/H2OC60.agda`

- **module**: `Sovereign.Physics.H2OC60`
- **行数**: 240（代码 62 / 注释 132）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.H2OC60
  - H2O@C60 量子受限模型形式化: 6D 平动-转动动力学 -> T6 晶格映射
  - 实验来源:
  - DOI: 10.1063/5.0044267 (J. Chem. Phys. 154, 124311, 2021) IR光谱
  - DOI: 10.1063/5.0086842 (J. Chem. Phys. 156, 124101, 2022) INS量子计算
  - DOI: 10.1038/s41598-020-74972-3 (Sci. Rep. 10, 18329, 2020) THz时域
  - DOI: 10.1073/pnas.1210790109 (PNAS 109, 12894, 2012) 量子转动
  - 核心命题:
  - 1. H2O 6D TR 空间 ≅ T6 GF(3)^6 晶格
  - 2. ortho-H2O三重简并基态分裂 (0.52 meV) -> Ih->A4 对称性破缺
  - 3. ortho/para 自旋异构 -> C2 Frobenius 手性共轭
  - 4. 21 条热带 = 3(trit) x 7(七阶段) -> TR 能级的离散量子化
  - 5. 39 条谱线 = 3 x (12 + 1) -> A4 胞腔剖分 + 仲吕奇点
  - 6. 0.5 meV 基态分裂 -> Delta=sqrt(3) 能隙热阈值投影
  - 7. 10h ortho->para 转换 -> 环向缠绕因子 a=1 的手性分离弛豫
- **导入 (4)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.Winding`, `Sovereign.Structology.IhC60Vibration`
- **data 类型**: `SpinIsomer`
- **record 类型**: `TRState`
- **顶层签名 (30)**: `TR-Dim`, `T6-Dim`, `tr-equals-t6-dim`, `orthoDegeneracy`, `paraDegeneracy`, `ortho-para-ratio`, `conversionTime`, `groundStateSplitting`, `Ih-Order`, `A4-Order`, `symmetryBreakingRatio`, `TropicalBands`, `SpectralLines`, `TritStates3`, `SevenStages`, `A4Cells`, `ZhonglvPt`, `tropical-bands-decomposition`, `spectral-lines-decomposition`, `basic-channels`, `channels-equals-a4-plus-one`, `C60-TotalModes`, `C60-FundamentalModes`, `c60-modes-ref-freq46`, `c60-modes-equals-toroidal`, `energyGapSq`, `T6-Points`, `tr-ground-states`, `t6-ground-orbits`, `ground-state-match`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Physics/HamiltonianDiscrete.agda`

- **module**: `Sovereign.Physics.HamiltonianDiscrete`
- **行数**: 16（代码 9 / 注释 1）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | HamiltonianDiscrete — MSC 70 · 连续统TypeError→离散相空间
- **导入 (3)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.Base.Trit`
- **顶层签名 (2)**: `PhaseSpace`, `hamilton-conservation`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Physics/HoneycombMagneticField.agda`

- **module**: `Sovereign.Physics.HoneycombMagneticField`
- **行数**: 201（代码 32 / 注释 128）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.HoneycombMagneticField
  - 蜂窝磁场 — 蜂窝晶格几何与量子场的深度耦合
  - 蜂窝磁场不是单一物理概念, 而是在蜂窝状晶格结构中,
  - 由磁场引发或与之相关的一系列新奇量子现象的统称。
  - 核心洞察:
  - 蜂窝晶格 = 六角对称 = T⁶ 环面的 2D 截面
  - 蜂窝磁场 = GF(9) 共轭对在晶格上的驻波模式
  - 量子自旋液体 = 零幂族的凝聚态物理投影
  - 手性轨道电流 = ChiralInterference 的材料实现
  - 研究方向映射:
  - 1. 巨磁阻 (Mn₃Si₂Te₆) → 范数坍缩的材料实现
  - 2. 量子自旋液体 (Na₂Co₂TeO₆) → 零幂族的凝聚态投影
  - 3. 人造规范场 → Frobenius 共轭在晶格上的实现
  - 4. 拓扑效应 → T⁶ 环面在 2D 截面上的投影
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (9)**: `honeycomb-vertices-per-cell`, `honeycomb-coordination`, `honeycomb-symmetry`, `norm-collapse`, `insulator-norm`, `conductor-norm`, `zero-power`, `frobenius-involution`, `chern-number`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/HydrogenBondCoherence.agda`

- **module**: `Sovereign.Physics.HydrogenBondCoherence`
- **行数**: 179（代码 54 / 注释 88）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.HydrogenBondCoherence
  - 氢键网络相干性 — 六重取向态 + 软模临界指数
  - 细化 WaterCriticalDerivation 中的相干增强因子:
  - Pauling 冰规则 → 六重取向态 → GF(9) 六重相位副本
  - 相干长度标度 → 软模临界指数 → 声子谱权重比
  - 诚实声明:
  - 冰 Ih 晶格常数 (0.452nm) 和氢键能量 (0.21eV) 是实验输入
  - 其余从框架常数和已证定理推导
  - 0 postulate.
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **data 类型**: `PaulingOrientation`
- **顶层签名 (14)**: `pauling-orientations`, `distinct-orientations`, `redundant-orientations`, `critical-exponent-nu`, `soft-mode-exponent`, `soft-mode-frequency-zero`, `coordination-number`, `full-tour`, `toroidal`, `polar`, `weight-ratio-num`, `weight-ratio-den`, `weight-ratio-check`, `weight-ratio-denom`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/InvisibleOrbitCount.agda`

- **module**: `Sovereign.Physics.InvisibleOrbitCount`
- **行数**: 104（代码 50 / 注释 37）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.InvisibleOrbitCount
  - 不可见自由度的系统计数: 共轭轨道对账 (0 postulate, 无洞)
  - 先算后写 — 与知识库"64 分型 = 51 有形 + 13 无形"的对账结论:
  - (a) GF(9) Frobenius 轨道: 不动点 = 实轴 GF(3) (3 个), 共轭对 = 3 对,
  - 总轨道 = 6。 9 = 3 + 2×3 — 每个共轭对是同一轨道的两个投影方向
  - (RightHandedNeutrinoTheorem 的推广: σ(α)=−α 只是 3 对之一)。
  - (b) 三个空间坐标 GF(3)³ 在手征共轭 (negation) 下:
  - 不动点恰 1 个 (零点), 非零点两两配对, 对数 = (27−1)/2 = 13。
  - 13 无形分型的代数对应: 空间三坐标的 13 个 ± 共轭对 —
  - 每一对的两个方向中至多一个落在选定可观测投影内。
  - (c) 64 = 51 + 13 是六爻二进制空间 (2⁶) 上的知识库分派 — 51/13 的
  - 具体清单是描述层输入, 不由 GF(3) 代数导出 — 不写假定理。
  - "729 = 3⁶ 格点 51/13 划分" 数学上不成立 (729 ≠ 64), 不形式化。
  - 诚实边界:
  - (a) 一切假设、理论、概念并存 — 无恒对理论, 本模块不裁决任何物理
  - 理论的正误; 计数结构与既有理论构成互补描述。
  - (b) 13 的代数对应与卢先生清单的逐项对应是框架层解读;
  - 本模块证明的是计数结构本身 (不动点唯一性 + 对合 + 对数算术)。
- **导入 (6)**: `Data.Nat`, `Data.Empty`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (10)**: `sigma-fixed-iff-real`, `conjugatePair-distinct`, `orbitCount6`, `Space3`, `conj3`, `conj3-involutive`, `negate-fixed-only-T₀`, `conj3-fixed-only-zero`, `thirteenPairs`, `invisibleCount27`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Physics/IsingTriangle.agda`

- **module**: `Sovereign.Physics.IsingTriangle`
- **行数**: 63（代码 35 / 注释 15）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.IsingTriangle
  - 82 统计力学补强 — 三角 Ising 模型的 8 构型配分 (0 postulate)
  - 3 自旋 (T₁=+1, T₂=−1) 在三角形上: E = −(s₁s₂ + s₂s₃ + s₃s₁)
  - 8 构型: 2 个全对齐 (E = −3), 6 个混合 (E = 1)
  - 配分多项式: Z = 2x³ + 6x⁻¹ (x = e^{βJ}); 磁化对称 Σ m = 0
- **导入 (3)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (15)**: `sign`, `edgeE`, `E3`, `energy-₁₁₁`, `energy-₁₁₂`, `energy-₁₂₁`, `energy-₁₂₂`, `energy-₂₁₁`, `energy-₂₁₂`, `energy-₂₂₁`, `energy-₂₂₂`, `aligned-count`, `mixed-count`, `magnetization-zero`, `partition-counts`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Physics/LatticeMembrane.agda`

- **module**: `Sovereign.Physics.LatticeMembrane`
- **行数**: 232（代码 78 / 注释 101）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.LatticeMembrane
  - 膜分层引理 — 模板→频率→步长→层数的除法结构
  - 语料锚 (word_5, word_72):
  - "我们这次玩儿的模板是12×12的关系, 所以宇宙的底层模板是以太"
  - "以太就是12×12是144阶幻方的关系"
  - "它一直从高维进行沉降, 十的96次方以上呢"
  - "从以太的共振的十的96次方...总共宇宙里边, 它有12层"
  - "这个东西它每隔一个物理区间, 十的八次方到十的12次方, 产生的一个物理的膜"
  - 因果链 (单向):
  - 12×12=144 (以太模板) → 10^96 (沉降起点) → 步长 10^8 → 12 层膜
  - 可形式化部分:
  - 模板 144 = 12² (refl)
  - 起点 96 = 12 × 8 (refl)
  - 膜数 = 96 / 8 = 12 (refl)
  - 步长 8 = GF(9)* 的阶 = φ 的阶 = 2³ (refl)
  - 总量 144 = 96 + 48 = 96 + 3×16 (refl)
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.GroupTheory.DuodecClock`
- **顶层签名 (37)**: `template`, `template-is-12-squared`, `template-equals-polar`, `descent-start`, `descent-total`, `above-96-span`, `above-96-span-val`, `above-96-is-3-times-16`, `step-size`, `step-size-equals-gf9-star-order`, `step-size-is-2-cubed`, `membrane-count`, `membrane-count-is-12`, `membrane-count-equals-joint-period`, `template-equals-count-squared`, `freq-layer`, `freq-layer-1`, `freq-layer-5`, `freq-layer-9`, `freq-layer-12`, `info-zone-boundary`, `emotion-zone-boundary`, `info-layers`, `emotion-layers`, `matter-layers`, `total-layers`, `total-layers-is-12`, `three-plus-nine`, `step-8-consistent`, `step-12-inconsistent`, `template-joint`, `start-joint`, `count-joint`, `step-gf9`, `pybitnet-depth`, `pybitnet-mid-pump`, `pybitnet-mid-pump-val`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/Physics/LightCone.agda`

- **module**: `Sovereign.Physics.LightCone`
- **行数**: 137（代码 41 / 注释 70）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.LightCone
  - 光锥边界公理系统: 将 LightConeSide 从 postulate 升级为可计算公理
  - 物理基础: 渠玉芝熵旋理论 — 光子通过左右旋螺旋对抵消形成中心驻波(质量涌现)
  - 光锥以内(银河系/火大): 光速不变 -> 光子沿类时测地线 -> 物质粒子
  - 光锥以外(仙女座):     光速可变 -> 光子全息瞬时 -> 未凝聚为物质
  - 光锥边界:             C2 Frobenius 不动点 -> 7个退化轨道 -> 21条热带
  - 核心公理 (6条构造性 + 0 postulate):
  - LC-1: 因果分解 LCSide = In | Out | Bdy
  - LC-2: 信息权重 weight(In)=3, weight(Out)=1, weight(Bdy)=7
  - LC-3: 全息对偶 holographicDuality (构造性, refl闭合)
  - LC-4: 边界量子化 boundaryOrbitCount=7 (来自 T6/(C2xC3))
  - LC-5: 热带产生 3x7=21
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.BurnsideT6`
- **data 类型**: `LCSide`, `PhotonState`, `EntropySpinResult`
- **顶层签名 (10)**: `weight`, `info-ratio`, `tropical-from-boundary`, `spectral-39`, `boundaryOrbitCount`, `boundary-tropical`, `StankovRatio`, `holographicDuality`, `holographicDuality-const`, `holographic-tropical`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Physics/LightConeMatrix.agda`

- **module**: `Sovereign.Physics.LightConeMatrix`
- **行数**: 266（代码 63 / 注释 164）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.LightConeMatrix
  - 光锥矩阵: GF9^3 上的光子↔物质熵旋变换算子
  - 理论基础: 渠玉芝熵旋定理 + 大衍4320D T6商空间理论
  - 光子 = C3相位旋量 (c3-cw/ccw 螺旋激发)
  - 物质 = 左右旋螺旋对抵消形成的中心驻波 (C2不动点)
  - 光锥矩阵 = 描述这一变换的线性算子, 分解在4320D的因子结构上
  - 核心算子分解:
  - M = M_24 ⊗ M_36 ⊗ M_5  (24=Merkaba, 36=水态, 5=五行)
  - 作用在 GF9^3 ≅ T^6 上
  - 物理对应的代数结构:
  - Merkaba层 (24=2x12):  C2手性 x A4相位 → 螺旋对配对
  - 水态层  (36=3x12):   C3三态 x A4谐波 → 信息承载
  - 五行层  (5):          模数共振 → 质量涌现通道
- **导入 (9)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Structology.BurnsideT6`, `Sovereign.Physics.LightCone`
- **data 类型**: `PMState`
- **顶层签名 (20)**: `classifyGF9`, `classifyGF9³`, `Chern`, `Stankov`, `entropySpinDensity`, `lc-step`, `lc-step-annihilates-imag`, `lc-step-fix-c2`, `lc-matrix`, `lc-fixpoint-count`, `lc-photon-count`, `lc-c2-consistency`, `MerkabaFactor`, `WaterFactor`, `WuxingFactor`, `lc-4320-decomposition`, `lc-boundary-channels`, `couplingStrength`, `coupling-a1`, `lc-iterate`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Physics/LightRotationFrequency.agda`

- **module**: `Sovereign.Physics.LightRotationFrequency`
- **行数**: 142（代码 37 / 注释 73）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.LightRotationFrequency
  - 光自转频率 — 从 α⁴=1 推导代数周期, 频率标定保留 (0 postulate)
  - HONEST: 诚实边界:
  - α⁴=1 给出代数周期 4, 但无法给出物理频率 (Hz)
  - 频率需要物理输入 (步长持续时间), 无法从纯代数推导
  - 本模块将自转频率表达为 Frobenius 频率的函数, 减少自由参数
  - §1 代数周期: α⁴=1 → 旋转周期 4
  - §2 Frobenius 周期: σ²=id → 共轭周期 2
  - §3 组合周期: lcm(4,2) = 4
  - §4 频率关系: ν_rotation = ν_Frobenius / 2
  - §5 诚实边界: 无法从纯代数推导 Hz
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (13)**: `alpha-order`, `alpha-order-correct`, `rotation-angle-degrees`, `rotation-angle-correct`, `frobenius-order`, `frobenius-order-correct`, `lcm-4-2`, `lcm-4-2-correct`, `four-divisible-by-2`, `freq-ratio-algebraic`, `freq-ratio-correct`, `order-relationship`, `freq-times-frobenius`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Physics/LightRotationTernary.agda`

- **module**: `Sovereign.Physics.LightRotationTernary`
- **行数**: 204（代码 73 / 注释 93）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.LightRotationTernary
  - 光自转与三进制编码 — α 阶 4 结构的形式化 (0 postulate)
  - 核心: 光的自转由 α 的 4 阶循环群描述, 每步旋转 90°。
  - α⁰ = 1  (0°,   无旋转)
  - α¹ = α  (90°,  第一象限)
  - α² = 2  (180°, 反向)
  - α³ = 2α (270°, 第三象限)
  - α⁴ = 1  (360° = 0°, 回到原点)
  - 三进制编码: 4 个旋转状态用 2 个 Trit 编码 (3² = 9 ≥ 4)
  - HONEST: 频率标定: 自转频率 2.92×10⁸ Hz 是标定参数, 非推导值
  - §1 旋转状态: Sub4 类型 (已有 GF9.agda)
  - §2 三进制编码: 4 状态 → 2 Trit
  - §3 频率标定: 自转频率与 Frobenius 周期
  - §4 与光学窗口的对接
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (16)**: `rotation-state-count`, `rotation-state-count-correct`, `rotation-period`, `rotation-period-correct`, `encode-rotation`, `decode-rotation`, `roundtrip-encode-decode`, `decode-encode-00`, `decode-encode-10`, `decode-encode-01`, `decode-encode-11`, `ternary-capacity`, `encoding-injective`, `decoding-surjective`, `capacity-sufficient`, `capacity-sufficient-correct`
- **质量**: `refl`×24；无 postulate / 无 hole

## `src/Sovereign/Physics/MaxwellFromLagrangian.agda`

- **module**: `Sovereign.Physics.MaxwellFromLagrangian`
- **行数**: 233（代码 113 / 注释 87）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.MaxwellFromLagrangian
  - 从作用量原理推导 Maxwell 四律 (L3 深层证明)
  - 核心命题:
  - 给定拉格朗日密度 L = ½|E|² - ½|B|², 作用量 S = Σ_p L(p),
  - 变分 δS/δφ = 0 给出 Gauss 定律, δS/δA = 0 给出 Ampère 定律。
  - 结合已有的 div(curl A)=0 和 curl(grad φ)=0, 得到全部四律。
  - 证明策略:
  - §1 拉格朗日密度定义 (GF(3) 上的精确算术)
  - §2 Gauss 定律: δS/δφ = 0 → div E = 0
  - §3 Maxwell 四律汇总 (引用已有定理)
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`, `Sovereign.Physics.DiscreteMaxwellTime`
- **顶层签名 (15)**: `half`, `electricEnergy`, `magneticEnergy`, `lagrangianDensity`, `extFieldFromPotential`, `dx-neg`, `dy-neg`, `dz-neg`, `vxextField`, `vyextField`, `vzextField`, `div-neg-grad`, `gauss-law`, `maxwell-four-laws-dynamic`, `maxwell-four-laws-static`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Physics/ObservabilityAngle.agda`

- **module**: `Sovereign.Physics.ObservabilityAngle`
- **行数**: 46（代码 10 / 注释 26）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.ObservabilityAngle
  - 可观测性角度 — 感官 2-进位采样序列的形式化 (0 postulate, 全 refl)
  - 锚点 (卢先生): 感官对电磁场的采样角度是严格的 2-进位减半序列:
  - 闻 1/2 转 = 180°, 看 1/4 转 = 90°, 想 1/8 转 = 45°,
  - 听 1/16 转 = 22.5°, 尝 1/32 转 = 11.25°, 触 1/64 转 = 5.625°。
  - GF(9) 中的共轭角 = 90° (α²=-1 生成, Frobenius 交换 α↔-α)。
  - 眼(看)采样角 = 90°。二者匹配 → 「眼睛只能看到 90° 旋转的电磁场」。
  - 本模块把「可见光的可观测性」从定性论述固化为可审计的代数事实:
  - 光子结构角 = 眼睛采样角 = 90° (减半 1 次), refl 直接落链。
  - 表示约定: 角度以「2-进位减半次数」编码 (ℕ):
  - 0 = 180° = 1/2 转, 1 = 90° = 1/4 转, 2 = 45° = 1/8 转, ...
  - 该编码是采样角的本质结构 (2 的幂次分母), 与 GF(9) 的 α 旋转 (4 阶)
  - 在 90° 档位精确对齐。
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (3)**: `photon-structure-angle`, `eye-sampling-angle`, `visible-light-observable`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/OpticalSampling.agda`

- **module**: `Sovereign.Physics.OpticalSampling`
- **行数**: 357（代码 109 / 注释 170）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.OpticalSampling
  - 光学采样理论 — 眼睛 = 90° 匹配滤波器 (0 postulate)
  - 核心主张 (卢先生语料):
  - "眼睛叫做矩阵系统，它叫透镜矩阵，眼睛只能看到 90 度旋转的电磁场"
  - "只要能形成 90 度的电磁场，就能形成光"
  - "看到就是范数坍缩在采样端的命名"
  - 形式化:
  - §1 采样端定义: 眼睛 = 90° 匹配滤波器
  - §2 "看到"= 范数坍缩: N(a+bα) = a²+b²
  - §3 频率定义采样窗口: 可见光 = 90° 共振的频率区间
  - §4 采样率-频率正比律
  - §5 发射端-采样端互锁
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Empty`, `Data.Product`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.ObservabilityAngle`
- **顶层签名 (39)**: `sampling-angle`, `sampling-angle-matches-photon`, `is-visible`, `alpha-visible`, `zero-invisible`, `norm-surjective-0`, `norm-surjective-1`, `norm-surjective-2`, `norm-surjective`, `norm-alpha-nonzero`, `norm-alpha2-nonzero`, `norm-conjugate-equal`, `norm-alpha-power-4`, `norm-nondegenerate`, `norm-nondegenerate-at`, `norm-nondegenerate-witness`, `optical-window-nondegenerate`, `optical-window-nondegenerate-all`, `sampling-rate-lower-bound`, `sampling-rate-lower-bound-correct`, `norm-alpha0`, `norm-alpha1`, `norm-alpha2`, `norm-alpha3`, `alpha-pow`, `norm-alpha-all`, `frequency-period-product`, `frequency-period-product-correct`, `sampling-window-width`, `sampling-window-width-min`, `sampling-window-width-max`, `sampling-rate`, `sampling-rate-at-4`, `sampling-rate-at-8`, `sampling-rate-at-12`, `emission-visible`, `emission2-visible`, `emission3-visible`, `zero-not-visible`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/Physics/OpticalWindow.agda`

- **module**: `Sovereign.Physics.OpticalWindow`
- **行数**: 498（代码 182 / 注释 227）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.OpticalWindow
  - 光学窗口形式化 — 可见光 = 电磁学的频率窗口 (0 postulate)
  - 核心主张: 光不是独立实体, 是电磁场在 Frobenius 频率窗口的共振表现。
  - 光 = 90° 共振 = α (阶 4, α²=-1, 1²+α²=0²)
  - 可见光频段 430-770 THz = 频率标定层的子集
  - 干涉/衍射 = 矩阵间循环 + 压差最小路径
  - 零幂族 (Zero Power Family):
  - 0² 不是"零的平方", 而是"零的二次幂 = 零"。
  - 零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
  - 零吸收一切幂次, 零的相位空间是单点 (无方向自由度)。
  - 出生证明 1²+α²=0² 中的 0² 是零幂族语义。
  - §1 光的代数定义: α 阶 4, 90° 共振
  - §2 可见光频段: 频率窗口形式化
  - §3 干涉: 离散叠加原理
  - §4 衍射: 离散 Huygens-Fresnel
  - §5 与已有模块的对接
- **导入 (10)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.ObservabilityAngle`, `Sovereign.Physics.OpticalSampling`
- **data 类型**: `Polarization`, `Absorption`
- **顶层签名 (40)**: `one-squared`, `zero-squared`, `light-birth`, `VisibleField`, `alpha-is-visible`, `alpha2-is-visible`, `alpha3-is-visible`, `zero-not-visible`, `visible-window-nondegenerate`, `OpticalWindow`, `optical-freq-min`, `optical-freq-max`, `optical-window-size`, `optical-window-size-correct`, `interfere`, `constructive`, `destructive`, `destructive-zero`, `constructive-0`, `constructive-1`, `constructive-2`, `neighbor-sum`, `const-neighbor-sum-0`, `rotate-polarization`, `rotate-period-4`, `polarization-to-gf9`, `polarization-rotation`, `decay-factor`, `propagate-step`, `propagate-preserves-norm`, `propagate`, `alpha-4-times`, `propagate-4`, `propagate-4k`, `propagate-period-341`, `absorb-step`, `absorb-full-zero`, `absorb-no-change`, `absorb-max-period-2`, `absorption-opaque`
- **质量**: `refl`×37；无 postulate / 无 hole

## `src/Sovereign/Physics/PhaseTransition.agda`

- **module**: `Sovereign.Physics.PhaseTransition`
- **行数**: 109（代码 30 / 注释 57）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.PhaseTransition
  - 相变 = 范数边界穿越
  - 核心映射:
  - 固态→液态: N=2→N=1 (范数减小)
  - 液态→气态: N=1→N=2 (范数增大)
  - 超导相变: N=1→N=0 (范数坍缩到零态)
  - 诚实边界:
  - 临界温度的具体数值是实验输入, 非框架推导
  - 45℃ 作为水的特征温度已被实验确认, 但第二临界点确切位置仍有争议
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Base.Invariants`
- **data 类型**: `PhaseTransition`
- **顶层签名 (6)**: `homogeneous-nucleation-temp`, `second-critical-temp-low`, `second-critical-temp-high`, `solid-norm`, `liquid-norm`, `superconducting-norm`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/ProteinFolding.agda`

- **module**: `Sovereign.Physics.ProteinFolding`
- **行数**: 130（代码 42 / 注释 58）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.ProteinFolding
  - 蛋白质折叠 — T⁶ 环面上的构象空间
  - 核心映射:
  - 蛋白质构象空间 = T⁶ 环面 (729 个可能构象)
  - 天然折叠态 = 零态 (零幂族保证稳定性)
  - 折叠路径 = 范数单调递减
  - 氢键网络 = GF(9) 矢量场相干对齐
  - 诚实边界:
  - 蛋白质构象空间的 729 个状态是理论最大状态数
  - 实际折叠路径受能量函数约束
  - 氢键网络的相干对齐是候选模型
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (12)**: `Conformation`, `native-state`, `native-is-zero`, `native-stability`, `folded-solid`, `unfolded-liquid`, `native-norm`, `hydrogen-bond-cond`, `hydrogen-bond-valid`, `non-hydrogen-bond`, `unfolded-state-norm`, `folded-state-norm`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Physics/QuantumChemistry.agda`

- **module**: `Sovereign.Physics.QuantumChemistry`
- **行数**: 225（代码 48 / 注释 132）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.QuantumChemistry
  - 量子化学 — T⁶ 离散环面上的分子结构
  - ⚠️ 核心原则:
  - 量子化学不是薛定谔方程在势能面上的求解,
  - 而是 T⁶ 离散环面上 GF(9) 矢量场的构型优化与范数投影。
  - "原子/分子" = 由 GF(9) 共轭对构成的、在 729 个格点间转移的离散驻波模式。
  - 与标准量子化学的区别:
  - 标准: 基函数=高斯/平面波, 电子相关=CC/CI, 势能面=连续曲面
  - 我们: 基函数=T⁶格点GF(9)矢量, 电子相关=范数坍缩, 势能面=离散相位跃迁
  - 包含:
  - §1 电子结构: 水的 10 电子 → T⁶ 维度锁定
  - §2 键角 104.5°: α乘法90° + 黄金分割修正
  - §3 偶极矩: 范数矢量的投影长度
  - §4 氢键: 范数闭包的轨道重叠
  - §5 离散角度体系: 精确离散值
  - 0 postulate.
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (16)**: `water-electrons`, `t6-dim`, `max-electrons-per-dim`, `t6-max-electrons`, `water-not-full`, `alpha-rotation-deg`, `bond-angle-deg`, `half-bond-angle-deg`, `bond-angle-deviation`, `dipole-norm`, `angle-0`, `angle-45`, `angle-90`, `angle-180`, `angle-270`, `angle-360`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Physics/QuantumErrorCorrection.agda`

- **module**: `Sovereign.Physics.QuantumErrorCorrection`
- **行数**: 145（代码 55 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.QuantumErrorCorrection
  - 量子纠错 — GF(3) 表面码 + Frobenius 相位保护
  - 核心映射:
  - 量子比特 = GF(3) 元素 (三态: 0, 1, 2)
  - 错误 = 范数扰动 (N=1→N=2)
  - 纠错 = 范数坍缩检测 + 逆操作恢复
  - 容错 = 零态稳定性 (零幂族)
  - 诚实边界:
  - GF(3) 表面码是概念框架, 未完全形式化所有错误类型
  - 容错阈值的精确值需实验校准
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (17)**: `Qutrit`, `qutrit-0`, `qutrit-1`, `qutrit-2`, `phase-flip`, `frobenius-error`, `no-error`, `detect-zero`, `detect-one`, `detect-two`, `zero-no-correction`, `frobenius-involution`, `phase-protection`, `phase-protection-is-involution`, `norm-zero`, `norm-one`, `norm-two`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/QuantumFieldAstrophysics.agda`

- **module**: `Sovereign.Physics.QuantumFieldAstrophysics`
- **行数**: 225（代码 43 / 注释 131）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.QuantumFieldAstrophysics
  - 量子场天体物理学 — 一切都是量子场的显化
  - 核心主张: 天体不是经典物理的引力体, 而是量子场的宏观驻波。
  - 从 GF(9) 量子场基底出发, 推导光、物质、膜、天体的统一结构。
  - 因果链:
  - GF(9) 量子场 → Frobenius 驻波 → 范数坍缩 → 光/物质/天体
  - 已证定理引用:
  - light-birth: 1²+α²=0 (光的出生证明)
  - galoisConjugate²: σ²=id (驻波对合)
  - norm-collapse: N(x)=x·σ(x) (信息坍缩)
  - charge-conservation (电荷守恒)
  - tri-period-zero: 三步归零 (基础驻波周期)
  - 0 postulate.
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.NormCollapse`, `Sovereign.Physics.OpticalWindow`, `Sovereign.Physics.RightHandedNeutrinoTheorem`
- **顶层签名 (15)**: `quantum-field-dim`, `quantum-states`, `quantum-field-char`, `standing-wave-involution`, `base-standing-wave`, `quantum-collapse`, `light-is-born`, `matter-antimatter-swap`, `energy-ratio`, `membrane-energy-ratio`, `overtone-1`, `overtone-2`, `overtone-3`, `membrane-1`, `membrane-12`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Physics/QuantumMotor.agda`

- **module**: `Sovereign.Physics.QuantumMotor`
- **行数**: 121（代码 44 / 注释 57）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (8)**: `Data.Fin`, `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`, `Sovereign.Algebra.TriCycGraph`, `Sovereign.Structology.ArthurMagicSquare`, `Sovereign.Structology.MotorStableStates`
- **顶层签名 (9)**: `RotorState`, `c3Step`, `c3Step³`, `StatorConstraint`, `MotorState`, `MotorStep`, `MotorStep³`, `StableState-fixedPoint`, `motorPeriod`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Physics/QuartzPhonon.agda`

- **module**: `Sovereign.Physics.QuartzPhonon`
- **行数**: 467（代码 177 / 注释 199）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.QuartzPhonon
  - 石英声子等离子体物理：相变、电离、泛音谱、C₃ 孤子
  - 训练验证：S2Sovereign 1.27B, 31000 步, 282 分钟
  - 实验锚定：T_αβ=846K, N14=3.17MHz, ρ_crit=0.38
  - 复用：H2OC60(46/21/39), EnergyGap(Δ²=3 镜像), EntropySpin(4320D 镜像), Invariants(144/46/C=2)
- **导入 (8)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Integer`, `Data.Rational`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`, `Sovereign.Base.Trit`, `Sovereign.Physics.H2OC60`
- **record 类型**: `IonizationState`
- **顶层签名 (70)**: `T-αβ`, `T-tridymite`, `T-cristobalite`, `T-liquidus`, `temp-span`, `temp-span-proof`, `soliton-λ₀`, `soliton-λ₁`, `soliton-λ₂`, `soliton-period`, `soliton-period-is-c3`, `λ₀≢λ₁`, `λ₀≢λ₂`, `λ₁≢λ₂`, `soliton-sum`, `soliton-sum-val`, `zhonglv-cycle`, `training-steps`, `closure-count`, `closure-remainder`, `closure-identity`, `closure-rate`, `χ`, `χ-zero`, `χ-one`, `χ-two`, `χ-three`, `χ-period3-0`, `χ-period3-1`, `χ-period3-2`, `chern-mod3`, `overtone-a-max`, `overtone-b-max`, `overtone-count`, `overtone-count-val`, `overtone-density`, `dim4320-factorization`, `dim4320-match`, `overtone-max-product`, `overtone-min-product`, `digitalRoot9`, `dr-groups`, `dr-per-group`, `dr-total`, `dr-total-val`, `dr-is-third`, `dr-polar-relation`, `dr-period9`, `dr-period9-3`, `dr-period9-6`, `steps-per-polar`, `steps-mod-polar`, `steps-per-toroidal`, `steps-mod-toroidal`, `I-eff`, `saha-const-scaled`, `saha-lhs-anchored`, `ρ-crit`, `ρ-plasma`, `ρ-percolation-theory`
  - … 其余 10 项
- **质量**: `refl`×47；⚠️ 3 postulate

## `src/Sovereign/Physics/RightHandedNeutrinoTheorem.agda`

- **module**: `Sovereign.Physics.RightHandedNeutrinoTheorem`
- **行数**: 107（代码 36 / 注释 50）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.RightHandedNeutrinoTheorem
  - 右旋中微子定理 (0 postulate, 无洞)
  - 定理内容 (代数层, 全部 refl):
  - νL = α, νR = −α (GF(9) 中的共轭对), σ = Frobenius/伽罗瓦共轭 z ↦ z³
  - 1. rightNeutrino-invisible   obs νR ≡ false — 右旋在可观测投影下不可见
  - 2. leftNeutrino-visible      obs νL ≡ true  — 左旋可见
  - 3. frobenius-swaps           σ(νL) ≡ νR    — Frobenius 交换左右旋
  - 4. realOf-nuR-zero           Re(νR) ≡ 0    — 右旋实部为零 (纯虚)
  - 5. conjugate-involutive-nuL  σ²(νL) ≡ νL   — 共轭对合
  - 6. conjugate-orbit-single    σ(νL) ≡ νR 且 νL ≢ νR — 同一条伽罗瓦轨道的
  - 两个不同投影方向 (共轭对 ≠ 两个独立实体)
  - 7. projection-complementary  两方向恰好一内一外 (可观测投影只取其一)
  - 诚实边界:
  - (a) 一切假设、理论、概念并存 — 无恒对理论。本模块不裁决任何物理理论
  - 的正误; "νR 是可观测物理态还是投影幻象" 属于框架层解读, 与标准
  - 模型 (跷跷板机制等) 构成互补描述而非替代关系。本模块证明的只是
  - 代数内核: 共轭对由 Frobenius 原生给出 (无外源实体), 且选定的
  - 可观测投影结构性地只看到其中一个方向。
- **导入 (5)**: `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (13)**: `neg-alpha`, `nuL`, `nuR`, `trit-eqᵇ`, `obs`, `realOf`, `rightNeutrino-invisible`, `leftNeutrino-visible`, `frobenius-swaps`, `realOf-nuR-zero`, `conjugate-involutive-nuL`, `conjugate-orbit-single`, `projection-complementary`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Physics/RootTwoGF9.agda`

- **module**: `Sovereign.Physics.RootTwoGF9`
- **行数**: 41（代码 9 / 注释 22）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.RootTwoGF9
  - 根号二·三步闭合 — 知识库原生锚点的形式化 (0 postulate, 全 refl)
  - 锚点 (卢先生): 「宇宙的晶体结构……所有的角度遵循为根号二。球的自转
  - r 和 R 的关系就是根号二, 一比一点四一四。你只需要竖的转一下, 横的
  - 转一下, 斜的转一下, 你就回归原点了。」
  - 在 GF(9) 中, 根号二**原生存在**: α² = -1 ≡ 2 (mod 3), 即 α 就是特征 3
  - 有限域中的 √2 (不可约多项式 x²+1=0 的根)。「根号二」从实数域的无理数
  - 变成了 GF(9) 的原生代数元 — 这正是离散第一性对连续统无理数的替代。
  - 三步闭合: T₁ ⊕ T₁ ⊕ T₁ = T₀ (1+1+1=3≡0 mod 3), 是 C3 加法群周期 3 的
  - 直接体现 — 三个正交方向各走一步、重复三次回原点。
- **导入 (3)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (2)**: `alpha-squared-is-root-two`, `three-steps-return-origin`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Physics/Scaling.agda`

- **module**: `Sovereign.Physics.Scaling`
- **行数**: 97（代码 43 / 注释 35）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.Scaling
  - 物理缩放：离散代数单位与物理单位的转换
  - 宪法条款：
  - 1. 律算代数是纯粹的 (Trit, Fin 3)，不包含物理单位。
  - 2. 物理单位 (meV, Hz) 是代数不变量在特定环境下的投影。
  - 3. 转换通过“缩放因子” (Scaling Factors) 实现，这些因子由实验测定。
- **导入 (4)**: `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.String`
- **data 类型**: `WuXingBase`
- **record 类型**: `Energy`, `Frequency`, `ExperimentalParameter`
- **顶层签名 (6)**: `EnergyGapScale`, `FrequencyScale`, `WuXingAlpha`, `toPhysicalEnergy`, `toPhysicalFrequency`, `baseToℕ`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Physics/SoftModeCriticality.agda`

- **module**: `Sovereign.Physics.SoftModeCriticality`
- **行数**: 94（代码 27 / 注释 42）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.SoftModeCriticality
  - 软模临界 — 从框架常数推导声子谱临界权重比
  - 目标: 将 228K 推导的最后一项依赖 (声子谱权重比 ≈1.58)
  - 从"实验输入"转化为"框架推导"。
  - 推导链:
  - FULL_TOUR = 6624, TOROIDAL_WINDING = 46, POLAR_WINDING = 144
  - → 声子谱临界权重比 = f(6624, 46, 144)
  - → 228K 完全闭合
  - 0 postulate.
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`
- **顶层签名 (10)**: `full-tour`, `toroidal`, `polar`, `coordination`, `six-fold`, `weight-num`, `weight-den`, `weight-num-val`, `weight-den-val`, `full-tour-equals-polar-times-toroidal`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/SpaceTimeMapping.agda`

- **module**: `Sovereign.Physics.SpaceTimeMapping`
- **行数**: 101（代码 26 / 注释 53）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.SpaceTimeMapping
  - 时空映射 — Frobenius 周期(时间) × 范数坍缩(空间)
  - 语料锚:
  - "时间: 频率" — 08-constants.md:140 "(时间: 频率)"
  - "空间: 格点" — 08-constants.md:140 "(空间: 格点)"
  - "1²+i²=0²" — 出生证明，范数坍缩的灵性层平方关系
  - "3²+4²=5²" — 勾股，范数坍缩的实数投影
  - 形式化映射:
  - 时间 = Frobenius 主频时钟 σ(x)=x³, 周期 2 (σ²=id)
  - 空间 = 频率平方投影 N(a+bα)=a²+b², 从 GF(9) 投射到 GF(3)
  - 宇/宙方向不裁决 (索引不稳定项), 采用功能定义
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.NormCollapse`
- **顶层签名 (6)**: `time-period`, `space-scale`, `space-collapse`, `time-space-unity`, `joint-period`, `magic-square-order`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Physics/Superconductivity.agda`

- **module**: `Sovereign.Physics.Superconductivity`
- **行数**: 132（代码 47 / 注释 55）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.Superconductivity
  - 超导态 — 范数边界的凝聚态投影
  - 核心映射:
  - 超导态 = N=0 (范数坍缩到零态, 零幂族保证稳定性)
  - 正常态 = N=1 (非零单位态)
  - 受限态 = N=2 (最大偏离态)
  - 诚实边界:
  - 临界磁场 Hc₂ 是候选映射, 非框架推导值
  - 超导态的范数分类与真实超导体的 Tc/Hc₂ 的定量关系需实验校准
  - 0 postulate.
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`, `Sovereign.Quantum.ZeroPowerQuantum`
- **顶层签名 (13)**: `norm-classify`, `norm-zero`, `norm-one`, `norm-two`, `superconducting-equilibrium`, `superconducting-stable`, `superconducting-power`, `superconducting-absorbˡ`, `superconducting-absorbʳ`, `norm-boundary-1-to-0`, `norm-boundary-0`, `defect-zero`, `defect-one`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Physics/TorusChain.agda`

- **module**: `Sovereign.Physics.TorusChain`
- **行数**: 151（代码 48 / 注释 70）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.TorusChain
  - 环面链 — GF(9) 构造序的完整性
  - 语料锚 (word_62):
  - "两极，然后只要一把它连上，它就会形成一个环面儿。
  - 就会归零，这个就是零……转180度就是个零……
  - 零和一是通的……再扭一个90度……
  - 这个动作就会形成克里斯托金体。"
  - 形式化映射:
  - 两极相连 → GF(3)→GF(9) 扩张, α 与 −α 共轭
  - 形成环面 → T⁶ = (GF(3))⁶ 环面格点
  - 归零(180°) → Frobenius 对合 σ²=id
  - 零和一通 → 零元唯一性, N(0)=0, N(1)=1
  - 扭90° → α 阶 4, 四步归位
  - 克里斯托水晶 → φ 阶 8, 子群链 ⟨-1⟩⊂⟨α⟩⊂⟨φ⟩
  - 本模块是已有定理的结构化汇聚, 不新增证明。
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (15)**: `poles-distinct`, `poles-cancel`, `alpha-squared-is-neg-one`, `torus-180`, `neg-one-is-alpha-squared`, `zero-plus-one`, `zero-absorbs`, `torus-90`, `torus-180-alpha`, `torus-270`, `torus-45`, `torus-360`, `neg-one-in-alpha`, `alpha-in-phi`, `chain-orders`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Physics/VectorFieldGeometricPhase.agda`

- **module**: `Sovereign.Physics.VectorFieldGeometricPhase`
- **行数**: 106（代码 49 / 注释 40）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.VectorFieldGeometricPhase
  - 矢量场决定几何相位 — Rust 核算的库内固化 (0 postulate, 无洞)
  - Rust 核算 (sov-math/sov-chiral/examples/entropy_spin_phase.rs) 的五项数据
  - 在此落为 Agda 定理, 逐项对应:
  - [1] S⃗ 为矢量场       → gradℚ/curlℚ 结构 (QVector)
  - [2] div∘curl = 0     → curl-kernel-source-free
  - [3] curl∘grad = 0    → curlQ-grad-zero (纯标量场不携带几何相位)
  - [4] divS-identity    → entropy-spin-phase-source (相位源仅沿 n̂)
  - [5] 质量 = −κ·N      → curl-flux-vanishes + vector-quantization
  - 三方场型对照 (并存互补, 非裁决, 文档层):
  - 主流宏观: 标量物质图像 — 几何相位需外贴 Berry 曲率
  - 斯瓦鲁量子场: 矢量场 (驻波谐波方向性) — 相位来自谐波方向结构
  - 渠玉芝熵旋: 矢量场 S⃗ = ∇×Ψ⃗ − κℋ²·n̂ — 旋度内核无源 (定理 2),
  - 几何相位/质量的全部来源是标量项 κℋ² 沿 n̂ 的梯度 (定理 4),
  - 且量子化为 −κ·N (定理 5)。矢量场选择决定了相位的一切。
  - 与 GF(3) 层 DiscreteEMField3D.curl-grad-zero (Trit 版) 的 ℚ 层对应。
- **导入 (9)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Rational`, `Data.Rational.Properties`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.EntropySpinLaw`, `Sovereign.Physics.EntropySpinVerification`, `Sovereign.Physics.EntropySpinMicro`, `Sovereign.Physics.EntropySpinQuantize`
- **顶层签名 (6)**: `gradℚ`, `curlQ-grad-zero`, `curl-kernel-source-free`, `entropy-spin-phase-source`, `curl-flux-vanishes`, `vector-quantization`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Physics/WaterAnchors.agda`

- **module**: `Sovereign.Physics.WaterAnchors`
- **行数**: 188（代码 34 / 注释 114）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.WaterAnchors
  - 水的四个科研锚点 — 2025-2026 公开数据的形式化映射
  - 锚点一: 水的"无人区"与第二临界点 (-45℃ / 228K)
  - 锚点二: 量子限域与水的"六重态" (零幂族物理实例)
  - 锚点三: H₂O@C₆₀ (46 基频 = TOROIDAL_WINDING)
  - 锚点四: 受限水的"超离子"与"铁电"行为 (divS-identity)
  - 关键定理: C₆₀ 的 46 个独立基频 = T⁶ 环面的 TOROIDAL_WINDING
  - 这是连接分子振动谱与离散全息拓扑学的首个可审计定理
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`, `Sovereign.Algebra.GF9`
- **顶层签名 (11)**: `temp-second-critical`, `temp-homogeneous-nucleation`, `temp-no-mans-land-low`, `zero-power-physical`, `c60-freq-equals-toroidal`, `toroidal-winding-value`, `freq-equals-winding`, `ih-order`, `ih-equals-10-times-12`, `c60-vib-dim`, `c60-vib-formula`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Physics/WaterCriticalDerivation.agda`

- **module**: `Sovereign.Physics.WaterCriticalDerivation`
- **行数**: 206（代码 47 / 注释 118）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.WaterCriticalDerivation
  - 水的第二临界点推导 — 从 T⁶ 环面到 228K
  - 推导链:
  - GF(9) 范数边界 (N=2) → 六重对称驻波模式
  - → 冰 Ih 晶格声子谱 → 氢键网络集体激发
  - → 温度算子 T = E/kB → T* = 228K
  - 诚实声明:
  - 推导链中每一步标注 [框架推导] 或 [实验输入]
  - 物理常数 (ℏ, kB, m_water, a_ice) 是实验输入
  - 228K 是推导输出 (不是拟合值)
  - 但推导的起点依赖实验输入的晶格常数和分子质量
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`
- **顶层签名 (16)**: `alpha-rotation-order`, `phi-rotation-order`, `six-fold-symmetry`, `coordination-number`, `ice-lattice-a`, `water-mass`, `boltzmann-const`, `hydrogen-bond-energy`, `acoustic-energy`, `optical-energy`, `branch-cross-temp`, `coh-bond-number`, `phase-fold-factor`, `collective-gap`, `collective-temp`, `branch-weight-ratio`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Physics/WaterQuantumIntegration.agda`

- **module**: `Sovereign.Physics.WaterQuantumIntegration`
- **行数**: 289（代码 80 / 注释 152）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.WaterQuantumIntegration
  - 水的量子数据全局统合 — 从 T⁶ 到凝聚态的完整理论链
  - 本模块统合已有水相关模块的全部数据, 建立从代数基座到物理投影的完整因果链:
  - T⁶ 环面 → GF(9) 矢量场 → 范数坍缩 → 水的量子态 → 凝聚态投影
  - 已有模块引用:
  - WaterStates.agda: 8 种状态 → T⁶ 编码
  - WaterStructure.agda: 广义液态 = 零态稳定性
  - WaterAnchors.agda: C₆₀ 46基频 = TOROIDAL_WINDING
  - QuantumChemistry.agda: 电子结构/键角/偶极矩/氢键
  - QuantumFieldAstrophysics.agda: 零幂族/范数坍缩/驻波
  - HoneycombMagneticField.agda: 蜂窝磁场/量子自旋液体
  - EntropySpinVerification.agda: divS-identity
  - IhC60Vibration.agda: C₆₀ 46基频
  - 0 postulate.
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (28)**: `standing-wave`, `norm-collapse`, `zero-power`, `birth`, `alpha-order-4`, `phi-order-8`, `phi-squared-alpha`, `t6-size`, `zero-is-identity`, `zero-stable`, `solid-to-liquid`, `liquid-to-gas`, `chiral-cancellation`, `liquid-equilibrium`, `norm-to-gf3`, `water-electrons`, `t6-max-electrons`, `c60-freq`, `toroidal-value`, `freq-equals-toroidal`, `ih-equals-10x12`, `c60-vib`, `honeycomb-vertices`, `honeycomb-coordination`, `honeycomb-symmetry`, `insulator-norm`, `conductor-norm`, `chern-number`
- **质量**: `refl`×15；无 postulate / 无 hole

## `src/Sovereign/Physics/WaterStates.agda`

- **module**: `Sovereign.Physics.WaterStates`
- **行数**: 217（代码 74 / 注释 97）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.WaterStates
  - 水的 8 种状态 → T⁶ 离散框架建模
  - 语料锚 (PPT 层, ≥7 处逐字坐实):
  - "水是标准的等离子结构，不止只有三态，还有：超临界流体、超固体、
  - 超流体、费米子凝聚态、等离子态。合计8种状态。"
  - 数据来源:
  - PPT 层: 8 种状态 + 温度阈值 + 两种排布 (百度百科可验)
  - 口述层: 5 种状态 (待验证, 不入库)
  - 维度层: 6/7/8 三变体 (语料内部, 不入库)
  - 形式化策略:
  - §1 水的 8 种状态 = T⁶ 的 8 个特定态
  - §2 温度阈值 = T⁶ 相变点
  - §3 两种排布 = GF(3) 手征 (T₀ 无序 vs T₁/T₂ 有序)
  - §4 4⁹/9⁴ 旋转力学 = DuodecClock 通道
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`
- **data 类型**: `WaterState`
- **顶层签名 (23)**: `water-state-count`, `state-to-t6`, `solid-is-zero`, `plasma-is-full`, `temp-second-critical`, `temp-homogeneous-nucleation`, `temp-no-mans-land-low`, `temp-density-max`, `solid-to-liquid`, `liquid-to-gas`, `dense-disordered`, `tetrahedral-ordered-l`, `tetrahedral-ordered-r`, `chiral-flip`, `dense-is-chiral-cancel`, `val-4-to-9`, `val-9-to-4`, `val-4-to-9-is`, `val-9-to-4-is`, `four-to-nine-is-two-to-eighteen`, `nine-to-four-is-three-to-eight`, `combined`, `combined-is`
- **质量**: `refl`×12；无 postulate / 无 hole

## `src/Sovereign/Physics/WaterStructure.agda`

- **module**: `Sovereign.Physics.WaterStructure`
- **行数**: 175（代码 39 / 注释 104）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Physics.WaterStructure
  - 水的离散全息结构 — 从零态到球形矢量场的统一
  - 核心主张:
  - 水不是经典流体, 而是 T⁶ 环面上的量子矢量场构型。
  - 广义液态 = 零态附近的稳定矢量场 + 范数坍缩到 GF(3)。
  - 水的不同"种" = T⁶ 状态空间中不同的 GF(3) 投影子集。
  - 球形矢量场 = T⁶ 上的 GF(9)-值旋度场在 3D 空间的投影。
  - 因果链:
  - GF(9) 共轭 → 驻波结构 → T⁶ 矢量场 → 范数坍缩 → 宏观水性质
  - T⁶ 旋度场 → 球谐模式 → 球形矢量场 → 水的电磁结构
  - 包含:
  - §1 广义液态: 零态稳定性 + 范数坍缩
  - §2 水种: T⁶ 投影子集的分类
  - §3 球形矢量场: T⁶ 旋度场的 3D 投影
  - §4 熵旋与水: S⃗ = ∇×Ψ⃗ − κℋ²n̂ 的水态表现
  - 0 postulate.
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.T6`, `Sovereign.Geometry.TorusGeometry`, `Sovereign.Quantum.ZeroPowerQuantum`
- **顶层签名 (6)**: `liquid-equilibrium`, `liquid-stable`, `norm-collapse-to-gf3`, `solid-to-liquid`, `liquid-to-gas`, `chiral-cancellation`
- **质量**: `refl`×5；无 postulate / 无 hole
