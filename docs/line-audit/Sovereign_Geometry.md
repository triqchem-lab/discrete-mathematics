# 目录 `src/Sovereign/Geometry/` 逐模块审计记录

共 13 个模块。


## `src/Sovereign/Geometry/ConformalCore.agda`

- **module**: `Sovereign.Geometry.ConformalCore`
- **行数**: 546（代码 427 / 注释 42）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.ConformalCore
  - 共形几何核心：共形群 Conf = (C₃)⁶ ⋊ C₂ + 共形点 = Conf-轨道
  - GF(3) 保角性: λ²≡1 → 缩放保持内积不变 (inner-scale2-inv)
  - Conf = (C₃ × C₃ × C₃ × C₃ × C₃ × C₃) ⋊ C₂, |Conf| = 1458
  - 射影群 G = (C₃)³ ⋊ C₂ 是 Conf 的子群
  - 2026-08-14 修复与证明（0 postulate）:
  - ① 作用约定核对（数值穷举）: conf-mul (t₁+s₁·t₂ 扭转) 与 conf-action
  - （缩放后平移）在右作用约定 (g·h)·x = h·(g·x) 下完全一致。
  - 群论七条公理均为真命题, 已全部构造性证明。
  - ② conf-inv 修正: 旧版对 s=1 也取平移负, 但 (t,1) 是对合
  - （(t,1)(t,1) = (t+2t, 0) = id），真逆元 = 自身。旧 conf-inv-left
  - 对 s=1, t≠0 为假（数值反例 t=1: (i3 1,1)·(1,1) = (1,0) ≠ id）。
  - ③ t6Inner-conformal 修正: 旧版断言 ∀g 保内积, 对平移为假
  - （数值反例: ⟨(0,..),(1,..)⟩ = 0, 平移 1 后 = 2）。
  - 已收窄为 t6Inner-scale2-inv（真）+ t6Inner-translation-counter（反例定理）。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.T6`
- **record 类型**: `C3Vec`, `ConfElement`, `ConfOrbitRel`, `ConformalPointRec`
- **顶层签名 (58)**: `tritOf`, `finOf`, `tritOf-finOf`, `finOf-tritOf`, `c3`, `scale2`, `scale2²`, `c3³`, `i3`, `+₃-assoc`, `+₃-zeroˡ`, `+₃-zeroʳ`, `+₃-comm`, `+₃-inv`, `+₃-invʳ`, `scale2-⊕`, `x-plus-scale2-x`, `c3-scale2-conj`, `inner-scale2-inv`, `t6Inner`, `conf-id`, `cong-c3v`, `+v-assoc`, `+v-zeroˡ`, `+v-zeroʳ`, `+v-comm`, `+v-inv`, `+₂-assoc`, `+₂-zeroʳ`, `scale-on-trans`, `sot-dist`, `sot-comp`, `conf-mul`, `conf-inv`, `conf-card`, `conf-card-refl`, `sot-vzero`, `conf-id-left`, `conf-id-right`, `conf-inv-left`, `conf-inv-right`, `conf-assoc`, `c3ⁿ`, `c3ⁿ-hom`, `c3ⁿ-scale2`, `conf-action`, `action-mul-right`, `conf-action-id`, `ConfOrbit`, `conf-refl`, `conf-sym`, `conf-trans`, `scaleElem`, `t6Inner-scale2-inv`, `translate1`, `p0`, `q0`, `t6Inner-translation-counter`
- **质量**: `refl`×73；无 postulate / 无 hole

## `src/Sovereign/Geometry/ConformalInvariants.agda`

- **module**: `Sovereign.Geometry.ConformalInvariants`
- **行数**: 30（代码 13 / 注释 8）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.ConformalInvariants
  - T⁶ 共形不变量: 内积保持 + 射影→共形嵌入
  - 0 postulate
- **导入 (3)**: `Data.Nat`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (6)**: `conf-cardinality`, `conf-cardinality-1458`, `proj-order`, `proj-order-ok`, `index`, `index-ok`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Geometry/DiscreteManifold.agda`

- **module**: `Sovereign.Geometry.DiscreteManifold`
- **行数**: 39（代码 11 / 注释 17）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteManifold — 离散流形 (MSC 57)
  - T⁶ 作为离散流形，有限点集 + 组合不变量.
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (6)**: `chi-t6`, `chi-ok`, `points-t6`, `points-ok`, `neighbors-t6`, `neighbors-ok`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Geometry/ProjectiveCore.agda`

- **module**: `Sovereign.Geometry.ProjectiveCore`
- **行数**: 532（代码 410 / 注释 53）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.ProjectiveCore
  - 4320D 射影几何核心：规范群 G = (C₃)³ ⋊ C₂ + 射影点 = G-不可约轨道
  - G = (C₃ × C₃ × C₃) ⋊ C₂, |G| = 54
  - 信息 = 群轨道, 非 βη 语法等价
  - 2026-08-14 修复: 旧版 g-mul 为直接积但 g-action-full 带 C₂ 扭转（c2∘c3ⁿ），
  - 两者不匹配导致 ~g-trans 为假（反例: ⟨1,0⟩·⟨0,1⟩ 在 x=0 上 2 ≠ 1）。
  - 已修正为真半直积: (a,h₁)(b,h₂) = (ψ_{h₂}(a)+₃b, h₁+₂h₂)，ψ₁ = i3（取反）。
  - 群公理（g-id/g-inv/g-assoc）与轨道关系三性质（~g-refl/sym/trans）
  - 全部由构造性证明承担，0 postulate。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.T6`
- **record 类型**: `C3Triple`, `GElement`, `GOrbitRel`, `ProjectivePointRec`
- **顶层签名 (53)**: `cong₃`, `toFin`, `ofFin`, `ofFin-toFin`, `toFin-ofFin`, `c3`, `c2`, `i3`, `negate-⊕`, `+₃-assoc`, `+₃-zeroˡ`, `+₃-zeroʳ`, `i3-invol`, `i3-⊕`, `+₃-inv`, `+₃-comm`, `+₃-invʳ`, `c2²-id`, `g-id`, `+₂-assoc`, `+₂-self-inv`, `+₂-zeroʳ`, `+₂-comm`, `tw`, `tw-zero`, `tw-⊕`, `tw-tw`, `g-mul`, `g-inv`, `g-id-left`, `g-id-right`, `g-inv-left`, `g-inv-right`, `g-assoc`, `c3ⁿ`, `c3³-id`, `c3ⁿ-hom`, `dihedral`, `c2h`, `c2h-comp`, `g-action`, `g-action-full`, `act-0-law`, `action-mul-right-00`, `action-mul-right-01`, `action-mul-right-10`, `action-mul-right-11`, `action-mul-right`, `action-g-id`, `GOrbit`, `~g-refl`, `~g-sym`, `~g-trans`
- **质量**: `refl`×72；无 postulate / 无 hole

## `src/Sovereign/Geometry/ProjectiveInvariants.agda`

- **module**: `Sovereign.Geometry.ProjectiveInvariants`
- **行数**: 29（代码 18 / 注释 3）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Geometry.ProjectiveCore`
- **顶层签名 (4)**: `t`, `t-is-6624`, `p1`, `p2`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Geometry/ProjectiveOrbit.agda`

- **module**: `Sovereign.Geometry.ProjectiveOrbit`
- **行数**: 79（代码 30 / 注释 32）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.ProjectiveOrbit
  - 4320D 轨道分解：Burnside 映射与轨道计数
  - 构建在 ProjectiveCore 之上:
  - G = (C₃)³ ⋊ C₂, |G| = 54
  - 射影点 = G-不可约轨道
  - 全息信息轨道 = 729 × 6 − 54 = 4320
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.T6`, `Sovereign.Structology.BurnsideT6`, `Sovereign.Geometry.ProjectiveCore`
- **顶层签名 (9)**: `T6-cardinality`, `total-yao-space`, `G-cardinality`, `info-dim-4320`, `decomposition-4320`, `decomposition-4320-alt`, `shao-yong-identity`, `g-size-decomposition`, `statement-info-is-orbit`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Geometry/ProjectiveTransform.agda`

- **module**: `Sovereign.Geometry.ProjectiveTransform`
- **行数**: 37（代码 22 / 注释 7）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.ProjectiveTransform
  - 射影变换群 A₄ ⋊ C₃ + CRT 谱投影
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.T6`, `Sovereign.Structology.A4Group`, `Sovereign.Geometry.ProjectiveCore`, `Sovereign.Geometry.ProjectiveInvariants`
- **record 类型**: `Alignment`
- **顶层签名 (1)**: `CRTProjection`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Geometry/ProjectiveTransformHFM.agda`

- **module**: `Sovereign.Geometry.ProjectiveTransformHFM`
- **行数**: 99（代码 50 / 注释 35）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
  - 主证明见: ProjectiveTransform.agda
  - | Sovereign.Geometry.ProjectiveTransformHFM
  - A₄×C₃ 直积的 HFM 交叉验证
  - HFM 验证 (test/SovereignGroups.hs):
  - A₄ × C₃ 直积: dp (_A 4) (_C 3) 生成 36 元素, 12 共役类
  - 数学原理:
  - |A₄| = 12, |C₃| = 3
  - |A₄ × C₃| = |A₄| · |C₃| = 12 × 3 = 36
  - 有限直积的共役类数是因子共役类数的乘积:
  - conj(A₄ × C₃) = conj(A₄) × conj(C₃)
  - A₄ 有 4 个共役类 (类型 1, 3, 4, 4)
  - C₃ 有 3 个共役类 (阿贝尔群, 每个元素自成一类)
  - 总: 4 × 3 = 12 类
  - 相关模块:
  - Geometry.ProjectiveTransform — A₄ ⋊ C₃ 半直积 (36 阶)
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (10)**: `orderA4`, `orderC3`, `orderProduct`, `orderA4-ok`, `orderC3-ok`, `orderProduct-ok`, `conjClassesA4`, `conjClassesC3`, `conjClassesProduct`, `conjClassesProduct-ok`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Geometry/TorusAlgebra.agda`

- **module**: `Sovereign.Geometry.TorusAlgebra`
- **行数**: 58（代码 34 / 注释 7）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Fin`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.T6`
- **顶层签名 (8)**: `tritOf`, `finOf`, `CoordFunc`, `constFn`, `zeroFn`, `oneFn`, `χ₀-χ₁-comm`, `add-zero`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Geometry/TorusFourier.agda`

- **module**: `Sovereign.Geometry.TorusFourier`
- **行数**: 40（代码 17 / 注释 11）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Data.Fin`, `Data.Vec`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.Structology.T6`, `Sovereign.Format.CRT`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`
- **顶层签名 (3)**: `fourierProj`, `fourierInv`, `fourier-zero`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Geometry/TorusGeodesic.agda`

- **module**: `Sovereign.Geometry.TorusGeodesic`
- **行数**: 47（代码 27 / 注释 8）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.T6`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Geometry.TorusGeometry`
- **顶层签名 (12)**: `c1`, `c2`, `c3`, `c4`, `c5`, `c6`, `spiral6`, `spiral-period3`, `polar-step`, `toroidal-step`, `spiral-fulltour`, `polar-toroidal-comm`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Geometry/TorusGeometry.agda`

- **module**: `Sovereign.Geometry.TorusGeometry`
- **行数**: 263（代码 195 / 注释 32）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.TorusGeometry
  - T⁶ 环面几何：加法群结构 + 群公理 + 基本群 + 测地线
  - T⁶ = (GF3)⁶, 729 个格点的 6 维离散环面
  - 加法群: (C₃)⁶, 逐分量 +₃ mod 3
  - π₁(T⁶) ≅ (C₃)⁶ ≅ T6Lattice (离散环面的基本群同构于加法群本身)
- **导入 (7)**: `Data.Fin`, `Data.Nat`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.T6`
- **顶层签名 (32)**: `tritOf`, `finOf`, `neg3`, `t6Add`, `z3`, `t6Zero`, `t6Neg`, `b1`, `b2`, `b3`, `b4`, `b5`, `b6`, `+₃-assoc`, `+₃-comm`, `+₃-identityˡ`, `+₃-identityʳ`, `+₃-inverseˡ`, `+₃-inverseʳ`, `t6Add-assoc`, `t6Add-comm`, `t6Add-identityˡ`, `t6Add-identityʳ`, `t6Add-inverseˡ`, `t6Add-inverseʳ`, `genL`, `generator-order3`, `generator-comm`, `t6Scale`, `t6GeodesicN`, `geodesic-b1-3`, `geodesic-b1-6624`
- **质量**: `refl`×99；无 postulate / 无 hole

## `src/Sovereign/Geometry/Tryte.agda`

- **module**: `Sovereign.Geometry.Tryte`
- **行数**: 187（代码 91 / 注释 71）
- **OPTIONS**: `--rewriting --guardedness --allow-unsolved-metas`
- **头部注释（数学背景）**:
  - | Sovereign.Geometry.Tryte
  - 几何定义：Tryte 作为 T⁶ 环面的单点纤维截面
  - 核心几何意义：
  - 1. T⁶ 结构：复三维 (Complex 3D) 等价于 实六维 (Real 6D)。
  - 其坐标可表示为 $(z_1, z_2, z_3) \in \mathbb{C}^3$。
  - 在实基底展开下为 $(x_1, y_1, x_2, y_2, x_3, y_3) \in \mathbb{R}^6$。
  - 2. 局部平凡化 (Local Trivialization)：
  - 在 T⁶ 的任意一点 p 处，纤维 (Fiber) 局部同构于基底空间的切空间。
  - 由于我们处理的是离散商空间，这个切空间被离散化为 6 个 GF(3) 维度。
  - 3. Tryte 定义：
  - Tryte 正是这个局部纤维的离散表示，包含 6 个 Trit。
  - Tryte = T⁶ 单点纤维截面 (Section over a point)。
  - 每一个 Trit 对应 T⁶ 的一个实维度方向上的离散坐标。
  - Tryte 的状态空间大小为 $3^6 = 729$。
  - 五行关联：
  - 主权状态机 (SovereignFiber) 总共有 30 个 Trit。
- **导入 (6)**: `Data.Vec`, `Data.Fin`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Data.Nat`
- **data 类型**: `WuXingIndex`
- **record 类型**: `LegalFiber`
- **顶层签名 (11)**: `Tryte`, `TryteStateCount`, `projectDimension`, `basisTryte`, `SovereignFiber`, `getWuXingTryte`, `setWuXingTryte`, `localChernContribution`, `localChernNormalized`, `globalChernConservation`, `globalChernConservationLegal`
- **质量**: `refl`×0；无 postulate / 无 hole
