# 目录 `src/Sovereign/Base/` 逐模块审计记录

共 7 个模块。


## `src/Sovereign/Base/Axioms.agda`

- **module**: `Sovereign.Base.Axioms`
- **行数**: 38（代码 24 / 注释 4）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (5)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`
- **顶层签名 (6)**: `digitalRoot`, `IsStable`, `zhonglvAlign`, `zhonglvAlignCorrect`, `polarWindingAtomic`, `toroidalWindingAtomic`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Base/FunctionTheory.agda`

- **module**: `Sovereign.Base.FunctionTheory`
- **行数**: 77（代码 23 / 注释 40）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Base.FunctionTheory
  - 递归幂函数与零幂族 — 函数领域的第一性构造
  - 零幂族 (Zero Power Family):
  - 零幂不是算术乘法 (0×0=0), 而是量子矢量相位回归的代数形式。
  - 零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
  - 零吸收一切幂次, 零的相位空间是单点 (无方向自由度)。
  - 0² 不是"零的平方", 而是"零的二次幂 = 零" (零幂族)。
  - 语料: "零的平方=零的五次方……零的一就等于零的N次方" (word_98)
  - 语料: "只有0跨维度" / "0是一切的密码" (ppt_27, ppt_7)
  - 定位: 把幂函数从具体代数结构中抽象出来，作为递归函数论的基础。
  - 不依赖 GF(9) 或 Trit，避免循环依赖。
  - 核心定理:
  - §1 通用幂函数 power : (A→A→A) → A → ℕ → A
  - §2 幂等元幂稳定性: e*e=e → e^n=e
  - §3 零元幂吸收 (零幂族): 在含零元吸收律的结构中 0^(n+1)=0
  - 0 postulate.
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (4)**: `power`, `power-with-one`, `idempotent-power`, `zero-power-generic`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Base/Invariants.agda`

- **module**: `Sovereign.Base.Invariants`
- **行数**: 67（代码 23 / 注释 27）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Base.Invariants
  - 律算基础：核心拓扑不变量 (Topological Invariants)
  - 定义：全宇宙通用的数学真理，不随文明层级改变。
  - 包含：极向/环向缠绕数、陈数、能隙、主权 LCM。
- **导入 (1)**: `Data.Nat`
- **顶层签名 (10)**: `POLAR_WINDING`, `TOROIDAL_WINDING`, `HOLO_PI_NUM`, `HOLO_PI_DEN`, `CHERN_NUMBER`, `GAP_NUM`, `GAP_DEN`, `POW3₁₁`, `POW2₁₆`, `SOVEREIGN_LCM`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Base/Lü.agda`

- **module**: `Sovereign.Base.Lü`
- **行数**: 61（代码 42 / 注释 10）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Base.Lü
  - 十二律共享定义
  - 提供 LüName（律名）类型和索引映射，供 Structology、RootMath、T6 等模块共享
- **导入 (1)**: `Data.Fin`
- **data 类型**: `LüName`
- **顶层签名 (2)**: `lüToIndex`, `indexToLü`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Base/Trit.agda`

- **module**: `Sovereign.Base.Trit`
- **行数**: 299（代码 167 / 注释 80）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Base.Trit
  - 律算基础：GF(3) 三进制定义与运算
  - 核心公理：宇宙最小几何单元为 GF(3) 格点。
  - 包含：Trit {0, 1, 2}，加法和乘法运算。
  - rewriting 说明：本模块本身不使用 REWRITE 规则，但下游模块
  - T6.agda (div3k/mod3k)、XuanwuAbsorption.agda (mod46k/div46k)、
  - jac_Pigeonhole.agda (decode9-encode9) 通过导入本模块继承此选项。
  - rewriting 与 --safe 不兼容 (Agda 2.9.0 设计约束)，因此本项目
  - 不使用 --safe 验证，以 exit 0 + 零 postulate + 零 hole + 零 meta 为准。
- **导入 (4)**: `Data.Nat`, `Data.Integer`, `Data.Fin`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `Trit`
- **顶层签名 (40)**: `tritToℕ`, `tritToℤ`, `tritToCode`, `codeToTrit`, `_⊕_`, `_⊗_`, `⊕-identityˡ`, `⊕-identityʳ`, `⊕-comm`, `⊕-assoc`, `⊗-identityˡ`, `⊗-identityʳ`, `⊗-comm`, `⊗-assoc`, `⊗-distribˡ-⊕`, `⊗-distribʳ-⊕`, `⊗-zeroʳ`, `⊗-zeroˡ`, `tritToFin3`, `fin3ToTrit`, `tr-to-f3-to-tr`, `f3-to-tr-to-f3`, `c3-cw`, `c3-ccw`, `c3-cw³`, `c3-ccw³`, `negate`, `negate²`, `⊕-inverse`, `c3-cw-fin3`, `c3-ccw-fin3`, `negate-fin3`, `c3-cw-equiv`, `c3-ccw-equiv`, `negate-equiv`, `verifyZero`, `verifyMul`, `tri-period-zero`, `one-plus-one`, `char-3`
- **质量**: `refl`×141；无 postulate / 无 hole

## `src/Sovereign/Base/TritOps.agda`

- **module**: `Sovereign.Base.TritOps`
- **行数**: 67（代码 26 / 注释 28）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Base.TritOps
  - 基础运算：Trit 的损益操作逻辑
  - 核心洞察：
  - 如果 Trit 表示长度格点 L 的 3 的幂次指数 (L ≈ 3^k) 的模 3 值，
  - 那么：
  - "损一" (L × 2/3) 对应指数 -1 (模 3 循环)
  - "益一" (L × 4/3) 对应指数 +1 (模 3 循环)
  - 因此，损益操作在 Trit 层面上表现为**相位旋转**。
- **导入 (2)**: `Sovereign.Base.Trit`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `Op`
- **顶层签名 (5)**: `lossOp`, `gainOp`, `applyOp`, `lossCycle3`, `gainCycle3`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Base/ZeroGeometry.agda`

- **module**: `Sovereign.Base.ZeroGeometry`
- **行数**: 136（代码 80 / 注释 28）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Base.ZeroGeometry
  - 零的几何拓扑本源：完美球体几何 S²/A₄
  - v5.5 (2026-07-03): 几何不变量计算函数 + 五行基数的正多面体推导
- **导入 (5)**: `Data.Nat`, `Data.Bool`, `Data.Product`, `Cubical.Foundations.Prelude`, `Sovereign.Base.Invariants`
- **data 类型**: `PlatonicSolid`, `A4Element`
- **顶层签名 (17)**: `faceCount`, `vertexCount`, `edgeCount`, `eulerChi`, `eulerChiAllTwo`, `c5AxisCount`, `c5NonTrivialRotations`, `numPlatonicSolids`, `cellCount`, `eulerCharacteristic`, `chernNumber`, `theorem_euler_equals_chern`, `energyGap`, `theorem_energyGapInvariant`, `theorem_cellCountIs12`, `a4Order`, `theorem_a4Order_equals_cells`
- **质量**: `refl`×9；无 postulate / 无 hole
