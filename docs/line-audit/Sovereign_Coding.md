# 目录 `src/Sovereign/Coding/` 逐模块审计记录

共 8 个模块。


## `src/Sovereign/Coding/BCHGF9.agda`

- **module**: `Sovereign.Coding.BCHGF9`
- **行数**: 1258（代码 1068 / 注释 99）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.BCHGF9
  - GF(9) 上的 [8,6,3] BCH 码: 最小距离界 + 系统编码 + 单错纠错 (P1-2, wiki 94B)
  - 数学背景:
  - β = 1+α ∈ GF(9)* 是 8 阶本原元 (GF9.gen-generates-all, α²=−1)。
  - 取连续根 {β, β²} 的 BCH 码: C = { c ∈ GF(9)⁸ | S₁(c)=S₂(c)=0 },
  - 其中 Sᵣ(c) = Σₖ cₖ·β^{r·k} (校验子)。设计距离 δ = 3。
  - 生成多项式 g(x) = (x−β)(x−β²) = x² + 2x + (1+2α) 给出维数 8−2 = 6。
  - 宪法原则 (全离散, 无浮点, 无除法):
  - 1. 校验子 = ℕ 递归显式和 (左结合), 零消去/拆分/稀疏引理均为 ℕ 归纳。
  - 2. 最小距离 ≥ 3 的 BCH 界: 权 1 码字 ⟹ S₁ = vβⁱ ≠ 0 (非零积);
  - 权 2 码字 ⟹ Vandermonde 恒等式 S₂−βⁱS₁ = wβʲ(βʲ−βⁱ) ≠ 0 (β 的 8 阶性)。
  - 3. 编码 = 系统码 2×2 校验子解 (d = β²−β 的逆 = β, 无除法: d·dInv = 1 refl);
  - 解码 = 校验子对 (S₁,S₂) → (位置, 值) 查表 (唯一性由 β 幂两两不同保证),
  - 纠错 = 位调整, 正确性 = 编码正确性 + 校验子加性 + 查表反演。
  - 4. GF(9) 域公理全部引用 GF9.agda (0 postulate)。
  - 包含:
  - §1 校验子机器: synd/syndFrom 递归和 + 零消去/拆分/稀疏引理
- **导入 (10)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Bool`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Relation.Nullary.Decidable`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (72)**: `zero9`, `negate9`, `_-gf9_`, `_-₉_`, `beta`, `βPowT`, `β2Pow`, `*gf9-zeroˡ`, `*gf9-zeroʳ`, `negate9-⊕`, `negate9²`, `negate9-⊗`, `*-negateʳ`, `cancel-front`, `cancel-left-neg`, `cancel-right`, `cancel-mid`, `sub≢0`, `cancel-cross`, `+-shuffle`, `β-absorb`, `β-absorb2`, `synd`, `syndFrom`, `syndFrom-zero`, `synd-zero`, `synd-split`, `synd-cong`, `≢-sym`, `synd-single`, `synd-sparse2`, `toGF9-nonzero`, `βPowT-nonzero`, `β-diff`, `S₁`, `S₂`, `M1`, `M2`, `d`, `dInv`, `dInv-correct`, `dInv-comm`, `p1`, `p0`, `encode`, `peel2`, `S1-eq`, `S2-eq`, `S1-zero`, `S2minusS1`, `S2minusS1-zero`, `S2-zero`, `encode-correct`, `no-weight-1`, `vdm-identity`, `no-weight-2`, `m3`, `wt`, `weight-3-witness`, `min-distance`
  - … 其余 12 项
- **质量**: `refl`×110；无 postulate / 无 hole

## `src/Sovereign/Coding/CyclicGF27.agda`

- **module**: `Sovereign.Coding.CyclicGF27`
- **行数**: 5031（代码 4893 / 注释 79）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.CyclicGF27
  - GF(27) 根结构 → 长度 26 三元循环码 (P1-2, wiki 94B)
  - 数学背景:
  - GF(27) = GF(3)[γ]/(γ³+2γ+1), γ 为本原元 (阶 26, 见 GF27Separation)。
  - g(x) = x³+2x+1 的三个根 = {γ, γ³, γ⁹} (Frobenius 共轭三元组, 已证)。
  - 三元循环码 C = { c ∈ GF(3)²⁶ | c(γ) = 0 }, 其中 c(γ) = Σₖ cₖγᵏ。
  - 由 char 3 的 freshman's dream (x+y)³ = x³+y³: c(γ)=0 ⟹ c(γ³) = c(γ)³ = 0,
  - 同理 c(γ⁹) = 0 —— 一个校验子自动覆盖三个共轭根。
  - 循环性: shift(c)(γ) = γ·c(γ) (γ²⁶=1 处理回绕) ⟹ C 对循环移位封闭。
  - 宪法原则 (全离散, 无除法):
  - 1. γ 幂 = ℕ 递归 (右乘), 校验子 = 显式左结合和。
  - 2. freshman's dream (cube-sum) / Frobenius 乘法性 (cube-mul) / γ-结合·分配
  - 为 27² = 729 case 穷举 (策略 A, 生成表) —— 与 BCHGF9 的 81 case 同款。
  - 3. +27 公理为结构证明 (Trit ⊕ 公理), 0 postulate。
  - 包含:
  - §1 GF(27) 基本律: +27-comm/assoc, 零律, 幺律 (结构) + *27-comm (729 穷举)
  - §2 freshman's dream: cube-mul/cube-sum (729 穷举) + γ-结合/分配 (729 穷举)
- **导入 (7)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Problem.PvsNP.GF27Separation`
- **顶层签名 (44)**: `emb`, `cong₃`, `+27-comm`, `+27-assoc`, `+27-identityʳ`, `shuffle4`, `*27-comm`, `*27-zeroˡ`, `*27-zeroʳ`, `*27-identityˡ`, `*27-identityʳ`, `cube-mul`, `cube-sum`, `assoc-γ`, `distribˡ-γ`, `distribʳ-γ`, `cube-zero`, `cube-one`, `t³≡id`, `cubeTrit`, `emb-mul`, `embed-cube`, `γPow`, `γ3Pow`, `γ9Pow`, `eval`, `evalFrom`, `evalFrom-zero`, `eval-zero`, `eval-split`, `sum-cube`, `γ3Pow-cube`, `γ9Pow-cube`, `γ-pow-26`, `eval-cong2`, `eval-at-γ3`, `eval-at-γ9`, `IsCodeword`, `shift`, `shift-eval`, `cyclic-closed`, `root-γ3`, `root-γ9`, `generator-order-26`
- **质量**: `refl`×4395；无 postulate / 无 hole

## `src/Sovereign/Coding/ExpSquaring.agda`

- **module**: `Sovereign.Coding.ExpSquaring`
- **行数**: 36（代码 15 / 注释 11）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.ExpSquaring
  - 68 理论 CS 补强 — 平方乘幂算法的步数定理 (0 postulate)
  - GF(9) 的 α^8: 平方链 α² → α⁴ → α⁸ 需 3 次乘法 (对数步数),
  - 朴素乘法需 8 次 — 指数运算的 O(log n) vs O(n) 离散见证。
  - (α⁴ = 1 引用 GF9.alpha-powers-4: α² 为 −1, α⁴ = 1)
- **导入 (4)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (7)**: `sq1`, `sq2`, `sq3`, `exp-sq-result`, `sq-steps`, `naive-steps`, `log-vs-linear`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Coding/FFIProtocol.agda`

- **module**: `Sovereign.Coding.FFIProtocol`
- **行数**: 86（代码 32 / 注释 37）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.FFIProtocol
  - 65 桥接规范 — 外部计算结果的可信封装 (0 postulate, 无洞无占位)
  - 外部计算 (Rust sov-guard 等) 不可在 Agda 内运行; 协议用 record 封装
  - "值 + 正确性证明": Rust 侧生成实例时**必须附证明字段**, Agda 侧只
  - 消费实例并推导组合正确性。若 Rust 暂无法提供证明 → 记录仅为类型
  - 规范存在, Agda 不得使用其实例 (契约纪律, 见 §4)。
  - 与 NumericalSpec 的关系: NumericalSpec = 内部可证算法;
  - 本模块 = 外部计算的可信接口层 (Q16 值/模逆/线性方程组解三契约)。
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **record 类型**: `Q16Value`, `ModInverseResult`, `LinearSolveResult`
- **顶层签名 (4)**: `q16-quarter`, `modinv-3`, `modinv-transport`, `linear-solve-22`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Coding/HammingMetric.agda`

- **module**: `Sovereign.Coding.HammingMetric`
- **行数**: 286（代码 133 / 注释 115）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.HammingMetric
  - Hamming 距离的构造性形式化——编码理论度量公理的 0-postulate 证明
  - 核心原则:
  - 1. 字 = 有限子集, 载体 Fin N → Bool (与 ProbabilityAddition.Subset 同构)
  - 2. 距离 = 逐点不等性的计数, d(x,y) = Σ bool→ℕ(xᵢ xor yᵢ)
  - 3. 穷举法证点态引理 (策略 A), 代数链 + N 归纳组装全局定理 (策略 B)
  - 4. 0 postulate — 全部构造性 refl/≤-trans/s≤s
  - 包含:
  - §1. 基础设施: bool→ℕ / Subset / card / δ(逐点距离) / hamming(全局距离)
  - §2. 同一性:   d(x,y)≡0 → x≡y
  - §3. 对称性:   d(x,y)≡d(y,x)
  - §4. 三角不等式: d(x,z) ≤ d(x,y)+d(y,z)   ⭐ 度量公理核心
  - §5. 非负性 + 具体实例 (Fin 3)
  - §6. 离散独特性
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Bool`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (22)**: `Word`, `card`, `pointwise-xor`, `hamming`, `δ`, `δ-sym`, `δ-refl`, `δ-triangle`, `hamming-refl`, `hamming-sym`, `+-rearrange`, `≤-respʳ-≡`, `hamming-triangle`, `hamming-nonneg`, `x-ex`, `y-ex`, `z-ex`, `hamming-xy`, `hamming-xz`, `hamming-yz`, `triangle-ex`, `triangle-ex-tight`
- **质量**: `refl`×40；无 postulate / 无 hole

## `src/Sovereign/Coding/NumericalSpec.agda`

- **module**: `Sovereign.Coding.NumericalSpec`
- **行数**: 114（代码 39 / 注释 48）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.NumericalSpec
  - 65 数值分析 — 可验证计算的离散底座 (0 postulate)
  - 按 62/65 空白补全架构的优先级 1 实现 (不用 postulate 占位 —
  - 只写可证部分):
  - §1 Q16.16 定点规范: 乘法语义 + 整点精确性样本
  - §2 扩展欧几里得: gcd(46,13) = 1 的除法链 + Bézout 恒等式
  - (46 = 环向缠绕, 13 = 基本跃迁通道数 — H2OC60.basic-channels)
  - §3 模逆: 3⁻¹ ≡ 43691 (mod 2¹⁶) — 仲吕闭合因子的精确逆
  - §4 GF(3) 高斯消元: 2×2 系统求解 + 代回验证 + 消元步链
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (18)**: `Q16-ONE`, `q16-mul`, `q16-integer-exact`, `q16-half-squared`, `euclid-step-1`, `euclid-step-2`, `euclid-step-3`, `euclid-step-4`, `gcd-46-13-is-1`, `bezout-46-13`, `bezout-back-substitution`, `mod-inverse-3`, `inverse-in-range`, `elim-step-1`, `elim-step-2`, `solve-check-1`, `solve-check-2`, `nontrivial-check`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Coding/PigeonholeStandard.agda`

- **module**: `Sovereign.Coding.PigeonholeStandard`
- **行数**: 87（代码 20 / 注释 54）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.PigeonholeStandard
  - 定理四: 0-Postulate 鸽巢原理的形式化泛函化
  - 在 Agda 类型论下, 将 Fin N → Fin N 的内射/满射等价性
  - 无缝映射到 N×N 矩阵行列式的代数特征上.
  - 提供高效、可复用的构造性 proof-assistant 模板,
  - 解决高维状态机在定理证明器中的爆炸问题.
  - 证明引用:
  - jac_Pigeonhole.agda  — Fin 9→8 鸽巢原理 + REWRITE decode9-encode9
  - jac_Injectivity.agda — 单射 ⟺ 满射 (右逆构造)
  - jac_4320DClosure.agda — 729 点鸽巢推广 (附录 6 引用分离策略)
  - 全部 0 postulate.
- **导入 (3)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `FinEncoding`, `SeparatedRecursion`
- **顶层签名 (2)**: `Inj`, `Surj`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Coding/Trit.agda`

- **module**: `Sovereign.Coding.Trit`
- **行数**: 91（代码 44 / 注释 28）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coding.Trit
  - 编码代数：三进制基底 Fin 3
  - 宪法定义：
  - Trit 不是整数的子集，而是独立的类型 Fin 3。
  - 这从类型论层面杜绝了将其误用为 {-1, 0, 1} 或 {-2, ...} 的可能性。
  - 符号对应：T₀(0) 吸收, T₁(1) 平衡, T₂(2) 表达。
- **导入 (6)**: `Data.Fin`, `Data.Nat`, `Data.Nat.Base`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (10)**: `Trit`, `T₀`, `T₁`, `T₂`, `_⊕_`, `_⊗_`, `inv`, `_⊖_`, `identityR`, `cancel`
- **质量**: `refl`×8；无 postulate / 无 hole
