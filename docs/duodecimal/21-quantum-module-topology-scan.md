# 量子类代码模块拓扑扫描与展示群本源对齐缺口

**日期**: 2026-09-08
**状态**: 拓扑扫描（对齐规划基础）
**视角**: 最新依赖类型论展示群本源（DuodecClock = GF3 幅度 × GF9⟨α⟩ 相位 × 归零闭合）
**范围**: 11 个量子类模块（Quantum/ + Physics/Quantum* + Algebra/Coupling/Structology 相关）

---

## 〇、审视标尺：展示群本源三合一

对齐的**真本源**应基于展示群（DuodecClock），而非投影：

```
叠加 = GF3 ⊕                        （幅度层，本源）
纠缠 = GF9 galoisConjugate 共轭对 (α, σα)   （相位域共轭，本源）
相位 = GF9 ⟨α⟩ mulAlpha 旋转 / mixedOp 联合走钟   （旋转群，本源）
```

本源相位载体（代码已确认）：
- `dayan-φ (t,a) = (t, mulAlpha a1 a)`（⟨α⟩ 旋转生成元，DayanCore）
- `mixedOp^12 p ≡ p`（本源走钟一圈，DuodecClock）

⚠️ **投影红线**：Duodec / Z/12 的 +1 是加法投影（Duodecimal.agda:6 自述"投影层"），
不是本源相位。用 Duodec+1 当相位 = 投影当本源（QuantumCorrespondence 犯此错）。

---

## 一、11 个量子类模块总览

| 模块 | 代数面 |
|------|--------|
| Quantum/Entanglement | 纯 Trit (GF3) |
| Quantum/ZeroPowerQuantum | GF9 + T6 + TorusGeometry |
| Algebra/QuantumCorrespondence | GF3 + GF9 + Duodec(Z/12) |
| Coupling/Entanglement | 主权状态机 (LCM) |
| Coupling/SpinTwistor | GF3 + 复扭量 |
| Physics/QuantumChemistry | GF9 + T6 |
| Physics/QuantumErrorCorrection | GF3比特 + GF9保护 |
| Physics/QuantumFieldAstrophysics | GF9 + NormCollapse |
| Physics/QuantumMotor | A4Group |
| Physics/WaterQuantumIntegration | GF9 + T6 + Invariants |
| Structology/QuantumBridge | (1132行, 待核) |

---

## 二、按展示群本源对齐度分三类

### 🟢 A 类：GF9 + T⁶ 链（已带 GF9 共轭相位，接近本源，未挂 DuodecClock）

| 模块 | 代数面 | 关键结构 |
|------|--------|---------|
| Quantum/ZeroPowerQuantum | GF9 + T6 + TorusGeometry | T⁶ 六维态 (729)，§7 DuodecClock 12态嵌入 |
| Physics/QuantumChemistry | GF9 + T6 + TorusGeometry | "GF9 共轭对驻波"，键角 = α乘法90° |
| Physics/QuantumErrorCorrection | GF3比特 + GF9保护 | 比特 = GF3，纠错 = GF9 范数/共轭 |
| Physics/QuantumFieldAstrophysics | GF9 + NormCollapse | GF9 场 → Frobenius 驻波 → 范数坍缩 |
| Physics/WaterQuantumIntegration | GF9 + T6 + Invariants | T⁶ → GF9 场 → 范数坍缩 → 水态 |

**共同缺口**：已用 GF9（galoisConjugate/alpha），但**没有显式挂 DuodecClock 本源**
（除 ZeroPowerQuantum §7 提 12态嵌入）；相位 = GF9 α 但未系统到 ⟨α⟩mulAlpha 旋转群
+ mixedOp 联合走钟。

### 🟡 B 类：混合/独立代数（非 GF3-GF9-DC 主链）

| 模块 | 代数面 | 说明 |
|------|--------|------|
| Algebra/QuantumCorrespondence | GF3 + GF9 + Duodec(Z/12) | 三合一(叠加×纠缠×相位)但**相位用投影 Duodec+1** |
| Physics/QuantumMotor | A4Group | 转子 = 正四面体群 A₄，另一套代数 |
| Structology/QuantumBridge | 1132行 | 大模块，待核 |

### 🔴 C 类：纯 GF3 标量 / 非量子域（停在最老层次）

| 模块 | 代数面 | 问题 |
|------|--------|------|
| **Quantum/Entanglement** | **纯 Trit** | 纠缠用 GF3 Bell 表，无 GF9 共轭 —— ⊗-语义错配源头 |
| Coupling/Entanglement | 主权状态机 | 耦合域（共享 LCM 缠绕数五行同步），非量子域代数 |

---

## 三、关键发现

1. **GF9 已成量子层主流**（6 模块用 galoisConjugate/alpha/T⁶）——但**没有一个显式挂
   DuodecClock 本源**（仅 ZeroPowerQuantum §7 提嵌入）
2. **Quantum/Entanglement 是唯一纯 GF3 落后者**（⊗-语义错配已裁定）
3. **QuantumCorrespondence 的相位在投影层**（Duodec+1 非本源 mulAlpha）
   —— 它自称"已提升"但相位部分仍停在投影
4. 两个"离群"：QuantumMotor (A₄)、Coupling/Entanglement (状态机/LCM)

---

## 四、对齐缺口汇总

| 目标模块 | 现状 | 对齐动作 |
|---------|------|---------|
| **主链模块**（A类 5个） | 已 GF9 | 挂 DuodecClock 本源：相位 → ⟨α⟩mulAlpha + mixedOp 走钟 |
| **Quantum/Entanglement** | 纯 GF3 | 从纯 GF3 提到 GF9 共轭纠缠（最高优先） |
| **QuantumCorrespondence** | 相位=Duodec+1 | 相位改本源 mulAlpha（投影→本源） |

**对齐原则**（防再犯）：
- 纠缠 = GF9 Frobenius 共轭对 (α, σα)，不可分离
- 相位 = GF9⟨α⟩ 旋转（本源），**不用** Duodec/Z12 加法投影
- 叠加 = GF3 ⊕（本源幅度）

---

## 五、关联锚点

- 展示群本源: DuodecClock.agda / 12-rigorous-type-theory.md §六
- 相位不可约元公理: memory/crt-wave-physics-not-modular-arithmetic.md
- 本源元理论定位: 20-dc-type-theory-positioning.md
- 已提升样板（纠缠部分）: QuantumCorrespondence.agda §2 (GF9 σ 共轭)
- 量子几何公理: Quantum/Foundation.agda 公理2(叠加=T⁶平移) 公理3(纠缠=GF9共轭)

---

## 六、对齐专项进度 (2026-09-08)

### 已完成对齐

| 提交 | 模块 | 对齐内容 |
|------|------|---------|
| d7cf316 | Quantum/Entanglement | §8 GF9 本源纠缠层 (Qutrit9=GF9×GF9, 共轭对(α,σα), 相位⟨α⟩) |
| 00a86b4 | QuantumCorrespondence | 相位本源化: Duodec+1(Z/12投影) → AlphaPower mulAlpha(⟨α⟩旋转群) |
| 0a75b3c | Algebra/Character/FrequencyMode | 频率模态接口: DC 特征谱作频率地基 |
| c2ea868 | FrequencyMode | 模态正交 + 显式 12 模态 (mode-00..mode-23) |
| cd35907 | Structology/StandingWave | 三代驻波 = DC 幅度频率模态 (相位静止 a0) |
| 4b9e909 | Physics/ChiralInterference | §6 GF9 手征层: CW/CCW → GF9 共轭对(α,σα), σ 非平凡阶2 |
| 49985d6 | Quantum/Foundation | 公理3 纠缠=GF9 共轭实现落地 (注释→实际定义) |
| 66e03c8 | Coupling/SpinTwistor | 对齐声明: 扭量复共轭=GF9 σ (DiscreteComplex本质=GF9) |
| 8db5985 | Coupling/SpinTwistor | §3b GF9扭量层: TwistorPoint9=GF9³ 标准GF9, 共轭=galoisConjugate, 无连续统 |
| e879476 | Coupling/CartanTorsion | 对齐声明: DiscreteComplex 乘法/共轭 = GF9 标准结构 (保类型) |
| 63e250e | Algebra/AlgebraicPoleUnified | L0 本源化: Duodec(Z/12投影) → DuodecPoint(mixedOp加乘联合); 截面 proj₁; 头注同步 |

### 🔴 待修复: 声子谱桥接 (暂缓, 2026-09-08)

**目标**: SevenStages/Nayin 的"144×奇次谐波" ↔ FrequencyMode (DC 模态)

**障碍** (桥接未做, 记录待后续):
- SevenStages `diqiHarmonic n = 144 × (2n+1)` (144,432,720... Hz) 是 **ℕ 物理频率层**
- FrequencyMode 是 **DC 群论频率层** (12 模态 = 振幅频 F₃ × 相位频 C₄)
- 两者量纲/层次不同, **无现成数学桥**
- SevenStages.agda:121 红线: 基频 144 与极向缠绕 144 相等但**禁止称"144 的投影"**
- 144 与 DC 的 12 无已声明的结构关系 (144=12² 关联被红线排除)
- **不可臆造映射** (硬桥会违背红线 + 物理未定)

**待后续**: 需澄清声子基频 144 与 DC 频率模态的真实物理关系 (代数模态层 vs 物理 Hz 层经标定桥? 还是独立两层) 后再修

### 🔴 概念张力记录: CartanTorsion (2026-09-08 分析, 待修)

**结构**: 嘉当挠场 = T⁶ 纤维丛 (底流形 S²/A₄ 12胞腔, 联络 Fin12→Fin12, 复振幅 Sqrt3)

**概念张力** (vs 展示群 DC):
- 用 **A₄ 结构群** (12阶, 非交换) vs DC (交换 3×4 加乘联合) — 代数结构不同
- 复振幅用 **Sqrt3 (√3 能隙域)** vs GF9⟨α⟩ (相位域) — 相位载体未对齐
- 底流形/联络用了 12 的数量 (=DC 载体数) 但代数结构是 A₄ 非 DC

**两种定位待定** (未裁决):
1. A₄+Sqrt3 是嘉当挠场的独立正确选择 (非交换结构群 + 能隙域), 保留仅声明区别
2. CartanTorsion 应重构到 DC 结构群 + GF9⟨α⟩ (大改)

**SpinTwistor**: 已实质对齐 (8db5985) — §3b 标准 GF9 扭量层 TwistorPoint9=GF9³, 无连续统

### 📋 代数链对齐调查 (2026-09-08)

**已对齐本源 (DuodecPoint/GF9⟨α⟩)**: DuodecClock/DCGroup/Day anCore/DuodecClockProperties/GF9/
GF9AlgebraicChain/AlgebraicPoleUnified(L0已本源化)/GF9Semiring/NormExactSequence/CyclicGroupStructure

**未对齐候选** (待评估是否需本源化):
| 模块 | 载体 | 状况 |
|------|------|------|
| VortexRoot/Connections/Tower/Differential (4) | **Duodec(Z/12 投影)** | 自述"以 Duodecial 为载体" — Z12 涡旋环层, 未本源化 |
| GF27/GF243 | 独立 GF(3³)/GF(3⁵) | 独立扩张未接 GF9 链 |
| GF81/GF729 | import GF9 + 独立 | 部分接 |

**待澄清**: Vortex 族的 Z/12 涡旋环是独立层(涡旋语义在投影环) 还是应按 AlgebraicPole L0 模式本源化到 DuodecPoint; GF27+ 独立扩张是否需统一到 GF9 链

### 📋 GF27/GF243 判定 (2026-09-08): 不需统一到 GF9 链

**数学事实**: 域扩张塔 GF(3^a)⊂GF(3^b) ⟺ a|b (GF243 头注/GF81 头注)
- GF9 = GF(3²) (2 次扩张, α²=-1 相位域)
- GF27 = GF(3³) (3 次扩张, α³=α+2)
- GF243 = GF(3⁵) (5 次扩张, x⁵≡x+2)
- **2∤3, 2∤5** → GF27/GF243 不含 GF9 为子域, 与 GF9 是**平行分支**

**判定**: GF27/GF243 数学上独立于 GF9 链 (展示群 GF9⟨α⟩ 是 2 次扩张的相位域;
3/5 次扩张是另分支). 不需统一. 各含 GF3 为公共子域, 高层收敛于 GF(3^lcm).
GF729 只形式化加法群 (乘法太复杂).

### 📋 GF27 Frobenius 补全 (2026-09-08, 完成至 GF81 同级)

**展示群特性对齐**: GF(3^n) 扩张自动有 Frobenius 自同构 (特征3 x↦x³):
- ✅ frobenius 显式定义 (5a11f3e): σ(a,b,c)=((a⊕neg b)⊕c, b⊕c, c)
- ✅ frobenius-add 保加法 (negate-⊕ + swap-middle)
- ✅ frobenius³-id (27 case, 阶 3) + frobenius-injective
- ✅ frobenius-alpha (bdc7fb1): σ(α)=α³ 生成元像 (与 GF81 同级)
- 🔴 frobenius-mul: 留待 — 项目 Frobenius 均未证乘法同态 (GF9 2分量特例除外;
  GF81 4分量也未证). σ 的保加+阶3+单射+生成元像已确立域自同构地位

### 📋 Frobenius-多项式桥接统一 (2026-09-08): GF9/27/81

**Frobenius 由约化多项式驱动** (每扩张加 frobenius-alpha-is-cube, σ(α)=α³):
| 扩张 | 约化多项式 | σ(α) | Galois 共轭 | σ 阶 |
|------|-----------|------|------------|------|
| GF9=GF(3²) | x²+1 | α³=-α | {α,-α} | 2 |
| GF27=GF(3³) | x³+2x+1 | α³=α+2 | {α,α³,α⁹} | 3 |
| GF81=GF(3⁴) | x⁴+x+2 | α³ | {α,α³,α⁹,α²⁷} | 4 |

**规律**: σ 阶 = 扩张次数 [GF(3ⁿ):GF(3)] = 约化多项式次数 n;
σ 遍历 α 的全部 Galois 共轭 (frobenius-alpha-is-cube 提交: GF9 982c1aa/GF27 6d45477/GF81 589f86f)

### 📋 GF243 评估 (2026-09-08): 仅加法层工具, 不强补乘法

- GF243 = GF(3⁵) = Vec Trit 5, 391 行, **仅加法群** (加法/取反/特征3/GF3嵌入)
- 头注声称 Galois≅C₅ Frobenius x↦x³ 生成但未实现 (需乘法, 无乘法)
- 用途: PackedByte 存储桥接 (Trit 5 向量存储), 非展示群域数学载体
- **评估**: 补 5 分量域乘法+约化+公理 ~300-500 行, 但 GF243 本质是加法向量空间
  工具非完整域; 不值得为 Frobenius 补全乘法. 保持加法层, 不强补.
- 对比: GF27 补 Frobenius 合理因它已有完整域 (乘法/分配律/乘法群)

### 📋 GF243/GF729 强补更新 (2026-09-08)

**GF243 强补 (完成 132c2cd)**: 乘法定义 + Frobenius σ
- poly-mul(5×5卷积) + reduce9(约化 x⁵=x+2) + _*gf243_ 定义式 (验证 α²=x², α⁵=α+2)
- Frobenius σ 显式坐标 (Python 验证 =x³): σ(a₀..a₄)=(a₀⊕neg a₃, neg a₂⊕a₃, a₂⊕a₄, a₁⊕a₄, neg a₃⊕a₄)
- frobenius-alpha: σ(α)=α³
- 乘法公理(单位/交换/分配) + σ 保加/阶5 + frobenius-is-cube: **另立后续** (数百行机械证明, 需本地 ≡-Reasoning)
- **判定**: 乘法定义+Frobenius σ 已满足当前对齐 (展示群特性 σ 就位)

### 📋 GF243 乘法公理 + frobenius-is-cube 全域收官 (2026-09-08)

**GF243 乘法公理 (ac050c5, 0 postulate, +414 行)**
- 基础设施: 本地 ≡-Reasoning / negate-⊕ / 左嵌套和工具 (congL3-5/revL3-5/mergeL3-5) / cong-Vec5/cong-Vec9
- poly-mul-comm (⊗-comm 逐项 + revL) → *gf243-comm = cong reduce9
- poly-mul-distribˡ (⊗-distrib + mergeL) + reduce9-additive (negate-⊕ + ⊕-swap-middle) → *gf243-distribˡ
- *gf243-identityˡ: 逐分量符号化简 (T₀⊗ 项 ⊗-zero 归零 + dropZ 链剥 T₀ 缀), 右单位 = 交换律 + 左单位
- *gf243-distribʳ 由左分配 + 交换律

**frobenius-is-cube 全域真定理 (cb4cb72 GF27/81, d0abeb9 GF243)**
- GF9 f4f6940: 符号证明 frobenius-is-cube x = trans (frobenius-cube x) (*gf9-assoc x x x)
- GF27 27 case / GF81 81 case / GF243 243 case 穷举全 refl (σ(x)=x³ 与 reduce9∘poly-mul 立方逐元素一致)
- 代数链 GF(3²)/GF(3³)/GF(3⁴)/GF(3⁵) 全部覆盖, 下游 TowerConnection 编译绿
- 0 postulate: 四个文件全部无 postulate

**GF729 域乘法不强补** (与 GF243 评估一致): 无不可约多项式 (line 550 "需选择 6 次不可约多项式, 本模块不处理"),
纯 T⁶ 格点加法工具 (非 GF(3⁶) 域载体, 系数 Fin3 非 Trit), **域乘法定义不补**

### 📋 GF729 展示群相位对齐 — 群论修正 (2026-09-08)

**⚠️ 修正记录**: 初版 (c449e38) 把相位写成"逐坐标乘 α"的坐标计算, 且误改上游 GF9.agda
加 fixity。用户指正: **相位旋转是 GF(9)× ≅ C₈ 的 4 阶循环子群 ⟨α⟩, 这是群论**;
且下游无权改上游基础定义。已撤销 (dd377a2) 并群论重写 (088ce6e)。

**正确的群论定位** (`PhaseSubgroup.agda`, 0 postulate, 不改上游):
- GF(9)× ≅ C₈ 循环 (gen=1+α, `gen-generates-all` + `gen-order-8` 阶恰 8)
- **⟨α⟩ 是 C₈ 的 4 阶循环子群**: α=gen⁶ (`gen-pow-6`), ⟨α⟩={gen⁰,gen²,gen⁴,gen⁶}
- **阶恰为 4**: α⁴=1 (上界) + α²≠1 + α≠1 (下界, 排除 1/2 阶)
- **4 | 8** (拉格朗日) + 4 阶元存在 (双侧阶证明)
- **相位旋转 = C₄ 循环作用**: rot x = x·α, 4-循环 orbit s1↦sα↦s2↦s2α↦s1, rot⁴=id, rot²=取负(180°)
- **AlphaPower ≅ ⟨α⟩**: `alphaPowerToGF9` 保乘 (`mulAlpha-hom`), 抽象 C₄ 阶恰 4

**GF729Field (GF(9) 三次扩张域)** — 独立模块, 不改 GF729 的 T⁶ 工具定位:
- 域乘法 *F (卷积+约化 t³=2t+α), 0 postulate
- 构造性证明 (符号, 非穷举): char3 / *F-distribˡ/ʳ / frobenius-add / scalar-extractˡ
- GF9 环同态 embed-9 (保加保乘)

**构造性进展**:
- ✅ `*F-assoc` 已闭合 (71afe27): 三级嵌套线性扩展 (Linear/expand3/linear-ext3),
  27 个基三元组 + assoc-Z→assoc-Y→assoc, 非穷举。
- ✅ `scalar-extractˡ` (6d09f91)、`*F-distribˡ/ʳ`、`char3`、`frobenius-add` (08d337a)。

**技术债 (诚实记录, 未完成)**:
- `GF729Field.frobenius-is-cube` 仍是 **729 条 refl 穷举** (待构造化)。
- 构造化路径已明确: σ 与立方映射均为 `galoisConjugate`-半线性
  (`semilinear-ext` 已验证可用), 两者在基 {1,t,t²} 上相等 (3 个 refl 已确认);
  还缺 `sigma-scalar` (σ 保标量) 与 `cube-add` (Freshman's dream)。
- `GF27`(27)/`GF81`(81)/`GF243`(243) 的 `frobenius-is-cube` 同样是 refl 穷举;
  GF27/81/243 均缺 `frobenius-mul` (保乘)。

### 📋 ParityViolation 对齐评估 (2026-09-08, 低优先不强制)

- 宇称破缺 = 环向缠绕深度 a 驱动 (a≥3), 手性对偶只是分类标签
- WuXingAmplitude 是**抽象三态标签** (AmpGenerate/Overcome/Overcome2), ω 仅在注释
- 无 GF9 共轭运算, 无 Zω 值 — 代码本身离散, 连续统记号只在注释
- **评估**: 硬引入 GF9 改变抽象层次且无明确物理增益, 不强改; 注释层可标注
  其 ω 振幅与三次单位根/DC 幅度频率同族
