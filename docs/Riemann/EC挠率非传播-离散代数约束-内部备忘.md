# EC 挠率非传播 · F₉ 离散代数约束 —— 内部备忘（M6-B5 延伸 · 未写 Agda 前的逻辑梳理）

> 来源：2026-11-25 Deep Research 模板讨论「方向 4 + 第二步内部备忘」。
> 性质：**自然语言 + 伪代码逻辑梳理**，不写 Agda（待 Gemini 方向 1 数学排雷报告对账后再定）。
> 每条断言标注：模块锚点 / oracle 表 / [物理假说·未验证] / [构造性缺席]。

## 一、EC 机制的代数化重述（连续侧锚点）

Einstein–Cartan 的挠率场方程是**代数方程**：T^μνλ = κ·S^μνλ（挠率 = κ×自旋密度）——
不含 ∂T/∂t 项 → **挠率无独立传播子**，只存在于物质内部、由局部源代数地决定。
对照：Maxwell/GR 的场方程含时间导数（动力学 → 波传播）。
这即讨论所谓「挠率不向真空自由传播」（contact interaction）。
[未形式化·经典对照: EC 标准教材层]

## 二、离散翻译：「不传播」= 三条可形式化约束

| # | 约束 | 连续侧含义 | F₉ 载体对应 | 状态 |
|---|---|---|---|---|
| **C1** | 点级代数决定性 | T 由**同点**自旋源代数决定，无独立自由度 | `SpinTorsionCoupling.coupling`: torsionValue ≡ spinImbalance cfg（**定义性**, refl） | ✅ 已形式化 |
| **C2** | 挠率-点群解耦 | 挠率不是点/度规的属性，不随几何算子搬运 | 挠率定义在 **SpinConfig** 上；点群算子（addE/sig/negp/mul2-4，共 1348+ 格）**无一携带挠率值** | ✅ **[构造性缺席]**（grep 实证: RH 31 模块零传播算子） |
| **C3** | 传输平坦/闭合归零 | 传输不产生挠率差；物质外挠率为零 | `TeleparallelA4.plaquette-collapse`（环绕六步净位移 ≡ v，零曲率 ✓）+ `coupling-closed`（闭合恒 +0）+ `CartanTorsion.torsionClosedAfterZhonglv`（+11 → +0） | ✅ 已形式化 |

## 三、现有结构 → 约束映射（哪些能定义/承载约束）

| 结构 | 承载的约束 | 锚点 |
|---|---|---|
| `SpinTorsionCoupling.coupling`（refl） | C1 | Synthesis/Geometry/SpinTorsionCoupling |
| `SpinTorsionCoupling.coupling-closed` | C3（闭合归零） | 同上 |
| `TeleparallelA4.plaquette-collapse` | C3（传输平坦, 零曲率） | Synthesis/Geometry/TeleparallelA4 |
| `CartanTorsion.torsionClosedAfterZhonglv`（refl: +11 → +0） | C3（仲吕实例） | Synthesis/Geometry/CartanTorsion |
| `GroupCls*.addE/sig/negp/mul2-4`（表驱动） | **C2 的反证基座**: 点群算子全集穷举, 无一含挠率 | Application/Problems/RH/GroupCls0..7 |
| `F9MultC8.c8-sig`（σ = k↦3k） | C2（σ 相位作用不触碰挠率） | 同上 |
| ⚠ `CartanTorsion.transportDiffEq`/`transportRule` | **风险点**: 演化规则占位 + `tritState`/`updateTrit` postulate——若未来补全为动力学演化且挠率进入状态, C2 可能被破坏 → 须显式审查 | CartanTorsion:310-319（登记） |
| ⚠ `CartanTorsion.cartanLegal` | 显式公理（B 轨道）—— C1-C3 链不含它 ✓ | PhysicalAssumptions:76（登记） |

## 四、「超光速传播主张」的离散翻译与裁判结论草案

**主张翻译**：「挠场可超光速长程传播」在离散载体上要求存在一个**传播算子**
`prop : SpinConfig → Pt → SpinConfig`（把挠率值从源点搬运/辐射到不同点），
或挠率进入点群动力学（演化方程含挠率项）。

**裁判结论草案**：在现有 F₉ 载体上——
1. C1（定义性决定）+ C2（算子缺席）+ C3（传输平坦/闭合归零）三约束齐备 ⟹
   **满足局部代数约束的自旋源诱导的挠率必然是「点级代数决定的非传播缺陷」**；
2. 「长程传播」所需的结构（prop 算子/挠率动力学项）**在载体中缺席**——
   [构造性缺席] 声明：缺席 ≠ 物理不存在，但任何补装都属于**新增公理**，
   必须以 [物理假说·未验证] 登记并显式审查（禁止隐式混入）；
3. **边界明示**：这是 F₉ 离散格点上的**代数层排除**（现有载体内无对应结构），
   不是对连续物理的证伪——连续侧结论等方向 1 数学排雷报告对账。

## 五、待外部输入与后续

1. **等用户侧 Gemini 方向 1 报告**（Rubakov/Kruglyakov 于 УФН 的 Shipov 方程数学批评）：
   到位后逐条对照 `TeleparallelA4`/`CartanTorsion` 的公理表做一致性审计
   （批评点若为「协变导数与外微分混用/Bianchi 违反」，离散侧检查 plaquette-collapse
   与 Cartan 方程 records 是否有同构陷阱）。
2. **若审计通过** → 方向 4 深化（把 C1-C3 升级为 Agda 引理：C2 的「无传播算子」
   可写为对 GroupCls 算子集的**逐算子性质引理**——量级 ≈ 每算子 1-2 条, 可行）。
3. **若审计发现同构陷阱** → TeleparallelA4/CartanTorsion 优先修补, 方向 4 暂停。

## 六、外部输入到位：Deep Research 报告对账 + M10 规范伪影定理（2026-11-25）

**Gemini Deep Research 方向 1+4 报告已到位**（用户提供全文）——与库内载体交叉核对结果：

### 核对一致项（oracle `gauge` 模式 + 既有表）
| 报告 §五 数据 | 本仓库承载 | 核对 |
|---|---|---|
| F₉\* ≅ C₈ 幂表（g = 1+i, 8 幂） | `F9MultC8`（oracle c8 模式） | **逐元素一致 ✓** |
| Norm: 偶幂 ↦ 1 / 奇幂 ↦ 2 | `c8-norm-*` 8 条 | 一致 ✓ |
| SO(2,F₃) = {偶幂} ≅ C₄ | （新数据点——M8 的 C₄ 子群） | ✓ |
| 纯规范联络零曲率 R ≡ 单位元 | `TeleparallelA4.plaquette-collapse`（零曲率定理） | 同构 ✓ |
| EC 挠率代数锁定（无动能项 → 真空恒零） | `SpinTorsionCoupling.coupling` + 内部备忘 C1 | 同构 ✓ |

### ★ 新定理候选 M10：规范伪影定理（本回合 oracle 全枚举核对 ✓）
4×4 周期 F₉ 格点上（Deep Research §五 离散模型）：
- **固定标架（Shipov 式拒绝同步变换）**：14/16 格点出现非零「挠率」——伪影出现；
- **联合局域规范变换** (e,U) → (h·e, h·U·h⁻¹)：非零挠率格点 **0/16 恒零**。
⟹ **「挠场」是规范伪影**：Shipov 把纯规范联络的标架非协变余项实体化为物理场
（报告 §一 审计表第 2 行：其本人承认 T_ijk 在 O(3,1) 下非张量变换）。
离散格点上该机制**完全可枚举、可形式化**——M10·Agda 候选
（表驱动：h 场 + U 表 + T 公式，量级 ≈ 16 格 × 3 件 ≈ 50 条，可行）。

### 报告审计表 → 库内/待办映射（方向 1 数学排雷结论）
| Shipov 错误（报告 §一） | 离散侧对应裁决 |
|---|---|
| R+P=0 是几何恒等式非动力方程（R/P 非独立） | **已裁**： plaquette-collapse 即「恒等式侧」；「动力方程侧」在载体内缺席（C2 构造性缺席）✓ |
| T_ijk 非张量（O(3,1) 下）+ 惯性余项实体化为挠场 | **M10 规范伪影定理正是其离散形式化**（本回合 oracle ✓；Agda 化待做） |
| 4D 陀螺仪违反自身零曲率前提（R₁₀+P₁₀ ≠ 0） | 离散侧判据 = plaquette-collapse 对该配置**失败**即复现同一破缺 [待枚举构造反例配置] |
| 挠场-电子耦合 10⁻²–10⁻³ 被 g-2/天体物理排除 | 物理Experiment 层——[物理假说·未验证] 隔离不变，库内不承载 |

### 三条刚性约束（报告 §五）与内部备忘 C1-C3 的对账
报告三约束（联合规范协变 / 一阶线性无挠率动能 / 紧支集近邻）与备忘 C1（点级代数决定）/
C2（挠率-点群解耦）/ C3（传输平坦闭合归零）**逐条同构**——两套独立推导合流 ✓。
