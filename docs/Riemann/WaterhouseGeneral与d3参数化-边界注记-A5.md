# WaterhouseGeneral（∀n）与 d=3 参数化：边界注记（M5 · A5.2 + A5.3）

> M5 立项不排期件的本体交付：**边界即交付**。本注记划定「已形式化」与「未形式化」的
> 精确分界，供后续会话直接续作；每条断言遵守散文断言规则（内核名或 [未形式化·经典对照]）。

## 一、A5.2 WaterhouseGeneral（∀n）的 ⑦B 边界

**已形式化（q=3 具体层, 全部 exit=0）**：
- 迹值层：`TraceTableF3`（迹集恰 7 值 + val-inj 49 案）；
- 超奇异性：`SupersingularF3`（IsSup 定义选择 + sup-trace 全称）；
- 判据 iff：`WaterhouseF3.water-iff`（IsSup ↔ t ∈ {−3,0,+3}，q=p 刻画在 q=3 的全称形式）；
- 存在性：`water-surj`（每迹值有实现曲线）。

**未形式化（∀n 一般层的缺口, 即 ⑦B 边界之外）**：
1. **「每值恰一个同构类」**——Waterhouse 细分类的核心（q=p 时值与 Fₚ-同构类一一对应）。
   需要 F₃-同构分类定理（库内 0 命中）`[未形式化·经典对照: Waterhouse 1968, Thm 4.1]`。
2. **p∣t ⇔ 超奇异的深层证明**——当前是定义选择（SupersingularF3 头注明示）；
   深层需 Deuring 正常元（库内 0 命中，见九项清单第 8 项）。
3. **q = p^r（r≥2）的一般刻画**——超奇异 ⟺ a_p ≡ 0 (mod p) 的 r≥2 推广
   （A4.2 的 Weil 递推是数值侧的 r=2 实例，非判据本身）`[未形式化·经典对照]`。

**续作动作回执（2026-11-25）**：
- ① ✅ `RH/CurveIsoF3.agda`（exit=0, 778 行）——18 条非奇异 → **恰 8 个 x-平移轨道**
  （cls0..cls7, 代表元 c010/c101/c102/c201/c202/c020/c021/c022; 5×size-3 + 3×size-1）。
  四件齐：覆盖（cls-of 18 分派, mkC 模式）+ 非空（rep-of/ns-rep 8 见证）+
  互斥（ne-cls 28 条）+ 轨道封闭（sic 54 条, ns-ds 54 条）。
  交叉核对：disc/#E 平移不变 ds/ps 162 条；类内迹一致 ct 18 条（=同构 ⟹ 同 #E 的
  分轨承载）。oracle `iso`/`emit-iso` 模式冻结（27×3 平移不变性 ✓ + 逐轨迹一致 ✓）。
  修正一处预估：8 类而非预估的「5 个」（预估把 t=0 双类 c020 与 c010-012 合并了——
  实枚举 c020（a₄=2）平移不动点自成一类）。与经典「F₃ 上恰 8 个同构类」计数一致
  [未形式化·经典对照]。
  剩余缺口：Deuring 正常元（②）—— **M6 已开工**（2026-11-25, 见下）。

## 三、M6 · Deuring/Frobenius 线（②的原子分解与执行回执, 2026-11-25）

**原子分解**：B0 oracle `frob`/`emit-frob` 模式 ｜ B1 `FrobF9.agda` 载体层 ｜
B2/B3 `FrobFix.agda` 计数定理 ｜ B4 `SupersingularDiv3.agda` 算术表述桥 ｜
B5 环论载体（本节登记, 未排期）。

**已交付（全部 exit=0, 0 postulate, 门禁 22 模块全绿）**：
- **B0**：σ = 共轭 (a,b) ↦ (a,−b) 全枚举——σ 封闭/σ²=id/总点数=pe9 ✓；
  **Fix(σ) = #E(F₃) 18/18 ✓**（口径含无穷远点——首跑漏 ∞ 被 B0 自交叉核对拦截,
  修正后一致, 先算后验纪律的活例）；`#E(F₉) = Fix + 2·pairs` 全 ✓。
  组合不变量 (Fix, pairs) 与 CurveIsoF3 的 8 类逐类一致。
  两个超奇异极端：c021（t=−3）σ = id（7 点全固定, pairs=0）；
  c022（t=+3）仅 ∞ 固定（Fix=1, 3 对 2-cycles）。
- **B1 `FrobF9`**：f9conj（σ）+ f9conj2（σ²=id）+ 环自同（neg-⊕/⊗-distr 27 格 +
  f9add/f9mul-conj）+ t2f9-conj（系数 σ-不动）+ rhs9-conj（σ-等变, conj-add3/4
  结构引理）+ **frob-closed**（y²=rhs(x) ⟹ (σy)²=rhs(σx) —— σ 置换载体）。
- **B2/B3 `FrobFix`**：嵌入判据（虚部 ≡ T₀；conj-fix-im 点级定理, 免分派）+
  **fix-e3：Fix(σ) = #E(F₃) 18 条**（口径含 ∞）+ **split 18 条：#E(F₉) = Fix + 2·pairs**
  （pairs 常量 oracle emit-frob 冻结）。
- **B4 `SupersingularDiv3`**：Div3V 迹值整除层 + div3V-cls（⟺ {trM3,trZ,trP3}）+
  **div3V-sup / sup-div3V 双向**（water-bwd / sup-trace + val-inj）+
  div3V-supΣ / sup-div3VΣ（Σ 包装, trace-in-Tr3 全覆盖）——
  **「p∣t」算术表述 ⟺ 迹集表述双向可证**：「定义选择」升级为「两等价表述互推」。

**B5 · 真正的 Deuring 正常元（登记未排期）**：
- ρ² = −3 于 End(E) 需要 E(F₉) 群律（加法公式 + 群公理）+ σ 的群自同性
  （π(P+Q) = π(P)+π(Q)）——库内 0 命中; σ 目前是点集置换（B1 载体）。
- 有了群律后的续作路径：σ 群自同 → π 特征多项式 x²−tx+3 于 End →
  p∣t ⟹ π 純不可分/幂零 ⟹ E[3] 破灭（Deuring）。
- 环论载体的最小起步：E(F₉) 点集上的加法公式逐类枚举（每曲线 ≤16 点,
  oracle 可全枚举冻结运算表——同 pe9 范式）, 但证明量级 ≫ M6 全部, 需独立排期。

## 四、B5 群律线开工回执（2026-11-25, G0 完成）

**G0 ✅ oracle `group` 模式**（char 3 一般 Weierstrass 加法公式, 全枚举核对）：
- 群公理（单位/逆/交换/结合——**全点**三重循环）18 曲线全部通过 ✓；
- **σ 群自同** σ(P+Q) = σP + σQ 全对通过 ✓（群律与 Frobenius 载体的桥）；
- **特征方程点级 [4]P = [t]·σ(P) 全点通过** ✓（π 满足 x²−tx+3=0 的点级承载;
  c010 等 t=0 类: 16 点群 2⁴ ⟹ 全 2-挠 ⟹ [4]P=0 ✓; c021: −3 ≡ 4 mod 7 自动 ✓）。
- 过程三坑（oracle 自核对拦截）：F₉ 求负 ≠ 共轭（全分量 vs 仅 α 分量）；
  椭圆求负 x 不变；P=−Q 判据是 yP+yQ=0（yP−yQ=0 是 P=Q 判据）。
- **G1 量级冻结**：8 类代表元点数 16/12/15/15/12/16/7/7 → 加法表合计 **1348 格**。
- 试点建议：cls6（c021, 7 点, 49 格）最小超奇异类先行范式验证。
- **G1 ✅ 表驱动群模块 8 个全部落地**（2026-11-25）：`GroupCls0..7.agda`（243–909 行/个,
  全部 exit=0, 0 postulate）——`addE` 1348 格 + `sig-hom` 1348 条（**σ 群自同 Agda 承载**）+
  `commE` 1348 + 单位/逆元 + **`charEq`**（特征方程点级 [4]P=[t]·σP, per-class mulT 形态）
  + 试点 `GroupCls6` 另含 **`assocE` 343 条**（结合律全量; 其余 7 类 oracle 侧已核,
  Agda 未收录——量级取舍, 排期外可机械补）。
  过程新增实测：**nightly 坑 #6** —— 表驱动函数的 `∀ p → addE p ptInf ≡ p` 类∀命题
  在抽象 p 上卡死（归约需首参构造子/或全部具体子句化）；乘法字面量先行同款
  （xshift 范式）。`mul4` 曾 typo 成 `mul3` 被 charEq pt1 的 pt6≠pt5 当场拦截。
- 待办：G2/G3 已随 G1 一并落地（sig-hom/charEq 即 G2/G3 的 Agda 承载）——
  **B5 线至此闭环**。剩余「Deuring ρ²=−3 于 End(E)」的**环论层**（π 特征多项式于
  End）需要群律公式层（非表驱动）+ 排期, 见 §三 B5。

## 五、M7 · E[3] 破灭线回执（2026-11-25, 代数侧表驱动承载）

**「超奇异 ⟺ E[3] 破灭」的表驱动形式化落地**（`E3Tor.agda`, exit=0）:
- **超奇异 4 类**（cls0/5/6/7, t ∈ {0,±3}）: `e3-triv` —— mul3 p ≡ ptInf ⟹ p ≡ ptInf
  （3-挠破灭; 16/16/7/7 条, 非无穷点假设为空 () 拦截）
- **普通 4 类**（cls1..4, t ∈ {±1,±2}）: 每类非平凡 3-挠恰 C₃（∞+2 见证;
  群阶 12/15 含 3 因子）——`e3w` 见证 + `e3w-ne`/`e3w-tor`
- `notsup-c1XX/c2XX`: ¬ IsSup（sup-div3V + Div3V=⊥ 退化）
- ⟹ 与 B4 合流: 超奇异判据三表述（迹集式 water-iff × 整除式 div3V ×
  **E[3] 破灭式本件**）两两等价（逐类）——**Deuring 代数侧判据的表驱动完整承载**
- 过程: 首版 mul3 从 P 起加误为 [4]P, 被「超奇异 ⟺ 破灭」判据交叉核对当场拦截
  （先算后验活例; 修正为 ∞ 起加）
- 边界: F₉ **有理** 3-挠破灭; 完整 E[3](F̄₃)=0 需代闭点集（B5 环论层同源, 未排期）
- nightly 坑 #5 新增（emit-iso 头注与 M1-M4 二分记录）：分派子句块（∀ 函数 + 多子句）
  前悬置其他已声明未定义签名会污染子句 refl 检查——本件全件改独立具名引理形态，
  唯 cls-of 保持函数形态（签名与子句零间隔）。

## 二、A5.3 d=3 参数化边界（ℤ[√−d] 类数问题）

**本仓库的实际载体**：范数方程 t² + 3s² = 4·3ⁿ 是 ℚ(√−3) 的范数形
（ProjectionMismatch 注记 §四；d=3）。**已形式化**：
- `NormClassify.classify`：**∀n** 全称解分类（v2 有限值形式, 两步归纳 + mod-3 递降）；
- `NoNormT0General.t0-odd`：t=0 谱系唯一性；
- `Witness.witness-sat`：正部见证的 ∀n 方程。

**d=3 的特殊性（为何本线可完全形式化）**：ℤ[√−3]（序, 判别式 −12）与 ℤ[ω]（极大序,
判别式 −3）的单位群秩/类数——**h(−3) = 1**（类数一），故范数形枚举无类数阻碍
`[未形式化·经典对照: 类数一的虚二次域共九个, Heegner/Stark 定理]`。
本线所有已证命题均不引用类数——它们由全枚举 + 归纳直接承载。

**d ≠ 3 的一般化边界（为何不在本线）**：类数 h(−d) > 1 时范数方程的解集不再由
有限值形式冻结（需理想类群承载），v2 冻结陈述的「解集 = 3·解集(n−2)」结构失效
`[未验证·路线推测：失效方式未枚举验证；核实动作 = 对 d=1（ℤ[i], h=1 仍可枚举）
与 d=7（h=1）跑同款 oracle 枚举，观察解集结构是否仍为 3 倍递降]`。

**续作动作**（排期时）：① d=1 线（ℤ[i], 对应 GF(p²)=GF(9) 的另一载体）同款 oracle + classify；
② d=7/11/19/… 类数一线（需先形式化「类数一」的枚举判据本身）。

## 六、B5 延伸 · A₄ 绝对平行线（Shipov 数学骨架, 2026-11-25 G0 试点完成）

**策略定案**（承讨论「不预设立场」）：俄系挠场理论 = 合法数学骨架（A₄ 绝对平行几何,
可形式化）+ 待检验物理诠释（超光速/意识, [物理假说·未验证] 严格隔离）。

**A₄ 离散试点 ✅ `Synthesis/Geometry/TeleparallelA4.agda`**（exit=0, 0 postulate）:
- 载体：T⁶ = T6Vec 6（Vec (Fin 3) 6）, 平行传输 = `updAt`（生成元坐标步进）；
- **零曲率定理 `plaquette-collapse`**：环绕平行四边形六步（含逆 = 自身两次,
  3-挠载体）净位移 ≡ v——证明 = 两次换位（`updAt-comm`）+ 两次三次归零
  （`updAt-cubed`）, 全部复用库内已证件, 零新引理；
- **A₄ 共存定理 `a4-coexist`**：传输可交换（零曲率形态）∧ 挠率非零
  （`zhonglvTorsion` = +11 ≢ 0, 承 CartanTorsion 离散复位）——
  **零曲率与非零挠率在同一离散载体无矛盾共存**（record TeleparallelA4 inhabited）。
- 对「Shipov 形式体系数学自洽性」的批判性研究（Cartan 活动标架/微分形式不一致）：
  本件给的是**离散正面数据点**——离散 A₄ 公理化自洽且 inhabited;
  不裁决其连续统形式体系 [边界明示]。

**三层语义隔离**（执行中持续）：
| 层 | 内容 | 状态 |
|---|---|---|
| 几何挠率（联络非对称部分） | TeleparallelA4 / CartanTorsion 离散复位 | **形式化中 ✓** |
| EC 物理挠率（自旋源） | WuXing 手征（LeftHanded/RightHanded）为候选载体 | 未形式化 |
| 俄系物理主张（超光速/相干放大/意识） | —— | **[物理假说·未验证] 与数学骨架严格隔离, 不得作公理/前提** |

**G2-G4 待做**：G2 泛型 plaquette 收录进 CartanTorsion 主件（本件在 Geometry 试点独立）；
G3 挠率-自旋耦合的离散类比（手征×仲吕相位, WuXing 载体已有）；
G4 「相位相干放大」的离散类比（C₈/C₁₂ 相位累加）——每个的答案无论正反都是结构性洞察,
不对物理实在性作裁决。

## 七、G3 ✅ 挠率-自旋耦合离散类比（2026-11-25, EC 谱系）

**`Synthesis/Geometry/SpinTorsionCoupling.agda`**（exit=0, 0 postulate）——
EC「挠率的源 = 物质自旋密度」的离散形态，三层构造：

| 层 | 构件 | 内容 |
|---|---|---|
| 源场 | `SpinConfig` = List Chirality + `spinImbalance` | 手征电荷和（左 +1 / 右 −1） |
| 耦合（κ=1） | `spinTorsion cfg nz` + ★ **`coupling`** | 挠率值**定义性等于**失衡（refl 即得——EC 方程离散形态） |
| 闭合 | `spinTorsionClosed` + `coupling-closed` | 平衡配置闭合归零（镜像 CartanTorsion P0-3 修复; 不走 DiscreteTorsion——那里需要 torsionNonzero, 平衡配置给不出, 正是 P0-3 矛盾同款） |

**★ 仲吕桥 `zhonglv-spin-bridge`**：repL 11（11 个净左手的自旋配置）的挠率值
≡ + 11 ≡ `zhonglvTorsion.torsionValue`——**CartanTorsion 的「仲吕不交」+11 挠率
获得自旋源解释**（12 步闭环中 11 净左手 + 1 闭合）。
语义标注：这是 EC 耦合的**离散构造类比**（κ=1 选择性）,
不对俄系物理主张作承载（[物理假说·未验证] 隔离不变）。

G4（相位相干放大的离散类比：C₈/C₁₂ 相位累加）候选待做。

## 八、G4 ✅ 相位相干放大离散类比判据（2026-11-25, M9 收官）

**`Synthesis/Geometry/CoherentPhase.agda`**（exit=0, 0 postulate）——
「相位相干放大」的**结构性判据 = 载体自由度**（AmplificationDichotomy record,
构造实例 inhabited）:

| 载体 | 判据 | 承载 |
|---|---|---|
| **自由 ℤ（自旋失衡场）** | **线性无界** coherent-linear（repL k ≡ +k）+ **忠实** coherent-inj（失衡相等 ⟹ 步数相等, posInj 归约）——放大不失真 | SpinTorsionCoupling |
| **有限阶 C₃（T⁶ 步进）** | 三步归零 trunc3（= updAt-cubed, M6） | T6CayleyVec |
| **有限阶 C₈（F₉ 相位）** | 八步回卷 trunc8（c8pow 8 ≡ c8pow 0） | F9MultC8 |
| **有限阶 C₁₂（仲吕）** | 十二步归零（DuodecClock ZeroOblivion.jointCycle, PROVEN 登记引用） | DuodecClock |

**结构洞察（讨论定案: 正反皆价值, 不裁决物理实在性）**:
「相位相干放大」机制的离散类比存在性由载体自由度决定——
自由 ℤ 载体忠实线性放大（不失真）; 有限阶载体周期截断。
即: 放大机制的数学条件 = **载体含自由（非挠）部分**。
物理层主张维持 [物理假说·未验证] 隔离。

**M9 全线收官**: G1 群律表 8 类 + G2 σ 群自同 + G3 挠率-自旋耦合（仲吕桥）+
G4 放大二分判据 + A₄ 绝对平行试点 —— 全部 exit=0, 0 postulate。
