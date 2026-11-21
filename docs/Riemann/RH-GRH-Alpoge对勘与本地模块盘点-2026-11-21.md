# Alpöge Lean 证明对勘 · 本地自守/算术几何盘点 · Agda 环境勘查

> 2026-11-21 集中调研的汇总。三块内容：① Alpöge RH/GRH Lean 证明与我们路径的对勘结论；
> ② 本仓库自守形式与算术几何相关模块的实际现状；③ 本机 Agda 编译环境的真实状态。
> 本文是**调研快照**，不是新定理；深度技术论证见已有的
> `src/Sovereign/Arithmetic/Riemann/doc/RH-GRH-合成Frobenius与代数刚性对译.md`（366 行）。

---

## 零、结论先行

1. **Alpöge 的证明不是「在特征 0 证了 RH」，而是用巨大工程量在特征 0 里补全正特征免费给出的代数刚性**。代码证据确凿：最朴素的 Frobenius 种子在 ℚ 上被证明失败，√q 是手工注入的归一化因子。这与本项目「特征连续统病态」诊断同向。
2. **本地「自守形式 / 算术几何」模块分三种**：域塔等数据级构造是真数学；Langlands/Sheaf/Chern 等是离散类比与命名借用；Arithmetic/ 下的 BSD/Riemann 是纯规划。三者必须分开陈述，不能混为「我们已有自守几何」。
3. **本机 Agda 2.9.0 确实存在，但项目一行都编译不了**——二进制在 Downloads 且带隔离属性，标准库四个依赖一个没装。全库 22 万行从未经过类型检查。

---

## 一、Alpöge 对勘（压缩版）

### 1.1 仓库事实

- `CocoSgt/riemann-hypothesis-lean` 是 Alpöge 2026-11-20 发布物的未修改镜像，2 个 commit。
- 主定理 `src/Main.lean` 五条；`RiemannHypothesis` 用 **Mathlib 官方定义**（pin `0df444a3`），非自造陈述——这是可信度基石。
- 规模 **175,187 个 .lean / 17.4 MB**，Lean v4.33.1。静态扫描 `sorry/admit/axiom/native_decide/unsafe` 全 0，但截至调研日**无独立团队完成完整构建复核**。

### 1.2 六段功能替换链（不是提升，是补造）

代码里**没有** GF(q)→ℚ 的函子，GF(2^s) 从未作为域对象出现。所谓「有限域到无限域」是六段替换：

| 段 | 正特征免费给的 | 特征 0 里的补造 | 代码位置 |
|---|---|---|---|
| 0 | Frobenius 自同构 | 种子在 ℚ 上**被证伪** | `FrobeniusBaseCase/Statement.lean:174`、`BaseCaseFalseGeneralHolds.lean` |
| 1 | GF(2^s) 的 Frobenius 轨道 | 2-进分圆塔的**共轭类**（不是自同构），`OrdIff`/`OrdCard` 仅 `def : Prop`，未在主链用 | `Formalism/BehrendSets/Statement.lean:9-19` |
| 2 | 除子交点数非零 | Behrend 厚集（真证明） | `BehrendSets/BehrendVariance/Select.lean` |
| 3 | 除子重数 m | θ-lift 链 `chainOp w K m`，取 m≈√X | `Formalism/ThetaLiftIndependence/Statement.lean` |
| 4 | 本征值模长 √q | **√q 手工注入** `algSat n q B := B.map (fun α => q^((n-1)/2) * α)` + ℓ-adic 钉扎 | `BlochKatoSelmerVanishes.lean:74`、`FrobEig`/`DivAll`/`PhiPol` |
| 5 | — | 局部-全局拼合 + 文献级块 `OpenLiteratureStatements` | `RowSrc.lean:6`、`MainConclusion.lean:7-11` |
| 6 | — | 收尾只用函数方程 + Gamma 因子，**不用 Landau 下界** | `Formalism/GammaFactorNonvanishing/CritLine.lean:29` |

### 1.3 对勘结论与措辞边界

- 两条路径**同名异物**：Lean 证 Clay 千禧题的连续 RH + 真 GRH；我们证 Weil 1948 已证定理在 GF(3^k) 上的 0-postulate 实例。
- 共享 Stepanov「重数」源头，方向相反：**他造重数跨鸿沟，我们守重数原生侧**。规模差 170 倍以上不是重点，重点是「桥」的有无。
- **必须守住的边界**：「他不是在特征 0 证明了什么」在结构层面成立，但不能按字面对外说——若构建通过且公理干净，Mathlib 官方陈述的 RH 就算形式证明成立。我们的价值主张落在原生侧的可计算性与 0-postulate，措辞用「补课程」而非「造假」。
- 用户明确立场（已长期记入 `.workbuddy/memory/MEMORY.md`）：**不得用「q=3 只有三个元素」的基数论调贬低 GF(3^k) 路线**。GF(3^k) 是完整域塔，区别于 2^k（char 3 有原生 i、C₂ Frobenius，char 2 无）。批评落点是「没建桥」（离散判据 ⇔ 连续零点线的对译字典仍是 `[ ]`），不是「基座小」。

---

## 二、本地自守形式与算术几何模块盘点

> 全库规模：`src/Sovereign` 下 **1008 个 .agda / 224,149 行**。
> 全局健康度（亲自逐条核实，纠正子代理误报）：真实顶层 `postulate` 仅 **1 文件**
> （`Synthesis/Model/DiscreteCCHM.agda` 的 `discreteGlue`/`discreteCanonicity` 2 条）；
> 真实洞 **0 个**；目标目录（Langlands/Geometry/BSD/FieldTower/RH）全部 0 postulate、0 洞。
> 搜索命中的「16 文件 postulate / 13 文件洞」是把注释里的「0 postulate」和「待证 ?」误计，已排除。

### 2.1 实做核心（可复核的数据级构造）

| 模块 | 规模 | 实际内容 |
|---|---|---|
| `Algebra/FieldTower/` | 36 件 / 13,584 行 | 全库最重。GF9(1104)/GF27(1486)/GF81(1546)/GF243 逐级扩张，`σ(x)=x³` 生成 Galois 群 |
| `Application/Problems/BSD/` | 9 件 / 637 行 | Hasse/Weil 迹递推 `t(n+1)=t₁tₙ−qtₙ₋₁`、GF(3) 点计数 `#E1-is-4` |
| `Application/Problems/RH/` | 6 件 / 1,017 行 | `t²+3s²=4q`  Eisenstein 刚性、Hasse 界、函数方程，全 refl |
| `Synthesis/Geometry/ChernConservation.agda` | — | Vec ℤ 上平移不改差分和，用 `map-++` 真证 |

### 2.2 离散类比 / 命名借用（名词到位，内容未到位）

| 模块 | 规模 | 实际情况 |
|---|---|---|
| `Application/Problems/Langlands/` | 6 件 / 359 行 | GL₂(GF(9)) 阶数公式、Burnside `1+1+4+9+9≡24`、Steinberg 值硬编码对账。**零自守表示、零 Hecke、零 L 函数、零特征标表构造**。头注自标「非 Langlands 纲领」 |
| `Application/Geometry/Sheaf.agda` | — | `Presheaf` record 仅一个字段 `ℱ-dim`；`restrict` 注释「需 Functor 范畴，~500 行」；`const-sheaf-H0=1` 是裸常数 |
| `Application/Geometry/Variety.agda` / `AlgGeom.agda` | 35 行 / — | ℙ¹=10、ℙ²=91 点数核对；GF(3) 二次多项式穷举。étale 上同调仅注释 |
| `Synthesis/Geometry/ChernClass.agda` | — | `TransportPolar`/`TransportToroidal` 均为恒等映射，`ChernNumberIsTwo = refl` 是宪法赋值——离散不变量，非上同调类 |
| `Application/Problems/Langlands/SelmerDiscrete.agda` | 95 行 | H¹(GF(3))=0 的常数对账，非真上同调 |

### 2.3 纯规划态（文档有，代码无）

- `Arithmetic/BSD/`：**0 个 .agda**，README 自标三重缺失 ❌❌❌。
- `Arithmetic/Riemann/`：仅 README + 两份诊断文档；离散 RH 主定理 / GRH / CRT 判据仍是 `[ ]`。
- 层的 restrict / 上同调：注释明示「需 ~500 行」。

### 2.4 连接关系

- `RH ← BSD.agda`（`#E1/#E2/#E6` 点计数 → Weil 迹）是**真实数据链**。
- Langlands 6 件只被目录内部 + `Master.agda`/`FinalAudit.agda` 引用；Geometry 的 Sheaf/Variety/AlgGeom **不被**任何 Problems/Arithmetic 引用。
- 结论：自守与几何侧目前是**孤立模块**，不构成通向 RH 的证明链。这与对译文档「Alpöge 用全套自守几何补特征 0 刚性，我们这套工具只有名字」的判断一致。

---

## 三、Agda 编译环境勘查

### 3.1 实际安装位置（纠正此前「本机无 agda」的误判）

全盘核实（brew / ghcup / cabal / /Applications / 整个用户目录）：

- **唯一可执行文件**：`/Users/zesheng/Downloads/agda`
- 版本 **Agda 2.9.0**（cabal `-f optimise-heavily` 编译）
- Mach-O arm64，108,278,904 字节，2026-11-04 下载
- 数据目录（XDG）：`~/.local/share/agda/2.9.0`

ghcup 只装了 GHC 9.14.1，无 agda component；brew / cabal store 均无 agda。

### 3.2 为什么 `command -v agda` 找不到、直接跑失败

1. **没进 PATH** —— 躺在 Downloads，`~/.ghcup/env` 只加 ghcup/cabal/.local 的 bin。
2. **带 Safari `com.apple.quarantine` 属性** —— 直接执行被系统 SIGKILL（exit 137），表现为「无声失败」。复制到 `/tmp` 并 `xattr -d com.apple.quarantine` 后可正常运行并输出版本号，说明二进制完好。**原文件未被改动。**

### 3.3 真正的障碍：标准库一个都没装

- `~/.agda/` 不存在（无 `libraries` / `defaults` 配置）；
- `~/.local/share/agda/2.9.0/` 为空；
- `sovereign.agda-lib` 声明的四个依赖 `standard-library-2.4`、`cubical-0.9`、`agda-categories`、`agda-algebras` **一个都没落地**；
- 全库 0 个 `.agdai` 编译产物。

**结论：二进制可用，但项目一行都编译不了。** 「22 万行未经类型检查」的原因从「没有编译器」修正为「编译器有、但库依赖与注册都没落地」。Makefile 期望调用 `agda +RTS -M8G -H6G -A128M -RTS`。

---

## 四、下一步（按优先级）

1. **编译闭环（最高优先）**：把 agda 装到持久位置并去隔离 → 装四个依赖库 → 写 `~/.agda/libraries` → 先拿一个小的 Geometry 模块试编 → 再评估全库类型检查。没有这一步，「0-postulate、全 refl」只能停留在文本扫描层面。
2. **Frobenius 链离散对译**：`FrobeniusChain.agda` 把 t-递推重写为 `σⁿ` 迭代（θ-lift 链的离散对译）+ 扩域次数 k 当重数 + `weil-norm-E1` 与 `algSat` 的 √q 来源对照引理。
3. **对译字典**：离散判据 ⇔ 连续零点线，这是真实缺口，不是基座大小问题。
4. **明确不碰**：连续 RH 的形式化竞赛（17.4 MB + 全栈朗兰兹不是可追赶目标）。

---

## 创建日期

2026-11-21
