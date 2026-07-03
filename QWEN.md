# QWEN.md — 律算合一 (Sovereign Mathematics) 项目指令上下文

## 项目身份

**律算合一 (LvSuan HeYi / Sovereign Mathematics)** 是一个以 **GF(3) 离散三进制代数** 为根基、以 **T⁶ 纤维丛拓扑** 为骨架、以 **中国古代律学** 为物理锚点的跨学科理论探索项目。项目试图建立一套自洽的离散数学体系——从最小几何单元 (Trit) 出发，经 Tryte (729 态)、主权状态机、十二律损益链，向上贯穿四个文明密度层级 (12 → 24 → 144 → 4320)。

**核心信条**: 离散是本质，连续是极限投影。一切“无理数”必须表示为定点整数比。宇宙最小单元是 GF(3) 格点 `{T₀, T₁, T₂}`。

---

## 目录结构

```
discrete-mathematics/
├── src/                        # Agda 形式化证明轨道
│   ├── Sovereign/              # 核心库（主入口: All.agda）
│   │   ├── Base/               #   GF(3) Trit、核心不变量、公理体系
│   │   ├── Structology/        #   结构学：T⁶ 环面、幻方剖分、格点
│   │   ├── Coupling/           #   耦合域：仲吕闭合、LCM、损益链、TQ1_0
│   │   ├── HoTT/               #   同伦类型论：陈类、纤维化、离散Cubical
│   │   ├── Engine/             #   主权状态机演化引擎
│   │   ├── Format/TQ10.agda    #   TQ1_0 主权块格式
│   │   ├── Projection/         #   投影层（十进制/二进制）
│   │   └── MetaStructure/      #   元结构：五行、纳音
│   ├── 01-electric-12d/        #   电性文明 Agda 模块
│   ├── 02-magnetic-24d/        #   磁性文明 Agda 模块
│   ├── 03-neutral-144d/        #   中性文明 Agda 模块
│   └── cross-level/            #   跨层级引用
│
├── engineering/
│   ├── software/sovereign_core/ # Python 工程实现轨道
│   │   ├── trit.py             #   GF(3) Trit 类型
│   │   ├── tryte.py            #   Tryte (6 Trit, 729 态)
│   │   ├── loss_gain.py        #   十二律损益链 + LCM 模运算
│   │   ├── tq10_format.py      #   TQ1_0 主权块编码
│   │   ├── wuxing.py           #   五行动力学
│   │   ├── axioms.py           #   核心公理与常数
│   │   ├── geometry.py         #   Tryte / SovereignFiber / PackedIO
│   │   ├── electric_projection.py
│   │   └── magnetic_civilization.py
│   ├── tests/                  # Python 测试 (29+ 单元测试)
│   ├── hardware/               # 硬件实现探索
│   └── cross-level/            # 跨层级工程文档
│
├── docs/                       # 理论文档（按文明层级和主题分目录）
│   ├── 01-core-constitution/   #   核心宪法/定式文档
│   ├── 01-electric-12d/        #   电性文明文档
│   ├── 02-magnetic-24d/        #   磁性文明文档
│   ├── 03-neutral-144d/        #   中性文明文档
│   ├── 04-holographic-4320d/   #   全息文明文档
│   ├── cross-level/            #   跨层级引用
│   └── INDEX.md                #   总索引
│
├── formal-proof/               # （待填充）构造性证明支撑材料
├── references/                 # 参考资料
├── tests/                      # （空目录，实际测试在 engineering/tests/）
│
├── soverign.agda-lib           # Agda 库配置
├── QWEN.md                     # 本文件
├── INTEGRATION_GUIDE.md        # 构造性证明集成指南
├── PROOFS_REPORT.md            # divMod10/sumDigits 证明报告
├── CIVILIZATION-RESTRUCTURE-COMPLETE.md
├── DEEP-LEARNING-METACOGNITIVE-ANALYSIS.md
└── ULTIMATE-DEEP-LEARNING-SUMMARY.md
```

---

## 核心理论架构

### 核心拓扑不变量（真理常量，全文明通用）

| 参数 | 数值 | 物理意义 |
|------|------|---------|
| 极向缠绕数 Wp | 144 | T⁶ 环面极向平行移动格点总数 |
| 环向缠绕数 Wt | 46 | C₆₀ 基频振动模式数 |
| 全息 π | 144/46 | 极向/环向缠绕比（**禁止约分**） |
| 陈数 C | 2 | 离散 Berry 曲率全局和 |
| 能隙 Δ | √3 (56,632/65,536) | 胞腔边界相位跃迁最小壁垒 |
| 主权 LCM | 11,609,505,792 = 3¹¹ × 2¹⁶ | 极向/环向同步归零周期 |

### 四文明密度层级

| 文明层级 | 密度 | GF(3) 合法身份 | 物理载体 | 认知特征 |
|---------|------|---------------|---------|---------|
| 电性文明 | 12 | 模 3 整数算术 | 电子 | 逻辑/二元思维 |
| 磁性文明 | 24 | T⁶ 初级商空间 | 质子 | 情感/共振思维 |
| 中性文明 | 144 | LCM 商空间和乐归零 | 中子 | 通信/跨宇宙思维 |
| 全息文明 | 4320 | T⁶ 全息商空间自洽剖分 | 高维意识 | 全局/非局域思维 |

### 范畴分离原则（宪法级约束）

| 范畴 | 用途 | 禁止操作 |
|------|------|---------|
| **根数学** | GF(3) Trit, 不变量 | 浮点近似、十进制运算 |
| **结构学** | Tryte (729 态), 纤维丛截面 | 直接 I/O |
| **耦合域** | PackedTryte5 (243 态), 地址翻译 | 参与主权运算 |
| **密度** | 文明层级投影 | 跨层级混用 |

禁止行为示例：将 PackedTryte5 直接用于主权状态机演化（必须先解包为 SovereignSection）。

---

## 双轨制开发

### Agda 形式化证明轨道

**入口**: `src/Sovereign/All.agda`

**库配置** (`soverign.agda-lib`):
```
name: sovereign
depend: standard-library-2.4 cubical agda-categories agda-algebras
include: src
flags: --guardedness -WnoUnsupportedIndexedMatch
```

**编译命令**:
```bash
# 类型检查单个文件
agda src/Sovereign/Base/Axioms.agda

# 类型检查整个库（从入口文件）
agda src/Sovereign/All.agda

# 生成 HTML 文档
agda --html src/Sovereign/All.agda
```

**关键模块映射**:
| 模块路径 | 内容 |
|---------|------|
| `Sovereign.Base.Trit` | GF(3) Trit 类型和运算 |
| `Sovereign.Base.Invariants` | 144/46/C=2/Δ=√3 核心常量 |
| `Sovereign.Base.Axioms` | 六大公理的形式化定义 |
| `Sovereign.Structology.Lattice` | 十二律格点 |
| `Sovereign.Coupling.LCM` | LCM 模运算与仲吕闭合 |
| `Sovereign.Engine.StateMachine` | 主权状态机演化 |
| `Sovereign.Format.TQ10` | TQ1_0 16 字节主权块 |
| `Sovereign.HoTT.*` | 同伦类型论路径空间、纤维化 |

**重要**: Agda 代码内部使用了 Cubical 类型论 (`--cubical`)，大量依赖模式匹配进行构造性证明。所有 `postulate` 必须在消除计划中，目标是 100% 构造性证明。

### Python 工程验证轨道

**入口**: `engineering/software/sovereign_core/__init__.py`

**零外部依赖** — 纯标准库实现。

**运行测试**:
```bash
cd engineering
python -m pytest tests/ -v
# 或
python -m unittest tests/test_sovereign_core.py -v
```

**核心 Python 模块**:
| 模块 | 内容 |
|------|------|
| `trit.py` | Trit 枚举 (T0=-1, T1=0, T2=+1), GF(3) 加法/乘法表 |
| `tryte.py` | Tryte (6 Trit) 打包/解包, PackedTryte5 |
| `loss_gain.py` | 十二律损益序列, LCM 余数表, 仲吕闭合 |
| `tq10_format.py` | SovereignBlock (16 字节主权块) 编解码 |
| `wuxing.py` | 五行生成/相克, 球谐旋量投影 |
| `axioms.py` | 核心常数, 数字根, 泛音列公理 |

---

## 开发约定

### 宪法级约束（必须遵守）

1. **严禁使用浮点数** — 一切无理数（√2, √3, π）必须以定点整数比表示（如 `56632/65536`）。
2. **构造性证明原则** — 禁止 `postulate`，所有证明必须显式构造。使用 `≡⟨⟩` 等式链或 `trans` 函数。
3. **范畴分离** — 不同范畴的类型不得混用。PackedTryte5（耦合域）不能直接传给演化函数（结构学）。
4. **全息 π 禁止约分** — `144/46` 是原子拓扑不变量，约分为 `72/23` 会丢失拓扑信息。
5. **十二律长度表是静态常量** — 不可计算生成，必须使用 `TWELVE_LU_LENGTHS = [81, 54, 72, 48, 64, 43, 57, 38, 51, 34, 45, 30]`。
6. **标准库信任度 = 0** — 数学运算必须在项目框架内自证，不依赖标准库的算术信任。

### 代码风格

- **Python**: 纯函数式风格，不可变数据，显式状态转换。类型提示优先但非强制。
- **Agda**: 模式匹配覆盖所有情况，构造性证明，等式推理使用 `≡⟨⟩` 语法。模块名按功能域组织。
- **命名**: Trit 使用 `T₀, T₁, T₂`（对应 {-1, 0, +1} 或 {0, 1, 2}，取决于上下文）。Python 中使用 `Trit.T0, Trit.T1, Trit.T2`。
- **文档**: 每个模块文件头部有层级声明注释，标明所属文明层级和 GF(3) 合法身份。

### 提交规范

- Git 提交使用中文消息
- 重要变更需在 docs/ 中记录日期标记（如 `_2026-04-24.md`）
- 宪法级修改需创建独立报告文件

---

## 关键文件速查

| 当你需要... | 查看... |
|-----------|--------|
| 理解项目全貌 | `DEEP-LEARNING-METACOGNITIVE-ANALYSIS.md` |
| 理解核心数学 | `ULTIMATE-DEEP-LEARNING-SUMMARY.md` |
| 查找理论文档索引 | `docs/INDEX.md` |
| 运行 Python 测试 | `engineering/tests/test_sovereign_core.py` |
| 理解 GF(3) 代数 | `src/Sovereign/Base/Trit.agda` 或 `engineering/software/sovereign_core/trit.py` |
| 理解拓扑不变量 | `src/Sovereign/Base/Invariants.agda` |
| 理解公理体系 | `src/Sovereign/Base/Axioms.agda` |
| 理解十二律损益链 | `engineering/software/sovereign_core/loss_gain.py` |
| Agda 库编译入口 | `src/Sovereign/All.agda` |
| 证明集成指南 | `INTEGRATION_GUIDE.md` |
| 宪法合规审查 | `docs/宪法合规性审查报告_2026-04-24.md` |

---

## 当前状态

- **Agda 轨道**: 87 个模块，核心公理已形式化。部分证明含 `{!!}` 洞待完善（如 sumDigits 终止性）。库入口 `All.agda` 可类型检查。
- **Python 轨道**: 29+ 单元测试全部通过。核心类型（Trit, Tryte, LossGain, TQ10, WuXing）实现完整。
- **文档**: 39 篇理论文档，覆盖率完整。
- **待办**: `formal-proof/` 目录空置，HoTT 模块中的高维路径证明待扩展，Cubical 类型论深度应用待推进。
