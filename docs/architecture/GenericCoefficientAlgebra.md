# 泛型系数代数框架——全景架构定型

> 版本：1.0（一次定型版）
> 对齐：Lean Mathlib 类型类层次 + agda-unimath 抽象环层 + hex-hensel 两阶段
> 本体论裁定：律算合一（三分损益法）为本源，数论层为定点算术的实现工具

---

## 全景依赖图（自底向上五层）

```
┌─────────────────────────────────────────────────────────────────────┐
│ L4 应用层                                                           │
│  Morse 同调│Hodge K3│Atkin q│律算定点│SOVEREIGN_LCM                │
├─────────────────────────────────────────────────────────────────────┤
│ L3 合成层（跨域拼合——CRT/商/同构/定点闭合）                           │
│  GenericCRT│QuotientGroup│ChainHom│ΣEquiv│HenselLift│ZhonglvClosure│
├─────────────────────────────────────────────────────────────────────┤
│ L2 结构层（代数结构——环/群/域的实例化）                               │
│  ModRoots(d)│RootCount(p,k)│FAb(n)│GF(3^k)│SunyiChain(n)          │
├─────────────────────────────────────────────────────────────────────┤
│ L1 基座层（系数原语——代数公理与法则）                                  │
│  Trit{⊕,⊗}│FAb法则│ModStep(d)│Coprimality│定点乘法│SunyiBase       │
├─────────────────────────────────────────────────────────────────────┤
│ L0 公理层（RootMath 第一性原理）                                      │
│  GF(3)公理│数字根公理│损益公理│归零公理│离散存在公理                  │
└─────────────────────────────────────────────────────────────────────┘
```

## L1 基座层缺口（新建两模块）

| 模块 | 内容 | 行数 |
|---|---|---|
| `SunyiBase` | 损益基元 sun(n)=2n/3, yi(n)=4n/3 + 合法性判定 | ~40 |
| `FixedPointQ16` | 定点 Q16：DELTA_Q16=113506=√3×65536 + 截断 | ~30 |

## L2 结构层缺口

| 模块 | 内容 | 行数 |
|---|---|---|
| `SunyiChain` | 十二律管长度 + 损益序列 + LCM 余数投影 | ~80 |
| `RootCount` | 3^k↔2根 / 2^k↔4根 统一判据 | 120–250 |

## L3 合成层缺口

| 模块 | 内容 | 行数 |
|---|---|---|
| `ZhonglvClosure` | acc=(acc×3^11)>>16——仲吕闭合 | ~60 |
| `GenericCRT` | **物不知数/大衍求一术的可执行算法形式化**（术 = 可执行算法 + 完备性证明；2026-10-10 裁决 ④ 选 (a) 改述——原「泛型 CRT 同构（环版）」= 西方环同构泛型化目标**作废**，红线：不得再做西方环同构） | 200–350 |
| `HenselLiftSchedule` | Hensel 提升调度 | 300–500 |

## 开工优先序

**律算线（低风险，直接服务 SOVEREIGN_LCM 真实意义）**：
S1 SunyiBase(~40行) + FixedPointQ16(~30行) → S2 SunyiChain(~80行) → S3 ZhonglvClosure(~60行) → **SOVEREIGN_LCM ≈210 行闭合**

**数论泛型线（中高风险，长期）**：
S4 RootCount(120–250) → S5 GenericCRT(200–350) → S6 HenselLiftSchedule(300–500, 独立线) → S7 迁移17模块(~100行净删减)

## 一次定型的核心承诺

1. 律算优先：SOVEREIGN_LCM 走律算路径（S1→S3, ~210行），不走数论根分析路径（680–1180行）
2. 数论为辅：HenselMod* 17 层作为 ModRoots 泛型框架的实例层保留
3. 两条独立线：3^k 数论线与 2^k 位域线在台账中解耦
4. CRT 为合成器：SOVEREIGN_LCM = CRT(3^11 分量, 2^16 分量)
5. G4 独立：Hensel 提升不阻塞律算线

## 挂接表（2026-10-10 裁决 ③——硬挂接，禁止两套编号各自开工）

> 已完成的 P3.2-hensel-* 系列**显式挂接**于此；后续任何开工先查本表，同一件事只走一套编号。

| 路线图项 | 台账节点 | 状态 |
|---|---|---|
| G1' 非根模式泛型化 | `G1-modular-roots` | 待开工 |
| G2（乘率/合成 泛型件） | `G3b-compose-theorem` | 见台账 |
| G3 术的形式化（④ 改述） | `G3-crt-generic`、`G3-crt-wuzhi` | proven |
| G4·2¹⁶ 四根线（独立位域） | `P3.2-hensel-mod-pow2`、`P3.2-hensel-2-side-fourfold` | proven |
| G4·3¹¹ 二根线 | `P3.2-hensel-mod177147`、`P3.2-hensel-mod531441`、`P3.2-hensel-mod27-part1`、`P3.2-hensel-lift-root1-uniqueness`、`P3.2-hensel-reduction-tower`、`P3.2-hensel-mod129140163` | 见台账 |
| G4·CRT 机械合成（2×4） | `P3.2-sovereign-lcm-roots`、`P3.2-sovereign-lcm-crt-synth` | proven |
| G4·8 根全景 | `P3.2-hensel-sovereign-lcm`、`P3.2-hensel-sovereign-lcm-numeric-layer` | proven |
| G4·唯一性等式层 | `P3.2-hensel-uniqueness-pure`、`P3.2-hensel-uniqueness-qge2` | qge2 proven(A 级)，pure WIP |
| S1–S3 律算线 | `S3-zhonglv-closure` 等（口径见 ②：定义+结构展示） | 见台账 |
| S4 RootCount | 待立项（挂 G1' 后） | — |
| S5 GenericCRT（④ 改述为术） | 同 G3 族 | 见上 |
| S6 HenselLiftSchedule | 待立项（G4 调度层） | — |
