# Fermat 离散投影链 — 依赖路线图 (PROOF-PATH)

**日期**: 2026-09-07
**状态**: 证明链工程文档（依赖纪律，对标 Claude/Lean 工程方法）
**来源**: `src/Sovereign/Problem/Fermat/` L0–L3 + `engineering/check_fermat_chain.sh`

---

## 0. 本文档的定位

> 本文档不证明任何新数学，也不复述 13-flt-analysis 的裁决。它把 Fermat **离散投影链**
> 组织成一张显式依赖 DAG，并给出一条命令的验证闸门——这是从 Claude/Lean 60478 模块
> 工程**借鉴的工程纪律**（依赖即引用、单点健康信号、强度审计），**不是借鉴其数学理论**。
>
> 数学立场以 [13-flt-analysis.md](13-flt-analysis.md) 为准（P0，宪法级）：
> FLT 的无解性在 Archimedes 序的债务里，本链只形式化"幂的律"，不断言 ℤ 上无解。

---

## 一、证明链总览（一条命令验证）

```bash
./engineering/check_fermat_chain.sh     # 期望: 整链健康, exit=0
```

闸门按**拓扑序**编译 L0→L1→L2→L3，并逐一扫描 postulate/hole/sorry。
这是本链的 `#print axioms` 健康信号：**单模块 exit=0 + 零 postulate/hole**。

```
L0  FermatL0  幂函数定义层  pow3, 零幂族, 非零分类
 │  依赖: Trit (GF3 环公理)
 ▼
L1  FermatL1  GF(3)× 幂周期层   周期 2: 偶→1 奇→x
 │  依赖: L0 (pow3, ≢₃, pow3-zero-odd), Trit
 ├──────────────┐
 ▼              ▼
L2  FermatL2  mod-3 方程分类   奇→线性伪解 / 偶→零通道
 │  依赖: L0 + L1 (pow3-even/odd)
 │
L3  FermatL3  GF(9)× 周期层      C₈: x⁸=1, φ 阶 8
    依赖: GF9 (phi/alpha/gf9-pow), Trit

L4 层（两模块，互补）:
├─ FermatL4_NatLift    ℕ 提升: 偶次解 ⟹ 3|abc   [依赖 L0+L1]
└─ FermatL4_Mod12Cycle R₁₂ 环: 幂分类 + 三单位偶次无解 [依赖 Duodecimal]
```

- L2 与 L3 **互不依赖**，只共享 L0/L1 地基 → 任一侧改动不波及另一侧（断点局部化）。
- L4 两模块互补：NatLift 把 mod3 约束提升到整数（主定理 T8），
  Mod12Cycle 分类 R₁₂ 环乘幂行为（DC12 论文 L4 的真内核）。

---

## 二、节点清单（每环的可验证单元）

| 层 | 模块 | 角色 | 核心导出（定理级） | 0 postulate |
|----|------|------|-------------------|:---:|
| L0 | FermatL0 | 定义 | `pow3`, `pow3-zero-odd`, `zero-trit?`, `nonzero-class` | ✅ |
| L1 | FermatL1 | GF(3)× 幂周期 | `nonzero-square`, `pow3-even`, `pow3-odd`, `pow3-even-channel` | ✅ |
| L2 | FermatL2 | mod-3 分类 | `flt-odd-linear`, `flt-mod3-sol-112/221`, `flt-even-nonsol`, `flt-even-zero-channel` | ✅ |
| L3 | FermatL3 | GF(9)× C₈ | `gf9-pow8`, `phi-3-11`, `phi-11-19` | ✅ |
| L4a | FermatL4_NatLift | ℕ 提升 | `flt-even-nat-nonsol`, `flt-even-nat-zero-channel` (3\|abc) | ✅ |
| L4b | FermatL4_Mod12Cycle | R₁₂ 环分类 | `pow12-unit-even/odd`, `flt-mod12-even-nonsol` | ✅ |

> **定义层与命题层分离**（对标 Claude 的 Definitions/ vs Theorems/）：
> L0 只定义不证明（pow3 的递归、零/一的幂行为），L1–L3 才是命题层。

---

## 三、依赖 DAG 的"精确强度"审计（对标 Claude PROOF-PATH 的每步强度声明）

> 原则（借自 Claude 工程）：**每条 import 边必须恰好是该节点证明所需的依赖，
> 不引入更强者，不缺更弱者。** 逐边审计：

### 边 L1 → L0：`pow3`, `_≢₃_`, `pow3-zero-odd`

- `pow3` 需要（幂定义）；`_≢₃_` 需要（非零前提）；`pow3-zero-odd` 需要（`pow3-even-channel` 的零分支）。
- **恰好**。L1 不需要 L0 的 `zero-trit?`/`nonzero-class`（那是 L2 才用）。

### 边 L2 → L1：`pow3-even`, `pow3-odd`

- L2 证偶/奇方程分类，**恰好需要这两个周期引理**。不需 L1 的 `nonzero-square`/`pow3-step2`
  （L1 内部用，L2 只引用成品）。
- L2 → L0 只需 `pow3`, `_≢₃_`, `zero-trit?`（零通道三重分派）。

### 边 L3 → GF9：`GF9; gf9-zero; gf9-one; gf9-pow; phi; alpha`

- L3 证 C₈ 周期，需要 `gf9-pow`（幂）、`phi`/`alpha`（实例元）、`gf9-zero/one`。
- 不需 GF9 的乘法公理（`*gf9-assoc` 等）——gf9-pow8 是 9-case 穷举 refl，不依赖域公理链。
- **恰好**。这条边体现"L3 是纯有限穷举，站在 GF9 的载体上而非其证明深度上"。

### 地基边：L0/L1/L2/L3 → Trit

- 全部只需 Trit 的**环公理**（`⊗-identityˡ/ʳ`, `⊗-assoc`, `⊗-zeroˡ`）与构造子不相交（`λ()`）。
- Trit 自身 0 postulate（GF3 公理 3-27 case 穷举 refl）→ 地基无泄漏。

### 顶层裁决（13-flt §10）对 L0–L4 的依赖

```
"无解性在 Archimedes 序的债务里" (元裁决, 非 Agda 定理)
  依赖(元层面): L1 pow3-even/odd (周期2), L3 gf9-pow8 (周期8), L2 零通道
  → 指数信息坍缩为 (奇偶, mod8) → 不足以区分 n=2 与 n≥3
```

顶层**不新增 Agda 模块**——它是对 L0–L4 已证内容的元阅读 + 对 ℤ 序结构的归属判断。
这正是与 Claude 结构性的差异：Claude 顶层是 1 个 `fermat_last_theorem` 定理
（在连续统内），我们的顶层是一个元裁决（在连续统外看）。**依赖图的形状不同，
因为论题不同；依赖纪律相同，因为都是"线不断"的工程要求。**

---

## 四、验证闸门（Claude `#print axioms` 的对应物）

| 健康信号 | Claude/Lean | 本链 |
|---------|------------|------|
| 单一出口 | `fermat_last_theorem` 定理 | 元裁决 13-flt §10（文档） |
| 公理集不扩散 | `#print axioms` = 3 标准公理 | 逐模块零 postulate/hole 扫描 |
| 链可局部验证 | 每环独立编译 | 每环独立编译（拓扑序 L0→L3） |
| 一键全链 | `lake build` | `./engineering/check_fermat_chain.sh` |

### 闸门输出示例（2026-09-07 实测）

```
✅ FermatL0: exit=0     ℹ️  0 postulate / 0 hole / 0 sorry
✅ FermatL1: exit=0     ℹ️  0 postulate / 0 hole / 0 sorry
✅ FermatL2: exit=0     ℹ️  0 postulate / 0 hole / 0 sorry
✅ FermatL3: exit=0     ℹ️  0 postulate / 0 hole / 0 sorry
✅ FermatL4_NatLift: exit=0     ℹ️  0 postulate / 0 hole / 0 sorry
✅ FermatL4_Mod12Cycle: exit=0  ℹ️  0 postulate / 0 hole / 0 sorry
✅ 整链健康: 全部 exit=0, 零 postulate/hole   (exit=0)
```

### 闸门自检（检测能力验证）

- 含 `postulate bogus` / `{! hole !}` 的文件 → 正确标记 postulate=1/hole=1 ✅
- 注释里写 "0 postulate" → 剥离注释后计数=0，不误报 ✅

---

## 五、边界声明（防越界，写入每模块头并在此汇总）

1. **不断言 FLT 在 ℤ 上无解**。本链只证幂周期/分类/约束，无解性裁决在 13-flt §10。
2. **约束是必要条件，非充分**：偶次 ⟹ 3|abc 排除的只是"三皆非 3-倍数"，不排除
   3|abc 的解（3²+4²=5² 正是允许形状）。
3. **不混 C₄ 与 V₄**：GF(9)× 的 ⟨α⟩ 是 C₄（4 阶元），R₁₂ 单位群 {1,5,7,11} 是 V₄
   （全 2 阶）。L4b 处理 R₁₂ 时明确其乘法是 `*12` 环乘、非 `mulAlpha`——
   防混淆引理 `DuodecClock.mulAlpha-not-*12` 已证，可随时引用。
4. **不做位值分离**：位数比较在 n≥3 时与 aⁿ+bⁿ 无恒成立分离（DC12 论文 L5 反例），本链不使用。

---

## 六、改动记录

| 日期 | 改动 |
|------|------|
| 2026-09-07 | 建本文档；建 `engineering/check_fermat_chain.sh` 闸门（L0→L3 全绿实测） |
| 2026-09-07 | FermatL1 补 `pow3-even-channel`（定理 C，闭合 13-flt §9.2 A–D 声称） |

---

## 更新 (2026-09-07): 大衍核心接链 + 群论闸门

- **DayanCore** (`Algebra/GroupTheory/DayanCore.agda`) 形式化最低公理基座
  DC = ⟨δ, φ | δ³=id, φ⁴=id, δφ=φδ⟩ ≅ C₃×C₄≅C₁₂:
  抽象定理 `dayan-joint-order-12 : (δ∘φ)¹² = id`（迭代交换律 + 周期分解归纳导出，非穷举）。
- **接链**: `FermatL4_Mod12Cycle` §8 新增 `dayan-anchor`——R₁₂ 层 "mod 12 穷尽相位信息"
  的合法性现在显式挂在表现级基座上，Problem 层依赖边闭合。
- **新闸门**: `engineering/check_group_chain.sh` 管理群论链
  DuodecClock → DuodecClockProperties → DCGroup → InformationStructure →
  NormExactSequence → NormHomomorphism → CyclicGroupStructure → DayanCore
  （当前全绿: 8/8 exit=0, 零 postulate/hole）。
- 群论/特征层裁定记录: DCCayleyGraph 假命题 P·A·P=A⁻¹ 已删除;
  DCCharacter 载体重建为 ℚ(ζ₁₂)（Sqrt3 全实域容不下单位根），特征同态性 1728 case refl。
