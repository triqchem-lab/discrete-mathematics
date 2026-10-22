# 内核补丁依赖解除与假公理清理（2026-10-22）

> 本文件记录一次**以「标准 Agda 可验证」为目标的收口**：把库从「依赖本地内核补丁」
> 拉回到「纯净 Agda 全绿」，并顺带清掉一批**被内核证否的假公理**。
> 结论全部可复跑；每个判断都附了产生它的命令或行号。

---

## 1. 最终状态（可复跑）

| 检查器 | 结果 |
|---|---|
| 纯净版 `/data/work/functional-programming/Agda-v2.9.0-rc1/agda`（**无补丁**） | **915 / 0 / 915** |
| 补丁版 `/opt/agda/2.9.0/bin/agda`（项目默认） | **915 / 0 / 915** |

对照实验（修复前）：纯净版 903/915，**12 FAIL** ⇒ 现在 **0 FAIL**。

> **主库已不再需要内核补丁。** 补丁可以保留，但它已不是任何单模块编译的必要条件。

复跑命令：

```bash
cd /data/work/discrete-mathematics
AGDA=/data/work/functional-programming/Agda-v2.9.0-rc1/agda HEAP=8G \
  bash engineering/check_all_modules_parallel.sh 4      # 并发上限 4（内存安全线）
```

---

## 2. 补丁到底改变了什么（实测）

- **不是性能**：580.7s（补丁，热缓存） vs 603.6s（纯净，冷编）—— 差异在冷热噪声内。
- **是接受关系**：12/915 模块（1.3%）的判定结果不同。
- **具体机制**：补丁让内核把「两个**相异 Def** 的等式」判为空类型；
  标准 Agda 对此报 `UnsolvedConstraints / Is empty: … (stuck)`。
- 在库里，被它救下的全是形如 `¬ (A ≡ B)` + 空模式匹配（`λ ()` / `name ()`）的断言。

---

## 3. 四类站点与处置（全库 26 处 `¬ (A ≡ B)` 签名）

| 类 | 判据 | 处置 | 例 |
|---|---|---|---|
| **A** | 两侧一侧是**空 data**、另一侧**有居民** | **`subst` 搬运**（标准 Agda 可证） | `EnergyGap` ×3 |
| **A′** | 模块内有**可挂的矛盾锚点** | 改成模型层命题，挂该定理 | `ParityViolation` ×1 |
| **C** | 两侧是**同一类型的构造子**／数值字面量 | **标准 Agda 本来就通过**，无需改动 | `SpinTwistor` ×9、`CRTMeasurement`、`MagicSquare144`、`NumberOptComp` |
| **D** | 两侧是**相异且都有构造子**的 data/record | **② 不可行** ⇒ 澄清意图后改为**文档标注** | `HolographicPi` ×3、`SpinTwistor` ×3、`Constitution` ×3、`Resonance` ×2 |

### 3.1 类 A 的证明形状（可复用）

```agda
-- 空 data 的消去是标准 Agda 的合法消去（空类型无居民）
absurd-ContinuousEnergyDiff : ContinuousEnergyDiff → ⊥
absurd-ContinuousEnergyDiff ()

-- 搬运论证：有居民的一侧搬进空类型 ⇒ ⊥
notEnergyDifference : EnergyGapDefinition ≡ ContinuousEnergyDiff → ⊥
notEnergyDifference eq = absurd-ContinuousEnergyDiff (subst (λ T → T) eq sqrt3)
```

### 3.2 类 D 为何 ② 不可行（两条路穷尽排除）

- **路 A（空类型搬运）**：D 的定义就是「两侧都有居民」⇒ 无矛盾可导出；
- **路 B（矛盾锚点）**：三个模块内**没有任何定理**与这些断言冲突（已逐个查命题型签名）。
- ⇒ 标准 Agda 里，两个相异且有居民的 `data`/`record` 类型互不相等**普遍不可证**（无大消除）。

### 3.3 类 D 的澄清结论（关键）

**11 处全部属「防止误用」（宪法/禁令条款），不是数学定理。** 证据是模块自己的措辞：

- `Constitution.agda:12` —「声明面如实标注，**不作定理声称**」
- `SpinTwistor.agda:377/404` —「范畴分离(类型级)」「**禁止表述**」
- `HolographicPi.agda:372` —「**宪法约束**：…三类非法表述的类型区分」
- `Resonance.agda:258` — 原写「禁止表述（**已证明**…）」⇒ 「已证明」是不实声称，已一并更正

⇒ 按类型论，防止误用的正确表述是**文档标注**，不是类型层 `¬ (A ≡ B)`。
每处原位保留：原式留档 + 标准内核报错证据 + 澄清结论 + 「若要变成定理需先定义什么不变量」。

---

## 4. 假公理清理（`postulate` 审计）

判据（可复用）：**对每条 postulate 问「它的否定能否被内核证出？」** —— 能，它就不是公理，是矛盾。

`src/Sovereign/Synthesis/CRT/Zhonglv.agda` 中 **3 条**被证否：

| 公理 | 为何为假 | 处置 |
|---|---|---|
| `chernInvariant` | 类型写 `≡ + 2`，但 `evolveStep` 保持原 chern（取 chern=+1 即得 +1≡+2） | 按注释本意改为**定理**，`refl` 可证 |
| `polarClosure` | `stepCount` 与 `windingPolar` 是**相互独立**的记录字段 | 移除（全库消费者 0） |
| `toroidalClosure` | 同上 | 移除（全库消费者 0） |

结果：该模块 `postulate` 块 **5 → 1**（只剩合法的 `energyGapEncoded`）。

> 另有一条**已知但按人类裁决保留**：`Aether.aetherEnergyGapIsSqrt3`（`+1 ≡ +3` 在 ℤ 上为假）——
> 人类明确「不要拿你认为的数据去修改我的证明」，故只加内核核验注，不改值。

---

## 5. 方法论教训（三次同类错误，务必记住）

**Agda 的声明可以出现在四种缩进上下文**：顶层 / `record … where` / `module … where` /
`postulate` 与 `where` 块。**行首正则天然只能看到第一种。**

| # | 错误 | 后果 |
|---|---|---|
| 1 | 只认 `name = λ ()` | 漏了 `name ()` 子句体式 ⇒ 把 11 处低估成 9 处 |
| 2 | 搜 `^chernInvariant:` | 漏了 `postulate` 块内**缩进**签名 ⇒ 误报「符号不存在」 |
| 3 | 只认行首签名 | 漏了 record 字段 / `module … where` ⇒ **全库扫描 48 个命中，抽查 3 个全是假阳性（3/3）** |

**规矩**：
1. 写扫描器**先枚举声明位置上下文**；行首匹配只能用于「顶层声明」这一窄问题；
2. 报出任何「N 个可疑」之前，**先抽查 ≥3 个**并报告假阳性率；
3. 真实比例出来之前**不得据此改代码**。

**另一条**：`subst` 的方向。持有 `eq : f ≡ 1` 而目标是 `P 1` 时，必须写
`subst P (sym eq) base`。判断线索：报错说「base 类型与 goal 不符，差异在 **RHS 的具体数字**上」⇒
先怀疑 `eq` 方向，不是 `base`。

---

## 6. 台账卫生（顺带清掉的）

| 指标 | 修复前 | 现在 |
|---|---|---|
| 台账↔代码断链 | 17 | **1**（依据不可复现，见下） |
| 回执失效 | 5 | **1**（被 artifact 门禁锁死） |
| 声明了不存在的 postulate | 6 | **0** |
| 证据可信度 | 847/852 | **851/852** |
| proven | 852 | **852（A 级 852）** |

**剩余 1 条断链不可复现**：`PIO-1.astepstd.defs` 声称依赖 `Pi1dCardinality`，
但既不在节点 `deps` 链上（`deps = ['P2.4-barcelo-ahomotopy']`，后者 `deps=[]`），
也不在模块 import 闭包（`AStepStd` 只 import `BarceloAHomotopy`，闭包 2 个模块）。
⇒ **判定依据不在可读到的那两种里**。**故未改动**（`deps` 本身是对的；
为消计数删正确依赖 = 为指标改数据）。

---

## 7. 待人类裁决（4 项要点，完整 11 条见 `proof_dag brief`）

| # | 内容 | 现成件 |
|---|---|---|
| **D1** | **`artifact` 依赖门禁语义错配**：`artifact`/`abandoned` 永不 `proven` ⇒ 下游**永久锁死**（影响 94 个 artifact 节点） | `QFIX.misc-postulate-declare` 回执已备：`74b3f8c2…` |
| **D2** | `Aether.aetherEnergyGapIsSqrt3` 三候选 | 流水 1817 |
| **D3** | 断链判定器**需自说明依据**（现不可审计） | 流水 1873 |
| **D4** | `I_h` 特征标表（算 `freq-46` 的外部正确性用） | 拿到即可一条命令算完 |

---

## 8. 两条「可开工」为何不开工

`P2.2-mccord-weak-equivalence` / `P2.2c.geometric-pi-n` 都需要
**几何实现 + 一般同伦群机件**；本库只有 π₁(T⁶) 这类特例 ⇒ **超出基建**。
强行开工会变成「拿未定义的东西当命题」。

---

## 9. 复跑清单（接手先跑这些）

```bash
cd /data/work/discrete-mathematics
# 1) 双内核全库
AGDA=/data/work/functional-programming/Agda-v2.9.0-rc1/agda HEAP=8G bash engineering/check_all_modules_parallel.sh 4
HEAP=8G bash engineering/check_all_modules_parallel.sh 4

# 2) 增量（改完单个文件）
AGDA=/data/work/functional-programming/Agda-v2.9.0-rc1/agda \
  python3 engineering/check_dependents.py <改动的.agda> --jobs 4

# 3) 台账体检
#    proof_dag action:"check" / action:"brief"
```
