# 考古：自定义 REWRITE 规则、All.agda 拆解、fixity 声明的真实历史

**日期**：2026-09-10（考古）｜仓库 `git rev-list --count HEAD` = 489 次提交
**触发**：用户质疑「fixity 声明应该是很久就写入目录的吧」+「自定义规则我们使用很多，之前 All.agda 统一编译内存太大，后面拆解为模块编译，自定义规则有传染性」
**关联台账节点**：`H.doc-code-drift-scan`

---

## 一、fixity 声明：**写进了技能文档（2026-07-27），代码侧从未执行过（0 次）**

| 证据 | 命令 | 结果 |
|---|---|---|
| `Trit.agda` 有无过 fixity | `git log -S "infix" --all -- src/Sovereign/Base/Trit.agda` | **空**（该文件 11 次提交里从未出现 `infix`） |
| `infixl 6 _⊕_` 在哪些文件 | `git log -S "infixl 6 _⊕_" --name-only --all` | 只有 `proof-engineer-merged.md` / `proof-engineer-updated.md`（`5e07836`，**2026-07-27**）与 `.reasonix/skills/proof-engineer/SKILL.md`（`6ad54f4`，**2026-07-28**） |
| 当前盘上还有谁 | `git grep "infixl 6 _⊕_"` | 仍只有那 **3 个 md**，**零个 `.agda`** |

⇒ 用户的印象是对的（"很久就写入了"），但写进的是**技能文档**；**代码侧零次执行**。

### ⚑ 决定性先例：项目**已经裁定过**「给上游模块加 fixity」= 不行

```
dd377a2  2026-09-08  revert: 撤销对上游 GF9.agda 的 fixity 改动 (违反依赖方向)
```
被撤销的正是（从**上游** `GF9.agda` 中删除，即那次改动把它们加进了 GF9.agda）：
```diff
- infixl 6 _+gf9_
- infixl 7 _*gf9_
```
同一次提交里 `GF729Field.agda`（下游）**被动改了 18 行**（11+/7−），**全部是补内层括号**。
⇒ 这实证了「fixity 会改变同一个文本的分组，并强迫下游改写」——与我用探针 A/B/C 得到的结论
（同一文本 B/C 两种 fixity 都编译通过但值不同）是**同一现象在真实工程里的发生**。

**关键**：`GF9.agda` 至今**没有** fixity（撤销后未再加回）。
⇒ 项目对这类改动的判定是：**不要为了书写方便去改上游模块**（理由：违反依赖方向）。
⇒ `Trit.agda` 是**更上游**（被 516 个模块间接依赖），给 `_⊕_`/`_⊗_` 加 fixity 属**同一类已被回退过的改动**。


### 补 fixity 的执行记录（2026-09-10）

**改动**：`src/Sovereign/Algebra/GF729.agda` 仅**插入** `infixl 6 _+gf729_`（`:182`）+ 4 行说明注释，
**无任何行被删改**（diff = 纯增量）。

**为什么这是合法的那一类**（对照三种情形）：
| 情形 | 判定 |
|---|---|
| 为**自有**运算符在**定义处**声明 | ✅ 本次做的；对齐 `GF27:127` / `GF81:117` / `GF243:672` / `GF729Field:701` 的 `infixl 6` |
| 为**导入的**运算符声明 | ❌ `UnknownNamesInFixityDecl`（Agda 拒绝） |
| 改**上游模块**的 fixity | 🚫 `dd377a2` 已裁定「违反依赖方向」 |

**验证（两步均有工具回执）**：
| 对象 | 结果 | 回执 |
|---|---|---|
| `GF729.agda`（本模块） | exit 0 / 5.2s | `c93f446410a7…` |
| `TowerConnection.agda`（下游，全库唯一 import GF729 者） | exit 0 / 5.3s | `87e0c592c847…` |
传递下游：无人 import `TowerConnection` ⇒ 链止于此。

**「分组不变」的论证方式（重要 —— 不靠"编译通过"）**：
编译通过只能否证**类型错**，**不能排除静默改分组**。真正的论证是**穷举扫描**：
1. GF729 内部 `_+gf729_` 各出现处均为单次使用或**已显式括号**（`:226 (x +gf729 y) +gf729 z` 全括号）
2. 下游 `TowerConnection` 仅 `:128/:139/:150` 三行，每行 `≡` 两侧**各只含一个**运算符
3. 正则全库搜「同一项内混用」（`+gf729` 与已有 fixity 的 `+gf9/+gf27/+gf81/+gf243`）→ **零处**
4. 按探针结论：未加括号的连写今天是 **Parse error**（默认 level 20 非结合）⇒ **不可能存在于可编译代码中**
   ⇒ 加 fixity 对现有代码只能是**纯增量**

**对照 `dd377a2`（为什么那次被迫改下游而这次不用）**：
那次是把 fixity 加到**上游** `GF9.agda`，而下游 `GF729Field` 有**大量**该运算符的表达式 ⇒ 被迫改 18 行；
这次下游只有 **3 行**、每行一个运算符、且无同项混用 ⇒ 零行改动。

### 正确用法（用户指出的语境）：**为「自己定义」的运算符声明 fixity 是合法的**

| 文件 | 自有运算符的 fixity | 判定 |
|---|---|---|
| `GF243.agda:672` | `infixl 6 _+p9_` | ✅ 合法（自己定义的 `_+p9_ : Poly9 → Poly9 → Poly9`） |
| `GF729Field.agda:701` | `infixl 6 _+p5_` | ✅ 合法（自己定义的 `_+p5_ : Poly5 → Poly5 → Poly5`） |
| `GF81.agda:117,200` | `_+gf81_` / `_*gf81_` | ✅ |
| `GF27.agda:127,163` | `_+gf27_` / `_*gf27_` | ✅ |
| **`GF729.agda`** | **✅ 已补**（2026-09-10） | 原为遗漏：自有的 `_+gf729_` 未声明。**已补 `infixl 6 _+gf729_`**（`:182`）。`_+₃_` **按惯例不动**（全库 7 处定义仅 `CyclicGF27:55` 声明过，且它是 `Fin 3` 上只作前缀用的小 helper） |
| `GF9.agda`（上游） | 无（曾被加、已 revert） | 🚫 被裁定 |
| `Trit.agda`（更上游） | 无 | 🚫 同「上游」类 |

⇒ **「加 fixity」在「自有运算符」语境下是对的**（GF243/GF729/GF729Field 那几次会话里是对的）；
我把它泛化到「在**新模块**里给**导入的** `_⊕_` 加 fixity」是**两头都不成立**的用法：
既非自有运算符（`UnknownNamesInFixityDecl`），又碰上游（`dd377a2` 已回退）。
⇒ 所以 `proof-engineer` 附录 4 规则 #1 不是「被违反」，而是**从未被尝试成功过**——且实测执行不了（`UnknownNamesInFixityDecl`，见 `prover_limits: agda-fixity-cannot-be-imported`）。

## 二、自定义 REWRITE 规则：起因、传染性的**实证代价**、现状

### 2.1 起因：GF(3⁶)=GF729 / 4320D 的大数归一化

```
591d25b  2026-07-13 21:04   REWRITE: mod3k rule active, div3k for base case
9e34298  2026-07-14 07:57   T6Lattice ≃ Fin 729: 0 error, 右结合框架 + div3k/mod3k rewrite + eqToPath 修复
```
动机（`AGENTS.md` 记录）：`div3k`/`mod3k` 让 4320D 归约替代 `mod-helper` 展开，**避免类型检查 OOM**。

### 2.2 传染性的**实证代价**：2026-07-14 上午 66 分钟内 6 次提交、其中 3 次 revert

```
08:08  cc9aac4  fix: 移除 --rewriting 消除 InfectiveImport（div3k/mod3k 暂存 wiki 作为未来优化）
09:02  d0b9821  Revert "fix: 移除 --rewriting 消除 InfectiveImport…"
09:04  27e35f8  feat: 传播 --rewriting 到全部 9 个依赖文件, 恢复 div3k/mod3k rewrite 规则
09:09  ce3abe6  Revert "feat: 传播 --rewriting 到全部 9 个依赖文件…"
09:10  efc0ef9  clean: 移除未使用的 div3k/mod3k rewrite 规则（待 4320D 纯模运算迁移时恢复）
09:14  1b8281b  feat: 4320D 超前规划——div3k/mod3k rewrite + --rewriting 传播到全部 9 个依赖文件
```
`1b8281b --stat` 显示被逼改旗标的文件（10 个）：
`SpinTwistor` / `CartanTorsion` / `HopfConstruction` / `T6Homotopy` / `WindingCover` /
`Aether` / `MagicSquare144` / `Platonics` / `QuantumBridge` / `T6`。

**一条 REWRITE 规则 → 10 个文件的 `--rewriting` 旗标 → 反过来触发 `InfectiveImport` → 来回 revert。**
这就是「自定义规则有传染性」的历史实证，也是项目对**全库级改动**有创伤记忆的来源。

### 2.3 现状

| 指标 | 值 |
|---|---|
| REWRITE 注册 | **12 条**（`T6`/`T6Rewrite`：`div3k`/`mod3k`/`gf3Toℕ-A4-inv`；`XuanwuAbsorption`/`XuanwuAbsorptionRewrite`：`mod46k`/`div46k`/`mod-a+598`；`jac_Pigeonhole`：`decode9-encode9`） |
| 带 `--rewriting` 的模块 | **516 / 557 = 92.6%** |

⇒ 用户「这个自定义规则我们使用很多」完全准确。

## 三、All.agda 拆解

```
8d667f6  2026-09-07  refactor: 取消 All.agda — 去聚合化, 模块独立编译
```
⇒ 用户「之前 All.agda 统一编译内存太大，后面拆解为模块编译」**准确**。

## 四、把三件事连成一条因果链（本次考古的真正价值）

```
自定义 REWRITE 规则（为 GF(3⁶)/4320D 大数归一化而加）
  → 传染性：--rewriting 必须传播到全部依赖文件（2026-07-14 实证代价：3 次 revert）
  → All.agda 统一编译内存爆
  → 2026-09-07 拆成模块独立编译
  → ⇒ 失去「一次全量编译验证全库」的通道
  → ⇒ 任何**全库级改动**（fixity、REWRITE 规则、Base 层改动）的验证成本与风险上升
```

**推论**：项目「没有原因不加全局规则」**不只是原则，有历史代价支撑**。
这也是为什么 `AGENTS.md` 把 `--rewriting` 定位为「语义完备性设计，不是补丁」却同时配有
`check_all_modules_parallel.sh` 这类批量闸门 —— 传染面 92.6% 决定了必须靠闸门而非人眼。

## 五、一个反复出现的系统性模式：**文档承诺 ≠ 代码存在**

同类缺陷已发现 **3 次**（全部由用户追问触发）：

| # | 文档说的 | 代码实际 | 发现方式 |
|---|---|---|---|
| 1 | `07 §6.1 G4`「¬(mulAlpha 经 toDuodec = \*12)」 | 证明用的是 `mixedOp`；`mulAlpha` 定义在 `AlphaPower` 上，`toDuodec` 不接受该类型 ⇒ 原标题类型上不成立 | 用户问「下降为 C₁₂ 是什么原因」时连带复核 |
| 2 | `CyclicGroupStructure` 头注释承诺 `mixedOp-power-add` / `dc-order-12` | **两个符号都不存在** | 开工块 7 时「先查再断言」 |
| 3 | `proof-engineer` 附录 4「在使用模块加 fixity」，写于 2026-07-27 | **代码侧 0 次执行、且实测执行不了** | 用户问「为什么要加这个 fixity」 |

**这不是三次巧合，是一个模式**：文档/技能里的符号名与规则，**没有与代码存在性做过交叉校验**。
对策（可机械执行）：**文档里出现的任何 Agda 符号名，都应能被 `grep` 在 `.agda` 里找到**；
找不到的就是待澄清项 —— 要么实现，要么改文档。已登记为台账节点 `H.doc-code-drift-scan`（active）。

## 六、诚实边界

- `git log` 的作者元数据**全部**是 `Yan Li <yanli@trit.local>`，**不记录"规则由谁提议"**
  ⇒ 用户说的「模型建议加的」**无法从 git 元数据证实**。可间接佐证的是：若干较晚的提交信息自带
  会话标记（`会话裁定 #11/#14/#16`、`GLM 审计`），说明 AI 会话参与过；但 REWRITE 那几次
  （2026-07-13/14）的提交信息里**没有**这类标记。
- 「All.agda 内存太大」是从提交标题与 `AGENTS.md` 推得，**未见具体内存数字入 git**（无实测日志）。
- 本次考古全部为**只读**（`git log/show/grep`），未改动任何文件。


---

## 七、机械化：「文档承诺 ↔ 代码存在性」扫描器（2026-09-10 交付）

**工具**：`engineering/tests/doc_code_drift.py`（只读）
**oracle 回执**：`7c0bdd03f09e…`（domain = points = **8154**，1.4s，exit 0）
**关联台账节点**：`H.doc-code-drift-scan`（active，含回执）

### 7.1 覆盖范围（诚实边界：只 1/3）

| 类 | 内容 | 抓得到？ | 历史实例 |
|---|---|---|---|
| **A** | 文档/注释承诺的符号名**在代码中不存在** | ✅ **已自动化** | `CyclicGroupStructure` 头注释承诺 `mixedOp-power-add` / `dc-order-12`（代码里都没有） |
| **B** | 符号**存在**但语义不符 | ❌ | `07` 的 G4 条标题写 `mulAlpha`，证明里是 `mixedOp`（名字都能 grep 到） |
| **C** | 文档陈述的**规则本身不可执行** | ❌ | 附录 4「在使用模块加 fixity」— Agda 报 `UnknownNamesInFixityDecl` |

### 7.2 设计

```
Tier-1  .agda 头注释里的承诺名（`-- name : 说明` 与 `-- 包含：a / b / c` 列表）→ 高置信错位
Tier-2  docs/**/*.md 反引号里的标识符                                          → 候选，噪声多
形状过滤 sym_like：小写开头 + 长度≥4 + 含 `-`/`_`/内部大写/数字
索引前 strip_comments：剥 `--` 行注释与可嵌套 `{- -}`（含 `{-# #-}`）
--rev <commit>：回放历史提交，用于**已知答案回归测试**
```

### 7.3 三个设计层坑（全部踩过并修好）

| # | 坑 | 后果 | 修法 |
|---|---|---|---|
| 1 | 用 `ls src/**/*.agda` 取文件列表（**bash 默认不递归**） | 只拿到 17/589 个文件 → 索引残缺 → 几乎全部候选被误报"缺失" | 改用 Python `glob(..., recursive=True)` |
| 2 | **索引把注释里的标识符也算作"代码中存在"** | **永远抓不到注释承诺型错位** —— 而那是靶心。实测 `git grep -c mixedOp-power-add -- CyclicGroupStructure.agda` = 1，但那唯一一次就是头注释那一行 | 索引前**剥注释** |
| 3 | 无形状过滤 | Tier-1 从 93 条误报（`BCW` 散文列表 / `Dvir` 人名标签 / `P3-C` 层级标签） | 加 `sym_like` → 降到 5 条 |

### 7.4 回归测试（已知答案）

对 `--rev HEAD`（我本次改动未提交，故 HEAD 就是"修复前"状态）运行：

```
mixedOp-power-add            CyclicGroupStructure.agda:14   ✅ 复现
dc-order-12                  CyclicGroupStructure.agda:15   ✅ 复现
```

**精确命中两条历史错位** ⇒ 扫描器不是摆设。

### 7.5 扫出的真错位（4 条，**全部已修**）

| 名字 | 出处 | 性质 | 处置 |
|---|---|---|---|
| `dc-order-12` | `CyclicGroupStructure:15` | **我自己造成的残留** —— 头注释承诺该名，但我把它实现成了 `mixedOp-power-12` | ✅ 头注释改引真实符号名 |
| `c8-summary` | `FermatL3.agda:20` | 头注释「本层主定理」第 3 项承诺，而文件尾部**只有一坨被 `{- -}` 注释掉的汇总文本**（§4 标题已预留「C₈ 周期汇总」）⇒ 作者写了却从未落成定义 | ✅ **落成真定义**（见 §7.8） |
| `jac_Langlands` | `Langlands.agda:3`（另散布 8 处注释） | 全库注释都用这个旧名；真实 module 名是 `Sovereign.Problem.Langlands.Langlands` | ✅ 头注释改真名，旧名保留为可 grep 别名 |
| `jac_RH` | `RH.agda:3` | 同理，真实名 `Sovereign.Problem.Riemann.RH` | ✅ 同上；顺带修同文件头部的旧名 `jac_BSD`（真名 `Sovereign.Problem.BSD.BSD`） |

**修复后复跑：Tier-1 从 5 条 → 2 条**，剩下的 2 条恰是下面 7.6 的已知假阳性 ✅。

### 7.8 `c8-summary` 的补法（最有价值的一条：欠账落成定理）

`FermatL3.agda` 尾部原文：
```agda
{-
-- 汇总: 幂的律全貌 (L1 × L3)
--   GF(3)×: x^(2k) = 1,  x^(2k+1) = x       (周期 2, 奇偶坍缩)
--   GF(9)×: x⁸ = 1 ∀ x ≠ 0                  (周期 8, C₈)
--   联合 12 = LCM(3,4) 进制: 指数维度在此坐标系中无 Archimedes 序内容
--   裁决引用: docs/duodecimal/13-flt-analysis.md §8.3
-}
```
⇒ 换成真定义（按项目惯例 —— 全库有 **13 个**顶层 `*-summary` 符号，模板见 `LCMVortexConnection.lcm-summary`）：
```agda
c8-summary :
    (∀ x → x ≢₉ gf9-zero → gf9-pow x 8 ≡ gf9-one)   -- C₈ 周期 (§2)
  × (gf9-pow phi 8 ≡ gf9-one)                        -- 生成元 φ 的 8 阶证据 (§4)
  × (gf9-pow phi 3 ≡ gf9-pow phi 11)                 -- mod 8 平移不变 (§3)
  × (gf9-pow phi 11 ≡ gf9-pow phi 19)
c8-summary = gf9-pow8 , (phi-pow8 , (phi-3-11 , phi-11-19))
```
**细节**：`Data.Product` 的 import 从 `using (_,_)` 扩为 `using (_×_; _,_)`；
元组用**显式括号**（`_,_` 无 fixity 声明 ⇒ 默认非结合，写成链式 `a , b , c , d` 会 Parse error ——
这正是本次 fixity 那条经验在实践中的又一次生效）。
回执 `2f5e491d0c30…`（exit 0，3.0s）。

### 7.6 已知假阳性类（保留待人工判定）

- **语料锚**：`LatticeMembrane.agda:24-25` 的 `word_5` / `word_72` —— 头注释写明 `-- 语料锚 (word_5, word_72):`，是外部语料标签，不是符号承诺。形状与真符号**无法区分** ⇒ 只能人工过（Tier-1 总数只有 5 条，成本可忽略）。
- 小节/层级标签（如 `P3-C`）已被 `sym_like` 剔掉。

### 7.7 结论

**从「靠用户追问发现」变成「5 条待人工判定」**。当前工作区 Tier-1 = 5 条（3 真错位 + 2 假阳性）。
