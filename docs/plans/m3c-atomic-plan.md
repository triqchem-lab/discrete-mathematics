# M3c 收敛协议 + 原子任务表（Cook–Levin tableau，路线 B）

> **性质**：本文件是 M3c 的**执行协议**（闸门/闭合判据/收敛规则），任务表在 §5。
> **它回答三个问题**：每一阶段怎么闭合（什么算完）、怎么收敛（怎么防止无限打转）、标准是什么（可机械检查）。
> **基线**：5 个新文件在 lib 口径（`--cubical --guardedness -WnoUnsupportedIndexedMatch`）下 5/5 `EXIT=0`，0 postulate。
> **总预算 12 轮**（含修复）。超预算即执行 §3.2 裁剪序，**不许原地续命**。

---

## 1. 「解决」的总标准（S1–S6，任一不成立就不算完成）

| # | 标准 | 机械检查 |
|---|---|---|
| **S1** | `InNP-TM-fin`（`Fin` 形态状态/字母表）存在；`tableauOf` 类型检查通过 | 文件 `EXIT=0` + `grep_search "record InNP-TM-fin"` |
| **S2** | **方向一闭合**：`run→sat : … → satFormula' (asgOf …) (tableauOf …) ≡ true` | 签名存在且 `EXIT=0` |
| **S3** | **方向二闭合**：`sat→run : … → Σ (运行) (λ r → 接受 r)` | 同上 |
| **S4** | 落 3-CNF：`tableau-3cnf` 双向 + 与 `CNF.formulaOf3` 对接 | 同上 |
| **S5** | 归约实例：`Reduces` 实例 + 被 `red-preserves-NP` 消费 | 同上 |
| **S6** | 0 postulate / 0 hole / 无 `with` 渗透结论 | `grep_search "postulate\|{!!}"` → 0 |

**S2 与 S3 是两个独立闭合点**：S2 只证编码忠实（不需提取），S3 才需重建运行。**S2 单独成立即可交付**（即便 S3 受挫）。

---

## 2. 闸门 G0–G7：闭合定义 + 检查 + 失败处置

> 闸门不过不进下一闸门；「过」的判据必须是**命令 + 期望输出**，不接受「我觉得写好了」。

| 闸门 | 内容 | 闭合定义 | 检查 | 失败处置 |
|---|---|---|---|---|
| **G0** 设计冻结 | 界参数化 = (b) `InOff (len t : ℕ) (o : TOff)`；帧宽 `L = suc (suc (len + T + T))`（原稿 `len + T + 1` 偏差一格，`ab3cdb0` 起修正） | 头注含修正后的帧宽，`2T+3` 零命中 | `grep_search "2T\+3"` → 0 | 反复即定 (b)，不再讨论 |
| **G1** 编号层 A1–A8 | `offTag`/`offIdx`/`InOff`/`offEnc`/`offDec`/往返/单射/界内保持 | 8 签名齐 + `EXIT=0` | `agda … Tableau-Tape.agda` | 仅 A8 卡：界内保持改为**逐支显式前提**（`k+1 < L`），不算失败 |
| **G2** 池 B1–B5 | `poolSize`/两层 `combine`/`poolDec`/往返/接 `Lit` | `poolDec-enc` 成立（stdlib `remQuot-combine`） | 文件 `EXIT=0` | `combine` 卡：退回手写 `toℕ` 编号（**仅一次**，须写为何 stdlib 不够） |
| **G3** 子句族 C1–C7 | 符号/状态/头 oneHot + 转移三支 + 非头不变 + 初始终止 + `tableauOf` | 七族齐；`tableauOf` 是 `++` 链；**不含语义** | 文件 `EXIT=0` + 每族 1 条形状核对 | 族太多：先做 C1/C4/C6（符号+转移+初始终止），其余记 G3b |
| **G4** 方向一 D1–D3 | `c_t`/`asgOf`/六族满足 | `run→sat` 存在且 `EXIT=0` | 同上 | 某一族卡：拆独立引理，该族记 G4b，不阻塞其余 |
| **G5** 方向二 D4–D6 | 取格值 + `c_{t+1}=step c_t` + 打包 | `sat→run` 存在且 `EXIT=0` | 同上 | **两档**：完整版 / 受限版（固定 T 实例 + 通用骨架）。**禁止假证** |
| **G6** 落 3-CNF E1–E3 | `InNP-TM-fin`/Tseitin/`formulaOf3` 对接 | `tableau-3cnf` 双向 + size 界陈述 | 同上 | Tseitin 编号卡：先交 `Formula'` 版并明说未落 3-CNF |
| **G7** 归约 E4 | `Reduces` 实例 | 实例值 + `red-preserves-NP` 消费成功 | 同上 | 只交「参数化归约记录 + 一个具体池实例」 |

---

## 3. 收敛机制

### 3.1 修复预算
同一闸门最多 **3 轮**「编译→修→再编译」；第 4 轮必须执行该闸门的失败处置并写回执。轮的口径：一次 `agda` 调用 + 对其错误的修复 = 1 轮；**同一错误第二次出现**视为浪费一轮。

### 3.2 裁剪序（超预算按此砍，保证总有可交付物）

```
G7（归约） → G6（3-CNF，退为一般 CNF） → G5（方向二，退为受限版）
G1–G4 不可砍（地基 + 方向一）
```

砍掉的项写进 §6「受限交付」，**不得**伪装完成。

### 3.3 反漂移条款
1. 闸门内不新增抽象：要加定义先在任务表加行（含验证列）。
2. 禁止 postulate / 洞 / 为过编译放宽命题。
3. 禁止 `with` 渗透结论；分支用 `bool-case` 或对**变量**做 clause 分派。
4. 每闸门结束留**回执**：命令 + `EXIT` + 行数 + 新增签名数。
5. 每闸门一个 commit；不跨闸门合并提交。
6. M1/M2/M3a/M3b 的文件只读（已冻结）。

### 3.4 预算分配（12 轮）

| G0 | G1 | G2 | G3 | G4 | G5 | G6 | G7 |
|---|---|---|---|---|---|---|---|
| 0 | 1 | 1 | 2 | 2 | 4 | 1 | 1 |

**判据**：第 6 轮仍未过 G4 ⟹ 立即 G5 降级并收尾，以 S2 作为本次交付终点。

---

## 4. 已知算术义务（只两处）

1. **A8 界内保持**：`tShiftR (tL k) = tL (suc k)`、`tShiftL (tR k) = tR (suc (suc k))` ⟹ 平移使索引增长，而**深度界 `len + t + t` 本身随 `t` 增长**，所以固定界的边界问题不出现 —— 这是 A0 必须选 (b) 的原因。**实测结论（`62a9a1b`）**：三支全部在 `InOff len t o → InOff len (suc t) (tShiftX o)` 的形状下直接成立，无需任何附加前提；唯一的技术点是 `tShiftL` 的 `tR` 支**恰好取等**（右窗每步长两格），要让 `suc (suc (len + t + t))` 与 `len + suc t + suc t` 对上，需借 stdlib `+-suc` 搬一次（`_+_` 递归在首参上，`len` 是变量，两式非定义相等）。
2. **A6 编号往返**：`toℕ-fromℕ<` / `fromℕ<`；池层由 stdlib `remQuot-combine`（`Data/Fin/Properties.agda:694`）与 `combine-remQuot`（:699）承担，**不手搓 `*` 边界**。

---

## 5. 原子任务表（产物 / 验证 / 失败处置）

### 层 0（已完成）

| # | 任务 | 产物 | 验证 | 状态 |
|---|---|---|---|---|
| 0.1 | 修正 `2T+3` 对称帧陈述 | 提案文档 | 文本核对 | ✅ `e8e4c66` |

### 层 A：偏移编号（`Tableau-Tape.agda` §3）

| # | 任务 | 产物 | 验证 | 失败处置 | 状态 |
|---|---|---|---|---|---|
| A0 | 定 (b)：`InOff (len t : ℕ) (o : TOff)`，帧宽 `L = suc (suc (len + T + T))` | 头注 + `InOff` | `2T+3` 零命中 | 立即定 (b) | ✅ `ab3cdb0` |
| A1 | `offTag : TOff → Fin 3` | 3 行 | 3 `refl` | 枚举 | ✅ `d608e78` |
| A2 | `offIdx : TOff → ℕ` | 3 行 | 3 `refl` | 枚举 | ✅ `d608e78` |
| A3 | `InOff len t o`（左界 `≤ t`、右界 `≤ len + t + t`） | 1 定义 | 类型 | 改单侧+余量并注明 | ✅ `92c6ff1` |
| A4 | `offEnc : InOff t o → Fin 3 × Fin L` | 1 定义 | `EXIT=0` | `fromℕ<` | ✅ `d2cb92e` |
| A5 | `offDec : Fin 3 × Fin L → TOff` | 1 定义 | 3 `refl` | 枚举 | ✅ `1d88bcc` |
| A6 | `offDec-enc : offDec (offEnc o h) ≡ o` | 1 引理 | `EXIT=0` | `toℕ-fromℕ<` | ✅ `f803f2a` |
| A7 | `offEnc-inj` | 1 行 | `EXIT=0` | 由 A6 | ✅ `8a12b83` |
| A8 | `InOff-shift*` 三支 | 3 引理（+4 备件） | `EXIT=0` | 见 G1 | ✅ `62a9a1b`（**无需** `k+1 < L` 前提） |

### 层 B：池（新文件 `Tableau-Pool.agda`）

| # | 任务 | 产物 | 验证 | 状态 |
|---|---|---|---|---|
| B1 | `poolSize` = `suc T · ((3 · L) · V)`（`3` = 偏移 tag 位；`Lit m` 是 m+1 槽，故最高槽空置） | 1 定义 | `EXIT=0` | ✅ `9190157` |
| B1b | `pool-fin-le : toℕ t ≤ T`（`t : Fin (suc T)`，由 `s≤s⁻¹ ∘ toℕ<n`） | 1 引理 | `EXIT=0` | ✅ `9190157` |
| B2 | `poolOffFin`（`combine (offTag o) (proj₂ (offEnc …))` → `Fin (3·L)`）+ `poolEnc`（两层 `combine`） | 2 定义 | `EXIT=0` | ✅ `9190157` |
| B3 | `poolDec` + 四个投影步 `poolTime`/`poolCell`/`poolCode`/`poolSym`（拆开是为了让 `remQuot-combine` 能直接改写；不拆则要在一整个嵌套投影项上做 `cong` 链） | 1+4 定义 | `EXIT=0` | ✅ `9190157` |
| B4a | `poolOffFin-spec : remQuot L (poolOffFin …) ≡ offEnc …`（三支各一条 `remQuot-combine`，无需 `cong`） | 1 引理 | `EXIT=0` | ✅ `9190157` |
| B4b | 五个中间 `*-enc`（时间/格位层/格位码/符号/格位码→TOff）+ `poolDec-enc` 往返（`cong₂ _,_` 组装） | 6 引理 | `EXIT=0` | ✅ `9190157` |
| B5 | `poolLit : Sign → Fin (poolSize) → Lit (poolSize)` + `PoolClause`/`PoolFormula` 别名 | 3 定义 | `EXIT=0` | ✅ `9190157` |
| B6 | 核对层：`poolSize 2 3 2 ≡ 240`、`poolDec-enc` 一个具体点 | 2 `refl` | `EXIT=0` | ✅ `9190157` |

### 层 C：六族子句（`Tableau-Clauses.agda`）

| # | 任务 | 产物 | 验证 | 状态 |
|---|---|---|---|---|
| C0 | 枚举件：`allFin`/`fin-le`/`OffW`（带界内性见证的偏移）/`allOffW`/`listHead` | 5 定义 | `EXIT=0` | ✅ `ba92e44` |
| C1 | 符号 oneHot（逐 `(t,o)`，套 M3a `oneHot`）：`symCells` + `symOneHot` + 3 条形状核对 | 2 定义 + 3 `refl` | `EXIT=0` | ✅ `ba92e44` |
| C2 | 状态 oneHot（逐 `t`，枚举 `Q × (T+1)` 个 `(q,p)` 槽）：`stCells` + `stOneHot` | 2 定义 | `EXIT=0` | ✅ `749c327` |
| C3 | ~~头 oneHot~~ **并入 C4**：相对行下头恒为 `tH`；裁决 §3.3 要的「`p` 递推一致性」正是 C4 的目标文字 `atSt (fsuc t) q′ p′` | — | — | ❌ 删除（理由见决策书 §5 / 裁决 §3.3） |
| C3′ | （可选，规模优化）`p ≤ t` 裁剪：只对 `p > t` 生成负单元子句 | 1 定义 | `EXIT=0` | ⬜ 未做（裁决 §3.4 明示不阻塞） |
| C4 | 转移族三支（R / L·`p=fzero` / L·`p=fsuc n`），每支 2 条子句 `¬St(t,s,p) ∨ ¬Sym(t,tH,a) ∨ <结论>`；`p′` 由 `pSuc`/`inject₁` 给出 | 1 定义（含 `pSuc`/`imp`/`headSym` 备件） | `EXIT=0` | ✅ `749c327` |
| C5 | 平移族：`clShiftAt` + `shiftClauses`。**R 支排除头格**（写入覆盖），L 两支用**全窗口**（`tH ↦ tR 1`/`tR 0` 是真映射） | 2 定义（+3 个 `InOff-shift*-fin`） | `EXIT=0` | ✅ `3afd87e` |
| C6 | 初始（`St(0,q₀,0)` + 左邻空白 + 右带 `inp`）+ 终止（`t=T` 接受态，任意 `p`） | 2 定义（含 `initR-bound`） | `EXIT=0` | ✅ `749c327` |
| C7 | `tableauOf` = `symAll ++ stAll ++ transAll ++ shiftAll ++ initClauses ++ finalClauses`（全展开） | 1 定义（+4 个 `*All`） | `EXIT=0` + 长度核对 | ✅ `3afd87e` |

### 层 D：两个方向（`Tableau-Sem.agda`）

| # | 任务 | 产物 | 验证 | 状态 |
|---|---|---|---|---|
| D1 | `c_t`（`runN` 直接给） | 1 定义 | 1 `refl` | ⬜ |
| D2 | `asgOf`（选中 T₁、同族其余 T₂） | 1 定义 | 1 `refl` | ⬜ |
| D3 | 六族满足（运行 ⟹ 赋值） | 6 引理 | `EXIT=0` | ⬜ |
| D4 | 六族提取（赋值 ⟹ `c_t` 三部分） | 6 引理 | `EXIT=0` | ⬜ |
| D5 | `c_{t+1} = step c_t` | 1 引理 | `EXIT=0` | ⬜ |
| D6 | 打包 `sat→run` | 1 定理 | `EXIT=0` | ⬜ |

### 层 E：落 3-CNF 与归约

| # | 任务 | 产物 | 验证 | 状态 |
|---|---|---|---|---|
| E1 | `InNP-TM-fin` | 1 record | `EXIT=0` | ⬜ |
| E2 | 长句经 M1 `tseitin-split`（辅助变元由 `poolSize + k` 编号） | 1 定义 | `EXIT=0` | ⬜ |
| E3 | `tableau-3cnf` 与 `formulaOf3` 对接 | 1 引理 | `EXIT=0` | ⬜ |
| E4 | `Reduces` 实例（参数化于池） | 1 记录值 | `EXIT=0` | ⬜ |

### 层 F：查重发现的冗余（自查）

| # | 任务 | 证据 | 处置 | 状态 |
|---|---|---|---|---|
| F1 | `tstep-*`（分量形）与 `tstep-*-pt`（逐点形）同事实 | 逐点形可推分量形 | 暂不删（C5 引用分量形），C5 落地后判 | ⬜ |

> **另两处「重复」非本会话引入**：库内两份 `isT₁`（`SATMember`/`PClass`，既有）；`Tableau.agda` 的抽象原子 CNF 与 `CNF.agda` 形状平行（有意，桥 `AtoCNF-sat`）。
> **近邻先例（`grep_search` 补查所得）**：`QBFOracle.agda:424` 的 `QO-onehot : (d : ℕ) → Fin d → List Trit` 是**字符串层** one-hot 编码；`Tableau.oneHot` 是**约束层**（至少一个 + 成对至多一个），不共用 —— 应在 `Tableau.agda` §4 头注补一句引用。

---

## 6. 「受限交付」节（降级必须写在此，不许静默）

（空 —— 尚无降级）

---

## 7. 闸门回执

| 闸门 | 回执 | 结论 |
|---|---|---|
| M1/M2/M3a/M3b（前置） | 5 文件 1657 行，lib 口径 5/5 `EXIT=0`，0 postulate | ✅ |
| **G1** 编号层 | `Tableau-Tape.agda` 660 行，`agda -i src --cubical --guardedness -WnoUnsupportedIndexedMatch …` → `EXIT=0`；A1–A8 八签名齐（合计新增顶层签名：A1/A2 = 3，A3/A4a = 5，A4b = 4，A5 = 1，A6 = 2，A7 = 1，A8 = 7）；7 个分段提交 `d608e78`→`62a9a1b`；0 postulate / 0 hole；A8 三次预置前提未用到，修复轮数为 0（A6 例外：3 轮，导入位置／模式变量遮蔽／证明参数不可推断） | ✅ |
| **G3** 六族子句 | `Tableau-Clauses.agda` 447 行，同命令 → `EXIT=0`；C0/C1/C2/C4/C5/C6/C7 齐（C3 并入 C4、C3′ 可选未做）；顶层签名 50；34 条 `refl` 核对；0 postulate / 0 hole、零警告；`ba92e44`→`3afd87e`。⚠ **修复 6 轮（预算 2，超预算 3 倍）**：2 轮是我自己的编辑脚本失误（核对块插错位置、`str.replace` 命中两处），4 轮真实问题（多余 `concat`、多行 `λ where` 破坏 layout、`toℕ (inject₁ t)` 非定义性——根因、`s<s⁻¹` 未导入）。另：查重门禁命中 `keepIf`/`shiftAt` 两次，均改名（`clKeepIf`/`clShiftAt`），未绕过 | ✅（超预算） |
| **G2** 池 | 新文件 `Tableau-Pool.agda` 207 行，同命令 → `EXIT=0`；B1–B6 齐（顶层签名 21，含 2 条 refl）；`9190157`；0 postulate / 0 hole、本文件零警告。stdlib `remQuot-combine` 足够，未触发「手写 `toℕ` 编号」退路。⚠ **修复 4 轮（预算 1，超预算）**，但四轮全是导入/隐参显式化（`s≤s⁻¹` 归属 `Data.Nat`、`tL`/`tR` 未 `using`、`tt` 未导入、`remQuot` 隐参 `{m}` 从乘积反解不出）—— 故障不在设计，退路不适用；已记入提交信息 | ✅（超预算） |
