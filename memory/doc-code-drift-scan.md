# 文档承诺 ↔ 代码存在性 扫描器（Tier-1/2/3）

**工具**: `engineering/tests/doc_code_drift.py`（只读；oracle 回执 `980c221a373d540f73a67cf2d84ec424ac8f87863f71368bae9245f1bc67e3eb`，domain=points=8691）
**最近一次结论（2026-09-10）**: 库内 557 个 `.agda`；Tier-1 符号错位 **2**（均为已知语料锚假阳性）；Tier-2 未命中 284（快照 136 / spec 148）；Tier-3 路径异常 1098（悬空 132 = spec 77 + snap 55；已迁移 20 = spec 16；旧名引用 63 = spec 60；短引/重名 883 **不算错位**）。

## 0. 一句话
**文档说的话，机器能查的就那三类**：符号名在不在代码里（Tier-1/2）、文档写的那条 `.agda` 路径在不在（Tier-3）、以及符号归不归它声称的那个模块（归属型断言，139/139 全对，无错位）。三类之外（语义不符、规则不可执行）本工具**抓不到**，别把"扫描通过"当成"文档正确"。

## 1. 分层的可靠性梯度（重要）
| 层 | 判据 | 可靠性 | 实测规模 |
| --- | --- | --- | --- |
| **Tier-1** | `.agda` **头注释**里承诺的符号名 | 高（说话人是代码自己） | 82 候选 / 错位 2 |
| **Tier-3** | 文档引用的 `.agda` **路径**存在性 | **高（无歧义）** | 1098 条 |
| Tier-2 | `docs/*.md` 反引号里的标识符 | **低（只能当候选清单）** | 7511 候选 / 未命中 284 |
| （未做成）归属型断言 | 「符号 X 属于模块 M.agda」 | 高，但产出率低 | 139 条 / 错位 **0** |

**结论**：要判定"文档错没错位"，**看 Tier-1 与 Tier-3，不要看 Tier-2 的总数**。Tier-2 是线索池，不是判决。

## 2. 「快照 vs 承诺」——不去分开会犯的错
同一条「文档写了 X，代码里没有」，在两类文档里含义**相反**：

- **承诺类（spec）**：文档描述**当下**代码应有的样子 → 未命中 = **错位**，要修。
- **快照类（snapshot）**：文档记录**某个时点**的状态 → 未命中 = **历史引用**，**改了就是篡改历史**。

判据（`doc_class` / `doc_reason`，三条都是机械的）：
1. 路径 `docs/line-audit/`（47 份「逐模块审计记录」）；
2. **文件名含日期**（`*_2026-04-24.md` 三份就占 47 条未命中）；
3. 头部 2000 字内含「审查日期 / 审计记录 / 审查范围 / 截至 / 快照 / snapshot」等时点标记。

反例警示：`docs/MATH-COMPLETENESS-REVIEW.md` 头一句就是「审查日期 2026-04-27 · 审查范围 Agda 文件 **79** 个」——**当时 79，现在 557**。把它的历史名当错位去"修"，等于用今天的代码去涂改昨天的审计。

## 3. Tier-2 未命中的四个真实来源（量过，别再猜）
1. **外部生态**：Agda 语言参考、`agda-mode`/`agda-algebras`/`agda-unimath`（包名）、1Lab README、Lean 项目（`fermats-last-theorem`/`native_decide`）→ 由 `EXCLUDED_DOCS` 排除。
2. **Python 工程轨**：`zhonglv_closure`（23 个 .py 里都有）、`chiral_beta`、`emotional_polarity`。⚠ **只覆盖 7/115**——所以"建 .py 索引就能消掉"是**假的**：那些名字在 Python 轨也找不到，是更早的设计名。
3. **历史名**：`jac_*`、`zhonglv_closure`（12 份文档提到、代码 0）、`Sovereign-Base` 时代的分层名。
4. **形状噪声**：公式片段（`ac-bd`）、反例引证（`chern2Proof = refl` 作反面教材）、路径串（`/data/work/...`）、我自己的措辞。

⚠ **被实测否掉的两个假设**（写下来免得再犯）：
- 「纯 snake_case ⇒ 外来符号」：**否**——本库代码自身有 49 个 snake_case 标识符。
- 「建 Python 索引能消掉大半」：**否**——只覆盖 7/115。

## 4. Tier-3 五分类（哪一类才是错位）
| 分类 | 含义 | 算错位? | 实测(spec) |
| --- | --- | --- | --- |
| `dangling` | 文件根本不存在 | **是** | 77 |
| `moved` | 写了路径却只靠 basename 命中 ⇒ 文件被搬走 | **是** | 16 |
| `renamed` | 旧名 `jac_X.agda`，规则=去 `jac_` 前缀 → `Problem/**/X.agda` | **是** | 60 |
| `shortform` | 文档就写文件名（`T6.agda`） | 否 | — |
| `ambiguous` | 只写文件名且库内重名（≥2） | 否（信息不足） | — |
| | | `shortform+ambiguous` 合计 | 883 |

解析必须容忍文档里实际出现的 **5 种写法**：`Physics/NSE.agda`（相对 Sovereign）／`src/Sovereign/.../X.agda`／`../../src/...`／`Sovereign.Structology.A4Group.agda`（**点号模块名又加 `.agda`**）／`./src/...`。最后退化到 basename。

## 5. 两个自身 bug（都会**虚报**，记下来）
1. **重复 relpath**：`agda_paths_for` **已经**返回相对 ROOT 的 `src/...`；再套 `os.path.relpath(p, ROOT)` 会按 **CWD**（`engineering/tests`）变成 `engineering/tests/src/...`，精确匹配恒失败 → 228 条虚报成 860 条。
   （原型侥幸没错，是因为它用 `endswith` 后缀匹配——后缀能穿过坏前缀。）
2. **glob 跟随符号链接**：`src/Sovereign/Algebra/Jacobian/_standalone -> /data/work/dissertation/Jacobian`（**外部论文目录**）。`glob(recursive=True)` 跟随它 → 索引混入 32 个外来 `.agda`，557 虚报成 589，并制造 **41 组重名 basename**，把「只写文件名」的引用全打成悬空。`find`（默认不跟随）与 `glob`（跟随）行为不同，是这个 bug 藏这么久的原因。

## 6. 本轮修掉的真错位（每条都核过）
| 文档 | 问题 | 处理 |
| --- | --- | --- |
| `docs/duodecimal/README.md:125` | 引 `Dihedral/ShortExactSequence.agda`：不存在，且 `git log --diff-filter=AD` 为空（**从未入库**，工作区草稿被删） | 标为失效指路；改指绿版 `GroupTheory/DuodecClockProperties.agda`（`quot-alpha-kernel`/`quot-size`）与 `NormExactSequence.agda` |
| `docs/duodecimal/13-flt-analysis.md §9.2` | 两条 `NormCollapse` 路径**都不存在**（真身在 `Algebra/NormCollapse.agda`）；且 A–D 四条定理标「⏳ 待办」**实际已完成** | 重写：给出 A→`FermatL1.nonzero-square:41`、B→`pow3-odd:77`、C→`pow3-even-channel:100`、D→`GF9.gen-generates-all:539`；基础件 `FermatL0.pow3:45` |
| `docs/NavierStokes/…初诊.md:5`、`docs/creation-law-from-gf3.md:407` | `Physics/NSE.agda` 已迁至 `Problem/NavierStokes/NSE.agda` | 改路径 |
| `docs/cross-level/PROJECT-STATUS.md:130` | `agda src/Sovereign/Constitution.agda`（不可执行） | 改 `src/Sovereign/AI/Constitution.agda` |

**归属型断言 139 条 0 错位** —— 「符号在库里但不在所引模块」一条都没有。这是**正面结论**，说明文档的模块归属是可信的。

## 7. 遗留（人工，别指望机器）
- spec 悬空 **77 条 / 59 个不同路径**，其中 **39 个从未入库**（= 文档自造的计划名，不是错位而是"计划"）；20 个曾入库后被删（`jac_*` 为主，已由 `renamed` 单列）。
- spec 旧名引用 **60 条**：`jac_X.agda` → `Problem/**/X.agda`，18/18 已机械对上，可一次批量改。
- Tier-2 的 B 类（语义不符：名字存在但含义变了）与 C 类（规则不可执行，如当年的 `fixity` 附录规则）**本工具抓不到**，只能人工审核。

## 8. 用法
```bash
cd engineering/tests
PYTHONPATH=<oracle-kit> python3 doc_code_drift.py --tier 3     # 默认：全量 + Tier-3 明细
python3 doc_code_drift.py --tier 1                             # 只看高置信（快）
python3 doc_code_drift.py --all-docs                           # 不排除外部生态文档
python3 doc_code_drift.py --rev HEAD                           # 回放历史提交（回归测试）
```
**回归测试基线**：`--rev HEAD` 必须复现当时已修的两条 Tier-1 错位（`mixedOp-power-add` / `dc-order-12`），说明扫描器确实能抓到已知错位——这是判"工具是不是摆设"的对照实验。
