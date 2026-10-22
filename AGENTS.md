# 律算合一 (Sovereign Mathematics) — AGENTS.md

离散数学形式化验证: GF(3) 三进制 + T⁶ 离散环面 + CRT 谐波谱 + 主权 LCM 商空间。
Agda 形式化证明 + Python 工程验证双轨制。

## Project
- 技术栈: Agda 2.9.0-nightly（**唯一默认 = `/opt/agda/2.9.0/bin/agda`**——系统层配置在 `math-proof` preset 的 `impl/local-paths.json` 的 `agdaBin`，env `SOVEREIGN_AGDA` 可覆盖；`~/.local/bin/agda` 与 `/usr/local/bin/agda` 都是指向它的**软链/alternatives 别名**（同一二进制 sha256 `649e2888…`，不是第二份）；`/opt/agda/2.8.0.2` 是官方 2.8.0.2 版，**仅**用于内核判据的负控制——⚠ **异版本**：负控制成立必须校验**报错内容**为判据预期（`UnsolvedConstraints` + `R1 ≡ R2` + `stuck`），只看 exit code 会把版本差异误判成区分力（2026-10-22 用户质疑定案）；实测 2.8.0.2 报错匹配 ✓，但最佳负控制仍是**同版本线（2.9.0-nightly）未打补丁构建**）, standard-library-2.4, cubical-0.9, agda-categories, agda-algebras
- 库注册: `sovereign.agda-lib` (flags: `--guardedness --cubical -WnoUnsupportedIndexedMatch`, include: `src`) — **2026-10-02 收编**：`--cubical` 上收为全库默认（承重：44 个文件级 cubical 模块 + 73 个依赖者），原同名 `src/Sovereign.agda-lib` 已删；文件级 `--rewriting` 纪律不变（REWRITE 传染性照旧）
- 入口: ~~`src/Sovereign/All.agda`~~ 已取消 (2026-09-07 去聚合化, 模块独立编译); 全库 **823** 个 `.agda`（`src/Sovereign` 实测 2026-10-19；迁移结案时记为 803，之后有新增）
- Python 轨道: `engineering/software/sovereign_core/` (零外部依赖)
- Git: 单分支 `master` → github.com/triqchem-lab/discrete-mathematics

## Commands（均已实测，注意当前状态）
- 全量编译: ~~`agda src/Sovereign/All.agda`~~ All.agda 已取消; 改为绿链/模块独立编译 (群论链/FLT链 gate, 见 engineering/check_*.sh)
  `Structology/HolographicSpace.agda:26` 等少数模块未开 `--rewriting`，却 import 带 `--rewriting` 的 `Base/Trit.agda`。
  **这是编译器传染性 flag 强制检查与项目代码的兼容性问题，不是代码缺陷**（全库 335/342 模块已统一 `--rewriting`）。
  项目既定处理（记忆 agda-stdlib-2-4-fixes §1）: 命令行不带 `--rewriting`，文件头保留 `{-# OPTIONS --rewriting --guardedness #-}`。
- 单模块检查: `agda src/Sovereign/Base/Trit.agda` ✅（仅 UnreachableClauses 警告）
- 测试集: **`make test` 是 no-op** — `test/` 目录遮蔽了 make target。必须用 `make -B test` ✅（17 模块，ALL_PASS）
- Python 测试: 在仓库根运行 `python3 -m pytest engineering/tests/` ✅ 29 passed
  （`cd engineering` 后运行会因 `engineering` 包不在 path 而 collection error）
- 结构 lint 门禁: `engineering/check_structure_lint.sh [ROOT]`（默认 `src`；**不编译**，静态查
  「module 名≠路径 / 非法目录分量（含 `-`）/ 非法标识符（`_` 接字面量）/ `where` 滥用（挂在
  postulate·data·record·类型签名上）/ `?` 洞（WARN）」）。**为什么需要**：`check_all_modules_parallel.sh`
  只扫 `src/Sovereign`，其它目录里的草稿会「从未编译、也从未进门禁」——2026-09-13 的实例
  （`src/{01-electric-12d,02-magnetic-24d,03-neutral-144d}`）已归档到 `archive/civlayers-2026-07/`。
  修法：路径与 module 名对齐；`where` 只留给函数子句。
- 八要素索引（**非门禁**）: `engineering/index_presentations.sh [ROOT]`（默认 `src`）——
  **索引工具，不是验证工具**。列出所有 `Presentation` 实例（形如 `X : Presentation A`）及其实例
  字段**齐 / 缺**、白名单排除（`Techniques/`、`/archive/`）。字段模板从
  `src/Sovereign/Algebra/Presentation.agda` 的 record **运行时提取**（不硬编码 ⇒ 增删字段无需改脚本）。
  输出带免责声明、**不判「通过 / 不通过」**：「字段齐全」只表示**形式**上提供了字段，
  **不**表示 `assoc` 成立、`rigidity` 确由 `galoisConjugate` 诱导 —— 那属 Agda 类型检查器与
  `proof_dag` 台账的权威（权威顺序：类型检查器 > 台账 > 本索引）。退出码 `0` = 索引完成
  （不代表任何数学结论），`2` = 用法错误。用法与输出解读详见
  `docs/maps/八要素统一形状-2026-10-14.md` §8.7。
- 编译产物: `_build/`、`*.agdai`（gitignored），不要删除

## Architecture
- `src/Sovereign/Base/`（**17** 个 `.agda`）— GF(3) 原语 `Trit`/`_⊕_`/`_⊗_`/`negate`、不变量（POLAR=144, TORUS=46, CHERN=±2）、`Base/Coding/Trit`（类型级编码）
- `src/Sovereign/Foundation/`（**31** 个 `.agda`）— L0 公理层：数字根、损益、归零、离散存在、元数学红线
- `src/Sovereign/Infrastructure/`（**26** 个 `.agda`）— 跨切带（豁免 import 单调性）：Engine/Trust/Verify/审计聚合/宪法审查、`Projection/`、`TwoViewRewritten`
- `src/Sovereign/Algebra/`（**277** 个 `.agda`，**17 个概念子目录、无直属文件**）— L2 结构层：`FieldTower/`(27，**GF(3^k) 域塔** GF9/GF27/GF81/GF243/GF729 + Frobenius)、`Jacobian/`(58)、`GroupTheory/`(52)、`Analytic/`(35)、`RingTheory/`(32)、`Combinatorics/`(15)、`NumberTheory/`(14)、`Holographic/`(12)、`LinearAlgebra/`(7)、`UniversalAlgebra/`(7)、`Automata/`(5)、`Dihedral/`(5)、`Character/`(2)、`Lie/`(2)、`Quantum/`(2)、`Representation/`(1)、`Spectral/`(1)
- `src/Sovereign/Synthesis/`（**168** 个 `.agda`，**15 个概念子目录、无直属文件**）— L3 合成层：`Homotopy/`(25，含 **分水岭定理** 相关 `T6`/`T6Homotopy`)、`Combinatorics/`(24)、`A4/`(19)、`CRT/`(18，波系统/Hensel/TQ10)、`Physics/`(16)、`Analysis/`(13)、`Geometry/`(10)、`NumberTheory/`(10)、`Topology/`(9)、`Graphs/`(8)、`FieldTower/`(6)、`Format/`(5)、`Representation/`(3)、`DiscreteCubical/`(1)、`Model/`(1)
- `src/Sovereign/Application/`（**304** 个 `.agda`，**25 个概念子目录、无直属文件**）— L4 应用层：`Problems/`（BSD/Kakeya/ABC/FLT/RH/NavierStokes/YangMills/PvsNP/Hodge/Langlands/Sqrt2）、`Physics/`(80)、`Analysis/`、`Geometry/`、`Homotopy/`、`Morse/`、`CrossDomain/`、`Topology/`、`Algebra/`、`Coding/`、`Coupling/`、`Diagnosis/`、`ML/`、含 `ABCL1` 壁垒定理 / `KakeyaPathology` 三重完备性
- 纯文档/参考目录（**无 `.agda`**，不得当代码目录用）：`Arithmetic/`（4 `.md`）、`Constitution/`（README）、`Problem/`（2 `.md` + 6 `.pdf`，含 IUTT 参考）
- **层序（依赖单调性，禁反向）**：`Foundation(L0) → Base(L1) → Algebra(L2) → Synthesis(L3) → Application(L4)`；`Infrastructure` 为跨切带（豁免单向律）。判据见 `docs/migration/五层架构文档.md`。
- **分类规范**：`docs/decisions/目录结构-三库对照-2026-10-19.md`（对照 agda-unimath/stdlib）。**三层层内细分已全部完成（2026-10-19）**：`Application/` 304→25 子目录、`Algebra/` 277→18、`Synthesis/` 168→15，**三层直属文件均为 0**；逐桶内核校验 24/24 + 33/33 绿（4 个 Laurent 模块已用 `--no-fast-reduce` 修好），**全库门禁 823/823 全绿**。
- **目录重组台账**：`docs/migration/目录重组-进度.md`（流程 5 步 + 回执 + 教训）、`目录重组-映射-2026-10-19.csv`（304 行 old→new 权威映射）
- 文档: `docs/`（架构/审计/路线图，中文）、`maps/` M1–M6、`memory/` 索引

## Conventions
- 注释一律中文；模块头部注释先说明数学背景（如 GF9 = GF(3)[x]/(x²+1)）
- Unicode 标识符: `T₀ T₁ T₂`、`⊕ ⊗`、`≡ ≅`、`⊎`
- 证明风格: 有限类型逐 case 的 refl 证明；目标零 postulate（README 的 85 文件/72 零 postulate 数字已过时）
- **非必要不用 REWRITE**（2026-10-10 人类裁决入册）: REWRITE 是**传染性强的元层工具**（全库 537 个模块声明 `--rewriting`，仅 8 个真含规则，其余为传染强制）；新增 REWRITE 须同时满足 ① 链式修复（命名引理 + let 类型注解）已验证无效 ② 属 mod-helper 类内核资源爆炸 ③ 逐条人类授权。「不违反 0-postulate」≠「应该用」；refl 层问题（如 `+Assoc`/`assocP`）一律先修链式
- `--rewriting` 是全库标准 (335/342 模块)，承载自定义 REWRITE 规则——**语义完备性设计**，不是补丁:
  - `T6.agda`: `div3k`/`mod3k`/`gf3Toℕ-A4-inv` (4320D 归约, 替代 mod-helper 展开, 避免类型检查 OOM)
  - `XuanwuAbsorption.agda`: `mod46k`/`div46k`/`mod-a+598`; `jac_Pigeonhole.agda`: `decode9-encode9`
  - 合法性论述: `/data/work/docs/wiki/02-geometric-pole.md` C.3.1
- REWRITE 规则传染性: import 带重写规则模块的模块必须自带 `--rewriting`（Agda 保证 subject reduction 的强制检查）。
  少数模块刻意不开（如 `HolographicSpace.agda` 注释: 类型保持 ∀ n 参数化、避免 Fin 归一化展开）——
  由此触发的 InfectiveImport 报错是 **Agda 2.9.0 开发版固有限制/兼容性问题**，非代码缺陷，不要当 bug 修
  - ⚠ **2026-09-14 实测修正（条件比原表述更宽）**：传染源是 **OPTIONS 里的 `--rewriting` 旗标本体**，与模块里**有没有规则无关**。
    对照实测：一个**零规则**、只声明 `--rewriting` 的模块，其下游（只开 `--guardedness`）照样 `rc=42 [InfectiveImport]`。
    计数：全库 **537** 个模块声明 `--rewriting`，其中只有 **8** 个真含 `{-# REWRITE … #-}`；
    DC 链闭包（`Base/Trit` → `Algebra/{GF9,Duodecimal}` → `GroupTheory/{DuodecClock,DayanCore,DCGroup}` 等 9 模块）**规则条数 = 0**，
    `Base/Trit.agda:9` 亦自述「本模块本身不使用 REWRITE 规则」——但库内消费者只开 `--guardedness` 时依旧 rc=42，报错源指着 `Base/Trit`。
  - ✅ **可达成的收益**：把 DC 链闭包 9 个模块做「同内容、改名、仅去旗标」的影子副本后**逐个 rc=0**，
    且只开 `--guardedness` 的消费者 import 整链 **rc=0** ⇒ 这条链上「下游零旗标」可**纯源码层**达成，且**语义风险为零**
    （链内 0 条规则 ⇒ 去旗标只解锁、不破坏）。未做：真改库内那 9 处 pragma（`Base/Trit` 被 300+ 模块 import，需单独任务 + 全量重编）。
  - 证据: `docs/techniques/pgm-assessment.md` Q1/Q1b、dype `docs/theory/PGM-metatheory-and-plan.md` §4「P1 泛化验证」
- 宪法约束（详见 `memory/dual_track_constitution.md`）: 禁浮点数（无理数用定点整数比）、禁 postulate、范畴分离、144/46 全息 π 禁止约分、十二律长度表静态、标准库信任度=0
- 工作区现状: 目录重组后 `GF9` 位于 `src/Sovereign/Algebra/FieldTower/GF9.agda`；`src/_test_irrelevant.agda` 是未跟踪草稿

## Notes

### ★★ 写「新」件前的硬性前置（2026-10-21 上闸，**不是建议**）

> **触发**：本会话实测**三次重复实现** ✗ ——
> ① `DCPresentation.agda`（119 行）漏掉 `Presentation.agda:131` 已有的 `dc-presentation`；
> ② `dc-oblivion-trit/-phase/-joint` 漏掉 `DuodecClock.agda:504` 已有的 `ZeroOblivion`（五字段）；
> ③ 「全库第一个 Presentation 实例」的声明（实为重复）。
>
> **根因**：`bash grep -n "pat" src/某文件.agda` —— **只查了单个文件** ✗ + 长会话忘记已证清单 ✗

**硬性前置（三条，按序执行，缺一条该提交不算完成）**：

| # | 动作 | 判据 |
|---|---|---|
| **0** | **读 `PROVEN.md`**（仓库根） | 里面有「最近 / 最常复用」的已证清单 |
| **1** | **`proof_dag action:"search" query:"<符号/概念>"`** | 台账里查（含对象层） |
| **2** | **DSH `grep` 工具全库查 `src/Sovereign`** | **不是** `bash grep` 单文件 ✗ |

**机器挡点**：`.git/hooks/pre-commit` → `engineering/check_duplicate.sh`
—— 提取 staged 新增的**顶层签名**，若已在**库内其他模块**定义则**拒绝提交** ✓
（绕过：`git commit --no-verify`，须在 `proof_dag journal` 说明理由）

**边界（诚实声明）**：该脚本只查顶层签名，**不查** record 字段 / where 块 / 局部定义 ✗

### ★ 检索方言（`bash grep` 已被机器拦截）

`PreToolUse` 的 `search-dialect-gate.mjs` 会拦**非管道位的 bash `grep`/`sed` 读文件**（exit 2）✓
放行：**管道过滤**（`agda … 2>&1 | grep -c error`）、`sed -i` 就地编辑 ✓

⚠ **闸门对 `git commit -m` 的消息文本也会误判** ✗（消息里含 `grep` / 门禁文件名即触发）——
**规避**：提交消息与 memory 增补走 **`write` 工具落盘 + `git commit -F 文件`** ✓

### ★★ 散文断言规则（2026-10-21 上闸，**不是建议**）

> **触发**：同一会话内、**同一个模块**里连犯两次同类错误 ——
> ① `Pi2dParity` 模块头写「`π₂ᵈ⁺` 至多两类」：实际对应的只有 `par2-Walk⁺`（一个**良定义**陈述），
>    把「良定义」读成了「单射」⇒ 差了一个单射性；
> ② 同模块写「`Ω2Walk G x w1 w2` 只在 `w1`、`w2` 相等时可居留」：把「步的两个 walk 参数**共享图顶点**」
>    读成「两个 walk **相等**」⇒ 假的（`cons2 s (nil2 w2)` 就是 `w1 ≢ w2` 的居留者）。
>
> **共同模式**：模块头 / 台账 note 写了「看起来很自然的事实」，**但代码里没有对应的定理，也没标它是直觉**。
> 后果是**文档比代码说得多**，后续会话（包括自己）会被骗。

**规则（每条可验证的断言必须二选一，没有第三条）**：

| 选项 | 要求 |
|---|---|
| **(a) 有定理** | 断言后面写清**具体的内核定理名**（如「见 `wind-Walk⁺`」），且该定理的**方向/强度**与断言逐字一致 |
| **(b) 无定理** | 显式标 `[直觉·未验证]`，并写明「缺什么才能证」 |

**判据（自查一问）**：把这条断言的「至多 / 至少 / 必须 / 不可能」挑出来，问「它的名字是什么？」
—— 指不出来 ⇒ 一律降级为 (b)。

**为什么是硬性的**：这与「未证不许谓证」同源，只是从**程序层**延伸到**文档层**。
`proof_dag check` 的另一半（「proven 无证据」）管的是台账；本规则管的是**散文**。

### ★★ 路线判断也要标推测（2026-10-21 上闸）

`### ★★ 散文断言规则` 管的是**数学陈述**。本条补上它漏掉的一类：**路线 / 差距判断**。

> **触发**：同一会话内连错两次 ——
> ① 我把「`updAt-comm` 等五项」列成「`π₁ᵈ ≅ (C₃)ⁿ` 五项前置已齐」，暗示只差一项（**高估**）；
> ② 纠正时说「`Ω3Walk⁺` 没有方块 2-胞」（**也是推测**）——核查后发现 `ASTep.slide` **同时涵盖
>    回溯与方块** ⇒ 方块 2-胞本来就在库里（**纠正本身也错**）。

**规则**：写「还差 X」「已有 N 项前置」「只差最后一步」「这条路可行/不可行」时，必须：

| 选项 | 要求 |
|---|---|
| **(a)** | 附上**能证实或推翻它的具体检查动作**（跑什么、看哪个定义、证哪条引理）|
| **(b)** | 标 `[未验证·路线推测]` |

**为什么**：路线判断**本身也是断言**，而且错得更隐蔽 —— 没人会去证「还差一项」，
于是它会一路传下去，污染后续会话的规划。实测代价：本会话因此白走两轮。

**与上一条的关系**：上一条说「断言必须指向内核定理」。这条说：**指不出来的，连路线判断也一样要标**。

### 其他

（待补充）
