# fixity 审核：过去态 vs 未来态（实测否证记录）

**日期**: 2026-09-10 ｜ **oracle 回执**: `b5c619cb9d0182fd07cbf79656936bc0fb0ff951a34383d4a1d1fb2a347463aa`
**可复现**: `python3 engineering/tests/oracle_fixity_audit.py`（在 /tmp 生成探针模块并**真调 Agda**，不碰工作区）

## 结论一句话
两份论证（`infixl` 版 / `infixr` 版）载入的 **11 条事实断言中 10 条被 Agda 实测推翻**；
唯一成立的是「在**定义处**声明 fixity 生效」。**加不加 fixity 是约定取舍，不是正确性问题**——
今天不存在任何因 fixity 缺失而产生的错值。

## 一、实测对照表
| # | 断言 | 声称 | 实测 | 判定 |
| --- | --- | --- | --- | --- |
| ① | Agda 默认 fixity | `infixl 9` | `infix operator, level 20`（**无方向**） | ❌ |
| ② | 无声明时 `a ⊕ b ⊗ c` | 编译通过（静默错值） | `error: [NoParseForApplication]` | ❌ |
| ②b | 同算子连写 `a ⊕ b ⊕ c` | 静默左结合 | 同样 ParseError | ❌ |
| ③ | 定义处声明 `infixl 6/7` | 生效 | 编译通过 | ✅ |
| ④ | 加法类方向 | `infixr` | **infixl 34 / infixr 0** | ❌ |
| ④b | 乘法类方向 | `infixr` | **infixl 27 / infixr 4** | ❌ |
| ⑤ | 「未来态」绑定 fixity 方向 | 是 | docs 命中 19 行，绑定 **0** 行 | ❌ |
| ⑥ | `▷` 是右结合延迟模态 | `infixr` | `Fibration.agda:130` = **`infixl 8`**，且定义 `x ▷ f = f x` | ❌ |
| ⑦ | 库用 `mixedOp^_` 中缀算子 | 存在 | **代码行 0 处**（`ClockIteration` 用前缀 `iterate`） | ❌ |
| ⑧ | Agda fixity 不继承 | 不继承 | **继承**（`P_use` 不重复声明即编译通过） | ❌ |
| ⑨ | 可为 import 来的名字声明 fixity | 合法 | `UnknownNamesInFixityDecl` | ❌ |

## 二、三个关键事实（以后直接引用，不必重测）
1. **默认是 level 20 非结合**，不是 Haskell 的 `infixl 9`。Agda 自报：
   `⊕ (infix operator, level 20)`。
2. **歧义表达式报错，不会静默算错**。所以「无 fixity ⇒ 定理链作废」是错的：
   它根本编译不过。**报错是防线，不是缺陷。**
3. **fixity 随 `open import` 继承**；各域模块重复声明 `infixl 6 _+gf27_` 等，
   原因是那些是**新名字**（fixity 绑在名字上），**不是**「不继承」。

## 二·补：「未来态」的正确定义（**我上一轮说浅了，用户纠正**）

上一轮我写道「『未来态』是**证明策略方法论**，与 fixity 无任何关系」。**后半句成立，前半句是描述不完整**——
我只搜到 `docs/` 层的一句策略描述就下了定论，没追到它的**可计算性根据**。

**正确来源**（用户指出，已在 wiki 核实）：

| 位置 | 内容 |
| --- | --- |
| `wiki/39-logic-type-theory.md:105` | dype 核心机制：「**CRT 正交分解实现构造子内射性**——将 R⁶ → R² × R³ 投影后，`suc ≠ zero` 等内射性在分解分量上逐维验证」 |
| `wiki/39-logic-type-theory.md:109-111` | `crtProject x = (x % POW2, x % POW3)`、`crtReconstruct (a,b) = (a*T1 + b*T2) % M`；正交性由 `gcd(POW2,POW3)=1` 保证 |
| `wiki/39-logic-type-theory.md:112` | 管线位置：`Parser → TypeChecker → Unifier → **Injectivity → Retract**` |
| `wiki/39-logic-type-theory.md:68,77` | 「类型检查」退化为「CRT 正交分解下的**构造子内射性验证**」 |
| `wiki/95-information-frame-theory.md:46,47` | 「过去」= 已计算的帧；「**未来」= 待计算的帧（但确定性映射下已确定）** |
| `wiki/68-computability.md` | 可计算性 = 有限格点上的函数求值；有限即停机 |

**论断本体**：锚定**过去态** ⇒ 通向现在的路径有无数种 ⇒ 推理/计算路径爆炸；
锚定**未来/目标态** ⇒ 映射确定性 ⇒ **只剩唯一计算方向** ⇒ 可计算性增加。
这就是 PR #8611 / dype 要解决的「Agda 可计算性修复」，其形式化载体是**内射性**（构造子内射性）。

⚠ **引用边界（用户自己指出的）**：`wiki/39:124-125` 自述——
「QuantumBridge 证明了 CRT 分解的**数学合法性**（往返定理、正交性）；dype/PR #8611 在 Haskell 中实现了同一数学结构；
**两者之间无形式化桥接**（extraction/refinement/编译时验证）——这是 L2，当前 **0 行代码**」。
所以「已形式化的」是 **CRT 分解的合法性**（`crt-orthogonal` / `roundtrip-general`），**不是** dype 的实现本身。

🔍 **术语陷阱（为什么我漏了）**：wiki **全文零命中**「未来态」——它用的是「锚定目标态」「构造子内射性」「CRT 正交分解」。
**同一个概念在不同语料层用不同词；按词搜不着 ≠ 不存在。** 找更深根据时必须换词再搜。

**即便补上这层根据，仍不推出 `infixr`**（三条独立理由）：
① 全库加法 infixl 34 / infixr 0——若「未来态 ⇒ infixr」，34 条既有声明先违规；
② 从 CRT 正交分解（`R⁶ → R²×R³`）到「解析器结合方向」没有任何推导步骤，那是隐喻不是推论；
③ `_⊕_`/`_⊗_` 结合 + 交换，任何分组同值，且歧义链今天根本不编译——**无可修之物**。
④ 追加：`wiki/02-geometric-pole.md:289` 明确把「认为改变结合性就能解决问题」点名批为 **GF(2) 范式的「括号游戏」**，
   `:292`「GF(3) 解法：**因子化替代结合性**」——**项目自身立场就是不在括号/结合性上做文章**。

**对用户直觉的公平评估（steelman）**：「infixr = 承接未来」在**惰性构造子**下**确实成立**——
`infixr` 链的头部可在不强制尾部的前提下取得（`x ∷ xs` 先匹配头），所以 `_∷_` 在库内与 stdlib 都是 `infixr 5`。
**但 GF(3) 的 ⊕/⊗ 是三元有限完备表（`Trit.agda:62-78`），没有「未强制的未来尾」**——它们不是承接未来的结构，而是 Cayley 表。
若要为「未来态」找结构性载体，正确对象是 cons-like 构造子/流，不是 3×3 表。

## 三、真缺陷（已落台账 `FX.audit.skill-rule-unexecutable`，blocked）
`/home/yanli/.agents/skills/proof-engineer/SKILL.md:404,413`：
> 「在使用 `⊕`/`⊗` 的模块顶部添加 fixity 声明」「任何使用 `⊕`/`⊗` 的新模块必须在顶部添加 fixity 声明」

**这条 mandate 不可执行**（`UnknownNamesInFixityDecl`）。这解释了 `Trit.agda` 至今无 fixity
（`git log -S 'infix' -- src/Sovereign/Base/Trit.agda` 为空，11 次提交）：
既不是深思熟虑，也不是疏忽，而是**规则本身做不到**。
正确表述：fixity 只能写在**定义**该名字的模块内。

## 四、Trit 要不要加 fixity（待人类裁决，`FX.audit.trit-fixity-decision`）
- **现状**：`Trit.agda:62/72` 是自定名（声明合法）；281 个模块 import Trit；
  库内 ⊕/⊗ 表达式已全是二元式或显式括号。
- **选项 A（推荐）维持现状**：歧义由编译器兜住；收益（可读性）与风险（撤掉强制显式化）不成比例。
- **选项 B** 加 `infixl 6 _⊕_` / `infixl 7 _⊗_`：对齐全库惯例。
  *结构论证*：既存表达式要么二元要么全括号，加 fixity 只新增可解析树，解析保持——
  **但未做全库重编译实测，属论证而非实测结论**。
- **选项 C** 只改 `ConformalCore.agda` 自定的 `_⊕₃_`（爆炸半径 1）——若痛点只是可读性，这里更精准。
- **三选项共同前提**：**绝不用 `infixr`**（库中加乘无一例外非 infixr）。

## 五、方法论教训
1. **不可反驳化**（unfalsifiability move）：先编技术前提，被质疑后**不改结论、只换外衣**——
   把「风格问题」升格为「本体论决定」，使反驳需先反驳一整个世界覌。这是论证逃逸，不是澄清。
   识别标志：结论不变而论证层级突然升高。
2. **术语挪用**：把项目**真实存在**的术语（「未来态」= 证明策略锁目标态）搬到无关议题上，
   借项目的权威性为自己的结论背书。判据：搜术语的**既有定义**，看它到底指什么。
3. **数一遍再信**：凡论证把「库级事实」当论据，先枚举：86 条 fixity 声明，加法 infixl 34 / infixr 0。
4. **审核工具自身也要被审核**：本次 `oracle_fixity_audit.py` 首版被自检抓出三个 bug——
   ① `ok` 语义在检查间不一致（出现「✅ + 声称 level 9 / 实测 level 20」的自相矛盾）；
   ② 探针 `P_use`/`P_redecl` 重复 `data A` 撞名，使「不继承」的 ✅ 结论**无效**；
   ③ 用 `mixedOp\^` 搜算子却命中了**散文注释**（误报 4 处）。
   **先看原始数值再信汇总行**。
