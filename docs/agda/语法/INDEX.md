# Agda 语言参考（Language Reference）中文索引

> 本目录镜像自 [Agda 官方 Language Reference](https://agda.readthedocs.io/en/latest/language/index.html)，
> 每个主题保留英文原文，并在文件头部添加**中文导读**与**本项目（律算合一 / Sovereign Mathematics）相关性**提示。

- 共 **51** 个主题页面，按主题分 10 组子目录存放。

- 导读头标记说明：★ 表示对 Sovereign 项目数学骨架高度相关。

- 思维导图：[agda-syntax-mindmap.svg](agda-syntax-mindmap.svg)

---


## 核心语法与词法

`01-核心语法与词法/`

- [核心语言（`core-language`）](01-核心语法与词法/01-core-language.md) — Agda 依赖类型 lambda 演算核心语法、项文法，以及 concrete→abstract→internal→treeless 的编译管线各阶段。
- [词法结构（`lexical-structure`）](01-核心语法与词法/02-lexical-structure.md) — token 分类、关键字、layout（缩进）规则、literate Agda（.lagda）支持。
- [语法糖（`syntactic-sugar`）](01-核心语法与词法/04-syntactic-sugar.md) — 隐藏参数 pun（.x）、do-notation、idiom 括号。
- [混合 fixity 运算符（`mixfix-operators`）](01-核心语法与词法/03-mixfix-operators.md) — 下划线占位的 mixfix 运算符、precedence、associativity、歧义与作用域、telescope 内的运算符。
- [语法声明（`syntax-declarations`）](01-核心语法与词法/05-syntax-declarations.md) — 为 mixfix 运算符绑定 notation（stub 文档）。

## 类型与数据

`02-类型与数据/`

- [排序系统（宇宙）（`sort-system`）](02-类型与数据/05-sort-system.md) — Set/Prop 宇宙层级、sort 元变量、未知 sort 的处理。
- [宇宙层级（`universe-levels`）](02-类型与数据/08-universe-levels.md) — Level 类型与运算（ℓ⊔ℓ/ℓ+1）、intrinsic 属性、forall 记法、Setω、相关 pragma。
- [函数类型（`function-types`）](02-类型与数据/02-function-types.md) — 依赖函数空间 (x : A) → B 的记法约定与箭头方向。
- [数据类型（`data-types`）](02-类型与数据/01-data-types.md) — 简单/参数化/索引数据类型定义，strict positivity 约束。
- ★ [记录类型（`record-types`）](02-类型与数据/04-record-types.md) — record 声明、构造/分解、record module、η 展开、递归 record、instance 搜索集成。
- [Prop 命题宇宙（`prop`）](02-类型与数据/03-prop.md) — 命题宇宙 Prop、predicative 层级、propositional squash 类型 ∥_∥、使用限制。
- ★ [望远镜（`telescopes`）](02-类型与数据/06-telescopes.md) — telescope（多绑定上下文）记法、binding 位置上的 irrefutable pattern、telescope 内 let。
- [两层类型论（`two-level`）](02-类型与数据/07-two-level.md) — 区分「外层」（fibrant，可 univalence）与「内层」（strict）的两层宇宙框架。

## 函数定义与模式匹配

`03-函数定义与模式匹配/`

- [函数定义（`function-definitions`）](03-函数定义与模式匹配/03-function-definitions.md) — 函数签名与子句定义、特殊模式（absurd/dot/record）、case tree 展开机制。
- [Lambda 抽象（`lambda-abstraction`）](03-函数定义与模式匹配/04-lambda-abstraction.md) — λ 表达式、pattern lambda、absurd lambda。
- [局部定义 let/where（`let-and-where`）](03-函数定义与模式匹配/05-let-and-where.md) — let 表达式、where 块的局部绑定与作用域，以及用 where 证明性质的技巧。
- ★ [with 抽象（`with-abstraction`）](03-函数定义与模式匹配/08-with-abstraction.md) — with 对中间值分类讨论、多 with、技术细节（隐藏、重写）。
- [协模式（`copatterns`）](03-函数定义与模式匹配/01-copatterns.md) — 用 copattern（对记录投影的模式匹配）定义余归纳/record 值，与对构造子的模式匹配对偶。
- [模式同义词（`pattern-synonyms`）](03-函数定义与模式匹配/06-pattern-synonyms.md) — 为复杂模式命名、模式重载与 refold。
- [覆盖检查（`coverage-checking`）](03-函数定义与模式匹配/02-coverage-checking.md) — 确保函数对所有可能输入模式完备覆盖，含 copattern 与索引数据类型的覆盖性检查规则。
- [终止检查（`termination-checking`）](03-函数定义与模式匹配/07-termination-checking.md) — 原始递归、结构递归、with-function 的终止性、相关 pragma 与选项。

## 模块与作用域

`04-模块与作用域/`

- ★ [模块系统（`module-system`）](04-模块与作用域/01-module-system.md) — 模块、private、名称修饰、re-export、参数化模块、多文件拆分、datatype/record 模块。
- [互递归（`mutual-recursion`）](04-模块与作用域/02-mutual-recursion.md) — interleaved mutual 块、前向声明、旧式 mutual 块。

## 参数解析与泛化

`05-参数解析与泛化/`

- [隐式参数（`implicit-arguments`）](05-参数解析与泛化/02-implicit-arguments.md) — 花括号隐式参数、tactic 参数、元变量与统一化（unification）机制。
- [实例参数（`instance-arguments`）](05-参数解析与泛化/03-instance-arguments.md) — Agda 的 type class 机制：instance 块、实例解析、overlap 与回溯。
- [声明变量泛化（`generalization-of-declared-variables`）](05-参数解析与泛化/01-generalization-of-declared-variables.md) — variable 块声明的变量自动泛化为顶层签名参数，含嵌套泛化、实例/无关变量、导入导出规则。
- [字面量重载（`literal-overloading`）](05-参数解析与泛化/04-literal-overloading.md) — ℕ/String/Negative 字面量通过 Number/IsString/IsNegativeNumber 实例重载的机制与限制。

## 可见性·相关性·模态

`06-可见性相关性与模态/`

- [无关性（证明无关）（`irrelevance`）](06-可见性相关性与模态/09-runtime-irrelevance.md) — @0（erasure）标注使参数在编译产物中被擦除，仅类型检查期保留。
- [运行时无关性（`runtime-irrelevance`）](06-可见性相关性与模态/09-runtime-irrelevance.md) — @0（erasure）标注使参数在编译产物中被擦除，仅类型检查期保留。
- [Opaque 定义（`opaque-definitions`）](06-可见性相关性与模态/06-opaque-definitions.md) — opaque 块（比 abstract 更精细的展开控制），unfolding 声明、在类型中的展开行为。
- [抽象定义（`abstract-definitions`）](06-可见性相关性与模态/01-abstract-definitions.md) — abstract 块内定义的实现细节对外不可见，只能看到其类型签名。
- [模态系统（`modalities`）](06-可见性相关性与模态/05-modalities.md) — 通用模态框架：位置模态系统与纯模态系统，统一描述 irrelevance/flat/...
- [Flat 模态（`flat`）](06-可见性相关性与模态/03-flat.md) — @♭（flat）模态与 #（sharp）模态，以及 @♭ 上的模式匹配，用于控时不假设（guarded/时态）分解。
- [极性注解（`polarity`）](06-可见性相关性与模态/07-polarity.md) — @++/@+/@-/@ω 等极性模态，与正定性检查的关系。
- [正定性检查（`positivity-checking`）](06-可见性相关性与模态/08-positivity-checking.md) —  occurrence 分析确保数据类型严格正定，禁止非正定出现。
- [累积性（`cumulativity`）](06-可见性相关性与模态/02-cumulativity.md) — --cumulativity 启用宇宙累积（Set ℓ ⊆ Set (ℓ+1)），简化 N-ary 函数等多宇宙签名，含约束求解与限制。

## Cubical / HoTT

`07-Cubical-HoTT/`

- ★ [Cubical 类型论（`cubical`）](07-Cubical-HoTT/02-cubical.md) — Cubical 模式：区间/路径类型 PathP、transport、partial、homogeneous composition、Glue 类型、高阶归纳类型（HIT）、索引归纳类型。
- [Cubical 兼容模式（`cubical-compatible`）](07-Cubical-HoTT/01-cubical-compatible.md) — --cubical-compatible（即 --without-K 的增强）使普通模式匹配代码可被 Cubical 理论解释，保留 univalence 语义。
- [无 K（`without-k`）](07-Cubical-HoTT/03-without-k.md) — --without-K 限制模式匹配（禁用 K 公理）、终止检查与宇宙层级限制，保证 univalence 一致。

## 元编程与重写

`08-元编程与重写/`

- [反射（元编程）（`reflection`）](08-元编程与重写/03-reflection.md) — 内建 Reflection 类型、TC 单子、quote/unquote、宏，用于编译期生成/检查代码。
- [重写规则（`rewriting`）](08-元编程与重写/01-local-rewriting.md) — --rewriting + 局部 rewrite 规则，在不全局破坏 canonicity 的前提下添加等式重写。
- [局部重写（`local-rewriting`）](08-元编程与重写/01-local-rewriting.md) — --rewriting + 局部 rewrite 规则，在不全局破坏 canonicity 的前提下添加等式重写。
- [有损统一（`lossy-unification`）](08-元编程与重写/02-lossy-unification.md) — --lossy-unification 启发的启发式统一，对 record/η-类型快速统一但有精度损失。

## 内建·余归纳·大小类型

`09-内建余归纳大小类型/`

- [内建类型（`built-ins`）](09-内建余归纳大小类型/01-built-ins.md) — Agda 内建的 ℕ/Bool/List/Maybe/Char/String/Float/Word/Equality/Sort/Level/Sized 等类型及其绑定机制。
- [余归纳（`coinduction`）](09-内建余归纳大小类型/02-coinduction.md) — 通过 coinductive record 与 copattern 定义无限/惰性数据结构（如流、余归纳类型）。
- [大小类型（`sized-types`）](09-内建余归纳大小类型/04-sized-types.md) — Size 索引类型用于保证（余）归纳的 productivity 与终止性。
- [守卫类型论（`guarded`）](09-内建余归纳大小类型/03-guarded.md) — later（@0/@tick）模态与时态类型，用于构造 productive 余归纳与因果分离。

## 公设·Pragma·FFI·安全

`10-公设Pragma-FFI安全/`

- [公设（`postulates`）](10-公设Pragma-FFI安全/02-postulates.md) — postulate 声明外部假设的项/类型，含 postulated built-ins 与局部 postulate 用法。
- [编译指令 Pragmas（`pragmas`）](10-公设Pragma-FFI安全/03-pragmas.md) — 全部 pragma 索引：OPTIONS/INLINE/REWRITE/BUILTIN/ETC，控制编译器行为。
- [Safe Agda（`safe-agda`）](10-公设Pragma-FFI安全/04-safe-agda.md) — --safe 选项禁用不安全特性（postulate 未信任、unquote 等），保证可信赖基础。
- [外部函数接口 FFI（`foreign-function-interface`）](10-公设Pragma-FFI安全/01-foreign-function-interface.md) — 通过 compiler pragma 与 Haskell/JavaScript 后端的 FFI 绑定外部函数。

---

*共 51 个主题。原始索引：<https://agda.readthedocs.io/en/latest/language/index.html>*
