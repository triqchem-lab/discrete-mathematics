# Agda 证明工程陷阱清单（2026-10 会话沉淀）

> 来源：Morse 泛型化 M1-M7b + 数论泛型 G1'-G5 + 大衍求一术 L2 共 ~120 个新模块的实战。
> 每条都付过编译失败的学费，下会话直接规避。

## 一、ℤ / GF(3) 引理参数顺序（最高频陷阱）

1. **`*-distribʳ-+` 第一参数是乘数**：`DistributesOverʳ` 展开为
   `∀ x y z → (y + z) * x ≡ (y*x) + (z*x)`——第一参数是乘数 x，不是第一个加数。
   写 `(a+b)*c` 的分配要用 `*-distribʳ-+ c a b`。此错误导致 DayanProof L2 连续 16 次编译失败。
2. **`⊕-assoc` 方向**：`(x⊕y)⊕z ≡ x⊕(y⊕z)`；把 `x⊕(a⊕b)` 化成 `(x⊕a)⊕b` 需要 **sym**。
3. **`a ⊗ T₀` 在 a 为变量时不定义性归约**（⊗ 按第一参数匹配）——必须按构造子 case
   （`⊗-zeroʳ` 三 case refl）。Base/Trit 已有 `⊗-zeroʳ/ˡ`（159-166 行），**先全量 grep 再局部定义**
   （grep 带 `| head` 会截断漏检——本次重复造轮子的根因）。

## 二、Agda 语法陷阱

4. **section 语法 `(_ ⊕ e)` 在 Agda 2.9.0 常解析失败**——一律用 `λ u → u ⊕ e`。
5. **record 内部不能定义 data 供同 record 字段引用**（`_∈_` 类）——移到顶层。
6. **`where` 块内同名定义与源定义不 convertible**（各自独立归约）——透明 alias 必须
   `∂ = ListLaws.sum⊕` 直接转发，不能 where 重定义再引用。
7. **`open import M using (...)` 不重导出**——下游要用手动转口或 `public` open
   （MagicSquare144Partition 的 MerkabaOrder 教训）。
8. **`using` 列表分隔符是 `;` 非 `,`**；续行缩进必须深于起始行
   （G1' 批量迁移 13 文件 ParseError 根因）。
9. **let 块内定义顺序敏感**（被引用者必须在前）。
10. **正交 · map-sum-fusion 类融合定理是「定理」不是「函数」**——
    `sq-right xs = foldr (λ x acc → f x ⊕ acc) T₀ xs`，不能写 `= map-sum-fusion f xs`。

## 三、cubical 模块对接

11. **cubical 模块的 `≡` 是 Path**（`Cubical.Foundations.Prelude`），与 PropEq `≡` 不同型——
    消费侧必须 `{-# OPTIONS --cubical #-}` 且 import 同源 `≡`
    （否则 `Trit i` interval 报错；ChainQuotIso 的教训）。
12. **cubical SetQuotients 的 elim-β 非定义性**——`f₀ [h₀-bwd c] ≡ c` 不要 refl 重证，
    直接转发已证引理（`h₀-surj`）。
13. **`h₀-bwd : Trit → C₀`**（C₀ 级）；商级反向需 `[_]` 引入（eq/ 语法）。

## 四、编译缓存与工程

14. **`.agdai` 缓存陈旧**：改 import 后报 NotInScope 且行号怪异——先删本模块 `.agdai` 重编。
15. **编译报错行号在修改后可能指向旧文**——重编译确认，别按旧报错改新文件。
16. **Python 批量生成 Agda**：`re.sub` 无锚会误改第一个匹配（G1' 的 Data.Nat using 被误替换）；
    f-string 里 Agda `{d}` 需转义——用 `.replace()` 代替 f-string。

## 五、证明策略

17. **div-rel 反转消除消去引理**：`rb ≡ q×rt + r` 改写为 `r ≡ rb − q×rt`（定义式），
    step-invariant 的 proof 从五步降为三步（sym div-rel 直接闭合）。
18. **陈述层先行**：先让类型签名编译（0 证明体），再逐引理填——
    M3 里程碑 1 的「陈述层修复」模式避免了大量返工。
19. **反例先行**：泛型定理前先构造性反例（MorsePairingLaw.ex-sqzero-fails）——
    证明「前提不可省」比硬凑公理便宜且诚实。
20. **mod 关系形式**：Bezout `a+k×m≡1` 与 mod `a≡1+k'×m` 数学等价（k'=−k），
    但 terminate-correct 应直接陈述 mod 形式（读者不用自行重写）。

## 六、`subst` 方向与「不可证」判定的教训（2026-10-21 T6Cayley/StepCode 会话）

21. **`subst` 方向是最高频陷阱（本会话连吃 4 次）**：`subst P eq : P x → P y`（`eq : x ≡ y`）。
    写之前先问「**手上的项落在 x 侧还是 y 侧**」；落在 y 侧就必须 `sym eq`。
    指纹：报错在**类型签名行**且说「期望类型退化成 `x ≡ x`」或「A 与 B 不相等」而 A/B 正好是该 subst 的两端。
    实例：`interpAt-++`（必须 `sym (foldT-++ …)`）、`interpC-walk`、`StepVertex→StepSide`、`StepSide→fold`。
22. **`Dec P` 的正确性：直接 `with` 判定器本身，两向各一行**——
    `yes p` 支 `TSet (yes p)` 归约为命题 ⇒ `p` 即证据；`no ¬p` 支 `TSet (no ¬p) = ⊥` 而 `¬p` 就是否证。
    本会话曾为此写 6 层 `with` + 5 条分量自反性引理（~85 行），**全部不必要**，后压缩为 8 行。
23. **`with` 里的「⊥ 假设」必须把分量引理一起带进来**：只写 `with x ≟ x` 不会细化
    `⊥` 假设（`T (no ¬p) = ⊥` 需要真的把 `no ¬p` 代入）——要写 `with x ≟ x | 分量引理 x`。
24. **断言「X 不可证」前先问：我枚举了几条分解/改写路径？所引引理覆盖其中几条？**
    本会话两次栽在这：① 判「异质相等需 HEq/J」（实际 `slide-subst` 一步 `refl`）；
    ② 判 `toStepCode` ill-posed（实际可证，漏看了**起点铸造** `cons-dtrans`——`subst-cons` 只覆盖端点铸造）。
    推翻后必须回头清理**所有引用该判断的地方**（模块注释 / 台账 note / handoff）。
25. **算术用 `k + k` 而不是 `2 * k`**：stdlib 的 `_*_` 对**第一个**参数递归（`suc m * n = n + m * n`），
    `2 * suc k` 会卡在 `suc k + …`；`k + k` 与 `suc` 结构定义性对齐，只需一处 `+-suc`。
26. **引理选址先看依赖方向**：想在模块 A 引用模块 B 的引理，先确认 B 不（直接或传递）import A，
    否则 `CyclicModuleDependency`。本会话为此白写过一条定理（`findEdge-neighbours`）。

## 七、文档与台账纪律（反向缺陷）

27. **「未证/未做」列表**不是可靠事实源**——本会话实测 **5 处**「文档声称没做，实际早就在别处证完」
    （`Pi2dFunctionLayer` 右逆 / `T6CayleyDec` 的 Dec 版 / `Omega3Suffix` 的 `suffix-resp` /
    `Pi2dQuotient` 的转述 / `AStepStdGroup` 的一般走层逆）。
    判据：看那个函数是否**已全定义**（构造子逐条有子句）+ 模块编译绿 ⇒ 它就已经存在。
    筛查工具：`python3 engineering/check_stale_claims.py`（默认只报；`--markers` 为高精度模式）。
28. **工程门禁会因目录重组而静默假失败**：`check_group_chain.sh` 曾指向迁移前的路径，
    报的是「链断裂」而实际是 `does not exist`。已改为「首选位置 + `find` 全库回退 + 路径预检」，
    缺文件时 `exit 2` 并明写「门禁脚本自身过期，不是证明错误」。**门禁红 ≠ 证明错**，先区分「读不到文件」与「内核拒绝」。
29. **台账回执会偶发误报 stale**：实测「md5 未变、两次编译给同一回执 id」仍被判「与源码不符」。
    遇到先**按 md5 对账**，不要回退成果。
30. **重复 `open import` 会累积成 `DuplicateUsing` 警告**，且补 `using` 时容易写成两段 `using`——
    合并时用脚本去重整行，别手工追加。
