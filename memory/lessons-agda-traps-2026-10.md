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
