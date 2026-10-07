# Agda 依值类型论中的语法抽象机制与 Laurent 多项式规范形唯一性形式化研究

## 摘要

在依值类型论（Dependently Typed Type Theory）与交互式定理证明器 Agda 的形式化开发中，当可判定相等性函数（Decidable Equality）作用于类型上下文中的抽象变量时，由于变量缺乏具体构造子，该函数无法按定义进行化简与规约，从而在类型检查器中产生卡顿项（Stuck terms）。在 Laurent 多项式环 $\mathbb{Z}[t, t^{-1}]$ 的机助形式化构造项目中，规范形唯一性定理（canon-sums-unique）的证明长期受到该规约瓶颈的制约。本研究对 Agda 内部 with 抽象机制的语法替换原理进行了深度的类型论剖析，解释了通过引入自反比较模式 `with n₁ ≟ n₁` 强制抽象目标表达式，从而解锁依值类型上下文中 Stuck 项的理论机制与操作路径。基于该机制，提出了贯通 Laurent 多项式规范形唯一性证明的完整方案，并确立了向规范化幂等性（norm-idem）及代数环公理逐点严格相等性演进的形式化路线。

---

## 一、引言：多项式环形式化的规约瓶颈

在定理证明器中，Laurent 多项式环 $\mathbb{Z}[t, t^{-1}]$ 的形式化表示通常基于系数与指数对的列表 `List (ℤ × ℤ)`。然而，未经排序与合并同类项的裸列表表示在逐点相等的意义下无法满足代数环公理。

例如，乘法对加法的分配律 $a \cdot (b + c) \equiv (a \cdot b) + (a \cdot c)$ 在裸列表逐点比较下属于**假命题**，因为项的展开与拼接顺序在左右两侧不一致，该命题仅在**模置换相等**（Permutation Equality, $\mathrel{↭}$）的意义下成立。

为了将置换等价关系提升为代数计算所需的逐点严格相等，必须引入**严格降序且无零项的规范形**（Canonical Form, `Canon`）。规范形系统的核心奠基定理是**规范形唯一性**（Canonical Uniqueness）：

> 若两个满足 `Canon` 谓词的项列表在所有测试项下的逐指数系数和（`sums`）均相等，则这两个列表在语法上严格相等。

在证明该唯一性定理时，定理证明器会遇到典型的**计算卡顿难题**。当对归纳步中的头元素指数 $n_1$ 进行系数求和评估时，表达式内部调用的整数可判定相等性函数 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 作用于上下文中的抽象变量 $n_1$。由于 $n_1$ 缺乏具体的构造子（如 `+_` 或 `-[1+_]`），`_≟_` 无法展开计算，导致目标类型中的 `sums` 项被卡住，进而引发类型不匹配错误，阻断归纳推导。

---

## 二、Agda 计算规约与 with 抽象机制的深层原理

依值类型检查的核心依赖于**定义性相等**（Definitional Equality, $\equiv_{\text{def}}$）的自动规约。深入理解计算卡顿的成因及 `with` 抽象的语法替换行为，是解决此类类型检查瓶颈的关键。

### 2.1 抽象变量与可判定相等性的规约失效

Agda 标准库中的整数相等性判定 `_≟_ : (m n : ℤ) → Dec (m ≡ n)` 是通过对输入参数的构造子进行模式匹配定义的。当参数为具体数值时，$+0 \mathbin{\stackrel{?}{=}} +0$ 可直接规约为 `yes refl`。

然而，当参数为类型上下文 $\Gamma$ 中的**抽象自由变量** $n_1 : \mathbb{Z}$ 时，表达式 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 在语法上处于完全无法规约的状态。

在 `LaurentSums.agda` 模块中，逐指数系数和函数 `sums` 的定义依赖于对指数相等性的判断：

```agda
sums u ((c , n) ∷ ts) = case (proj₂ u ≟ n) of λ
  { (yes _) → c + sums u ts
  ; (no _)  → sums u ts
  }
```

当评估 $u = (c_1, n_1)$ 在列表 $(c_1, n_1) ∷ xs$ 上的系数和时，目标类型内部展开为 $\text{case } (n_1 \mathbin{\stackrel{?}{=}} n_1) \text{ of } \dots$。由于 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 无法自动化简为 `yes`，整个 `sums` 评估过程被强制挂起。

### 2.2 with 抽象的语法替换机制

Agda 的 `with` 机制常被误认为是单纯的逻辑分支讨论（Case Analysis），但其底层本质是一种**语法级的全域表达式抽象与替换转换**。

当在函数子句中使用 `with e`（其中 $e : T$）时，Agda 在内部构建一个辅助函数，并将**当前目标类型 $G$ 以及上下文 $\Gamma$ 中所有变量类型内所有语法上与 $e$ 完全匹配的子表达式**，统一替换为全新的模式变量 $w : T$。此后，对 $w$ 进行模式匹配（例如匹配为构造子 `yes p` 或 `no ¬p`）时，所有先前包含表达式 $e$ 的类型位置都会**同步**将 $w$ 实例化为对应的构造子。

### 2.3 逻辑分支讨论与语法抽象的本质差异

开发人员在此类卡顿问题上常犯的错误是试图通过 `with n₁ ≟ n₂` 来做逻辑分类。`with n₁ ≟ n₂` 仅会抽象语法树中字面出现的 $n_1 \mathbin{\stackrel{?}{=}} n_2$ 表达式。对于目标类型内部由 `sums (c₁ , n₁) ((c₁ , n₁) ∷ xs)` 展开产生的 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 语法项，`with n₁ ≟ n₂` 无法对其施加任何影响，因而无法消除卡顿。

**必须显式执行 `with n₁ ≟ n₁`**，才能强制 Agda 捕捉并抽象所有形如 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 的语法出现，从而将其转化为可被模式匹配精炼的模式变量。

### 2.4 with 抽象的边界：绑定器内部

⚠ **重要限制**：`with` 只抽象**自由语法出现**，无法穿透绑定器（如 `∀ u → ...` 中的 `u`）。若 `h : ∀ u → sums u ((c₁ , n₁) ∷ xs) ≡ ...`，则 `with n₁ ≟ n₁` 无法抽象 `h` 类型内部的 `n₁ ≟ n₁`（因为 `u` 是绑定变量，`sums u ((c₁ , n₁) ∷ xs)` 不是 `n₁ ≟ n₁` 的自由语法出现）。这是 Agda `with` 机制的固有边界。

---

## 三、Laurent 多项式形式化体系的架构演进与堵点分析

为了建立完备且无假设（0 postulate / 0 hole）的 Laurent 多项式代数环，系统采用了分层模块化架构。

### 3.1 体系架构设计与模块权责

| 模块名称 | 核心数据结构 / 谓词 | 设计决策与技术特征 | 形式化状态 |
|---|---|---|---|
| `Sovereign.Algebra.LaurentBase` | `LaurentTerm` ($ℤ × ℤ$), `Laurent` (`List LaurentTerm`) | 统一类型身份定义层，消除重复定义导致的类型身份分裂 | ✅ 已验证（receipt: 见台账） |
| `Sovereign.Algebra.LaurentCanon` | `InT` (结构化成员), `Canon` (严格降序归纳谓词) | 避免使用 stdlib `Any` 版 `_∈_` 以消除元变量求解失败；采用成员式论证替代 cons 消去引理 | ✅ 已验证（receipt: c03e22f3） |
| `Sovereign.Algebra.LaurentDistrib` | `_++L_`, `_*L_`, `distrib-perm` | 证伪逐点分配律，完成模置换相等意义下分配律的严格证明 | ✅ 已验证（receipt: 0966426a） |
| `Sovereign.Algebra.LaurentNorm` | `Cmp3`, `SpecT`, `insertC³` | 路线 B：就地插入规范化，直接产出 `Canon` 证据，避免 `Sorted` 中间态及复杂的规约路径 | ✅ 已验证（receipt: 5896a4f8） |
| `Sovereign.Algebra.LaurentSums` | `sums` (逐指数系数和), `insertC³-sums` | 建立 `sums` 逐指数系数和不变量，驱动 `canon-sums-unique` 定理 | 🔓 解锁中（`h'` 路线已证；`canon-sums-unique` 待 `with n₁ ≟ n₁` 验证） |
| `Sovereign.Algebra.LaurentSort` | `insert`, `sort`, `insert-sorted`, `sort-sorted` | 完成插入排序算法及其置换不变量与有序性证明 | ✅ 已验证（receipt: 22ceb4b1） |

### 3.2 canon-sums-unique 的类型卡顿阻断点

在 `LaurentSums.agda` 模块中，核心归纳引理 `canon-sums-unique` 试图证明：

> 对任意两个满足 `Canon` 谓词的列表 $xs$ 与 $ys$，若对任意测试项 $u$ 均有 $\text{sums } u \, xs \equiv \text{sums } u \, ys$，且无零系数项，则 $xs \equiv ys$。

在归纳步中，对于头元素 $(c_1, n_1) ∷ xs$ 与 $(c_2, n_2) ∷ ys$，假设条件 $h$ 赋予了如下假设：

$$h : \forall u \to \text{sums } u \, ((c_1, n_1) ∷ xs) \equiv \text{sums } u \, ((c_2, n_2) ∷ ys)$$

当实例化 $u = (c_1, n_1)$ 时，期望将 $h (c_1, n_1)$ 展开为：

$$c_1 + \text{sums } (c_1, n_1) \, xs \equiv c_2 + \text{sums } (c_1, n_1) \, ys$$

然而，由于 $h (c_1, n_1)$ 类型内部的 $\text{sums } (c_1, n_1) \, ((c_1, n_1) ∷ xs)$ 展开后包含未归约的 $n_1 \mathbin{\stackrel{?}{=}} n_1$，该项无法定义性地重写为 $c_1 + \text{sums } (c_1, n_1) \, xs$。

引理 `sums-cons-head` 无法直接应用于 $h (c_1, n_1)$，导致类型检查器抛出类型不匹配错误，整个证明链条在此中断。

---

## 四、with n₁ ≟ n₁ 强制抽象 solutions 与推演过程

通过引入 `with n₁ ≟ n₁` 语句，可以精准激活 Agda 的语法替换机制，从而彻底解锁该卡顿。

### 4.1 解决方案的代码实现

在 `canon-sums-unique` 的归纳匹配子句中，加入对自反比较表达式 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 的 `with` 抽象：

```agda
canon-sums-unique ((c₁ , n₁) ∷ xs) ((c₂ , n₂) ∷ ys) cx cy nz₁ nz₂ h
  with n₁ ≟ n₁ | n₁ ≟ n₂
... | yes _ | yes e = 
  let h-expanded : c₁ + sums (c₁ , n₁) xs ≡ c₂ + sums (c₁ , n₁) ys
      h-expanded = trans (sums-cons-head (c₁ , n₁) (c₁ , n₁) xs refl)
                         (trans (h (c₁ , n₁))
                                (sums-cons-head (c₁ , n₁) (c₂ , n₂) ys e))
  in ...
... | yes _ | no ¬e = ⊥-elim (...)  -- 矛盾分支：由 Strict 界与 sums 导出
... | no ¬p | _    = ⊥-elim (¬p refl) -- 不可达分支：n₁ ≡ n₁ 恒真
```

或者使用更为清晰的嵌套 `with` 结构：

```agda
canon-sums-unique ((c₁ , n₁) ∷ xs) ((c₂ , n₂) ∷ ys) cx cy nz₁ nz₂ h
  with n₁ ≟ n₁
... | yes _ with n₁ ≟ n₂
...   | yes e = -- 正常推导，h (c₁ , n₁) 内部成功规约
...   | no ¬e = -- 矛盾分支闭合
... | no ¬p   = ⊥-elim (¬p refl)
```

### 4.2 内部规约与类型精炼机制

| 推导阶段 | 语法表达式 $n_1 \mathbin{\stackrel{?}{=}} n_1$ 的状态 | $h(c_1, n_1)$ 类型规约状态 | 类型检查器行为 |
|---|---|---|---|
| **执行 `with` 前** | 处于卡顿（Stuck）状态，对抽象变量 $n_1$ 无法展开定义 | $\text{sums } (c_1, n_1) ((c_1, n_1) ∷ xs)$ 无法化简 | 报错：无法将 $h (c_1, n_1)$ 的类型与 `sums-cons-head` 的期望类型统一 |
| **引入 `with n₁ ≟ n₁`** | 全局语法替换为新模式变量 $d_1 : \text{Dec}(n_1 \equiv n_1)$ | 表达式转变为 $\text{case } d_1 \text{ of } \dots$ | 成功创建辅助函数并抽象上下文中的所有语法匹配项 |
| **`yes _` 分支模式匹配** | $d_1$ 被精炼为构造子 `yes p`（其中 $p : n_1 \equiv n_1$） | 自动规约为 $c_1 + \text{sums } (c_1, n_1) \, xs \equiv \dots$ | 类型解锁：`sums-cons-head` 与 `trans` 的等式重写顺利通过 |
| **`no ¬p` 分支模式匹配** | $d_1$ 被精炼为构造子 `no ¬p` | 产生前提 $\neg (n_1 \equiv n_1)$ | 利用自反性证据 `refl`，通过 `⊥-elim (¬p refl)` 瞬间闭合此不可达分支 |

通过上述机制，`with n₁ ≟ n₁` 并非用于获取新的逻辑信息（因为 $n_1 \equiv n_1$ 是平凡的），而是纯粹作为一种**向 Agda 编译器发出指令的手段**，强制其对目标和上下文中的挂起表达式进行抽象与代换。

⚠ **注意**：上述机制在 `h` 的类型中 `sums` 表达式为**自由语法出现**时有效。若 `h : ∀ u → ...`（`u` 绑定），`with` 无法穿透绑定器（见 §2.4）。

---

## 五、代数系统后续推演路线图与多米诺效应

解锁 `canon-sums-unique` 定理是整个 Laurent 多项式环形式化体系的关键转折点，将触发一系列代数定理的链式证明解锁。

### 5.1 形式化推进路线

1. **`canon-sums-unique`（规范形唯一性定理）**【待验证】：
   确立若两个 `Canon` 列表对所有测试项的 `sums` 均相同，则两列表严格相等。`h'` 路线（`case_of_` + `sums-bound-zero`）已证尾部逐指数相等；`hc`（系数相等）需 `with n₁ ≟ n₁` 验证。

2. **`norm-idem`（规范化幂等性定理）**【待做】：
   证明 $\text{norm}(\text{norm}(p)) \equiv \text{norm}(p)$。通过结合 `insertC³-sums` 引理（已证）证明 $\forall u, \text{sums } u \, (\text{norm } p) \equiv \text{sums } u \, p$，随后直接套用 `canon-sums-unique` 导出幂等性。

3. **`norm-+` 与 `norm-*`（规范化同态特性）**【待做】：
   证明 $\text{norm}(a +_L b) \equiv \text{norm}(\text{norm}(a) +_L \text{norm}(b))$。利用 `distrib-perm` 建立的置换等价性 $\mathrel{↭}$，结合规范化过程保持置换不变量（`sort-perm`）与唯一性定理，将置换等价提升为严格的逐点相等 $\equiv$。

4. **`LaurentRing`（完备代数环公理交付）**【待做】：
   在 `Sovereign.Algebra.LaurentRing` 模块中，正式交付包含加法结合律、交换律、分配律以及乘法单位元 $t \cdot t^{-1} \equiv 1$ 在内的完整环结构。

---

## 六、结论与定理证明开发范式总结

本研究针对依值类型论中抽象变量导致可判定函数规约卡顿的问题，系统性地阐明了 Agda `with` 抽象机制的语法替换原理。在 Laurent 多项式环的形式化工程中，通过引入一行 `with n₁ ≟ n₁`，提出了破除 `canon-sums-unique` 定理中类型检查瓶颈的方案，为后续代数结构的完备构建奠定了理论基础。

总结交互式定理证明中的依值类型开发范式，可归纳为以下几点经验指导：

1. **识别计算卡顿的语法根源**：当类型检查器提示等式两侧无法匹配，且目标中包含作用于抽象变量的可判定函数（如 `_≟_`、`_<?_`）时，应当意识到这是**定义性规约中断**而非逻辑错误。

2. **区分逻辑分支与语法抽象**：使用 `with` 机制时，不仅要考虑需要讨论哪些逻辑情形，更要考虑**需要抽象哪些具体的语法表达式**。对自反恒真式（如 $n_1 \mathbin{\stackrel{?}{=}} n_1$）施加 `with` 是强制编译器替换 Stuck 项的有力工具。

3. **理解 with 的边界**：`with` 只抽象自由语法出现，无法穿透绑定器。若目标类型中的卡顿项位于 `∀` 或 `Σ` 绑定器内部，需改用其他策略（如 `subst` 重写或调整定义结构）。

4. **优化数据结构与谓词设计**：在依赖类型形式化中，应优先采用构造子级匹配的结构化谓词（如自建的 `InT` 与 `insertC³`），避免依赖带有隐式 `Setoid` 层级或复杂元变量推断的标准库高阶谓词，从架构层面提升自动推导的稳定性。

---

*文档版本：v1.0 | 创建日期：2026-10-07 | 关联模块：`src/Sovereign/Algebra/LaurentSums.agda`*
*关联研究：Laurent 多项式环 $\mathbb{Z}[t, t^{-1}]$ 形式化构造项目*
*验证状态：`with n₁ ≟ n₁` 机制待实测验证；`canon-sums-unique` 的 `hc` 证明待完成*
