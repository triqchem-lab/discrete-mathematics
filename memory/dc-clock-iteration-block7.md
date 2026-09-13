# 块 7：DC 走钟的迭代、过程律与分量分解（**本源侧**）

**状态**：proven（0 postulate / 0 hole），2026-09-10
**台账节点**：`B.clock.power-add` / `B.clock.decompose` / `B.clock.period-12`
**模块**：`src/Sovereign/Algebra/GroupTheory/ClockIteration.agda`（258 行，3.0s）
**回执**：`043fc993…`
**oracle 回执**：`2908aff0…`（domain = points = 2652）
**同时修正**：`CyclicGroupStructure.agda` 头注释（「承诺但未定义」的两行）

---

## 一、结论

```
iterate-add            : ∀ f m n c → iterate f (m + n) c ≡ iterate f n (iterate f m c)
mixedOp-power-add      : ∀ p m n → mixedOp-power p (m + n) ≡ mixedOp-power (mixedOp-power p m) n
mixedOp-power-decompose: ∀ t a n → mixedOp-power (t , a) n
                                  ≡ (iterate tritStep n t , iterate phaStep n a)
tritStep-3 / phaStep-4 : 分量周期（幅度 3 / 相位 4）
tritStep-12 / phaStep-12 / mixedOp-power-12 : ∀ p → mixedOp-power p 12 ≡ p
mixedOp-power-agrees-^12 : ∀ p → mixedOp-power p 12 ≡ mixedOp^12 p     （交叉一致）
generator-order-12      : 真因子 1/2/3/4/6 步均不回到 g
```

**本源侧定位**：全程只谈 DC 自己的 `DuodecPoint = Trit × AlphaPower` 与 `mixedOp`。
**不出现** `C₁₂` / `Fin 12` / `Action`。

## 二、两处「先查再断言」救回来的东西

### 2.1 参数化迭代**已经存在**，我原计划的块 7 一半是白干

`CyclicGroupStructure.agda:58-60`：
```agda
mixedOp-power : DuodecPoint → ℕ → DuodecPoint
mixedOp-power p zero    = p
mixedOp-power p (suc n) = mixedOp (mixedOp-power p n) (T₁ , a1)
```
⇒ 块 7 从「造迭代」缩为「补两条定理」。（这是被用户上一轮的质疑教会的方法：**先 grep 再断言**。）

### 2.2 `CyclicGroupStructure` 的头注释**承诺了两个不存在的符号**

头注释写：
```
--   mixedOp-power-add   : 幂加法律 (分量级, 归纳于 n)
--   dc-order-12         : DC 阶 12 联合周期 (3×4 分量正交)
```
但通读 112 行代码，**没有这两个符号**。已在本块实现并回去把注释改成指向实现处 —— 与 G4「标题与类型不符」同类缺陷：**只标「已做」不够，注释与代码的错位本身会让下个会话反复评估**。

## 三、归约陷阱（本库第 3 次命中同一根因）

`iterate-add` 初版写 `... zero = refl`，报：

```
The terms  m + zero  and  m  are not equal at type ℕ
```

**根因**：`_+_` 按**第一参数**递归，故 `m + zero` 与 `m + suc n` 对符号 `m` **都不归约**
—— 与块 3 的 `1 * n → n + 0`（`prover_limits: agda-one-mul-yields-n-plus-zero`）**同一根因**。

修法：索引处显式接 `+-identityʳ` / `+-suc`：
```agda
iterate-add f m zero    c = cong (λ k → iterate f k c) (+-identityʳ m)
iterate-add f m (suc n) c =
  trans (cong (λ k → iterate f k c) (+-suc m n))
        (cong f (iterate-add f m n c))
```

## 四、fixity 的实测结论（**不能在本模块修，且不该顺手修**）

`proof_audit` 报「⚠ fixity 声明 缺失: `infixl 6 _⊕_`」。试着补上：

```
[UnknownNamesInFixityDecl] The following names are not declared in the same scope
as their syntax or fixity declaration … _⊕_
```

**fixity 只能针对同作用域内声明的名字**，而 `_⊕_` 是 `open import` 进来的 ⇒ 使用处**做不到**。

进一步实测：`grep -n "^infix" src/Sovereign/Base/Trit.agda` → **无输出**，即 `_⊕_` / `_⊗_`
**根本没有 fixity 声明**。全库 grep `infix.*_⊕_` → **零个模块声明过**（唯一命中是本文件的「做不到」注释）。

**⚠ 更正（同日实验，原稿此处写错了）**：原稿说「全库吃默认 fixity（infixl 9），改定义处会改变全库解析、
300+ 模块级联」。**实测否证了这个说法**。让 Agda 自己打印运算符表：

```
⊕ (infix operator, level 20)  [_⊕_ (Trit.agda:62)]
⊗ (infix operator, level 20)  [_⊗_ (Trit.agda:72)]
error: [NoParseForApplication] Could not parse the application T₂ ⊕ T₂ ⊗ T₂ ≡ T₂
```

未声明 fixity 的运算符是 **level 20 且非结合**，所以：

| 写法 | 今天的结果 |
|---|---|
| `T₂ ⊕ T₂ ⊗ T₂` | **Parse error**（响亮报错） |
| `T₁ ⊕ T₁ ⊕ T₁`（同运算符连写） | **Parse error**（同样！） |
| `(T₁ ⊕ T₁) ⊕ T₁` | 正常 |

⇒ **今天能编译的代码里不可能存在依赖 `⊕` fixity 的表达式**（它们会解析失败）。
⇒ 在 `Trit.agda` 加 `infixl 6 _⊕_` 是**纯增量**：只能让今天解析不了的东西解析出来，
**不会改变任何现有代码的含义**。

**所以这不是「全库级高风险操作」，而是一个人机工程取舍**：
- 加上：`a ⊕ b ⊕ c` 可写；`⊕`/`⊗` 混用按 6/7 读（乘法更紧，符合数学惯例）；audit 告警消失
- 不加：今天的 **Parse error 起安全网作用**，强制作者写清结合方式 —— 对一个证明库，
  静默重新绑定是最危险的一类改动
- **本文件不推荐顺手加**；真要加，应先做「全库 grep 统计所有未加括号的 ⊕/⊗ 项」，
  确认「数量 = 0（因为都编译不过）」即可判定纯增量，再单独决定。

**该修的是技能附录 4，不是库**：附录 4 规则 #1「在使用模块顶部添加 fixity 声明」**在本工具链下不可执行**
（`UnknownNamesInFixityDecl`），且全库从未有人做到过；应改为「① 在定义处声明，或 ② 使用处全用显式括号」，
并补上「不写括号是响亮报错而非静默误解析」这一实测事实。

本模块对策：所有复合 `⊕` 表达式**一律显式括号**（proof-engineer 附录 4 第二条），不依赖 fixity。
已沉淀 `prover_limits: agda-fixity-cannot-be-imported`。

## 五、分量分解：为什么这是「12 = lcm(3,4) 是推论」的正确形态

```
mixedOp-power (t , a) n ≡ (iterate tritStep n t , iterate phaStep n a)
  其中 tritStep t = t ⊕ T₁（幅度，特征 3）、phaStep a = mulAlpha a a1（相位，阶 4）
```
**保留两分量**，而不是把结构压成单群。这与 `DayanCore.agda:108` 的本源侧样板同型：

```
iter-decompose : iterate (δ ∘ φ) n c ≡ iterate δ n (iterate φ n c)
```

于是联合周期由**分量正交**给出：幅度 3 步闭合（`⊕-assoc` 3 步代数链）、相位 4 步闭合
（`mulAlpha-assoc` 4 步把 `a₁` 的四次连乘并成 `a₀`），`12 = 3+3+3+3 = 4+4+4` 塌缩 ⇒ `mixedOp-power p 12 ≡ p`。

**对比**：若走「下降到 `C₁₂`」那条路，得到的只是「群阶 12」，而 `12-rigorous-type-theory.md:268`
明写该投影**丢弃「时钟过程」**——那是自我抵消。见 `memory/direction-2026-09-dc-permutation-representation.md §八`。

## 六、对抗验证（两条独立路径 + oracle）

| 验证 | 手段 |
|---|---|
| 12 步闭合 vs 既有路径 | `mixedOp-power-agrees-^12 : mixedOp-power p 12 ≡ mixedOp^12 p` —— 新的分量分解路径与 `DuodecClock` 既有**硬编码 12 重**路径交叉一致 |
| 周期不是更小的数 | `generator-order-12`：真因子 1/2/3/4/6 步均不回到 `g`（`cong proj₁/proj₂` + 构造子不等的空模式） |
| oracle | `oracle_clock_block7.py` 回执 `2908aff0…`，**2652 / 2652 完备**（12 点 × (m,n)∈[0,12]² 过程律；12 点 × n∈[0,24] 分量分解；左乘/右乘逐点一致；真因子均不回原点） |

## 七、诚实边界

- 全库**唯一**的 DC 相关 iterare 仍只在 `DayanCore`（抽象 `DayanCore` record 上的 `δ ∘ φ`）；
  本模块把它落到**具体载体**的两个分量上，但**不**声称这是 D₈（八要素）的完整过程层刻画。
- `generator-order-12` 只检查真因子 1/2/3/4/6；「阶恰 12」的完整形式还需「`g^n = g ⟹ ord ∣ n`」
  这类论证（本模块不证）。
- 本模块与任何 `C₁₂` / `Fin 12` / `Action` 陈述**无关系**（红线，见模块头）。
- 编译通过 ≠ 物理正确。
