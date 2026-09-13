# Doz 记数法层的形式化（Positional + Doz）

**日期**: 2026-09-13
**新增模块**（按范畴分列，不混）:
· **进制层**（记数法）: `src/Sovereign/Format/Positional.agda`、`src/Sovereign/Format/Doz.agda`
· **位域层**（字段状态数）: `src/Sovereign/Format/DigitField.agda`
· **桥**（位域 ↔ 进制，双射）: `src/Sovereign/Format/DigitRealization.agda`
· **查询面**: `src/Sovereign/Verify/DuodecOracle.agda`
**关联**: [01-ontology.md](01-ontology.md)（Doz 的本体论位置）、[08-terminology.md](08-terminology.md)（禁止混用 DC/C₁₂/R₁₂/Doz）

---

## 一、为什么补这一层

`01-ontology.md` 把十二进制分成四层，其中三层的载体与运算都已在库里形式化：

| 记号 | 载体 | 形式化状态 |
|------|------|-----------|
| **DC**（DuodecClock） | `DuodecPoint = Trit × AlphaPower` | ✅ `Sovereign.Algebra.GroupTheory.DuodecClock`（0 postulate，144 case refl） |
| **C₁₂** | `(Duodec, +12)` | ✅ `Sovereign.Algebra.Duodecimal` |
| **R₁₂** | `(Duodec, +12, *12)` | ✅ 同上（含零因子 `2 *12 6 ≡ d0`） |
| **Doz** | 以 12 为底的位值数字串 | ❌ **本文之前：尚未系统形式化** |

Doz 不是装饰：`phase_bias` 的高 4 位（十二律相位）、TQ10 的相位字段、`loss_gain.py` 的整数格点，
都建立在「以 12 为底记数」这件事上。这一层没有定义，就等于整条位值链没有底。

## 二、做法：抽出一个泛型位值制，而不是只写十二进制

关键观察：**Doz（base 12）与内核里的 Z/3¹¹ 环（base 3）是同一套机制**——
把一个可能超范围的位表按 base 逐位进位归一，位表的值在归一前后不变；
加法是逐位相加再归一，乘法是逐位卷积再归一。

于是只写一次 `Sovereign.Format.Positional`（对任意 `base ≥ 2`），Doz 就是 `base = 12` 的实例。
同时，内核侧 `lib/sov/sov_z3r_*`（11 位基 3 环）那个已知缺口，
也能用同一个模块的 `base = 3` 实例补上（**待办**，见 §六）。

### 2.1 位序与值函数

位表 `Raw = List ℕ`，**低位在前**（与 `Data.Vec` 的 `unpack5` 一致）：

```agda
value : Raw → ℕ
value []       = 0
value (x ∷ xs) = x + base * value xs
```

「原始位」允许暂时 ≥ base —— 这正是逐位相加/卷积的中间状态。

### 2.2 归一：为什么写成 `expand` 而不是手写进位循环

手写的进位循环要处理「尾进位自身还要展开成多位」，那一步只有良基递归能终止；
而 Agda 的 `wfRec` 在**递归调用处不按定义化简**（不同调用点带不同的可及性证明 ⇒ 项不相等），
于是「展开保值」这条引理无法用 `≡⟨⟩` 走通——这是本次实现中真实踩到的坑，记录在此以免重犯。

改用**外延指定**：

```agda
-- v 的 base 进制 n 位表示（低位在前）＋ 一个剩余高位值
expand : ℕ → ℕ → ℕ × Raw
expand zero    v = v , []
expand (suc k) v = proj₁ (expand k (v / base)) , v % base ∷ proj₂ (expand k (v / base))

norm : ℕ → ℕ → Raw
norm n v = proj₂ (expand n v)
```

（定义里直接写 `proj₁/proj₂` 而非 `let`-模式：`let (a , b) = e in …` 在 `e` 卡住时不化简，
会让计算引理无法用 `refl` 证明。）

## 三、证明清单（全部 0 postulate）

`Sovereign.Format.Positional (base) (1 < base)`：

| 定理 | 签名 | 含义 |
|------|------|------|
| `expand-spec` | `value (proj₂ (expand n v)) + base ^ n * proj₁ (expand n v) ≡ v` | **核心引理**：展开保值，被丢弃的高位显式留在等式里 |
| `expand-bound` | `All (_< base) (proj₂ (expand n v))` | 展开出来的每一位都合法 |
| `norm-spec` | `value (norm n v) + base ^ n * proj₁ (expand n v) ≡ v` | 归一语义（机器位宽语义的规范写法） |
| `norm-bound` | `All (_< base) (norm n v)` | 归一后每位都合法 |
| `value-addRaw` | `value (addRaw xs ys) ≡ value xs + value ys` | 逐位相加（不进位）保值 |
| `add-spec` | `value (addNorm n xs ys) + base ^ n * carry ≡ value xs + value ys` | **位值制加法正确**（模 base^n） |
| `value-scale` / `value-conv` | `value (scale k xs) ≡ k * value xs`；`value (conv xs ys) ≡ value xs * value ys` | 数乘 / 卷积保值 |
| `mul-spec` | `value (mulNorm n xs ys) + base ^ n * carry ≡ value xs * value ys` | **位值制乘法正确**（模 base^n） |
| `trim-bound` | 截断后每位仍合法 | 定长机器字的位合法性 |

`Sovereign.Format.Doz`（`base = 12`）：

| 定义/定理 | 内容 |
|-----------|------|
| `DOZ_DIGITS = 9` | 机器位宽；`12⁹ = 5159780352 ≤ 3²⁷`，`12¹⁰` 越界 |
| `POOL≡12^9` | `5159780352 ≡ 12 ^ 9`（refl） |
| `add` / `mul` / `digits` | 十二进制加 / 乘 / 规范位表（全部 `norm 9`） |
| `add-spec` / `mul-spec` | 上面的同态定理在 base 12、9 位下的实例 |
| `digits-bound` | `All (_< 12) (digits v)` |
| `render` | 规范十二进制写法（高位在前，`A`=10 `B`=11，至少一位） |

## 四、数位分离：十二进制**不需要**新元件，也**不浪费**

> **2026-09-13 更正**。本节初版按「每位固定 3 个 trit」算利用率，得出「三进制不适合 Doz」——
> 那是**错的口径**：把一种人为的统一布局当成了载体性质。按项目的 **数位分离**
> （二进制位与三进制位分开承载、靠换算互通）口径，结论相反。

一个数位只要能写成 `3^m · 2^k` 就能**精确**承载，一个状态都不浪费。于是：

```
十二进制一位 = 3 × 4 = 3¹ · 2²   ⇒   1 个三进制位 + 2 个二进制位 = 12 态（零浪费）
9 位十二进制 = 3⁹ · 2¹⁸ = 12⁹                （Agda：word-capacity，refl）
```

关键在于 **4 = 2²**：⟨α⟩ 是 4 阶乘法旋转，它天然落在**两个二进制位**上。
所以十二进制既不需要 radix-4 元件，也不需要 radix-12 元件——**这就是「不增加硬件」**，
代价只是**换算**（把同一批数位在两条位轨之间翻译）。换算保值已形式化：
`value-sep-hom` / `value-duodec-hom`（分离 ⇄ 合流，数值不变）。

### 位宽对照（按值换算，不固定布局）

| 载体 | 容量 | 装得下几位十二进制 |
|---|---|---|
| 27 个三进制位 | 3²⁷ | **11** 位（`trit27-holds-doz11` + `trit27-not-doz12`） |
| 43 个二进制位 | 2⁴³ | **11** 位（`bit43-holds-doz11` + `bit43-not-doz12`） |
| 9 个三进制位 + 18 个二进制位（数位分离） | 3⁹·2¹⁸ = 12⁹ | **9** 位，**精确零浪费**（`word-capacity`） |

三进制并不吃亏（每个三进制位承载 log₂3 ≈ 1.585 bit）。真正会浪费的只有
**「固定 3 trit/位」的统一布局**：9 位十二进制占满 27 个三进制位，而按值打包只需
⌈9·log₃12⌉ = 21 位——tritvm v1 目前就是这种统一布局，所以它有人工约束
`TRAP bad-doz`（位值 ≥ 12 即陷阱），那是**实现**约束，不是载体性质。

### 形式化落点（两个范畴 + 一座桥，§7.5 有术语红线）

| 范畴 | 模块 | 内容 |
|---|---|---|
| **进制**（记数法） | `Sovereign.Format.Positional` / `Doz` | 权重 `12^k`、位值 `0..11`、逢 12 进一、进位归一 |
| **位域**（字段状态数） | `Sovereign.Format.DigitField` | `3·2²=12`、`3⁹·2¹⁸=5159780352`、`3²⁷`、`2⁴³` 等**纯容量算术** |
| **桥** | `Sovereign.Format.DigitRealization` | 12 态位域 ⇄ 1 三态域 + 2 二态域（**双射**，复用 `crt12`）；容量 ⇒ 位数；换算保值 |

**桥是双射，不是等号**：`realize` / `separate` 互逆（`realize-separate` / `separate-realize`），
所以「12 态位域」与「一位十二进制数位」**一一对应**——但前者是字段容量、后者是记数法的位。
把两者写成等号是范畴错误；`12 = 3·2²` 读作「位域容量分解」，**不能**读作「12 进制 = 3 进制 × 2 进制」。

⚠️ **术语红线**：**数位分离**（本节，已形式化）≠ **位数分离**（DC12 论文 L5 的
「ℓ(cⁿ) > ℓ(aⁿ+bⁿ)」，已被反例 (a=b=9,c=10,n=3) 击穿、项目废弃，
见 [16-dc12-layer-adjudication.md](16-dc12-layer-adjudication.md)）。中文词形近，含义无关。

## 五、机器侧对接（tritvm v1）

形式化的价值必须在机器上可见。`~/work/tritvm/`（TritVM v0/v1）实现了 DC/C₁₂/R₁₂/Doz 指令层，
并用本库作 oracle（`agda-oracle.mjs --duodec` → `DuodecOracle.agda` 求值 → `tritvm --agda-check` 逐例比对）：

```
- DC/Doz 层: 已对照 3163 项；键族：DC_MIXT(9) DC_MULALPHA(16) DC_INVT(3) DC_INVA(4)
  DC_MIXP(144) DC_LABEL(12) DC_PI3(12) DC_PI4(12) DC_TICKT(13) DC_TICKA(13) DC_TICKL(13)
  C12_ADD(144) R12_MUL(144) DOZ_ADD(1301) DOZ_MUL(1301) DOZ_STR(22)
- 未含（无 Agda 对应）：DOZ_SUB DOZ_DIV DOZ_MOD
SOV_TRITVM_AGDA_OK 18/18
SOV_TRITVM_AGDA_DC_OK 3163/3163
```

其中 `DC_TICKT/DC_TICKA/DC_TICKL` 是**走钟轨迹**（联合生成元 `g = (T₁,a₁)` 的 k 次幂），
Agda 算出的 13 个点与机器上 `DCOUT` 输出的 13 行逐字一致：

```
k=0  (T₀,a₀)  k=3  (T₀,a₃) ← 3 步：损益归零，相位未归零
k=1  (T₁,a₁)  k=4  (T₁,a₀) ← 4 步：相位归零，损益未归零
k=2  (T₂,a₂)  k=12 (T₀,a₀) ← 12 步：联合归零（lcm(3,4)=12）
```

只看 C₁₂ 标签的机器看到 `0,1,…,11,0`（一个 12 阶循环）；
看分量的机器看到 3 步 / 4 步的**部分归零**与 12 步的联合归零。
**前者是投影，后者是本源，而两者在同一台机器上同时可见**——这是 `12-rigorous-type-theory.md`
所说「DC 不是 C₁₂」的机器级证据。

## 六、诚实边界（不许含糊）

1. **不证明进位循环的精化**。本模块证明的是位运算的**规范语义**：
   `addNorm` / `mulNorm`（= 逐位运算后归一）的值满足模 base^n 的同态。
   C 里那个 `for` 进位循环（`sov_z3r_mul`、tritvm 的 `doz_mul`）**是否精化**为这里的 `expand`，
   需要程序验证工具链（Frama-C/ACSL、VST 之类），**不在 Agda 能力范围内**。
   两者之间的落差由差分 oracle（抽样对照）覆盖——这是两条不同的证据线，不互相冒充。
2. **Doz 的减法 / 整除 / 取余尚未形式化**。tritvm v1 实现了 `DOZSUB/DOZDIV/DOZMOD`，
   它们目前**只有**对 BigInt 基准的差分自测，不构成形式验证。
3. **`render` 是编码显示函数**。它的输出等于「规范十二进制写法」这一点由 `expand-spec`
   （值定理）间接支持，而不是逐字符证明。

## 七、下一步

- **把位域划分落到 ISA**：`DigitField` 只谈容量，`DigitRealization` 只谈桥（双射 + 容量⇒位数），
  两者都**没有**规定位在硬件里如何物理排布（交织还是分块、字宽多少）。tritvm v1 仍是
  「27 个三态域、每位数位占 3 个」；要改成别的位域划分（例如 9 个三态域 + 18 个二态域）
  需要先定 ISA 布局——注意这是**位域**决定，与**进制**（Doz 的逢 12 进一）互相独立。
- **用 `Positional` 的 `base = 3` 实例补 Z/3¹¹**：这可以一次性关掉内核树
  `lib/sov/README` 里「`sov_z3r_*` 在库中无形式化对应」那个缺口
  （内核 `verify-against-agda.sh` 目前明确打印这一条未对照）。
- Doz 的减法 / 整除 / 取余形式化（补上 §六.2）。
- DC 的**置换表示**（`Action DC`）仍缺（见
  `memory/direction-2026-09-dc-permutation-representation.md`：R2 方向仍开）；
  本次 `DuodecOracle` 未覆盖它。
