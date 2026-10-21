# PROVEN.md — 已证清单（防重复实现）

> **用途**：写任何「新」定理 / record / 实例**之前**，先读本清单 + 跑 `proof_dag action:"search"`。
> **为什么存在**：本会话实测**三次重复实现**（`DCPresentation.agda` / `dc-oblivion-*` / 「全库第一个 Presentation」），
> 根因是「`bash grep` 只查单个文件」+「长会话忘记前面证过什么」。
>
> **本清单是人工维护的「最近 / 最常复用」子集**（全库 771 条 proven 在台账里，不在此重复）：
> - 权威全量：`proof_dag action:"list"`（或 `~/.dsh/state/math-proof/dag-11083e096b45.json`）
> - 按关键词查：`proof_dag action:"search" query:"…"`
> - 按模块查：DSH `grep` 工具（ripgrep 语法）

---

## 一、检索纪律（硬性前置，不是建议）

| 场景 | 强制动作 |
|---|---|
| 写任何「新」定理 | **先** `proof_dag action:"search"` + **DSH grep 全库** `src/Sovereign` |
| 写任何「新」record / 实例 | 同上（尤其是 `record X : Set` / `X : SomeRecord`） |
| 搜索任何概念 | **DSH `grep` 工具**（ripgrep 语法），**不用** `bash grep` 单文件 |

**⇒ 已由机器强制**：`.git/hooks/pre-commit` → `engineering/check_duplicate.sh`（提交前拦重复符号）

---

## 二、零冥族归零（**本地早已完成**，不是新增）

### `ZeroOblivion`（`src/Sovereign/Algebra/GroupTheory/DuodecClock.agda:504`）

| 字段 | 命题 |
|---|---|
| `addZeroR` | `∀ x → mixedOp x zero ≡ x` |
| `addZeroL` | `∀ x → mixedOp zero x ≡ x` |
| `mulAlphaCycle` | `mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0`（α⁴ = 1） |
| `tritCycle` | `∀ x → (x ⊕ x) ⊕ x ≡ T₀`（⊕³ = 0） |
| `jointCycle` | `∀ p → mixedOp^12 p ≡ p`（mixedOp¹² = id） |

**实例**：
- `zero-oblivion-instance : ZeroOblivion`（`DuodecClock.agda:673`）
- `dcZeroOblivion : ZeroOblivion`（`DCGroup.agda:153`，第二份）
- `zero-oblivion-to-d0 : toDuodec duodec-e ≡ d0`（`DuodecClock.agda:870`）

**⚠ 别重复实现**：本会话曾写 `dc-oblivion-trit/-phase/-joint` ✗ —— 全部是这三条的重复 ✗（已删除）

---

## 三、Trit 加法归零（`src/Sovereign/Base/Trit.agda`）

| 符号 | 命题 |
|---|---|
| `verifyZero`（:277） | `T₁ ⊕ T₂ ≡ T₀` |
| `verifyMul`（:281） | `T₂ ⊗ T₂ ≡ T₁` |
| `⊕-inverse`（:232） | `∀ x → x ⊕ negate x ≡ T₀` |
| `negate-equiv` | 逐元素取反表 |

---

## 四、展示群模板层（`PresentationTheorems.agda`）

### `g-ne-unit`（**回执 `fe46503a`**）

```agda
g-ne-unit : ∀ {A} (P : Presentation A)
  (0<clk : 0 < clock)
  (1<po  : 1 < phase-order)
  (clock-min : ∀ k → Period (λ y → step y g) k → clock ∣ k)
  (po∣clk    : phase-order ∣ clock)
  → g ≢ unit
```

**普遍定理** ✓ —— 不依赖 DC 的任何特殊结构 ✓
**证明**：若 `g = unit` ⇒ `step y g = y`（`zeroʳ`）⇒ `1` 是周期 ⇒ `clock ∣ 1` ⇒ `clock ≤ 1` ✗
但 `1 < phase-order ≤ clock` ⇒ `clock ≥ 2` ✗ 矛盾 ✓

---

## 五、DC 特有定理（**不写进通用模板** ✗，`Presentation.agda` 末尾，回执 `9e2e0966`）

| 符号 | 命题 | 缺口 |
|---|---|---|
| `dc-phase-step-comm` | `∀ x y → dc-phase (mixedOp x y) ≡ mixedOp (dc-phase x) y` | G3 |
| `dc-phase-g-comm` | `∀ x → dc-phase (mixedOp (T₁,a₁) x) ≡ mixedOp (T₁,a₁) (dc-phase x)` | N8 |
| `dc-clock-neq-phase` | `4 < 12` | N3b |
| `dc-oblivion-algebra` | `T₁ ⊕ T₂ ≡ T₀`（= `verifyZero` 引用，非新增） | 代数归零 |

**⚠ 这些不是普遍约束** ✗ —— 当前 `Presentation` 模板**没有字段**连接 `phase` 与 `step` ✗
（写进模板 = 过拟合 DC ✗ —— 见 `docs/duodecimal/42-presentation-group-definition.md` §4.2）

---

## 六、T4 主线（`GF3HammingCount` 家族）

| 模块 | 关键定理 | 回执 |
|---|---|---|
| `Algebra/LinearAlgebra/GF3HammingCount.agda`（1206 行） | `★a-binomial : C0 n ≡ S'' fzero n`<br>`★b-formula : (S'' fzero n ∸ Z n) + Z n ≡ C0 n`<br>`★C0-3step` / `★C0-odd` | `da832222` |
| `Algebra/LinearAlgebra/GF3HammingCountLink.agda`（158 行） | `★Cnt : ∀ r n → Cnt r n ≡ Cr r n`<br>`★C0-is-hamming : ∀ n → Cnt fzero n ≡ C0 n` | `a2d87388` |
| `Algebra/LinearAlgebra/GF9KernelImageZero.agda` | `q-zero : Ker f → Im f → ∀ x → f x ≡ gf9-zero`（`q_n = 0`） | `4dcfbb13` |
| `Algebra/LinearAlgebra/GF3BnLinearAlgebra.agda`（161 行） | `★AllH : ∀ n → AllH fzero n ≡ Z n` | `4eb44d77` |
| `Algebra/UniversalAlgebra/RnDCPresentation.agda`（143 行） | `RnDCPresentation : (n : ℕ) → Presentation (RD n)`（`clock = 12` ✓） | `647efff9` |

**⚠ 已撤回**：`RnPresentation.agda`（`clock = 4 = phase-order` ✗ 踩 DC 红线 ✗，节点标 `needs_review`）

---

## 七、Presentation 模板的三个实例

| 实例 | 载体 | `clock` | 合法？ |
|---|---|---|---|
| `dc-presentation`（`Presentation.agda:131`） | `DuodecPoint` | 12 | ✅ **本源实例** |
| `RnDCPresentation`（`RnDCPresentation.agda:127`） | `Vec DuodecPoint (3^n)` | 12 | ✅ |
| `RnPresentation`（`RnPresentation.agda:126`） | `Vec GF9 (3^n)` | **4** | ❌ **已撤回**（`clock = phase-order` ✗） |

**⚠ 索引工具只看「字段齐全」✗ —— 语义红线要人工判** ✓
（`engineering/index_presentations.sh` 的免责声明即为此而写）

---

## 八、高阶同伦线 · `π₂ᵈ⁺`（`src/Sovereign/Synthesis/Homotopy/`，2026-10-21 建线）

> **本节只写「有内核回执」的事实**（符号 + 命题 + 回执）。
> 路线判断一律不写 —— 见 `AGENTS.md`「★★ 路线判断也要标推测」。

### 8.1 定义层 → 群结构

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `Omega2.agda` | `Ω1ᵈ` / `Ω2Walk`（`nil2`/`cons2`）/ `Ω2ᵈ` / `_++2_` / `++2-assoc` | `72d0eecf` |
| `Omega3.agda` | `invAStep` / `invAStep-invol` / `Ω3Step`（`fill-tri`）/ `Ω3Walk` / `Ω3ᵈ` | `31bc258e` |
| `Omega3Plus.agda` | `bub` / `Ω3Step⁺` / `embed3` / **`base3+-redundant`**（`base3+` 可由 `bub3` 导出 ⇒ 生成集可缩到 `{whisk3, bub3}`） | `f0fc1f7a` |
| `Omega3Suffix.agda` | `whisk-resp` / `suffix-resp` / **`≡→Ω3Walk⁺`**（propEq → 关系的零成本桥） | `62112afd` |
| `Omega2Reverse.agda` | `rev2` / `rev2-cancel` / **`suffix-cancel`**（带上下文的反向消去） | `b550e39c` |
| `Omega2ReverseInvol.agda` | `rev2-dist` / **`rev2-invol`** / `inv-right-Ω3` | `f76b17cc` |
| `Omega2Std.agda` | `Ω2WalkStd` / `Ω2ᵈˢᵗᵈ` / `++2s-nilR` / `++2s-assoc` | `403e74b1` |
| **`Pi2dFunctionLayer.agda`** | **★ `π₂ᵈ⁺` 是群**（函数表示层，零 Cubical）：`unit-left` / `unit-right` / `assoc-Ω3` / `cong₂-Ω3` / `inv-left-Ω3` / `inv-left-ctx` | `037128ec` |

### 8.2 不变量 → 非平凡性 → 群同态

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `Pi2dParity.agda` | `par2`（步数奇偶）/ **`par2-Walk⁺`**（奇偶是良定义的**类函数**＝分裂器）/ `two-classes`（有自步时**至少**两类） | `0e9a7aa2` |
| `Pi2dWinding.agda` | `wstep`（`slide ↦ +1`、`expand ↦ −1`）/ `wind` / **`wind-bub`**（气泡位移 = 0）/ `wind-Walk⁺` / **★ `no-collapse`**（不同层数不同类 ⇒ **无穷多类**） | `206dc30e` |
| `Pi2dWindingRev.agda` | `wstep-inv-sum` / `rev2-wind-form` / **★ `wind-rev2`**（`wind (rev2 c) + wind c ≡ +0`）⇒ **`wind : π₂ᵈ⁺ →+ ℤ` 是群同态** | `0159b507` |

### 8.3 商路线（另一条，保留）

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `Pi2dQuotient.agda` | `π₂ᵈ` / `π₂ᵈ⁺` / `[_]ᵈ` / `desc` / `π₂ᵈ-hom` / `addL`·`addR` + 结合律（`_/_` 商路线，含 `SetQuotient`） | `113f4102` |

### 8.4 码层（`T6Cayley`，**无证明分量**）

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `T6CayleyDec.agda` | `DecEq-T6Vec`（`Vec (Fin 3) n` 可判定）/ `decAt` / `decAt2` / `findEdge`（`Maybe`，带见证）/ `∈-allFinD`（穷尽性） | `30333b2f` |
| `T6CayleyCode.agda` | `CStep`（`cplus`/`cminus`，**无证明分量**）/ `CWalk` / `DecEq-CStep` / `DecEq-CWalk`（平凡，**不用 uip**）/ **`creduce`**（fuel 递归消相邻逆对） | `a3664bd1` |
| `T6CayleyCodeWalk.agda` | `ctarget` / **`cEdge`（见证 = `refl`，无需搜索）** / `interpC` / `ctarget-inv` / **`ctarget-3`**（每步 3 阶）/ `foldT` / `foldT-++` / `crev` / **`ctarget-rev`**（逆律） | `f07cfdae` |
| `T6CayleyComm.agda` | **`updAt-comm`**（`updAt i` 与 `updAt j` 交换 ⇒ **`(C₃)ⁿ` 作为群 Abel**） | `4ae7a0a7` |
| `T6CayleyNorm.agda` | `cpassA`/`creduceA`（无 fuel）；`NoCancel`（3 构造子）；`cpassS`/`creduceS`；`cpassA-eq`（两者差一个 `reverse`，`refl` 级）；**`cpassS-noCancel`**（①范式性）/ `creduceS-noCancel`；**`adj-sym`/`adj-sym'`**（相邻关系对称，4 情形）；`NoCancelR` + `NoCancel→R`/`R→NoCancel`（双向桥）；`creduceS-noCancelR` | `54107092` |
| `T6CayleySem.agda` | `foldStack`（栈的**右折叠**语义，避开 `reverse`）；**`cpassS-fold`**；**`creduceS-fold`**（③ 归约不改终点） | `b2a04a3a` |
| `T6CayleyBool.agda` | **`finEqB`**（在 ℕ 上比较，不携带证明）+ `complete`/`sound`；`cdEqB`（判定 `x ≡ cstep-inv y`，4 情形）+ `complete`/`sound`/`cdEqB-¬`（**一行** via `T false = ⊥`）；`cpassB`/`creduceB`；`cpassB-noCancel`/`creduceB-noCancel` | `3c10dc1a` |
| `T6CayleyIdem.agda` | `NoCancel-head` / `NoCancel-tail₂`（投影小件） | `6e1b5faf` |
| **`T6CayleyIdem2.agda`** | `pushB` + **`pushB-no-cancel`**（用 `cdEqB-sound` 排空 `true` 分支，**不需反射**）；`cpassApp`（**追加版**，尾部展开）；**`cpassB≡cpassApp`**（桥）；`cpassApp-++`；`reverse-∷`；**`cpassApp-rev`** / **`cpassB-self`**；**★★ `creduceB-idem`** / **★★ `creduceB'-idem`（② 幂等）** | `f6d65f9e` |
| `T6AStepCode.agda` | ④ 探针：`ADir`（`dslide`/`dexpand`）/ `AStepCode n = ADir × CWalk n × CWalk n` / **`DecEq-AStepCode`**（平凡，**不用 uip**） | `f66e1ac2` |

**⑤ 一阶（PIO-2 线）**

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `AStepStdReverse.agda` | **★★ `rev-cancel : ∀ (p : Walk G u v) → AHomotopyStd G (p ++w rev p) (nil u)`**（`sym-edge` 作为假设；一次 `++w-assoc` 运输 + `prefix-cong` + `AHStd-++w` + `rev-cancel-one`） | `d24fbea1` |

### 8.5 ⚠ 已撤回 / 未验证（**别当成已证复用**）

| 曾声称 | 现状 |
|---|---|
| `π₂ᵈ⁺` **至多两类**（⇒ 或 ≅ C₂） | ❌ **已撤回**。`par2-Walk⁺` 只给「良定义」；**良定义 ≠ 单射**，拿不到上界。 |
| `Ω2Walk G x w1 w2` 只在 `w1`、`w2` 相等时可居留 | ❌ **已撤回**。`cons2 s (nil2 w2)` 就是 `w1 ≢ w2` 的居留者。 |
| `π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ`，「五项前置已齐，只差一项」 | ❌ **路线判断已撤回**：该「差距分析」本身未核实。**已证的只有** 8.4 表里的那些符号。 |

**现已补上的（原 8.5 里的「未做」项）**：

| 曾未做 | 现状 |
|---|---|
| `creduce` **范式性**（一遍不保证到不动点）| ✅ **已证**：`creduceS-noCancel`（`54107092`）/ `creduceB-noCancel`（`3c10dc1a`）|
| `creduce` **幂等** | ✅ **已证**：`creduceB'-idem`（`f6d65f9e`）—— 注意**正确陈述是 `reverse ∘ creduceB`**（`creduceB` 本身**不**幂等，oracle `0c189883` 给出 4056 反例）|
| `creduce` **语义正确** | ✅ **已证**：`creduceS-fold`（`b2a04a3a`）|
| ④ 的可行性探针 | ✅ **通过**：`AStepCode` + `DecEq-AStepCode`（`f66e1ac2`）—— 二级码可判定，**不用 uip** |

**仍未做**（如实标注）：

| 项 | 说明 |
|---|---|
| **范式唯一（汇合性）** | ⬜ 未做。`creduceB'-idem` 只给「再归约不变」，「不同路径到同一范式」未证。 |
| **④ 的码→步影射** | ✅ **步 1–6 全部完成**（归约所需范围内已闭合）：六组件码 + `DecEq`（`92938fa5`）/ 两条走 + 侧条件可判定（`4c84d29a`）/ `interpC-end`（`a958d82c`）/ `interpAt` + `interpAt-++` + **`toStep`**（`5f8d6110`）/ `subst-cons` + `subst-irrel` + `stepE3-irrel`（`fe3075c1` / `fa8be818`）。⚠ 两处**更正**：(i) 原记「需要 `Maybe`」**错** —— `slide` 的 `e1,e2,e3` 是**显式参数**，映射无需搜索；(ii) `interpAt-++` 卡 4 批的**根因是陈述方向错**（`subst P eq : P x → P y`，而 `interpAt (foldT u a) b` 落在 **y 侧** ⇒ 需 `sym`），**不是证明难**。|
| **④ 的忠实性（`toStep-irrel`）** | ⬜ **未做，且判定不属归约所需**：`toStep` 的**返回类型依赖 `h`** ⇒ 依赖余定义域 ⇒ `cong` 不适用；正确写法需 `subst` 把类型搬到 `h'` 侧，而 `subst` 沿 `e` 作用在 `slide … e` 上不归约 ⇒ 是 **heterogeneous equality（John Major）** 困难，本库不用 `HEq`。**[判断·非定理]** 归约只需**可靠性**（同码 ⇒ 同一步，由「`toStep` 是函数」**定义性成立**），不需要忠实性。 |
| ~~`sym-edge` 的可构造性~~ | ✅ **已完成**：`T6SymEdgeReverse.sym-edge-T6`（`feee492f`，靠 `updAt-cubed`）+ `rev-cancel-T6`（`rev-cancel` 在 `T6CayleySym` 上**无条件**）。 |
| **`π₂ᵈ⁺` 的精确刻画** | ⬜ 形状未定。`ASTep` 含见证 ⇒ 一般图不可判定（见下「已知墙」）。 |

### 8.6 ⚠ 已知墙（**下次别再撞**）

| 墙 | 内容 |
|---|---|
| **`Dec` 的见证需要无关性** | 证 `DecEq-CStep x y ≡ yes p / no ¬p` 需 `CStep` 的 **UIP**（`yes` 侧）或 **funext**（`no` 侧）；本库纯 PropEq 下都没有。stdlib 的 `≟-≡`/`≟-≢`（`Data/Fin/Properties.agda:111-118`）**存在但不够**（它们给的证明项与我需要的不一定相同）。⇒ **绕过：换 `Bool`**（`T6CayleyBool`）：`finEqB` 在 ℕ 上比较、`T false = ⊥` 一行闭合 —— 已奏效。 |
| **`T b` ≠ `b ≡ true`** | `T true = ⊤` ⇒ 陈述用 `T`，不要用 `≡ true`。 |
| **`with … in eq`** | 想拿到「决策 = `false`」作为**见证**，必须写 `in eq`；否则分支里拿不到。 |
| **`Data.Bool` 的 `true`/`false` 要显式 import** | 否则在模式里成变量（`PatternShadowsConstructor` + `UnreachableClauses`）。 |
| **`AHStd-++w` 的第一个参数是 `Walk`（后缀）** | 不是 homotopy；`rfl` 也是**函数**（`rfl (nil v)`）。 |
| **`reverse-∷` 与头部递归方向相反** | `reverse (x ∷ xs) = reverse xs ++ [x]` 把 `x` 推到末尾 ⇒ 对「从头部递归」的函数归纳假设用不上；**改用「追加版」（尾部展开）** 就通（`cpassApp` 一案）。 |

### 8.7 方法（本线验证有效的两条）

1. **先算后验证**：陈述拿不准时，先用 `proof_oracle` **全枚举**（非抽样，`points = domain`）定陈述。
   实例：`creduceB'` 幂等 0 反例 / `creduceB` 4056 反例（回执 `0c189883`）—— 避免拿错陈述施工。
2. **换到不带证明的载体**：本线已 6 次靠这一手法过关
   （码层 → 二级码 → 右折叠 → 阅读序谓词 → `Bool` 决策器 → 追加版）。
3. 猜 API 两次仍不对时，**直接查源码**（`grep` 定义），别再猜。

**⚠ 层级提醒（已核实）**：`Ω2Walk` 的步是 **`ASTep`（一阶同伦）**，不是图边；
而 `CStep` 是**图边方向** ⇒ **码层服务 `π₁ᵈ` 层，不是 `π₂ᵈ⁺` 层**。

---

## 九、维护约定

1. **新增 proven 时**：在本清单对应章节加一行（符号 + 命题 + 回执）
2. **撤回时**：**不删除** ✓ —— 标 ⚠ 并写撤回理由（台账只增不改史 ✓）
3. **本文件与台账冲突时**：**以台账为准** ✓（`proof_dag` 是机器权威 ✓）
