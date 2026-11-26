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
| `T6AStepCode2.agda` | ④ 修正：**六组件**码 `StepCode`（方向+前缀+`e1`+`e2`+`e3`+后缀）+ `DecEq-StepCode`（6 层 `with` + 6 个 `cong` 链，**不用 uip**）—— 因为 `slide` 的 `e1,e2,e3` 是**显式参数** | `92938fa5` |
| `T6AStepMap.agda` | ④ 骨架 + 走层：`srcCode`/`tgtCode`；**`StepSide`**（走层侧条件）+ `decStepSide`；`interpC-++` / **`interpC-end`**（`refl` 级）；**`StepVertex`**（顶点层侧条件）；**`StepVertex→fold`** / **`StepVertex→StepSide`**；**`ctarget-inj`** / **`foldT-inj`**（每步双射 ⇒ `foldT` 对起点单射）；**`StepSide→StepVertex`**（⇒ **`StepSide ⇔ StepVertex` 等价**）；`interpC-walk` / **`interpC-++-walk`**（走层 `++` 分配律）/ `interpC-walk'`；`subst-sym-inv`；**`StepSide ⇔ StepSide-fold`**（双侧齐）；**`astStep-cast`**（`ASTep` 端点铸型，一行）；**`decStepVertex`**（顶点层侧条件**可判定**）| `70b82d86` / `0790d979` / **`badda7a9`** |
| **`T6CayleyInterp.agda`** | `interpAt`（码 → 走，终点 = **可计算**的 `foldT u w`）；**`subst-cons`**（一行）；`stepE1`/`stepE2`/`stepE3`；**★★ `toStep`（构造 `ASTep` 值）**；**`interpAt-++`**（卡 4 批，根因是**陈述方向错** —— 需 `sym`）；`subst-irrel`（Hedberg）/ `stepE3-irrel`；`subst-++w` / `interpAt-++-glue`；**`slide-subst`**（一行）+ **`toStep-irrel`（步 7 忠实性）**；§7 具体点验证 `x1`/`side-ok`/`endpoint-1`/`step-1` | `42f221a8` |
| `T6CayleyCheck.agda` | **①②③⑤ 的具体点对抗验证**（纪律 §6，9 条全 `refl`）：`check-nil`/`check-one`/**`check-cancel-pair`**/`check-cancel'`/**`check-three`（三步同向不消 —— 顶点层 vs 消去层的分离）**/`check-idem-1`/`check-idem-2`（② 幂等）/`check-end`（③ 语义）/`check-interp`；**`check-rev-one`/`check-rev-cancel`（⑤ 逆律）** | `c78ee4e5` |
| `T6AStepCodeMap.agda` | ④ 末段（**`toStepCode` 剩余部分判定为「纯管道」**：cast 对齐 5–6 条交换引理，**不产生新数学内容**）：**`toStep-vertex-form`**（把 `toStep` 的 `stepE1/E2/E3` 定义性展开 ⇒ **内核证据：侧条件是顶点层**）+ `srcCode-glue`（码展开）| `7fba6f38` |

**⑤ 一阶（PIO-2 线）**

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `AStepStdReverse.agda` | **★★ `rev-cancel : ∀ (p : Walk G u v) → AHomotopyStd G (p ++w rev p) (nil u)`**（`sym-edge` 作为假设；一次 `++w-assoc` 运输 + `prefix-cong` + `AHStd-++w` + `rev-cancel-one`） | `d24fbea1` |
| `T6SymEdgeReverse.agda` | **★★ `sym-edge-T6`**（`T6SymEdge x y → T6SymEdge y x`，靠 `updAt-cubed`）+ **`rev-cancel-T6`**（`rev-cancel` 在 `T6CayleySym` 上**无条件**） | `feee492f` |

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

### 8.7 方法（本线验证有效的四条）

1. **先算后验证**：陈述拿不准时，先用 `proof_oracle` **全枚举**（非抽样，`points = domain`）定陈述。
   实例：`creduceB'` 幂等 0 反例 / `creduceB` 4056 反例（回执 `0c189883`）—— 避免拿错陈述施工。
2. **换到不带证明的载体**：本线已 7 次靠这一手法过关
   （码层 → 二级码 → 右折叠 → 阅读序谓词 → `Bool` 决策器 → 追加版 → 「不吃 `p` 吃码」）。
3. 猜 API 两次仍不对时，**查源码**（DSH `grep` 定义），别再猜。
4. **★ `T`-反射里的 `⊥` 细化要「带引理进 `with`」**（本会话踩了 3 次）：
   `T (no ¬p) = ⊥` **只有** `no ¬p` 真的被代入时才成立 ⇒ 在 `with` 里**必须同时带分量引理**：
   ```agda
   Fin-refl (suc i) with i ≟ i | Fin-refl i
   ... | yes p | _  = refl
   ... | no  ¬p | h = ⊥-elim h      -- h : ⊥（只有带了 Fin-refl i 才拿得到）
   ```
   只写 `with i ≟ i`（不带引理）⇒ `⊥` 假设不会被细化 ⇒ `⊥-elim` 拿不到 `⊥` ✗。
   ⇒ 这是 `Dec`/反射型证明的**通用形**，与 §1b 的 `subst-cons` 同族（都是「把该有的见证带进作用域」）。
4. **★★ 「收口」前的覆盖率自查（本会话末三批连续靠它发现真问题）** —— 说「已完成」之前逐项问：

   | 问 | 本会话的实例 |
   |---|---|
   | ① 每个 `data` 的**构造子**都被处理了吗？ | `toStep` 的签名**没有 `ADir`** ⇒ 只造 `slide`，**从不造 `expand`** ✗ |
   | ② 每个构造子都有**具体点**验证吗？ | 只有 `slide` 有 `step-1`，`expand` 没有 ✗ |
   | ③ 参数的**方向/分支组合**至少各一支都验过吗？ | 只验过 `s1 = s2 = cplus`；`cminus` 在 `s1`/`s2` 从未验 ✗ |

   **判据**：拿「签名里有、实现里没用上的参数」当红旗（`ADir` 就属此类）；
   拿「`data` 有几个构造子」逐个数，对不上就是缺口。
   **代价对照**：本会话三次「已收口」的宣告都早了一步 ✗ —— 而补缺口每次只花 1–3 次编译。

**⚠ 层级提醒（已核实）**：`Ω2Walk` 的步是 **`ASTep`（一阶同伦）**，不是图边；
而 `CStep` 是**图边方向** ⇒ **码层服务 `π₁ᵈ` 层，不是 `π₂ᵈ⁺` 层**。

---

## 十、多面体群 / 内嵌富勒烯线（`src/Sovereign/Synthesis/Physics/`，2026-10-22 建线）

| 模块 | 关键定理 | 回执 | 说明 |
|---|---|---|---|
| `IhGroup.agda` | `a5-card-check`（1+15+20+24 ≡ 60）、`ih-card-check`（2×60 ≡ 120）、`polar-winding-check`（120+24 ≡ 144） | `c024f1ed…` | `IhOrder` 已从字面量改为由构造子基数推出；§6 八要素表已按代码实际更正（原全标 ✓ 与模块头 5/8 矛盾） |
| `IhDecomposition.agda` | `a5-order-check`、`ih-total-check`、`merkaba-check`、`holographic-check`、`polar-consistent` | `45bb1432…` | 24 的口径改为 **2A₄**（二元四面体群 SL(2,3)）；§1 注释更正：A₅ 有 **5** 个共轭类（1,15,20,12,12），24 = 12+12 |
| `PolyhedralReps.agda` | `a4/a5/two-a4/two-a5/ih-dim-sum`（Σdᵢ²=|G|）、`ih-class-sizes-sum`、`orbit-stabilizer-vertex`（120 ≡ 60×2） | `46b697b0…` | 不可约表示维数与共轭类数为**数值核验**（四元数模型）；Agda 只证算术 |
| `NoSplitJ1.agda` | `no-split-diag`：对角算符与 A₄ 的 3-循环交换 ⇒ 三个对角元相等 | `53f331b3…` | **只证对角情形**；一般情形需整环无挠性，已在模块头标 roadmap |
| `TRMultipletsZ.agda` | `sq-suc-Z`：ℤ 上 x² + (2x+1) ≡ (x+1)²（RingSolver 宏，代数核心） | `6f4517ba…` | — |
| `TRMultipletsNat.agda` | `sum-odd`：∀ a n → sumOdd a n + a² ≡ (a+n)²（**完整 ℕ 索引版**）+ 4 个实例 | `262bbfb8…` | 距 Σ_λ(2λ+1)=(2l+1)(2J+1) 只差 a=J∸l、n=2l+1 的实例化 |
| `NoSplitJ1Full.agda` | `no-split-full`：与 shift + flip 都交换 ⇒ 6 个非对角元为 0、三个对角元相等（标量）；另 `shift³`、`flip²`（生成元阶） | `c9d1e186…` | 一般情形（含非对角）；无挠性用构造子互异证 `neg-eq-self`；生成元阶 `shift³`/`flip²`/`g³`（g=flip∘shift）全在 Agda；闭包 = 12 阶 = A₄（oracle 回执 `56921d3e…`） |
| `NoSplitJ1Ring.agda` | `no-split-ring-general`：**无挠交换环** R 上，与 shift、flip 都交换的 3×3 矩阵 ⇒ 六个非对角元为 0、三个对角元相等（标量）。`TorsionFree = ∀ x → - x ≈ x → x ≈ 0#` 是唯一额外假设 | `7890fd1c…` | **从 ℤ 提升到任意无挠交换环**（stdlib `CommutativeRing`，等式取 setoid `_≈_`，不引入可判定相等）；证明结构与 NoSplitJ1Full 逐条对应；§9 实例化到 ℤ（复用 `neg-eq-self`）+ §9b **内核核验推广蕴含 ℤ 版** `no-split-full`（逐点转换后类型检查器接受）；oracle `fea7e790…`：GF(3)^9 全穷举 19683 + GF(p)/ℚ 精确消元维数 1 + GF(2) 非标量反例（无挠性不可去） |
| `IhC60Vibration.agda` | `freq-46`、`dim-174`、`vib-vector`、`active-plus-dark` | `28fef4c6…` | 本线既有；本轮几何独立复核 + 去重重命名（`dim`/`count`/`classSize` 等 6 个通用名加 `vib` 前缀），duplicate 审计 151/151 无同名 |

**独立复核记录（Python 侧，非 Agda）**：2A₅ 阶 120 / 2A₄ 阶 24 / 2A₄ ⊂ 2A₅；I_h 特征标表正交性 100 项（最大偏差 5.9e-17）；
I_h 作用于 60 顶点的顶点对 1770 个 ⇒ 23 个轨道（Burnside 与直接枚举一致）；Plancherel 熵表（A₄ 1.2075 … I_h 2.9543）。

**同数异物（写文档时必须区分）**：|2A₅| = 120 = |I_h| 但 2A₅ ≇ I_h（I_h 无 4 阶元）；24 有 2A₄ 与 A₄×C₂ 两种不同实现。

## 九、维护约定

1. **新增 proven 时**：在本清单对应章节加一行（符号 + 命题 + 回执）
2. **撤回时**：**不删除** ✓ —— 标 ⚠ 并写撤回理由（台账只增不改史 ✓）
3. **本文件与台账冲突时**：**以台账为准** ✓（`proof_dag` 是机器权威 ✓）

---

## 十二、C₆₀ 内嵌分子 / 中微子味（2026-10-24 新增）

> **本节的模块已被 `check_duplicate.sh` 误报为重复**（13/15 条是文件与自己比）。
> **绕过时已 `journal` 记录**（规则集 `r16/1e254b5f`）。

### `Sovereign.Application.Physics.NeutrinoFlavorGF3`

**文件**：`src/Sovereign/Application/Physics/NeutrinoFlavorGF3.agda`
**回执**：`a42aa456ff1617bfa2434139c8620cab72ed78ce634c300a224e70392d1b04cf`
**台账**：`IceCube.flavor-gf3-zero-sum`（proven）

| 符号 | 命题 |
|---|---|
| `source-zero-sum` | `(T₁,T₂,T₀)` 的 GF(3) 和 ≡ T₀ |
| `earth-zero-sum` | `(T₁,T₁,T₁)` 的 GF(3) 和 ≡ T₀ |
| `c-gives-zero-sum` | **充分性**：`(a,b,negate(a⊕b))` 必零和（**只用 `⊕-inverse`，无 case**） |
| `zero-sum-gives-c` | **必要性**：零和 ⟹ `c ≡ negate(a⊕b)`（27 案：9 `refl` + 18 荒谬模式） |
| `neg-preserves-zero-sum` | `negate` 保持零和 |
| `neg-distrib-⊕` | `negate(x⊕y) ≡ negate x ⊕ negate y`（9 案） |

**核心**：零和 ⟺ `c = negate(a⊕b)` ⇒ 零和集是线性泛函的核（9 元素），**不是 27 案穷举**。

**⚠ 诚实边界**：
- `(T₁,T₁,T₁)` 与 `(T₂,T₂,T₂)` **都是**等分量零和态，`negate` 互换 ⇒ **「(1,1,1) 唯一」不成立**
- 不涉及 PMNS 矩阵 / 质量平方差 / CP 相位
- 「混合保持零和」需幺正性，**未形式化，不是定理**

### `Sovereign.Application.Physics.TracelessCentroidZero`

**文件**：`src/Sovereign/Application/Physics/TracelessCentroidZero.agda`
**回执**：`69a38f55846706c8e3cb7df5c0bc0c10cbd960b9f8d3c4bf2f63908a30469f11`
**台账**：`Endofullerene.traceless-centroid-zero`（proven）

| 符号 | 命题 |
|---|---|
| `three-axis-is-trace` | `three-axis-sum T ≡ trace T`（`refl`） |
| `traceless-three-axis-zero` | `Traceless T → three-axis-sum T ≡ +0` |
| `traceless-six-axis-zero` | ⭐ **`Traceless T → six-axis-sum T ≡ +0`** |

**⚠ 关键设计**：
- **必须在 ℤ 上**（char 3 中 `3 ≡ 0` ⇒ 「`3·tr ≡ 0`」**平凡成立**，定理内容消失）
- **离散化**：取向集取六条坐标轴 `{±e_x,±e_y,±e_z}`，不引入 ℝ / 球面积分 / 测度
- **「×2」写在定义里**（`six-axis-sum T = three-axis-sum T + three-axis-sum T`），避免循环论证

**⚠ 诚实边界**：
- **未证明**「六轴等权平均 = 球面平均」——只证了六轴和的陈述
- **未证明**任意取向集（非六轴）的版本

### ⚠ 本节的「不要重做」清单

| 别重做 | 原因 |
|---|---|
| 「无迹 ⇒ 质心位移为零」 | 已证（`TracelessCentroidZero`）+ 数值验证（0.046/0.043 cm⁻¹） |
| 「HF 中心下移是四极效应」 | ❌ **已否证**（9×9 里质心只动 0.043 cm⁻¹） |
| 「锁定假说（线性分子 ⇒ 四极不平均）」 | ❌ **模型否定**（9×9 天然含 M 混合，无法锁定） |
| 「P/H × 2+1 给 4 个分量」 | ⚠ **4 参数拟合 4 点，不是证据** |
| 「1.5 因子」 | ✅ 已定位为代数错误（`Q₂₀ = Q − tr/3`，旧迹非零） |

---

## 十三、H₂O 四极张量的**权威值**（2026-10-24 追加，防再错）

> **为什么单列**：本会话对这一个张量改了 **5 次**，每次都以为对了。
> **根因**：没有先查权威文献就凭「偶极沿 C₂ ⇒ 四极也沿 C₂」的直觉填数。

### 权威值（**Verhoeven & Dymanus, JCP 52, 3222 (1970)**）

**轴定义（**关键，容易搞错**）：**

| 文献轴 | 位置 | 主惯量轴 |
|---|---|---|
| **z** | **沿 C₂ 对称轴** | **b** |
| **y** | **面内垂直 C₂** | **a** |
| **x** | **面外** | **c** |

**分量（Buckingham = 10⁻²⁶ esu·cm²）：**

| 分量 | 主惯量轴 | **Buckingham** | **a.u.** |
|---|---|---|---|
| **Θ_xx** | **c** | **−2.50 ± 0.02** | **−1.859** |
| **Θ_yy** | **a** | **+2.63 ± 0.02** | **+1.955** |
| **Θ_zz** | **b** | **−0.13 ± 0.03** | **−0.097** |

**⇒ 按主惯量轴排：`(Θ_a, Θ_b, Θ_c) = (+2.63, −0.13, −2.50)`**

### ⚠⚠ 三条「不要搞错」

| # | 易错点 | **正确** |
|---|---|---|
| **1** | **最大分量在 b 轴（C₂）** | ❌ **错**——最大在 **a 轴（面内垂直 C₂）** |
| **2** | **Felker 的 `Θ_b = −0.13` 是 a.u.** | ❌ **错**——那是 **Buckingham**（a.u. 是 −0.097） |
| **3** | **符号** | ⚠ 四极矩有两种约定（`3x_ix_j−r²δ` vs `r²δ−3x_ix_j`），差一负号 |

**⭐ 物理上为什么最大在 a 轴：**
**⇒ 偶极沿 C₂（b 轴，**瘦**），四极在垂直于 C₂ 的方向最大（a 轴，**胖**）——孤对电子云。**

### 本库代码用的值

**`engines/eoh/molecules_theta.py` 的 `Q_H2O_FULL`：**
```python
Q_H2O_FULL = (-2.63, 0.13, 2.50)   # (a, b, c) = 文献值整体取负
```

**⇒ 取负的理由：观测「m=±1 在 m=0 之上」⇒ doublet 在上 ⇒ 要求 `Θ_c > 0`（本约定）。**
**⚠ 这是**条件性结论**（若文献符号约定与我们的相同，则矛盾未解）。**

### ⚠ 数值结论**不受轴归属影响**

**⇒ 9×9 实测：a↔b 对调**不改极差（4.562）也不改能级顺序**。**
**⇒ 因为比值用 `|Q₂₀| = 2.50`。**

### 三个 Θ 的可靠度分层

| 分子 | Θ_zz (e·a₀²) | 来源 | 可靠度 |
|---|---|---|---|
| **HF** | **2.295** | 文献 1.706 a.u.（四方法 3%）+ Felker 零参数 3.86 vs 3.9 | **高** |
| **H₂** | **0.652** | **Felker 0.652** + 零参数 1.096 vs 1.09±0.01 | **高** |
| **H₂O** | **2.50** | **Verhoeven 1970**（2.63 Buckingham）| **高**（本会话最后确认） |

**⇒ **⇒ 三个都「高」⇒ 三个比值都有文献支撑**（早先说 H₂O「中」是因为当时没查文献）。

---

## 十四、⚠⚠ **数据归属更正**：那 4 个峰**不是** H₂O@C₆₀（2026-10-24 终稿）

> **为什么单列**：本会话花**十几轮**分析「H 位点为什么是 1.30 而不是 0.13」，
> 而**真正该做的第一件事**是验证那 4 个峰是不是 `H₂O@C₆₀` 的。

### 一、结论

**⇒ `3754.2 / 3758.4 / 3750.8 / 3752.1 cm⁻¹` 这 4 个峰 **不是** `H₂O@C₆₀` 笼内数据。**
**⇒ 它们是 **Ar / p-H₂ 基质中自由 H₂O 单体**的 ν₃ 位点裂分。**

### 二、三条判据（**任一条都足够**）

| # | 判据 |
|---|---|
| **1** | **笼内伸缩相对气相**红移 2.4%**（Rõõm 2021 原文）；这 4 峰**几乎无红移**（−1.9 cm⁻¹） |
| **2** | **笼内伸缩在 3573.2（ν₁）/ 3659.6（ν₃）**；这 4 峰在 **3750–3758**（气相 3755.8 附近） |
| **3** | **Chartrand 2025 的 39 条 ro-vibrational 跃迁**全在 3500–3680 / 3400–3580，**无一条**在 3750–3758 |

### 三、⚠ 易错点（**三条，都踩过**）

| # | 易错 | **正确** |
|---|---|---|
| **1** | **`ω₁ = 3573.2` 是 `ν₃`** | ❌ **`ν₁`（对称伸缩）**；`ν₃ = 3659.6`（反对称伸缩） |
| **2** | **「红移 180–190」是理论预言** | ❌ **是「气相 `ν₃` − 笼内 `ν₁` 实测」的跨模巧合**（`3755.9 − 3573.2 = 182.7`） |
| **3** | **Felker 2020 引用为 `JCP 153, 074107`** | ❌ **该卷页是「H₂O-CO and D₂O-CO complexes」**；正确是 **`JCP 152, 014108`**（DOI `10.1063/1.5138992`） |

### 四、✅ 已立住的（**8 条，不受上述更正影响**）

| # | 结论 | 验证 |
|---|---|---|
| **1** | **`HF/H₂ = 3.5199 vs 3.5616 ± 0.132`（−1.2%，0.32σ）** | 自算，零自由参数 |
| **2** | **`tr(Θ)=0` ⇒ 质心位移为零** | **Agda 已证** |
| **3** | **2 模块 / 12 命题**（`NeutrinoFlavorGF3` / `TracelessCentroidZero`） | 回执 `a42aa456ff16` / `69a38f558467`，**哈希逐字符一致** |
| **4** | **`m=±1` doublet 在 `m=0` 之上** | Rõõm 2021 原文直引 |
| **5** | **`ν₁=3573.2 / ν₂=1570.0 / ν₃=3659.6 / ν_trans=110 / \|101⟩=4.2`** | Rõõm 2021 TABLE II |
| **6** | **`A = eQq/h`（含 `Q`）** | Felker 2017（Gemini 转述 + 待原文二次确认） |
| **7** | **`s_H = 4.2/30 = 0.14 cm⁻¹ < 线宽 0.35`** | **30× 是分裂比**（Felker 摘要「level splittings ... 30 times smaller」）；与「HF 只有一对峰」一致 |
| **8** | **4 峰（3750–3758）不是笼内数据** | 三方证据 |

### 四点五、⚠⚠ **外部转述数据的可靠性**（2026-10-24 教训）

**⇒ Gemini 对**同一篇论文**（Felker & Bačić, `JCP 152, 014108`）给出了**三个互相矛盾**的版本：**

| 轮 | 声称 | 引文 | 与 PubMed 摘要 |
|---|---|---|---|
| **①** | 红移 183.6/184.1 | ❌ `JCP 153, 074107`（该卷页是 H₂O-CO 二聚体） | ❌ 矛盾 |
| **②** | **蓝移 ~24 cm⁻¹** | ✅ `JCP 152, 014108` | ✅ **一致** |
| **③** | 红移 86.5/183.1 | ✅ `JCP 152, 014108` | ❌ **矛盾** |

**⇒ **唯一可独立验证的锚点**：PubMed `31914751` 摘要逐字 ——**
> **「...the caged H₂O are **blueshifted** relative to those of the gas-phase H₂O, the two stretch modes much more so than the bend.」**

**⇒ **⇒ 只采信 ②（与摘要一致）；①③ 一律标「未验证」。****

**⚠ 且 ③ 的 `ν₃ = 3572.8` 恰好落在**跨模假连接**上：**
```
气相 ν₃ (3755.9) − 笼内 ν₁ 实测 (3573.2) = 182.7
⇒ 「红移 180–190」是这个巧合，不是任何理论预言
```
**⇒ Gemini 在这个巧合周围构建了「TR 侧带 +86.8」的故事，但该解释已被否证：**
- **能量尺度不符**：TR 侧带是 `ν_trans = 110`，**不是 86.8**
- **原文不支持**：Rõõm 2021 **没有**把 `3659.6` 归因于「带轴 + 86 侧带」
- **与蓝移矛盾**：若预言蓝移，带轴应在 `3755.9` **之上**

### 五、⚠ 未解决的**真实物理张力**

> **Felker 2020（9D 全耦合理论）预言**蓝移**（摘要逐字：「are **blueshifted**」）**
> **Rõõm 2021（IR 实验）实测**红移 2.4%**（TABLE II）**
> **⇒ **方向相反**。**

**⇒ Felker 2020 原文自述：「Further progress hinges on the experimental measurement ... and ab initio calculation of a high-quality 9D PES, **neither of which is presently available**.」**

**⇒ **⇒ 解决它需要做 9D 全耦合计算，超出转子+平动（5D/6D）模型能力。**

### 六、代码层面的防护（`engines/eoh/`）

| 防护 | 内容 |
|---|---|
| **`molecules_theta.py`** | **两套常数分开命名**：`H2O_AR_MATRIX_NU3_PEAKS`（带 `DO_NOT_USE_AS` 标记）/ `H2O_C60_CAGE_NU3_PEAKS` |
| **三道门禁** | `assert_no_cross_contamination()` / `assert_anchors_consistent()` / `check_refs.py` |
| **测试** | **29 个 pytest**（含 9 条归属回归测试） |

### 七、⭐ 三条方法论判据（本会话 30 次更正的结晶）

> **⑫ 分析任何「特征」前，先验证它的**归属**（哪个体系的哪个跃迁）。**
> **⑬ 拿到全文后，先**通读关键数值**（坐标约定、张量值）再推导。**
> **⑮ 两个数字「看起来正好相等」时，先检查是否描述**同一个物理量**；跨模/跨体系的数值碰巧相等，是最常见的假连接。**

---

## 十三、RH 全称化线（F₃/F₉ Weil 离散 RH，2026-11-24 建线）

> 目录：`src/Sovereign/Application/Problems/RH/`（18 模块，`check_rh_chain.sh` 全绿 ×2）。
> 数值权威：`engineering/oracle_rh_tables.py`（check/emit/emit9/norm 四模式）。
> 台账登记待 Linux 机（本机无 proof_dag），符号+命题先行入册防重复。

### 范数方程线（M2）

| 符号 | 位置 | 命题 |
|---|---|---|
| `classify` | `NormClassify.agda`（§8 末） | **∀② 全称分类**：`∀ n t s → sol n t s → BSol n t s`（v2 冻结：n=2k ↔ (3^k,3^k)/(2·3^k,0)；n=2k+1 ↔ (0,2·3^k)/(3^{k+1},3^k)，ℕ 正部） |
| `descent1` | `NormClassify.agda` §7 | `sol (suc m) t s → Σ t₀, t ≡ t₀·3 × sol m s t₀`（mod-3 三案剥层, 角色互换） |
| `no-suc-mult3` | `Mod3Core.agda` | `suc (3·A) ≢ 3·q`（互递归归纳; r=1/2 反证核） |
| `no-suc4-mult3` | `NormClassify.agda` §7 | `suc⁴ (3·A) ≢ 3·q`（RHS 经 `3suc` 归位后剥三层） |
| `tri3-split` | `Mod3Core.agda` | `∀ t, t ∈ {q·3, suc(q·3), suc(suc(q·3))}`（**右乘形式**: +3 平移 = 纯 cong） |
| `t0-odd` | `NoNormT0General.agda` | **t=0 唯一性**: `sol n 0 s → ∃k, n = 2k+1 ∧ s = 2·3^k` |
| `witness-sat` | `Witness.agda` | `∀ n, wt n² + 3·ws n² ≡ 4·3ⁿ`（两步归纳; 正部见证可解方向） |
| `no-norm-t0-even` | `NoNormT0Even.agda:411` | `∀ m → ¬ Σ ℤ s, 3s² ≡ 4·3^{2m+2}`（t=0 偶指数无解, ℤ 层） |

### F₃ 曲线线（M1/M3）

| 符号 | 位置 | 命题 |
|---|---|---|
| `hasse-all` | `HasseAllF3.agda` | **∀①** `∀ c → IsNonSing c → 1 ≤ #E ≤ 7`（⟺ t ∈ {−3..3}） |
| `trace-in-Tr3` / `trace-witness` / `val-inj` | `TraceTableF3.agda` | 迹集恰 7 值三件套（全覆盖 / 7 值见证 / 49 案单射） |
| `sup-trace` | `SupersingularF3.agda` | **∀③** `IsSup c → t ∈ {−3,0,+3}`（27 分派） |
| `water-iff` | `WaterhouseF3.agda` | `IsSup c ↔ t ∈ {−3,0,+3}`（⟸ `water-bwd` 27 分派; ⟹ 复用 sup-trace） |
| `water-surj` | `WaterhouseF3.agda` | **∀④** 界内每迹可实现（trace-witness 别名） |

### F₉ 线（M4）

| 符号 | 位置 | 命题 |
|---|---|---|
| `pe9-*`（18 条） | `CountF9All.agda` §5 | 18 条 #E(F₉)（oracle emit9 逐字; Agda 与 Python 独立枚举 18/18 一致） |
| `recurrence-all` | `WeilRecurrenceAll.agda` | **∀⑤** `t₂ = t₁² − 2q`（q=3; 27 分派 ×18 refl） |
| `bsd9-all` | `WeilRecurrenceAll.agda` | ∀BSD9 `#E(F₉) = 10 − t₂`（WeilRigidity 三例全称化） |

### A1 · D0/D1 d=1 范数线基案（2026-11-25, RH 线）

| 符号 | 位置 | 命题 |
|---|---|---|
| `norm-d1` | `oracle_rh_tables.py` | x²+y²=4·3ⁿ n≤12 全枚举: **可解 ⟺ n 偶**（±2·3^k,0)/(0,±2·3^k); n 奇无解 ✓ |
| `solD1`/`BSolD1` | `NormD1.agda` | 系数-1 范数载体 + 偶-only 冻结族 |
| `xCap-le`/`yCap-le`/`9≤4-empty` | 同上 | 系数-1 上界链 + 新封闭空型 |
| `base0-thm`（9 格）/★ `base1-thm`（n=1 **无解定理**, 16 格） | 同上 | 奇指数镜面（与 d=3 t=0 谱系互为镜像） |

### A1 · D2/D3 d=1 递降核 + 全称分类（2026-11-25, RH 线——d=1 线收口）

| 符号 | 位置 | 命题 |
|---|---|---|
| ★ `nm3s2` | `NormD1.agda` §6a | suc²(3·A) ≢ 3·q —— 剥两层 suc 后**归约到 no-suc-mult3**（3 行; 非 A-归纳重写） |
| ★ `x1-shape` | 同上 §6b | x ≡ 3q+1 ⇒ x² ≡ suc(3·K₁)（sq-suc + shape1 镜像, ≡-Reasoning 形态） |
| ★ `x2-shape` | 同上 §6c | x ≡ 3q+2 ⇒ x² ≡ suc(3·suc J) —— **suc⁴ 经 sym(cong suc (3suc J)) 一行归一**, 免去 r2 全链的 suc⁴ 载体 |
| `s1s0`/`s0s1`/`s1s1` | 同上 §6d | 和式形状件 —— 六个非零 mod-3 组合全部化归 no-suc-mult3 / nm3s2 两核（**无需 no-suc4/5/8-mult3**） |
| `xnz1`/`xnz2`/`ynz1`/`ynz2` | 同上 §6e/f | x≢0（对 y 三案）/ y≢0（x 已定）矛盾（S 步先 `cong (z+y·y) xx` 定位重写再形状件——探针实测教训） |
| `sol-nextD1` | 同上 §7 | **双剥层**: 9·(t₀²+s₀²) ≡ 4·3^(m+2) ⟹ t₀²+s₀² ≡ 4·3^m（mul4-3out 双次 + mult3-inj 双次） |
| ★ `descentD1` | 同上 §7 | tri3-split **双坐标 9 案** = 8 矛盾 + 1 剥层（d=3 的 descent1 双坐标推广） |
| `pow3-dub` | 同上 §8 | 3^(2k) = (3^k)²（dub-suc + Witness sq3 归纳） |
| `witness-satD1` | 同上 §8 | (2·3^k)² + 0 ≡ 4·3^(2k)（*-assoc 链; NoNormPrelude *-assoc 方向 = (m·n)·o ≡ m·(n·o)） |
| `liftD1` | 同上 §8 | BSolD1 m (t₀,s₀) ⇒ BSolD1 (m+2) (3t₀,3s₀)（**索引 k ↦ suc k**; dub-suc 归位——NormClassify:429 同款） |
| ★ `classifyD1` | 同上 §8 | **∀② 的 d=1 镜像**: solD1 n x y ⇒ BSolD1 n x y（two-ind 两步归纳; 边界同 NormClassify §8——逆向不作陈述, 见证满足性由 witness-satD1 承载） |

### M12 · W-筛网形式化（2026-11-25, RH 线）

| 符号 | 位置 | 命题 |
|---|---|---|
| `Coincidence` + `F9-coincidence` | `WitneSieve.agda` | **W1·双结构同格 record**: 同一载体加法交换/单位 × 乘法相位 8 步回卷/幂 0≠1; 实例 F₉（f9add/c8pow/dist-g0-1 承件） |
| `RigidityCert` + `pt0-rigidity` | 同上 | **W2·共轭可承证 record**: 对合 σ + 逐对群自同; 实例 Pt0（sig-sq-id + sig-hom 256 条承件） |
| `SeparationCert` + `pt0-separation` | 同上 | **W4·非循环分离 record**: 见证点 + 构造子冲突; 实例 cls0 rho-vs-零作用（rho-ne-act1 直接承） |
| ★ `W3-skeleton` + 七实例 | `NormFormPositive.agda` | **W3·正性可定位 ℤ 承证**: 配方恒等式 RHS ≡ P1form + (M4form + ((+4)*(+q))·b²)（prem : t²+c ≡ 4q 乘入; 4N 的 + 形由两个平方项承证——Schwarz 型）+ 八类 prem 全 refl; 泛化 W 形态（免坑 #2/#8） |
| `sq+`/`M0-lemma`/`sq-reassoc`/`S-partW` | 同上 §1 | 总装四承件（平方 + 形析取 / distribʳ+reassoc / 平方再结合 / prem 乘入泛化 W） |

### M11 · End(E) 公式层第一砖：Deuring 失真映射（2026-11-25, RH 线）

| 符号 | 位置 | 命题 |
|---|---|---|
| `distortion`（新 oracle 模式） | `oracle_rh_tables.py` | cls0/cls5（a₆=0 超奇异）全枚举: 封闭 + 256 对 hom 零失败 + ρ²=neg + σρ=−ρσ + Z[σ]-作用（去重 16/8 个）逐个分离 ✓ |
| `rho`（16 条） | `EndDistortion0.agda` | (x,y) ↦ (−x, α·y)——经典 Deuring 失真映射的 F₉ 离散承载 |
| ★ `rho-hom`（256 条 refl） | 同上 | **rho(P+Q) ≡ rho P + rho Q 全对** —— End(E) 成员判据 |
| `rho-sq-neg`（16） | 同上 | ρ² = negp（ρ²=[−1], CM by ℤ[i] 谱系） |
| `rho-sig-anticomm`（16） | 同上 | **σρ = −ρσ**（Galois 共轭作用于 CM: σρσ = −ρ; 手算 σρ=ρσ 被枚举否证入档） |
| ★ `rho-ne-act1..16` | 同上 | **rho ∉ ℤ[σ]-作用**: 作用映射 P↦[a]P+[b]·σP（去重 16 个）逐个有分离点——超奇异 ⟹ End ⊋ ℤ[π]-作用的构造性离散见证（第一砖; 完整四元序不作陈述） |
| `EndDistortion5`（N2 镜像） | 同上（cls5 = c020 y²=x³−x） | 与 cls0 全镜像: rho-hom 256 + ρ²=neg + σρ=−ρσ + sig-sq-id + 16 分离见证, exit=0 |
| ★ `sig-sq-id`（16×2） | `EndDistortion0/5` | σ²=id —— 生成关系三件套 {σ²=1, ρ²=−1, σρ=−ρσ} 的 Agda 承载齐 |
| `endact`（新 oracle 模式, N3） | `oracle_rh_tables.py` | ℤ[σ,ρ] 秩-4 作用: 256 候选 → **去重 64**（两类一致）; 核 = ⟨2(σ+ρ)⟩ / ⟨2ρ(1+σ)⟩ 4 元; 合成封闭抽样零失败; 群阶分布 ⟹ **E(F₉) ≅ ℤ/4×ℤ/4** |
| `DistortionAbsent`（N4） | `DistortionAbsent.agda` | **rho-候选于普通 4 类缺席**（[构造性缺席·候选级]）: a₆≠0 ⟹ 封闭恒等式 (α·y)² = rhs(−x) 即失败, 逐类 absurd（fneg/mula/rhs9 全归约构造子冲突）; ℤ[σ]-作用去重 12/15/15/12 数据冻结 |
| ★ `actK*-zero`（16×3×2, N5） | `EndRing0/5.agda` | **核引理**: 非平凡核元素（2(σ+ρ) 等）逐点作用恒 ptInf |
| ★ §S 分离见证（63×2, N5） | 同上 | **商忠实性**: 其余 63 个典范代表逐个 act ≠ 零映射 ⟹ 核 = 恰为「零作用元素」全体（64 元作用环结构定案; 4096 合成全表量级取舍定为不作） |

### M9 · G4 相干放大二分判据（2026-11-25）

| 符号 | 位置 | 命题 |
|---|---|---|
| `coherent-linear` | `CoherentPhase.agda` | 自由 ℤ 载体相干累加线性（repL k ≡ +k） |
| ★ `coherent-inj` | 同上 | **忠实性**: 失衡相等 ⟹ 步数相等（posInj 归约; 放大不失真） |
| `trunc3`/`trunc8` | 同上 | 有限阶截断: C₃ 三步归零（updAt-cubed）/ C₈ 八步回卷 |
| `AmplificationDichotomy` + `dichotomy-instance` | 同上 | **放大二分定理**: 放大机制存在条件 = 载体含自由（非挠）部分 |

### M9 · G3 挠率-自旋耦合（2026-11-25, EC 谱系离散类比）

| 符号 | 位置 | 命题 |
|---|---|---|
| `spinImbalance`/`chiralCharge` | `SpinTorsionCoupling.agda` | 手征串源场（左 +1/右 −1 电荷和） |
| ★ `coupling` | 同上 | **EC 耦合离散形态**: 挠率值定义性等于自旋密度差（κ=1, refl） |
| `coupling-closed` | 同上 | 平衡配置闭合归零（镜像 P0-3） |
| ★ `zhonglv-spin-bridge` | 同上 | repL 11 挠率 ≡ +11 ≡ zhonglvTorsion 挠率——「仲吕不交」获得自旋源解释 |

### M9 · A₄ 绝对平行试点（2026-11-25, Synthesis/Geometry 线）

| 符号 | 位置 | 命题 |
|---|---|---|
| `plaquette-collapse` | `TeleparallelA4.agda` | 环绕平行四边形六步（含逆）净位移 ≡ v —— **零曲率**（2×updAt-comm + 2×updAt-cubed, 零新引理） |
| `flat` | 同上 | 传输可交换（绝对平行 = updAt-comm 别名承载） |
| `TeleparallelA4` record + `a4-instance` | 同上 | **A₄ 共存**: 零曲率 ∧ 挠率非零（zhonglvTorsion +11）inhabited |
| `a4-coexist` | 同上 | 共存判据字面展开（updat-comm × torsionNonzero） |

### M6 · Frobenius/Deuring 线（2026-11-25）

| 符号 | 位置 | 命题 |
|---|---|---|
| `f9conj` / `f9conj2` | `FrobF9.agda` | σ(a,b)=(a,−b); σ²=id |
| `f9add-conj` / `f9mul-conj` | 同上 | σ 环自同（neg-⊕/⊗ 分配 27 格承载） |
| `rhs9-conj` | 同上 | σ(rhs(x)) ≡ rhs(σx)（系数 F₃-嵌入 σ-不动） |
| `frob-closed` | 同上 | y²=rhs(x) ⟹ (σy)²=rhs(σx)（σ 置换载体） |
| `conj-fix-im` | `FrobFix.agda` | σP≡P ⟹ P 虚部≡T₀（F₃-嵌入判据, 点级） |
| `fe-*`（18） | 同上 | **Fix(σ) = #E(F₃)**（口径含 ∞） |
| `split-*`（18） | 同上 | #E(F₉) = Fix + 2·pairs（σ²=id ⟹ 非不动点成 2-cycles） |
| `div3V-sup` / `sup-div3V` | `SupersingularDiv3.agda` | **「p∣t」表述 ⟺ 迹集表述 双向**（值层桥） |

### M6 · B5 群律线（2026-11-25, G0+G1）

| 符号 | 位置 | 命题 |
|---|---|---|
| `e9add`/`e9neg`/`e9mulint` | `oracle_rh_tables.py`（group 模式） | char 3 一般形加法公式（oracle 侧; 群公理全点核对 ✓） |
| `addE`（1348 格）/`sig`/`negp` | `GroupCls0..7.agda` | E(F₉) 群律表驱动（8 同构类, 代表元 = rep-of） |
| `commE`（1348）/`unit-*`/`inv-r` | 同上 | 交换律/单位/逆元（表内性质 Agda 承载） |
| `assocE`（343） | `GroupCls6.agda`（试点） | 结合律（cls6 全量; 其余 7 类 oracle 侧已核, Agda 未收录——量级取舍） |
| `sig-hom`（1348） | `GroupCls0..7.agda` | **σ 群自同** σ(P+Q) = σP+σQ（G0 全点核对 ✓ 的 Agda 承载） |
| `charEq`（~99） | 同上 | **特征方程点级** [4]P = [t]·σP（π 满足 x²−tx+3=0 的点级承载） |

### M7 · E[3] 破灭线（2026-11-25, Deuring 代数侧表驱动承载）

| 符号 | 位置 | 命题 |
|---|---|---|
| `e3-triv0/5/6/7` | `E3Tor.agda` | **超奇异 4 类 3-挠破灭**: mul3 p ≡ ptInf ⟹ p ≡ ptInf（16/16/7/7 条, () 拦截） |
| `e3w{1,2,3,4}-0/1` + `e3w-ne/tor` | 同上 | **普通 4 类 3-挠非平凡**: 每类恰 C₃（∞+2 见证; 群阶 12/15 含 3） |
| `notsup-c101/c102/c201/c202` | 同上 | ¬ IsSup（sup-div3V + Div3V=⊥ 退化, 逐类非整除迹值） |
| 判据 | oracle `e3` 模式 | **「p∣t 超奇异 ⟺ E[3](F₉) 破灭」逐类成立**（首版 mul3 从 P 起加误为 [4]P, 被判据交叉核对拦截） |

### M8 · F₉* = C₈ 乘法群相位线（2026-11-25）

| 符号 | 位置 | 命题 |
|---|---|---|
| `ggen`/`c8pow` | `F9MultC8.agda` | g = 1+α, g⁸=1, 8 幂表（oracle c8 逐字） |
| `dist-g*`（28） | 同上 | C₈: 8 幂两两不同 |
| `c8-sig-*`（8） | 同上 | σ 作用 = k ↦ 3k (mod 8)（2 阶） |
| `c8-norm-*`（8） | 同上 | **Norm ∈ F₃\* = {±1}**（修正「α⁴=q=9」——枚举否证, 见 docs/Riemann 原生共轭性注记 §二） |

⚠ 别混写两层: 域元素层 Norm ∈ {±1}; 曲线 Frobenius 本征值层 α·ᾱ = q（WeilRecurrenceAll 承载）。

### F₃ 同构分类（A5.2①, 2026-11-25）

| 符号 | 位置 | 命题 |
|---|---|---|
| `xshift` | `CurveIsoF3.agda` §1 | 平移作用（a₄ → 2a₂r+a₄; a₆ → r³+a₂r²+a₄r+a₆; 乘法字面量先行） |
| `ds-*`（81）/ `ps-*`（81） | 同上 §3/§4 | disc / #E 平移不变（oracle 27×3 ✓ + Agda refl） |
| `cls-of`（27 分派, mkC 模式） | 同上 §2c | 18 非奇异 → 8 类（cls0..cls7; 9 奇异 absurd） |
| `sic-*`（54）/ `ns-ds-*`（54） | 同上 §2d/§2e | 轨道封闭（平移不离类）+ 平移目标非奇异见证 |
| `ct-*`（18） | 同上 §2f | 类内迹一致（同构 ⟹ 同 #E 的分轨承载） |
| `ne-cls*`（28） | 同上 §2g | 8 构造子互斥 |

### ⚠ 别重复实现
- `descent1` 的 r=1/2 分支**不可**直接 `suc-injective` 剥层（RHS 3·q 非 suc 头）——须 `3suc` 归位（`no-suc4-mult3` 范式）。
- 递降三分**必须用右乘形式** `t ≡ q·3`（左乘的 +3 平移要多付 +-suc×3 + mul3-suc 链）。
- **F₃ 同构分类已定**：8 类（cls0..cls7）——别再建第二套分类（t=0 双类：c020 自成一类 ≠ c010-012 类）。
- nightly 坑 #5（分派子句块前悬置未定义签名污染 refl）+ 四坑见 `docs/plan/rh-allcurves-plan.md` §六。
- **d=1 双坐标递降已定**（`descentD1`）: tri3-split 须对 x、y **各跑一次**（9 案）——别套用 d=3 单坐标 descent1。
- **suc⁴ 平方形状别重开新矛盾核**: d=1 线 r=2 案已归一 `suc(3·suc J)`（`x2-shape` 经 3suc）,
  和式件三件齐（s1s0/s0s1/s1s1）⇒ 六组合只用 no-suc-mult3/nm3s2 两核——no-suc4/5/8-mult3 在 d=1 无用武之地。
- **形状步先定位再形状**: 和式 `x*x + y*y` 的 S 步必须先 `cong (λ z → z + y*y) xx`（x² 是命题等价非定义等价）,
  再对 y² 重写、最后上形状件——探针实测三轮教训。
- **NoNormPrelude `*-assoc` 方向 = (m·n)·o ≡ m·(n·o)**（与 stdlib 相反）——2·(2·X) ≡ 4·X 要 `sym`。
- **σρ ≠ ρσ（cls0 失真映射）**: 正确关系 σρ = −ρσ（ρ 含 α∉F₃, Galois 共轭反交换）——手算「交换」被 oracle 否证, 勿凭直觉写。
- **语句里别用裸 λ 应用**（nightly 实测: `(λ _ → ptInf) pw` 触发 UnsolvedMetaVariables）——具名零映射（act0）替代。

---

## 十五、矩阵乘法指数线（`Algebra/LinearAlgebra/`，2026-11-26 登记）

> 与 GF(3)/三进制主线的接口有三处: M13 的 GF(3) 七乘方案（Trit 上的 2×2）、M14 的 12×12 展示群寄存器、
> M16 的秩分解谓词与展平下界（只对 GF(3)）。M15（ListBounds）与域无关——只用标准库 ℕ。

### M13 · Strassen GF(3) 七乘方案全枚举（`StrassenGF3.agda`，6621 行，回执 `4ca2f1d3`）

| 符号 | 位置 | 命题 |
|---|---|---|
| `strassen` / `mul₃` / `m1`…`m7` | `StrassenGF3.agda:42–50` | 七乘方案与朴素乘法（⊗ 7 次 vs 8 次; 加/减另计） |
| ★ `strassen-correct` | 同上 §3（6561 条 `refl`, oracle 逐字发射） | ∀ a…h : Trit → `strassen (mkMat2 a b c d) (mkMat2 e f g h) ≡ mul₃ (…)`; 3⁸ 全枚举, `engineering/oracle_strassen_gf3.py` 6561 对零失败 |

### M14 · 12×12 寄存器（⚠ 界已撤回; 回执 `dc35eea3` / `c0655afe`, 撤回 `668ecab4`）

| 符号 | 位置 | 命题 / 状态 |
|---|---|---|
| `record Matmul12Bounds`（字段 `output-positions = 144` 等） | `Matrix12Bounds.agda:39` | 只是**存三个登记数的 record**, 不证明任何界 |
| `E-at` / `E-inj` / `mulEii-*`（288 条） | `Matrix12LowerWitness.agda:54/105` | 基矩阵两两不同 + 144 条 `E_ii·E_ik = E_ik` 的全枚举 `refl` |
| ⚠「144 ≤ 秩 ≤ 1728」 | — | **不是已证结论, 勿引用**（「两两不同 ⇒ 秩 ≥ 144」是无效推理; 1728 只是 `12*12*12` 的算术恒等式; 库内无形式代价模型）。见 `docs/techniques/M14-12x12矩阵指数上下界-2026-11-26.md` 顶部勘误 |

### M15 · ListBounds——软核的不用实数镜像（`ListBounds.agda`，1533 行，回执 `6982c9a1` + 非空真见证见本节末）

镜像对象: openai/math `OAI/LinearAlgebra/MatrixExponent/ListBounds.lean`（Seed / ManyList / Compression）+ `Iteration.lean:76–77` `incompatible`。
证明: 独立重构, 事后通读 `Iteration.lean`（164 行）确认同构（`lb-step-Y` ↔ `absorb`, `lb-Inv` ↔ `iterate`）。

| 符号 | 位置 | 命题 |
|---|---|---|
| ★ `lb-incompatible` | `ListBounds.agda` §8 | `lb-Grow N H → lb-Seed P N → lb-Many P N → lb-Comp P N H → ⊥`（n、h 抽象为满足增长条件的函数 N、H） |
| ★ `lb-incompatible-lists` | 同上 §10 | 上条取 N := `lb-listBits`、H := λ w → w * w（Lean `incompatible` 的 ℕ 形态） |
| ★ `lb-wk≤2w` | 同上 §9 | `2 ^ (k + 4) ≤ w → w ^ k ≤ 2 ^ w`（归纳于 k; 取半 `lb-half` + `lb-lin-exp` 线性·常数 ≤ 指数） |
| `lb-step-Y` / `lb-step` / `lb-copy` / `lb-size` / `lb-iter` / `lb-final` | 同上 §2–§5 | 迭代压缩 J 步的全部算术引理（不变式 `lb-Inv`） |
| `lb-seed-at` / `lb-many-at` / `lb-comp-at` / `lb-rn-pkg` | 同上 §3/§5/§6 | 三条性质搬到 w = W^N0 上; 衰减率 rn 的选取 |
| `lb-Ev` / `lb-Seed` / `lb-Many` / `lb-Grow` / `lb-Comp` | 同上 §7 | 四条性质的 ℕ 表述（分数次幂 → 整数不等式; 「最终」→ `lb-Ev`） |
| ★ `lb-consistent-SMG` / `lb-consistent-SCG` / `lb-consistent-MCG` / `lb-consistent-SMC` | 同上 §11 | **非空真**: 去掉任意一条假设, 其余三条对某个具体的 P 同时成立（P_hard: `t·listBits·w + 1 ≤ 3m` / P_ne: `1 ≤ m` / P_big: `listBits²·w ≤ m` / P_w 配 n ≡ 1、h ≡ 1） |
| ★ `lb-necessary-C` / `lb-necessary-M` / `lb-necessary-S` / `lb-necessary-G` | 同上 §11 | 配合主定理: 被去掉的那一条对同一个 P 不成立 ⟹ **四条缺一不可** |

**边界（引用时必带）**:
- 「Lean 的实数陈述 ⟹ 本 ℕ 陈述」这座桥**未形式化** [手工论证·未验证]; 桥的左端要实指数幂（要 ℝ）, 本库宪法禁无理数, 写不出。
  本文件是软核在 ℕ 上的一条**独立**定理, 不是 Lean 那条定理的形式化推论。
- 只镜像软核; 不是任何域上任何矩阵乘法下界的证明; 不改变 ω = 9/4 的审计状态。
- 旁证: `engineering/oracle_list_bounds.py`（10 项 ALL_PASS, 整数/分数精确）+ `engineering/tests/test_oracle_list_bounds.py`（11 个 unittest）。
  ⚠ 本件顺序与「先算后验」**相反**: Agda 先行（逐段过内核）, oracle 事后核对陈述与桥接。

### M16 · 秩分解谓词 + M13 接桥 + 展平下界 + 秩相乘/取幂 + 两半的有限语言（`TensorRankGF3.agda` 299 行 / `TensorRankFlattenGF3.agda` 281 行 / `TensorRankPowGF3.agda` 354 行 / `TensorRankUpperGF3.agda` 200 行，2026-11-26）

镜像对象: openai/math `OAI/LinearAlgebra/MatrixExponent/RationalCircuits.lean:48 RankLE`（谓词）、
`Flattening.lean:6 rank_lower`（展平下界）、`RankPower.lean:12 rank_mul` / `:15 rank_pow`（张量积与取幂）、
`FieldExtension.lean:72 exponent_lt_iff_rank`（指数 < s ⟺ ∃ 分解 + 增长条件; 取形状 (1,1,1) 与 s = p/q）。
证明**独立重构**: Lean 走展平后矩阵的秩（`Rectangle.RankLE.area`）,
本库没有矩阵秩的不变性理论, 改走有限域上的计数（基数比较代替维数比较）。

| 符号 | 位置 | 命题 |
|---|---|---|
| `record RankLE₃` | `TensorRankGF3.agda:87` | r 项秩分解: `ra rb rc : Fin r → … → Trit` + `rank-eq : ∀ x y z → Σ_i (ra i x) ⊗ (rb i y ⊗ rc i z) ≡ mm n x y z` |
| `mm` / `oneIf` | `:82` / `:75` | ⟨n,n,n⟩ 的结构常数 `[x.1 = z.1][x.2 = y.1][y.2 = z.2]` |
| ★ `strassen-is-rank-form` | `:246` | `∀ A B z → Σ_i (L i A) ⊗ (R i B ⊗ C i z) ≡ at (mul₃ A B) z`（由 M13 的 `strassen-correct` 承证） |
| ★ `rank-strassen` | `:278` | `RankLE₃ 2 7`（上界见证: 秩 ≤ 7） |
| `ω₃-boundary` | `:296` | 外部边界类型 `∀ n r → 2 ≤ n → RankLE₃ n r → n ^ 9 ≤ r ^ 4`——**无居民**, 本库不证 |
| ★ `rank-lower` | `TensorRankFlattenGF3.agda:272` | `∀ n r → RankLE₃ n r → n * n ≤ r`（展平下界, 计数证法） |
| ★ `span-full` | 同上 `:227`（`module Span`） | 由秩分解构造坐标 `t v`, 使 `Σ_i (t v i) ⊗ (a i x) ≡ v x`——张成里装下一切函数 |
| `basis-in-span` / `delta` | 同上 `:169` / `:199` | n² 个标准基落在 `span {a i}` 里 / δ 的两次消化（`sumFin-δ` ×2） |
| `φ-injective` / `count` | 同上 `:243` / `:265` | 单射 `Fin (3^(n²)) → Fin (3^r)` ⟹ `3 ^ (n * n) ≤ 3 ^ r`（`injective⇒≤` + `combine-surjective`） |
| `sumFin-distrʳ` / `sumFin-scale₃` / `sumFin-swap₃` / `sumX-swap` | 同上 `:73` / `:81` / `:94` / `:142` | Trit 值 `sumFin` 的分配 / 提公因子 / 双和交换 |
| `oneIf-δc` / `δc-sym` / `oneIf-refl` / `⊗-rot` | 同上 `:118` / `:124` / `:113` / `:130` | 指示函数与库内 δc 的关系; 三因子轮换 |
| `check-lower-strassen` | 同上 `:280` | `2 * 2 ≤ 7`: 定理作用于库内真实的分解（非空性） |
| ★ `rank-mul` | `TensorRankPowGF3.agda:290` | `∀ {n r m s} → RankLE₃ n r → RankLE₃ m s → RankLE₃ (n * m) (r * s)`——两个分解的张量积仍是分解 |
| ★ `rank-pow` / `rank-one` | 同上 `:310` / `:300` | `RankLE₃ n r → ∀ k → RankLE₃ (n ^ k) (r ^ k)`; 零次幂 = `RankLE₃ 1 1` |
| ★ `rank-strassen-pow` / `rank-strassen²` | 同上 `:315` / `:319` | `∀ k → RankLE₃ (2 ^ k) (7 ^ k)`; `RankLE₃ 4 49`——每个尺寸 2^k 都有内核检查过的见证 |
| `strassen-certificate` / `strassen-upper` / `cert-base` | 同上 `:327` / `:338` / `:323` | `∀ k → (7 ^ k) ^ 6 ≤ (2 ^ k) ^ 17`（由 `7 ^ 6 ≤ 2 ^ 17` 两边取 k 次幂）; `strassen-upper k` = 分解 × 证书 |
| `rank-eq×` / `mm-split` / `oneIf-combine` | 同上 `:276` / `:258` / `:116`（`module TensorProd`） | 张量积满足结构常数方程: T_{nm}((x₁,x₂),(y₁,y₂),(z₁,z₂)) ≡ T_n(x₁,y₁,z₁) ⊗ T_m(x₂,y₂,z₂)（位置按 `combine` 拆开） |
| `rank-lower-pow` / `rank-lower-strassen²` | 同上 `:349` / `:353` | 与展平下界的组合: `∀ k → (2 ^ k) * (2 ^ k) ≤ 7 ^ k`; `4 * 4 ≤ 49` |
| `Saving₃` / `ω₃-upper` | `TensorRankUpperGF3.agda:94` / `:98` | `Saving₃ p q = ∃ n r, 2 ≤ n × RankLE₃ n r × (r ^ q < n ^ p)`; 外部上半的陈述 `∀ p q → 9 * q < 4 * p → Saving₃ p q`——**无居民** |
| ★ `strassen-saving` | 同上 `:110` | `∀ p q → 0 < q → 17 * q ≤ 6 * p → Saving₃ p q`（n = 2^(6q)、r = 7^(6q); 实例 `Saving₃ 17 6`、`Saving₃ 3 1`、`Saving₃ 23 8` 由内核裁决前提） |
| ★ `saving-above` / ★ `exactness₃` | 同上 `:166` / `:194` | 有下半时任何节省满足 `9 * q < 4 * p`（n^(9q) ≤ r^(4q) < n^(4p) ≤ n^(9q) 矛盾）; 两半一旦成立, 节省恰好是比值在 9/4 之上的 (p, q) |
| `boundary-strassen` / `cert-strict` | 同上 `:199` / `:86` | 下半在 (2, 7) 处的实例 `2 ^ 9 ≤ 7 ^ 4`; `7 ^ 6 < 2 ^ 17` |
| `pow-exp-mono` / `pow-base-<` / `mul-<` | 同上 `:61` / `:72` / `:66` | 幂对指数单调（底 ≥ 1）/ 底严格增（不走类型类实例）/ u < v、w > 0 ⟹ u·w < v·w |
| `sumFin-↑` / `sumFin-combine` / `sumFin-⊗ˡ` / `sumFin-⊗ʳ` / `⊗-tensor` | 同上 `:82` / `:92` / `:61` / `:69` / `:129` | `Fin (a + b)` 上的和拆成低段 ⊕ 高段 / `Fin (a · b)` 上的和按 `combine` 重排成双重和 / 左右缩放 / 六因子重排（只用库内 `⊗-4swap` + 结合律） |

**边界（引用时必带）**:
- `ω₃-boundary` 是**外部定理的陈述**, 不是本库定理; M16 **没有**推进它。Lean 对应 `key/MatrixExponent.lean:45 square_iff_prime_ranks`
  是阅读层的对应, 与 `RankLE₃` 的逐字对应未形式化 [手工论证·未验证]。
- `rank-lower` 只对 GF(3)（计数用 \|Trit\| = 3）; Lean 的 `rank_lower` 对任意域。
- n = 2 处: 库内 `r ≥ 4`（`rank-lower`）与 `r ≤ 7`（`rank-strassen`）; 外部定理按算术给 `r ≥ 5`（4⁴ = 256 < 512 ≤ 5⁴）。
  「n = 2 时秩恰为 7」[直觉·未验证], 库内没有（要证它得有 r ≤ 6 时的排除论证）。
- 旁证: `engineering/oracle_tensor_rank_gf3.py`（结构常数 64 / 矩阵乘法 26244 / 两路会合 64 / 张成构造 1616 / 张成容量 2061 /
  张量积 4096 + 随机 4×4 矩阵 4800 / rank-one 与证书 12 次核对, ALL_PASS）
  + `engineering/tests/test_oracle_tensor_rank_gf3.py`（18 个 unittest, 含 4 个负控制: 弄坏一个系数, 对应判据必须报错; 去掉下半前提, 蕴含不成立）。
  M16-D 旁证: oracle `check_savings`（3365 次核对; 「下半 + 节省 ⟹ 9q < 4p」实际触发 92638 次; 对照 13/5、14/5、19/7、24/9 落在 9/4 与 17/6 之间, Strassen 的 n = 2^(6q) 不满足）。
- M16-D 的边界: 「Lean 的实数陈述 ⟹ 本处的分数形态」是 [手工论证·未验证]（s = p/q 时 r < n^(p/q) ⟺ r ^ q < n ^ p; 形状 (1,1,1) 对应 `Rectangle/Bounds.lean:15 square`）。
  `exactness₃` 把两半都当**假设**。本件能证的上半只有 17/6 那一段; 靠 9/4 的见证 Lean 那边也不是显式的
  （`Coefficients.lean:43 candidate := Classical.epsilon …`, 上界机器在用选择公理挑出的代数闭域上工作, 再由 `closed_laws` 推广）。
- M16-C 的边界: `strassen-certificate` 只是算术不等式; 读成「GF(3) 上 ω ≤ 17/6」是 [手工论证·未验证]
  （本库没有 Lean `formalOmega` 那套定义）。`rank_map`（沿环同态搬运）未做——本库的谓词只在 GF(3) 上, 没有可搬运的目标域。
  与 M16-B 的组合是库内具名定理: `rank-lower-pow : ∀ k → (2 ^ k) * (2 ^ k) ≤ 7 ^ k`（`TensorRankPowGF3.agda:349`）、`rank-lower-strassen² : 4 * 4 ≤ 49`（`:353`）。
- **复用而非重写**（先查后写的结果）: `sumFin-add`（`GF3RankNullity.agda:153`）、`sumFin-δ` / `δc`（`GF3Dim`）、
  `fromFun` / `toFun` 往返（`GF3Count`）、`fromFun-cong`（`GF3BasisCount.agda:42`）、`3^-mono-<`、`cong₁`。
  库内已有的 `⊕-interchange`（`Algebra/Analytic/DiscreteAnalysis.agda:166`）本件**没有**用到（`sumFin-add` 已含那步交换律）。

### ⚠ 别重复实现 / 别再踩（本线）

- **stdlib `^-distribʳ-*` 首参是指数**: `∀ m n o → (n * o) ^ m ≡ n ^ m * o ^ m`（写成「底、底、指数」会得到莫名其妙的 UnequalTerms）。
- **`*-monoˡ-≤ k h : a·k ≤ b·k`（第二因子固定）; 第一因子固定用 `*-monoʳ-≤ k h : k·a ≤ k·b`**; `+-monoˡ-≤` / `+-monoʳ-≤` 同理。
- **环形求解器（`Data.Nat.Solver`）的多项式必须逐字镜像目标的括号结构**（转换检查是语法优先; `2 * (8 * G) * p` 与 `2 * (8 * G * p)` 合不上）。
  求解器调用只能出现在**带类型的具名绑定**里——不能嵌在 `cong` 的参数位或 ≤ 链的元变量位置。
- **`x + 0` 与 `x` 不是定义等价**; `k + 3` 与 `k + 1 + 2` 不是, 与 `suc (suc (k + 1))` 是; `2 * x` 与 `x + x` 不是。
  ≤ 链、≡ 链的中间项一律写成带类型的绑定。
- **`m≤n+m m n : m ≤ n + m`**（右端是 `n + m`）; `lb-1≤ k : 1 ≤ suc k`（不是 `k ≤ k + 1`）。
- **oracle 必须打印「前提成立数」**: 迭代一步那项首版 fires = 0（m 取样范围太小, 整项空转）——打印出来才看得见。
- **`ListBounds` 的 ℕ 表述已定**（`lb-Seed` / `lb-Many` / `lb-Comp` / `lb-Grow`）——别为同一件事再设计第二套表述。
- **`⊗-assoc x y z : (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)`, `⊕-assoc` 同向（左嵌 → 右嵌）**: M16 为反方向套 `sym` 连错两次。
- **`sumFin-δ f i` 的形状是 `δc i j ⊗ f j`（固定指标 i 在前、求和变量 j 在后）**: 和项里若是 `δc j i` 且不在首位, 先 `δc-sym` 翻转, 再挪到首位。
- **量词必须带类型**: `∀ v x → …` 里 v、x 的类型会成为元变量, 整条下游链 UnsolvedMetaVariables（M16 的 s1–s4 / summand-rot / d1 / d2 各犯一次）。
- **结论里不出现隐式参数的引理要显式给**: `sumFin-zero {n = r}`、`sumFin-cong {n = r} {g = …} {h = …}`——不给就 UnsolvedMeta, 或触发「Refusing to invert pattern matching of sumFin（深度 50）」。
- **`Injective _≡_ _≡_ f` 的两端是隐式**: 子句写 `f-injective {x} {y} h`。
- **record 字段不随模块按名导出**: `import M using (ra)` 报 ModuleDoesntExport; 要在本地 `open RecordName using (…)`（不加 `public`）。
- **`fromFun-cong` 在 `GF3BasisCount.agda:42`**, 不在 `GF3Count`。
- **括号只信脚本, 不信心算**（M16 同一处连错三次）: 行首 `trans (X …)` 的括号属于**第一个参数**, 最外层调用本身没有括号。
- **`RankLE₃` 谓词与 `rank-lower` 的表述已定**——别为同一件事再设计第二套; 秩相乘 / 取幂已在 `TensorRankPowGF3.agda`（`rank-mul` / `rank-pow`）。
- **隐式尺寸落在 `_*_` 下面时 unifier 不反演**: `remQuot {n} m p`、`sumFin {a * b} G`、`sumFin {r} (λ i → sumFin {s} (λ j → …))`——
  **陈述和子句里都要**显式给。症状 = 「Refusing to invert pattern matching of _*_ / sumFin（深度 50）」+ `Fin (?m * ?n)` 对 `Fin (a * b)` 的 UnsolvedMeta。
- **`^-monoˡ-≤` 首参是指数**（`^-monoˡ-≤ k h : a ^ k ≤ b ^ k`, 底变）; `^-monoʳ-≤ m h : m ^ a ≤ m ^ b`（指数变）。≤ 链用 `≤-trans`, 不是 `trans`。
- **`uncurry combine p` 在中性 `p` 上不归约**（stdlib `combine-remQuot` 用 uncurry 写）→ `uncurry-combine-proj : ∀ p → uncurry combine p ≡ combine (proj₁ p) (proj₂ p)`（`TensorRankPowGF3.agda:76`）。
- **Trit ⊗ 的现成引理**: `⊗-4swap`（`Algebra/Jacobian/Matrix.agda:311`, 四因子交换）; 本库 `sumFin` **没有**通用的「单射重排」引理,
  按 `combine` 的重排是 `TensorRankPowGF3.agda:92 sumFin-combine`。
- **stdlib 的 `_*_` 是左结合**（`a * b * c` = `(a * b) * c`; M16-D 我先记成右结合, 改坏了一组本来正确的等式）: `*-assoc a b c : (a * b) * c ≡ a * (b * c)`。
- **`0 < n` 就是 `s≤s z≤n`**（`s≤s` 两边同加一; 我把 `0 < 4` 数成四层 `s≤s` 两次）; `m ≤ suc m` 是 `m≤n⇒m≤1+n ≤-refl`（`≤-step` 自 stdlib 2.0 起弃用, 会告警）, 不是 `s≤s ≤-refl`。
- **`<-irrefl refl h`**（stdlib 的 `<-irrefl : Irreflexive _≡_ _<_`, 首参是等式）; ≡ 链里夹严格不等式要用 `≤-<-trans` / `<-≤-trans` + `≤-reflexive`, 不能用 `trans`。
- **`Σ[ x ∈ A ] B` 语法在 `open import Data.Product using (Σ)` 下不可用** → 写 `Σ ℕ (λ n → …)`。
- **严格单调的 stdlib 引理带类型类实例参数**（`*-monoˡ-<`、`^-monoˡ-<` 的 `{{NonZero …}}`）: 变元位置解析不出实例 → 自己写（`TensorRankUpperGF3.agda:66 mul-<`、`:72 pow-base-<`）, 非严格的 `*-monoˡ-≤` / `^-monoˡ-≤` 不需要实例。
- **顶层名查重脚本别把连字符排除在名字字符集外**（否则带 `-` 的名字全漏——首版扫描漏掉了几乎全部引理名）; 查重要扫**陈述**里的类型是否相同, 不只是名字。

## 十六、矩阵乘法指数线 M17——3×3 的 23 项秩分解（`TensorRankLadermanGF3.agda`，893 行，2026-11-26 登记）

> M16 把「ω = 9/4 在 GF(3) 上」写成了关于 `RankLE₃` 的两半有限命题; M17 给出尺寸 3 的第一个见证。
> 证书来源: GitHub `RakTikoo/matmul-333-tensor-rank`（2026-11-26 经代理取回）的 Laderman 1976 23 门方案
> 机器可读件（`laderman_r23_Q.json`）; 系数全 ∈ {-1,0,1}, ℤ 恒等式 ⟹ 任意交换环（GF(3) 是实例）。
> 同仓库 Perminov CN-122 第二份方案在 oracle 判据 4 逐点核验通过（未入库, 只作稳健性数据点）。

| 符号 | 位置 | 命题 |
|---|---|---|
| `raL` / `rbL` / `rcL` | `TensorRankLadermanGF3.agda:66`（各 207 条子句, oracle 发射） | 23 门 × 9 位置的系数表 |
| `rank-eqL` | 同上 `:691`（81 条子句 × 9 分支 = 729 条 `refl`, oracle 发射） | Σ_k raL⊗(rbL⊗rcL) ≡ `mm 3`——9×9×9 全枚举 |
| ★ `rank-laderman` | `:781` | **`RankLE₃ 3 23`**——尺寸 3 的内核检查过秩分解见证（此前只有 n=2 的七门） |
| `rank-lower-laderman` | `:790` | `3 * 3 ≤ 23`——展平下界（M16-B）与见证配对: n=3 处库内两方向 9 ≤ r ≤ 23 |
| `cert-laderman` / `cert-laderman-strict` | `:800` / `:803` | `3^17 ≤ 23^6`、`23^7 < 3^20`（数值由 oracle 发射, 不手算） |
| ★ `laderman-saving` | `:812` | `∀ p q → 0 < q → 20 * q ≤ 7 * p → Saving₃ p q`（结构与 `strassen-saving` 相同, 换一组证书） |
| `saving-laderman-20-7` | `:860` | 可读实例: ω₃ ≤ 20/7 |
| ★ `laderman-not-below` | `:865` | `6 * p < 17 * q → 23^q < 3^p → ⊥`——(3,23) 见证**从不越过 17/6**（否则 23^(6q) < 3^(6p) ≤ 3^(17q) ≤ (23^6)^q = 23^(6q) 矛盾） |
| `rank-mixed` | `:894` | `RankLE₃ 6 161`——`rank-mul rank-strassen rank-laderman`（M16-C 的张量积机制） |

**诚实边界**: 这是**上界见证**（秩 ≤ 23）, 不是「秩恰为 23」。（3,23）的比值 20/7 ≈ 2.857 **不改进**
(2,7) 的 17/6 ≈ 2.833——M16-D 的缺口（9/4 与 17/6 之间的见证）**没有**被这一件填上。
尺寸 3 上要进入空档: r = 21 即可（21^5 < 3^14 且 6·14 = 84 < 85 = 17·5, oracle 判据 7 整数核对）;
r = 22 也行（首个 (p,q) = (31,11), 31/11 ≈ 2.818）; r = 23 不行（`laderman-not-below` 内核核验）。
「rank(⟨3,3,3⟩) ≤ 22」是公开问题 [阅读层·未验证, 文献状态]; 本件 23 门经 oracle 判据 6 核验为
**删除封闭**（23 个秩一贡献在 GF(3) 上线性无关, 丢任何一门都不再是分解; 库内无对应定理, 只有 oracle 事实）。

**验证链（先算后验, 三条机器轨互证）**:
1. oracle `engineering/oracle_rank3_witness_gf3.py` ALL_PASS——判据 1 结构常数 27、判据 2 GF(3) 729/729、
   判据 3 ℤ 729/729、判据 4 Perminov、判据 5 负控制 207/207 全转红、判据 6 贡献秩 = 23、
   判据 7 阈值整数扫描、判据 8 有界爬山（6×12000 步最优失配 215/729, 只是有界尝试不下结论）、判据 9 发射;
2. Agda 内核: `TensorRankLadermanGF3.agda` exit=0, 0 postulate / 0 REWRITE / 0 洞;
   独立检查件（/tmp/m17chk/CheckM17.agda）8 个主签名逐字核对 exit=0;
3. TriRV 三进制 VM: `engineering/trirv/laderman23_gf3.c`（打包系数 69 字, 运行时解包）
   `cc/trirv_cc` → `trirv_vm` 100 万步 **exit=0**; 负控制件（PK[12] 最低位 2→0）**exit=66**,
   与 oracle 侧模拟预言逐字一致（bad=16, hits=26）。
回归: `engineering/tests/test_oracle_rank3_witness_gf3.py` 16 项（表逐字核对 / 签名 / PK 同源 / 双侧预言）; 全套 129 项 OK。

**新坑（别再踩）**:
- **发射 Fin 构造子模式要套外层括号**: `raL (fsuc (fsuc fzero)) (i , j) = …`——写成 `raL fsuc (fzero) …`
  会被解析成三个参数（`WrongNumberOfConstructorArguments`）。M16-A 的先例 `L (fsuc fzero) A` 就是带外层括号的。
- **（3,b）见证的 `2 ≤ 3^(7q)` 不能直接 `pow-exp-mono 3 1 …`**——它给 `3 ≤ …`（Strassen 那边底是 2 所以恰好行）;
  补一步 `2 ≤ 3`。
- **Σ 第二分量取幂要用 `rank-pow`**: `rank-laderman : RankLE₃ 3 23` 的类型不定义等价于
  `RankLE₃ (3 ^ (7q)) (23 ^ (7q))`——用 `rank-pow rank-laderman (7 * suc q′)`。
- **独立检查件的旗标放文件头 OPTIONS, 不放命令行**——命令行 `--rewriting` 会连动 `--safe` 检查, 撞 stdlib 的 `SafeFlagPragma`。
- **TriRV 全局数据区 16K**: 621 个 int 装不下 → 系数按 9 trit/int 打包（69 字）, 运行时解包;
  **初始化器不能有尾逗号**（`parse_primary: bad '}'`）。

## 十七、矩阵乘法指数线 M18——电路模型与双线性归约的陈述层（`TensorRankCircuitGF3.agda`，172 行，2026-11-26 登记）

> M16/M17 的见证都是**作为表**给出的; Lean 那边秩分解还能从**算法**生产——`Bilinearize.lean:111`
> bilinearize: 算出矩阵乘法的电路, 乘法门数 m, 给出 2m 项秩分解（在泛点 Rat F 上）。
> M18 把这一环的**陈述层**镜像进库（用户 2026-11-26 定案的「选项 2」: 补陈述层）。

| 符号 | 位置 | 命题 / 状态 |
|---|---|---|
| `Cir` / `mulCount` / `eval` | `TensorRankCircuitGF3.agda:56` / `:65` / `:74` | 电路模型（表达式树, 无除法门: inA/inB/const/add/sub/mul; 只数乘法门——镜像 Lean 的代价口径） |
| `Computes` | `:91` | 正确性: 输出线族在一切输入处取值 = (A·B) 条目（sumFin 形式） |
| `mmRect` / `RankLERect` | `:101` / `:105` | **矩形**秩谓词（镜像 Lean Rectangle 的 RankLE I J K; 本库此前只有方形 RankLE₃） |
| `rankLE₃→rect` | `:113` | 方阵桥: RankLE₃ n r 就是矩形版 (n,n,n) 实例（mm 与 mmRect 逐字同构, record 映射直证） |
| ★ `bilinearize` / `bilinearize-square` | `:136` / `:141` | **陈述, 无居民**: Computes E ⟹ RankLERect I J K (2·gateTotal E)——镜像 Bilinearize.lean:111 的形状 |
| `schoolbook` / `schoolbook-computes` / 两个哨兵 | `:149` / `:167` / `:155`/`:159` | 1×1 schoolbook 的 Computes 居民（⊕-identityʳ 收 sumFin{1} 的 ⊕T₀ 尾）+ mulCount/gateTotal ≡ 1 哨兵 |

**诚实边界（与 Lean 原件的系数环差距, 逐条标注）**:
- Lean 原件的秩落在 **Rat F**（泛点——免极化、免 char-2 问题; `mixed_mul` 每门两个 cross 项、
  `mixed_output` 输出端是矩阵单位）。本件的 `bilinearize` 把秩落在 **GF(3)（Trit 原生）**上;
  这一步在 Lean 里不存在, 真伪未证 [直觉·未验证]——有限域上「函数恒等 ⟹ 多项式恒等」失效
  （Fermat: A³ = A）是潜在障碍。类型无居民, 无害。
- Lean 的 Build 是 DAG 序列且带除法门（泛点处理）; 本件是表达式树、无除法门（GF(3) 矩阵乘法不需要）;
  树口径的 gateTotal 计入共享子表达式 [边界标注]。
- 机制细节见审计 §K/本节: 泛点追混合偏导 ⟹ 每门至多两外积 ⟹ 张成 ⟹ 秩。

**验证**: standalone exit=0（0 postulate / 0 REWRITE / 0 洞）; 独立检查件 6 签名 exit=0;
顶层名查重唯一（`eval` 与 `CyclicGF27.eval` 同名不同型, 门禁判据按类型比对通过）。

## 十八、矩阵乘法指数线 M19——稀疏加权层 + 文献检索（2026-11-26，用户定案「检索论文 + 镜像」）

> 下界（rank ≥ …）不走表，走**约束**：加权张量的支撑结构约束一切分解形态。
> M19 镜像 Lean `Rectangle/Weights.lean` 的谓词层——Bläser 2003 的 2n²+n−2、
> 2603.07280/2609.06725 的自动化下界都以它为承重结构。

| 符号 | 位置 | 命题 |
|---|---|---|
| `wmm` / `WeightedRankLE₃` | `TensorRankSparseGF3.agda:51` / `:55` | 加权结构常数（条件处取 w，其余 T₀）+ 加权矩阵张量的 r 项分解（镜像 Lean WeightedRankLE） |
| `suppInd` / `supportSize₃` | `:68` / `:74` | 支撑指示 + 支撑数（嵌套 ℕ 和；镜像 Lean supportSize） |
| `rankLE₃→weighted` | `:82` | 桥：RankLE₃ n r → WeightedRankLE₃ n r (λ _ _ _ → T₁)（mm = 全 T₁ 加权特例；经 ⊗-identityˡ） |
| 哨兵 | `:95` / `:99` / `:103` | 支撑数 1、8（n=1,2）；1×1 加权结构常数 = T₁ |

验证：standalone exit=0（0 postulate / 0 REWRITE / 0 洞）；独立检查件 7 签名 exit=0。
诚实边界：只有谓词层；三条稀疏定律是抽象指数的泛量化命题（K.1：域泛型组合学，无可枚举的
有限核对对象），其有限形态等 exponent 机制镜像口径；限制界词汇（rows/cols/inner、陪集）未镜像。

## 十九、矩阵乘法指数线 M20——限制界词汇与零秩抽取（`TensorRankRestrictGF3.agda`，115 行，2026-11-26 登记）

> 立项 B-T2（`docs/plan/matrix-rank-line-plan.md`）。下界机制的词汇层：2609.06725（F₂ 上 3×3 ≥ 21）
> 的证明对象 = 「限制界约束每个子空间里第一因子的个数」+ 陪集分析 + 穷举；Lean 的 DegreeBound
> 同样以这三把尺子（rows/cols/inner）计量。

| 符号 | 位置 | 命题 |
|---|---|---|
| `suppRows` / `suppCols` / `suppInner` | `TensorRankRestrictGF3.agda:51` / `:55` / `:59` | 完成集计数：同 (b,c) / 同 (a,c) / 同 (a,b) 的支撑格数（镜像 Lean Sparse/Model.lean:15-21 的 Finset.filter .card） |
| `sumℕ-const` / `sumℕ-one` | `:67` / `:72` | Σ_{i<n} c = n·c；Σ 1 = n |
| `supportSize-allT₁` | `:76` | 全 T₁ 加权的支撑数 = n·n·n（对 n 归纳；每层 sumℕ-const + 收尾 *-identityʳ/*-assoc） |
| `mm-cyclic` | `:98` | mm 在循环位 (a,c),(c,b),(a,b) 处 = T₁（三重 oneIf-refl + 双重 ⊗-identityˡ） |
| ★ `weighted-zero` | `:107` | **零秩抽取：WeightedRankLE₃ n 0 w ⟹ w ≡ T₀（处处）**——下界游戏的第一个约束：0 项分解只剩零张量；证明 = 实例化 (x,y,z) = ((a,c),(c,b),(a,b)) + sumFin{0} 定义 + ⊗-identityʳ |

验证：standalone exit=0（0 postulate / 0 REWRITE / 0 洞）；独立检查件 6 签名 exit=0。
诚实边界：陪集/子空间分析未镜像（2609.06725 的第二半）；条件熵词汇（conditional/premium）
要 ℝ 对数，有限口径属立项 B-T3/B-T4。
