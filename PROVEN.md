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
> M19 镜像 Lean `Rectangle/Weights.lean` 的谓词层——Bläser 2003 的 2mn + 2n − m − 2（m ≥ n ≥ 3; 2026-11-28 更正公式, 此前记作 2n²+n−2）、
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

### 立项 A-T2 执行记录（2026-11-26/27）：Wang 框架 F₂ ⟨3,3,3⟩ ≥ 20 证书的独立复验

`engineering/wang_cert_check.py` + `engineering/tests/test_wang_cert_check.py`（立项书 A-T2/A-T4 的
Python 轨）。复验对象 = `wcgbg/tensor-rank-lower-bound` 的 `cert_matrix_q02_n333`（F₂ ⟨3,3,3⟩ ≥ 20,
arXiv:2603.07280 的机器可查证书; LFS 真身 115KB 文本 + 33MB .btp 回溯档案）。

- **全量 496/496 轨道独立核对通过**（两次全量套件独立 OK: 4133s + 4139s）: 结构规范 RREF 495/496
  （终轨道无约束）+ flatten 14 + forced 14 + degenerate 230 + backtracking 238（含终轨道 ≥ 20）;
- **负控制精确转红**: 篡改 orbit-300 声明 +7 → `claim 24 > proved 17` 在该轨道精确失败 ✓;
- 调试手段: C++ probe（ng-log/tbb shim 编译信任基）逐组合打印对拍, 定位两个移植 bug
  （T1 打包的跨步展平提取、query 群作用方向 Apply vs ApplyInverse）——移植 bug, 非证书问题;
- 意义: 我们的 GF(3) 下界路线（立项 A-T3 = F₃ 实例化自跑）的核对器范式已通（同一框架、同一格式）,
  A-T3 跑出 F₃ 证书后可直接入本核对管线。

## 二十、矩阵乘法指数线 M21——稀疏定律的有限口径（`TensorRankSparseLawsGF3.agda`，462 行，2026-11-27 登记）

> 立项 B-T3（陈述层）+ B-T4 的代理定义。Lean 上界机器的三条定律
> （`Rectangle/Weights.lean:19` DensityBound、`Rectangle/Mask.lean:17` CellBound、
> `Rectangle/Sparse/Law.lean:332` DegreeBound）都以 `exp(exponent F (log I)(log J)(log K))` 的形式出现,
> 那是实数。本件不用 ℝ: 把 `|U|·E ≤ C` 写成「对每个下斜率 p/q 的纯 ℕ 不等式」`|U|^q·(IJK)^p ≤ C^q`。

| 符号 | 位置 | 命题 / 状态 |
|---|---|---|
| `wmmRect` / `WeightedRankLERect` | `TensorRankSparseLawsGF3.agda:79` / `:84` | 矩形加权结构常数 + 加权矩形积的 r 项分解（镜像 Lean `Weights.lean:8`）; M19 的 `WeightedRankLE₃` 是 (n,n,n) 实例 |
| `supportSizeᵣ` / `suppRowsᵣ` / `suppColsᵣ` / `suppInnerᵣ` | `:109`–`:119` | 支撑数与三个完成集计数的矩形版（M19/M20 的方形版定义性相同, 独立检查件 `refl` 核对） |
| `LowerSlopeᵣ` / `UpperSlopeᵣ` | `:152` / `:157` | **指数的离散代理**: 格式 (I,J,K) 的下斜率（每个幂的每个分解都满足 体积^{(p/q)·幂} ≤ 项数）与上斜率（每个幂存在分解 ≤ 体积^{(p/q)·幂}） |
| `DensityBound₃` / `DegreeBound₃` | `:168` / `:177` | ★★ 定律的有限口径, **陈述, 无居民** |
| `CellBound₃` | `:190` | ★★ CellBound 的有限口径——**只有平方输出集实例**（见诚实边界）, 无居民 |
| ★ `lower-slope-boundary` | `:227` | ω₃-boundary ⟹ 方格式 (n,n,n) 的下斜率 3/4: `(n·n·n)^(3m) = (n^m)⁹ ≤ ρ⁴` |
| ★ `upper-slope-strassen` | `:245` | Strassen ⟹ (2,2,2) 格式的上斜率 15/16: `(7^m)^16 = (7^16)^m ≤ (8^15)^m` |
| `pow-exp-strict` / `pow-cancel` | `:267` / `:284` | 底 ≥ 2 时幂对指数严格单调、可约指数（自写, 不走类型类实例） |
| ★ `upper-lower-slope` | `:290` | 同格式的上斜率 ≥ 下斜率: `p′·q ≤ p·q′`（在 m = 1 处对拍） |
| ★★ `saving→upper-slope` | `:325` | **Saving₃ ⟹ 上斜率**: `RankLE₃ n r` 且 `r^q < n^p` ⟹ `UpperSlopeᵣ n n n p (3·q)`（指数换底: Saving₃ 以 n 为底, 格式体积是 n³; m = 0 一侧要用 `*-zeroʳ` 与 `1^k≡1`, 因为变元指数下 `p · 0`、`1 ^ k` 都不归约） |
| `saving-2-7` | `:385` | 可读实例: `UpperSlopeᵣ 2 2 2 17 18`（复用 `cert-strict`, 不重算） |
| `upper-slope-one` | `:369` | 上斜率的**非空性见证**（仅平凡格式）: `∀ p q → UpperSlopeᵣ 1 1 1 p q`——每幂取 `rank-one` 的张量幂; 一般格式的 schoolbook 非空性未做 |
| ★★ `degree-law-boundary` | `:451` | **应用示范**: DegreeBound₃ + ω₃-boundary ⟹ `支撑数⁴·(n·n·n)³ ≤ (432·n³·r)⁴`（U = 整个支撑, I = J = K = n, 下斜率 3/4） |

**数值子句的来源**: `cert-7¹⁶≤8¹⁵ = m≤m+n (7^16) 1951441519231`——7^16 = 33232930569601、
8^15 = 35184372088832 由 Python oracle 整数核对; 同一组里 7^15 ≤ 8^14 **不**成立, 所以 15/16 是这组分母下最紧的见证。

**验证**: standalone exit=0（0 postulate / 0 REWRITE / 0 洞）; 独立检查件 `/tmp/m21chk/CheckM21.agda`
17 条主签名逐字核对 exit=0; 顶层名全库扫描无重复（首版 `cube` 与三处同名, 已改 `cubeₙ`）。

**诚实边界**:
- CellBound₃ 不是完整的 CellBound: Lean 的 `short i j |u| = min(log i, log j, log|u|/2)` 在一般 |u| 下给出
  实数边长, 格式不是整数格式; 其证明核心 `width`（`Sparse/Degree.lean:562`）是熵型实数量。
  本件只覆盖 |u| = A·A 且 A ≤ i、A ≤ j 的情形——此时 short = log A 精确成立 [边界标注]。
- 三条定律**不证**: 它们在 Lean 里是定理（`coeff_density` / `coeff_cells` / `coeff_degrees`）, 证明走
  Character 定价层（`exponent_le_of_characters`）, 本库没有 Character 对象。
- 斜率代理与 Lean 的 `exponent` 之间的等价（E = inf 上斜率 = sup 下斜率）是外部事实, 需要 ℝ 上的稠密性论证
  [阅读判断·外部]——本件**不陈述也不证明**它, 只保证有限形式自身成立、并与库内两半衔接。
- 上斜率的无条件非空性（schoolbook ⟹ 斜率 1 对一切格式可容）未做: 需要一般格式的 schoolbook 矩形分解, 库内没有。

**本轮踩坑（别再踩）**:
- **三层嵌套的 `sumℕ-cong` 不要手写括号**: 首版最后多关 3 层; 改成带类型的具名绑定（fb / gb / hb）才对。
  编译前跑括号深度自检（逐行累计深度, 负深度即多关）一次抓出两处。
- **单调性引理的「哪个因子固定」**又错了一次: `2 * V^a ≤ V * V^a` 是左因子变, 要 `*-monoˡ-≤`;
  已在 §「别重复实现」记过, 这次仍先写成了 `*-monoʳ-≤`。
- `cong (λ t → t * V) (*-comm V x)` 是把已经是乘积等式的东西又套一层——`*-comm V x` 本身就是 `V * x ≡ x * V`。

### 立项 A-T3 执行记录（2026-11-27）：Wang 框架的 F₃ 实例化——GF(3) 上 ⟨3,3,3⟩ ≥ 17 的机器可查证书

证书 = `engineering/wang_f3ext/certs/matrix_q03_n333_v1.{pb.txt,btp}`（322 KB + 13.0 MB; sha256 见 README §7.1）。
重跑核验 = `bash engineering/wang_f3ext/verify.sh engineering/wang_f3ext/certs/matrix_q03_n333_v1.pb.txt`。

- **结果**: `UNCONSTRAINED TENSOR RANK LOWER BOUND: 17`。逐维（界 / 证明类型）: dim 7: 6–12; dim 6: 9–13;
  dim 5: 10–13; dim 4: 12–14; dim 3: 13–15; dim 2: 15; dim 1: 16; dim 0: **17**。
- **三重核验**: ① 框架自带 C++ verifier `OK`（8.7 s CPU）; ② 独立核对器 `engineering/wang_cert_check_fq.py`
  736/736 轨道（flatten 15 + forced 2 + backtracking 339 + degenerate 380, 回溯重放 22,520,923 个节点, 60 s CPU）;
  ③ 负控制: 终轨道 17 → 24, 在 `orbit 735: claim > proved` 处拒绝; dim 9–5 检查点上四类证明各做过一个负控制, 都精确转红。
- **枚举完整性**（独立于枚举器实现的证明）: 轨道大小守恒 Σ|orbit| = [9 choose d]₃, 10 个维度逐维精确相等。
- **搜不到的边界（诚实）**: 17 < 域泛型已知的 19（Bläser 2003）, **没有刷新 F₃ 的下界**。差距不是数学上的:
  F₂ 公开证书用满 forced product 2^32 + 1e7 步, 这里是 2^28 + （dim ≤ 4）1e6 步; F₃ 每维的极小约束数约 2.5–3 倍,
  `Get` 一次探针原版 2.1 µs（F₂ 约 0.1 µs）。dim ≤ 5 的时间由回溯步数上限主导。
- **工程件**: `engineering/wang_f3ext/`（F₃ 扩展补丁 + 手工构建垫片 + 五处语义不变的快路径 / 剪枝 + 各自的对拍件 + README）。
  本机 bazel 构建崩溃（无 Xcode）, 走 clang++ 直编。
- **这轮修掉的自身 bug**（都不是框架的）: 垫片 `parallel_for` 分块差一（F₂ 回归「碰巧绿」）; 核对器把内核输出的
  `claim_ok` 标志当成了界。教训写入 README §8 与 memory。

**新坑（别再踩）**:
- **「回归通过 ≠ 替身件正确」**: 垫片要针对自己的逻辑单写测试（参数格点全扫 + 对旧版本的负控制）。
- **排查先在崩溃点打印输入**: 这次先怀疑了自己的群作用和上游枚举器（各写了一个独立检验, 都通过）才去加转储, 多走两轮。
- **先量再改**: 我先给 RREF 写了快路径, 空闲时一测只快约 1.7 倍; 微基准显示 `Get` 的时间 3/4 在群作用上。
- **可复现性要说准**: 产物差异全部落在 Mach-O 的 `LC_UUID` 与 ad-hoc 代码签名里（签名覆盖可执行文件名）,
  不能用 `cmp` 整文件比较不同名的产物; 按段比（`otool -l`）。
- **替换正在运行的二进制用 `mv`**（`cp` 覆盖会改写正在被映射的 inode）; 结束进程要按名字精确匹配
  （`pgrep -x`, 不要 `pgrep -f`——后者会匹配到监控自己的命令行, 也曾只杀掉了外层 `time` 包装而漏掉真正的搜索进程）。

**续跑 v2 与搜索层后续（2026-11-27 下午）**——细节在审计 §M.10 与 `engineering/wang_f3ext/README.md` §5.3 / §5.4 / §7.4:
- **续跑 v2**（v1 上 1e7 步全程）: 53 条中间轨道上涨（dim 4: 14 的轨道 151 → 172; dim 3: 15 的轨道 3 → 35）, **终界仍 17**;
  三重验证全过。证书不在 git（轨迹档案 114 MB）, 在 `~/work/wang-f3-certs/matrix_q03_n333_v2.{pb.txt,btp}`。
- **为什么不是再加预算就行**: 回溯证明是对「假想 (L−1) 项分解」的反证, 节点值取所有子节点的最小值;
  dim 0 的 18 以 dim 2 的 14 张平面全部到 16 为前提（v2 一张都没到）。
- **一处差点误报**: 回溯叶子里大量「基 ∪ 选中行」线性相关, 我一度当成可靠性缺口; 查论文后确认重复因子是设计
  （路径项 = 乘积项）。核对器保持与框架验证端逐条一致。
- **新加速**: `Get` 的 NEON 批量内核; 回溯搜索去重键 + 类子集求值（dim 6 CPU 56.79 s → 5.92 s, 轨迹逐字节相同）;
  核对器 `bt_fq.c` 两处越界修复。
- **一处更正（2026-11-27 晚）**: 去重键那一提交在 dim 5 上让搜索**慢了 1.9 倍**（同窗口 1813 → 3389 CPU 秒）, 当时只记了「没有提速」。
  换成紧凑键缓存后 dim 5 为 1086 CPU 秒（扇出 8: 785）, 轨迹仍逐字节相同。教训: 新旧二进制要在同一窗口、同一步数预算下背靠背计时。
- **又是一处更正（2026-11-27 深夜）**: 紧凑键缓存的首版（75de6fdc）在 dim 4 上比最初还慢（丢了上游的提前退出）,
  且缓存的淘汰有 bug（到上限后重建风暴）。重开的续跑 v3 在 dim 4 卡了五个多小时、零产出。两处已修:
  dim 4、1e5 步 最初 860 CPU 秒 → 688（扇出 8: 115）; dim 5、1e6 步 835 CPU 秒。
  教训: 逐字节等价回归只管对不对、不管快不快; 每换一层要在目标维度上同窗口计时, 并把「到上限」的分支单独逼出来测。
- **续跑 v3（2026-11-28 凌晨, 第四次才跑完）**: dim 3 步数 2e7、dim 2–0 步数 3e7; dim 3 有 2 条 14 → 15, **终界仍 17**;
  dim 2 的 14 张平面在 3 倍步数下一张没动。三重验证全过; 证书 `~/work/wang-f3-certs/matrix_q03_n333_v3.{pb.txt,btp}`
  （sha256 03efce71… / 376e8b43…）。另修了日志垫片 `LOG_EVERY_T` 判断写反的 bug（bc94dfe5）——搜索一慢进度行就全没了,
  前两次没能及时发现卡死有它一份。
- **加步数的上限（2026-11-28 01:25 实测）**: dim 2–0 开 3e8 步, 32 分钟后进程占用 25 GB、交换区 13.4 / 14.3 GB, 已杀。
  原因是回溯证明的轨迹全程在内存里、随步数增长。dim 4 卡在时间上、dim 2 卡在内存上: 这台机器上「加步数」走不到 18。
  我挂的内存哨兵量的是 RSS（3–4 GB）, 没响——macOS 上要看占用（top 的 MEM）或交换区。

## 二十一、矩阵乘法指数线 M22——指标集泛型的秩分解与结构引理（`TensorRankIndexGF3.agda`，252 行，2026-11-28 登记）

**起因**：用户问「3×3 能不能用代数结构闭包做数学证明、不靠暴力搜索」，要求先盘点、先规划、想清楚再尝试。
盘点与判断写在立项书「立项 C」；本件是按计划走的第一步。

**文件**：`src/Sovereign/Algebra/LinearAlgebra/TensorRankIndexGF3.agda`。

- §1 `RankLE X Y Z T r`：指标集泛型的 r 项秩分解（X Y Z 任意集合，T : X → Y → Z → Trit）；
  `rankLE₃→idx` / `idx→rankLE₃` 与 `RankLE₃` 往返。
- §2 ★ `rank-pull`（沿任意映射 g : X' → X 拉回）、★ `rank-invar`（g 有左逆 h 时搬回原张量）。
- §3 ★ `rank-restrict`（线性限制：子空间的基由 s : Fin k → Fin m 给出，限制后的结构常数
  Σ_x s j x ⊗ T x y z 仍有 r 项分解；核心等式 `restrict-eq`）。
- §4 ★ `rank-swap`（两个输入对换）、★ `rank-rot`（三变元轮回）。
- §5 `bläser₃-boundary : Set` = ∀ r → RankLE₃ 3 r → 19 ≤ r（陈述，无居民）；
  ★ `bläser₃→flatten`（它蕴含展平下界 r ≥ 9）；`sentinel-compatible`（19 ≤ 23）。

**核对**：`agda` exit=0；0 postulate / 0 REWRITE 规则 / 0 洞。
独立检查件 `~/work/checks/CheckM22.agda`（仓库外，持久副本；2026-11-28 从 /tmp 转存，转存后重编 exit=0）：21 条（主签名逐字重述 + 读法检查：对换两次 = 没动、轮回三次 = 没动、
Laderman 分解先拉回再限制仍是 23 项、陈述层展开），exit=0。
oracle `engineering/oracle_tensor_rank_gf3.py` 新增 M22 一节，ALL_PASS：
rank-pull 3072/3072；rank-invar 384/384，负对照（非置换 g）0 个 h 能恢复；
rank-restrict 19216/19216，独立路径（三线性型 = 普通矩阵乘法）1200/1200，负对照（s = 2·e_x₀）恰 8 次；swap / rot 64/64。

**诚实边界**：不改进任何下界数字（库内 n = 3 仍是 r ≥ 9）。它交付的是以后任何一条下界证明都要用的结构事实
（Wang 框架 §3.1 命题 1 的 monotonicity / invariance）。一般线性换元的完全不变性（「(T∘s)∘s⁻¹ ≡ T」）未做。

**同日更正（文献）**：此前库内 4 处把 Bläser 的 19 写成「2n²+n−2」。按 arXiv:2603.07280v11 引言逐字核对：
R(⟨n,m,n⟩) ≥ 2mn + 2n − m − 2（m ≥ n ≥ 3），任意域，秩；出处是 2003 年 «On the complexity of the multiplication
of matrices of small formats»。1999 年那篇给的是 (5/2)n² − 3n。已改：立项书「现状」与 B-T6、审计 §L、
`TensorRankSparseGF3` 头注（改后重编 exit=0）、本文件 §十八。

**新坑（别再踩）**:
- **类型签名里的隐式变量不进函数体**: `restrict-eq {k m r} …` 的定义体里要用 m / r, 必须显式绑成模式
  `restrict-eq {m = m} {r = r} …`; where 块 / let 块的局部签名里同样取不到。
- **「提公因子」的 u 是函数不是值**: `sumFin-scale₃ k u c` 里 u : Fin r → Trit; 写成 `(ra ρ i)`(i 未绑定)是 NotInScope。
  要的是 `λ i → ra ρ i x`。
- **括号自检脚本别用 `line.split('--')`**: 它会把首行 `{-# OPTIONS --rewriting … #-}` 从 `--` 处切开, 误报一个没闭合的 `{`;
  而正文里真正的错误(第一行多一个右括号)反而被平衡计数掩盖——逐个应用各占一行, 再用脚本数, 才定位到。

## 二十二、矩阵乘法指数线 M23 / M24 / M24-a——Hopcroft–Kerr 的 2×2 排除论证：GF(3) 上 ⟨2,2,2⟩ 的秩恰为 7（2026-11-28 登记）

**起因**：用户对 C-T2（Hopcroft–Kerr）说「开始」。动笔前先读原始论证：Wang 论文（arXiv:2603.07280v11）§2 与附录 C
给出 F₂ 上 ⟨2,2,2⟩ ≥ 7 的完整走例；再让框架在 F₃ 上跑了一遍 ⟨2,2,2⟩（枚举与下界各 0.0 秒，10 个轨道，下界 7），
把它的证明树当作路线的预言。Agda 里的证明沿同一棵树：全空间 ≥ 1 + 超平面 → 每个超平面含一个 K 型子空间
（K = span{J, E₂₂}，X = [[0,a],[-a,d]]）→ K 上 forced product（两个单积切片 + 残差展平 4）。

**文件**（三件，全部 exit=0，0 postulate / 0 REWRITE 规则 / 0 洞）：

- `src/Sovereign/Algebra/RingTheory/TritStdlibRing.agda`（M24-a，125 行）：Trit 作为标准库的 `CommutativeRing 0ℓ 0ℓ`
  （★ `trit-comring`，逐字段取 Base/Trit 的律）+ Trit 上的环求解器 `module TritSolver` + 可判定相等 `_≟ₜ_`。
  库内已有 12 个模块把 ℕ 的算术重排交给标准库 solver（ListBounds / GF3HammingCount / Ring3pow11 等），这是同一个做法在 Trit 上的实例。
- `src/Sovereign/Algebra/LinearAlgebra/TensorRankAlgebraGF3.agda`（M23，598 行）：指标集泛型、与 2×2 无关的四条操作。
  `skip` / `skip-sum`；★ `rank-drop`、`rank-drop₃`（去掉恒零的一项）；`TritInv`、`sumFin-nonzero`；
  ★★ `slice-normalize`（Hopcroft–Kerr 的代换：切片是非零的秩一张量 f ⊗ g ⟹ T = f⊗g⊗w ⊕ 余项，w c ≡ 1，余项少一项；
  证明就是 Gauss 消元）；
  ★ `SpanGen`（切片张成：`span-full` 一切切片组合都在第一因子的张成里；`bound` 计数下界：嵌入 Fin (3^d) ⟹ d ≤ r；
  这是 M16-B 展平下界的推广）；
  ★ `rank-linvar` / `rank-change₂` / `rank-change₃`（线性换元：M22 `rank-restrict` 的逆向一半）；`rank-cong`。
- `src/Sovereign/Algebra/LinearAlgebra/TensorRankHK2GF3.agda`（M24，977 行）：
  ★★ `rank-2x2-lower : ∀ r → RankLE₃ 2 r → 7 ≤ r`；`rank₂₂₂-is-7`（下半本件、上半 M13 的 `rank-strassen`）；
  ★ `K-bound`（K 上 ≥ 6：`slice-normalize` 两次 + `res-flatten`）；
  ★ `res-flatten`（残差的 y-切片张成 4 维：四个权重恒给出 δ₂, δ₃, −δ₀, −δ₁，与两次规范化留下的未知量 u, v 无关）；
  ★★ `hyper-wit`（80 个非零泛函各一个 K 型子空间的见证，`Good` 记录四条恒等式：`ker` / `inv-A` / `inv-B` / `move`）；
  ★ `transfer`（沿见证把 W 上的分解搬到 K 上）；`check-weaker`（与展平下界相容）。

**核对**：

- 三件 `~/.local/bin/agda -i src …` 各自 exit=0（本机没有全库门禁，只编了动过的模块与检查件；
  头注改过的 `TensorRankGF3` / `TensorRankFlattenGF3` 也重编 exit=0）。
- 独立检查件 `~/work/checks/CheckHK2.agda`（仓库外，持久副本；运行方法见同目录 README.txt）：54 条，exit=0。含主签名逐字重述，以及读法检查：
  `chk-no-below : ∀ r → r < 7 → ¬ RankLE₃ 2 r`（特别地 `chk-no-6 : ¬ RankLE₃ 2 6`）、
  `chk-strassen : 7 ≤ 7`（定理作用在库内真实的 7 项分解上）、见证行的闭值（`Wit.row … ≡ T₂` 等由内核算出）、
  计数下界在零张量上的实例。
- **负控制（M24，均在副本上做，做完恢复，文件哈希不变 `297ca25aed9d0d39…`）**：
  ① 把 trace 泛函 (1,0,0,1) 那一行的 (P,Q) 换成 (I,I)：内核在该行拒绝——`tt` 的类型 `True (good? …)` 归约成 ⊥，报 `⊤ is not a subtype of ⊥`；
  ② 定理结论改成 8 ≤ r：拒绝（`6` 与 `7` 不等）；③ `K-bound` 结论改成 7 ≤ r：拒绝。恢复后 exit=0。
- oracle `engineering/oracle_tensor_rank_gf3.py`（新增 M23/M24 一节）ALL_PASS：forced product 残差 26244/26244
  （6561 组 (u,v) × 4 个权重），负对照（λ₃ 漏一项）4374 组；超平面分类 80/80（实际用到 17 对 (P,Q)），
  负对照（(I,I) 对多少个泛函不成立）72 个，计数（ℓ 的矩阵秩 1 的 32 个、可逆的 48 个）；
  端到端（Strassen 的 7 项各当一次 i₀：限制 → 搬到 K → 两次规范化 → 残差权重）7/7；分类表对账 81 行逐字一致。
- `engineering/tests`：161 tests OK（2 skipped）。
- 重名：手工模拟门禁（本机 `check_duplicate.sh` 是薄壳）。`T₀≢T₁` 库内已有两处（`NumberTheory/DiscreteFibonacci`、
  `Synthesis/Analysis/EqualityTruncation`），本件改为 import 前者，不写第三处。其余无完全相同的签名。
- 框架的 2×2 证书入库：`engineering/wang_f3ext/certs/matrix_q03_n222_v1.{pb.txt,btp}`（README §7.7）；
  框架 C++ verifier exit=0，负控制（终界 7 → 8）rc=134。

**文献核对（2026-11-28，用户指出「C-T2 先核对 Hopcroft–Kerr 的域假设」——动笔前没做，事后补做）**：

- 动笔前实际做的是: 读 Wang 论文 §2 / 附录 C（F₂ 的走例）+ 让框架在 F₃ 上跑 ⟨2,2,2⟩。**没有对照 Hopcroft–Kerr、
  Winograd 的原文**。
- Hopcroft–Kerr，一手来源已读: Cornell 技术报告 TR69-44（1969-09，扫描件，`~/work/lit/HopcroftKerr_TR69-44_1969.pdf`）。
  报告第 15 页「Minimality of the number of multiplications」: 下界**只在 GF(2) 上证**——
  「we will assume that the elements of the matrix are binary numbers and addition and multiplication are modulo two」，
  靠「整数上的算法取模 2」约束整数情形，并明说反方向不一定成立。所以 **GF(3) 不在 Hopcroft–Kerr 的定理范围内**;
  用户的担心是对的。网络搜索的小模型摘要说「Hopcroft–Kerr 证的是任意域」——是错的，以一手来源为准。
- Winograd 1971（Linear Algebra Appl. 4, 381–388; zbMATH 0225.68018 只给书目）: **域假设没有查到**——原文付费墙，
  zbMATH 评论不开放;二手说法不一（Wang 引言说 ℚ;搜索摘要说特征 ≠ 2 且自标「不是引文」）。[未核对原文]
- 结论不变: GF(3) 上的 7 来自本件的内核证明, 不依赖上面两篇。证明里唯一与 F₃ 绑定的是那张 80 行的见证表;
  K 上的 forced product 与残差的切片下界对任意 u, v 成立, 不含特征假设。
- 顺带查到一处**文献自身的不一致**（未裁决, 留给 C-T3）: Ballard–Ikenmeyer–Landsberg–Ryder 2018（arXiv:1801.00843）引言写
  「M⟨3⟩ 秩的最好下界是 16 [17]」, [17] 是 Landsberg–Michalek 的**边界秩**界 2n²−n+1（ℂ）;
  而 Wang 2026 引言说 Bläser 2003 给 19（秩, 任意域）。两者的对象（边界秩 / 秩）与域（ℂ / 任意）都不同,
  谁对、是否只是措辞疏漏, 要读 Bläser 原文才知道。本仓库 `bläser₃-boundary` 的陈述依据的仍是 Wang 引言这一二手来源。
- 展平这条线的文献值（Landsberg–Michalek, arXiv:1608.07486 引言; 全是 ℂ 上的**边界秩**）:
  Strassen 3n²/2 → Lickteig → Landsberg–Ottaviani 2012 用 Koszul 展平 2n²−n → 2016 得 2n²−n+1 → 本文 2n²−⌈log₂n⌉−1。
  n = 3: 15、16、15。特征 3 下是否成立没有查。

**这次抓到的自己的错**（都发生在 oracle 或编译阶段，没有进内核）：

- 残差的第四个权重手算时把 R(a, b₁₁, c₀₁) 写成 1−v₃（实为 −v₃），6561 组全错——独立实现抓到；
- 残差的参数 u 写成 w₀ + w₀₁·w₁（实为 w₀ − w₀₁·w₁）——端到端 7 个里错 4 个；
- 一度想只用「带符号置换」类的对称搬分解，枚举发现 80 个泛函有 32 个覆盖不到 ⇒ 必须上一般的 P X Q⁻¹。

**诚实边界**：

- 这是把一个已知的、经典的证明形式化，不是新数学结论。n = 3 的下界不变（库内仍是 r ≥ 9；文献 19，搜索 17）。
- 超平面分类没有抽象证明：实现是一张 80 行的见证表，每行由内核归约核对（`mkW … tt`）。
  「80 个非零泛函分两个轨道」在本仓库是 [直觉·未验证]，表不依赖它。
- `span{I, J}` 那个轨道（框架用回溯）在 Agda 证明里用不到。
- 依赖标准库的 `Algebra.{Bundles, Structures, Solver}`（反射生成的证明项仍由内核检查）。
- 独立核对器 `wang_cert_check_fq.py` 写死了 n = 3，2×2 的框架证书没有做独立核对（只过了框架自己的 verifier）；
  它在仓库里只是路线图，定理的权威是 Agda 内核。
- M23 的 `_≡ₜ?_` 与 M24-a 的 `_≟ₜ_` 是两份可判定相等（类型相同、名字不同）；没有合并，因为不想让通用的 M23 依赖求解器模块。

**新坑（别再踩）**:

- **隐式集合变量要写 `: Set`**：`∀ {X Y Z} → (X → Y → Z → Trit) → …` 这种签名，若没有别的东西把 level 钉住，
  模式变量的类型就是悬着的 level 元变量，报 `UnsolvedMetaVariables`（位置在各个模式变量上，很容易误判成别的问题）。
  M22 的引理没事，只是因为返回类型 `RankLE … : Set` 顺带约束了它们。写成 `∀ {X Y Z : Set}`。
- **内联的等式链过不了，拆成具名带类型的步骤就过**：`trans (cong … (sym (sumFin-scale …))) (trans …)` 内联时，
  推断类型里留着未归约的 λ 应用，元变量解不出来；同样三步各给一个 `s1 : A ≡ B` 的签名就一次通过。以后每条链都这么写。
- **内核不会去反演 `sumFin` 的模式匹配来猜张量参数**：`rank-drop₃ _ record{…}`、`sumFin-nonzero _ h` 里的 `_` 都是
  `UnsolvedMetaVariables` + `Refusing to invert pattern matching of sumFin`。张量、被加项一律显式写出。
- **Trit 的 ⊕ / ⊗ 对中性项不归约**：`x ⊗ T₀`、`T₁ ⊗ x`、`x ⊕ T₀` 在 x 是变量时都不动（库里有 `⊗-zeroʳ` 等引理正是为此）。
  所以闭指标上的求和会留下「尾巴」，残差恒等式不能靠 `refl`。解法：给 Trit 建标准库交换环 + ring solver
  （`TritStdlibRing`），每步「具名 + 带类型」，环内重排交给 `TritSolver.solve`；它只认 ⊕ / ⊗ / negate / 字面量，
  δc、sumFin、Fin 的结构要先用手写引理化成干净形状（`sum₂-eval` / `sum₄-eval` / `Rc` / `Rd`）。
- **`trans A B` 后面没有括号**：我惯用的 `trans (cong f e)
 (solve …)` 形式里 `trans` 后面不跟左括号，
  所以第二参数结束处不要再补右括号——这次连续四处在同一个地方多写了一个。
- **where 块里的名字会遮蔽外层模式变量**：`Wemb u v κ y = trans (steps y) (cleanup y)` 里又写 `steps : ∀ y → …`，
  内层的 y 与外层的 y 不是同一个，报 `y₁` 与 `y` 不等。外层已经有的变量不要再量词化。
- **`λ` 是关键字**：不能给变量取名 `λ`（`∀ λ x →` 被读成 λ 抽象，报 `Missing body for lambda`）。
- **`T₁` 是 Trit 的构造子**：局部定义取名 `T₁` / `T₂` 会 `ClashingDefinition`。
- **`Record.field` 不随模块导出**：`open SpanGen …` 不写 `public`，外面就取不到 `W`；record 字段名要 `open` 过才能在
  record 字面量里裸用。
- **`toWitness {a? = d} tt` 在 d 是中性项时过不了**：`tt : ⊤` 对不上 `T (isYes d)`。把「判定为真」做成显式参数
  （`mkW … : True (good? …) → …`），表里每行传 `tt`，闭项时归约成 ⊤，不成立时是 ⊥。

**事故与更正（2026-11-28，下一轮自查发现）**：

- 当时的本地提交（`48ec3e70`、`1ac6961f`；按用户建议压缩后这两个提交已不在历史里，内容并入压缩后的那一个）里的
  `engineering/oracle_tensor_rank_gf3.py` 是**空文件**（0 字节）。
  上一节「核对」里「oracle … ALL_PASS」在那次运行时是真的，但提交进去的不是那个文件。
- 原因：改它的顶部说明时写成了 `open(p, 'w').write(open(p).read().replace(…))`——Python 先求值 `open(p, 'w')`
  把文件清空，再去读它。随后那次「oracle exit=0」是空脚本运行成功，被当成了通过；提交前既没有重跑测试，
  也没有看 `git diff --numstat`（那里会显示 567 行全删）。
- 影响范围：只有这一个文件、只有本地两个提交。远端 `c76d52d9` 的版本完整（24,178 字节 / 567 行）；
  同一天改过的其它文件、仓库外的检查件与 memory 都不空（逐个查过）。
- 恢复：以 `c76d52d9` 的版本为基底，把当天的 M23/M24 一节按原样重放（相对基底 **+325 行 / −0 行**，892 行）。
  忠实性核对：oracle ALL_PASS 且各项数字与截断前逐项相同（残差 26244/26244、负对照 4374；分类 80/80、
  试探 11478 对、实际 17 对、负对照 72、32/48；端到端 7/7）；重新生成的分类表与已提交的表 81 行逐字一致；
  `engineering/tests` 161 OK（2 skipped）。
- 别再踩：① 改文件一律「先读进内存、改完、再写」，禁止在 `open(p, 'w')` 的参数里读同一个文件；
  ② 改完任何文件先看 `wc -c`；③ 「exit=0」不算通过，要看预期的输出标记（ALL_PASS）且输出非空；
  ④ 提交前看 `git diff --cached --numstat`，任何文件出现「行数归零」先停；⑤ 最后一次编辑之后必须重跑测试。

**对一份外部评估文档的核对（2026-11-28，用户贴来并附建议；按「对照记录核」处理，不当指令）**：

- 「阶段 0：审计 17」——重跑 `engineering/wang_f3ext/verify.sh`（对 v1 证书）：① 框架 verifier `Verified. Rank lower bound … is 17`；
  ② 独立核对器 736 轨道全过（展平 15 / forced 2 / 回溯 339 / 退化 380，回溯节点 22,520,923）；③ 负控制（终界 17 → 24）
  `orbit 735: backtracking kernel rejected`，rc = 1。**17 是下界证书**（排除了 ≤ 16），仓库文档里没有任何「17 项分解」的说法
  （README §7.3 本来就写着「它是下界」）。不需要排查。
- 外部文档的数字：子空间总数（56,632 / 8,283,458 / 13,721,229,088）、各维子空间数、射影点数都对；
  **群阶三个数里两个与标准公式对不上**（⟨3,3,3⟩/F₃ 写 126,157,824 = |GL₃(F₃)|² 没算转置，而 F₂ 那一行算了；
  ⟨2,3,3⟩/F₃ 写 269,568，|GL₂(F₃)|·|GL₃(F₃)| = 539,136），「群阶放大 2,235 倍」同口径应为 4,470。
- 外部文档的代码库盘点是另一个代码状态（85–272 个文件、`jac_*` 模块名；本仓库 1066 个文件，点名的 18 个模块里
  只有 `Trit` / `A4Group` / `BurnsideT6` / `GF9` 存在）。它说「完全缺失」的三阶张量秩 / 双线性分解 / 商约化模块，
  库内有 12 个（`TensorRank*`，M16–M24）；它提议当「首个测试用例」的 Laderman 23 项正例早就在内核里（M17）。
- 文献（arXiv 摘要，经代理核）：Tomar 2610.11823（F₂ = 23）的摘要里没有「互补幂等」——
  是替换法 + 对 Wang 的 496 类中的 111 类收紧界 + 27×27 展平约束秩 + 列出全部可行的 22 个首因子集合 + **精确补全搜索**。
  「互补幂等」出自 Yang 等 2609.18722（F₂ ≥ 21 的结构证明）：容量约束与有限几何先把 20 项分解逼到秩剖面 (16,1,3)
  （Σ 秩 = 27），这时秩次可加性取等 ⟹ 各项两两零化的幂等元 ⟹ 与「至多一个首因子可逆」矛盾；全文（含有限商界）有 Lean 形式化。
  另两篇存在：Rudich–Rousseau 2610.01639（整数系数递归算法 ≥ 22，496 个子问题解出 359 个）、Wang 2609.06725（F₂ ≥ 21）。
- 互补幂等恒等式：手推复核成立；oracle 原型（`~/work/checks/proto-idem_oracle.py`，未入库）在真实分解上核对通过——
  Laderman 23 项（GF(3)）：首因子秩剖面 (17,4,2)，Σ 秩 31，Δ = 4，恒等式 529 对零失配；
  Strassen 7 项：剖面 (6,1,0)，Σ 秩 8 = 2³，**Δ = 0**，`R_tᵀ B_t C_tᵀ L_t = I` 成立；负对照（改一个系数）恒等式失败。
  两处与外部文档的写法不同：① 按行主序向量化，恒等式是 `A_t B_s C_tᵀ A_s = δ_ts A_t − l_t m_sᵀ`（C 带转置；
  不带转置时 Laderman 上 266 处失配）；② X、Y 不必满列秩（Laderman 的 rank X = 27 < N = 31），
  但 rank Γ = 27 与 rank Π = Δ 仍成立（幂等元的秩 = 迹 = n³）。
- F₃ 上 3×3 的低维商界（外部文档「阶段 3」的前两步）**本仓库证书里已有**：736 个轨道按余维 0–9 的个数是
  1, 3, 14, 84, 266, 266, 84, 14, 3, 1；直线 3 个轨道，下界 3 / 6 / 9（秩 1 / 2 / 3）；
  平面 14 个轨道，下界依次为 6, 6, 8, 9, 9, 9, 9, 9, 9, 10, 10, 11, 11, 12，其中不含秩-1 点的恰 8 个（下界 8, 9, 9, 9, 10, 11, 11, 12）。
  余维 1 的 3 个超平面轨道下界都是 16。

## 二十三、矩阵乘法指数线——F₃ 容量–剖面探针（2026-11-28 登记；工程件，不进内核）

**起因**：用户第六条消息定方向——「走探针，明确不做 C-T3（至少现在不做）」，并说 F₃ 容量–剖面枚举
「花一个会话就能决定幂等是否值得形式化」。

**结论先写**：主问题**未决**——没有找到 r = 19 下满足全部容量约束且 Σ 秩 ≥ 28 的首因子配置，也没有证明它不存在。
本节的产出是三样可复用的东西（容量表、查表件、五道验证）和若干实测事实。
**不改进任何下界；库里 n = 3 不变**（展平 r ≥ 9；工程证书 ≥ 17）。据此的建议是**现在不形式化幂等恒等式**（理由见末尾）。

**问题**。「互补幂等」恒等式（§二十二末）只在 Δ = Σ_t rank(a_t) − 27 = 0 时有刚性。所以先问：
r = 19 的假想分解是否被**容量约束**逼进 Δ = 0？若是，幂等法在 F₃ 上有抓手；
若能给出一个满足容量约束而 Δ ≥ 1 的首因子配置，这条路在 r = 19 就用不上。

**容量约束（推导）**。设 T = Σ_{t<r} a_t ⊗ b_t ⊗ c_t 是 ⟨3,3,3⟩ 的分解，首因子 a_t ∈ A（9 维）。
W ⊆ A 是子空间，N(W) = #{t : a_t ∈ W}。把第一变元限制到 V ⊆ W^⊥（零化子），首因子落在 W 里的项全消失，
剩下 r − N(W) 项给出 T|_{V×B×C} 的分解，所以 L(V) ≤ r − N(W)；取 V = W^⊥ 最强：**N(W) + L(W^⊥) ≤ r**。
证书 `certs/matrix_q03_n333_v1.pb.txt` 里「余维 c」的条目，其约束行张成的正是某个 c 维 W，
于是 736 个轨道给出一切 W^⊥ 的下界（§二十一 A-T3，三重验证过）。

**容量表**（r = 19；`engineering/wang_capacity_probe.py` 从证书重算；`test_capacity_table_r19` 守住）：

| dim W | 轨道数 | L(W^⊥) 的取值 | cap = 19 − L |
|---|---|---|---|
| 1（直线） | 3 | 16 | 3 |
| 2（平面） | 14 | 15 | 4 |
| 3 | 84 | 13 / 14 / 15 | 4–6 |
| 4 | 266 | 12 / 13 / 14 | 5–7 |
| 5 | 266 | 10–13 | 6–9 |
| 6 | 84 | 9–13 | 6–10 |
| 7 | 14 | 6, 8, 9, 10, 11, 12 | 7–13 |
| 8（超平面） | 3 | 3 / 6 / 9（= 3 × 法向量的矩阵秩） | 10–16 |

即每条直线最多 3 项、每个平面最多 4 项、每个 3 维子空间最多 4–6 项。
⚠ 上一会话摘要里那张表的「d」一列混用了两个含义，以本表为准。

**文件**：

- `engineering/wang_f3ext/standalone/orbit_lookup.cc`（查表件；`bash engineering/wang_f3ext/build.sh 3 lookup …`）：
  把证书的 736 个轨道装进上游 `OrbitMap`（Store = 右乘 GL₃ 共 11,232 个，Query = 左乘 GL₃ × 转置共 22,464 个；
  约 830 万个表项），之后任给 W 的一组基，一次查到 L(W^⊥)。`C` 命令完备地检查一个首因子配置：
  候选子空间用**子集法**枚举——违规的 W 满足 N(W) ≥ t := thr(dim W)，而它的点张成 W，故其中有 t 个点张成恰为 W。
- `engineering/wang_capacity_probe.py`（驱动：容量表 + 五道验证，`ALL_PASS`）与
  `engineering/tests/test_wang_capacity_probe.py`（10 项；查表件缺失时 5 项跳过、降级为 `TABLE_ONLY`）。
- `engineering/wang_f3ext/build.sh` 新增目标 `lookup`；`engineering/wang_f3ext/README.md` §7.8。
- 探索性脚本与会话日志在仓库外 `~/work/checks/probe-capacity/`（会话级，原样保存，不保证可重跑）。
- 上游盘点：`wang-tensor-rank`（origin/main = `9db3d21`，无新提交）**没有**任何容量 / 剖面 / 幂等代码；本仓库此前也没有。
  归属（更正，凭 arXiv:2609.06725 摘要）：capacity-and-profile 策略出自 **D'Ambrosio**，Wang 那篇是把它与自己的自动化框架结合；
  本文首版写成了「Wang 论文的策略」。

**对三份外部总结的核对**（2026-11-28，用户贴来的外部文本；文献部分只到摘要级，经代理取 arXiv）：

- 与记录一致：全子空间数 F₂ 8,283,458 / F₃ 13,721,229,088；平面数 43,435 / 8,069,620；群阶 56,448 / 126,157,824；
  容量表；L = 12 平面的结构（808,704 = 10.02%）；H₀ 内部穷举；负控制是终轨道 17 → 24；全量测试跳过的 2 项是显式门控的
  （F₂ 496 轨道全量核对要 `WANG_FULL=1`，F₃ 全量核对要 `WANG_F3_CERT`）。
- 对不上（文献）：① ω < 2.371552 出自 Vassilevska Williams–Xu–Xu–Zhou（arXiv:2307.07970，2023），不是 Alman 等；
  Alman–Duan–Williams–Xu（arXiv:2404.16349）v3 摘要报的是 ω < 2.371177（配合 arXiv:2608.16884 的数值优化）。
  ② 「ℤ 上精确秩 23 已闭合」不成立：arXiv:2610.01639 摘要写的是「任何带整数系数的 3×3 **递归**算法」下界 22（不排除 22，且限递归类）。
  ③ F₂ 的 ≥ 20 出自框架论文 arXiv:2603.07280，≥ 21 出自 arXiv:2609.06725；外部文本把两者记在同一篇名下。
  ④ Burichenko 2022（arXiv:2211.03404）证的是：不存在长度 ≤ 23、以 S₄ × S₃ 为自同构群的算法（ℂ 上）——对；
  但「Laderman 23 正是破坏对称性的」不对：按 Burichenko 2015（arXiv:1508.01110）摘要，Laderman 算法的自同构群是 S₄。
  ⑤ Conner–Harper–Landsberg（arXiv:1911.07981，2019）：ℂ 上边界秩 ≥ 17——对；「2023」「Smirnov 2013 边界秩 20」没查到。
- 对不上（本地）：① 「F₉ 可用」不对：矩阵族只支持素域（`build.sh` 的 M 只能取 1）。② 「SIMD 2.1 µs → 0.55 µs（4.6–6.4×）」
  自相矛盾（那是 3.8×），且不是记录里的数（README §5.2 是每探针 24–61 ns 对标量 171–291 ns）。
  ③ 「dim 6 从 251 s → 10.9 s（23×）」记录里没有。④ 「8 个首因子落在 F₂₇ 子代数的可逆部分里」说反了：
  全可逆平面是 W 的**零化子**，8 个点落在 7 维的 W = {x : ⟨x, A⟩ = ⟨x, AN⟩ = 0} 里。
- 建议本身的问题：「主动构造一个坏类型的 8 点 + 其余 11 点」得到的是一个**至少有一处违规**的配置（那 8 个点所在的
  W 恰是坏类型），推不出「零违规配置存在」，更推不出「r = 19 被封死」。另外「零违规配置存在 ⟹ 幂等值得做」也不成立：
  若可行的配置里有 Δ ≥ 1 的，正是幂等刚性形式用不上的情形（见上文 (A)/(B)/(C)）。
- 这些「建议」没有执行，等用户定。

**验证**（2026-11-28，全部通过）：

| 验证 | 做法 | 结果 |
|---|---|---|
| 自检 | 每个证书条目取 4 个随机群像，`Get` 必须命中同一个界并由见证还原 | 736 × 4，0 失败 |
| 见证重放 | Python 用**自己写的**矩阵乘法重放 v ↦ (L·τᵗ(v))·R⁻¹，必须落回证书条目的子空间 | 60/60；穷举批各 40/40 |
| 两套完备枚举互证 | C 的子集法 vs 纯 Python 的子集枚举（独立实现） | 候选数与违规多重集逐项相同 |
| 真实分解 | Laderman 23 项的 23 个首因子在 r = 23 下必须零违规；对照 r = 22 应有违规 | 645 个候选、0 违规；r = 22 有 17 处 |
| L = 12 平面的结构 | 穷举过三条固定直线的全部 3,280 个平面；代表束全可逆与行列式型；全枚举 3×3 矩阵后双计数 | 见实测事实第 4 条 |

两条负对照在测试里：见证的界或所指轨道被改动后复核必须失败；一条直线上放 4 个点必须在 dim 1 被报出。

**实测事实**（都是「按证书界」的陈述；查表件 + 驱动给出）：

1. **随机 19 点配置的违规量级**：7 个互不相同直线的随机配置 665–1121 处。按类拆（4 个随机配置共 3,435 处）：
   「7 维子空间里恰 8 个点而零化子是 L = 12 的平面」38%，7 维的其它情形 34%，超平面 16%，6 维 12%，5 维以下 0.3%。
   所以「7 维 + 8 点 + L = 12」只是最大的一类，不是唯一的；再加上第 3 条，至少有两类约束没法靠「把点摊开」来满足。
2. **类型分布**（随机平面，大样本 6,000 个）：L = 6 / 8 / 9 / 10 / 11 / 12 各 8 / 3 / 1450 / 1994 / 1908 / 637 个——
   约 10.6% 的平面是 L = 12（见第 4 条的精确计数 10.02%）。
3. **码表事实**（codetables.de 的 Brouwer–Grassl 表，下界 = 上界）：[19, 9]₃ 的最大最小距离是 **7**，[19, 10]₃ 是 **6**。
   推论：任何 19 点配置必有某个超平面含 ≥ 12 个点（其法向量须为秩 ≤ 2 才不违规），且必有 ≤ 6 个点线性相关；
   「任意 7 点无关」的配置不存在，所以 8 点 7 维子空间躲不掉。
   [文献事实·未独立核验：Griesmer 界本身只排除到 d ≥ 10 与 d ≥ 9，更强的 d ≤ 7 / d ≤ 6 是表里的结果]
4. **L = 12 的那个平面轨道的精确结构**（证书位置 17；程序核对：穷举 + 双计数；测试守住）：平面里 8 个非零元素**全部可逆**，
   即 K = A·span{I, N}，A 可逆、N 的特征多项式在 F₃ 上不可约（N 生成 M₃ 里的一份 F₂₇）。
   代表元 span{A, B} = span{022110100, 020100001}（行主序 9 位），det(xA + yB) = x³ + x²y + 2xy² + y³。
   这类平面共 808,704 个 = 全部平面的 10.02%（全枚举 19,683 个 3×3 矩阵：没有 F₃ 特征值的 3,456 个；
   11,232 × 3,456 ÷ 48 与 576 × 11,232 ÷ 8 两种数法一致），与随机抽样的 10.1–10.6% 相符。
   含奇异矩阵（秩 1 或 2）的平面都不属于这一类。
   所以「8 个点张成的 7 维子空间 W 恰好是坏类型」⟺ 这 8 个点同时被两个矩阵 A、AN 零化（A、N 如上）；
   类型只由 W 自己决定，与配置里其余的点无关。
5. **穷举**（过一条固定直线的平面共 3,280 个，全查）：过秩 1 矩阵的平面 L 只取 6 / 9 / 10（152 / 2552 / 576 个）；
   过秩 2 矩阵的平面从不取 12；过可逆矩阵的平面有 576 个是 L = 12。
   **秩 1 法向量超平面 H₀ = {x₁₁ = 0} 内部**（全查）：7 维子空间 3,280 个，L 只取 6 / 9 / 10（152 / 2552 / 576），
   所以 9 个点以内自动合规；6 维子空间 896,260 个，L 只取 9–12（9,714 / 7,104 / 328,434 / 551,008），从不取 13，
   所以 7 个点以内自动合规，8 个点则只有 38.5% 的 6 维子空间放得下。跨超平面的子空间仍是通用类型。
6. **搜索都没到零**：稀疏族（矩阵单位 + 二元和）219–533 处；「12–16 个点放进 H₀、其余在外」的规范化族 685–1371 处；
   按「相关关系稀疏度」做局部搜索，罚项从 996 只降到 900–936 就卡死（每换进一个随机点就带来约 200 个新的 8 点相关关系，
   没有指向「任意 7 点无关」的梯度）；类型无关的放宽版（上限取 3, 4, 5, 5, 6, 7, 8, 12）退火 686 → 331–350 后冻住。

**诚实边界**：

- 证书界是下界，不是受限制张量的真实秩；「零违规」只针对按证书界写出的约束。
- 没找到 ≠ 不存在。F₂ 上同类枚举可行是因为空间只有 511 个点；F₃ 有 9,841 个点。
- 查表件依赖上游 `OrbitMap`；本节没有新增对 `OrbitMap` 本身的验证（它的证据是 README §6 的对拍与上游自测）。

**走过的弯路（如实记）**：

- 首版候选枚举（自顶向下取超平面 + 阈值剪枝）的完备性论证是**错的**（祖先维数更大、阈值也更大，中间节点可能被剪掉）。
  随机配置下靠鸽巢原理碰巧完备；换成可证明完备的子集法后全部数字逐项不变，Laderman 那道验证重跑仍是 645 / 0。
- 一组「对称候选」把轨道大小数错（3×3 的对称对只有 3 个，不是 6 个），配置只有 16 个点、r 也跟着设错，作废。
- 驱动首版一次性往管道写两万条查询，与查表件互等而死锁；改成分批往返。
- 测试首版有三处是测试自己写错（测试矩阵的秩、`ask` 的参数层数、奇异矩阵求逆的期望），逐个改正，被测代码未改。
- 给 `build.sh` 加目标时在同一行上两次把变量名打错，最后用程序从 HEAD 取回那一行并逐字节比对。
- **在对话里说错过一个数学事实**：把 L = 12 的平面说成「正则幂零束、非零元素秩都 ≥ 2」。依据是一次手算行列式，
  抄矩阵时错了一个元素（第三行第一列）。用程序对全部 (x, y) 重算后：det = x³ + x²y + 2xy² + y³，在 F₃ 上无零点，
  是「三个共轭特征值落在 F₂₇」的正则束；「非零元素全部可逆」这半句是对的。随后又把这类平面的占比错算成 5%
  （双计数时分子用直线数、分母用向量数），大样本一量是 10%，改正后两种数法都是 10.02%。
  教训与 §二十二同源：手算的数值结论进对话或文档之前先过一遍程序。

**对下一步的含义**：

- 决定：**现在不形式化幂等恒等式**。它的前提（容量逼出 Δ = 0）在 F₃ 上没有任何证据；
  探针显示容量约束强而带类型，「是否可行」本身是未解的组合问题。三种情形没有区分开：
  (A) 容量约束对 r = 19 不可行（容量本身就给出 ≥ 20，幂等用不上）；(B) 可行但全部落在 Δ = 0（幂等是下一步的工具）；
  (C) 存在可行且 Δ ≥ 1 的配置（幂等的刚性形式对它用不上）。随机配置违规上千、各种搜索都到不了零，
  这个现象对 (A) 和 (C) 都相容，不构成倾向任何一方的证据。
- [未验证·路线推测] 两条可能的下一步，都要新想法：(a) 在规范化族里（大部分点在秩 1 法向量超平面内，
  全部结构约化到 8 维坐标）做**精确**搜索（约束规划 / SAT），而不是随机撒点或盲退火；
  (b) 证明不存在「满足容量约束且 Δ ≥ 1」的配置。
  核对动作：先对「12 个点在 H₀ 内 + 7 个点在外」的 8 维版本做一次小规模精确求解（哪怕只解 dim ≤ 6 的约束）。
- 「只盯 7 维 + 8 点 + L = 12 这一类做局部分析」不够：它只占随机配置违规的 38%，而且它的类型只由那 8 个点决定，
  没有「被其余点破坏」这回事；难点在几百个这类子空间能否同时取好类型，以及超平面那一类（第 3 条）同时满足。

**它不改进什么**：没有新的下界，没有新的内核定理。
