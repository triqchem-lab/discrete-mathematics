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
| `TRMultipletsNat.agda` | `sum-odd`：∀ a n → sumOdd a n + a² ≡ (a+n)²（**完整 ℕ 索引版**）+ 4 个实例 | `05743ad7…` | 距 Σ_λ(2λ+1)=(2l+1)(2J+1) 只差 a=J∸l、n=2l+1 的实例化 |
| `NoSplitJ1Full.agda` | `no-split-full`：与 shift + flip 都交换 ⇒ 6 个非对角元为 0、三个对角元相等（标量）；另 `shift³`、`flip²`（生成元阶） | `c9d1e186…` | 一般情形（含非对角）；无挠性用构造子互异证 `neg-eq-self`；生成元阶 `shift³`/`flip²`/`g³`（g=flip∘shift）全在 Agda；闭包 = 12 阶 = A₄（oracle 回执 `56921d3e…`） |
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
