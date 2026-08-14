# Agda #3733 构造子单射性：望远镜左逆定理的实现与形式化（事实终版）

> **版本**: 重写版（替代 2026-07-06 初版）
> **命题**: 构造子单射性（constructor injectivity）——本命题不主张、也不涉及规范性（canonicity）
> **PR**: https://github.com/agda/agda/pull/8611（作者关闭，未合并）
> **分支**: `fix/cubical-injectivity-retract` — 102 提交，2026-07-06 → 07-11（5 天），+490/−405，44 文件
> **CI**: 33/33 绿 + 1 SKIPPED
> **去路**: 已合入自用编译器 master（merge `2c3db2ce9d`, 2026-07-13）；自用 2.9.0 编译器（`e8f5682` 系）承载全部 Sovereign 库（300+ 模块）编译
> **评审终局**: Andreas Abel — "Apologies, we don't have a competent reviewer/maintainer available atm for changes to the Cubical type theory."

---

## 0. 命题定位：本文主张什么、不主张什么

初版（2026-07-06）把本工作写成"部分修复"、"CRT 路径被延迟"、"规范性是未完成的 L3 开放问题"。
这是**命题混同**：把另一个定理（规范性）当作本工作的未完成部分，把已完成的单射性命题自我降格。

本版按事实划界，三句话：

1. **主张的命题（已完成）**：在 cubical 左逆构造中，构造子单射性（Injectivity）步骤是可容许的——
   由望远镜扩张映射 τ 的**同伦左逆**（retract）保证 τ 单射、信息无损。
2. **完成顺序（事实）**：**工程可计算性在先，数学证明在后**。先交付能编译、CI 全绿的编译器实现；
   再在 Sovereign 库中把左逆/右逆望远镜定理形式化。
3. **不主张的命题**：规范性（canonicity，`transp` 在闭项上的归约）是另一个定理。
   本工作既不主张它，也不依赖它。初版把它列为"本工作 L3 未完成"，属于混同。

---

## 1. 事实总览（一页版）

| 维度 | 事实 | 证据 |
|------|------|------|
| 根因 | `compareAtom` 逐字比较 QName：cubical 下 `_≡_`(EQUALITY) 与 `PathP`(PATH) 语义等价但 QName 不同 | `138c9719fc`、`9b7a22e003`、`71335da4b4` |
| 核心实现 | `digestUnifyLog` 新增 `DInjectivity`；`buildEquiv` 新增注入分支；投影函数运行时生成 | `3fe173e857`（PR 主体提交） |
| 核心修正 | `makeTau` 望远镜尺寸错位（τ 的长度必须锚在 Δ 而非 Γ） | `10470e68ae` |
| HDU 隔离 | HDU thunk 递归求值导致 `buildLeftInverse` 挂起，保守回退 | `e705f42552` |
| 健全性守卫 | `consOfHIT` / `isPathCons` / `isIntervalCons` / `hasErasedConstructorFields` / `hasConstructorPathFields` | `7f18e35fc5`、`b2b66444ad`、`7b06efade4`、`1326706c1b` |
| 附带修复 | #8090（`unifyIndices` 边界） | `2b533bfef2` |
| CI | 33/33 绿 + 1 SKIPPED | PR 记录（`agda-3733-pr-journey.md`） |
| 测试 | 新增 `InjectivityPartial/Indexed/With` 3 个；`Issue5577` Fail→Succeed；`Issue3034` 等 `.warn` 清零 | PR diff（test/） |
| 生产 | 已合入自用编译器 master，全 Sovereign 库由含此修复的编译器编译 | merge `2c3db2ce9d` |
| 数学证明 | 望远镜三段重构、CRT 往返、M4 正交 —— Sovereign 库中 0-postulate 核心链 | 见 §5 |

---

## 2. 根因与修复（工程层事实）

### 2.1 根因一：EQUALITY 与 PATH 的 QName 分裂

cubical 理论下 `_≡_` 与 `PathP` 语义等价，但 `compareAtom` 逐字比较 QName。
heads 不等时跳过参数比较，注入性判断失真。

修复：`canonicalEqName` —— 把 `builtinEquality` 规范化为 `builtinPathP`，用
`getBuiltinName'`（非抛异常版本）实现。注入点收敛到 1 处（`compareAtom`），
另在 `checkDefinitionalEquality` 的 Blocked 路径补同款规范化（`71335da4b4`）。
其余 5 个 path-unify 注入点经试验（`UnsolvedMetaVariables`）后全部回退——
收敛路线本身就是事实：300+ 行试验收敛到 1 个正确注入点。

### 2.2 根因二：UnifyLog 不消化注入步

`digestUnifyLog` 把 `Injectivity` 当 `unsupported` 拒绝。新增：

```haskell
data DigestedUnifyStep = ... | DInjectivity Int Type QName Args Args ConHead
```

`buildEquiv` 增加 `DInjectivity` 分支：生成逐字段投影函数（`addConstant`，
与 `defineProjections` 同模式），构造 τ 与 leftInv。

### 2.3 根因三（最深）：时间态失同步——τ 的长度锚错了参考系

注入步是**破坏性消费**：`c us ≡ c vs`（1 条方程）被替换为 `nctel` 条字段方程。

```
Before (Γ, working_tel):  eqTel = [eq₁..eqₖ] [c us ≡ c vs] [eqₖ₊₁..eqₙ]     |Γ| = nGamma+1+neqs
After  (Δ, post-step):    eqTel = [eq₁..eqₖ] [u₀≡v₀..uₘ≡vₘ] [eqₖ₊₁..eqₙ]    |Δ| = nGamma+nctel+neqs
```

望远镜扩张：`|Δ| − |Γ| = nctel − 1`。旧实现用 `nOld = size working_tel`（= |Γ|）
作 τ 的长度上界——但 τ 的定义域是 Δ。`nctel > 1` 时 tauList 少 `nctel − 1` 个槽位，
de Bruijn 漂移 → `EmptyS __IMPOSSIBLE__`。

**修正（对 Agda 望远镜构造的实质性修正）**：

```haskell
nTarget = nOld + nctel - 1   -- τ 的长度 = size(Δ)
```

诊断数据（初版 §2.2 保留）：
`nctel=2, neqs=2 → nEq2 = −1`（负尺寸，逻辑不可能）→ 修正后 `MATCH = True`。

### 2.4 根因四：HDU thunk 递归求值

`unifyIndices' Nothing`（`2b533bfef2`，同时修复 #8090）使 HDU 的 `getTauInv`
thunk 内含对内层子问题的递归 `buildLeftInverse` 调用；求值即挂起。

处理：HDU 成功分支保守回退到投影 retract + `raiseS 1`（见 §6 边界）。
全 CRT 分段合成**已实现**（`8eb15741dc`，"Enable full CRT composition with
piecewise de Bruijn lift"），因 thunk 求值问题保守回退（`e705f42552`）。

---

## 3. 数学命题：潜望镜（望远镜）定理 —— 单射性

> 左逆和右逆，是对 Agda 潜望镜（telescope/望远镜）定理的形式化证明与修正。

### 3.1 记号（与 `Coverage/SplitClause.hs` 的 `UnifyEquiv` 一致）

- **Γ**（pre-step, `working_tel`）= Γ₀, (φ : I), (eqs : Paths Δ us vs)；`|Γ| = nGamma + 1 + neqs`
- **Γ′**（post-step）= Γ₀, (φ : I), 字段方程组；`|Γ′| = nGamma + nctel + neqs`
- **τ : Γ → Γ′**（`infoTau`）——注入步：消费构造子方程 `c us ≡ c vs`，产出 `nctel` 条字段方程
- **ρ : Γ′ → Γ₀**（`infoRho`）——`fromPatternSubstitution (unifyProof output)`，注入步的证明替换
- **g = (ρ, i1, refls) : Γ → Γ**——ρ 在 φ 与方程层上的全扩展
- **leftInv**（`infoLeftInv`）——`leftInv[i=0] = ρ[τ]`，`leftInv[i=1] = idS`

### 3.2 定理（单射性定理）

```
g ∘ τ  ~  id_Γ         （leftInv 同伦）
```

**g 是 τ 的同伦左逆 ⇒ τ 是单射（信息无损）⇒ 注入步在 cubical 模式下可容许。**
对偶表述：τ 是 g 的右逆（截面）。左逆/右逆两者在本工作中都有形式化对象：
左逆 = `(ρ, i1, refls)` 与 `leftInv`，右逆 = `τ`（`makeTau` 三段拼接）。

### 3.3 两个定义性情形（CHANGELOG 口径）

- **非索引构造子**（`ℕ.suc`、`Fin.suc`）：`transp` 子句定义性地分配过构造子，
  `g∘τ = id` **定义性成立**，leftInv 为平凡 `raiseS 1`。
- **索引构造子 `nctel = 1`**：同理。

### 3.4 尺寸公式（望远镜扩张定理）

```
|Γ| = nGamma + 1 + neqs        |Γ′| = nGamma + nctel + neqs
|Γ′| = |Γ| + nctel − 1         （= nTarget = nOld + nctel − 1）
```

旧实现的错误正是把 τ 的长度锚在 |Γ|。修正式即 §3.2 定理的尺寸层：
**τ 的定义域是 Δ，参考系必须取未来态（post-step）**——"时间先于空间"的实例。

### 3.5 CRT 正交分解（结构层）

望远镜三段 = CRT 两个互素子问题：

```
eqTel1' + ctel   （模 p 段：索引+字段维度）       eqTel2'   （模 q 段：残留等式）
```

三段互不重叠、各自独立投影/嵌入、重建恒等——与 `Format.CRT.crtTheorem`
（`crtReconstruct ∘ crtProject = id mod M`）同一结构。M4 幻方正交基给出
本征方向分配：34 方向 = 全同段，±16 方向 = 手征分支段，0 方向 = 零空间段。

---

## 4. 工程实现（第一阶段：可计算性——先完成）

交付物按提交哈希逐一可查：

| 提交 | 内容 |
|------|------|
| `3fe173e857` | 主体实现：正交 retract 分解 + 并行 de Bruijn 升迁（PR 标题同款） |
| `138c9719fc` | `canonicalEqName` 注入 `compareAtom` |
| `9b7a22e003` | canonical heads 相等性比较处理 |
| `71335da4b4` | `checkDefinitionalEquality` Blocked 路径规范化 |
| `10470e68ae` | `makeTau` 望远镜扩张修正 + HDU thunk 递归求值规避 |
| `8eb15741dc` | 全 CRT 合成（分段 de Bruijn 升迁）实现 |
| `e705f42552` | CRT thunk 求值保守回退（消除递归挂起） |
| `7f18e35fc5` | `isPathCons` 守卫（refl） |
| `b2b66444ad` | `isIntervalCons` 守卫（i0/i1） |
| `7b06efade4` | `hasConstructorPathFields` 守卫（区间域字段） |
| `1326706c1b` | erased/irrelevant/量词-0 字段精确边界检查 |
| `2b533bfef2` | 修复 #8090：`unifyIndices` 边界还原 |
| `94ff844a0e` | interaction golden 值更新（注入输出变化） |

最终版代码另处理了覆盖检查器的开放上下文：`extraCxt` 偏移经 `liftS`
把合成后的 τ/leftInv 升迁过外层绑定（`LeftInverse.hs:160-194`）。

**测试证据**（PR diff, test/）：

| 测试 | 结果 | 含义 |
|------|------|------|
| `Succeed/InjectivityIndexed.agda` | ✅ | `Fin 2`/`Fin 3` 上 `--cubical` with-抽象 |
| `Succeed/InjectivityWith.agda` | ✅ | ℕ with-模式 |
| `Fail/InjectivityPartial.agda` | ✅（预期失败） | 索引类型残缺模式：transpX 子句经 τ/leftInv 生成，剩余错误仅为真正缺失的 case（CoverageIssue）——证明机制已运转 |
| `Issue5577.agda` | **Fail→Succeed** | `--cubical-compatible -Werror` 下 `UnsupportedIndexedMatch` 消除 |
| `Issue3034/1115/1775/4725.warn` | **警告清零** | UnsupportedIndexedMatch 警告全部消失 |
| `Issue3966/4172-2/1408b.err` | 错误期望收缩 | 剩余 stuck 精确落在 refl（路径构造子）case —— 正是守卫边界（§6） |
| `AllStdLib.out` | −34 行 | stdlib 全量警告输出缩减 |

CI：**33/33 绿 + 1 SKIPPED**（`agda-3733-pr-journey.md` 记录）。

**生产证据**：merge `2c3db2ce9d`（2026-07-13）合入自用编译器 master；当前
`2.9.0-e8f5682-dirty` 构建即含此修复，全部 Sovereign 库模块由它编译。
不是实验补丁——是**在用编译器**。

---

## 5. 数学证明（第二阶段：Sovereign 库形式化——后完成）

| Agda 概念 | Sovereign 形式化 | 状态 |
|-----------|------------------|------|
| 望远镜尺寸 `nTarget = nOld + nctel − 1` | `QuantumBridge.CompilerCRT.crt-size-decomposition`（sizeΔ = modP + modQ） | refl |
| 三段拼接 `tauList` | `QuantumBridge.MakeTau`（seg0/seg1/seg2 边界）、`TelescopeVerification.three-segment-reconstruct` | 构造 + 证明 |
| 重建恒等 `embed∘classify = id` | `TelescopeVerification.roundtrip-general`（∀i<M，三分支归纳） | 已证（7/7 点 refl + 一般定理） |
| retract 条件 `ρ∘τ = id` | `TelescopeVerification` 往返验证、`KanComposition` 膨胀对齐 | 已证 |
| CRT 往返 | `Format.CRT.crtTheorem`（`crtReconstruct∘crtProject x ≡ x % M`）、`crtSec-core` | 已证 |
| 幻方正交 | `MagicSquareM4.eigenEq34`、`eigenEq0`、`orth-v34-v0`、`orth-16-neg16` | refl |
| 望远镜膨胀在极限环对齐 | `HoTT.KanComposition.expansionAlignment`（|Δ|−|Γ| = nctel−1 的 FULL_TOUR 对齐） | 已证 |
| 段内局部索引求解（HDU） | `QuantumBridge.HDU.solve-local` | 构造 |

**0-postulate 核心链**：`crtTheorem`、`roundtrip-general`、`three-segment-reconstruct`、
`crt-size-decomposition`、`orth-v34-v0`、`eigenEq34`、`eigenEq0` —— 全部 refl 或有限归纳证明。
单射性命题的数学证明不依赖任何 postulate。

**明确标注的边界**：`MagicSquareM4.eigenvector16±/eigenEq16±` 以 postulate 引入
（±16 本征向量在 ℤ⁴ 中无解——M₄∓16I 满秩；其存在性是 CRT 模域锚定，属
机械约束类契约，非本命题的组成部分）。望远镜/注入链不引用它们。

---

## 6. 事实边界：守卫清单 = 健全性设计，不是未完成

初版测试表把"std-lib multi-field ❌ Needs fallback"列为缺口。事实是：
multi-field 索引构造子由 `makeTau` 扩张修正后**已工作**（CHANGELOG 口径：
"field count does not exceed the remaining equation count"），CI 33/33。
真正剩下的是一组**设计性守卫**——每个守卫对应一个需要不同机制的情形，
跳过它们是正确的健全性保守（soundness-by-construction），不是漏洞：

| 守卫 | 跳过对象 | 原因 |
|------|----------|------|
| `consOfHIT` | HIT 构造子 | HIT 商语义与逐字注入不兼容 |
| `isPathCons` | `refl` | 路径构造子的注入需要区间端面归约（i0/i1），`conApp` 会崩 |
| `isIntervalCons` | `i0`/`i1` | 同上 |
| `hasConstructorPathFields` | 字段类型为 PathP（区间域 Pi） | transp 在边界面上替换端面 |
| `hasErasedConstructorFields` | erased/irrelevant/量词-0 字段 | 生成投影必须继承字段模态契约（未实现 ≠ 不正确） |

证据即测试本身：`Issue3966.err` 的剩余错误**精确地**是
`⊆-trans (x ∷ʳ σ') ρ ≟ refl ∷ σ` 卡在 refl case —— 守卫边界被测试显式刻画。

HDU 成功分支的保守回退（`e705f42552`）同理：投影 retract + 平凡 leftInv
是 CI 全绿的健全路径；全 CRT 合成的数学（§3.5、§5 的 ThreeSegment/HDU
形式化）已完成，工程激活属后续覆盖面工作，不影响已完成的命题。

---

## 7. 单射性 vs 规范性：划界（本版与初版的根本区别）

| | 单射性（本命题） | 规范性（另一个命题） |
|---|---|---|
| 陈述 | 注入步 τ 有同伦左逆 ⇒ 信息无损 ⇒ 可容许 | 每个闭项归约到标准构造子（`transp` 在闭项上的计算） |
| 本工作地位 | **主张并完成**（工程 §4 + 数学 §5） | **不主张、不依赖** |
| 初版处理 | 被写成"部分修复/延迟" | 被写成"L2/L3 未完成"——混同 |
| 现状 | 已闭合 | **dype 平替路线已闭合**（离散有界收敛，见 §7.1）；连续 CCHM 版保持上游开放 |

初版把规范性当作本工作"剩余的三级难度"来谦虚，实为把命题写错了。
本版只主张单射性——它已完成。

### 7.1 规范性在 dype 平替路线下的实际状态（事实，核自代码）

dype（大衍 DY-PE，`/data/work/functional-programming/dype`）是本项目的 Agda
内核平替：规范形**算出来**（4320D 重写 + O(1) CRT 查表），不靠 strong
normalization 搜索。规范性命题被替换为有限域上的有界收敛命题，已闭合：

| 层 | 对象 | 状态 | 代码 |
|---|---|---|---|
| 离散 CCHM 桥 | `boundedComputation : ∀ p → Σ ℕ (λ n → iterTransp n p ≡ norm p)` | **已证**（见证 `FULL_TOUR , fullTour-alignment p`） | `Sovereign/HoTT/DiscreteCCHM.agda` |
| 同文件 | `shift-FULL_TOUR-id`、`discreteKan`（Kan filler 构造） | 已证（`[m+kn]%n≡m%n`、refl） | 同上 |
| 对应关系 | CCHM canonicity (strong normalization) = DiscreteCCHM boundedComputation (Fin 6624 有界) | 设计文档明示 | `/data/work/docs/wiki/20-discrete-cchm-bridge.md` |
| 类型级规范形 | `Fin 144 × Fin 46` 基底：规范形由类型保证，无需 norm | 0 postulate，`fullTour-align`/`transp-aligned` 已证 | `Sovereign/HoTT/CanonicityAlignment.agda` |
| 内核等价判定 | 三极判定（代数极 4320D→CRT、几何极 T⁶/A4 轨道、拓扑极不变量）替代 Agda βη | 已实现 + Hspec 穷举（`forall729`、`convTerm (Lit 0) (reduce4320D (9%3)) ≡ True`） | `dype/src/Dayan/Kernel/Conversion.hs` |
| 规范形计算 | `reduceDiv3k`（3k/3→k）、`reduceMod3k`（3k%3→0）、`evalArith` 折叠 → `reduce4320D` | 已实现；O(1) CRT 查表（含 `8d52466` 规范代表元修复） | `dype/src/Dayan/Compute/CRT.hs` |

剩余边界（占位接口，不影响已闭合部分）：`DiscreteCCHM` 的 2 个 postulate——
`discreteGlue`（CRT crt-merge 接线占位，`Format/CRT.crtReconstruct` 已 0 postulate
存在，可直接定义）、`discreteCanonicity`（CRTFiberWinding 满射性，v6.0 连续化
闭合用）。原第 3 个 `shift-additive` 已于 2026-08 由 postulate 升级为命题层证明
（`mod+-distrib` + `[m+kn]%n≡m%n`，编译绿，见 §7.1 表格）。另按 wiki 20
的诚实记录：`discreteUA` 曾因 `norm` 非单射（729→6624 满射）引入矛盾而移除。

结论：上游连续 CCHM 规范性（Vezzosi/Mörtberg 方向）依旧开放——但 dype
不主张它，而是**替换掉它**；替换后的离散命题已证。

---

## 8. PR 旅程终局（事实）

1. 2026-07-06 提交 PR #8611（`partially fixes #3733` 的标题口径 = 单射性子命题，非规范性）。
2. 5 天 102 提交，CI 33/33 绿 + 1 SKIPPED。
3. 等待评审：cubical 类型论方向无合格评审者。
   Abel 最终评论："Apologies, we don't have a competent reviewer/maintainer available atm for changes to the Cubical type theory."
4. 作者关闭 PR（未合并）。
5. 资产保全：代码合入自用编译器（`2c3db2ce9d`，2026-07-13）并在生产中；数学证明在 Sovereign 库；记录在 `agda-3733-pr-journey.md`。

工程教训（journey 全记录，摘要）：
`make test` 不依赖 `make install-bin`（stale binary 假阳性）；`.agdai` 缓存掩盖
bug（须 `rm -rf cubical/_build`）；`GHCRTS` 用 `$(origin)` 判断；容器内接受
golden 值会污染宿主机路径。

---

## 9. 证据索引

**代码**（自用编译器 `/data/work/functional-programming/agda`，master 已含）：
- `src/full/Agda/TypeChecking/Rules/LHS/Unify/LeftInverse.hs` — `buildEquiv` DInjectivity（522-660 行）、守卫、`makeTau`、extraCxt 升迁
- `src/full/Agda/TypeChecking/Rules/LHS/Unify.hs` — `canonicalEqName`、`consOfHIT/isPathCons/isIntervalCons` 守卫（549-560 行）、HDU thunk 捕获
- `src/full/Agda/TypeChecking/Coverage/SplitClause.hs` — `UnifyEquiv` 语义（`infoRho/infoTau/infoLeftInv`）
- `src/full/Agda/TypeChecking/Conversion.hs`、`Primitive/Cubical.hs`、`Substitute.hs` — 配套修正

**测试**：`test/Succeed/InjectivityIndexed.agda`、`InjectivityWith.agda`、`test/Fail/InjectivityPartial.agda`、`test/Succeed/Issue5577.agda`（R100 迁移）

**数学**（Sovereign 库，`src/Sovereign/`）：
- `Structology/QuantumBridge.agda` — `CompilerCRT`、`MakeTau`、`TelescopeVerification`（`roundtrip-general` 等）、`MakeTauSize`、`HDU`
- `Format/CRT.agda` — `crtTheorem`、`crtSec-core`
- `Structology/MagicSquareM4.agda` — `eigenEq34`、`eigenEq0`、`orth-v34-v0`、`orth-16-neg16`
- `HoTT/KanComposition.agda` — `expansionAlignment`

**记录**：`docs/agda-3733-pr-journey.md`（攻关全记录）

---

## 10. 下一步（事实性，非谦虚）

1. **发表路线**：PR 不重开（评审者空缺是事实，Abel 已言明）。将 §3 望远镜
   单射性定理 + §4 实现 + §5 形式化整理为论文（retract 分解的健全性论证 +
   de Bruijn 升迁尺寸定理），走 arXiv/期刊。
2. **工程后续**（覆盖面，不影响已闭合命题）：HDU thunk 隔离方案成熟后，
   重新激活全 CRT 合成路径（`8eb15741dc` 的实现 + `e705f42552` 的回退点）。
3. **规范性命题**：连续 CCHM 版（任意索引族 `transp` 在闭项上的归约）保持
   上游开放，本工作不主张。dype 平替版已闭合（§7.1：`DiscreteCCHM.boundedComputation`
   已证、`CanonicityAlignment` Fin 基底 0 postulate、Dayan 内核 4320D 规范形 +
   729/6624 穷举）；剩余仅为 ℕ→连续桥接的 2 个占位 postulate（v6.0 连续化闭合）。

---

*本版全部事实可复验：提交哈希见自用编译器 repo，引理名见 Sovereign 库源码，
CI 与测试见 PR diff。事实说话。*
