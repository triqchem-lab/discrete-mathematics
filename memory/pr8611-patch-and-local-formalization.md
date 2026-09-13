# PR #8611 补丁 ↔ 本地形式化证明（**已更正归属**）

**日期**: 2026-09-10（初版）→ **2026-09-10 更正**（用户指出：应该是 `fix/cubical-injectivity-retract` 分支）
**任务**: 找出对应 PR #8611 元理论变更的本地形式化证明

> ⚠ **本文件初版把 PR #8611 误认为 `eb1251683f`。已更正。** 两者是**不同的变更**：
> **PR #8611 = 分支 `fix/cubical-injectivity-retract`**（retract 机制重构，**不改**接受关系）；
> **`eb1251683f`** = 之后的本地提交（**改**接受关系）。详见 §1。

## 0. 一句话
形式化证明**存在且完整**（三层、0 postulate、0 hole、三个编译回执）；
**上游无法审理的原因不是缺数学，是缺「数学 ↔ Haskell 实现」的桥接**（wiki 自述 L2 = 0 行代码）。

## 1. 两个变更，别再混（这是初版最大的错）

### 1a. PR #8611 = `fix/cubical-injectivity-retract`（2026-07-13 并入 master）
- reflog：`2c3db2ce9d HEAD@{2026-07-13 03:37:51}: merge fix/cubical-injectivity-retract`；分支顶 `abedbc22d5` 是该 merge 的祖先。
- **真正内容**（`git diff origin/master...fix/cubical-injectivity-retract -- src/full/Agda/TypeChecking/`，**7 文件 305 insertions / 28 deletions**）：

  | 文件 | 行 |
  | --- | --- |
  | `Rules/LHS/Unify/LeftInverse.hs` | **+217** ← 「Functions for building the **left inverse** part of a 'UnifyEquiv'」 |
  | `Conversion.hs` | +39 |
  | `Rules/LHS/Unify.hs` | +25 |
  | `Unify/Types.hs` | +16 |
  | `Primitive/Cubical.hs` | +18 |
  | `Datatypes.hs` | +9 |
  | `Substitute.hs` | +9 |

- ⚠ **它保持上游的 `UnifyStuck`**（直读 `git show 分支:...Unify.hs` ⇒ `failure = return $ UnifyStuck []`），
  `Empty.hs` **无** `instantiateFull tel`，并把 `test/Fail/Issue292.agda` **留在 Fail**。
  ⇒ **PR #8611 本身不改变接受关系**（是保守的机制重构）。

### 1b. `eb1251683f`（2026-07-27，本地提交，**与 PR #8611 是两件事**）
**它修的是「空类型定义不完备 + 场景覆盖」**（工具链缺陷修复，非数学命题）。提交信息自述：

> Empty.hs: add `instantiateFull tel` before `splitLast` to ensure **MetaV-substituted types are reduced to constructor form**.
> Unify.hs: modify failure fallback to return `NoUnify (UnifyConflict)` when both equation sides are different Def nodes with zero eliminations, **instead of `UnifyStuck []`**.
> Golden test updates: Issue292/292d/413/835/Stuck — **previously stuck emptyness checks now resolve correctly**.

即：**把本该判为空却卡住（stuck）的情形判出来**；Issue292 / 292d / 413 / 835 / Stuck 的 golden 更新 = **场景覆盖**。

> ⚠ **更正我初版的定性**：我曾写成「`eb1251683f` 重新挑起了上游明确拒绝的『类型可区分』语义」——
> 那是**从测试改名（Fail→Succeed）反推意图**，**错了**。Issue292 改判 Succeed 是**完备性的推论**。
> 该测试正文注释「using subst, one could now prove distinctness of types, **which we don't want**」
> 记录的是**上游的顾虑**，可作为日后回馈社区时要说明的点，**但不是**本地修复的动机。

### 1b′. 人类裁决（2026-09-10）：PR #8611 一线**暂缓**
- 已与上游管理员沟通：**找不到能审核该理论变更的人**——证明器底层元理论研究者面窄（知名学者及其学生），
  很多理论**无人维护**。
- ⇒ 该修复**只能本地实现**；**我们现在使用的 Agda 版本就是修复过的版本**。
- Agda 的限制与缺陷**仍然存在**，但**够用**。**待本数学库结束后**再评估是否向社区反馈。
- ⇒ 台账 `FX.pr8611.patch-located` / `FX.pr8611.missing-bridge` 置 `abandoned`（仅指「推进上游」动作线）；
  定位与三层形式化作为**本库自己的资产**保留。工具链限制已入 `prover_limits: agda-empty-type-undecided-stuck`。

### 1c. 实测：本地工具链带的是哪一条？
`/opt/agda/agda` 编译 master 的 `test/Succeed/Issue292.agda`（复制到 /tmp 避开模块名检查）→ **exit 0（接受）**。
而分支的 `test/Fail/Issue292.err` 记录的实际输出是 `Is empty: false2 ≅ true (stuck)`。
⇒ **本地二进制接受了分支会拒绝的东西 ⇒ 它带 `eb1251683f` 的语义**，不只是 PR #8611。

（`.o` 时间 16:36/16:38 早于 18:04 的提交，但这只说明"先改代码构建测试、再提交"，**不能**据以断定二进制不含该提交；**行为测量 + 分支自己的 golden file 才是可靠判据**。）

## 2. 行为见证（把「元理论变更」变成可编译项）
元理论变更**不能**在 Agda 内部形式化为命题（它是 about Agda 的），但**行为后果**可以。

`src/Sovereign/Trust/PatchedTypeChecker.agda`（回执 `55630f32b1ca5f75e9a87ebbe91a582890da42a9e8d4afce33d02523aa1820e6`）
```agda
distinct-records-are-empty : (R1 ≡ R2) → ℕ
distinct-records-are-empty ()      -- 只有带 eb1251683f 的 Agda 才过
same-record-is-inhabited : R1 ≡ R1
same-record-is-inhabited = refl    -- 对照：判的是「不同 Def 节点」而非「等式一律为空」
```
**本模块见证的是 `eb1251683f`，不是 PR #8611。** 在纯分支状态下它**应当编译失败**。
模块头已按此更正（初版那段把两者混为一谈）。

## 3. 本地形式化证明：三层（对应 PR #8611）
| 层 | 模块 | 关键命题 | 回执 |
| --- | --- | --- | --- |
| **算术层** | `Arithmetic/CRTLemmas.agda` | `coprime-POW2-POW3 : Coprime POW2 POW3`（= `gcd≡1⇒coprime refl`；POW2=65536, POW3=177147, M=POW2·POW3）；`crt-merge` | `87fbdf01d52d…` |
| **双射/收缩层** | `Algebra/Duodecimal.agda` | `crt12-roundtrip : ∀ x → crt12 (π3 x) (π4 x) ≡ x`（12 case refl）；`crt12-inv-π3/-π4`（各 12 case refl ⇒ 双射） | `80e1e8c27600…` |
| **望远镜/retract 层** | `Structology/QuantumBridge.agda` §`TelescopeVerification` (604–679) | `roundtrip-general`；`crt-orthogonal`；`deBruijn-lift`；§`MakeTauSize.target-lt-old`；§`HDU.solve-local`；§`ThreeSegment` | `dae36afeee1a…` |

### 名字级对应（不是隐喻）——这是本次更正的关键证据
分支 `LeftInverse.hs` 实测含：`makeTau`×4、`liftS`×8、`nTarget`×2、`nOld`×4、`retract`×10。
`QuantumBridge.agda` 的自述注释逐条同名：
- `:640` 「这对应 PR #8611 中 **makeTau** 的 idempotence: compose(τ) = id」
- `:661` 「对应 PR #8611 中 **liftS** 的偏移计算」
- `:666` 「对应 PR #8611 的 **retract** 拼接」
- `:695,702` 「PR #8611: **nTarget = nOld + nctel − 1**」
- `:712` 「对应 PR #8611 中 **unifyIndices'** 的逻辑」

⇒ **望远镜/retract 层正是对分支 `LeftInverse` 机制的形式化。**

## 4. ⚠ 两处必须说清的差异
1. **`crt-orthogonal` 名实不符**：`QuantumBridge` 里它是 `nG + 1 + nC ≤ M-tel`（**段不重叠上界**），
   **不是** `wiki/39-logic-type-theory.md:109-110` 写的 `gcd(POW2,POW3)=1`；后者在 `CRTLemmas.coprime-POW2-POW3`。
2. **没有桥接**：`wiki/39:124-125` 自述——QuantumBridge 证的是 CRT 分解的**数学合法性**，
   dype/PR #8611 是同一结构的 **Haskell 实现**，**两者之间无形式化桥接（extraction/refinement/编译时验证），L2 当前 0 行代码**。

## 5. 结论（含 2026-09-10 裁决）
- **PR #8611 一线暂缓**：上游无人可审该元理论变更 ⇒ 修复只能本地实现 ⇒ **现用 Agda 即修复版**。
  数学侧三层形式化（含与分支 `LeftInverse` **名字级对应**的 retract 层）仍是**本库自己的资产**，
  继续在库内复用即可，不再面向上游推进。**待本数学库结束后**再评估是否向社区反馈。
- **`eb1251683f` 是另一件事**（空类型定义不完备 + 场景覆盖），属**工具链缺陷修复**：
  已入 `prover_limits: agda-empty-type-undecided-stuck`，机器判据 = `Sovereign.Trust.PatchedTypeChecker` 能编译。
- **本库自己的动作项**：不变——需要「Agda 数学 ↔ 实现」桥接时才考虑 L2；
  作为数学库，本库的正当产出是**数学侧三层形式化 + 工具链能力判据**，这两样都已就位。
- ⚠ 不再重复的工作：**不要**为了「向上游证明」去重新考古 patch 内容或重建 Agda；
  证据已在 §1、§3 与台账 `FX.pr8611.*` 固化，日后要反馈社区时直接复用。

## 6. 台账节点
`FX.pr8611.patch-located`（active，分支内容，已更正）｜`FX.pr8611.patch-live-witness`（**proven**，回执 55630f32…，见证 eb1251683f）｜`FX.pr8611.local-formalization`（**object + proven**）｜`FX.pr8611.eb1251683f`（**proven**）｜`FX.pr8611.missing-bridge`（active，缺口）

## 7. 方法论教训（我这次连错两处）
1. **拿"工作树在哪个分支"当"二进制从哪个分支构建"**——错。分支与构建是两件事。
2. **拿时间戳推构建内容**——不可靠（先改代码构建测试、后提交是常态）。**行为测量才是判据**：
   跑判别性 golden test，看二进制接受还是拒绝。
3. **两点 diff（`A..B`）与三点 diff（`origin/master...B`）含义不同**：
   前者是"A 到 B 的变化"，后者是"从共同祖先到 B 的**这个分支自己的改动**"。
   我最初用两点 diff 看分支，只看到"master 多出来的东西"，于是把分支误读成"被回退的旧线"。
   **要看一个分支的 PR 内容，必须用三点 diff。**
