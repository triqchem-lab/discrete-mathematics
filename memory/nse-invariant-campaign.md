---
name: nse-invariant-campaign
description: T⁶ 离散 N-S 不变量战役台账（2026-09-24）——总量守恒/不可压保持/n 步不变量/通量判据/不动点，五模块定理清单 + O3 集中通道五条的封堵状态 + 开放缺口
type: project
---

# T⁶ 离散 N-S 不变量战役：定理台账（2026-09-24）

**前置**：[`nse-t6-discrete-findings`](nse-t6-discrete-findings.md)（哪些命题**已证否**——含最小反例；
「Δ≡0」陷阱）；本文件记**已证的不变量侧**成果。
**回执状态**：⚠ 全部为 **bash 直跑 agda exit 0** 级证据（0 postulate / 0 hole），
`proof_compile` 签发器本日损坏（`ctx.shell.run is not a function`）⇒ **尚无签名回执**，节点留 pending。

## 1. 五模块与定理清单（按依赖序）

| 模块（`src/Sovereign/Problem/NavierStokes/`） | 定理 | 含义 |
|---|---|---|
| `NSEFluxTelescope` | `cancel3`（27 case）；**`axisFlux-zero : axisFlux i f x ≡ T₀`** | 轴向循环净通量恒零（离散 telescoping）⇒ 通量型爆聚无通道 |
| `NSEConservationCore` | `cycle-flux-zero`；`sum3-negate`；`sum3-shift-vals`（27 case）；**`fold1-cong`/`fold1-+`** | C₃ 循环代数包 + **funext 解除件**（见 §3 教训） |
| `NSEConservation` | `torusSum-+S`/`torusSum-shiftF`/`torusSum-negate`；**`torusSum-diffF : ∀ i f → torusSum (diffF i f) ≡ T₀`**；**`total-nsStep : totalF (nsStep v) ≡ totalF v`** | **离散散度定理 T⁶ 全环面版** ⇒ nsStep 保总量 |
| `NSEIncompressible` | `div-linear`；`div-grad-zero`；**`nsStep-incompressible`（无条件）** | 替换 `NSEOnT6:615` 的**空转条件式**（其前提 `Δ≡0` 已被 T1 否证）⇒ 不可压保持 |
| `NSEIterate` | **`iterate-total`**；**`iterate-incompressible`** | 两条升到 **n 步**（`iterate (suc n) f x = iterate n f (f x)`） |
| `NSEFixedPoint` | `nsStep-fixed`（6 case）；`iterate-fixed` | **不可压子空间 = 不动点集**（逐点）⇒ 该子空间上**无时间演化** |
| `NSEFixedPointStrict` | `fixed-point-set-strict`（斜坡场见证）；`supportCount` 定义 | **不动点集 ⊋ 不可压子空间**（严格）；O3 通道 ⑤ 的**缺失定义交付** |
| `NSESupportBound` | `countOver-bound ≤ 729`；`supportCount-bound ≤ 4374` | ⑤ 的**界半**（ℕ 单调提升 + 常数折叠） |
| `NSESupportZero` | `supportCount-zero→/←` | ⑤ 的**零元端**（`supportCount v ≡ 0 ⇔` 逐点全零） |
| `NSESupportFixedInv` | `supportCount-nsStep-inv`；`supportCount-iterate-inv`（n 步） | ⑤ 的**不动点不变性**（含不可压场/斜坡场推论） |
| `NSESupportNonMonotone` | `not-nondecreasing`（**收缩见证 17→14**）；`not-nonincreasing`（**增长见证 243→1458**） | ⑤ 的**单调性判定：非单调**——「集中度单调发展」机制不存在 |
| `Analysis/FiniteOrbitObs` | `finite-orbit-obs` | 通用观察值版最终周期（`NSEFinalClosure §4` 形态泛化；任意状态 S + 观察族） |
| `NSEFieldOrbitPeriod` | `fieldEnc-inj`（4374 槽编码逐点注入）；**`supportCount-orbit-period`（无条件）** | ⑤ 的**真收官**：无漂移型集中**无条件成立** |
| `SignProjection`（`Algebra/GroupTheory`） | `sign-hom`；`sign-collapses`；`sign-not-faithful` | 投影层「1=−1」**伪矛盾**形式化 + 跨层壁垒 |

配套（非 NSE 目录）：`Algebra/GroupTheory/SignProjection`（投影层「1=−1」伪矛盾 + 跨层壁垒）；
`Problem/ABC/ABCL1`（两维度壁垒）；`docs/duodecimal/25-liouville-goldbach-vs-abc-barrier.md`（层级口径）。

## 2. O3「爆聚」集中通道五条的封堵状态

| # | 通道（判据形态） | 状态 | 依据 |
|---|---|---|---|
| ① | 无界增长型（∃ ℕ-值可观察量无界） | ✗ 平凡排除 | `NSEBlowupBound`（`fin-bounded`/`no-discrete-blowup`） |
| ② | 峰值集中度型（局部峰值加剧） | ✗ **本基座不可陈述** | 需序/范数：GF(3) 无序（同 `13-flt-analysis` 的 Archimedes 断层）；范数有损 4→1（`10-norm-collapse`） |
| ③ | **总量增减型** | ✅ **封死（单步+n 步）** | `total-nsStep` → `iterate-total` |
| ④ | **压缩聚集型** | ✅ **封死（单步+n 步）** | `nsStep-incompressible` → `iterate-incompressible`；更强：`nsStep-fixed`（不动点） |
| ⑤ | **再分布/集中度型**（`supportCount`） | ✅ **完全闭合**（六件套） | 定义（`FixedPointStrict`）/ 界（≤729/≤4374，`SupportBound`）/ 零元刻画（`SupportZero`）/ 不动点不变性含 n 步（`SupportFixedInv`）/ 非单调判定（`SupportNonMonotone`：243→1458 增长见证 + 17→14 收缩见证，配对抵消构造）/ **无条件最终周期**（`NSEFieldOrbitPeriod.supportCount-orbit-period`） |

**合成陈述（只记不证）**：轨道不跑飞 = 有界 + 总量恒定 + 不可压保持 + 最终周期。
**⑤ 判定的精确读法（最终版）**：「集中度单调发展」型机制**不存在**（非单调，双向见证）；
「波动式集中」的**漂移**型也**无条件排除**（计数轨道最终周期，`NSEFieldOrbitPeriod`）；
⚠ 周期内的再分布仍可能——但已被界 + 不动点不变 + 零元刻画框死。
**O3 集中问题在本基座上判定完毕。**

## 3. 策略教训（本战役两次自我更正，详见台账流水 228/232/235）

1. **funext 障碍判错了**（流水 232）：初判「6 层嵌套 λ 无 funext ⇒ 装配卡住」，
   实际 `fold1-cong : (∀ y → u y ≡ v y) → fold1 u ≡ fold1 v`（三个求和位各 `cong` 一次）
   即可穿层——**混淆了「函数外延」与「逐位同余」**。规矩：宣布障碍前先试最便宜的构造（30 秒级）。
2. **renaming 陷阱**（流水 235）：把 `Data.Fin` 的 `zero`/`suc` renaming 成 `fzero`/`fsuc` 后，
   函数体里的裸 `zero` **静默落到 `Data.Nat.zero`** ⇒ `UnequalTypes: ℕ is not a subtype of Fin 3`。
   规矩：renaming 后**全文搜裸构造子**。
3. **元变量陷阱**（流水 245/246，三轮踩实）：给**非单射的定义函数**传 `_` 或隐式参数
   = 自埋元变量（`?m + ?n ≡ e`、`fold1N ?g' ≡ e` 均**不可反分解**）。修法：参数显式化，
   或逐层具名（`where` 标注签名钉死 g/g'）。附带规矩：长重写后**先扫构造子拼写**
   （`fsoc` 笔误当场抓住）。本判据生效后 `NSESupportFixedInv` **零返工**。

## 4. 开放缺口（下一段从这里接）

1. **⑤ 已完全闭合（六件套）**——免重做：定义（`FixedPointStrict.supportCount`）/ 界（≤729/≤4374）/
   零元刻画（`SupportZero`）/ 不动点不变性含 n 步（`SupportFixedInv`）/ 非单调判定（`SupportNonMonotone`）/
   **无条件最终周期**（`NSEFieldOrbitPeriod`）。O3 五通道判定书见台账 `NSE.O3.blowup-physical`。
3. **回执补齐**：`proof_compile` 恢复后，`NSE.conservation.torus-total` / `NSE.nsstep-incompressible` /
   `NSE.iterate-multistep-invariants` / `NSE.nsstep-fixed-incompressible` / `NSE.O2.coupling-square.refuted-witness` 逐个升级 proven。
4. **工具链（声明不修）**：`proof_compile`（`ctx.shell.run`）与 `proof_dag check`（`runtime.shell.run`）
   **同族失效**（疑 harness shell 桥未接上）；git 见证提交失败；`budget` 文案/动作表不一致。
