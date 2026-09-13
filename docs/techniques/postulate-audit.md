# 全库 postulate 体检（`H.postulate.audit.unexempted`）

**日期**: 2026-09-14　**方法**: 全量静态扫描 `src/**/*.agda`，**无抽样**
**脚本**: `/tmp/postaudit/audit2.py`（oracle 回执 `1dadfc18dd1a802bfad3860057e38ff313c6fabfaa10b8d1d8c35dc2a571814a`，论域 27 = 枚举 27）
**目的**: 把「哪些 `postulate` 是项目**已论证的 REWRITE 设计**，哪些是**真缺口**」从口头口径变成可复核清单。

> ⚠ 证据分档：**枚举**（哪些模块、几个名字、有无 REWRITE、有无标记、有无洞）是 🟢 oracle 回执级；
> **分类裁决**（下列「桥接公理 / 待审 / 真缺口」）是 🟡 **我的判断**，不是机器判据——须逐条人核。

---

## 1. 数字（含对旧记的更正）

| 事实 | 实测 | 旧记 | 差异原因 |
|---|---|---|---|
| 含 `postulate` **声明**的模块 | **27** | 25 | 旧记用 `grep '^postulate'`（只认第 0 列）；漏掉**缩进块式**（`Engine/QsUpdate.agda:94`、`Format/CRT.agda:233`）与**注释后紧跟成员**的写法（`Coupling/Zhonglv.agda:153`、`Structology/Aether.agda:316`、`Platonics.agda:428`） |
| 其中带 `{-# REWRITE #-}` | **5** | 4 | 多出的 1 个是 `Trust/TwoViewRewritten.agda`（本项目 PGM P1 新增） |
| 无 REWRITE 的 | **22** | 21 | 同上 |
| **单行式** `postulate foo : T`（判定器 `postulateNames` **漏扫**） | **41 处** | 0 | 见 §4 |

5 个带语法依据的：`Structology/{T6,T6Rewrite,XuanwuAbsorption,XuanwuAbsorptionRewrite}.agda` + `Trust/TwoViewRewritten.agda`。

## 2. 22 个无 REWRITE 模块（`post` = postulate 数，`标记` = 项目自带公理登记注释行数，`洞` = `{!` 计数）

| 模块 | post | 标记 | 洞 |
|---|---|---|---|
| `Generated/T6Verification.agda` | 1 | 0 | 0 |
| `Coupling/ZhonglvPhaseSync.agda` | 1 | 0 | 0 |
| `Format/CRT.agda` | 3 | 0 | 0 |
| `Geometry/ProjectiveOrbit.agda` | 6 | 0 | 0 |
| `HoTT/CRTFiberWinding.agda` | 9 | 0 | 0 |
| `HoTT/DiscreteCCHM.agda` | 2 | 0 | 0 |
| `RootMath/Base.agda` | 1 | 0 | 0 |
| `Density/Resonance.agda` | 1 | 1 | 0 |
| `Engine/QsUpdate.agda` | 2 | 1 | 0 |
| `Geometry/ConformalCore.agda` | 8 | 1 | 0 |
| `Geometry/ProjectiveCore.agda` | 4 | 1 | 0 |
| `HoTT/CRTHarmonics.agda` | 3 | 1 | **1** |
| `Coupling/TQ10.agda` | 11 | 4 | 0 |
| `Coupling/Entanglement.agda` | 2 | 5 | 0 |
| `Structology/MagicSquareM4.agda` | 5 | 8 | 0 |
| `Constitution/WindingAsymmetry.agda` | 1 | 9 | 0 |
| `Coupling/CartanTorsion.agda` | 21 | 10 | 0 |
| `Physics/QuartzPhonon.agda` | 3 | 10 | 0 |
| `Structology/Aether.agda` | 4 | 13 | 0 |
| `Structology/Platonics.agda` | 5 | 15 | 0 |
| `Coupling/Zhonglv.agda` | 4 | 19 | 0 |
| `RootMath/EnergyGap.agda` | 14 | 32 | 0 |

## 3. 三分类（**判断**，非机器判据）

- **① 有公理登记注释（标记 ≥ 1）＝ 项目自认的桥接公理，不是缺口**（14 个）：典型注释形如
  `-- [轨道 B 物理锚定登记] … 合法公理 (genuine bridge), 不计入任何 "0 postulate" 宣称范围`
  （`Coupling/Zhonglv.agda:154`、`Structology/Aether.agda:317`）。这类须在**「0 postulate 宣称」的范围声明**里排除，
  而不是当成已证定理。
- **② 无任何标记（标记 = 0）＝ 优先审清单**（8 个）：
  `Generated/T6Verification`、`Coupling/ZhonglvPhaseSync`、`Format/CRT`、`Geometry/ProjectiveOrbit`、
  `HoTT/CRTFiberWinding`、`HoTT/DiscreteCCHM`、`RootMath/Base`、`Density/Resonance`。
  其中结构定律类（`orbit-refl/sym/trans`、`total-orbits`、`g-assoc`/`g-id-*`、`conf-*`）**若算法可判应改为证明**，
  否则应在模块头写明「为何不可证 / 待构造性闭合」（`crtSec-restricted`/`crtRet-restricted`、`stableRootConstraint` 尤其如此）。
- **③ 有洞者必须标「未验证」**：`HoTT/CRTHarmonics.agda` **同时**含 3 个 postulate 与 **1 个 `{!` 洞**；
  另有 `Topology/HighDimClosure.agda`、草稿 `src/_rt.agda` 含洞。**含洞模块不得出现在任何「全绿」清单里**。
- 附带更正：`Structology/T6.agda` 的第 4 个 postulate `φ-respects` **不在** `{-# REWRITE #-}` 中
  （规则只有 `div3k`/`mod3k`/`gf3Toℕ-A4-inv`），对外常说「T6 的 3 条规则」是准确的；
  若要为 `φ-respects` 申请 `rewrite` 豁免，须走三合取判据 + 人类裁决。

## 4. 判定器缺口（**严格性漏洞**，非本项目代码问题）

`plugins/proof-dag.mjs:799` 的 `postulateNames` 只认 `^postulate$` 缩进块式 ⇒
**单行式 `postulate foo : T` 完全不被扫描**，这类 postulate 既不进「未声明」也不进「豁免」检查（静默通过）。
库内实测 **41 处**，集中在 `Structology/Aether.agda`、`RootMath/EnergyGap.agda`、
`Geometry/{ProjectiveCore,ConformalCore}.agda`、`HoTT/CRTFiberWinding.agda`、`Coupling/TQ10.agda` 等。
台账节点：`H.toolchain.postulate-inline-gap`（附件含复现实验：块式 ⇒ 命中；单行式 ⇒ `[]`）。

> 我自己第一版审计脚本也犯了**同一类**错误（成员缩进假设），把 27 数成 24——仪器有盲区是常态，
> 所以本文数字用「两种写法都扫」的 v2 脚本 + oracle 回执，而不是 grep。

## 5. 诚实边界

1. **oracle 担保的只是「枚举完整」**（27 个模块一个不漏、名字与 REWRITE/标记/洞的计数），**不担保分类正确**；§3 的分类是判断。
2. 「标记」是 grep 关键词计数（`登记|合法公理|genuine bridge|物理锚定|不计入任何|bridge|公理`），
   **可能误命中**（例如 prose 里提到「公理」）⇒ 只能当**筛选器**，不能当结论。
3. 本文**不改变**任何模块的 postulate 状态、不动任何源码；它是清单与判据，不是修复。
4. 「0 postulate」是**逐模块**可核验的口径，不是全库口号：全库现况是 **27 个模块含 postulate**
   （其中 5 个有 REWRITE 语法依据、1 个含洞）。

## 6. 下一步（已入台账，未开工）

1. `H.postulate.audit.unmarked8`：对 §3 ② 的 8 个模块逐个定性，产出 `diagnosis`；
2. `H.postulate.audit.scope-claim`：在 `README`/`PROJECT_MEMORY.md` 的「0 postulate」表述旁写**范围声明**；
3. `H.postulate.audit.harmonics-hole`：`HoTT/CRTHarmonics.agda` 的洞先定性，再决定补证还是标「未验证」；
4. 结构定律类 postulate（`Geometry/*`、`HoTT/CRTFiberWinding`）尝试**结构化改写**（对照 `DuodecClockProperties` 的做法）。
