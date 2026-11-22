# Weil 刚性路径可行性审计：九项 Yes/No 清单

> 审计日期：2026-11-22。背景：Alpöge RH/GRH Lean 证明大概率已获社区背书确认。
> 本审计把「在 Agda 仓库实现 Weil 刚性路径」拆为九个二进制问题逐项取证，
> **只做静态扫描，未修改任何代码**。每条给 `[Yes/No/Partial]` + 文件路径与行号。
> 前置警告：清单中有两个前提与本库实测不符，已在对应条目标注。

---

## 一、基础设施与本体基座

### 1. GF(9)/GF(3ⁿ) 与 Frobenius 对合性 —— **Yes（超预期）**

| 子项 | 结论 | 证据 |
|---|---|---|
| GF(9) 定义 | Yes | `Algebra/FieldTower/GF9.agda`（1104 行，`GF9 = GF(3)[x]/(x²+1)`）；同目录另有 GF27(1486 行)/GF81(1546 行)/GF243/GF729/GF3K——**GF(3^n) 塔全谱已存在，共 36 件 13,584 行** |
| σ(x)=x³ 形式化 | Yes | `Algebra/FieldTower/GF9AlgebraicChain.agda:220-228`：σ = galoisConjugate（a+bα ↦ a−bα，即 x ↦ x³），`FrobeniusProofs` record 含两字段 |
| σ² = id 对合性**证明** | Yes | `GF9AlgebraicChain.agda:225-230`：`l5-proofs : FrobeniusProofs`，`involutive : ∀ x → σ(σ x) ≡ x` 是**已证字段**，非注释 |
| 轨道结构 | Yes | `Algebra/FieldTower/FrobeniusOrbit.agda`：σ 作用在 GF(9) 上的轨道/周期=2/`Gal(GF(9)/GF(3)) ≅ C₂` 全套 |

### 2. Eisenstein 整数环 ℤ[ω] —— **Yes（三项全齐）**

| 子项 | 结论 | 证据 |
|---|---|---|
| ℤ[ω] 定义 | Yes | `Foundation/Eisenstein.agda:39` `record Eisenstein`；另 `Algebra/FieldTower/Zomega.agda`（§7 有 Gal 对合环自同构） |
| 范数映射 | Yes | `Eisenstein.agda:646-647` `normᵉ (eis a b) = a*a − a*b + b*b`——正是 a²−ab+b² |
| 范数乘法同态 | Yes | `Eisenstein.agda:906-930` `norm-mul : ∀ x y → normᵉ(x *ᵉ y) ≡ normᵉ x * normᵉ y`，经 `norm-form`+`conjᵉ-mul` 链式全构造证明（0 postulate） |
| 附加资产 | — | `conj-ω≡ω²`(L115)、`conjᵉ-mul`(L707)、`norm-form`(L650) 皆已证 |

### 3. 模运算与整数算术 —— **Yes（但有边界）**

| 子项 | 结论 | 证据 |
|---|---|---|
| Stdlib 使用面 | Yes | 143 个文件 import `Data.Integer`；`Data.Nat`/`Data.Nat.Properties` 同级别覆盖 |
| `3s²=36` 类无解引理 | **Partial** | 现成「平方×3 无解」专用引理**不存在**。可复用件：`Algebra/NumberTheory/Diophantine.agda`（435 行，模 n 判定核心 `∃Fin?` 判定程序 yes/no 构造健全）、`Divisibility.agda`（120 行，∣-∸ 等）、`Data.Integer.Properties`（stdlib 自带）。**判定程序路线可行但需写薄胶水**——把 `3s²=4·3^k` 化为 mod-3/模幂穷举 |

---

## 二、核心定理移植可行性（Lean 4 → Agda）

### 4. 反例 `no_norm_t0_even : ¬∃s, 3s² = 4·3^(2k)` 的迁移 —— **Partial（可行，有现成范式）**

**最合适的工具组合**（按优先级）：

1. **`Diophantine.agda` 的判定程序范式**——`∃Fin? : Dec ∃` 已示范「yes 携 witness / no 携反驳」的构造健全否定。把 `3s² = 4·3^(2k)` 对固定 k 化成模 m 同余判定即可继承此范式。
2. **`Sqrt2Irrational.agda` 的归谬法范式**——`Application/Problems/Sqrt2/Sqrt2Irrational.agda` 已用 mod-3 论证（无理性的 3-adic 证明），其「假设整数解 → 平方项 mod 3 矛盾」结构与 `no_norm_t0_even` 同构，**直接抄这个骨架**。
3. **模式匹配 + refl 收尾**——本库 0-postulate 风格的标准做法：对 `s : ℤ` 拆 `+n / -[1+ n]` 两分支、对 n 拆 `0/1/2` mod-3 残类，最后 `Data.Integer.Properties` 的非负/反对称引理封口。

**缺口**：无现成「3 ∣ s² → 3 ∣ s」引理（Sqrt2 有 2-adic 版），需按同构新写约 30-50 行。

### 5. 范数 N(α)=q 的纯代数改写（避开 Complex/sqrt）—— **Yes（已经就是这么写的）**

- `Application/Problems/RH/WeilRigidity.agda` 全文 **0 处** `Complex`/`sqrt`/`abs`（已 grep 验证）。
- 现有定理即纯代数形式：`norm-product-E1 : alpha-E1 *ᵉ conjᵉ alpha-E1 ≡ 3ᵉ`（L147-148，refl）、`trace-sum-E1`（L134）。
- Lean 版 `Im·(2Re−t)=0` 的逼出结构在 Agda 侧的对应物是 `trace-sum` + `norm-product` 二元组（α+conj(α)=t 与 α·conj(α)=q 联立）——**这个改写已经完成，无需迁移**。

---

## 三、Postulate 污染与构造性纯净度

### 6. 「27 个 postulate 模块」—— **No（前提不成立：实测仅 1 个）**

- 全库顶层 `postulate` 声明：**仅 `Synthesis/Model/DiscreteCCHM.agda` 两处**（L117 `discreteGlue`、L122 `discreteCanonicity`），且都带 `[postulate 登记 2026-10-11] kind:**gap**` 的立界注释。
- 「27」是把注释里的「0 postulate」字样误计（842 个文件含 "postulate" 字样，绝大多数是声明**零**公理）。
- **污染路径核查**：`WeilRigidity.agda` 的 import 链（`Data.*` + `Foundation/Eisenstein`）与 `Eisenstein.agda` 的 import 链（`Data.*` + stdlib Properties）**均不含** `Synthesis/Model`，DiscreteCCHM 在 L3/Synthesis 深处，RH 轨道在 L4——依赖方向单向，**无污染**。✅ 0-postulate 核心链干净。

### 7. 终止性检查（Waterhouse 迹清单）—— **Yes（有先例与规范）**

- 库内 `{-# TERMINATING #-}` 使用：仅 3 处（`Synthesis/Homotopy/C5LInvariance.agda:1506,1694`、`Infrastructure/Projection/Decimal/Axioms.agda:49`），每处都附「真子term依据」注释——**有纪律的例外，不是惯例**。
- Waterhouse 迹清单按 n 奇偶分支，是**对 n 的结构递归**（同 `t-rec` 模式，`BSD_L3.agda:31-34` 对 `suc (suc n)` 递降两层），Agda 能自动过终止检查，**不需要 TERMINATING 也不需要 Well-founded**。
- 若做无限分类（全素数扫描）则需 `Foundation/WellFounded.agda`（已存在）的 Acc 通道——但四步走范围内不需要。

---

## 四、缺口标记与目录规划

### 8. 几何缺口定位 —— **Partial（比预期多，但深度浅）**

| 概念 | 存在？ | 性质 |
|---|---|---|
| 椭圆曲线 | Yes（浅） | `Application/Problems/BSD/BSD.agda:34`（GF(3) 上 y²=x³+ax+b **穷举点计数**）、`AlgGeomBridge.agda:136`（E: y²=x³+x+1 点计数）——**计算实例，无群律/形式化定义** |
| 自同态环 | **No** | 全库 0 命中 |
| 超奇异 | **No** | 全库 0 命中 |
| Waterhouse 分类 | **No** | 全库 0 命中 |

`Gaps.agda` 新建建议：**可行且必要**。书写风格参照 `DiscreteCCHM.agda:113-122` 的立界格式：

```agda
-- [postulate 登记 YYYY-MM-DD] kind:**gap**（真缺口——Waterhouse 分类表）
--   依据：有限域全迹分类需引理集尚不存在；**gap 不得 proven**——节点须标 blocked/立界。
```

### 9. 文档与四步走冲突 —— **No 冲突（但需补一行衔接）**

- 现有 `Sovereign-RH-Constructive-Path.md` 的阶段一已规划「把 weil-norm 提升为一般命题」，与四步走（Eisenstein → Waterhouse → WeilRigidity → Gaps）**方向一致**。
- 唯一需衔接处：现有文档未提 Waterhouse 分类与 `Gaps.agda` 落点（grep 0 命中）。四步走是阶段一的**细化施工顺序**，不推翻任何现有结论——包括「判别式 −3 写死是阶段一真实难点」的判断（Waterhouse 路线恰好**绕开** ℤ[√−d] 类数问题：迹清单只用到 ℤ 上的整除性，不换环）。
- `Eisenstein.agda`/`WeilRigidity.agda` **已存在**（Foundation/ 与 Problems/RH/ 下），四步走中对应步骤实为「扩充」而非「新建」——清单原表述「新建」不成立。

---

## 总表

| # | 检查项 | 结论 |
|---|---|---|
| 1 | GF(9)/GF(3ⁿ) + σ + σ²=id | **Yes**（36 件 13,584 行塔 + 对合已证） |
| 2 | ℤ[ω] + norm + 乘法性 | **Yes**（三项全齐，norm-mul 已证） |
| 3 | 整数算术工具 | **Yes**（143 文件；专用引理 Partial 需薄胶水） |
| 4 | Lean 反例迁移 | **Partial**（Sqrt2/Diophantine 范式可抄，缺 3∣s²→3∣s 引理约 30-50 行） |
| 5 | 纯代数范数改写 | **Yes**（WeilRigidity 已是 0 Complex/sqrt） |
| 6 | 27 个 postulate 污染 | **No 前提不成立**（实测 1 个，且不在依赖链上） |
| 7 | 终止性 | **Yes**（结构递归即可，t-rec 同模式先例） |
| 8 | 椭圆曲线/超奇异 | **Partial**（点计数有、End(Waterhouse) 三概念 0 命中；Gaps.agda 建议采纳） |
| 9 | 文档冲突 | **No 冲突**（需补 Waterhouse/Gaps 衔接行） |

**一句话**：基础设施三项（1/2/5）**超预期齐全**——Eisenstein 范数乘法性、Frobenius 对合、纯代数范数全部已证；真正要新写的是 4（反例引理）与 8（Waterhouse 分类 + Gaps.agda），且清单第 6 条的「27 个 postulate」是误报。

---

## 创建日期

2026-11-22
