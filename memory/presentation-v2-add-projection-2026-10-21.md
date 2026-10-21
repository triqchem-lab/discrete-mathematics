# 展示群定义 v2：`add` 投影闭合 G1 与 G5（2026-10-21）

**触发**：人类审核要求「修展示群的定义」（`docs/duodecimal`）。
**产出**：`docs/duodecimal/42-presentation-group-definition.md` 重写为 **v2**；
`docs/duodecimal/11-type-theory-presentation.md` 交叉引用同步。

---

## 一、v2 相对 v1 的三条**实质性修正**

### 修正 1：`rigidity-hom` + `rigidity-invol` **排除不了** `ρ` ✗

**v1 判定（错）**：G1 由 N5（自同构）+ N6（对合）「✅ 部分解决」。

**v2 反证**：

```
库内证据：DuodecClock.agda:739
  rho-is-inv : ∀ p → rho p ≡ duodec-inv p        （ρ 就是群反转，已证）

① 对合：  ρ(ρ p) = (p⁻¹)⁻¹ = p                                    ✓
② 自同构：ρ(p · q) = (p · q)⁻¹ = q⁻¹ · p⁻¹ = p⁻¹ · q⁻¹ = ρ p · ρ q
          第三步用 mixedOp-comm（DuodecClock.agda:270，DC 交换）✓
```

⇒ **`ρ` 同时满足 N5 与 N6** ⇒ 它们**没有判别力** ✗

**唯一判别式**：`add (rigidity x) ≡ add x`（N10）
- `μ (t, aᵏ) = (t, a⁻ᵏ)` ⇒ `add (μ x) = t = add x` ✓
- `ρ (t, aᵏ) = (-t, a⁻ᵏ)` ⇒ `add (ρ x) = -t ≠ t`（`t ≠ T₀` 时）✗

**⇒ 这是本体论级的判别**：`μ` 是域自同构的运输、固定素域 GF(3) ⇒ 加法分量不动；
`ρ` 把 `t ↦ -t` ⇒ 不可能是 Frobenius 的运输（见 `39-frobenius-vs-group-inversion.md`）。

### 修正 2：G1（刚性）与 G5（归零）是**同一个缺口**

v1 把二者当独立缺口，各自找补丁（G1 → N5/N6；G5 → `oblivion` 字段）✗

v2：

```
       add : A → Trit
            │
   ┌────────┼────────┐
   ▼        ▼        ▼
 ② 生成元  ⑥ 归零   ⑦ 刚性
 来源     ⊕³ 层    判别 μ vs ρ
```

- ⑥ 归零的加法层：`add-oblivion : ∀ x → (add x ⊞ add x) ⊞ add x ≡ T₀`
- ⑦ 刚性判别：`rigidity-fixes-add : ∀ x → add (rigidity x) ≡ add x`
- ② 生成元来源：`add-hom : ∀ x y → add (step x y) ≡ add x ⊞ add y`

**⇒ 三者共用 `add` 不是巧合** —— ②⑥⑦ 本来就是「生成元来源」的三个侧面：
② 有哪些生成元 / ⑥ 生成元怎么回单位 / ⑦ 哪个自同构来自生成元所在的域。

### 修正 3：四层归零里**两层已在模板**

v1 说「record 只覆盖了第三种」✗

| 归零层 | record 字段 | 状态 |
|---|---|---|
| 相位 `α⁴ = a₀` | `phase-cycle` | ✅ **已在模板** |
| 联合 `mixedOp¹² = id` | `clock-cycle` | ✅ **已在模板** |
| 加法 `⊕³ = T₀` | 无 | ❌ 缺（N9′ 补）|
| 仲吕 12 | 无 | 非代数命题，不入模板 |

⇒ G5 的真实内容只是**加法层**缺失 ✗，不是「归零整个概念缺失」✗

---

## 二、N9′ 无需新证：`tritCycle` 就是它

`DuodecClock.agda:512`（`ZeroOblivion` 字段）：
```agda
tritCycle : ∀ x → (x ⊕ x) ⊕ x ≡ T₀
```
这**逐字**就是 `add-oblivion` 在 `add = proj₁`、`add-op = _⊕_` 下的实例 ✓
⇒ DC 侧 `add-oblivion` 是**纯搬运**（引用 `ZeroOblivion.tritCycle`），零新证 ✓

同理可 `refl` 闭合的字段：
- `add-hom`：`mixedOp` 分量级定义 ⇒ `refl`
- `add-zero`：`duodec-e = (T₀ , a₀)` ⇒ `refl`
- `rigidity-fixes-add`：`mu` 只改第二分量 ⇒ `refl`

**需要新证的只剩 4 条**：`clock-min`（11 case）、`generated`（12 case）、
`rigidity-hom`、`rigidity-invol`。

---

## 三、迁移影响面（DSH `grep` 全库实测）

`Presentation` 实例**只有 3 处** + 1 个消费者：

| 文件 | 角色 | 动作 |
|---|---|---|
| `Presentation.agda:131` `dc-presentation` | **唯一本源实例** | 补 14 字段 |
| `RnDCPresentation.agda:134` | 派生（`clock = 12`）| 补字段 |
| `RnPresentation.agda:126` | ⚠ 已撤回（`clock = 4` 踩红线）| 删除/重写 |
| `PresentationTheorems.agda:62` `g-ne-unit` | 消费者（抽象 `P`）| 假设变字段 ⇒ 签名**简化** |

**⇒ 级联风险低**（3 + 1）。但 `add : A → Trit` 让模板**显式依赖 `Base.Trit`** ⇒
模板从「任意代数」收窄为「DC 族模板」—— 与 `Presentation.agda:180` 已有的自我定位
（「群式 + GF9 刚性约束的 DC 族特化模板，尚非通用模板」）**一致** ✓

**分两批**：
- 批 1（低风险，纯搬运）：加 N-add 五件套 + N3b/N7/N8 + N9′/N10，补 `dc-presentation`
- 批 2（需新证）：`clock-min` / `generated` / `rigidity-hom` / `rigidity-invol`

---

## 四、可引用的文件:行锚点

| 内容 | 锚点 |
|---|---|
| `ρ = 群反转` | `src/Sovereign/Algebra/GroupTheory/DuodecClock.agda:739` |
| DC 交换 | 同上 `:270` |
| `⊕³` 归零 | 同上 `:512` |
| `mu` 定义 | 同上 `:692` |
| `mu` 固定单位 | 同上 `:768` `zero-fixed-mu` |
| 现有 record（13 字段）| `src/Sovereign/Algebra/UniversalAlgebra/Presentation.agda:56-85` |
| 本源实例 | 同上 `:131` |
| 模板层定理 | `PresentationTheorems.agda:62` |
| DC 侧已证三条（N7/N8/N3b）| `Presentation.agda:194-206` |

---

## 五、★ 内核落地（2026-10-21 当日完成）

`src/Sovereign/Algebra/UniversalAlgebra/PresentationV2.agda`
（`record PresentationV2` **28 字段** + `dc-presentation-v2`，
`proof_compile` exit 0，回执 **`a59ea9c2…`**，0 postulate / 0 hole / 0 sorry）

**全部字段的证明来源**：

| 字段 | 证明 |
|---|---|
| `add-hom` / `add-zero` / `rigidity-fixes-add` | `refl`（`mixedOp`/`mu` 分量级）|
| `add-oblivion` | 逐字引用 `ZeroOblivion.tritCycle`（`:512`）|
| `rigidity-hom` | `cong₂ _,_ refl (rho-alphaInv-homo a b)`（`:722`，该引理与 ρ 无关）|
| `rigidity-invol` | 12 case `refl` |
| `generated` | 12 case `refl`（`g` 的幂表）|
| `clock-min` | 11 case 反驳（`Fin 12` 形式）|
| `phase-nontrivial` / `clock-phase` | `1 < 4` / `divides 3 refl` |
| N7/N8/N3b | 复用 `dc-phase-step-comm` / `dc-phase-g-comm` / `dc-clock-neq-phase` |

**★ 判别力的内核级证据**（不是散文）：
```agda
dc-rho-not-fixes-add : ∃ (λ x → dc-add (rho x) ≢ dc-add x)
dc-rho-not-fixes-add = (T₁ , a0) , dc-T₂≢T₁
```
`ρ` 满足 `rho-mixedOp`(N5) + `rho-involution`(N6)，却在 N10 上失败 ✓

**⚠ 仍未做（批 3）**：旧 `Presentation.agda`（13 字段）**未被替换**，两套并存。
替换需动 3 个实例（`dc-presentation` / `RnDCPresentation` / 撤回的 `RnPresentation`）。

## 六、诚实边界

- ✅ **设计层**：v2 的 N1–N10 + `add` 四件套在**文档层**闭合 G1–G6。
- ❌ **Agda 层**：`N1–N10` **当前一条也没有进 record** —— 不能声称「模板已修好」。
- ⚠ **G7**（无统一 record）**仍未闭合** —— 需改 `Presentation.agda` 本体。
- ⚠ 数值验证（`g^0..g^11` 覆盖 12 个、最小周期 12）是 **Python 精确枚举**，
  不是 Agda 证明；`clock-min`/`generated` 的形式化仍在批 2。
- ❌ 未断言「仲吕 12」可形式化 —— 它是谐波对齐，非代数命题。
