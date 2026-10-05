# 天元术证明模式——李冶《测圆海镜》的 Agda 对应

> **日期**: 2026-10-04
> **性质**: 证明模式规范——筹算 Agda 化第三实例（非状态机，是证明方法论）
> **来源**: 李冶《测圆海镜》(1248) + 四库馆臣按语"立天元一于左上之语...其用不同而法则无二也"
> **配套**: 35-suanchou-agda-manual.md（操作手册）+ DayanState.agda（第一实例）+ KaiFang.agda（第二实例）

---

## 一、天元术不是状态机

| 维度 | 大衍求一术（状态机） | 天元术（证明模式） |
|---|---|---|
| **本质** | 可执行算法（布局→操作→终止→读数） | 推理方法（设未知→推演→消元） |
| **Agda 对应** | `record + step + termination + projection` | `Σ-witness + ≡-Reasoning + subst` |
| **筹算范式** | SuanChou record 适用 | SuanChou record **不适用**（无"布局/盘面"） |
| **验证** | `refl`（算筹验算） | 证明（归纳/推理） |

**天元术是"证明的方法论"，不是"计算的算法"。** 它不能编码为 `SuanChou record`——强行编码会犯"把结构定理当状态机"的范畴错误。

---

## 二、天元术三步 → Agda 对应

### 步骤一：立天元一（设未知量）

| 天元术操作 | Agda 对应 | 适用条件 |
|---|---|---|
| **存在量词**（∃x, P(x)） | `Σ A (λ x → P x)` | 未知量是 witness |
| **全称引入**（∀x, P(x) → Q(x)） | `(x : A) → P x → Q x` | 未知量是任意元 |
| **中间变量**（令 x = ...） | `let x = ... in ...` | 未知量是计算中间值 |

### 步骤二：推演（从已知条件推导关系）

| 天元术操作 | Agda 对应 | 工具 |
|---|---|---|
| **等式推演**（a = b = c = ...） | `≡-Reasoning` 链 | `begin ... ≡⟨⟩ ... ∎` |
| **代数运算**（乘除消去） | `cong` / `cong₂` | 函数应用保持等式 |
| **代入**（用条件替换） | `subst` / `transport` | 等式替换 |

### 步骤三：消元（消去未知量得结果）

| 天元术操作 | Agda 对应 | 适用条件 |
|---|---|---|
| **替换消元**（用等式替换） | `subst` / pattern match on refl | 有定义性等式 |
| **witness 提取**（从 Σ 提取） | `proj₁` / `proj₂` | 未知量在 Σ 中 |
| **代数化简**（符号运算化简） | `rewrite` / `with` | 有重写规则 |

---

## 三、天元术证明模板

```agda
-- 天元术证明模板（三步）

-- 第一步：立天元一
--   根据具体术的形态选择引入方式：
my-proof : (input : ℕ) → SomeProp input
my-proof input =
  let witness = compute-witness input in     -- 立天元一（中间变量形态）
  let relation = derive-relation input witness in  -- 推演（条件→关系）
  let result = eliminate relation in          -- 消元（关系→结果）
  final-proof result

-- 或 Σ 形态：
my-proof-Σ : Σ ℕ (λ x → SomeProp x)
my-proof-Σ = (witness-value , proof-that-prop-holds)  -- 立天元一 + 验证

-- 或 Π 形态：
my-proof-Π : ∀ (x : ℕ) → P x → Q x
my-proof-Π x px = ...  -- 推演：从 P(x) 推导 Q(x)
```

---

## 四、实例：天元术在律算线中的应用

### SunyiBase 的 SOVEREIGN_LCM 推导就是天元术的应用

```
第一步：立天元一
  设"闭合比"为未知量 r（天元）
  实际操作：引入 CLOSURE_NUM 和 CLOSURE_DEN

第二步：推演
  r = 黄钟/仲吕
    = 3⁴ / (2¹⁶/3⁷)
    = 3⁴ × 3⁷ / 2¹⁶
    = 3¹¹ / 2¹⁶
  （每步用 ⊕-Reasoning 链和 Frac 运算）

第三步：消元
  从 r = 3¹¹/2¹⁶ 读出分子和分母：
  SOVEREIGN_LCM = 3¹¹ × 2¹⁶ = 177147 × 65536 = 11609505792
```

**这不是事后解释——SunyiBase 的代码结构确实是按天元术三步组织的。**

---

## 五、筹算 Agda 化四实例总结

| 实例 | 术 | 类型 | 范式 | 状态 |
|---|---|---|---|---|
| 第一实例 | 大衍求一术 | 状态机 | SuanChou record（布局/操作/终止/读数） | ✅ DayanState |
| 第二实例 | 开方术 | 状态机 | PellState record（双算筹递推） | ✅ KaiFang |
| **第三实例** | **天元术** | **证明模式** | **Σ-witness + ≡-Reasoning + subst** | ✅ **本文档** |
| 第四实例 | 正负术 | 数据类型 | `data 正负 = 正 ℕ \| 负 ℕ` | 待建 |
| 第五实例 | 方程术 | 状态机 | 矩阵行变换（Gaussian 消元原型） | 待建 |
| （律算线） | 三分损益术 | 纯函数 | sun/yi + Frac | ✅ SunyiBase |

**天元术的关键贡献**：它定义了**非状态机型"术"的 Agda 对应**——证明模式（方法论）而非数据类型（算法）。
