# Agda `with` 纪律（2026-10-20 人类工程建议入册）

> **核心判据**：`with` 的危险不在于它是 `with`，而在于它的 **scrutinee 是否与
> goal / 索引 / 参数类型耦合**。

## 1. 决策表

| 场景 | 用 `with`？ | 替代 |
|---|---|---|
| 简单分支（scrutinee 不出现在 goal 或参数类型中）| ✅ 可以用 | — |
| scrutinee 出现在 goal 类型中 | ❌ 避免 | 顶层辅助函数（显式签名）|
| 多层嵌套 `with`（≥3 层）| ❌ 避免 | 拆成「每层一个函数」|
| scrutinee 是索引类型（`Fin n`、`Walk G a a`）| ❌ 避免 | 泛端点 + 显式等式 |
| 需要在后续 goal 引用原表达式 | ⚠️ `inspect` | `eq : f x ≡ result` ⇒ `rewrite` |
| 递归结构递减依赖 with 抽象 | ❌ 避免 | 提取辅助函数 + 显式递减 |
| `Dec` 判定分支（`with x ≟ y`）| ⚠️ | `case_of_` 或 `Dec` 消去器 |

## 2. 替代方案优先级

1. **顶层辅助函数**（显式签名）—— 最彻底，完全绕开翻译
2. **`case_of_`** —— 表达式内分支，作用域局部
3. **`inspect` + `rewrite`** —— 需要保留等式证据
4. **`Dec` 消去器**（`Dec-elim` / `⊥-elim`）
5. **直接在函数子句上匹配**（不用 `with`）

## 3. 卡点信号（一出现立即换，不试探）

| 信号 | 含义 |
|---|---|
| `CannotEliminateWithPattern` | with 抽象后的模式无法消去 |
| `UnequalTerms` 且报错位置在 `with-XXXX` | 内部抽象函数与预期目标不匹配 |
| `C-c C-,` 看到 goal 里出现 `with-XXXX` | goal 已被改写 |
| `subst` motive 端点报「`a` vs `a + b`」 | 端点被 with 抽象污染 |
| 同一处 `assoc` 方向反复报错 | 上下文被改写，方向推断失效 |

**「再看一次」是 whack-a-mole 的开始** —— 第三次不成功就换方案。

## 4. 止损协议

```
with-stop-loss :
  ① 单处 with 相关改动，3 次编译不通过 → 立即提取辅助函数
  ② 同一类 with 错误（同信号）出现 2 次 → 记入 prover_limits
  ③ 修改核心定义（Walk / AStep / reduceG 等）时 → 预先审视下游 with 的使用
```

## 5. 反向提醒：不要过度避免

纯局部计算（`with n` 后对 `ℕ` 构造子分支，无 goal 耦合）用 `with` 比提取辅助函数更简洁 ✓。
**判据始终是「scrutinee 是否与类型耦合」，不是「是否用了 with」。**

## 6. 本会话实例（证据）

**`GF3Rank.agda` 的 `elimBelow-heads`**（2026-10-20）✗：
```agda
elimBelow p ((x ∷ xs) ∷ rs) with isZeroT x
... | true  = elimBelow-heads p rs
```
报错：`UnequalTerms` —— goal 是 `allHeads (elimBelow p rs)`，但期望
`if isZeroT x then allHeads (...) else false` ✗ —— **正是信号 ②**：
`allHeads` 内部还有一次 `if isZeroT x`，`with` 只抽象了**外层**那一次 ✗。

**按本纪律的正解**：把 `allHeads` 改成显式接收首项的参数化版本（方案 1）：
```agda
allHeadsWith : ∀ (x : Trit) → Row → Matrix → Bool
```
消掉内层 `if` 之后，`with` 的抽象就与外层一致 ✓。

## 相关

- `memory/search-discipline.md`（跨库检索纪律）
- `prover_limits` 条目：`agda-with-goal-rewrite`、`agda-with-inner-if-nested`、
  `agda-assoc-direction-cubical-vs-stdlib`
