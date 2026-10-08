# rearrange 方法论：裸 Agda 加法重排证明的模板化方法

> 2026-10-10 由 Laurent→Burau→Braid 链验证（rearrange9 + sum3-comm 两处复用成功）

## 核心洞察

裸 Agda 的加法重排（无 solver）不可用「形状拼接」——每步端点必须**定义性同**。
正解 = **引理组合**（每步一个具名引理 + `sym` 方向，Agda 只查声明类型不展开体）。

## 模板：n 元重排 = 展平 + bubble + regroup (+ gather)

```
原始形 → [展平: sym (+Assoc) × k 步] → 全右形
       → [bubble1-9: 重排] → 行序全右形
       → [regroup: +Assoc × m 步] → 目标形
       → [gather × n: sym (+Assoc) ∙ cong (sym ·DistR+) × 2] → 提取公因子（可选）
```

### 关键引理（全部已绿）

| 引理 | 签名 | 用途 |
|---|---|---|
| `bubble1-9` | 9 项交换 | 3×3 转置重排 |
| `swap3` | `p+(q+r) ≡ q+(p+r)` | 相邻交换 |
| `gather` | `((a·x)+(a·y))+(a·z) ≡ a·((x+y)+z)` | 提取公因子（2 步版） |
| `+interchange` | `(a+b)+(c+d) ≡ (a+c)+(b+d)` | 4 项交叉交换（5 步） |

### gather 2 步版（比旧版 3 步更简）

```agda
gather a x y z =
      cong (_+ (a · z)) (sym (·DistR+ a x y))   -- ax+ay+az → a·(x+y)+az
  ∙ sym (·DistR+ a (x + y) z)                     -- a·(x+y)+az → a·((x+y)+z)
```

## 工程纪律（从 10+ 批迭代中提炼）

1. **每步独立 let 绑定**——Agda 可从 body 推断类型（不需要显式注解，避免括号层级错误）
2. **cong (λw→...) 包装**——内层变换在任意深度上下文中安全执行（≤1 层嵌套）
3. **proof_goals 读精确目标**——不猜形状，让 Agda 告诉你（纪律 §4.5）
4. **+Assoc 方向判定**：正向 = 右→左（深→浅），sym = 左→右（浅→深）
5. **展开时追踪包含关系**——s6/s7 教训：展开 C1 后 p3 变为内层，后续步骤的上下文必须含 p3
6. **探针先行**——在自含探针环境（无依赖破损）中迭代，绿后接入主文件
7. **show s5 RHS 精确括号**——`+Assoc A B C` 的 RHS = `(A+B)+C` 左结合（非 `A+(B+C)`）

## 应用实例

| 引理 | 模块 | 步数 | 回执 |
|---|---|---|---|
| `rearrange9` | _ProbeAssoc→BurauCubical | 25+ | `96c5f84d` |
| `sum3-comm` | Fin3 | 17 | `4a96bfd` |
| `assoc-entry` | BurauCubical | 2 步组合 | `fec3f65e` |
