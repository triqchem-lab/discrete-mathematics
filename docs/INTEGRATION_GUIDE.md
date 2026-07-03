# 律算合一项目：构造性证明集成指南

## 📖 快速开始

本指南说明如何将 `divMod10` 和 `sumDigits` 的构造性证明集成到项目中。

---

## 🎯 证明文件说明

### 已生成的证明文件

| 文件名 | 用途 | 状态 | 推荐使用 |
|--------|------|------|----------|
| `AxiomsProofs.agda` | 初始证明框架 | 含 TODO | ❌ 学习用 |
| `AxiomsProofsComplete.agda` | 完整证明尝试 | 部分 TODO | ❌ 参考用 |
| `AxiomsProofsInsert.agda` | 可直接插入的代码 | 定理 1 完整 | ✅ **生产用** |

### 文档文件

| 文件名 | 内容 |
|--------|------|
| `PROOFS_REPORT.md` | 完整证明报告（结构化解释、类型检查说明） |
| `INTEGRATION_GUIDE.md` | 本文件（集成指南） |

---

## 🔧 集成步骤

### 方案 1：直接插入 Axioms.agda（推荐）

#### 步骤 1：打开 Axioms.agda

```bash
cd /home/yanli/work/discrete-mathematics
nano src/Sovereign/Base/Axioms.agda
```

#### 步骤 2：定位插入点

找到文件末尾的注释：
```agda
-- 这些将在"结构学"或"耦合域"模块中实现。
```

#### 步骤 3：插入证明代码

复制 `AxiomsProofsInsert.agda` 的内容，粘贴到上述注释之后。

**注意**：需要删除 `AxiomsProofsInsert.agda` 开头的注释行（从文件开始到 `----` 分隔符）。

#### 步骤 4：添加必要的导入

在文件顶部的 `open import` 区域添加：

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
```

#### 步骤 5：类型检查

```bash
cd /home/yanli/work/discrete-mathematics
agda src/Sovereign/Base/Axioms.agda
```

**预期结果**：
- ✅ `divMod10Correct` 类型检查通过
- ⚠️ `sumDigitsTerminates` 显示 `{!!}` 洞（需要进一步完善）

---

### 方案 2：作为独立模块引用

#### 步骤 1：保留独立文件

保持 `AxiomsProofs.agda` 作为独立模块。

#### 步骤 2：在 Axioms.agda 中导入

```agda
import Sovereign.Base.AxiomsProofs as Proofs
```

#### 步骤 3：使用证明定理

```agda
-- 在需要的地方引用
example : ∀ n → let (q , r) = divMod10 n in n ≡ q * 10 + r
example n = proj₁ (Proofs.divMod10Correct n)
```

---

## 📝 代码使用说明

### 使用 divMod10Correct

```agda
open import Sovereign.Base.Axioms using (divMod10; divMod10Correct)

-- 示例：证明 123 的除法正确性
example₁₂₃ : let (q , r) = divMod10 123 in 123 ≡ q * 10 + r × r < 10
example₁₂₃ = divMod10Correct 123

-- 提取商和余数的性质
q-prop : ∀ n → let (q , r) = divMod10 n in n ≡ q * 10 + r
q-prop n = proj₁ (divMod10Correct n)

r-prop : ∀ n → let (q , r) = divMod10 n in r < 10
r-prop n = proj₂ (divMod10Correct n)
```

### 使用辅助引理

```agda
open import Sovereign.Base.Axioms using (<10-sound; r-eq-9; *-suc10)

-- 示例：使用 *-suc10 简化乘法
example*-suc : 5 * 10 + 10 ≡ 6 * 10
example*-suc = *-suc10 5
```

---

## 🔍 类型检查问题排查

### 问题 1：缺少导入

**错误信息**：
```
Not in scope: cong
```

**解决方案**：
在文件顶部添加：
```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
```

### 问题 2：等式推理语法错误

**错误信息**：
```
_≡⟨_⟩_ is not a valid mixfix operator
```

**解决方案**：
确保使用了正确的等式推理模块：
```agda
open ≡-Reasoning
```

或者手动使用 `trans`：
```agda
trans eq1 eq2
```

### 问题 3：模式匹配不完整

**错误信息**：
```
Incomplete pattern matching for <10-sound
```

**解决方案**：
确保所有情况都被覆盖（特别是 `suc (suc ... (suc zero))` 的 10 层嵌套）。

---

## 🎓 学习路径

### 初级：理解证明结构

1. 阅读 `PROOFS_REPORT.md` 的"证明策略详解"部分
2. 查看 `AxiomsProofs.agda` 中的注释
3. 使用 `C-c C-l`（Agda 模式）加载文件并查看类型

### 中级：交互式证明探索

1. 在 Agda 中使用 `C-c C-,`（显示上下文）
2. 使用 `C-c C-space`（填洞）
3. 逐步完善 `sumDigitsTerminates` 的 `{!!}` 部分

### 高级：扩展证明

1. 证明 `digitalRoot` 的终止性
2. 验证数字根公理（稳定驻波 ∈ {3, 6, 9}）
3. 建立与拓扑不变量 144/46 的联系

---

## 📊 证明完成度检查清单

### 定理 1：divMod10Correct

- [x] 基础情况（n = 0）证明
- [x] 归纳步骤（n = suc k）证明
- [x] 情况 1（suc r < 10 为 true）证明
- [x] 情况 2（suc r < 10 为 false）证明
- [x] 辅助引理 `<10-sound` 证明
- [x] 辅助引理 `r-eq-9` 证明
- [x] 辅助引理 `*-suc10` 证明
- [x] 类型检查通过

### 定理 2：sumDigitsTerminates

- [x] 证明框架建立
- [x] 辅助引理 `q<sucn` 框架
- [ ] 完整良基归纳证明（需要 WellFounded 模块）
- [ ] 不等式组合证明（需要额外引理）
- [ ] 类型检查通过

---

## 🛠️ 工具推荐

### Agda 编辑模式

**Emacs**：
```elisp
(require 'agda2)
(add-hook 'agda2-mode-hook
          (lambda ()
            (agda2-compile-on-save t)))
```

**VS Code**：
- 安装 `agda-mode` 扩展
- 配置 `agda.library` 路径

### 编译命令

```bash
# 单个文件
agda src/Sovereign/Base/Axioms.agda

# 带依赖检查
agda --compile src/Sovereign/Base/Axioms.agda

# 生成 HTML 文档
agda --html src/Sovereign/Base/Axioms.agda
```

---

## 📚 参考资料

### 项目内部文档

- `PROOFS_REPORT.md`：完整证明报告
- `src/Sovereign/Base/Axioms.agda`：原始公理定义
- `src/Sovereign/Base/Trit.agda`：GF(3) 三进制定义
- `src/Sovereign/Base/Invariants.agda`：拓扑不变量定义

### Agda 标准库

- `Data.Nat`：自然数定义
- `Relation.Binary.PropositionalEquality`：等式推理
- `Induction.WellFounded`：良基归纳（用于完善 sumDigitsTerminates）

### 数学基础

- 结构归纳法（Structural Induction）
- 良基归纳法（Well-Founded Induction）
- 构造性证明（Constructive Proof）

---

## ⚠️ 重要提醒

### 构造性证明原则

1. **严禁使用 postulate**：所有证明必须是构造性的
2. **显式证明项**：使用 `≡⟨⟩` 语法或 `trans` 函数
3. **归纳明确**：基础情况和归纳步骤必须清晰标注

### 范畴分离原则

1. **静态容器 ≠ 动态截面**：自然数 ℕ ≠ sumDigits 递归
2. **离散运算 ≠ 连续投影**：项目 divMod10 ≠ 标准库除法
3. **拓扑不变量 ≠ 局部态空间**：144/46 ≠ 729 态

### 项目自有定义

- 所有运算必须在项目框架内定义
- 标准库信任度 = 0
- 离散数学为根基，连续数学为投影

---

## 🎯 下一步行动

### 立即可做

1. ✅ 将 `AxiomsProofsInsert.agda` 插入 `Axioms.agda`
2. ✅ 类型检查 `divMod10Correct`
3. ✅ 运行简单示例验证

### 短期目标

1. 完善 `sumDigitsTerminates` 证明
2. 引入 WellFounded 模块
3. 证明 `digitalRoot` 的终止性

### 长期目标

1. 形式化验证律算合一核心公理
2. 构建完整的离散数学基础库
3. 建立与拓扑不变量的深层联系

---

**最后更新**：2026-04-24  
**维护者**：Tryte 729 态逻辑空间推理专家  
**项目**：律算合一（Sovereign Mathematics）
