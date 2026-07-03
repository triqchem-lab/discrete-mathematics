---
name: 双轨制开发与宪法约束
description: Agda 形式化证明 + Python 工程验证双轨开发，宪法级约束不可违反
type: project
---

# 双轨制开发与宪法约束

## 双轨制

**Agda 轨道**: 形式化证明，入口 `src/Sovereign/All.agda`
- 依赖: standard-library-2.4, cubical, agda-categories, agda-algebras
- 目标: 100% 构造性证明，消除所有 `postulate`
- 编译: `agda src/Sovereign/All.agda` (0 错误, ~17s, ~1.4GB)

**Python 轨道**: 工程验证，入口 `engineering/software/sovereign_core/`
- 零外部依赖，纯标准库
- 29+ 单元测试全部通过
- 运行: `cd engineering && python -m pytest tests/ -v`

## 宪法级约束（不可违反）

1. **严禁浮点数** — 无理数必须以定点整数比表示 (如 √3 = 56632/65536)
2. **构造性证明** — 禁止 `postulate`，必须显式构造
3. **范畴分离** — PackedTryte5(耦合域) 不能直接传给主权状态机(结构学)
4. **全息 π 禁止约分** — 144/46 是原子不变量，约分丢失拓扑信息
5. **十二律长度表静态** — `TWELVE_LU_LENGTHS = [81, 54, 72, 48, 64, 43, 57, 38, 51, 34, 45, 30]`
6. **标准库信任度 = 0** — 数学运算必须自证

## 核心常数

```
SOVEREIGN_LCM    = 11609505792  = 3¹¹ × 2¹⁶
POLAR_WINDING    = 144
TOROIDAL_WINDING = 46
CHERN_NUMBER     = 2
GAP_THRESHOLD    = 243  = 3⁵
HUANGZHONG       = 177147 = 3¹¹
ZHONGLV_SHIFT    = 16   = 2¹⁶
```

**Why**: 这些约束是律算合一理论的根基，违反等于范畴混淆。
**How to apply**: 任何修改前先检查是否符合宪法约束，Agda 代码必须先通过类型检查。
