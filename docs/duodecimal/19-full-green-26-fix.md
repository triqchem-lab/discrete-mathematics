# 全库 511 全绿专项 — 26 失败模块修复清单与进度

> 状态: 2026-09-07 建立. 目标: 26 个 stdlib 2.4 迁移/草稿问题模块逐个修通到全库 511 独立编译全绿.

## 总体判断 (诚实)

26 个失败模块分两类:
1. **stdlib 2.4 迁移断裂** (多数): `_mod_` 返回 Fin 语义变 / `fromℕ` 无界 / import opt-in / Vec.sum 只 ℕ / Fin 算术 roundtrip.
2. **未完成草稿** (相当多): 假 refl / 引用未定义符号 / 接口引用未定义类型 / 数学建模未定型.

每模块平均需 1-3 轮深入 (非纯 import). 部分需重建模或补数学定义.

## 进度清单

| # | 模块 | 状态 | 卡点/进展 |
|---|------|------|----------|
| 1 | Coding/PigeonholeStandard | ✅ 全绿 (93bec67) | 缺 ℕ/suc import; Inj/Surj 隐参; SeparatedRecursion 签名对齐 jac_Pigeonhole |
| 2 | HoTT/ChernConservation | 🔶 部分 (7027ae5) | ✅ rotLeft 提顶层/zsum(ℤ和)/diffInvariant 真证(shuffle4+neg-distrib); ❌ curvatureVectorInvariant (全局平移差分不变) 需 rotLeft-map+zipWith-map+diffInv 提升 ~30 行 |
| 3 | Quantum/Entanglement | 🔶 部分 (7044faa) | ✅ T≢T0 提顶层/⊕括号/proj5/Bell state-E 统一/真违反设置; ❌ classical-bound 假定理(36 反例)需裁剪, Bell 语义重建模收尾 |
| 4 | Structology/LuCellGrid | 🔶 部分 (7044faa) | ✅ mod→%/import/isId/gridRow/gridCol/mkGridPoint fromℕ<+界证; ❌ shift* 的 toℕ(fromℕ<) roundtrip mod-helper (需 fromℕ<-toℕ REWRITE 或重写) |
| 5-26 | 其余 22 | 🔴 未动 | 抽样: WuXingTransition(缺 polygonSides), TorusClosure(接口引用未定义 FrobeniusVisible/GlobalMatrix), DiscreteCalculus(_mod_ 同 LuCellGrid), ElectricalTopology(FileNotFound→依赖 LuCellGrid?) 等 |

## 已知修复模式 (供后续)

- `_mod_` (stdlib 2.4 返回 Fin) → `_%_` (Data.Nat.Base 返回 ℕ), 需 NonZero 实例
- `fromℕ (expr)` → `fromℕ< (m%n<n expr 12)` 或界证; div 界用 `/-monoˡ-≤`
- `toℕ (fromℕ< p)` 不归约 → 需 Data.Fin.Properties 的 `fromℕ<-toℕ` (或 REWRITE)
- `Vec.sum` 只对 ℕ → ℤ 求和用 foldr
- 假 refl (整数恒等式) → shuffle4/neg-distrib 真证
- 引用不存在符号 (rho-inverse/A4-toℕ/bell-calc) → 找绿库真实名或本地补
- 缺 import (stdlib 2.4 opt-in) → 补 using

## 验证

`./engineering/check_all_modules.sh` 全库独立编译扫描 (485/511 基线).
