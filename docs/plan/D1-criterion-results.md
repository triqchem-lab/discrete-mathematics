# D1 判据实验：Gcmp 上 π₂ᵈ——oracle 面第一阶段结果

> fork e99d1dff 存体接手（2026-10-13）｜oracle 供料非证明（Agda 唯一裁决）
> 脚本：`engineering/tests/oracle_pi2_gcmp.py`（→ oracle 面 ①② 完成/③④ stub——如实）

## 一、已完成面（oracle ①②）
1. **Gcmp two-chain 模型**（V={0,1}，双向边，无自环）✓；
2. **闭走枚举**（词长 ≤5 完全性上限声明）：从 0 出发闭走词形 = 奇偶交替段；
3. **Ω2Walk 数据形**（nil2/cons2 逐字 Python 面）+ 闭 2-腔枚举。

## 二、oracle 面结果（词长 ≤5 完全性）
```
raw walks ≤5 : 3
canonical classes : 3（全单例——((0110 0110) / (0110) / ()）
```
⚠ **定性质疑（诚实）**：这里的 3 类是**词形规范面**（raw canonical dedup）**未过 Ω3Walk⁺ 商面**——
bubble-complete/fill-tri 的 **gen 关系未应用**！分水岭定理在 π₁ᵈ 面 w2∼nil 的 AHomotopy 等价
**未传导进这个 Ω2Walk 的词形枚举**（walk-level 载体 ≠ AHomotopy-class 载体）——
**③ 商面 + ④ 判定面 = 未完成**。

## 三、D1 判据当前状态（不定判）
| 问 | 状态 |
|---|---|
| π₂ᵈ(Gcmp) 商类数（过 Ω3⁺ 关系） | 🔄 **需先闭合 gen 关系面**（fill-tri 气泡→词层规约：class[] / class[w2] 是否合并——直接 testable） |
| 是否阿贝尔群 | 🔄 依赖上条 |
| A2 域反射传导结论 | 🔄 依赖上条 |

**下一步（最小闭合）**：把 Ω3⁺ 的 gen 关系面（fill-tri 型 `s∘s⁻¹` 气泡+whiskKey 缘饰）在词层闭 2-腔枚举上**重启规约**，得真商类数，再判群/阿贝尔面——预期能全闭（论域=完全的一点点扩大，
词长 ≤6 保守）。**不定判不伪造 verdict**（内容审核纪律——oracle 面非证明面）。
