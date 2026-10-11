# 线3 disp2-respects 证明形状图（每步 LHS/RHS 字面）

> 状态：✅ **已完成**（2026-10-11 形状图展开 → 执行首编即绿）｜回执 `e6a1250b`
> 台账映射：`disp2-respects`（proven）｜定位：线2 代码注「泛化 harm（递归调用需要）」= 本件预留接线口

## 目标与成功标准
唯一目标：disp2 在 A-homotopy 等价下不变 → proof_compile EXIT=0 + disp2-respects 台账 update ✓

## 证明形状图（路径 A——归纳 + gen 直调）
```agda
disp2-respects : (W) → ∀ {w1 w2} → AHomotopy (G W) w1 w2
  → (harm : ∀ a b c → wt a b *A wt b c ≡ wt a c) → disp2 W w1 ≡ disp2 W w2
-- 主件四案（AHomotopy 构造子穷尽 4 ≤ 27）：
--   refl' w        = refl                    LHS: disp2 W w   RHS: disp2 W w   [defeq]
--   symm h         = sym (IH h)              LHS: disp2 W w2  RHS: disp2 W w1  [递归①]
--   trans' h1 h2   = trans (IH h1) (IH h2)   LHS: disp2 W w1 →disp2 W w2→ w3   [递归②③]
--   gen s          = step-respects s harm    LHS: disp2 W w1  RHS: disp2 W w2  [归约]
-- 辅件二案（AStep）：
--   slide  p b e1 e2 e3 = disp2-slide-gen W p b e1 e2 e3 harm   [线2 泛化件直调]
--   expand p b e1 e2 e3 = sym (disp2-slide-gen …)               [sym]
```
**关键约束**：harm 必须**全局 gen 形**（∀ a b c）——symm/trans' 的 IH 间传递需要；
这正是线2 留 `disp2-slide-gen`（泛化 harm）的原因——三线形状自洽。
**复杂度**：~20 行（+34 含分节注释）｜**风险：低**（首编即绿）

## 验证点（最终，全达成）
① PostnikovTruncation EXIT=0（`e6a1250b`，2.6s）② _PL3chk 双核对（refl 级 wt≡1 实例 + 定理调用双通道）③ 零洞零 postulate
