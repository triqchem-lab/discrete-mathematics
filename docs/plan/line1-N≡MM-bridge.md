# 线1 N≡MM Bridge 详细计划（证明形状图——每步 LHS/RHS 字面）

> 状态：✅ **已完成并核实**（2026-10-11 复核：proof_compile EXIT=0 + 双节点回执挂账）
> 台账映射：`P3.2-hensel-uniqueness-pure`（`7bad59be`）｜`P3.2-hensel-uniqueness-qge2`（`efc5efdd`）

## 目标与成功标准
唯一目标：unique-root₃-same q≥2 分支闭合 → proof_compile EXIT=0 + 台账 update
串行模式：本批只做线1（不启动线2/线3）

## fable5 开工四项
### 1. 分解（子任务 + 依赖 + 验证点）
| 子任务 | 依赖 | 验证点 |
|---|---|---|
| 1.1 N≤MM 构造 | 无 | ≤-trans 形过类型关 |
| 1.2 MM≤N 构造 | 无 | *-identityʳ 桥过类型关 |
| 1.3 ≤-antisym 组合 | 1.1 + 1.2 | N≡MM-form 过类型关 |
| 1.4 q≥2 分支闭合 | 1.3 | proof_compile EXIT=0 |

### 2. 拓扑扫描（级联风险）
HenselCRTUniqueness（叶子）——HenselCRTSynth/ModExtract 只依赖 SovereignLCMRoots → 零级联 ✓
修改安全（不触碰 Base/Trit 等 300+ 依赖模块）

### 3. 多路径（两条路径 + 复杂度/风险）
路径 A（选此）：≤-antisym + *-identityʳ 桥
```agda
-- 目标：SOVEREIGN_LCM ≡ M + M（未来态锁定）
-- 其中 M = pow3 11 * pow2 15（literal 形）
N≤MM : SOVEREIGN_LCM ≤ M + M
N≤MM = ≤-reflexive (trans (refl {x = SOVEREIGN_LCM}) N≡MM-form)
  where
    N≡MM-form : SOVEREIGN_LCM ≡ M + M
    N≡MM-form = trans (sym (cong (M +_) (*-identityʳ M))) (refl {x = 2 * M})
    -- 步骤 1a: 2·M ≡ M + M·1（defeq literal 2 ✓）  1b: M + M·1 ≡ M + M（*-identityʳ）
    -- 1c: sym → M + M ≡ M + M·1    1d: refl {x = 2·M}（defeq ✓）
MM≤N : M + M ≤ SOVEREIGN_LCM
MM≤N = ≤-reflexive (sym N≡MM-form)
N≡MM : SOVEREIGN_LCM ≡ M + M
N≡MM = ≤-antisym N≤MM MM≤N
```
复杂度：~10 行｜风险：低（*-identityʳ 已证明引理——附录 2 规则）｜符号 safe：✓
备选路径 B（留备）：陈述改造（x ≡ 1 + t·M mod-extract 提取）｜~30 行｜风险：中

### 4. 落台账（proof_dag 节点）
现有节点：P3.2-hensel-uniqueness-pure（WIP 主节点）｜本批 update：q≥2 分支闭合 → proven

## 证明策略
策略 E（未来态锁定）：锚定 SOVEREIGN_LCM ≡ M + M 推导｜附录 2（*-identityʳ 替代 M·1 归约）｜trans ≤3 层

## 执行顺序（批 J）
批 J.1：N≤MM 构造——验证点：过类型关｜批 J.2：MM≤N 构造——过类型关｜批 J.3：≤-antisym 组合 + q≥2 闭合——proof_compile EXIT=0

## 假设与风险
假设：*-identityʳ + ≤-reflexive（探针级 safe）｜风险：M·1/2·M 归约 defeq 卡 → 显式桥绕开

## 验证点（最终）
proof_compile EXIT=0（HenselCRTUniqueness）｜unique-root₃-same 台账 update（proven）

---
## 附：核实状态（2026-10-11 复核对账）
| 计划步骤 | 代码实况 | 判定 |
|---|---|---|
| 1.1/1.2 N≤MM/MM≤N | 实作更简：并入 q≥2 矛盾收口（`≤-<-trans N≤x x<N` → `⊥-elim (n≮n …)`）+ `M+M≡A+A`/`A+A≡N` 等式链 | ✅ 超出 |
| 1.3 N≡MM | `:458 N≡MM = sym (trans M+M≡A+A A+A≡N)`——≤-antisym 路径精化为纯等式链 | ✅ 精化 |
| 1.4 q≥2 闭合 | `unique-root₃-same :437` 三分派全闭（q=0→root₁/q=1→root₃/q≥2→矛盾）| ✅ EXIT=0 |
| 台账 | 双节点 proven + 回执挂账（`7bad59be`/`efc5efdd`——锚哈希与归档记录逐字一致）| ✅ |
**结论：三条件全满足；两处偏差均为改善（路径精化/粒度合并），无遗漏。**
