# 展示群规约缺口：机器判定的边界（探针矩阵）

**日期**: 2026-09-14　**状态**: 全部实测（Agda 2.9.0-nightly，本机 `/home/yanli/.local/bin/agda`）
**主张**: 「Agda 的归一化器只有 β/δ/ι/η，没有展示群关系规约；δ³=id 等是命题相等，不是定义相等」

本目录把**主张的量**测出来：把「归一化器到哪儿为止」「REWRITE 能不能救」变成一组可复跑的 exit 码。

## 复跑命令（在仓库根）

```
for m in GapProbe1 GapProbe2b GapProbe3 GapProbe3b GapProbe7 GapProbe9 GapProbe10; do
  agda --guardedness -i docs/techniques/presentation-reduction-gap \
       docs/techniques/presentation-reduction-gap/$m.agda; echo "$m rc=$?"
done
```

## 矩阵（实测）

| 探针 | 内容 | 结果 | 说明 |
|---|---|---|---|
| `GapProbe1` | 已定义生成元 `step` 的**闭合实例**（`step³ t0 ≡ t0`）用 `refl` | **rc=0 接受** | 归一化器对**闭合项**工作：β/δ/ι 把实例算到范式 |
| `GapProbe3b` | **具体** record 实例（投影 `Pres.d inst` 归约到 `step`） | **rc=0 接受** | 同上；这正是「穷举 12 case」路径的来源 |
| `GapProbe2b` | **普遍定律**（变量 `x`）用 `λ x → refl`，无 REWRITE | **rc=42 `UnequalTerms`**：`step (step (step x))` 与 `x` 不等 | **主张的直接机器证据**：变量上不归约 ⇒ 定律必须显式证明（case 分解 or 代数链） |
| `GapProbe3` | **抽象实例**（`Pres.d p`，`p` 是变量）用 `refl` | **rc=42 `UnequalTerms`** | 展示群的**抽象形态**（生成元是记录字段）连实例都不归约 |
| `GapProbe4` | 对 **postulate** 生成元声明 `{-# REWRITE law #-}` | **rc=0**（规则被接受） | ⚠ 与常见说法相反：抽象生成元**可以**声明 REWRITE |
| `GapProbe10` | 同上 + 用 `λ x → refl` 证普遍定律 | **rc=0**（**规则生效**） | ⚠ 关键：**REWRITE 在抽象（postulate）生成元上照样生效** |
| `GapProbe9` | 对**已定义**生成元声明 REWRITE + `λ x → refl` | **rc=0** | 两条路都能「自动规约」，代价见下 |
| `GapProbe7` | 控制实验：`∀ x → x ≡ x` 用裸 `refl` | **rc=42 `UnequalTypes`** | 提醒：**裸 `refl` 对显式 Π 型是写法问题**，与规约无关（本矩阵最初误把它当成规约失败，已更正） |

## 结论（精确化）

1. **主张成立**：普遍量化定律（变量）**不能**靠归一化器闭合（`GapProbe2b`）；抽象形态（记录字段生成元）连实例都不闭合（`GapProbe3`）。
2. **但「抽象形态不能 REWRITE」不成立**（`GapProbe4`/`GapProbe10`）：Agda **允许并执行**在 postulate 生成元上的重写规则。
3. ⇒ 本库「保留 δ、φ 为独立字段、**不**声明 δ³/φ⁴/δφ 为 REWRITE」是**立场（不商化）**，不是技术不可能：
   - 声明 REWRITE ⇒ 自动规约 ✓，但关系从**命题相等**降为**定义相等** ⇒ 生成元的三阶/四阶结构被**商掉**；
   - 不声明 ⇒ 结构保留 ✓，但每处使用都必须 `trans`/`cong`/`subst` **手工搬运**。
4. **pair-popping 是对 (3) 第二种代价的手工补偿**：不改变「缺统一规约」的事实，只把逐 case 穷举换成「代数律重排 + 归一化器收口」（本库 12/729/6561 三处实例已改造）。

## 未验证（不得当成已证）

- **合流性（confluence）**：本目录**没有**探针涉及两条规则冲突的情形 ⇒ 未验证。
- **终止性**：`GapProbe6`（RHS 更大的规则）**没有**表现出死循环（该目标里规则未触发）⇒ 「Agda 不检查重写终止性」**未被本目录证实**，只是文献口径。
