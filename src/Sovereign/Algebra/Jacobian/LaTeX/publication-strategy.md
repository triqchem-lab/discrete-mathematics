# 发表策略

## 拆分方案

| # | 类型 | 目标期刊 | 内容 | 状态 |
|---|------|---------|------|------|
| 1 | **通讯 (2-3页)** | 任意综合期刊的 Letters 栏目 | 定理陈述 + 证明概略 + 验证状态 | `communication.tex` |
| 2 | **完整论文 (15-20页)** | J. Automated Reasoning 或 MSCS | 全部证明链 + 三重防火墙 + 反例分析 | `paper.tex`（已有草稿） |
| 3 | **验证报告 (5-8页)** | J. Formalized Reasoning | Agda 形式化方法论 + 模块审计 + 0-postulate 达成 | 待写 |

## 通讯优先（抢优先权）

`communication.tex` — 2 页，定理 + 证明概略 + "全部 16 模块, 0 postulate, 可独立验证"

投 `arXiv` + 任何 Letters 栏目（如 `Amer. Math. Monthly` 或 `Math. Intelligencer`）

## 完整论文（展开论证）

`paper.tex` 已有 5 页草稿，需要：
1. 扩充证明链的详细推导
2. 三重防火墙的形式化陈述
3. Alpöge 反例的判决（沿 RFC-DJC-1 标准）
4. 完整依赖图

## 不投的期刊

- ❌ Annals of Mathematics — 不接受形式化验证为主要证据
- ❌ Inventiones — 同上
- ❌ 任何要求传统手写证明的期刊 — Agda 代码就是证明

## 可投的期刊

- ✅ J. Automated Reasoning — 形式化验证的黄金期刊
- ✅ Mathematical Structures in Computer Science — 接受 Agda/Coq 证明
- ✅ J. Formalized Reasoning — 专门的形式化验证期刊
- ✅ arXiv — 预印本，无门槛，优先权确立
