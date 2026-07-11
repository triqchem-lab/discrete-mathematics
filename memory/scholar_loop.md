---
name: Scholar Loop 自主研究框架
description: 博士级 ML 实验循环，位于 /data/training/cli/scholar-loop，8 agent + 预算漏斗
type: reference
---

# Scholar Loop

**路径**: `/data/training/cli/scholar-loop`
**Skill**: `scholar-loop`（Qwen Code 可调用）
**上游**: https://github.com/renee-jia/scholar-loop

自主多智能体 AI 研究框架：读论文 → 找空白 → 运行真实验 → 反思 → 写作并自审。

## 8 个 Agent

| Agent | 职责 |
|-------|------|
| Director | 读 ledger + 文献趋势 → 设定方向/预算 |
| Lit Scout | arXiv + OpenAlex 检索 → 结构化引用 |
| Reasoner | 约束 + 文献 + 历史教训 → 提出实验 |
| Debate Panel | 三人投票：值得烧 GPU？ |
| Funnel | smoke → verify → full 三级筛选 |
| Runner | 运行真实 PyTorch 实验 |
| Reflector | 结果 → 衰减技能库中的教训 |
| Advisor | PROCEED · REFINE · PIVOT |

## 为什么关联

律算合一项目（离散数学/GF(3)理论）需要定量实验验证。Scholar Loop 可用于：
- 自动搜索 GF(3) 计算的最优参数
- 验证十二律损益链的数值性质
- 石英声子实验（已有 quartz-phonon-plasma profile）
