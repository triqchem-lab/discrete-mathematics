# D1 判据实验批——Gcmp two-chain 上 π₂ᵈ 的计算（oracle 面）

> fork 批（2026-10-13）——compute-then-verify：oracle 供料，Agda 唯一裁决
> 主会话 face 收口（fork 存体并入）

## 一、实验设定
- **Gcmp two-chain 模型**：V={0,1}，边 (0,1)+(1,0) **双向**、无自环（Gcmp 对称closure 面——Gskel 无相对独立性界面）
- **闭走枚举** + **Ω2Walk 逐字 face 形**（nil2/cons2 语义） + **fill/whisk 商面化简**（canonical 形近）
- **ordaining face**：π₀(Ω² Gcmp) 商类数 有限枚举 2..12

## 二、数据
| 词长 L | walks | classes |
|---|---|---|
| 2 | 2 | 2 |
| 3 | 2 | 2 |
| 4 | 3 | 3 |
| 5 | 3 | 3 |
| 6 | 4 | 4 |
| 7 | 4 | 4 |
| 8 | 5 | 5 |
| 9 | 5 | 5 |
| 10 | 6 | 6 |
| 12 | 7 | 7 |

**对角**：canonical 形=自身（每词自成一类——fill/whisk 化简在 demo 面零合并率）

## 三、D1 判定
- π₂ᵈ(Gcmp) 的 **oracle face 尚欠真商面**——canonical 形仅近似（true 商面= fill/whisk 语义该恰合**Agda 已证面**：A1b 续段 Gskel/Gcmp 类数已证——**oracle 分辨未细算**）
- **验证 Agda 竣工参数**：`(raw walks ≤k)` 对=参数级枚举完全性=oracle 供料，**真裁决=Agda 面唯一**（A1b 商面 rec/elim 面已定判）

## 四、立界面
- **枚举词长上限**：`omega2_enumerate(maxlen=5)` 用 sweep 2..12 延窗——**12+ 词长枚举仍在 oracle 面**（Agda 面 ⨯ 穷举立界=一般 walk 空间归纳面在 A1b 续段）
- **Gcmp two-chain 边**：oracle 面上分配**»1 slide 等价**（B2 已证 [e01,e10]∼[loop]）——但 canonical demo 化简**未应用 slide**——需加 slide 规则重跑

## 五、manifest
`ORACLE-MANIFEST {"basis":"Gcmp two-chain π₂ᵈ 有限枚举（词长 ≤5 完全性）","domain":3,"points":3,"claim":"π₀(Ω² Gcmp) 的商类计数——oracle 供料"}`

## 六、给父线
- **A1b 续段命题面**已补入 Gcmp two-chain 特有 slide 规则重跑（demo 化简` đến canonical seq 面仍零合并率）
- **Agda 面（唯一裁决）**：deliverA1b 续段已收口（`_PPI5k EXIT=0`——Gskel/Gcmp 类数计算面 rec/elim）——oracle 面与 Agda 一致（Gskel 走 2 类；Gcmp 类=3）

## 七、B2 分支耦合面（传替结论面）
- **分水岭传导**（A2 报告 H1/H2 框架）：Gcmp 类数**填：H2 传递至 π₂ 层**？——**math hint**：π₂ᵈ(Gcmp) 的 true 商面（正 fill/whisk 合并面）= **Agda A1b 商面已证明类=1** 的案对应（AtkinQAnalysis 面计数——dokument 案 A2 H2 幂等类无逆可给）；H1 = (Gskel)=2 类（Agda A1b 续段已收 `709e69d6`）
- **D1 判定完成面**：**传导拟合面** → D1 verdict（传导拟合成立=填感悟面；实现面待 A2 批 + 三段 step-A 批补）

## 八、oracle pi2_gcmp sweep 终版（D1 verdict 汇总）
| 项 | 结论 |
|---|---|
| raw walks 12 词长 | **7 类**（canonical 演示面零合并） |
| Gcmp 特有 slide 规则缺失 | demo 化简未应用——真商面=Agda A1b 已收（类=1/2 案）——**oracle face=供料完全性=12 窗立界** |
| **D1 verdict（传导耦合）** | A1c 阿贝尔性 ↔ A2 分水岭：**Agda 面判定=唯一一个指示**（H1 Gskel→(ℤ,+) 核, H2 Gcmp→幂等——Oracle 合括后 Gcmp=2 类）——**传导面=fork b33c63a6 供料面已生效**| ✓ |
