# Erratum: Frobenius 共轭 vs 复共轭——「原生 vs 外挂」的精确化

**日期**: 2026-08-17
**来源**: GLM 审计结论（会话裁定），经库内核对后落库
**影响文件**: `src/Sovereign/Algebra/GF9.agda`（头注释 + §14/§16）、`src/Sovereign/Constitution/GroupTheoryRedLight.agda`（§3 注释）

---

## 一、修正的硬错误

旧表述（已作废）：

> 「区别于复共轭 z↦z̄：char 0 无 Frobenius，必须额外引入」「来源：人为引入 i vs 不可约式生成」

**错误**：复共轭 z↦z̄ **是** ℂ 的域自同构——保加、保乘、双射、固定 ℝ；ℂ 的出生证明同样是 ℝ[x]/(x²+1)，与 GF(9) 的 GF(3)[x]/(x²+1) 结构平行。「是否自同构」不构成区别。

## 二、正确的对比表（替换旧表）

| 维度 | 复共轭（ℂ/ℝ） | GF(9) Frobenius σ |
|:---|:---|:---|
| 域自同构？ | **是**（保加保乘、固定 ℝ） | 是 |
| 出生证明 | ℝ[x]/(x²+1) | GF(3)[x]/(x²+1) |
| 基矩阵 | diag(1,−1) | diag(1,−1) |
| 与幂映射关系 | char 0 中任何 x↦xⁿ (n>1) 不可加；共轭不是幂映射 | **σ(x)=x³，幂映射本身即同态**（(x+y)³=x³+y³，char 3 freshman's dream） |
| 自同构群 | Aut(ℂ) 有 2^beth 个野自同构（依赖选择公理，不可构造）；复共轭靠 ℂ 之外的解析/序结构才被挑出 | **Aut(GF(9)/GF(3)) = {id, σ}**，唯一、典范、定义即得 |
| 验证 | 不可穷举 | 0-postulate，refl 穷举 |

**「原生 vs 外挂」的正确形式化**——不在「是否自同构」（都是），而在两点：

1. **算术强制**：σ 是幂映射，幂映射=同态是 char p 独有的刚性（char 0 不存在）；
2. **唯一典范**：σ 是 GF(9)/GF(3) 唯一非平凡自同构，无需任何选择；ℂ 的复共轭合法，但只是 2^beth 个野自同构中被外借解析结构挑出的一个。

## 三、库内证据（0 postulate）

| 定理 | 位置 |
|:---|:---|
| σ 保加 `galoisConjugate-add` | GF9.agda L789 |
| σ 保乘 `galoisConjugate-mul` | GF9.agda L794 |
| 三组件打包 `frobenius-automorphism` | GF9.agda L809 |
| σ = x³ 立方恒等式 `frobenius-cube` | GF9.agda §15 |
| 对合 `galoisConjugate²` / 不动域 `galoisFixedPoint` | GF9.agda L81 / L214 |
| 可分性见证 §16（新增）：`alpha-distinct-neg-alpha`（α≢−α）、`neg-alpha-squared`（−α 同根）、`formal-derivative-at-alpha-nonzero`（f'(α)=2α≠0） | GF9.agda §16 |

**审计待办核对**：审计称「σ-add、σ-mul 未在已证清单中」——系清单过时，两者早已在库（上表 L789/L794）。

## 四、「导数为零」防误读注

- **幂映射多项式** x³ 的形式导数 3x² = 0（char 3）——体现 freshman's dream 刚性；
- **扩张多项式** x²+1 的形式导数 2x ≠ 0，f'(α) = 2α ≠ 0 —— **扩张可分**（两根 ±α 相异）。

两者不可混用：「导数为零」说的是幂映射，不是说扩张不可分。§16 的可分性见证引理把这一点机器锁定。

## 五、行为同构（命名层保留）

复共轭翻转手征（反全纯），σ 翻转 α 手征（α↔−α）——在「翻转手征」这一点上两者行为同构。Slot 6 手征对偶的命名层锚点在修正后仍然成立。

## 六、宿主清理状态（2026-08-17 已全部执行）

| 宿主 | 处理 |
|:---|:---|
| `docs/群论红灯审查-离散全息修复.md`（表行 + L54） | ✅ 已替换：`ConjugationExternallySelected` 新标签，旧标签作废注记 |
| `docs/Riemann/RH-GRH-数学极值相变宣言-正文定稿.md`（公理二） | ✅ 已加 erratum 注（判据精确化 + 野自同构诚实边界） |
| `docs/Riemann/RH-GRH-文献检索与元理论断层诊断.md`（L25） | ✅ 已加 erratum 注 |
| `docs/数学大厦底层更新-离散连续界面规范-v7.0.md`（L109） | ✅ 已替换为精确表述 |
| wiki `01-algebraic-pole.md` §代数原生 vs 外挂共轭 | ✅ 已加勘误块 + 表行修正 |
| wiki `103-gf9-conjugate-irrationality.md` | ✅ 已加勘误块 + 表行 + 正文修正 + 更新历史条目 |
| `docs/Riemann/RH-GRH-文献检索与元理论断层诊断.md` L276（scaling flow 非代数自同构） | 保留（该表述本身正确） |

---

*最终立场：接受数学修正，坚持本体论承诺。真正的区别不在「是否自同构」，而在「σ 由算术强制、唯一典范；ℂ 的复轭是无数野自同构中被解析结构外挂挑出的一个」。*
