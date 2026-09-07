# D₁₂ 二面体群模块 — 数学内容分析与依赖类型论落法

> 分析 (2026-09-07): fable5-thinking 结构反思 + proof-engineer 形式化审查
> 对象: `src/Sovereign/Algebra/Dihedral/DihedralD12.agda` (246 行草稿, 未编译)
> 结论: 数学内容正确且近乎完整, 卡在 3 处局部错误, 修复需补 2 条小引理即可复用绿库闭合。

## 一、这个模块数学上是什么

**二面体群 D₁₂ = 24 阶非交换群** = 正十二边形的对称群（12 旋转 + 12 反射）。
形式上是**半直积** D₁₂ = DC ⋊_ρ C₂，其中 DC = DuodecPoint（12 阶交换"时钟"），ρ = 取逆自同构。定义关系:
```
r¹² = 1  (DC 的联合周期 12, 已证 mixedOp-12-cycle)
s²  = 1  (反射对合, rho-involution 已证)
srs = r⁻¹ (反射共轭旋转 = 取逆 ← 半直积的 twisting, 模块核心验证)
```

**在群论绿链中的位置**: 现有链 (DuodecClock → DCGroup → Norm → CyclicGroup → DayanCore)
全部是**交换群** (C₃×C₄≅C₁₂)。DihedralD12 是库中**第一个非交换群**——它示范 DC 上
能长出半直积结构、ρ 确为自同构、非交换性是构造性反例。这是绿链没有覆盖的数学空白。

## 二、草稿已做对的核心 (依赖类型论亮点)

1. **归纳类型编码半直积纤维**——信息全保留, 无商化:
```agda
data DihedralElement : Set where
  rotate  : DuodecPoint → DihedralElement   -- (x, ε=0)
  reflect : DuodecPoint → DihedralElement   -- (x, ε=1)
```
2. **乘法 2×2 分 4 条, ρ 正确作用第二分量** (头注第 3 条承重):
```agda
rotate  p ⋆ rotate  q = rotate  (mixedOp p q)          -- ε=0,δ=0: x·y
rotate  p ⋆ reflect q = reflect (mixedOp p q)          -- ε=0,δ=1: x·y
reflect p ⋆ rotate  q = reflect (mixedOp p (rho q))    -- ε=1,δ=0: x·ρ(y)
reflect p ⋆ reflect q = rotate  (mixedOp p (rho q))    -- ε=1,δ=1: x·ρ(y)
```
3. **群公理逐 case 归约到 DC 已证** (mixedOp-assoc/identity/inverse) — 高层结构归约到底层已证交换群。
4. **非交换性是构造性反例**: `Σ(p,q). p⋆q ≢ q⋆p` (具体对 rotate(T₁,a0), reflect(T₀,a1))。
5. **嵌入 + 短正合列**: embed-dc 单射同态 + d12-sign : D₁₂→C₂ (sign-surjective)。
   这是依赖类型论表述"DC 是正规子群"的正确方式 (纤维结构+单射), 非断言商群。

## 三、卡住的 3 处真实错误 (均非数学问题)

| # | 位置 | 错误 | 根因 | 修法 |
|---|------|------|------|------|
| 1 | rho-conjugation (~145) | NoParse `reflect e ⋆ rotate g ⋆ reflect e ≡ rotate(rho g)` | `⋆` 与 `≡` 混用无结合 | 加括号 `(reflect e ⋆ rotate g) ⋆ reflect e ≡ ...` |
| 2 | rho-conjugation-inverse (~160) | NotInScope `rho-inverse` | 引用了不存在的引理; 绿版只有 rho-involution | 用 rho-is-inv (见 §四) |
| 3 | d12-assoc 反射情形 | 组合需 rho 与 assoc 兼容 | 8 条里 reflect 情形需 rho 的混合性质 | 用 rho-mixedOp (见 §四) |

## 四、所需补的 2 条引理 — 且已存在于绿库!

**关键发现**: rho 的代数性质层**已在绿库证过**, 不必重证:

1. **rho-is-inv**: `rho p ≡ duodec-inv p`
   - 证明: rho p = (negate t, alphaInv a) [DuodecClock 522], duodec-inv p = 同 [217] → 逐 12 case refl 定义性成立。
   - 需要新增 (DuodecClock 或本地)。

2. **rho-mixedOp**: `rho (mixedOp p q) ≡ mixedOp (rho p) (rho q)`
   - **已在 DCCayleyGraph.agda ~509 行证明** (rho 是 mixedOp 自同构, 分量级 neg-homo-⊕ 9 case + alphaInv-mulAlpha 16 case)。
   - 因 DC 交换 (mixedOp-comm), 反同态 `rho(xy)=rho(y)rho(x)` 与同态 `rho(xy)=rho(x)rho(y)` 等价 → 这条同态方向正是 DihedralD12 需要的。
   - **复用方式**: import 自 DCCayleyGraph, 或把这两条分量引理上提到 DuodecClock/DCGroup 更合理 (rho 的代数性质应属群论层而非谱层)。

## 五、修复步骤 (最小路径, 让草稿编译通)

1. DCCayleyGraph 的 neg-homo-⊕ / alphaInv-mulAlpha / rho-mixedOp **上提到 DuodecClock** (rho 属 DC 群论层), DihedralD12 import 之。
2. 补 `rho-is-inv` (12 case refl)。
3. rho-conjugation 加括号修解析。
4. rho-conjugation-inverse 改用 rho-is-inv。
5. d12-assoc 反射情形: 需检查 8 条是否含 "p·ρ q 再 assoc" 的嵌套, 若需重排则用 rho-mixedOp + mixedOp-assoc 组合成 ≡-Reasoning。
6. 编译通过后: 0 postulate 0 hole 目标, 并验证 d12-order = 24 (计数 DC 12 + 反射 12)。

## 六、更深的设计考量 (依赖类型论 vs 集合论)

- D₁₂ 若用集合论定义 = 商掉 ⟨srs=r⁻¹⟩ 的最小正规子群, 信息丢失 (哪些等式是"定义"哪些是"推论"不可辨)。
- 依赖类型论: 半直积直接编码 (rotate/reflect 携带 DC 坐标 + ε), 定义关系 srs=r⁻¹ 是**机器检查的定理** (rho-conjugation), 非商掉的 axiom。
- 短正合列 1→DC→D₁₂→C₂→1 用纤维结构表达: DC 是 D₁₂ 的正规子群是**结构事实** (每元素唯一分解为 rotate x 或 reflect x), 非额外公理。
- 非交换性是构造性 witness。这与 Green 库 NormExactSequence (1→C₄→C₈→C₂→1 不分裂) 互补:
  NormExactSequence 证明"非分裂", D₁₂ 证明"真非交换"。

## 七、价值评估与建议

- 唯一「库中真空白 + 数学近乎完整 + 修复仅局部」的 Dihedral 草稿。
- 完成后补上群论链缺的非交换例子, 与 DayanCore (抽象基座) 呼应。
- **建议**: 按 §五 修通, 并把 rho 代数性质 (rho-mixedOp 等) 归位到 DuodecClock/DCGroup (群论层), DihedralD12 作为独立 D₁₂ 模块入库。
- 其余 4 个 Dihedral 草稿 (DCTopos/CayleyMetric/DiscreteMetric/ElectronCloud) 价值被覆盖或建模粗糙, 建议保留源码不追或删除。

## 附: 依赖侧标注

- **本地形式化**: DC 群结构, rho, D₁₂ 半直积全部本地; 修复只需已在库的 rho-mixedOp + 12-case rho-is-inv。
- **连续统**: 无。D₁₂ 有限群, 无极限/几何对称群连续体。
- **待补**: rho-is-inv (12 case), rho-mixedOp 上提到群论层 (代码迁移, 不改语义)。
