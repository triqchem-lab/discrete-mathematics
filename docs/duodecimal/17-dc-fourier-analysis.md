# DC 傅里叶分析层 — 特征分解的完整形式化

> 状态: ✅ 完成 (2026-09-07)
> 文件: `src/Sovereign/Algebra/Character/DCCharacter.agda` (3700+ 行, 0 postulate, 0 hole)
> 依赖: DuodecClock (DC 载体), AlgebraicComplex (载体启发), Data.Rational (定点坐标)

## 一、核心载体: Z12Sys = ℚ(ζ₁₂)

DC 的 12 个特征值无法落在全实域 Sqrt3 = ℚ(√3)（草稿曾误用, ζ₃³ 计算否证），
正确载体是 ℚ(ζ₁₂) = ℚ(i, γ)/(i²+1, γ²+3) 的 4 维 ℚ 基表示:

```
Z12Sys (a,b,c,d)  ↦  a + b·i + c·γ + d·iγ,   i² = -1, γ² = -3
ζ₃ = -1/2 + γ/2 (三次单位根),  i (四次单位根),  ζ₁₂ = ζ₃·i
```

坐标全 ∈ ℚ（定点整数比, 宪法禁浮点）。载体验证 refl 可验: ζ₃³=1, i²=-1, conj ζ₃=ζ₃²。

## 二、代数结构 (Z12Sys 是真交换环)

全部机器证明, 是傅里叶组装的代数地基:

| 引理 | 内容 | 证明 |
|------|------|------|
| `+ᶻ-comm/assoc` | 加法交换/结合 | 分量 ℚ 引理 |
| `*ᶻ-comm` | 乘法交换 | 分量链 |
| `*ᶻ-assoc` | 乘法结合 (4 坐标) | `solve 12` 环反射 (变量全泛化时可用) |
| `*ᶻ-middle4` | (a·b)·(c·d) ≡ (a·c)·(b·d) | assoc+comm 推出 |
| `*ᶻ-distribˡ/ʳ` | 分配律 | 分量链 |
| `*ᶻ-zeroʳ`, zid | 零元 | 分量 |
| conj-+ᶻ, conj-*ᶻ, conj-involutive | 共轭是环自同构+对合 | 分量链 |

## 三、特征分解 (具体穷举 refl)

- 特征 χ₍u,v₎(t,aₖ) = ζ₃^{u·t} · ζ₄^{v∘k}（ζ₄ = i; 相位通道用指数乘法 alpha-pow, 非 mulAlpha）
- 载体验证: ζ₃³=1, i²=-1 (refl)
- **特征同态性**: χ(p·q) = χ(p)·χ(q) — 1728 case refl (dc-character-hom)
- **反射作用**: χ(ρ p) = conj χ(p) — 144 case refl (rho-character)

## 四、对偶完备性 (Parseval 的数学内核)

具体索引下的 12 项求和全部 refl 穷举:

- **正交性**: 不同特征内积 Σ_x χ₍u,v₎(x)·conj χ₍u',v'₎(x) = 0 — 132 case + 24 对角 ⊥-elim
- **自内积**: Σ_x |χ₍u,v₎(x)|² = 12 — 12 case
- **对偶完备性** (Fin 枚举形式 kerFin): Σ_k conj χ_k(x)·χ_k(y) = 12·δ_xy — self 12 + off 132 case refl

## 五、Parseval/Plancherel 恒等式 (主定理)

```
parseval : ∀ (f : DuodecPoint → Z12Sys) →
  Σ_x |f(x)|² = (1/12) · Σ_k |f̂(k)|²
```

**组装方法** (依赖类型论: 结构归纳优先于字面穷举):
1. **归纳求和算子 sumF**: `(Fin n → Z12Sys) → Z12Sys`, 结构归纳定义
2. **泛型求和引理** (全部 sumF 结构归纳):
   - sumF-mull/mulr: 因子穿入求和
   - sumF-comm2: 双和交换 (Σ_i Σ_j ≡ Σ_j Σ_i)
   - sumF-ext: 点等→和等
   - sumF-prod: 两和之积 = 二重和
   - pick, diag-collapse: 对角吸收
3. **枚举桥**: chr12/dc-points 把字面 sum-over-* 同构到 sumF{12}
4. **对偶核逐点代入**: 12×12 个 (x,y) 的具体对偶值 (12 或 0) refl
5. **标量消去**: (1/12)·12 = 1 (solve 0)

**全程无 144 项字面树重排** — 结构重排全在 sumF 归纳层, 对偶吸收在对偶核引理层。

## 六、依赖侧标注

- **本地形式化**: 载体 Z12Sys、环结构、特征、对偶完备性、Parseval — 全部在
  DCCharacter.agda 内机器证明, 坐标纯 ℚ 定点比。
- **连续统**: 无。整个傅里叶层在有限 12 点 DC 上, 无极限、无谱分解。
- **遗留边界** (诚实): 谱定理 (对称矩阵可对角化) 需要 ℚ(ζ₁₂) 外载体, 未形式化;
  对任意有限阿贝尔群 G 的泛 Parseval 未泛化 (仅 DC=C₃×C₄ 特例)。

## 七、代码位置

`src/Sovereign/Algebra/Character/DCCharacter.agda` 内新节 §9″ (文件尾, col-0):
- 泛型求和: fsuc 引理, *ᶻ-zeroˡ, sumF-mulr/prod, pick, diag-collapse
- 枚举: chr12, χF, kerFin, dftFin, bridge12, dcOver-sumF, charOver-sumF
- 对偶核: kerFinSelf (12 refl), kerFinOff (132 refl)
- 组装: conj-dftFin, reshapeFin, triple-swap, inner-factorFin, plancherelFin
- 主定理: z1-lunit, scal-mult, sc112-comp, cancel112-12, dftPlancherel, **parseval**

## 八、成果地位

DC 傅里叶分析层 (特征→正交→对偶完备→Parseval) 现已完整闭环。
这是 Problem 层 (如 FermatL4_Mod12Cycle) 之上、为后续谐波/能量论证提供
"离散能量守恒"机器的本地形式化基座。
