# N×N 完成度盘点 — 本地实现实况（文件:行锚点）

口径：「完成」= **类型层有证明项**（`proof_compile` 可裁决）；「注释级」= 只在散文里声称；逐尺寸、逐能力分开记。审计背景：《理论-代码对应审计》E/F 组。

---

## 〇、直接回答：n×n 我们完成了多少

| 问题 | 答案 |
|---|---|
| **N×N 判定**（det≠0 ⟺ 双射/非退化） | **两个闭合实例 + 一条同态**：① **9×9 函数表**判定链完整闭合（`jac_NMatrix`，GF3² 9 点域）；② **12 点 CRT 双射分解**双向闭合（`jac_CRTSpectrum`）；③ **一般 N 的 π3 侧行列式同态**（`jac_CRTDet` §2b `π3-det`） |
| **行列式计算** | 2×2 **全套**（含 det(AB)=detA·detB 6561-case）；3×3、4×4 有 GF(9) 实例件；一般 N 只有 Duodec Laplace 版（π3 侧） |
| **一般 N 全式** `det=crt12(det_gf3,det_fin4)` | **半闭合**：π3 侧 ✅；π4(Z/4) 侧与 crt12 组装 ❌（Fin 4 环算子不存在） |
| **一般 N rank/逆/Leibniz** | ❌ 未做（jac_FunctionTable §6 自认 N×N gap） |

用户记忆「N×N 判定已完成」**基本属实**——但完成的是**结构判定链**（det≠0 由「无全零行∧列互异」代理定义后与双射等价），不是一般 N 的行列式计算；且判定链钉在 9 点域上。

---

## 一、行列式（计算型）逐尺寸

| 尺寸 | 载体 | 符号与位置 | 状态 |
|---|---|---|---|
| 2×2 | GF(3) | `det2`（<u>jac_Discrete.agda</u>:33、<u>jac_GF3.agda</u>:48）、`det2'`（<u>jac_LinearAlgebra.agda</u>:50） | ✅ |
| 2×2 | **泛载体**（任意 F + 二元运算） | `det : ∀ {F} (_+F_ _*F_) → Mat2 F → F`（<u>src/Sovereign/Algebra/Matrix2.agda</u>:62，另有 mulMat2/addMat2/trace/idMat2/zeroMat2） | ✅ 参数化 |
| 2×2 | GF(9)/Bool/其它 | `det2-gf9`（<u>jac_GF9Matrix.agda</u>:45）、`det2 : Mat2 → Bool`（S3IsGL22:50）、YM_SpectralGap:184、ProjectionDifferential:256 | ✅ |
| 2×2 | Duodec | `det2D`（<u>jac_CRTDet.agda</u>:67）+ `π3-det2-homo` | ✅（本轮） |
| 2×2 | **乘法性** | **`det-mul : det2 (mat-mul A B) ≡ det2 A ⊗ det2 B`**（<u>jac_Matrix.agda</u>，6561-case 穷举；台账 `Jac.det-mul.*` ✅）+ det-I/det-scale | ✅ |
| 3×3 | GF(3) | `det3 : M3 → Trit`（<u>Complexity3.agda</u>:15，实例 diag-det/CM） | ✅ 实例级 |
| 3×3 | GF(9) | `det3-gf9 : GF9Mat 3 3 → GF9`（<u>jac_GF9Matrix.agda</u>:90，det3-gf9-I ✅）+ CharPoly3 | ✅ 实例级 |
| 4×4 | GF(9) | `det4-gf9`/`I4-gf9`（jac_GF9Matrix，YM_L3/SUn_GF9/YM_Transfer/WilsonPlaquette 消费） | ✅ 实例级 |
| **一般 N** | **Duodec** | **`det : ∀ {n} → Mat n → Duodec`**（Laplace 行 0 展开 + punch/minor/sumD/sgn，<u>jac_CRTDet.agda</u> §2b:135） | ✅（本轮新增） |
| **一般 N** | **同态** | **`π3-det : ∀ {n} (M : Mat n) → π3 (det M) ≡ detT (λ r c → π3 (M r c))`**（§2b:180，归纳 + 无 funext） | ✅（本轮新增） |

## 二、秩 / 逆 / 伴随（集中在 2×2）

| 能力 | 位置 | 状态 |
|---|---|---|
| 2×2 逆 + 逆律 | `inv`/`inv-correct`（jac_Matrix:36-42）、`adjugate`（:424）、`invertible`（:433）、inverse-correct 全链 | ✅ |
| 2×2 秩判据 | `rank`/`rank2`/`det≠0→rank2`（jac_Matrix）、`rank-by-det`（jac_LinearAlgebra:57） | ✅ |
| GF(9) 秩 | `rank2-gf9`/`rank3-gf9`（jac_GF9Matrix:75,110） | ✅ |
| GF(3) 无零因子 | `no-zero-divisor`（jac_LinearAlgebra:15） | ✅ |
| 一般 N 秩/逆/伴随 | — | ❌ 未做 |

## 三、N×N「判定」= 结构判定链（用户记忆的实证来源）

| 件 | 内容 | 状态 |
|---|---|---|
| <u>jac_NMatrix.agda</u>（173 行） | **9×9 函数表** `Mat9 = Fin 9 → Fin 9 → Trit`；`DetNonzero := NoZeroRow × ColDistinct`（**结构代理定义**）；定理链 `detNonzero↔surj-inj`/`detNonzero↔bij`/`detNonzero↔nonsingular`（:155-167）+ funcTable 命中/未中引理 | ✅ 完整闭合（论域 = GF3² 9 点）⚠ 「det≠0」是定义代理，非行列式计算——与 jac_FunctionTable:113「形式化代理」口径一致 |
| <u>jac_FunctionTable.agda</u> | 列互异↔行满 ↔ NonSingular↔bij（9 点）；§6 **自认 gap**：N×N Leibniz 展开与一般交错性未构造 | ✅ 判定链 / ❌ N×N 行列式腿 |
| <u>jac_CRTSpectrum.agda</u>（606 行） | **12 点 CRT 双射分解**：`crt-bijection-forward`（:133）/`crt-bijection-backward`（:192）——`Bij12 (crt-compose f₃ f₄) ⟺ (Inj3×Surj3) × (Inj4×Surj4)` 双向 ✅ + `crt-id-decompose` + π3/π4-surjective；另有 CRT-structural/Inj3/Surj3/Inj4/Surj4 词汇 | ✅ 双向闭合（12=3×4 两个分量域） |
| <u>jac_DiscreteJC.agda</u> | 离散雅可比猜想三层强度陈述：形式导数 < 差分算子 < 函数表矩阵；反例整合 | ✅ 陈述层 |

## 四、一般 N 的 CRT 同态（2026-09 已全闭合）

| 分量 | 内容 | 状态 |
|---|---|---|
| π3（GF(3)） | `π3-det`（一般 N Laplace 同态）+ `π3-det2-homo`（2×2）+ `π3-neg`/`π3-sumD`/`π3-sgn`/`sumT-ext` | ✅ **闭合** |
| π4（Z/4Z） | Fin 4 环算子 `suc4/+4/\*4/neg4` + `π4-homo-+`/`π4-homo-\*`（24 拆子引理×12 案 refl）+ `π4-neg` + `det4` 镜像 + `π4-det` | ✅ **闭合**（2026-09 §2c） |
| crt12 组装 | **`det-crt12 : det M ≡ crt12 (detT (π₃∘M)) (det₄ (π₄∘M))`** = crt12-roundtrip ∘ cong₂（§2d） | ✅ **闭合**（回执 daf3e873…） |
| det≠0 等价（一般 N） | 元素级成立（crt12 同构）；⚠ 可逆性另受 R₁₂ 零因子约束（不许混） | ✅ 元素级 / ⛔ 可逆性措辞红线 |

> 推广声称勘误（2026-09）：WilsonLoop/YMTransfer/YM_DetMul/Complexity/PvsNP_Separation/CharPoly3 六处注释已插入勘误行（「3×3/4×4 小分量」是误读；一般 N 同态以 jac_CRTDet 为准）。

## 五、注释级 N×N 声称清单（未类型化 + 沿用旧误读）

以下消费者在注释里引 jac_CRTDet 做「N×N → 3×3+4×4 小分量」推广——**两个问题**：① 声称未类型化；② 沿用 jac_CRTDet:77-79 已修正的误读（**分量矩阵仍 N×N，「3/4」是环的元素数**）：

| 文件 | 位置 | 待勘误内容 |
|---|---|---|
| `Problem/YangMills/WilsonLoop.agda` | :78-93 | 「N×N 质量间隙由 2×2/3×3/4×4 的 det≠0 判定」 |
| `Problem/YangMills/YMTransfer.agda` | :4-26 | 「CRT N×N 推广 (结构闭合)」 |
| `Problem/YangMills/YM_DetMul.agda` | :58 | 「任意 N 分解为 3×3+4×4」 |
| `Problem/PvsNP/Complexity.agda` | :199-227 | 「CRT N×N 推广…所有 CRT 分量 ≤4×4」 |
| `Problem/PvsNP/PvsNP_Separation.agda` | :128 | 「N×N 高阶推广归约到 3×3+4×4」 |
| `Problem/PvsNP/CharPoly3.agda` | :26 | 「CRT N×N 推广 (结构闭合)」 |

## 六、对账：本轮 §2b 与既有件无重复（复用优先纪律核对）

- §2b `Mat/det`（Duodec 一般 N Laplace + π3 同态）vs `jac_NMatrix.Mat9`（9×9 函数表结构判定）：**不同问题**，无重复。
- vs `Matrix2.det`（泛载体 2×2）：尺寸/载体不同；Matrix2 的参数化风格是 §2b 未来「泛环版 det」的现成模板（roadmap）。
- vs `jac_GF9Matrix.GF9Mat : ℕ → ℕ → Set`（**尺寸参数化的矩阵类型已存在**！det 逐尺寸）：一般 N det 若做 GF9 版可直接复用其类型。

## 七、缺口按优先级（下一步候选）

1. **π₄ 侧**：定义 Fin 4 环算子 + π4-homo + det4 → crt12 组装定理（E1 全闭合）。
2. **注释级勘误**（第五节 6 处）：批量改「3×3+4×4 小分量」措辞 + 标 roadmap。
3. jac_FunctionTable §6 N×N Leibniz gap（一般 N 行列式 = 交错性等）——**正向已两段落定**（2026-09）：`jac_PermDet.det-perm-nonzero`（置换矩阵 det ≢ d0）+ **`det-struct-nonzero`/`det-funcTable-nonzero`**（结构代理→真 det 桥，9 点域 DetNonzero (funcTable F) ⟹ det ≢ d0，回执 e9e74a4e…）；反向「同列 → det = 0」需列反对称性，仍 roadmap。
4. 一般 N rank/逆（大件，另立 DAG 骨架再动）。

---
（盘点人：math-proof 会话；全部锚点为本轮 grep/read 实测，行号以当前工作树为准。）
