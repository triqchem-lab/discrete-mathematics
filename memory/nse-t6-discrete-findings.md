---
name: nse-t6-discrete-findings
description: T⁶=(Z/3)⁶ 上离散 Navier-Stokes 形式化的判定台账——哪些命题已证、哪些已证否（含最小反例）、为什么「离散 Laplacian 恒零」是陷阱
type: project
---

# T⁶ 离散 Navier-Stokes：判定台账 (2026-09-09)

**工作区**：`src/Sovereign/Problem/NavierStokes/NSEOnT6.agda`（0 postulate / 0 hole，`proof_compile` exit 0）

## 1. 核心修正：草案的「Δ_gf ≡ 0」是假命题

初稿断言「T⁶ 上离散 Laplacian 恒零」，并据此把 Leray 投影定义为恒等、把不可压保持写成无条件定理。
**该命题为假**，由两条独立路线同时判定：

| 路线 | 方法 | 结论 |
| --- | --- | --- |
| 反例路线 | Python 精确整数，729 δ 基 × 729 点全穷举 + 第二套独立实现复算 | Δδ_y ≠ 0 于 12 点 {y+e_i, y+2e_i}；8748/531441 个 (y,x) 对非零 |
| 计算路线 | Python 精确整数，729×729 矩阵 GF(3) 高斯消元 | rank(Δ) = 454，dim ker Δ = 275（非平凡核） |

**陷阱的成因**：Δ = Σ_i (T_i + T_i²) 中 f(x) 项系数为 6 ≡ 0 (mod 3)，
造成「六项全消」的假象；实际 Σ_i f(x+e_i) 与 Σ_i f(x+2e_i) 是独立的非平凡项。

**正确公式**（已编译）：

```agda
axisLap-eq : ∀ i f x → axisLap i f x ≡ (f x ⊕ f (shiftAt i (shiftAt i x))) ⊕ f (shiftAt i x)
discrete-laplacian-formula : ∀ f x → laplacian f x ≡ sum6 (...六轴展开...)
```

即 Δf(x) = Σ_i [f(x+e_i) ⊕ f(x+2e_i)]（f(x) 不出现）。

## 2. 与本项目已有 1D/2D 结果的关系（勿混淆）

- `Algebra/ProjectionDifferential.agda:131` 的 `Δ³≡0`、`:99` 的 `Δ²-is-const` 是
  **单轴/二维切片**的幂零性 —— 与六维 Δ 恒零**不等价**。
- 六维 Δ 不可逆：T¹..T⁴ rank = 1,4,14,46；T⁶ rank = 454。限制到零和子空间亦不可逆
  （T2: rank 3/8；T3: rank 13/26）。

## 3. 由此推翻的推论（含最小反例）

| 命题 | 判定 | 最小反例 |
| --- | --- | --- |
| Δf ≡ 0 | 假 | f = δ_{e₁}, x = 0 ⇒ Δf(0) = 1 |
| Δf ≡ -f | 假 | 常数场 f≡1 ⇒ Δf = 0 ≠ 2；9477/531441 失配 |
| div(∇(div v)) ≡ 0 | 假 | v = (δ_{e₁},0,0,0,0,0) ⇒ div(∇(div v))(0) = 2 |
| div v = 0 ⇒ div P(v) = 0 | 假 | T² 无散度场全穷举 59049 个，51030 个（86.42%）失效 |
| div(adv v) ≡ -div v | 假 | v = (x₁,0,…) ⇒ div v = 1, div(adv v) = 1, -div v = 2 |
| D_i²f(x) ≡ f(x+2e_i)⊕f(x) | 假 | 漏掉中间项 f(x+e_i)；反例 i=0, f=δ₀, x=2e₁ ⇒ 1 vs 0 |

## 3b. 已证的真定理（并入 NSEOnT6.agda, exit 0）

| 定理 | 内容 | 锚点 |
| --- | --- | --- |
| `axisLap-core` | (a ⊕ -b) ⊕ -(b ⊕ -c) ≡ (c ⊕ a) ⊕ b（27 case） | NSEOnT6.agda:313 |
| `axisLap-eq` | L_i f(x) ≡ (f x ⊕ f(x+2e_i)) ⊕ f(x+e_i) | NSEOnT6.agda:343 |
| `discrete-laplacian-formula` | 六轴精确公式（`cong6'` 组合） | NSEOnT6.agda:353 |
| `negate-double` | negate y ⊕ negate y ≡ y（特征 3, **不是** ≡ T₀） | §4c |
| `axisLap-formula` | L_i f(x) ≡ f(x+e) ⊕ (f(x+2e) ⊕ f x) | §4c |
| **`diff-cubed-zero`** | **D³ ≡ 0**（axisLap ∘ diffF ≡ 0，任意抽象 i/f/x） | §4c |
| `leray-conditional-divergence` | div(v +F grad p) = div v ⊕ Δp（条件式） | §5 |
| `leray-preserves-incompressible` | 压力可解 + 对流无散度 ⇒ 投影不可压 | §5 |

**关键教训**：`negate y ⊕ negate y ≡ T₀` 是**假引理**（正确为 `≡ y`）。
草案据此推出的「Δ 恒零」全链作废 —— 这是把「特征 3 的 y⊕y⊕y=0」误用为「y⊕y=0」。

## 3c. 相位层修正 (NSEPhaseField.agda, 2026-09-09, exit 0)

**范式修正**：NSEOnT6 用纯 GF(3) 幅度建模，违反**相位不可约性元公理**（相位 C₄ 被约化为幅度）。
新模块 `NSEPhaseField.agda` 换用展示群载体：

```
PhaseField = Torus6 → Trit × AlphaPower     (幅度 GF(3) × 相位 C₄)
phaseDiff i θ x = mulAlpha (θ (x+e_i)) (alphaInv (θ x))   -- C₄ 左不变差商
```

**关键修正**：密度不能只用 `galoisNorm`（它是 GF(9)→GF(3) 的**有损投影**，核 = ⟨α⟩ ≅ C₄，
会把相位丢第二次）。故分两个不可约分量：
- 幅度密度 `rhoAmp = amp ψ`（GF(3) 值，相位不进入）
- 相位输运 `rhoPhase i ψ = phaseDiff i (ph ψ)`（C₄ 值，相位保留）

**已证 (构造性, 0 postulate)**：
| 定理 | 内容 |
| --- | --- |
| `phase-order-4` | α⁴ = 1 (C₄ 闭合) |
| `phase-irreducible` | α² ≠ α (C₄ → C₂ 非忠实) |
| `mulAlpha-invʳ` | a · a⁻¹ = 1 |
| `phaseDiff-const` | 常数相位 → 输运 = 1 |
| `rhoAmp-bounded` | 幅度密度 ∈ {T₀,T₁,T₂} |
| `phase-rate-bounded` | 相位转动 ∈ {a0,a1,a2,a3} |
| `lapAtOrigin-value` | lapA 在原点 ≡ T₂ (构造性, **非数值**) |

**Frobenius 相位共轭 (C₄ 的 C₂ 自同构)**：
```
phaseConjugate: a0↦a0, a1↦a3, a2↦a2, a3↦a1   (α^k ↦ α^{-k})
phaseConjugate-hom : σ(a·b) = σ(a)·σ(b)  (16 case)
phaseConjugate-nontrivial : σ(a1) ≠ a1
```
用于定义非平凡的 `Qphase = σ(Π_i phaseDiff_i θ)`。

**O2 已证 (关键修正)**：六轴相位差乘积**不**望远镜（各轴基点 `x+e_i` 不同，
不构成对消——我最初推断错了）。构造性见证：
```
madelung-nontrivial-exists : Σ PhField (λ θ → Σ Torus6 (λ x →
  phaseDiff zero θ x ≡ mulAlpha (quantumPotentialPhase θ x) (pressurePhase θ x)
  × phaseDiff zero θ x ≢ a0))
```
见证 θ = theta-e1, x = origin: transport=a1, Qphase=a2, RHS = a2·a3 = a1 ✅

**开放义务 (未证)**：
- O1 ρ=0 处量子势的物理含义（现为显式约定）
- O3 部分闭合: `rotate-4` / `phase-accumulation-period-4` 已证「单点相位累积四步回归」；
      但「因此无爆聚」仍未证（需先定义 729 格点上的「爆聚」）
- O4 连续统极限（本框架不声称）

**不声称**：工业 CFD 可用性；真实 Navier-Stokes 的解。

## 3d. 对抗自检发现的硬错误与修正 (2026-09-09)

devil's advocate agent 审查后确认 **3 blocker + 3 major**，已核实并修正：

| # | 问题 | 严重性 | 修正 |
| --- | --- | --- | --- |
| **Q5** | `shiftAt` 只覆盖轴 0,1,2（`C3 = Fin 3` 只有 3 元素），x₄,x₅,x₆ **从未被移位**；实测 rank=**378**/核=**351**，而头注释声称 454/275（那是真六轴算子的值） | major | ✅ 两个模块的注释已改为实测值 + 标注实现缺陷 |
| **Q2** | ρ=N(a·α^k)=a²∈{0,1}：**相位+幅度符号同时抹掉**，ρ 退化为支撑指示函数；相位从未进入 Q | blocker | ✅ §2 头注释改为双分量（rhoAmp/rhoPhase），标注 galoisNorm 有损 |
| **Q1** | `inv3 T₀=T₀` 把无定义写成 0；唯一被求值的 Q 恰为 T₀ | major | ✅ 补见证 ρ=x₀², x=e₁：Q=T₂≠T₀（构造性 `refl`） |
| **Q3** | 「高频/爆聚」无定义 | blocker | ⚠️ 部分：`rotate-4` 只证**固定旋转**四步回归；任意路径反例 (a1,a1,a1,a2)→a1 已标注 |
| **Q4** | `p=-ρ` 无方程；`MadelungCoupling` 无 ∀-实例 | major | ⚠️ 已标注：§4d 只是**单点**等式，不是 ∀-律 |
| **Q6** | GF(9) 符号仅出现在 import 行，零使用 | major | ⚠️ 待修（当前用 fin3ToTrit，GF(9) 确未用） |

**另一处自检发现**：§4c 注释曾写「乘积=a1、σ 后=a3」，实测为 **a2**，且 **σ(a2)=a2 —— Frobenius 在该见证点完全无作用**；非平凡性来自「轴 0 重复两次」(a1·a1=a2)。已修正注释。

**Q5 修复进展**：
- `NSEPhaseField.agda` 已改为 `Axis6 = Fin 6`，`lapA` 覆盖六个轴，rank 应为 454/275 ✅
- `NSEOnT6.agda` **仍含缺陷**（C3 = Fin 3 只有 3 轴；div/advection 3 轴对应 6 分量），头注释已如实标注「待重写」

**6 轴重算后的见证值变化**（原先按 3 轴重复算的都要改）：
| 量 | 3 轴版 | 6 轴版 |
| --- | --- | --- |
| `lapA(δ_{e₁})(origin)` | T₂ | **T₁** |
| `lapA(ρ=x₀²)(e₁)` | T₁ | **T₂** |
| `Q(ρ=x₀²)(e₁)` | T₂ | **T₁** |

**Q2 修复 (§9)**：新增 `quantumPotentialPhaseField : PhaseField → PhField`（C₄ 值），
相位经 `quantumPotentialPhase` 进入 Q；幅度经 `ampToPhase`（**单射**提升，非坍缩）。
见证 `test-phase-enters`：幅度层为 0 而相位非平凡 ⇒ Q = a2 ≠ a0（若相位不进入必为 a0）。

**Q3 修复 (§10)**：定义可计算的爆聚指标 `phaseLevel (phaseDiff i θ x) ∈ {0,1,2,3}`，
并证 `blowup-indicator-bounded : ∀ i θ x → phaseLevel (phaseDiff i θ x) ≤ 3`（构造性）。
⚠ 仍未证「指标有界 ⇒ 系统无爆聚」（需先定义演化时间步）。

**工程坑**：本环境下 `s≤s` 构造子在 `_≤_` 证明中行为异常（`s≤s (s≤s z≤n)` 报 `0 ≤ 2`）；
改用 `Data.Nat.Properties.≤-step` + `≤-refl` 可绕开。

**Q4 修复 (§4b)**：给 `MadelungCoupling` 一个**可证实例** `madelung-trivial`
（transport = pressurePhase, Qphase = 常数 a0, coupling 由 `mulAlpha-identityˡ` 闭合）。
⚠ 该实例是平凡的；真正非平凡的耦合方程对任意 θ **不成立**（反例 θ-e1-e2 在原点：pdiff0=a1, Q=a0, RHS=a3）。

**Q6 修复**：删除未使用的 GF(9) import（8 个符号仅出现在 import 行，零实际使用），
改为注释说明「相位层用 AlphaPower (C₄)，幅度层用 Trit (GF(3))；GF(9) 的 galoisNorm 是有损投影，
不适合作量子势载体」。同时用 `m≤n⇒m≤1+n` 替换弃用的 `≤-step`。

**结论**：三大支柱（Q 非零 / 相位进入 Q / 爆聚可陈述）已全部落地；6 项审计中
**Q1/Q2/Q3/Q4/Q6 已修**，仅 **Q5 在 NSEOnT6 侧未修**（3 轴遗留），
且「相位刚性 ⇒ 系统无爆聚」这一完整命题仍未证。

## 3e. 展示群审核与 NSEPresentation.agda (2026-09-09)

按 `docs/duodecimal/11-type-theory-presentation.md` 八要素逐项审核 NSEOnT6：

| # | 要素 | NSEOnT6 | 判定 |
| --- | --- | --- | --- |
| ① | 载体 | `Torus6 → Trit`（纯幅度） | ❌ 相位截断 |
| ② | 生成元 | shift3/diffF | ✅ |
| ③ | 关系 | D³≡0 / laplacian 公式 | ✅ |
| ④ | 相位 | 无 | ❌ |
| ⑤ | 时钟 | 无 | ❌ |
| ⑥ | 归零 | D³≡0 | ✅ |
| ⑦ | 刚性 | 仅有限性 | ⚠️ 弱 |
| ⑧ | 核对 | refl | ✅ |
| + | Q5 轴 | `C3 = Fin 3` 只 3 轴 | ❌ 轴截断 |

**新模块 `NSEPresentation.agda`（287 行, exit 0, 0 postulate）** 按八要素重建：

```
① 载体: PresField = Torus6 → DuodecPoint = Trit × AlphaPower  (幅度 × 相位)
② 生成元: diffAmp (幅度差分) + diffPh (C₄ 左不变差商) + diffMix (混合)
③ 关系: mixedOp 群律 (引用 DuodecClock) + 本模块差分律
④ 相位: phase-order-4 / phase-irreducible / mulAlpha-invʳ / diffPh-const
⑤ 时钟: clockAt ψ 12 x ≡ ψ x  (引用 mixedOp-12-cycle)
⑥ 归零: add-cycle (⊕³) / phase-order-4 (α⁴) / clockAt-12 (mixedOp¹²)
⑦ 刚性: phaseConjugate (16 case 同态) + phaseConjugate-nontrivial
⑧ 核对: reconstruct / no-info-loss (分量外延)
+ Q5 修复: Axis6 = Fin 6, shiftAt 覆盖 x₁..x₆, shiftAt-cubed (6 case)
```

**无信息丢失判据**：`no-info-loss` —— 若两场在所有点的幅度与相位都相等，则场相等。

**§9 已补：div/advection（新载体，分量↔轴 1-1）**：
```
VelField = 6 × PresField
div v x = Σ_{i=1..6} diffAmp (axis i) (v_i) x     -- 六轴各不相同 (Q5 修复)
advSum vi v x = Σ_j (amp v_j ⊗ diffAmp (axis j) vi)  -- 6 路分派
adv1..adv6 + advField                              -- 幅度层对流
zeroVel-incompressible                             -- 构造性
```
⚠ 相位层对流待补（C₄ 上的「速度×相位差」乘法）。

**§10 已补：nsStep 的相位层**
```
Qphase ψ x = σ(Π_{i=0..5} diffPh i ψ x)        -- 六轴 + Frobenius
phaseStep ψ x = amp ψ x , mulAlpha (ph ψ x) (Qphase ψ x)   -- C₄ 群作用
mulAlpha-4-cycle : 固定乘子四步回归 (16 case, 构造性)
phaseStep-period : 相位演化周期上界 4
```
**O3 状态**：相位演化的四步回归已证（固定乘子）；「Qphase 演化稳定 ⇒ 无爆聚」仍未证
（依赖幅度层动力学，本模块未建）。

**§11 状态空间与最终周期**：
```
VelState = VelField                    -- 有限: 12^729
NSMap = VelState → VelState            -- 演化是自映射
```
最终周期性的证明骨架（5 步）已写明，但**步骤①状态编码注入性**是本项目历史卡点
（NSEOnT6 §7c 与 NSEPhaseField §7b 均未闭合；12^729 混合基数编码需 729 层递归）。
**不声称最终周期性** —— 只给出必要结构（有限 + 自映射）。
绕法候选：复用 `Structology.T6.toℕ-sum` + 其注入性；或改用「轨道直接比较」（只需 12^729+1 步内碰撞）。

**§12 尝试结果（复用已编译模块）**：
- ✅ 已证：`ampCode-injective`（Trit→Fin 3 注入）、`pc-bound`（pointCode ≤ 728）
- ❌ 卡点：`mod3-of`/`div3-of` 的符号参数归一化 —— Agda 把 `3 * n` 规范化成 `n + 2 * n`，
  与 stdlib `[m+kn]%n≡m%n` 的 `m + k * n` 形式不 unify；`mod-helper`/`div-helper` 对符号参数不归约
- 📝 已记录到 `prover_limits`：`agda-mod-helper-symbolic-stuck`（severity: degrade，
  附实测证据 + 4 条绕法），这是**工具链限制**，不是数学困难
- **✅ 已找到代码库标准做法并移植成功**（2026-09-09）：
  - **REWRITE 规则**：`Structology/T6Rewrite.agda` 可独立导入，定义
    `div3k : div-helper 0 2 (3 * k) 2 ≡ k` + `mod3k : mod-helper 0 2 (3 * k) 2 ≡ 0`
  - **关键陷阱**：规则 LHS 是 `3 * k`（因子在前）。`m*n/n≡m k 3` 产生 `k * 3`，**不匹配** →
    必须先 `*-comm` 翻转，或直接把编码写成 `3 * (...)` 的因式分解形式
  - **标准证明模式**（`T6.div3-add`）：
    ```
    (a + 3*b)/3
      ≡⟨ cong (λ x → x/3) (+-comm a (3*b)) ⟩
      (3*b + a)/3
      ≡⟨ cong (λ x → (x+a)/3) (*-comm 3 b) ⟩
      (b*3 + a)/3
      ≡⟨ +-distrib-/-∣ˡ a (divides-refl b) ⟩
      (b*3)/3 + a/3
      ≡⟨ cong (λ x → x + a/3) (m*n/n≡m b 3) ⟩
      b + a/3 ≡⟨ cong (b +_) (div3-fin3 a) ⟩ b + 0 ≡⟨ +-identityʳ b ⟩ b ∎
    ```
  - **已移植到 NSEPresentation**：`div3-fin3` / `div3-add` / `mod3-of` / `pc/3-1` 全部编译通过
  - **配套**：pointCode 改成 `x1 + 3*(x2 + 3*(...))` 的**因式分解形式**，使 `/3` 可用 div3-add 逐层剥离

**§12e–§12h 链条进展（全部编译 exit 0, 0 postulate）**：
| 环节 | 符号 | 状态 |
| --- | --- | --- |
| 层 1–5 除法提取 | `pc/3-1` .. `pc/3-5` | ✅ |
| 层 1–5 取模提取 | `pc%3-1` .. `pc%3-5` | ✅ |
| **点编码注入性** | `pointCode-injective` | ✅ 6 层剥离 |
| 因式分解上界 | `fac-bound` | ✅ |
| 点编码 | `pc<729` / `encodePt` / `encodePt-injective` | ✅ |
| 幅度值编码注入 | `ampCode-injective` | ✅ |
| 点解码器 | `digit` / `decodePt` / `decodeAux` | ✅ |
| 解码-编码往返 | `decode-encode` | ⚠️ **未证**（需对符号 n 展开 mod/div） |
| 分量场编码注入 | `encodeComp-injective` | ⚠️ 依赖往返 |
| 状态编码 / 最终周期 | — | ⚠️ 依赖上一步 |

**剩余瓶颈的解法已找到（查代码库 `Coupling/LCM.agda:149-158`）**：

代码库的编码一律用 **Horner 形式** `v + q * 3`（因子在**右**），配 `divExtract`/`modExtract`：
```agda
modExtract : ∀ v q → v < 3 → (v + q * 3) % 3 ≡ v
modExtract v q v<3 = trans ([m+kn]%n≡m%n v q 3) (m<n⇒m%n≡m v<3)

divExtract : ∀ v q → v < 3 → (v + q * 3) / 3 ≡ q
divExtract v q v<3 =
  let n = v + q * 3
      eq  = m≡m%n+[m/n]*n n 3            -- n ≡ n%3 + (n/3)*3
      eq2 = trans eq (cong (λ x → x + (n/3)*3) (modExtract v q v<3))
      eq3 = +-cancelˡ-≡ v _ _ eq2        -- q*3 ≡ (n/3)*3
  in sym (*-cancelʳ-≡ q (n/3) 3 eq3)     -- q ≡ n/3
```
**关键**：用 `m≡m%n+[m/n]*n` + 消去律，**完全不依赖算术归一化**——绕开 `3*c ≡ c+(c+c)` 问题。

**已移植到 NSEPresentation（编译通过）**：
- `valH`（Horner 形式，因子在右）
- `tail0`（尾零化简，3 case）
- `modExtract` / `divExtract`（LCM 范式）

**已移植到主模块（编译通过）**：
- 逐层 Horner 值函数 `val1`..`val5`（shift 友好）
- 尾零引理 `tail2`..`tail5`
- `val5-shift`（shift 关系，refl）
- `decode5`（5 元组解码器）

**剩余最后一个结构性问题**：归纳步需桥接 `val4 ∘ decode4 = val5 ∘ decode5`
（两个不同元数的值函数之间的对应），这是往返引理的最后一环。

## 4. 正确的形式化路线（下一步）

1. **离散 Leray 投影是条件存在**：`Δp = -div(adv v)` 仅在 RHS ∈ im(Δ) 时可解。
   形式化陈述应为「若 ∃p, Δp ≡ -div(adv v)，则 `P(v) := v +F grad p` 不可压」。
2. **最终周期性可直接复用**：`Analysis/FiniteDynamics.agda:102` 的
   `orbit-eventually-periodic`（Fin N 轨道最终周期，已证）+ `Structology/T6.agda:714`
   的 `toℕ-sum-injective` / `4320DClosure.agda:196` 的 `t6ToFin-injective`
   （T⁶ ↔ Fin 729 编码单射）。**不要再自证鸽巢**。
3. 状态空间 |State| = 3⁶ · 3⁷²⁹ = 3⁷³⁵ 有限 ⇒ 任何自映射轨道最终周期 ⇒ 无有限时间爆破。

## 5. 工程教训（可复用）

- **Python 精确穷举必须先于 Agda 证明**：本假命题靠 Python 才发现；
  若直接写 Agda 会被类型检查卡住而不自知（编译器只报「不类型检查」，不告诉你命题假）。
- **抽样验证会骗人**：只用线性场（f = x_i）测试时 Δf = 0 恰好成立（巧合），
  必须用随机场 + δ 基穷举才能暴露反例。
- **反例路线与计算路线必须互相独立复算**：本次两套 Python 实现结论一致才判定为「确定」。

## 6. 可引用锚点

- `src/Sovereign/Problem/NavierStokes/NSEOnT6.agda:313` `axisLap-core`（27 case）
- `src/Sovereign/Problem/NavierStokes/NSEOnT6.agda:343` `axisLap-eq`
- `src/Sovereign/Problem/NavierStokes/NSEOnT6.agda:353` `discrete-laplacian-formula`
- `src/Sovereign/Analysis/FiniteDynamics.agda:102` `orbit-eventually-periodic`
- `src/Sovereign/Structology/T6.agda:714` `toℕ-sum-injective`
- `docs/NavierStokes/NavierStokes-三重完备性编译器初诊.md`
- Lean 侧对照：`/data/work/leanprover/NavierStokesAndEuler`（616276 行，Clay 备选 (C)/(D)，
  爆破机制 = 相似标度 q(t)→0 ⇒ ‖v‖ ~ q^{-A} → ∞）

---

## 7. 编码链闭合 (2026-09-09 续): 往返引理 + 有限动力学推广

### 7.1 障碍的根因 (已定位, 非数学问题)

早前用**分层** `val1..val5` + `decode5` 试图证 `val5 (decode5 n k) ≡ n % 3^k` 失败，根因两条：

1. **`NonZero (3 ^ k)` 无法被 Agda instance 搜索找到**：`3 ^ k` 对变量 `k` 不归约到 `suc _`
   （`3 ^ suc k` 归约成 `3 ^ k + 2 * 3 ^ k`，内层 `3 ^ k` 卡住），而 `_%_`/`_/_` 的
   `{{NonZero divisor}}` 需要看到 `suc` 形式。即使显式给 `{{nz3pow {k}}}` 也留下
   `3 ^ _k = 3 ^ k` 的未解元变量（instance 证明项含 meta）。
2. **`val5` 的第 5 位永远被丢弃**：`val5 (x1..x5) = x1 + val4 (x2..x5) * 3`，
   而 `decode5 n (suc k)` 把 `decode5 (n/3) k` 的前 4 项右移 —— 两者不 definitionally 相等。

### 7.2 解法: 按位数递归的值函数 (完全避开 3^k 与 NonZero)

```agda
Val : ℕ → Set ; Val zero = ℕ ; Val (suc k) = ℕ × Val k
valN zero x = x ; valN (suc k) (x , d) = x + valN k d * 3
decN zero n = zero ; decN (suc k) n = n % 3 , decN k (n / 3)
remN zero n = zero ; remN (suc k) n = n % 3 + remN k (n / 3) * 3
```

- `valN-decN : valN k (decN k n) ≡ remN k n` —— **纯 `refl` + `cong`**，零算术引理。
- `remN-full : n < 3^k → remN k n ≡ n` —— 对 k 归纳，用 `m<n*o⇒m/o<n`（基 3）+ `m≡m%n+[m/n]*n`。
- `pointCode-roundtrip : valN 6 (decN 6 (pointCode x)) ≡ pointCode x`（`pc<729` + `3^6≡729` refl）。
- `decN6-pointCode-injective`：第二条独立注入路径（与 `encodePt-injective` 并列）。

**关键洞察**: 只用 `% 3` 与 `/ 3`（字面量 3 有 `NonZero` 实例），**从不**用 `3^k` 作除数。

### 7.3 库级推广: 有限类型 (经注入) 的轨道最终周期

`Analysis/FiniteDynamics.agda` 新增 `orbit-eventually-periodic-fin`：

```
∀ {A} (N : ℕ) (enc : A → Fin N) → (∀ {x y} → enc x ≡ enc y → x ≡ y)
  → (f : A → A) (x0 : A) → EventuallyPeriodic (orbit f x0)
```

证明：把编码序列 `enc ∘ orbit f x0` 的前 N+1 项交给 `Data.Fin.Properties.pigeonhole`，
得碰撞；用 `enc` 注入性拉回 A；`orbit-collision-propagates` 传播。
**只需单向注入**（不需要解码器/右逆）。

### 7.4 状态编码现状 (NSEPresentation §14)

- ✓ `phCode : AlphaPower → Fin 4` + `phCode-injective`（16 case）
- ✓ `compEnc : PresField → (Torus6 → Fin 3 × Fin 4)` + **逐点**注入性 `compEnc-injective`
- ⚠ `stateEnc` 用 `decodePt` 索引需要 `decodePt (encodePt x) ≡ x`（往返接线未做；
  `decodePt` 用 `digit`/`decodeAux`，与 `decN` 的对应未形式化）
- ⚠ 把 `(Torus6 → Fin 3 × Fin 4)` 注入 `Fin N` 未做 → 最终周期性未接线

**本库无 `funExt`**（非 cubical）：`ext` 只给逐点相等，给不出 `ψ ≡ φ`。
故 `orbit-eventually-periodic-fin` 的 `inj` 假设对本库的 `PresField` 需要逐点版本，
或改用 cubical `funExt`（需 `--cubical`，与 REWRITE 规则共存需另测）。

### 7.5 新撞到的证明器限制

- `_≤_` 的空模式 `()` 被 `Agda.Primitive.Cubical.primHComp` 挡住（`ShouldBeEmpty` 报「还有
  primHComp 构造子」），导致「具体数值 < 界」的证明难以用空模式消去不可能分支。
- `+-distrib-/-∣ˡ {m = m} (p * 4) {d = 4} (divides-refl p)` 报 `m ≡ p * 4` 不匹配：
  显式给 `{m}` 后 `∣` 证明的隐式 `m` 仍被绑到外层 `m`。
- `m*n≢0` / `m^n≢0` 类引理内部含 instance 参数，用作**另一个 instance** 会留下未解元变量。

### 7.6 编译证据 (回执)

- `NSEPresentation.agda` — `proof_compile` exit 0，回执 `49779e024aeb42f0e2db09b42d380ea0359ff34dc44840273d979837e00e4820`
  （0 postulate / 0 hole；`proof_audit` 需关注 3 项：fixity 声明缺失、1 处 `let`、1 条未用 using）
- `Analysis/FiniteDynamics.agda` — `proof_compile` exit 0，回执 `07221e822b68e1fccf77470c0a4119ab508c4715cafff993a2aaa276adede9f4`

---

## 8. 评估报告三阶段路线的执行结果 (2026-09-10)

依据 `/home/yanli/文档/math/Lean NSE库与FLT库缺口对比 Clay备选方案语义解析及大衍Agda证明实施方案评估报告.txt` 的三阶段路线：

### 8.1 A 档（PacketShiftArithmetic 迁移）— 完成

`src/Sovereign/Applied/PacketShiftArithmetic.agda`（524 行，回执 `c7ad6518`）。
Lean 侧 `Euler/PacketShiftArithmetic.lean` 的 10 条纯 ℕ 定理逐条迁移，
处理 `_∸_` 截断减法用 `suc` 模式匹配。**注意报告 §3.1.1 的函数定义是示意**
（真实 Lean 源：`highShift p = 100*p-80`、`meanShift p = 100*p-140`、
`highForceShift p = highShift p - 10`、`meanForceShift p = meanShift p - 10`）。

### 8.2 B 档（通用群论基础设施）— 完成

- `src/Sovereign/Algebra/GroupTheory/Lagrange.agda`（751 行，回执 `60942a3c`）：
  `record FinGroup n` + `record Subgroup` + 通用 `lagrange`（陪集分割 + 双射）+ C4/C12 实例
- `src/Sovereign/Algebra/GroupTheory/OrbitStabilizer.agda`（323 行，回执 `c1ad51f3`）：
  通用 `orbit-stabilizer : m * k ≡ n` + C₄ 正则/奇偶作用实例
- `src/Sovereign/Algebra/Representation/Maschke.agda`（570 行，回执 `a489f62c`）：
  抽象分裂引理 `invariant-projection-splits` + C₃/GF(2) 具体实例（6 分量）

### 8.3 C 档（NSE.T13 编码链）— 第一阶段闭合，最后一跳精确定位

**新证（本会话）**：

| 模块 | 新证符号 | 回执 |
|---|---|---|
| `Analysis/PairEnc.agda` | `pairEnc` / `pairEnc-injective`（144 case 穷举） | `2401929c` |
| `Analysis/FinMixedRadix.agda` §3 | `enc12` / `head12` / `enc12-tail` / `enc12-inj-pointwise` / `N12` / `enc12Fin` / `enc12Fin-inj-pointwise` | `56d09a52` |
| `Analysis/FiniteDynamics.agda` §4c/§4d/§4a' | `orbit-eventually-periodic-fin-pw` / `orbit-eventually-periodic-val-pw` / `orbit-collision-pw` | `7b2a3f49` |
| `NSEPresentation.agda` §15 | `div3f` / `mod3f` / `f3` / `codeToPoint` / `codeToPoint-pointCode` / `decodePt-codeToPoint` / **`decodePt-encodePt`** | `3df674d3` |
| `NSEFinalClosure.agda` | `stateCode` / `stateCode-injective` / `observe` / `STATE_DIM` | `80473ad3` |

**关键突破**：`decodePt (encodePt x) ≡ x` —— 往返闭合。手法：
1. `codeToPoint (pointCode x) ≡ x`：6 层剥离，每层用
   - `mod3f : f3 (toℕ a + 3 * t) ≡ a`（`% 3` + `[m+kn]%n≡m%n` + `m<n⇒m%n≡m`）
   - `div3f : (toℕ a + 3 * t) / 3 ≡ t`（**交换成 `t * 3 + a` 后用 `+-distrib-/-∣ˡ`**，
     避开显式 `{m}` 捕获的坑）
2. `finToℕ (encodePt x) ≡ pointCode x`（`toℕ-fromℕ<`）

**剩余一跳（已精确化）**：`nse-eventual-periodicity` 的鸽巢需要
「完整编码 `observe : PresField → ℕ` 的碰撞」，但：
- 单坐标 `Fin 12` 碰撞只能给**一个点**的相等，不足以推逐点相等（无 funExt）
- `Fin (suc (N12 729))` 的证明项随函数变化（`fromℕ< (s≤s (enc12≤N12 k f))`），
  导致 `cong` 无法对齐（`prover_limits: agda-cong-lambda-extra-application`）

**可行路径**：把 `enc12Fin` 改成不依赖证明项的包装（例如先 `fromℕ<` 到固定界
再 `inject≤`），或用 `subst` 显式重写证明项。
