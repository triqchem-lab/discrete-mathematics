# Morse 同调术语体系——Forman 离散 Morse 理论

> **日期**: 2026-10-04
> **性质**: Morse 泛型化术语提取——12 个模块的核心概念统一
> **来源**: Forman (1998) 离散 Morse 理论 + 本库 12+ 模块

---

## 一、Morse 场与配对

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **MorseFieldG** | 泛型 Morse 场 record——Face + face-dim + V(配对) + dim-law | `MorseFieldG` record | MorseRoute |
| **配对函数 V** | V σ = just τ 表示 σ 配对到 τ（升维方向） | `V : K → Maybe K` | DiscreteMorseGeneral |
| **临界胞腔 (critical)** | V σ ≡ nothing ∧ ¬∃τ, V τ ≡ just σ | `IsCritical` | DiscreteMorseGeneral |
| **临界复形** | 按维度分层的临界胞腔集合 | `criticalComplex : ... → Set` | DiscreteMorseGeneral |
| **配对** | τ↔σ：V τ = just σ（低维→高维的匹配） | `V τ ≡ just σ` | — |
| **Morse 函数** | 离散 Morse 函数 f: K → ℕ 满足 Morse 不等式 | `DiscreteMorseFunction` | DiscreteMorseGeneral |
| **完美 Morse 函数** | 临界胞腔数 = Betti 数（最小临界集） | 完美 ⟹ C₀ᶜ = ⟨v₀⟩ | FormanMinimal |
| **Morse 场存在性** | 任意 K 上取平凡场 V ≡ nothing 全临界 | `MorseExistence` | MorseExistence |

## 二、临界复形与链群

| 术语 | 定义 | 代码 | 值（K₃ triVF 实例） |
|---|---|---|---|
| **MorseChain₀** | 临界 0-胞腔链群 | `FAb 2` = C₀ᶜ | 临界顶点 {v₁, v₂} |
| **MorseChain₁** | 临界 1-胞腔链群 | `FAb 1` = C₁ᶜ | 临界边 {e₂₀} |
| **MorseChain₂** | 临界 2-胞腔链群 | `FAb 0` | 无临界面 |
| **FAb(n)** | 自由阿贝尔群（n 个生成元 over GF(3)） | `FAb n = Fin n → Trit` | — |
| **IsCrit σ** | σ 的临界性判定 | `(V σ ≡ nothing) × (∀τ → V τ ≢ just σ)` | — |

## 三、交替路径路由

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **交替路径** | Face 升维 + V 配对降维交替的路径 | `MorseRoute` data（r-direct / r-via） | MorseRoute |
| **r-direct** | 直连路由：σ 面到临界 τ | `r-direct σ τ h Vτ-crit` | MorseRoute |
| **r-via** | 链式路由：经 w（配对入口 V w = just e'）间接到达 τ | `r-via σ w e' τ hface hw hw-tau hrout` | MorseRoute |
| **维度下降** | MorseRoute σ τ ⟹ dim τ < dim σ | `route-dim-descent` | MorseRoute |
| **routeList** | σ 到 τ 的路由列表 | 手写实例层枚举 | MorseRouteListDT |
| **路由完备性** | 每条路由被枚举恰一次 | 实例层：11 胞腔逐一排除 | MorseRouteListDT |

## 四、系数簿记

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **MorseCoeffField** | MorseFieldG + coeff + entry-inv | `record MorseCoeffField` | MorseCoeffRoute |
| **coeff** | 面关系系数（GF(3) 上） | `coeff : ∀ τ σ → Face τ σ → Trit` | — |
| **entry-inv** | 配对入口系数的逆（GF(3) 域性） | `entry-inv : ∀ σ → GF(3)⁻¹` | — |
| **CoeffRoute** | 系数为索引的归纳路由 | `data CoeffRoute : K → K → Trit → Set` | MorseCoeffRoute |
| **cr-direct** | 系数直连路由（临界终止判定） | `cr-direct σ τ c h Vτ-crit coeff-σ-τ` | — |
| **cr-via** | 系数链式路由（经配对入口间接） | `cr-via σ w e' τ c σ-w hw w-tau c' ν hrout` | — |
| **系数 μ(path)** | 路径系数乘积 μ = (∂系数)×(入口系数)⁻¹×(出口系数)×ε | — | — |
| **ε 符号** | 路径方向符号 ε = (−1)^V(箭头) | — | — |

## 五、∂^Morse 边界与消元

| 术语 | 定义 | 公式 | 状态 |
|---|---|---|---|
| **∂^Morse** | Morse 边界算子 | ∂ᶜτ = Σ_{p ∈ routeList τ} μ(p)·p(终止临界胞腔) | 泛型 pending |
| **∂²消元** | ∂^Morse ∘ ∂^Morse = 0（关键定理） | 泛型配对论证 pending；K₃ 实例 ✅ | M3 |
| **μ 组合律** | 路径切分点任意总系数不变 | 单位律+非零保持+ε对消+组合一致 | ✅ proven |
| **m3-cancel** | ∂²消元 K₃ 实例：T₁ ⊕ T₂ = T₀ | `m3-cancel : T₁ ⊕ T₂ ≡ T₀` | ✅ refl |
| **双三角测试床** | 11 胞腔 Sx2 + Face2(16 构造子) + V2 + coeff2 | `DoubleTriangle` | ✅ |

## 六、Morse 不等式与坍缩

| 术语 | 定义 | 代码 | 值（K₃） |
|---|---|---|---|
| **Morse 不等式** | μₖ(临界k胞腔数) ≥ βₖ(Betti数) | `morse-inequality` | ✅ |
| **χ(Morse) = χ(原)** | Euler 示性数不变 | `FormanChiInvariant` | ✅ |
| **坍缩 (collapse)** | 初等坍缩：移除配对 (τ,σ) 其中 Face σ τ | `Collapse` | ✅ |
| **可坍缩 ⟹ 完美 Morse** | 坍缩序列诱导 collapseVF | `CollapseToMorse` (B4 正向) | ✅ |
| **完美 Morse 非唯一** | K₃ 上 perfectVF(临界{v₂}) ≠ collapseVF(临界{v₀}) | 机器见证 | ✅ |

## 七、Morse 泛型化进度

| 阶段 | 内容 | 状态 |
|---|---|---|
| 泛型机件 ① 路由关系 | MorseRoute + MorseFieldG + route-dim-descent | ✅ |
| 泛型机件 ② 系数簿记 | MorseCoeffField + CoeffRoute + coeff-dim-descent | ✅ |
| 泛型机件 ③ μ 组合律 | 单位+非零+ε对消+组合一致 | ✅ |
| 泛型机件 ④ 临界判定 | IsCritical + criticalComplex | ✅ |
| 泛型机件 ⑤ 组合律 | sun-yi 交替律 | ✅ |
| 泛型机件 ⑥ HIT 商群 | FreeAbQuotient + f₀ 同构 | ✅ |
| 泛型机件 ⑦ Σ 商等价 | FreeAbImEquiv | ✅ |
| M1 临界链群 | MorseChain (K₃ 对账) | ✅ |
| M2 路由列表 | routeList 完备枚举（实例首站） | ✅ 实例 / 泛型 pending |
| M3 ∂²消元 | ∂²=0 泛型配对论证 | K₃ 实例 ✅ / 泛型 pending |
| M4 链映射 | ChainHom 结构层 | 🔶 |
| M5–M7 | Ψ / 链同伦 / 同调同构 | pending |
