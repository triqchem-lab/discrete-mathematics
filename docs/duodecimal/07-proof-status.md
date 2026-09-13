# 十二进制证明状态

**日期**: 2026-08-25  
**最后核查**: 2026-09-10（关闭 G1/G4，其余各行附「核查」标注）  
**状态**: 审核清单  
**来源**: Agda 源码、algebraic-chain-status.md

---

## 一、证明总览

| 层级 | 模块 | Postulate | 状态 |
|------|------|:---------:|:----:|
| L0 | Duodecimal (C₁₂/R₁₂) | 0 | ✅ 完成 |
| L0C | CRT 分解 | 0 | ✅ 完成 |
| L1 | GF(3) 加法群 | 0 | ✅ 完成 |
| L2 | GF(3)* 乘法群 | 0 | ✅ 完成 |
| L3 | GF(9) 加法群 | 0 | ✅ 完成 |
| L4 | GF(9)* 乘法群 | 0 | ✅ 完成 |
| L5 | Frobenius σ | 0 | ✅ 完成 |
| L6 | Norm N(z) | 0 | ✅ 完成 |
| L7 | Trace Tr(z) | 0 | ✅ 完成 |
| L8 | Z/12Z 加法群 | 0 | ✅ 完成 |
| L9 | (Z/12Z)* ≅ V₄ | 0 | ✅ 完成 |
| L10 | CRT 分解 | 0 | ✅ 完成 |
| DC | DuodecClock | 0 | ✅ 完成 |

---

## 二、GF(3) 证明清单

| 证明 | 方法 | 状态 |
|------|------|:----:|
| 加法结合律 (27 case) | 穷举 refl | ✅ |
| 加法交换律 (9 case) | 穷举 refl | ✅ |
| 加法单位元 | 穷举 refl | ✅ |
| 加法逆元 | 穷举 refl | ✅ |
| 乘法结合律 (27 case) | 穷举 refl | ✅ |
| 乘法交换律 (9 case) | 穷举 refl | ✅ |
| 乘法单位元 | 穷举 refl | ✅ |
| 分配律 (27 case) | 穷举 refl | ✅ |
| 零乘消去 | 穷举 refl | ✅ |
| char3-triple | 穷举 refl | ✅ |

---

## 三、GF(9) 证明清单

| 证明 | 方法 | 状态 |
|------|------|:----:|
| α² = -1 | refl | ✅ |
| α⁴ = 1 | refl | ✅ |
| 域加法公理 | 分量 + GF3 引理 | ✅ |
| 域乘法公理 | 代数推导 | ✅ |
| Frobenius σ(x·y) = σ(x)·σ(y) | 代数推导 | ✅ |
| σ(x) = x ↔ x ∈ GF(3) | 构造性证明 | ✅ |
| Norm/Trace | 定义 | ✅ |

---

## 四、Duodecimal (C₁₂/R₁₂) 证明清单

| 证明 | 方法 | 状态 |
|------|------|:----:|
| +1^12-id | 12 case refl | ✅ |
| +12-assoc | 144 case | ✅ |
| +12-comm | 144 case | ✅ |
| +12-identityˡ/ʳ | 12 case | ✅ |
| +12-inverse | 12 case | ✅ |
| *12-comm | 144 case | ✅ |
| *12-identityˡ/ʳ | 12 case | ✅ |
| *12-zeroˡ/ʳ | 12 case | ✅ |
| zero-divisor-2×6 | refl | ✅ |
| zero-divisor-3×4 | refl | ✅ |
| not-a-field | 构造性 | ✅ |
| π3-homo-+ | 144 case | ✅ |
| π3-homo-* | 144 case | ✅ |
| crt12-roundtrip | 12 case | ✅ |
| crt12-inv-π3 | 12 case | ✅ |
| crt12-inv-π4 | 12 case | ✅ |

---

## 五、DuodecClock 证明清单

| 证明 | 方法 | 状态 |
|------|------|:----:|
| mulAlpha-assoc | 64 case | ✅ |
| mulAlpha-comm | 16 case | ✅ |
| mulAlpha-identityˡ/ʳ | 4 case | ✅ |
| mulAlpha-inverse | 4 case | ✅ |
| alphaPowerToGF9-hom | 16 case | ✅ |
| alphaPowerToGF9-injective | 16 case | ✅ |
| mixedOp-assoc | 分量引理 | ✅ |
| mixedOp-comm | 分量引理 | ✅ |
| mixedOp-identityˡ/ʳ | 分量引理 | ✅ |
| mixedOp-inverse | 分量引理 | ✅ |
| toDuodec/fromDuodec 往返 | CRT 引理 | ✅ |
| mixed-to-+12 | 144 case | ✅ |

---

## 六、缺口清单

### 6.1 定义层缺口

| ID | 缺口 | 优先级 | 说明 |
|----|------|:------:|------|
| G1 | ZeroOblivion record | ~~P1~~ | ✅ **已闭合（2026-09-10 核查）**：`DuodecClock.agda:415` 定义 `record ZeroOblivion`（5 字段：addZeroR / addZeroL / mulAlphaCycle / tritCycle / jointCycle），`DCGroup.agda:133` 给出 DC 实例 `dcZeroOblivion`，五字段分别由 `mixedOp-identityʳ` / `mixedOp-identityˡ` / `alpha-order-4` / `char3-triple` / `mixedOp-12-cycle` 供给。回执：DuodecClock `d6d927aeae6b…`、DCGroup `3c101976b58f…`（均 exit 0，0 postulate） |
| G2 | π₄ 同态性 | ~~P2~~ | ✅ **已闭合 (2026-09-09)**: `Algebra/Pi4Homomorphism.agda` 证 `π4-homo-+ : ∀ x y → π4 (x +12 y) ≡ (π4 x) +4 (π4 y)`（0 postulate; DAG: π4-+1 → pi4-iter → 12-case 主定理, 配 fin4-suc-4 周期约化；回执 `8a3755138de7…`，2026-09-10 复核仍在库） |
| G3 | CRT 与 mulAlpha | P2 | 如何从 CRT 分量重构 mulAlpha？**（2026-09-10 核查：仍开** —— 全库检索 `crt12`↔`mulAlpha` 无对应引理；`Format/CRTMeasurement.agda:293-300` 的 `reconstruct-N-N` 是别的东西） |
| G4 | *12 与 **DC 运算** 的关系 | ~~P1~~ | ✅ **已闭合（2026-09-10 核查）**：`DuodecClock.agda:372` `mulAlpha-not-*12 : Σ (DuodecPoint × DuodecPoint) (λ (p , q) → toDuodec (mixedOp p q) ≢ toDuodec p *12 toDuodec q)`，见证 `((T₁,a1),(T₁,a1))`（左端算得 `d2`，右端 `d1 *12 d1 = d1`，由 `d2-not-d1` 收口）。回执 `d6d927aeae6b…`（exit 0，0 postulate）。<br>⚠ **措辞更正**：证明中的算子是 `mixedOp`（DC 的群运算），**不是**原标题写的 `mulAlpha` —— `mulAlpha` 定义在 `AlphaPower` 上，`toDuodec` 不接受该类型，故原措辞不成立。引理名沿用了 `mulAlpha-not-*12`，以此为历史名保留。 |

### 6.2 文档层缺口

| ID | 缺口 | 优先级 | 说明 |
|----|------|:------:|------|
| D1 | AlgebraicPoleUnified 本体字段 | P0 | 与 README/DuodecClock 冲突 |
| D2 | algebraic-chain-status 矛盾 | P0 | 同时写「L8=Z/12 完成」和「Z/12 仅为投影」 |
| D3 | CRT-4POLE-AUDIT 判据 | P1 | 代数极判据需改挂到 DC |
| D4 | 早期「代数极基于 z12」表述 | P1 | 全文检索降级为 C₁₂/R₁₂ 投影语言 |

### 6.3 环论层缺口

| ID | 缺口 | 优先级 | 说明 |
|----|------|:------:|------|
| R1 | 理想格 | P2 | (2),(3),(4),(6) 主理想与 CRT 素幂分解 |
| R2 | 模与表示 | P2 | Duodec-模上的自由模；十二律置换表示。**（2026-09-10 核查：A₄ 一侧已有** —— `Structology/A4Representations.agda:11,230` 给了 V₃ = 置换表示去掉全对称分量（`sumZero-invariant`，13 case）；**DC 一侧的「十二律置换表示」仍开**，且全库无任何 DC 群作用）<br>→ **已选定为下一方向**，见 §九 |
| R3 | A₄ 阶 12 衔接 | P3 | |A₄|=12 已在注释，需要形式化 |

---

## 七、审计记录

### 7.1 四极正交性审计 (2026-07-18)

| 对 | 正交性 | 验证 |
|----|:------:|------|
| 代数极 ⊥ 拓扑极 | ✅ | 6624≠3312 区分独立于 %144/%46 模运算 |
| 代数极 ⊥ GF9 极 | ✅ | CRT 投影处理 ℕ，GF9 极处理 GF(9) 共轭，范畴不同 |
| 代数极 ⊥ 几何极 | ✅ | CRT 模域 vs T6 格点域，范畴分离 |
| 拓扑极 ⊥ GF9 极 | ✅ | 6624 parity 是缠绕数，GF9 共轭是域自同构 |

**审计结论**：四极等价判定链全部闭合，无退化正交。

**待修订**：代数极判据需从「R₁₂ CRT」升级到「DC 结构 + 投影函子」。

---

## 八、零因子审计

### 8.1 R₁₂ 零因子

```agda
zero-divisor-2×6 : d2 *12 d6 ≡ d0  -- 2×6 = 0 (mod 12)
zero-divisor-3×4 : d3 *12 d4 ≡ d0  -- 3×4 = 0 (mod 12)
zero-divisor-4×3 : d4 *12 d3 ≡ d0  -- 4×3 = 0 (mod 12)
zero-divisor-6×2 : d6 *12 d2 ≡ d0  -- 6×2 = 0 (mod 12)
```

### 8.2 DC 无零因子

在 DuodecClock 里，`mulAlpha` 来自 GF(9)* 的子群 ⟨α⟩，是域子群的乘法，**没有零因子**。

R₁₂ 的零因子是**投影层外加结构**，不是本源的。

---

## 九、下一步工作

**⚠ 条目 3、4 已于 2026-09-10 核查关闭**（对应 §6.1 G1 / G4）—— 下个会话**勿重复评估**。

1. **P0**：修订 AlgebraicPoleUnified 头注释，与 DuodecClock 对齐
2. **P0**：修订 algebraic-chain-status 矛盾表述
3. **P2 · 已选定方向**：**R2 的「十二律置换表示」—— 须走本源侧形态**。把展示群八要素里的「时钟（迭代过程）」「归零（周期闭合）」从**等式语言**升级为**过程/轨道语言**。
   *正确形态（本源侧）*：`mixedOp^_ : ℕ → DuodecPoint → DuodecPoint` 参数化迭代 + 过程律 + **分量分解**（对齐 `DayanCore.agda:108 iter-decompose`）：
   `mixedOp^n (t , a) ≡ (iterate ⊕ n t , iterate mulAlpha n a)`；联合周期由**分量正交**给出 `lcm(3,4) = 12`。
   *现状缺口*：`mixedOp^12` 是硬编码 12 重组合（`DuodecClock.agda:406-407`），**无 ℕ-参数化迭代**，故「走 n 步」无法表述。
   *样板已在库内*：`DayanCore.agda:42-44 iterate` + `:172 dayan-joint-order-12` —— 本源侧参数化迭代的既有做法。
   ⚠ **红线（2026-09-10 更正）**：**禁止**把本方向表述为「下降为 C₁₂ 作用」或「`Action C12 (Fin 12)`」。
   `12-rigorous-type-theory.md:263-272` 定位 `toDuodec` 为**有损投影 / 截断操作**，其丢弃清单**恰好包含「时钟过程」与「归零机制」**——沿 `toDuodec` 走即走信息丢失方向，等于把「走钟」搬到已经丢掉走钟的地方，自相矛盾。
   另：块 1–6 的作用机器（`Action` / orbit-stabilizer / Burnside）是 **`FinGroup n` 索引的投影层工具**，要用须经 `C12 : FinGroup 12`（投影）⇒ **不搬进本源**；若做，只作投影层回归检查，不列入方向主线。
   决策与块分解见 `memory/direction-2026-09-dc-permutation-representation.md`。
4. **P2**：R1 理想格（(2),(3),(4),(6) 主理想与 CRT 素幂分解）
5. **P3**：R3 A₄ 阶 12 衔接（|A₄|=12 目前仍只见于注释与 `A4Representations` 的类大小 1+4+4+3；未做逐项核查）

## 十、傅里叶层更新 (2026-09-07)

DC 特征分解层已从"框架完成、求和部分待补充"推进到**完整闭环**:

- Z12Sys 载体 = ℚ(ζ₁₂) 真交换环 (*ᶻ-assoc/comm/distrib/middle4 全证)
- 特征同态性 (1728 refl)、正交性、自内积、对偶完备性
- **Parseval/Plancherel**: Σ_x|f(x)|² = (1/12)·Σ_k|f̂(k)|² (0 postulate 0 hole)

详见 [17-dc-fourier-analysis.md](17-dc-fourier-analysis.md)。
旧"求和部分待补充"表述已过时。谱定理 (对称矩阵对角化) 仍需 ℚ(ζ₁₂) 外载体, 仍未形式化。

