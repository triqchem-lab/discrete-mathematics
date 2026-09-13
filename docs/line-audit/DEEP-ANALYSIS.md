# 全库逐模块审计 — 深度分析报告

> 本报告是对 `INDEX.md` 与各目录记录文件的补充，聚焦"需关注"的模块：历史遗留、hole、postulate。
> 遍历范围：`src/` 下全部 502 个 `.agda` 模块（排除 `_build/`），逐行读取。

---

## 0. 全库概览

| 指标 | 数值 |
|------|------|
| 模块总数 | 502 |
| 总行数 | 119,086（代码 67,358 / 注释 34,955）|
| `refl` 出现次数 | 26,994 |
| `postulate` 总数 | 90（分布在 30 个模块）|
| hole `{!!}` / `{! !}` | 3（分布在 3 个模块）|
| 含 REWRITE 规则的模块 | 至少 2（T6、XuanwuAbsorption）|

---

## 1. 历史遗留目录识别（重要发现）

`src/` 下存在三组**早期文明层快照目录**，其 `module` 声明与 `src/Sovereign/` 下的正式模块**同名**，属于同一代码的旧版本：

### `01-electric-12d/`（2 模块，272 行）
| 文件 | module 声明 | 正式模块 | 状态 |
|------|------------|----------|------|
| `Base.agda` | `Sovereign.RootMath.Base` | `src/Sovereign/RootMath/Base.agda` | **重复** |
| `DigitalRoot.agda` | `Sovereign.RootMath.DigitalRoot` | `src/Sovereign/RootMath/DigitalRoot.agda` | **重复** |

差异：旧版 `OPTIONS` 仅 `--guardedness`，新版为 `--rewriting --guardedness`。

### `02-magnetic-24d/`（3 模块，545 行）
| 文件 | module 声明 | 正式模块 | 状态 |
|------|------------|----------|------|
| `ParityViolation.agda` | `Sovereign.Coupling.ParityViolation` | `src/Sovereign/Coupling/ParityViolation.agda` | **重复** |
| `SpinTwistor.agda` | `Sovereign.Coupling.SpinTwistor` | `src/Sovereign/Coupling/SpinTwistor.agda` | **重复** |
| `WuXing.agda` | `Sovereign.MetaStructure.WuXing` | `src/Sovereign/MetaStructure/WuXing.agda` | **重复** |

### `03-neutral-144d/`（6 模块，1390 行）
| 文件 | module 声明 | 正式模块 | 状态 |
|------|------------|----------|------|
| `CartanTorsion.agda` | `CartanTorsion`（非 Sovereign 前缀） | — | 独有（旧命名） |
| `Entanglement.agda` | `Sovereign.Coupling.Entanglement` | `src/Sovereign/Coupling/Entanglement.agda` | **重复** |
| `LossGain.agda` | `Sovereign.Coupling.LossGain` | `src/Sovereign/Coupling/LossGain.agda` | **重复** |
| `TQ10.agda` | `Sovereign.Coupling.TQ10` | `src/Sovereign/Coupling/TQ10.agda` | **重复** |
| `Zhonglv.agda` | `Sovereign.Coupling.Zhonglv` | `src/Sovereign/Coupling/Zhonglv.agda` | **重复** |
| `ZhonglvClosure.agda` | `Sovereign.Coupling.ZhonglvClosure` | —（已并入 ZhonglvPhaseSync/Zhonglv） | 独有（旧命名） |

**结论**：这 11 个文件是历史遗留，其 module 名与正式模块冲突。它们不在 `All.agda` 的 import 列表中（`All.agda` 导入的是 `Sovereign.*`，Agda 按 include 路径 `src` 解析时会命中 `src/Sovereign/` 下的正式模块）。这些目录是 `docs/` 中 `01-electric-12d`、`02-magnetic-24d`、`03-neutral-144d` 三个子目录的历史来源，属"文明层"早期命名遗留，建议后续归档或删除以免同名 module 歧义。

---

## 2. 三个 hole（未完成证明）逐一定位

### 2.1 `src/Sovereign/HoTT/CRTHarmonics.agda` L172
```agda
alignment-implies-standing-wave : ∀ steps → Aligned steps → StandingWave (steps * OMEGA0 % M)
alignment-implies-standing-wave s (isAligned aligned) = {!!}  -- 待 CRTFiberWinding 桥接
```
- **根因**：跨模块依赖缺口。注释自述："需证 Aligned → 落在 harmonic k 的纤维上，CRTFiberWinding（待完成）提供纤维结构 + T6Homotopy 提供同伦连续化"。
- **性质**：已知未完成，非隐藏 hole。

### 2.2 `src/Sovereign/Topology/HighDimClosure.agda` L132
```agda
convergenceTheorem :
  ∀ (s : HighDimView.State) →
  ∃ (λ n → T (isHolographicState (iterateEvolve n s)))
convergenceTheorem s = {! !}
```
- **根因**：高维闭合收敛定理（极限环面吸引子）尚未证。文件头显式声明 `--allow-unsolved-metas`，属有意保留的未完成证明。

### 2.3 `src/_rt.agda` L37（根目录草稿）
```agda
rt n@(ℕsuc (ℕsuc (ℕsuc _))) with ... | q | r | eq | q<n with stc (cts q) | rt q
... | sq | ihq =
  trans (cong (r +_) (trans (eval-*3 ...) (cong (3 *_) {!!}))) eq
```
- **根因**：三进制 Vec roundtrip 证明 `stc (cts n) ≡ n` 的归纳步骤中间步骤未填。属未跟踪草稿（`module _rt`），不在 `All.agda` 内。

---

## 3. 90 个 postulate 的分类分析（30 个模块）

全库 90 个 postulate 分四类，其中前两类按 AGENTS.md 约定属"语义完备性设计"与"合法公理桥"，不计入零 postulate 宣称范围：

### 类别 1 — REWRITE 规则配套（约 6 个，语义完备性设计）
Agda REWRITE 机制要求规则绑定一条等式声明；当等式是对 `div-helper`/`mod-helper` 的大数展开（类型检查 OOM 的根源）时，直接 postulate 后标记 `{-# REWRITE #-}` 让它成为归一化规则：
| 模块 | postulate | 说明 |
|------|-----------|------|
| `Structology/T6.agda` | `div3k` / `mod3k` / `gf3Toℕ-A4-inv` | 4320D 归约，替代 mod-helper 展开；`gf3Toℕ-A4-inv` 带 `{-# REWRITE #-}` |
| `Structology/XuanwuAbsorption.agda` | `mod46k` / `div46k` / `mod-a+598` | 46 周期归一化 REWRITE 规则 |

### 类别 2 — 轨道 B 物理锚定登记（合法公理，注释标注"genuine bridge"）
这些 postulate 前均有注释 `[轨道 B 物理锚定登记] Constitution/PhysicalAssumptions.agda ② 类: 实验/几何锚定, 合法公理 (genuine bridge), 不计入任何 "0 postulate" 宣称范围`：
| 模块 | 数量 | 代表 |
|------|------|------|
| `RootMath/EnergyGap.agda` | 7 | `energyGapSquared`（能隙²=3）、`sqLenIs3`、`halfGapExact`、`thresholdIsHalfGap` |
| `Coupling/CartanTorsion.agda` | 8 | `globalCurvatureSum`、`tritState`/`updateTrit`、`CartanGeometryConstitutional` |
| `Coupling/Zhonglv.agda` | 3 | `chernInvariant`、能隙定点编码（56632/65536≈√3/2） |
| `Coupling/Entanglement.agda` | 3 | `trappest1Instance`（TRAPPIST-1 共振）、`EntanglementDefinition` |
| `Physics/QuartzPhonon.agda` | 3 | `saha-equilibrium-anchored`、`percolation-anchored`、`ρ-evolution-anchored` |
| `Structology/Aether.agda` | 2 | `aetherEnergyGapIsSqrt3`、`aetherNotContinuous` |
| `Structology/Platonics.agda` | 3 | `tetrahedralCell`、`s2_to_torus_ratio`（R:r=144:46） |
| `Coupling/ZhonglvPhaseSync.agda` | 1 | `zhonglvConstitutionalClause` |
| `Density/Resonance.agda` | 1 | `resonanceLegal` |
| `Format/CRT.agda` | 1 | `crtSec-restricted`/`crtRet-restricted` |
| `Engine/QsUpdate.agda` | 1 | `pack5∘unpack5`/`unpack5∘pack5`（5-trit 打包往返） |

### 类别 3 — 范畴分离声明（`¬ (X ≡ Y)`，防连续统污染）
| 模块 | postulate | 说明 |
|------|-----------|------|
| `Coupling/CartanTorsion.agda` | `notCartanAsBase` / `notConnectionAsGauge` / `notCurvatureAsField` | 卡当几何 ≠ 量子力学基底等 |
| `Coupling/Entanglement.agda` | `noActionAtDistance` | 纠缠 ≠ 超距作用 |
| `Coupling/TQ10.agda` | `sovFormatImmutable` / `noFloatInBlock` | 主权格式不可变、块内禁浮点 |
| `Constitution/WindingAsymmetry.agda` | `onlyLegalLanguage` | 仅合法语言 |
| `02-magnetic-24d/ParityViolation.agda`（旧版） | `noSpatialReflection` | 无空间反射 |

### 类别 4 — 待证/遗留类型定义（真正的欠账，多集中在旧版 01/02/03 目录）
| 模块 | postulate | 说明 |
|------|-----------|------|
| `RootMath/Base.agda` | `stableRootConstraint` | 数字根稳定约束 |
| `Coupling/TQ10.agda` | `updatePhaseBias`/`updateChernGuard`/`updateWuxingMask` | Word8 状态更新 |
| `Structology/MagicSquareM4.agda` | eigenvector16⁺ | M₄-16I 满秩，ℤ⁴ 无解，ℝ 上 λ=2√10 |
| `02-magnetic-24d/SpinTwistor.agda`（旧版） | 9 个 | `notElectronSpin12`、`spinTwistorResetClause` 等 |
| `03-neutral-144d/*`（旧版） | 约 30 个 | 卡当挠率/纠缠/损益链/仲吕等旧快照 |

**要点**：90 个 postulate 中的大多数集中在**旧版 01/02/03 目录**（约 40 个），这些目录本身已被 `src/Sovereign/` 正式模块取代；正式 `Sovereign/` 树下的 postulate 几乎全部属于类别 1（REWRITE 配套）与类别 2（轨道 B 合法锚定），均有注释背书。真正无注释背书的"裸 postulate"仅 `RootMath/Base.stableRootConstraint`、`Coupling/TQ10` 三个 Word8 更新函数、`Structology/MagicSquareM4` eigenvector 等少量。

---

## 4. 结论与建议

1. **遍历完整性**：502 个模块全部逐行读取并记录，无遗漏。
2. **历史遗留**：`01-electric-12d/`、`02-magnetic-24d/`、`03-neutral-144d/` 三目录 11 个文件为旧版快照，与 `Sovereign/` 正式模块同名，建议归档。
3. **未完成证明**：3 个 hole 均有明确注释或属草稿，非隐藏假设。
4. **postulate 现状**：90 个 postulate 大多有"轨道 B 合法公理"或 REWRITE 配套背书，仅少量裸 postulate 需后续关闭。
