# 上游迁移补丁说明（bridge → src）

本目录的模块是**桥**，不修改上游跟踪树。本文件列出每项应如何迁进 `src/Sovereign/**`。

## 1. `DigitalRootClassic.agda` → `src/Sovereign/Foundation/DigitalRoot.agda`

**现状**：上游只有 `digitalRoot n = n % 9`（9 ↦ 0），无经典数字根、无幂等/周期。

**建议改动**：
- 新增 `classicRoot : ℕ → ℕ`（`0 ↦ 0`；`suc k ↦ suc (k % 9)`）。
- 迁入本模块的 6 个枢纽引理（`mod9-period` / `mod9-step` / `mod9-suc-cases` / `mod9-suc-eq9` /
  `mod9-step-value` / `mod9-step-nonzero`）与 5 条主定理（`classicRoot-nine` / `digitalRoot-nine` /
  `classicRoot≡mod9` / `classicRoot-idem` / `classicRoot-period`）。
- 保持 `digitalRoot` 原样（破坏性变更需 MAJOR），新增经典版即可；两者关系由 `classicRoot≡mod9` 给出。

**验证**：`agda --guardedness -i src -i <stdlib> src/Sovereign/Foundation/DigitalRoot.agda` 应 exit 0。

## 2. `DayanNatFix.agda` → `src/Sovereign/Algebra/GroupTheory/{DayanState,DayanCorrect}.agda`

**现状**：`DayanState.dayan-step` 用 `(q·lt) ∸ lb` 且 `乘率 = 定 ∸ lt`；`DayanCorrect` 三义务只有类型。
实测：m≤60 的 1101 组互素对中仅 22.6% 给出模逆；(奇=3,定=5) 得乘率 5，`3·5 ≡ 0`。

**建议改动**：
- 把 `dayan-step` 改为修正形：`lt' = (lb + 定 ∸ ((q·lt) % 定)) % 定`，`lb' = lt`，`乘率 = lt`。
- 把 `DayanCorrect` 的三义务类型改为已证定理（可直接引用本模块的 `init-invariant` /
  `step-invariant` / `terminate-correct` / `dayan-correct`，或移入）。
- 保留原版定义（改名 `dayan-step-legacy`）以便本模块的反例定理继续成立。

⚠ **未含**：整术终止性（`rt` 严格递减，上游 roadmap S-D3）仍缺，不要宣称已闭合。

## 3. `NSE6Axis.agda` → `src/Sovereign/Application/Problems/NavierStokes/NSEOnT6.agda`

**现状**：`C3 = Fin 3` 只有 3 个轴，`shiftAt`/`div`/`grad` 只覆盖 x₁,x₂,x₃；模块头自报 Q5 缺陷。

**建议改动**：
- `Axis6 = Fin 6`，`shiftAt` 6 个 case，`div`/`grad` 每分量对应自己的轴（i ↦ i）。
- 迁移 `div-grad6`（仍 `refl`）与 `ns-step6-preserves-incompressible`（**逐场版**；上游的
  全局前提 `∀ f x → laplacian f x ≡ T₀` 可满足性为假，对应条件式定理是空洞的）。
- 一并迁入判别引理 `laplacian6≢laplacian3Replica` / `div6≢div3Replica` / `laplacian6-not-identically-zero`
  —— 它们证明「`refl` 只证三处定义自洽，不证轴分配正确」。

⚠ **未含**：`adv6` 对流项、离散 Leray 投影存在性、Δ₆ 秩/核维数形式化。

## 4. `RotBridge.agda` / `HopfSpinLift.agda` → `src/Sovereign/Algebra/GroupTheory/`

**现状**：上游 `PhaseSubgroup.rot` 是「乘 α」的群作用，无矩阵实现；`HopfConstruction` 的 A₄ 作用无 4 阶元。

**建议改动**：
- 迁入 `Rot : ⟨α⟩ → ⟨R⟩`（GF(3) 矩阵，`R = [[0,2],[1,0]]`）与 `Rot-hom`（16 refl）/`Rot-injective`/
  `R²≡2I`/`R⁴≡I`/`det R ≡ 1`（⇒ R ∈ SL(2,3) = 2A₄）。
- 迁入 `HopfSpinLift`：`SpinTotal = TotalSpace × GF(3)²`，`phaseAct`，`phaseAct⁴≡id-inst`
  （实例化 `g₀ = A4.Flip zero`，**无参数假设**），`phase-equivariant`（保 A₄ 轨道）。

## 通用纪律

- 上游每个文件改完必须在**上游编译链**下 exit 0，0 postulate / 0 hole；
- 本目录模块的 `{-# OPTIONS --rewriting --guardedness #-}` 是必需的（上游 import 会被 `--rewriting` 污染）；
  命令行仍不加 `--rewriting`；
- 迁移引用关系：本目录模块互相独立（除 `HopfSpinLift` import `RotBridge`），可单独迁。

## 5. `Ring3pow11.agda` → `src/Sovereign/Algebra/`（新增环模块）

**现状**：`Algebra/Jacobian/HenselMod177147.agda` 只处理 x²≡1 的根，没有 Z/3¹¹ 环律。

**建议改动**：
- 迁入 `toℕ`/`repr`（小端）与互逆定理、`add`/`mul`（值语义）与交换/结合/单位/逆/分配律。
- 配套 oracle：`bridge-from-sov-math/oracle_ring_z3_11.py`（全域 177147 双射 + 729² 值语义 + 20000 三元组环律）。
- 若要给 ABI 的**按位** ring 算法做背书，需补「按位进位算法 ≡ 值语义」的一致性定理（**未做**）。

## 6. 交付状态一览

| 模块 | 上游目标 | 状态 |
|---|---|---|
| `Modu.agda`-类（无） | — | — |
| `DigitalRootClassic.agda` | `Foundation/DigitalRoot.agda` | ✅ 待迁移 |
| `DayanNatFix.agda` | `Algebra/GroupTheory/{DayanState,DayanCorrect}.agda` | ✅ 待迁移（终止性仍缺） |
| `NSE6Axis.agda` | `Application/Problems/NavierStokes/NSEOnT6.agda` | ✅ 待迁移（adv6/Leray 未做） |
| `RotBridge.agda` + `HopfSpinLift.agda` | `Algebra/GroupTheory/` | ✅ 待迁移 |
| `Ring3pow11.agda` | `Algebra/`（新增） | ✅ 待迁移（按位算法一致性未做） |
