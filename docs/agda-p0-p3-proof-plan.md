# Agda 编译器 P0-P3 数学证明规划

> 基于 Sovereign 律算合一框架，为 Agda #8611 PR 的后续工作提供数学基础
>
> **更新 (2026-08)**:
> - P3 状态由「⏳ 待启动」改为「**平替路线已闭合**」——dype/DiscreteCCHM（见 P3 节），
>   连续 CCHM 规范性不再列为本规划任务。
> - 本规划的 `Sovereign/Compiler/` 模块路径已被实际形式化取代：
>   `Structology/QuantumBridge.agda` §12/§17（`crt-size-decomposition`、
>   `roundtrip-general`、`MakeTauSize`、`ThreeSegment`），对应关系见
>   `docs/agda-3733-injectivity-deep-analysis.md` §5。

## 状态总览

| 任务 | 数学模块 | 状态 | 备注 |
|------|---------|------|------|
| P1a | `Sovereign.Compiler.TelescopeAlgebra` | 📐 框架已搭建（实现在 QuantumBridge §17） | De Bruijn 坐标的形式化验证 |
| P0 | `Sovereign.Compiler.CRTOrthogonal` | 📐 框架已搭建（实现在 QuantumBridge §12） | CRT-HDU 正交分解 |
| P2 | `Sovereign.Compiler.TranspCRT` | 📐 框架已搭建 | CRT-aware transp 框架 |
| P3 | `DiscreteCCHM` + dype Dayan 内核 | ✅ 平替路线已闭合 | 离散 boundedComputation 已证（见 P3 节） |

## P1a: TelescopeAlgebra

**目标:** 形式化验证 `makeTau` 的 De Bruijn 坐标计算

**已建立:**
- `TelescopeParams` — 望远镜参数化 (nGamma, nctel, neqs)
- `sizeΓ` / `sizeΔ` — 望远镜大小公式
- `tauListLength` — tauList 三段拼接的长度验证
- `Retract` — ρ[τ] = id 的形式化
- `leftInvDimension` — leftInv 的定义域验证

**待完成 (postulate → proof):**
- `expansion-theorem`: nctel + |Γ| ≡ |Δ| + 1
- `tauList-length-valid`: tauList 长度 = |Δ|
- `leftInv-dimension-correct`: leftInv 维数 = nGamma + 2 + neqs

**难度:** ⭐⭐ — 基本的自然数等式, 需要 +-comm, +-assoc, ∸ 引理

## P0: CRTOrthogonal

**目标:** 证明 CRT 正交分解在望远镜上的正确性

**已建立:**
- 正交维度: `indexDimension`, `fieldDimension`, `residualDimension`
- `CRTSpectralProjection` — 三段投影算子
- `CRTTelescopeIsomorphism` — CRT 同构 M ≅ P + Q

**待完成:**
- `CoprimeSegments` 的交不重叠证明
- `crt-theorem-Δ`: 投影后重建 = 恒等

**难度:** ⭐⭐⭐ — 需要将已证明的 CRT (Sovereign.Format.CRT) 适配到望远镜上下文

## P2: TranspCRT

**目标:** 桥接 L1 (injectivity) 到 L2 (transp 子句生成)

**已建立:**
- `TranspClause` — transp 子句的抽象
- `InjectivityAsCRT` — 注入性作为 CRT 往返
- `LimitCycleAlignment` — 极限环收敛框架
- `BridgeL1toL2` — L1→L2 桥接

**待完成:**
- `crt-roundtrip`: 投影后重建 = 定义性相等
- `transp-equivalence`: CRT 推导的 transp ≡ 定义性 transp
- `convergence`: 所有轨道收敛到不动点

**难度:** ⭐⭐⭐⭐ — 需要 Coverage/Cubical 的 transp 生成语义的形式化

## P3: CanonicityProof → dype 平替路线（2026-08 更新：已闭合）

**原目标 (2026-07):** 用极限环框架证明索引族的规范性。当时标「未开始」：
1. 形式化"极限环"在离散重写系统中的定义
2. 证明 indexed HITs 的所有 closed terms 归约到 canonical form
3. 将相位对齐点 (6624) 编码为不动点定理

**当前事实：** 连续 CCHM 规范性（第 2 步）在用户层无法闭合——定义性归约需内核
支持。dype（大衍 DY-PE，Agda 内核平替）把命题**替换**为有限域有界收敛，已闭合：

| 部件 | 状态 | 代码 |
|------|------|------|
| `boundedComputation`：Fin 6624 有界收敛到规范形（= CCHM strong normalization 的离散替代） | **已证**（见证 `FULL_TOUR , fullTour-alignment p`） | `Sovereign/HoTT/DiscreteCCHM.agda` |
| `shift-FULL_TOUR-id`、`discreteKan`（Kan filler 构造） | 已证（`[m+kn]%n≡m%n`、refl） | 同上 |
| 类型级规范形（Fin 144×46 基底，规范形由类型保证，0 postulate） | 已证（`fullTour-align` 等） | `Sovereign/HoTT/CanonicityAlignment.agda` |
| 三极等价判定 + 4320D 规范形计算 + O(1) CRT 查表 | 已实现 + Hspec 穷举（`forall729`） | `dype/src/Dayan/Kernel/Conversion.hs`、`Compute/CRT.hs` |
| CCHM canonicity ↔ boundedComputation 对应关系 | 设计文档明示 | `/data/work/docs/wiki/20-discrete-cchm-bridge.md` |

**原三步的落点：** 第 1 步（极限环离散重写定义）= `DiscreteCCHM` 的
`iterTransp`/`norm`；第 3 步（6624 不动点）= `fullTour-alignment`；第 2 步
（indexed HITs 闭项归约）属连续 CCHM，由 dype 平替而非证明。

**剩余（占位，不影响已闭合部分）：** `DiscreteCCHM` 3 个 postulate——
`shift-additive`（`%` 幂等性阻塞定义性相等，T6 REWRITE 同款模式）、
`discreteGlue`、`discreteCanonicity`（v6.0 连续化闭合用）。另按 wiki 20：
`discreteUA` 因 `norm` 非单射（729→6624 满射）引入矛盾而移除。

**难度（原评级 ⭐⭐⭐⭐⭐⭐ 博士论文级）：** 仅适用于连续 CCHM 版——
dype 不主张它，替换后的离散命题已证。

## 文件结构

```
src/Sovereign/Compiler/
├── All.agda                  ← 总入口
├── TelescopeAlgebra.agda     ← P1a: 望远镜代数
├── CRTOrthogonal.agda        ← P0: CRT-HDU 正交分解
└── TranspCRT.agda            ← P2: CRT-aware transp
```

## 与 Agda PR 的对应

| 数学证明 | Agda 源码 | 作用 |
|---------|---------|------|
| `TelescopeAlgebra.expansion-theorem` | `LeftInverse.hs:600-602` nTarget = nOld + nctel - 1 | 验证公式 |
| `TelescopeAlgebra.tauList-length-valid` | `LeftInverse.hs:603-607` tauList concat | 验证拼接 |
| `CRTOrthogonal.decomposition-holds` | `LeftInverse.hs:618-622` Telescope layout | 验证布局 |
| `TranspCRT.crt-roundtrip` | `LeftInverse.hs:634-639` retract condition | 验证往返 |
| `TranspCRT.convergence` | `Substitute.hs:155-163` fieldNotFound | 验证收敛 |
