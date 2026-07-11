# Agda 编译器 P0-P3 数学证明规划

> 基于 Sovereign 律算合一框架，为 Agda #8611 PR 的后续工作提供数学基础

## 状态总览

| 任务 | 数学模块 | 状态 | 备注 |
|------|---------|------|------|
| P1a | `Sovereign.Compiler.TelescopeAlgebra` | 📐 框架已搭建 | De Bruijn 坐标的形式化验证 |
| P0 | `Sovereign.Compiler.CRTOrthogonal` | 📐 框架已搭建 | CRT-HDU 正交分解 |
| P2 | `Sovereign.Compiler.TranspCRT` | 📐 框架已搭建 | CRT-aware transp 框架 |
| P3 | (待建) | ⏳ 待启动 | 极限环 canonicity 证明 |

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

## P3: CanonicityProof

**目标:** 用极限环框架证明索引族的规范性

**未开始** — 需要:
1. 形式化"极限环"在离散重写系统中的定义
2. 证明 indexed HITs 的所有 closed terms 归约到 canonical form
3. 将相位对齐点 (6624) 编码为不动点定理

**难度:** ⭐⭐⭐⭐⭐⭐ — 博士论文级别

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
