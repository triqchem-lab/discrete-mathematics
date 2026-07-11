# M5: Agda PR #3733 与 Sovereign 框架的交叉映射

## 汇接全景

```
  Agda #3733 (编译器工程)              Sovereign (数学基础)
  ════════════════════                ════════════════════

  L1: 覆盖率检查 + 投影生成    ←──→  CRT 正交分解 (Z/M ≅ Z/p × Z/q)
       makeTau Δ 参照系              FULL_TOUR = 6624
       isPathCons guard              损益交替 [1,2,1,2,1,2]

  L2: Kan 纤维化条件            ←──→  6624 相位对齐定理 (闭合定理)
       transp 子句归约                Christoffel 螺旋闭合
       望远镜膨胀 (nctel > 1)         T⁶ 环面缠绕数重映射

  L3: 索引族单值语义            ←──→  陈数 C=±2 拓扑守恒
       Canonicity 规范性              能量间隙 Δ²=3
       Logical Relations              π_H = 144/46 全息不变量
```

## 逐层详细映射

### L1 工程层 (已解决 ✅)

| Agda 实现 | Sovereign 原理 | 状态 |
|----------|---------------|------|
| `digestUnifyLog` + `DInjectivity` | CRT 双模投影 (Z/M ≅ Z/65536 × Z/177147) | ✅ PR 已提交 |
| `makeTau` 的 `nTarget = nOld + nctel - 1` | Δ 参照系迁移 (时间先于空间) | ✅ |
| `isPathCons` guard | Z₂ 奇偶选择 (损益交替) | ✅ |
| `hasErasedConstructorFields` | GF(3) 能隙 Δ=√3 (模态保护) | ✅ |
| `extraCxt` open context | Christoffel 螺旋测地提升 | ✅ |

### L2 计算层 (当前研究前沿)

| 待解决问题 | Sovereign 方向 | 关键模块 |
|-----------|---------------|---------|
| Kan 纤维化自动边界闭合 | 6624 相位对齐闭合定理 | `HoTT/PhaseAlignment6624.agda` |
| CRT 合成路径 (HDU embedding) | 双振子拍频同步 (harmonic-phase-preserving) | `HoTT/CRTHarmonics.agda` |
| JIT-style path synthesis | Christoffel 螺旋的损益交替节拍 | `Structology/WuXingTransition.agda` |
| 多字段构造子 (nctel > 1) 遍历 | T⁶ 环面 FULL_TOUR 遍历 | `Structology/MagicSquare144.agda` |

**关键定理**: `HoTT/PhaseAlignment6624.agda`
- `alignmentIdentity`: FULL_TOUR ≡ 144 × 46 (对齐恒等式)
- `closureTheorem`: ∀n, (n × FULL_TOUR) % 144 ≡ 0 × (n × FULL_TOUR) % 46 ≡ 0
- `phaseResyncAxiom`: x % FULL_TOUR ≡ (x % 144) + 144 × ((x / 144) % 46)

### L3 元理论层 (长期方向)

| 待解决问题 | Sovereign 方向 | 关键模块 |
|-----------|---------------|---------|
| 索引族单值语义 | T⁶ 环面陈数 C=±2 拓扑守恒 | `HoTT/ChernClass.agda` |
| Canonicity 保证 | 能量间隙 Δ²=3 模态分离 | `RootMath/EnergyGap.agda` |
| 规范性证明 | π_H = 144/46 全息不变量 | `Structology/HolographicPi.agda` |
| Logical Relations 模型 | A₄ 群的 4 个不可约表示 {3,1,1′,1″} | `Structology/A4Representations.agda` |

## 研究路线图

```
  现在 ────────────────────────────────────────────→ 未来

  ✅ L1 完成           📐 L2 进行中            🔮 L3 方向
  │                    │                       │
  │  makeTau Δ参照系    │  6624 相位对齐定理      │  T⁶ 陈数守恒
  │  isPathCons        │  Kan 边界闭合证明       │  Δ²=3 模态分离
  │  erased boundary   │  HDU+CRT 合成验证       │  A₄ 表示论
  │                    │                       │
  ▼                    ▼                       ▼
  PR #8611             本地数学库              未来 PR
  (CI 审核)            (PhaseAlignment6624)    (L2/L3 完整体)
```

## Sovereign 模块与 Agda PR 文件对应

| Sovereign 模块 | Agda PR 文件 | 概念映射 |
|---------------|-------------|---------|
| `Structology/Winding.agda` | `LeftInverse.hs` (makeTau) | 缠绕数 → nTarget 计算 |
| `HoTT/PhaseAlignment6624.agda` | `LeftInverse.hs` (CRT 合成) | 6624 对齐 → τ 的缩放 |
| `HoTT/CRTHarmonics.agda` | `Unify.hs` (HDU thunk) | 谐波同步 → HDU 不求值 |
| `RootMath/EnergyGap.agda` | `Unify.hs` (erased check) | Δ²=3 → modality 边界 |
| `Structology/A4Representations.agda` | `Types.hs` (UnifyOutput) | A₄ 不可约表示 → 类型分解 |
| `Structology/T6.agda` | `Substitute.hs` (conApp) | T⁶ 环面 → 替换拓扑 |
