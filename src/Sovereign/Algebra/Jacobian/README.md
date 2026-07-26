# 大衍离散雅可比理论 — 形式化证明项目

> **核心定理：有限集上，全局函数表矩阵 det(M_F) ≠ 0 ⟺ F 双射（0 postulate）。**
>
> 离散是本质，连续是投影。大衍框架回到离散基座（GF(3)/GF(9)/T⁶ 环面），
> 用全局矩阵 + 鸽巢原理 + 三重防火墙，给出了"局部→全局"元问题的完备解答。

---

## 目录结构

```
src/Sovereign/Algebra/
├── Jacobian.agda                    综合入口
└── Jacobian/
    ├── jac_GF3.agda                 GF(3)² 反例 (形式导数 + 差分算子)
    ├── jac_Discrete.agda            三种"雅可比"的区分
    ├── jac_FrobeniusBlind.agda      GF(9)² 反例 (Frobenius 盲区 + 81点)
    ├── jac_Pigeonhole.agda          鸽巢原理 Fin 9→8 (REWRITE decode9)
    ├── jac_Matrix.agda              GF(3) 2×2 矩阵全理论 (7215行)
    ├── jac_Injectivity.agda         单射↔满射 (右逆 + pigeonhole)
    ├── jac_FunctionTable.agda       函数表矩阵等价性论证
    ├── jac_NMatrix.agda             9×9 函数表矩阵 (toTrit, 0 postulate)
    ├── jac_Conjecture.agda          离散 JC 陈述 + 实质定理
    ├── jac_DiscreteJC.agda          三层综合 + 连续统 JC 关系
    ├── jac_CRTSpectrum.agda         CRT 四极 × 矩阵谱
    ├── jac_4320DClosure.agda        729 点鸽巢 + 环面有界性
    ├── jac_EscapeAnalysis.agda      射影几何逃逸分析 (Alpöge 阻断) 🆕
    ├── jac_Algorithm.agda           算法规格
    ├── jac_Theorem.agda             最终定理
    ├── doc/                         理论文档 (12 篇)
    └── README.md                    本文件
```

## 编译状态

| 模块 | 行数 | postulate | 编译 |
|------|------|-----------|------|
| jac_GF3 | 324 | 0 | ✅ |
| jac_Discrete | 122 | 0 | ✅ |
| jac_FrobeniusBlind | 284 | 0 | ✅ |
| jac_Pigeonhole | 322 | 0 | ✅ |
| jac_Conjecture | 112 | 0 | ✅ |
| jac_Matrix | 7215 | 0 | ✅ |
| jac_Injectivity | 174 | 0 | ✅ |
| jac_CRTSpectrum | 606 | 0 | ✅ |
| jac_4320DClosure | 408 | 0 | ✅ |
| jac_FunctionTable | 131 | 0 | ✅ |
| jac_NMatrix | 166 | 0 | ✅ |
| jac_DiscreteJC | 324 | 0 | ✅ |
| jac_EscapeAnalysis | 127 | 0 | ✅ |
| jac_Algorithm | 79 | 0 | ✅ |
| jac_Theorem | 85 | 0 | ✅ |
| **合计** | **~10480** | **0** | **✅** |

## 三层雅可比强度

```
形式导数 det J (最弱, Frobenius 盲区)
  < 差分算子 det J_Δ (无盲区, 但仍为局部条件)
    < 函数表矩阵 det(M_F) (全局, 鸽巢完备)
```

| 层 | 判据 | GF(3)² 反例 | GF(9)² 反例 | 结论 |
|----|------|------------|------------|------|
| 1 | 形式导数 | F=(x,0): det=1 非双射 | F=(x,y+αy³): det=1 非双射 | ❌ 不充分 |
| 2 | 差分算子 | det=0 正确检测 | det=1+α≠0 仍非双射 | ❌ 不充分 |
| 3 | **函数表矩阵** | — | — | **✅ 充要条件** |

## 证明链

```
det(M_F) ≠ 0
  ⟺ 列互异 ∧ 无全零行     (函数表矩阵结构, jac_FunctionTable)
  ⟺ F 单射 ∧ F 满射        (行列性质, jac_NMatrix)
  ⟺ F 双射                 (鸽巢原理: pigeonhole-2 + surj→inj)
```

## 三重防火墙（阻断经典反例）

| 防火墙 | 内容 | 对 Alpöge 反例的裁决 |
|--------|------|---------------------|
| **几何闭包** | T⁶ 环面天然闭合，无射影无穷远 | 根逃逸机制不存在 |
| **代数共轭** | GF(9) Frobenius σ(x)=x³ 原生可见 | ℂ³ 排除复共轭的策略无法复制 |
| **描述完备** | 全局矩阵 M_F 精确捕获所有格点转移 | det(M_F)=0 直接暴露坍缩 |

## 关键定理索引

| 定理 | 文件 | 策略 |
|------|------|------|
| fermat3 | jac_GF3 | 3-case refl |
| σ-shift | jac_FrobeniusBlind | 9-case refl |
| frob-3to1 | jac_FrobeniusBlind | Σ-构造, 81点验证 |
| pigeonhole-2 | jac_Pigeonhole | Fin 9→8 + stdlib pigeonhole |
| surj→inj | jac_Injectivity | 右逆构造 + pigeonhole-2 |
| det-mul | jac_Matrix | 81-case refl |
| inverse-correct | jac_Matrix | GF(3) 逆元 + 伴随矩阵 |
| detNonzero↔bij | jac_NMatrix | toTrit + 列互异论证 |
| collapse→not-detnonzero | jac_EscapeAnalysis | 函数表矩阵列相同→det=0 |
| triple-closure-theorem | jac_EscapeAnalysis | 几何+代数+描述完备 ➜ Alpöge 阻断 |

### 七大千禧问题离散验证模块

| 问题 | 模块 | 定理 | refl |
|------|------|------|------|
| **YM** | jac_YM_DetMul | det-mul 6561-case + 质量间隙 det≠0 | 6838 |
| **Hodge** | jac_Hodge | dimℋ=dimH + Hodge分解 | 8 |
| **BSD** | jac_BSD_L3 | Weil 递推 t₁-t₁₀ | 18 |
| **Langlands** | jac_GL2_Ortho | GL₂(5760) 特征标正交性 | 3 |
| **PvsNP** | jac_PvsNP_Separation | Eval≢Invert 分离定理 | 9 |
| **RH** | jac_RH_FuncEq | 泛函方程 + Hasse界 + trace | 7 |

## 依赖

```
Jacobian (80 模块, ~15233 行, 0 postulate)
  ├── Sovereign.Base.Trit      (GF(3) 代数, 0 postulate)
  ├── Sovereign.Algebra.Duodecimal (Z/12Z CRT, 0 postulate)
  ├── Sovereign.Structology.T6     (T⁶ 729格点, 含 REWRITE)
  ├── Sovereign.Structology.A4Group (A₄ 群, 0 postulate)
  └── Sovereign.Physics.NSE        (NS 全域精确解, 12定理)
```

## 创建日期

2026-07-24 — 更新 2026-07-27 (七问题验收锁定)
