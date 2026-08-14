# 大衍离散雅可比理论 — 形式化证明项目

> **核心定理：有限集上，全局函数表矩阵 det(M_F) ≠ 0 ⟺ F 双射（0 postulate）。**
>
> 离散是本质，连续是投影。大衍框架回到离散基座（GF(3)/GF(9)/T⁶ 环面），
> 用全局矩阵 + 鸽巢原理 + 三重防火墙，给出了"局部→全局"元问题的完备解答。

---

## 目录结构（2026-08 P0-4 同步：实际 15 模块）

```
src/Sovereign/Algebra/Jacobian/
├── jac_GF3.agda                 GF(3)² 反例 (形式导数 + 差分算子)
├── jac_Discrete.agda            三种"雅可比"的区分
├── jac_Pigeonhole.agda          鸽巢原理 Fin 9→8 (REWRITE decode9)
├── jac_Matrix.agda              GF(3) 2×2 矩阵全理论 (7215 行)
├── jac_Injectivity.agda         单射↔满射 (右逆 + pigeonhole)
├── jac_FunctionTable.agda       函数表矩阵 M_F 等价性论证
├── jac_NMatrix.agda             9×9 函数表矩阵 (NoZeroRow ∧ ColDistinct, 0 postulate)
├── jac_GF9Matrix.agda           GF(9) 矩阵与 Frobenius 共轭
├── jac_CRTDet.agda              CRT 行列式分解定理 (拱顶石, 对齐 dype Compute/Det.hs)
├── jac_CRTSpectrum.agda         CRT 四极 × 矩阵谱
├── jac_DiscreteJC.agda          三层综合 + 连续统 JC 关系
├── jac_AutT6.agda               T⁶ 自同构群
├── jac_LieGroup.agda            Aut(T⁶/GF(9)) 李群结构
├── jac_LinearAlgebra.agda       有限域线性代数基元
├── jac_Topology.agda            拓扑不变量 (dim H_k = nullity − rank)
├── doc/                         理论文档
└── README.md                    本文件
```

## 编译状态（2026-08 实测，全部 exit=0, 0 postulate）

| 模块 | 行数 | postulate | 编译 |
|------|------|:---------:|------|
| jac_GF3 | 324 | 0 | ✅ |
| jac_Discrete | 122 | 0 | ✅ |
| jac_Pigeonhole | 331 | 0 | ✅ |
| jac_Matrix | 7215 | 0 | ✅ |
| jac_Injectivity | 202 | 0 | ✅ |
| jac_FunctionTable | 116 | 0 | ✅ |
| jac_NMatrix | 173 | 0 | ✅ |
| jac_GF9Matrix | 164 | 0 | ✅ |
| jac_CRTDet | 112 | 0 | ✅ |
| jac_CRTSpectrum | 606 | 0 | ✅ |
| jac_DiscreteJC | 324 | 0 | ✅ |
| jac_AutT6 | 139 | 0 | ✅ |
| jac_LieGroup | 231 | 0 | ✅ |
| jac_LinearAlgebra | 76 | 0 | ✅ |
| jac_Topology | 159 | 0 | ✅ |
| **合计** | **~10294** | **0** | **✅** |

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
  ⟺ 列互异 ∧ 无全零行     (函数表矩阵结构, jac_FunctionTable / jac_NMatrix)
  ⟺ F 单射 ∧ F 满射        (行列性质, jac_NMatrix 四方向已证)
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
| pigeonhole-2 | jac_Pigeonhole | Fin 9→8 + stdlib pigeonhole |
| surj→inj | jac_Injectivity | 右逆构造 + pigeonhole-2 |
| det-mul | jac_Matrix | 81-case refl |
| inverse-correct | jac_Matrix | GF(3) 逆元 + 伴随矩阵 |
| detNonzero↔bij | jac_NMatrix | toTrit + 列互异论证 (四方向已证) |
| crt-det 分解 | jac_CRTDet | CRT 环直积保 det (Duodec π3/π4 环同态) |

## 七大千禧问题离散验证模块（2026-08 P0-4 同步）

原 README 在此列出的 6 个 `jac_*` 七问题模块已迁移/独立成 Problem/ 目录下的正式模块
（07-27 拆分 Jacobian 77→24, 53 模块入 Problem/ 七目录并去除 jac_ 前缀），本目录不再重复：

| 问题 | 实际位置 |
|------|---------|
| **YM** | `Problem/YangMills/YM_DetMul.agda`（det-mul 6561-case + 质量间隙 det≠0） |
| **Hodge** | `Problem/Hodge/Hodge.agda`（dimℋ=dimH + Hodge 分解） |
| **BSD** | `Problem/BSD/BSD.agda`（Weil 递推 t₁-t₁₀；另有 BSD9/BSD_GF27/BSD_GF243） |
| **Langlands** | `Problem/Langlands/Langlands.agda`（GL2 特征标正交性） |
| **PvsNP** | `Problem/PvsNP/PvsNP_L15.agda` + `GF27Separation.agda`（Eval≢Invert 分离） |
| **RH** | `Problem/Riemann/` 统一居（8 模块, 0 postulate）: `AlgGeom` / `FrobeniusBlind` /
  `Galois` / `RH` / `Sheaf` / `Variety` / `WeilRH` / `WeilRigidity`
  （泛函方程 + Hasse 界 + trace; 07-27 拆分自 Jacobian, 已去 jac_ 前缀） |

## 依赖

```
Jacobian (15 模块, ~10294 行, 0 postulate)
  ├── Sovereign.Base.Trit      (GF(3) 代数, 0 postulate)
  ├── Sovereign.Algebra.Duodecimal (Z/12Z CRT, 0 postulate)
  ├── Sovereign.Structology.T6     (T⁶ 729 格点, 含 REWRITE)
  ├── Sovereign.Structology.A4Group (A₄ 群, 0 postulate)
  └── Sovereign.Physics.NSE        (NS 全域精确解, 12 定理)
```

## 创建日期

2026-07-24 — 更新 2026-08（P0-4: 目录/编译表/七问题指针与实际代码对齐）
