# M3: 概念连通图 (Concept Graph)

> **更新** — 反映 502 模块 / 119,086 行的当前概念结构。
> 更新时间: 2026-08-20 (北京时间)

---

## 1. 核心数学对象及其连接

```
          GF(3) [Base/Trit]
           │
     ┌─────┼─────────┐
     ↓     ↓         ↓
   GF(9)  Fin 3    Z/3 加法
     │              │
     ├──→ ⟨α⟩(4阶) ─┼→ DuodecClock(12阶交换群)
     │              │
     ├──→ GF9Star(8阶循环群)
     │
     ├──→ T⁶ 环面 [Structology/T6]
     │     ├──→ Winding(缠绕数)
     │     ├──→ A₄ 群作用
     │     └──→ HoTT 同伦
     │
     ├──→ Jacobian [Algebra/Jacobian/*]
     │     ├──→ jac_GF3 → jac_GF9Matrix
     │     ├──→ jac_Pigeonhole → jac_Injectivity
     │     └──→ jac_Topology → jac_LieGroup
     │
     └──→ Holographic [Algebra/Holographic/*]
           ├──→ 4320D → 4320DClosure
           └──→ Theorem → Conjecture
```

---

## 2. 概念域映射

### 2.1 代数域

| 概念 | 核心模块 | 连接到 |
|------|----------|--------|
| **GF(3)** | Base/Trit | → GF(9), Fin 3, Z/3 |
| **GF(9)** | Algebra/GF9 | → Duodecimal, Jacobian, 所有 Problem/ |
| **GF(27)** | Algebra/GF27 | → GF81, Problem/PvsNP |
| **GF(81)** | Algebra/GF81 | → GF243, Problem/BSD |
| **GF(243)** | Algebra/GF243 | → Problem/BSD_GF243 |
| **GF(729)** | Algebra/GF729 | → 顶层有限域 |
| **Z/12** | Algebra/Duodecimal | → DuodecClock, 十二律 |
| **A₄** | Structology/A4Group | → Burnside, 表示论, Problem/Langlands |
| **二元四面体群** | Structology/BinaryTetrahedral | → 表示论, 不可约性 |

### 2.2 几何拓扑域

| 概念 | 核心模块 | 连接到 |
|------|----------|--------|
| **T⁶ 环面** | Structology/T6 | → Winding, HoTT, Physics |
| **射影几何** | Geometry/ProjectiveCore | → 4320D G-轨道 |
| **共形几何** | Geometry/ConformalCore | → 1458 轨道 |
| **环面几何** | Geometry/TorusGeometry | → Fourier, Geodesic |
| **陈类** | HoTT/ChernClass | → ChernConservation, ChernEulerLadder |

### 2.3 物理域

| 概念 | 核心模块 | 连接到 |
|------|----------|--------|
| **电磁场** | Physics/DiscreteEMCore | → EMField, Maxwell, EMField3D |
| **量子力学** | Quantum/Foundation | → NoCloning, Measurement |
| **热力学** | Physics/EntropySpin* | → 6 个 EntropySpin 子模块 |
| **相对论** | Physics/DiscreteLagrangian | → Lagrangian3D, Hamiltonian |

### 2.4 千禧年问题域

| 问题 | 核心模块 | 依赖链 |
|------|----------|--------|
| **BSD** | Problem/BSD/* (11) | GF81 → EllipticComplex → BSD_L3 |
| **Hodge** | Problem/Hodge/* (8) | ChainComplex → Hodge(分解) / Hodge_L3(猜想) |
| **P vs NP** | Problem/PvsNP/* (11) | GF27Separation → Complexity3 |
| **Riemann** | Problem/Riemann/* (9) | ZetaFunctional → WeilRH |
| **Yang-Mills** | Problem/YangMills/* (11) | WilsonLoop → YM_SpectralGap |
| **Langlands** | Problem/Langlands/* (6) | GL2TestVectors → Langlands_L15 |
| **Kakeya** | Problem/Kakeya/* (4) | KakeyaGF3 + KakeyaGF9 → Pathology |
| **Navier-Stokes** | Problem/NavierStokes/* (3) | NSRegularity → NSVortex |

---

## 3. 概念依赖核心链

```
数学公理层:  Base/Trit → Base/Invariants → Base/Axioms
    ↓
代数构造层:  GF(9) → Duodecimal → GroupTheory/DuodecClock
    ↓
结构层:      T⁶ → A₄ → Winding → Structology/*
    ↓
几何层:      ProjectiveCore → ConformalCore → TorusGeometry
    ↓
同伦层:      HoTT/* (CRT → Chern → Hopf → Kan)
    ↓
物理层:      Physics/* (EM → Quantum → Thermo)
    ↓
问题层:      Problem/* (七大千禧年 + Kakeya)
    ↓
应用层:      Applied/* (工程 + 生物 + 经济)
```

---

## 4. 五行概念映射

```
     火 (Tetrahedron/A₄) ←→ Structology/A4Group
      ↕
  土 (Hexahedron) ←→ Structology/Platonics
      ↕
  金 (Dodecahedron/Iₕ) ←→ Structology/IhC60Vibration
      ↕
  水 (Icosahedron) ←→ Structology/WuXingEulerHFM
      ↕
  木 (Octahedron) ←→ MetaStructure/WuXing
      ↕
  空 (S²/A₄ 12胞腔) ←→ Base/ZeroGeometry
```

---

> 此文件手动维护，反映概念层面的结构连接。
