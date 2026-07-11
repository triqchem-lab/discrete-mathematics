# M3: 概念连通图

## 核心概念拓扑

```
                    全息观测 (L8)
                         │
                    Π_H = 144/46
                         │
          ┌──────────────┼──────────────┐
          │              │              │
     陈数 C=±2      仲吕倍频 ×8    纳音孤子 ρ=0.38
     (拓扑守恒)     (频率级联)      (极限环)
          │              │              │
          └──────────────┼──────────────┘
                         │
                   FULL_TOUR = 6624
                   (相位对齐点)
                         │
          ┌──────────────┼──────────────┐
          │              │              │
     T⁶ 环面 (L4)   手征离合 (L3)   LCM 桥
     144×46 格点    Z[ω] 振幅     (acc×3¹¹)>>16
          │              │              │
          └──────────────┼──────────────┘
                         │
                    GF(3) (L1)
                    {0,1,2} Trit
```

## CRT 域的四条路径

### 数论路径
```
GF(3) → Z/3¹¹Z → CRT 同构 Z/M ≅ Z/65536 × Z/177147 → 互质性 → 双模投影
```

### 谐波路径
```
T¹=65536, T²=177147 → 拍频 M=11609505792 → 驻波条件 → 谐波阶梯 → X₀=5148246160
```

### 拓扑路径
```
GF(3)⁶ → T⁶ 环面 → 万有覆盖 → 缠绕数 144/46 → A₄ 覆盖 → 陈数 C=±2
```

### 谱路径
```
M₄ 幻方 (4×4) → 16²≡40(mod 216) → 谱截断 ±2√10→±16 → T⁶ 正交投影
```

## 关键定理依赖链

```
alignmentIdentity (FULL_TOUR ≡ 144×46)
    │
    ├──→ closureTheorem (∀n, n·6624 % 144 ≡ 0, n·6624 % 46 ≡ 0)
    │         │
    │         └──→ L2: Kan 纤维化边界闭合
    │
    ├──→ phaseResyncAxiom (x%6624 ≡ (x%144) + 144·((x/144)%46))
    │         │
    │         └──→ L3: 索引族单值语义基础
    │
    └──→ 144/46 不可约性 → Π_H 全息不变
```

## 概念到代码的映射

| 概念 | 模块 | 关键函数/类型 |
|------|------|-------------|
| Trit {0,1,2} | `Base/Trit.agda` | `Trit`, `toℕ` |
| GF(3) 群 | `RootMath/Base.agda` | `GF3`, `step1-cubed-id` |
| 缠绕数 144/46 | `Structology/Winding.agda` | `PolarWinding`, `ToroidalWinding` |
| T⁶ 环面 | `Structology/T6.agda` | `T6Lattice`, `polarStep`, `toroidalStep` |
| FULL_TOUR 6624 | `Structology/MagicSquare144.agda` | `FULL_TOUR` |
| 6624 相位对齐 | `HoTT/PhaseAlignment6624.agda` | `closureTheorem`, `phaseResyncAxiom` |
| CRT 同构 | `Format/CRT.agda` | `crtTheorem` |
| CRT 纤维 | `HoTT/CRTFiberWinding.agda` | `X₀=5148246160` |
| 谐波驻波 | `HoTT/CRTHarmonics.agda` | `harmonic-phase-preserving` |
| M₄ 幻方桥 | `HoTT/M4CRTBridge.agda` | `16²≡40(mod216)` |
| T⁶ 同伦 | `HoTT/T6Homotopy.agda` | `π₁(T⁶)≅GF(3)⁶` |
| 陈数 C=±2 | `HoTT/ChernClass.agda` | `ChernInvariant` |
| 能隙 Δ²=3 | `RootMath/EnergyGap.agda` | `C3 生成元`, `弦长 √3` |
| A₄ 表示 | `Structology/A4Representations.agda` | `{3,1,1′,1″}` |
| Christoffel 螺旋 | `Structology/WuXingTransition.agda` | `损益交替 [1,2,1,2,1,2]` |
| 仲吕闭合 | `Coupling/ZhonglvClosure.agda` | `isZhonglvPoint` |
| LCM 桥 | `Coupling/LCM.agda` | `SOVEREIGN_LCM = 11609505792` |
