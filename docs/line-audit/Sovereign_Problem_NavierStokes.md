# 目录 `src/Sovereign/Problem/NavierStokes/` 逐模块审计记录

共 3 个模块。


## `src/Sovereign/Problem/NavierStokes/NSE.agda`

- **module**: `Sovereign.Problem.NavierStokes.NSE`
- **行数**: 306（代码 148 / 注释 91）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.NavierStokes.NSE — N-S方程 GF(3) 全域精确解
  - 状态: 全部对齐 (2026-05-11)
  - 12项定理 + 零postulate + 零自由参数
  - 从泛音列公理到12.15 MHz, 完整推导链
- **导入 (6)**: `Data.Nat`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`, `Data.Bool`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`
- **顶层签名 (46)**: `f0`, `sunyi-ratio-num`, `sunyi-ratio-den`, `zhonglv-mult`, `grid-verify`, `pi-holo-num`, `pi-holo-den`, `zhonglv-factor-num`, `zhonglv-factor-den`, `C`, `add3`, `add3-comm`, `add3-assoc`, `c3-cw`, `c3-inverse`, `comma-verify`, `comma-den-ok`, `ρ-num`, `ρ-den`, `triv₀-num`, `triv₀-den`, `triv₀-verify`, `non-triv-num`, `non-triv-den`, `α-num`, `α-den`, `α-verify`, `C-SUB`, `N-eff-num`, `N-eff-den`, `φ-num`, `φ-den`, `N-blocks`, `blocks-verify`, `E0`, `E1`, `E2`, `eigen-sum`, `wuxing-cubed-val`, `wuxing-cubed-verify`, `c3-cycle`, `c3-decomp`, `N14`, `coeff-num`, `coeff-den`, `resonance-k1`
- **质量**: `refl`×49；无 postulate / 无 hole

## `src/Sovereign/Problem/NavierStokes/NSRegularity.agda`

- **module**: `Sovereign.Problem.NavierStokes.NSRegularity`
- **行数**: 166（代码 59 / 注释 82）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | NSRegularity — N-S 方程的 GF(3) 离散正则性判据
  - 连续统病态: ℝ³ 上 N-S 正则性 (是否存在光滑解) 是千禧年问题
  - 离散自愈: GF(3)³ 上所有函数自动光滑 (有限格点, 无 ε→0)
  - 核心定理:
  - §1. 离散能量: E(v) = Σ|v(x)|² ∈ GF(3), 天然有界
  - §2. 能量不等式: 无粘时 E 守恒, 有粘时 E 递减
  - §3. 正则性: GF(3) 上无奇点 (所有值 ∈ {T₀,T₁,T₂})
  - §4. 爆破排除: 离散能量无法趋向无穷
  - 复用: Sovereign.Base.Trit, NSVortex
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Sum`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Problem.NavierStokes.NSVortex`
- **顶层签名 (14)**: `point-energy`, `zero-energy`, `unit-energy`, `energy-is-trit`, `energy-lower-bound`, `velocity-regular`, `no-blowup-point`, `discrete-regularity-summary`, `step`, `step³-id`, `step-injective`, `energy-step-invariant`, `iterate`, `orbit-period-3`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Problem/NavierStokes/NSVortex.agda`

- **module**: `Sovereign.Problem.NavierStokes.NSVortex`
- **行数**: 128（代码 39 / 注释 67）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | NSVortex — N-S 方程的 GF(3) 离散涡旋演化
  - 连续统病态: ℝ³ 上 N-S 方程的涡旋可无限细分 → 爆破奇点
  - 离散自愈: GF(3)³ 格点上涡旋密度有刚性上限 → 正则性自动保证
  - 核心结构:
  - §1. 离散速度场: GF(3)³ → GF(3)³
  - §2. 离散涡量: ω = ∇×v (GF(3) 差分)
  - §3. 涡旋演化算子: 离散 Euler 方程
  - §4. 涡量守恒: 无粘时涡量沿流线不变
  - 复用: Sovereign.Base.Trit (GF(3) 运算)
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Data.Sum`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (13)**: `Point3`, `Vec3`, `VelocityField`, `zero-field`, `uniform-flow`, `gf3-diff`, `diff-zero-const`, `Vorticity`, `TimeStep`, `identity-evolution`, `stationary-is-fixed`, `zero-vorticity-preserved`, `vorticity-bounded`
- **质量**: `refl`×9；无 postulate / 无 hole
