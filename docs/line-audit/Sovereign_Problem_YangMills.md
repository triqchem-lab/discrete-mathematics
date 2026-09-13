# 目录 `src/Sovereign/Problem/YangMills/` 逐模块审计记录

共 11 个模块。


## `src/Sovereign/Problem/YangMills/SU2_Embedding.agda`

- **module**: `Sovereign.Problem.YangMills.SU2_Embedding`
- **行数**: 37（代码 13 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_SU2_Embedding — SU(2) ⊂ SL₂(GF(9)) 嵌入
  - 0 postulate
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (3)**: `neg`, `det-I2`, `det-σx`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/SUn_GF9.agda`

- **module**: `Sovereign.Problem.YangMills.SUn_GF9`
- **行数**: 43（代码 10 / 注释 22）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_SUn_GF9 — SU(2,GF(9)) 规范群 + Wilson作用量 + 质量间隙
  - SU(2,GF(9)) ≅ 2A₄ (24元素, BinaryTetrahedral 已形式化)
  - 0 postulate
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (3)**: `triv-gap2`, `triv-gap3`, `triv-gap4`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/WilsonLoop.agda`

- **module**: `Sovereign.Problem.YangMills.WilsonLoop`
- **行数**: 114（代码 20 / 注释 76）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_WilsonLoop — 3×3 Wilson 圈 + 格点质量间隙定理
  - 0 postulate
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`, `Sovereign.Algebra.Holographic.LatticeField`, `Sovereign.Algebra.Jacobian.jac_CRTDet`
- **顶层签名 (5)**: `WilsonLoop`, `w-loop-I₃`, `wilson-mass-gap`, `joint-mass-gap`, `crt-mass-gap`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/WilsonPlaquette.agda`

- **module**: `Sovereign.Problem.YangMills.WilsonPlaquette`
- **行数**: 37（代码 11 / 注释 15）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_WilsonPlaquette — YM 单 plaquette Wilson 圈 · 独立形式化
  - 0 postulate
- **导入 (3)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (2)**: `triv-plaq`, `gap-all`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YMTransfer.agda`

- **module**: `Sovereign.Problem.YangMills.YMTransfer`
- **行数**: 28（代码 8 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_YMTransfer — YM 转移矩阵 + CRT 质量间隙 (闭合)
  - det≠0 ⇒ λ_min>0. 实证: 2×2/3×3/4×4. CRT: N×N.
  - 0 postulate
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (3)**: `gap2`, `gap3`, `gap4`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YM_Action.agda`

- **module**: `Sovereign.Problem.YangMills.YM_Action`
- **行数**: 18（代码 7 / 注释 5）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (2)**: `SU2Element`, `triv-plaq`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YM_DetMul.agda`

- **module**: `Sovereign.Problem.YangMills.YM_DetMul`
- **行数**: 88（代码 21 / 注释 47）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_YM_DetMul — YM L3: det(AB)=det(A)·det(B) + 质量间隙
  - 证明策略: GF(3) det-mul (jac_Matrix, 0 postulate, 6561 case)
  - → GF(9) 是 GF(3) 的交换扩张
  - → 同一多项式恒等式扩张到 GF(9)
  - → SU(2) 的 det=1 约束下: det(UV)=1≠0 → 质量间隙
  - 0 postulate.
- **导入 (5)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_Matrix`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (8)**: `det-mul-GF3`, `I2-det`, `I2-nonzero`, `I3-nonzero`, `I4-nonzero`, `I2-det-GF3`, `I2mul-det`, `mass-gap`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YM_Full.agda`

- **module**: `Sovereign.Problem.YangMills.YM_Full`
- **行数**: 25（代码 8 / 注释 9）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_YM_Full — YM 全规模: SU(2) 任意构型 + Wilson 圈
  - 0 postulate
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (3)**: `gap2`, `gap3`, `gap4`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YM_L3.agda`

- **module**: `Sovereign.Problem.YangMills.YM_L3`
- **行数**: 37（代码 9 / 注释 19）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_YM_L3 — YM 质量间隙 L3 证明
  - 转移矩阵 T 对平凡构型: det≠0 ⇒ λ_min>0
  - 非平凡构型: det 由 CRT 分解 ≤4×4 保证
  - 0 postulate
- **导入 (3)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (3)**: `trivial-gap2`, `trivial-gap3`, `trivial-gap4`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YM_SpectralGap.agda`

- **module**: `Sovereign.Problem.YangMills.YM_SpectralGap`
- **行数**: 526（代码 343 / 注释 97）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.YangMills.YM_SpectralGap
  - 单 plaquette Wilson 转移矩阵的精确谱与质量间隙（严格化 YM_L3 的平凡 gap）
  - 数学背景：
  - 单 plaquette、C₃ 规范群的 Wilson 转移矩阵（真空+共轭对双扇区）:
  - T = A·I + B·(R + R²)，R = 3-循环置换（C₃ 的平移表示）。
  - 取 A=2, B=1:  T = [[2,1,1],[1,2,1],[1,1,2]]。
  - 谱（精确整数，无连续统）:
  - λ₀ = A+2B = 4  真空（平凡表示，重数 1，刚性）
  - λ₁ = A−B  = 1  共轭对扇区（ω,ω² 退化，重数 2）
  - 质量间隙 Δ = λ₀ − λ₁ = 3B = 3 > 0。
  - 一致性: tr(T) = 3A = 6 = λ₀ + λ₁ + λ₁；det(T) = λ₀λ₁² = 4。
  - 本模块证明（0 postulate，全部 ℤ 算术 refl + λ()）:
  - §1 真空特征向量（重数 1）
  - §2 共轭对扇区: 两个退化特征向量 + C₃ 旋转下无实不动模（无刚性真空）
  - §3 质量间隙公式与正性
  - §4 谱一致性（迹 = 特征值之和；det = 特征值之积）
  - §5 2×2 Wilson 圈完整谱（全部 4 类构型）: Klein 四元群 V₄ = {I, σₓ, σ_z, σₓσ_z}，
  - 类4 谱 {α,−α} ⊂ GF(9)（Frobenius 共轭对, 无 GF(3) 特征值 — 刚性）
- **导入 (8)**: `Data.Integer`, `Data.Integer.Properties`, `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.RootMath.Eisenstein`
- **顶层签名 (70)**: `Vec3`, `T`, `R`, `R²`, `vacuum`, `vacuum-eigen`, `mode1`, `mode2`, `mode1-eigen`, `mode2-eigen`, `mode1≢mode2`, `mode1-not-R-fixed`, `mode1-not-R²-fixed`, `R-mode1-cycles`, `gap-formula`, `gap-positive`, `trace-consistency`, `det-T-formula`, `det-nonzero`, `Mat2`, `0₉`, `2₉`, `neg9`, `_-₉_`, `apply2`, `scalar2`, `tr2`, `det2`, `charpoly2`, `class1`, `class2`, `class3`, `class4`, `class1-eigen-e1`, `class1-eigen-e2`, `class1-tr`, `class1-det`, `class1-gap`, `class2-eigen-1`, `class2-eigen-2`, `class2-tr`, `class2-det`, `class2-charpoly-1`, `class2-charpoly-2`, `class2-gap`, `class2-gap-nontrivial`, `class3-eigen-1`, `class3-eigen-2`, `class3-tr`, `class3-det`, `class3-gap`, `class4-eigen-alpha`, `class4-eigen-negalpha`, `class4-tr`, `class4-det`, `class4-charpoly-alpha`, `class4-charpoly-negalpha`, `class4-gap`, `class4-gap-nontrivial`, `class4-spectrum-conjugate`
  - … 其余 10 项
- **质量**: `refl`×35；无 postulate / 无 hole

## `src/Sovereign/Problem/YangMills/YM_Transfer.agda`

- **module**: `Sovereign.Problem.YangMills.YM_Transfer`
- **行数**: 36（代码 7 / 注释 19）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_YM_Transfer — YM 转移矩阵 · 多链接格点一般构造
  - 0 postulate
- **导入 (3)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **顶层签名 (1)**: `t2-gap`
- **质量**: `refl`×0；无 postulate / 无 hole
