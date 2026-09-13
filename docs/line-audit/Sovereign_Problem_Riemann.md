# 目录 `src/Sovereign/Problem/Riemann/` 逐模块审计记录

共 9 个模块。


## `src/Sovereign/Problem/Riemann/AlgGeom.agda`

- **module**: `Sovereign.Problem.Riemann.AlgGeom`
- **行数**: 151（代码 25 / 注释 104）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Riemann.AlgGeom
  - 离散代数几何 — GF(9) 上有限代数簇与函数-矩阵对偶
  - 核心定理:
  - §1. GF(9) 上仿射代数簇 V(f₁,...,f_k) = {x∈GF(9)ⁿ | fᵢ(x)=0}
  - §2. 正则函数环 Γ(V) = GF(9)[x₁,...,xₙ]/I(V) — 有限维 GF(9) 代数
  - §3. M_F ↔ Γ(V) 对偶: 函数表矩阵 ≅ 正则表示的乘法矩阵
  - §4. 点计数: |V(𝔽_q)| = dim 的代数表达
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (4)**: `eval-quad`, `variety-quad`, `RegFunc`, `discriminant`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/FrobeniusBlind.agda`

- **module**: `Sovereign.Problem.Riemann.FrobeniusBlind`
- **行数**: 285（代码 118 / 注释 117）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.FrobeniusBlind
  - Phase 3: Frobenius 盲区的精确形式化
  - GF(9)² 上的反例 F(x,y) = (x, y + α·y³):
  - 逐点 J(F) = I, det = 1 (盲区)
  - 全局: 81 → 27 像 (3-to-1), det(F*) = 0
  - Frobenius σ(y) = y³ 是 GF(3)-线性核的来源
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`
- **顶层签名 (26)**: `GF9`, `gf9-add`, `gf9-mul`, `α₉`, `emb`, `σ₉`, `GF9²`, `F-frob`, `det-J-formal-frob`, `frob-collision-1`, `frob-collision-2`, `frob-3to1`, `shift9`, `Sy9`, `_⊖₉_`, `gf9-neg`, `π₂₉`, `Δy-F2-at-00`, `σ-shift`, `Δy-F2-const`, `Sx9`, `π₁₉`, `Δx-F1-const`, `gf9-self-inv`, `Δy-F1-const`, `Δx-F2-const`
- **质量**: `refl`×43；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/Galois.agda`

- **module**: `Sovereign.Problem.Riemann.Galois`
- **行数**: 178（代码 43 / 注释 105）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Riemann.Galois
  - 离散 Galois 理论 — 有限域扩张的 Galois 群与基本定理
  - 核心定理:
  - §1. GF(9)/GF(3) 是 2 次 Galois 扩张, Gal ≅ C₂
  - §2. Frobenius σ(x)=x³ 是 Galois 群的生成元
  - §3. Galois 对应: 中间域 ↔ Galois 子群
  - §4. 范数与迹: σ 的不变量刻画
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **data 类型**: `C2`
- **顶层签名 (13)**: `c2-mul`, `c2-inv`, `galois-act`, `galois-σ²`, `fixed-by-σ`, `gf3-embed`, `gf3-is-fixed`, `dim-gf9-over-gf3`, `galois-order-match`, `norm9`, `trace9`, `norm-α`, `trace-α`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/RH.agda`

- **module**: `Sovereign.Problem.Riemann.RH`
- **行数**: 109（代码 48 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - jac_RH: 有限域 Weil/RH — 深度形式化
  - 所有数值从 jac_BSD 的穷举 #E 自动推导, 无手动赋值.
  - 0 postulate.
- **导入 (5)**: `Data.Integer`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Problem.BSD.BSD`, `Sovereign.Problem.BSD.BSD_L3`
- **顶层签名 (20)**: `tE1-ok`, `tE2-ok`, `tE6-ok`, `t1val`, `t2val`, `t3val`, `t4val`, `t5val`, `func-sig`, `n1-E1ok`, `n1-E2ok`, `n1-E6ok`, `hasse-E1`, `hasse-E2`, `hasse-E6`, `t3-E1-zero`, `t3-E2-zero`, `t3-E6-zero`, `e27`, `e27-ok`
- **质量**: `refl`×24；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/Sheaf.agda`

- **module**: `Sovereign.Problem.Riemann.Sheaf`
- **行数**: 121（代码 22 / 注释 80）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Riemann.Sheaf
  - 离散层论 — GF(9) 上有限拓扑空间的层与 Čech 上同调
  - 核心定理:
  - §1. 有限拓扑空间 (Fin n 上任意开集族)
  - §2. GF(9)-值预层与层条件
  - §3. Čech 上同调 Ȟ⁰, Ȟ¹ 的有限计算
  - §4. 与 jac_Topology 同调的对齐
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **record 类型**: `Presheaf`
- **顶层签名 (5)**: `OpenSet`, `const-sheaf-H0`, `const-sheaf-H1`, `sheaf-verify`, `topology-sheaf-alignment`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/Variety.agda`

- **module**: `Sovereign.Problem.Riemann.Variety`
- **行数**: 34（代码 8 / 注释 16）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_Variety — GF(9) 上代数簇基础设施
  - 0 postulate
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`
- **顶层签名 (2)**: `pl`, `p2`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/WeilRH.agda`

- **module**: `Sovereign.Problem.Riemann.WeilRH`
- **行数**: 52（代码 18 / 注释 21）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_WeilRH — Weil 有限域 RH · GF(3)/GF(9) 双实例独立形式化
  - 0 postulate
- **导入 (3)**: `Data.Integer`, `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (13)**: `e13`, `e13ok`, `t11`, `t21`, `e19`, `e23`, `e23ok`, `t12`, `t22`, `e29`, `t16`, `t26`, `e69`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/WeilRigidity.agda`

- **module**: `Sovereign.Problem.Riemann.WeilRigidity`
- **行数**: 228（代码 109 / 注释 65）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Riemann.WeilRigidity
  - 有限域 Riemann 假说的刚性形式：三条显式椭圆曲线的 Weil 定理完整形式化
  - 数学背景：
  - E/F_q 的 L-函数 L(E,T) = 1 − t·T + q·T²，t = q+1−#E(GF(q))。
  - 有限域 RH（Weil 已证，1948）断言：L 的互逆根 α,β 满足 αβ = q 且
  - |α| = √q —— 其整数形式即 Hasse 界 t² ≤ 4q（无无理数）。
  - 刚性形式：t² + 3s² = 4q（s 为整数）⟺ 特征值
  - α = (t + s√−3)/2 ∈ ℤ[ω]（Eisenstein 整数，√−3 = 1+2ω），
  - β = conjᵉ α 为其原生共轭（ω ↔ ω²，√−3 ↔ −√−3）——
  - 与 GF(9)/GF(3) 的 Frobenius 共轭 σ(x)=x³ 同构。
  - 三条曲线（WeilRH.agda 同款实例）:
  - E₁: y² = x³+x+1   #E₁(GF(3))=4,  t₁=0
  - E₂: y² = x³+2x+1  #E₂(GF(3))=7,  t₁=−3
  - E₆: y² = x³+2x+2  #E₆(GF(3))=1,  t₁=+3
  - 本模块证明（0 postulate，全部 refl）:
  - §1 BSD 恒等式:  L(E,1) = #E(GF(q))  与  L(E,1) = #E(GF(q²))（精确）
  - §2 Weil 范数恒等式:  t² + 3s² = 4q  （Hasse 界的整数形式）
- **导入 (5)**: `Data.Integer`, `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Eisenstein`
- **顶层签名 (48)**: `q3`, `t1-E1`, `t1-E2`, `t1-E6`, `t2-E1`, `t2-E2`, `t2-E6`, `bsd-identity-E1`, `bsd-identity-E2`, `bsd-identity-E6`, `bsd-identity-E1-9`, `bsd-identity-E2-9`, `bsd-identity-E6-9`, `weil-norm-E1`, `weil-norm-E2`, `weil-norm-E6`, `weil-norm-E1-9`, `weil-norm-E2-9`, `weil-norm-E6-9`, `hasse-bound-E1`, `hasse-bound-E2`, `hasse-bound-E6`, `alpha-E1`, `alpha-E2`, `alpha-E6`, `alpha-E1-9`, `alpha-E2-9`, `alpha-E6-9`, `trace-sum-E1`, `trace-sum-E2`, `trace-sum-E6`, `trace-sum-E2-9`, `norm-product-E1`, `norm-product-E2`, `norm-product-E6`, `norm-product-E2-9`, `eigen-E1`, `eigen-E2`, `eigen-E6`, `conjugate-pair-E1`, `conjugate-pair-E2`, `conjugate-pair-E6`, `conjugate-pair-E2-9`, `real-split-E1-9`, `bsd-summary-gf3`, `weil-norm-summary-gf3`, `bsd-summary-gf9`, `weil-norm-summary-gf9`
- **质量**: `refl`×26；无 postulate / 无 hole

## `src/Sovereign/Problem/Riemann/ZetaFunctional.agda`

- **module**: `Sovereign.Problem.Riemann.ZetaFunctional`
- **行数**: 279（代码 145 / 注释 74）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Riemann.ZetaFunctional
  - 有限域 zeta 函数的有理式、函数方程与零点刚性 (P1-1, 11M 离散版)
  - 数学背景:
  - E/F_q 椭圆曲线, Frobenius 迹 t = q+1−#E。L(E,T) = 1 − tT + qT²,
  - Z(T) = L(T)/((1−T)(1−qT)) 是 E 的 zeta 函数 (有理式)。
  - 函数方程 (genus 1): Z(1/qT) = Z(T) —— 权重因子 q^(1−g)T^(2−2g) = 1。
  - 零点: Z 的零点 = L 的零点 = α⁻¹, β⁻¹, 其中 α,β 为 L 的互逆根
  - (αβ = q, α+β = t, α ∈ ℤ[ω] — Eisenstein 刚性 t²+3s²=4q 见 WeilRigidity)。
  - 宪法原则 (全离散, 无浮点, 无除法):
  - 1. T ↦ 1/qT 的替换以"通分多项式" recipClear q P := q²T²·P(1/qT) 实现,
  - 系数运算只含 ℤ 加减乘; 分式相等用交叉相乘四次恒等式表达。
  - 2. 零点不取逆元: "α⁻¹ 是零点"以互逆多项式 P*(T) = T²·P(1/T) = T²−tT+q
  - 在 α 处取零的整数形式陈述。
  - 3. 函数方程 = recipClear(q,L)·D ≡ L·recipClear(q,D) (四次恒等式),
  - 三条曲线逐条 refl 验证 (与 WeilRigidity 同款实例)。
  - 本模块证明 (0 postulate, 全 refl/cong):
  - §0 多项式与分数类型 (Quad/Quart/ZetaFraction, 通分 recipClear, 求值 evalE)
- **导入 (5)**: `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Eisenstein`, `Sovereign.Problem.Riemann.WeilRigidity`
- **record 类型**: `Quad`, `QuadE`, `Quart`, `ZetaFraction`
- **顶层签名 (46)**: `recipClear`, `mulLin`, `embed`, `negᵉ`, `evalE`, `Zpoly`, `denPoly`, `Z`, `numEis`, `reversePoly`, `num-factor-E1`, `num-factor-E2`, `num-factor-E6`, `den-factor-direct`, `den-factor-swapped`, `clear-num-E1`, `clear-num-E2`, `clear-num-E6`, `clear-den-E1`, `fe-cross-E1`, `fe-cross-E2`, `fe-cross-E6`, `zeta-recip-E1`, `zeta-recip-E2`, `zeta-recip-E6`, `fe-cross-E1-9`, `fe-cross-E2-9`, `zeta-recip-E1-9`, `zeta-recip-E2-9`, `zero-alpha-E1`, `zero-beta-E1`, `zero-alpha-E2`, `zero-beta-E2`, `zero-alpha-E6`, `zero-beta-E6`, `zero-alpha-E1-9`, `zero-alpha-E2-9`, `zero-beta-E2-9`, `recip-num-E1`, `recip-num-E2`, `recip-num-E6`, `disc-E1`, `disc-E2`, `disc-E6`, `disc-E1-9`, `disc-E2-9`
- **质量**: `refl`×33；无 postulate / 无 hole
