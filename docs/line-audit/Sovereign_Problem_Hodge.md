# 目录 `src/Sovereign/Problem/Hodge/` 逐模块审计记录

共 8 个模块。


## `src/Sovereign/Problem/Hodge/ChainComplex.agda`

- **module**: `Sovereign.Problem.Hodge.ChainComplex`
- **行数**: 40（代码 26 / 注释 5）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (3)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `ChainComplex`
- **顶层签名 (7)**: `dimH`, `null3`, `dimℋ3`, `hodge3`, `tri`, `tri-H0`, `tri-H1`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/DeligneHodge.agda`

- **module**: `Sovereign.Problem.Hodge.DeligneHodge`
- **行数**: 27（代码 10 / 注释 9）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_DeligneHodge — Deligne Weil 猜想 · 在三角复形上的独立形式化
  - 0 postulate
- **导入 (4)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Problem.Hodge.Hodge`, `Sovereign.Problem.Hodge.ChainComplex`
- **顶层签名 (3)**: `z-dim`, `h-dim`, `deligne-holds`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/EulerChar.agda`

- **module**: `Sovereign.Problem.Hodge.EulerChar`
- **行数**: 44（代码 17 / 注释 16）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_EulerChar — 欧拉示性数 · ℤ 算术通用公式
  - χ = Σ(-1)^k dimC_k = Σ(-1)^k dimH_k
  - 0 postulate
- **导入 (3)**: `Data.Integer`, `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (12)**: `s2-χ`, `s2-χH`, `s2-euler`, `tri-χ`, `tri-χH`, `tri-euler`, `t2-χ`, `t2-χH`, `t2-euler`, `kl-χ`, `kl-χH`, `kl-euler`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/Hodge.agda`

- **module**: `Sovereign.Problem.Hodge.Hodge`
- **行数**: 93（代码 35 / 注释 39）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Hodge.Hodge
  - GF(3) 三角复形的离散 Hodge 理论 (正确版本)
  - 不同于经典 ℝ/ℂ 的 Laplacian+内积论证,
  - GF(3) 的 Hodge 理论 = rank-nullity 结构:
  - h⁰ = dim C₀ - rank(∂₁) = 1
  - h¹ = nullity(∂₁) = 1
  - χ  = h⁰ - h¹ = 0
  - 正合列 0 → im(∂₁) → C₀ → H₀ → 0 不分裂
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Topology`
- **顶层签名 (11)**: `poincare`, `euler-zero`, `dims-ok`, `hodge-isomorphism`, `coboundary3`, `const-vec`, `const-in-ker-δ`, `const-in-im-∂`, `hodge-rank-nullity`, `hodge-dim-H0`, `hodge-dim-H1`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/HodgeTetra.agda`

- **module**: `Sovereign.Problem.Hodge.HodgeTetra`
- **行数**: 34（代码 15 / 注释 10）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_HodgeTetra — 四面体边界 (S²) Hodge 分解 · 三角→球面推广
  - 0 postulate
- **导入 (3)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (4)**: `h0`, `h1`, `h2`, `hodge-S2`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/Hodge_L3.agda`

- **module**: `Sovereign.Problem.Hodge.Hodge_L3`
- **行数**: 28（代码 4 / 注释 16）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_Hodge_L3 — Hodge L3: GF(9) 射影簇 + 代数闭链 ≅ Hodge 类
  - 0 postulate
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/KleinHodge.agda`

- **module**: `Sovereign.Problem.Hodge.KleinHodge`
- **行数**: 41（代码 18 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_KleinHodge — Klein 瓶 Hodge 分解 (第四种同调型)
  - 0 postulate
- **导入 (3)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (5)**: `h0`, `h1`, `h2`, `kl-hodge`, `kl-euler`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Problem/Hodge/TorusHodge.agda`

- **module**: `Sovereign.Problem.Hodge.TorusHodge`
- **行数**: 46（代码 18 / 注释 17）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_TorusHodge — 环面 T² △-复形 Hodge 分解
  - 0 postulate
- **导入 (3)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (4)**: `h0`, `h1`, `h2`, `t2-hodge`
- **质量**: `refl`×9；无 postulate / 无 hole
