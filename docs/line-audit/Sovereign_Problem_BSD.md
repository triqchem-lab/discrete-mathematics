# 目录 `src/Sovereign/Problem/BSD/` 逐模块审计记录

共 11 个模块。


## `src/Sovereign/Problem/BSD/BSD.agda`

- **module**: `Sovereign.Problem.BSD.BSD`
- **行数**: 187（代码 58 / 注释 102）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.BSD.BSD
  - 离散 BSD 猜想 — 有限域椭圆曲线点计数与秩判据
  - 核心定理:
  - §1. GF(3) 椭圆曲线点计数 (穷举验证)
  - §2. Hasse 界: |#E - (q+1)| ≤ 2√q (实例验证)
  - §3. 离散秩 = ord_{s=1} L(E,s) 的有限域编码
  - §4. 与 jac_Langlands 的桥接: Selmer 群 ⊂ H¹(G, E[n])
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `Point`
- **顶层签名 (23)**: `sq`, `rhs`, `on-curve`, `count-points`, `#E1`, `#E1-is-4`, `hasse-ok`, `trace-E1`, `trace-E1-zero`, `#E2`, `#E2-is-7`, `#E3`, `#E3-is-4`, `#E4`, `#E4-is-4`, `#E5`, `#E5-is-4`, `#E6`, `#E6-is-1`, `discrete-rank`, `rank-E1`, `rank-E2`, `bsd-E1`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSD9.agda`

- **module**: `Sovereign.Problem.BSD.BSD9`
- **行数**: 52（代码 10 / 注释 28）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSD9 — GF(9) 椭圆曲线点计数 · 未来态锁定法
  - 目标: #E(GF(9)) = 16 (Hasse紧界), 由迹递推一步到位
  - 不使用暴力枚举. 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Problem.BSD.BSD`
- **顶层签名 (4)**: `t₁`, `q`, `#E-gf9`, `target-anchored`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSDTrace.agda`

- **module**: `Sovereign.Problem.BSD.BSDTrace`
- **行数**: 30（代码 10 / 注释 11）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSDTrace — BSD Weil 迹递推 + GF(qⁿ) 点计数 (闭合)
  - 0 postulate
- **导入 (3)**: `Data.Integer`, `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (4)**: `t₂`, `e9`, `t₁0`, `e16`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSD_GF243.agda`

- **module**: `Sovereign.Problem.BSD.BSD_GF243`
- **行数**: 27（代码 8 / 注释 9）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSD_GF243 — BSD t₅ 递推 + GF(243) · 三曲线全分化
  - 0 postulate
- **导入 (2)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (4)**: `q3`, `t51`, `t52`, `t56`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSD_GF27.agda`

- **module**: `Sovereign.Problem.BSD.BSD_GF27`
- **行数**: 32（代码 11 / 注释 11）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSD_GF27 — BSD 迹递推 t₃ + GF(27) 点计数
  - 0 postulate
- **导入 (2)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (7)**: `q3`, `t31`, `e127`, `t32`, `e227`, `t36`, `e627`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSD_GF81.agda`

- **module**: `Sovereign.Problem.BSD.BSD_GF81`
- **行数**: 33（代码 11 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSD_GF81 — BSD t₄ 递推 + GF(81) 点计数 · 三曲线分化
  - 0 postulate
- **导入 (2)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (7)**: `q3`, `t41`, `e181`, `t42`, `e281`, `t46`, `e681`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSD_General.agda`

- **module**: `Sovereign.Problem.BSD.BSD_General`
- **行数**: 34（代码 12 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSD_General — BSD Weil 迹递推 · 三条独立定理
  - 0 postulate
- **导入 (3)**: `Data.Integer`, `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (3)**: `q3`, `trace0`, `trace-3`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/BSD_L3.agda`

- **module**: `Sovereign.Problem.BSD.BSD_L3`
- **行数**: 77（代码 41 / 注释 23）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_BSD_L3 — BSD L3: tₙ递推严格递归定义 + 正确性证明
  - 0 postulate
- **导入 (3)**: `Data.Integer`, `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (21)**: `step`, `t-rec`, `q3`, `t1-val`, `t2-val`, `t3-val`, `t4-val`, `t5-val`, `t6-val`, `t7-val`, `t8-val`, `t9-val`, `t10-val`, `step-t3`, `step-t4`, `step-t5`, `step-t6`, `step-t7`, `step-t8`, `step-t9`, `step-t10`
- **质量**: `refl`×21；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/EllipticComplex.agda`

- **module**: `Sovereign.Problem.BSD.EllipticComplex`
- **行数**: 80（代码 18 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_EllipticComplex — dim ℋ = dim H (Hodge 定理, rank-nullity 链)
  - 0 postulate
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (12)**: `dimC₀`, `dimC₁`, `rank∂₁`, `dimH₀`, `dimH₁`, `dimℋ₀`, `dimℋ₁`, `hodge-iso₀`, `hodge-iso₁`, `χ-complex`, `χ-homology`, `euler-identity`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/SelmerDiscrete.agda`

- **module**: `Sovereign.Problem.BSD.SelmerDiscrete`
- **行数**: 87（代码 17 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_SelmerDiscrete — 离散 Selmer 群: C₂ cocycle 穷举 + H¹ 计算
  - 0 postulate
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Problem.BSD.BSD`
- **顶层签名 (9)**: `c2-cocycle-count`, `c2-total-cases`, `c2-valid-check`, `c2-H1-dim`, `c2-H1-ok`, `v4-cocycle-count`, `v4-H1-dim`, `v4-H1-ok`, `selmer-e1`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Problem/BSD/ZetaDiscrete.agda`

- **module**: `Sovereign.Problem.BSD.ZetaDiscrete`
- **行数**: 54（代码 8 / 注释 35）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_ZetaDiscrete — GF(q) 有限域 zeta + Weil 定理 (未来态)
  - 0 postulate
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Problem.BSD.BSD`
- **顶层签名 (3)**: `e1-gf3`, `e1-ok`, `e1-gf9`
- **质量**: `refl`×2；无 postulate / 无 hole
