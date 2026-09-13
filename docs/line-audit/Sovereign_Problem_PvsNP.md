# 目录 `src/Sovereign/Problem/PvsNP/` 逐模块审计记录

共 11 个模块。


## `src/Sovereign/Problem/PvsNP/Algorithm.agda`

- **module**: `Sovereign.Problem.PvsNP.Algorithm`
- **行数**: 80（代码 8 / 注释 59）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.Algorithm
  - Phase 5: 全局矩阵判定算法 + 正确性
  - 算法: 给定 F: S → S (有限集), 构造全局矩阵 M_F, 计算 det
  - 正确性: det(M_F) ≠ 0 ⟺ F 是双射 (鸽巢原理)
  - 复杂度: O(N³) 行列式计算, N = |S|
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/CharPoly3.agda`

- **module**: `Sovereign.Problem.PvsNP.CharPoly3`
- **行数**: 30（代码 10 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_CharPoly3 — 3×3 det判定 + 不可约性框架
  - 0 postulate
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`, `Sovereign.Problem.PvsNP.Complexity`
- **顶层签名 (2)**: `irred2`, `det3-ok`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/Complexity.agda`

- **module**: `Sovereign.Problem.PvsNP.Complexity`
- **行数**: 229（代码 31 / 注释 169）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.PvsNP.Complexity
  - 全息计算复杂度 — M_F 不可约性穿透 P vs NP 三重屏障
  - 核心定理:
  - 古典复杂性理论被三重屏障锁死:
  - B1: Baker-Gill-Solovay 相对化 (1975)
  - B2: Razborov-Rudich 自然证明 (1997)
  - B3: Aaronson-Wigderson 代数化 (2009)
  - 所有以"局部电路多项式"为工具的攻击路径均在此三屏障之一失效.
  - 本模块的构造性路径:
  - 将 P≠NP 的分离性判定转换为 M_F 在 GF(9) 上的代数不可约性.
  - M_F 的全息特征 (非局部/非自然/非相对化) 天然穿透三重屏障.
  - 本模块建立框架接口与桥接定理陈述,
  - 完整的 NP 完备问题全息映射为长期工程目标.
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **record 类型**: `CharPoly`
- **顶层签名 (5)**: `eval-quad`, `has-root`, `irred-example`, `red-example`, `matrix-irred`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/Complexity3.agda`

- **module**: `Sovereign.Problem.PvsNP.Complexity3`
- **行数**: 55（代码 33 / 注释 9）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **record 类型**: `M3`
- **顶层签名 (12)**: `negate`, `det3`, `diag-det`, `CM`, `det-CM`, `f₃`, `f0-val`, `f1-val`, `f2-val`, `irr-CM-f0`, `irr-CM-f1`, `irr-CM-f2`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/CubicRoot.agda`

- **module**: `Sovereign.Problem.PvsNP.CubicRoot`
- **行数**: 34（代码 11 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (6)**: `v0`, `v1`, `v2`, `v0≠0`, `v1≠0`, `v2≠0`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/CubicRootTest.agda`

- **module**: `Sovereign.Problem.PvsNP.CubicRootTest`
- **行数**: 133（代码 47 / 注释 54）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (3)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (29)**: `eval3`, `neg`, `p-coef`, `sq`, `s-coef`, `f-at-0`, `f-at-1`, `f-at-2`, `red-f-at-0`, `red-p`, `red-s`, `red2-f-at-2`, `red2-p`, `red2-s`, `expand-λ²`, `expand-λ¹`, `expand-λ⁰`, `d₁`, `p₁`, `s₁`, `exp1-λ²`, `exp1-λ¹`, `exp1-λ⁰`, `d₂`, `p₂`, `s₂`, `exp2-λ²`, `exp2-λ¹`, `exp2-λ⁰`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/DetMul.agda`

- **module**: `Sovereign.Problem.PvsNP.DetMul`
- **行数**: 29（代码 6 / 注释 18）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (3)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/GF27Separation.agda`

- **module**: `Sovereign.Problem.PvsNP.GF27Separation`
- **行数**: 172（代码 85 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.PvsNP.GF27Separation
  - PvsNP 分离定理的 GF(27) 扩域版: 不可约三次 λ³+2λ+1 的完全根结构
  - 数学背景:
  - GF(27) = GF(3)[γ]/(γ³+2γ+1)，γ³ = γ+2（不可约三次 λ³+2λ+1 在 GF(3) 无根,
  - 见 PvsNP_Separation.no-root）。GF(3) 上 Invert（根搜索）失败;
  - GF(27) 上恰好 3 个根: {γ, γ³, γ⁹} —— Frobenius 共轭三元组
  - （σ(x)=x³ 的原生轨道: γ → γ³ → γ⁹ → γ, 与 GF(9) 的共轭对同构模式）。
  - Vieta 验证: 根和 = 0（λ² 系数为 0）, 根积 = 2 = −1（常数项取负）。
  - 形式化内容（0 postulate, 全部 GF(3) 算术 refl/λ()）:
  - §1 GF(27) 环结构: 三元组 + 乘法（γ³=γ+2 约化）
  - §2 Frobenius 共轭三元组: γ³, γ⁹ 恒等式 + 轨道闭合
  - §3 三根验证 + 互异
  - §4 27 元素穷举: 恰好 3 个根（3 refl + 24 λ()）
  - §5 GF(3) 内无根（3 λ()）—— Eval/Invert 分离从 GF(3) 到 GF(27) 的完整见证
  - §6 Vieta: 根和 = 0, 根积 = 2
- **导入 (4)**: `Data.Product`, `Data.Sum`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (20)**: `GF27`, `zero27`, `one27`, `γ`, `cube27`, `eval27`, `gamma-cube`, `gamma-nine`, `γ3`, `γ9`, `frobenius-cycle`, `root-gamma`, `root-gamma3`, `root-gamma9`, `roots-distinct`, `root-or-not`, `gf3-no-root`, `vieta-sum`, `vieta-product`, `gamma-order-26`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/PvsNP_Conjecture.agda`

- **module**: `Sovereign.Problem.PvsNP.PvsNP_Conjecture`
- **行数**: 34（代码 11 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_PvsNP_Conjecture — 全息穿透猜想 · 形式化陈述
  - 0 postulate (猜想本身未被证明, 仅陈述类型)
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `PvsNPConjecture`
- **顶层签名 (1)**: `status`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/PvsNP_L15.agda`

- **module**: `Sovereign.Problem.PvsNP.PvsNP_L15`
- **行数**: 28（代码 10 / 注释 10）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_PvsNP_L15 — PvsNP L1.5: 3×3 不可约性穷举判定
  - 0 postulate
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`, `Sovereign.Problem.PvsNP.Complexity`
- **顶层签名 (2)**: `irred2`, `det3-I`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/PvsNP/PvsNP_Separation.agda`

- **module**: `Sovereign.Problem.PvsNP.PvsNP_Separation`
- **行数**: 131（代码 32 / 注释 69）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (3)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (14)**: `eval3`, `EvalStep`, `Invert3`, `eval0`, `eval1`, `eval2`, `no-root`, `invert-fail0`, `invert-fail1`, `invert-fail2`, `invert-success`, `EvalAlways`, `InvertSaturates`, `separation`
- **质量**: `refl`×9；无 postulate / 无 hole
