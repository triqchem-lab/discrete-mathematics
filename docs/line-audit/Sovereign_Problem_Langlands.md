# 目录 `src/Sovereign/Problem/Langlands/` 逐模块审计记录

共 6 个模块。


## `src/Sovereign/Problem/Langlands/DeligneLusztig.agda`

- **module**: `Sovereign.Problem.Langlands.DeligneLusztig`
- **行数**: 24（代码 7 / 注释 9）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_DeligneLusztig — Deligne-Lusztig 理论 · 在 A₄ 上的独立形式化
  - 0 postulate
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representations`
- **顶层签名 (1)**: `dl-A4`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Problem/Langlands/GL2TestVectors.agda`

- **module**: `Sovereign.Problem.Langlands.GL2TestVectors`
- **行数**: 171（代码 102 / 注释 50）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Problem.Langlands.GL2TestVectors
  - GL₂(GF(9)) 群分类的 HFM 穷举交叉验证测试向量
  - HFM 验证 (test/GL2Verify.hs):
  - 穷举全部 6561 个 Mat₂(GF(9)) 矩阵, 筛出可逆者 5760 个
  - 按判别式 Δ = tr² − 4·det 在 GF(9) 中的性质分类
  - 数学原理:
  - GF(9) = GF(3)[i], i² = -1, 共 9 个元素
  - Mat₂(GF(9)) 有 9⁴ = 6561 个矩阵
  - GL₂(GF(9)) 的行列式不为零, 个数 = (9²-1)(9²-9) = 5760
  - GL₂(F_q) 的共役类由特征多项式 f(t) = det(t·I − M) 分类:
  - (1) Central (标量矩阵): f(t) = (t−λ)², 极小多项式 = t−λ
  - 共 q−1 = 8 类, 类大小 = 1
  - (2) Split regular (可对角化, 特征值相异):
  - f(t) = (t−λ)(t−μ), λ≠μ ∈ GF(9)
  - 共 (q−1)(q−2)/2 = 28 类, 类大小 = q(q+1) = 90
  - (3) Anisotropic (不可对角化, 特征值在 GF(81)\GF(9)):
  - f(t) 不可约, Δ 不是 GF(9)* 中的平方
- **导入 (4)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`, `Data.Integer`
- **顶层签名 (19)**: `orderGL2`, `orderSL2`, `centerSize`, `orderGL2-ok`, `orderSL2-ok`, `orderSL2-factor-check`, `totalClasses`, `burnsideSum`, `totalClasses-ok`, `burnsideSum-ok`, `chiSt-dim`, `chiSt-cent`, `chiSt-split`, `chiSt-aniso`, `chiSt-unip`, `orthTriv`, `orthTriv-ok`, `orthSelf`, `orthSelf-ok`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/Langlands/GL2_Rep.agda`

- **module**: `Sovereign.Problem.Langlands.GL2_Rep`
- **行数**: 28（代码 6 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_GL2_Rep — GL₂(GF(9)) 表示论: Burnside + 共轭类
  - 0 postulate
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (2)**: `order`, `center`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Problem/Langlands/Langlands.agda`

- **module**: `Sovereign.Problem.Langlands.Langlands`
- **行数**: 122（代码 43 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - jac_Langlands: GL₂(GF(9)) 共轭类 + 特征标 — 深度形式化
  - 深度提升: 共轭类大小从代数公式参数化推导 (q=9).
  - 类个数: (q-1), (q-1)(q-2)/2, q(q-1)/2, q-1 — 需要除法, 用具体值.
  - 0 postulate.
- **导入 (2)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (14)**: `q`, `q²`, `sSplit-ok`, `sAni-ok`, `sUni-ok`, `nCent-ok`, `nSplit-ok`, `nAni-ok`, `nUni-ok`, `burnside`, `χ1`, `ortho-1-St`, `irred-St`, `irred-1`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Problem/Langlands/Langlands_L15.agda`

- **module**: `Sovereign.Problem.Langlands.Langlands_L15`
- **行数**: 29（代码 5 / 注释 16）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_Langlands_L15 — Langlands L1.5: GL₂(GF(9)) 表示论框架
  - 0 postulate
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (1)**: `order-GL2`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Problem/Langlands/S4Burnside.agda`

- **module**: `Sovereign.Problem.Langlands.S4Burnside`
- **行数**: 21（代码 7 / 注释 7）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_S4Burnside — S₄ Burnside 验证 · Langlands 第二实例
  - 0 postulate
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (2)**: `s4-order`, `s4-burnside`
- **质量**: `refl`×2；无 postulate / 无 hole
