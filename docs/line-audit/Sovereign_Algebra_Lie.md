# 目录 `src/Sovereign/Algebra/Lie/` 逐模块审计记录

共 2 个模块。


## `src/Sovereign/Algebra/Lie/LieAlgebra.agda`

- **module**: `Sovereign.Algebra.Lie.LieAlgebra`
- **行数**: 1722（代码 1645 / 注释 43）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Lie.LieAlgebra
  - 离散李代数 — GF(3) 上的括号结构完整形式化 (0 postulate)
  - 与 jac_LieGroup (Jacobian 家族) 分开的独立建立; 重复内容为有意为之。
  - 结构:
  - §1 局部 2×2 GF(3) 矩阵环 (对式 Mat2T: 加法/取负/乘法)
  - §2 李括号 [X,Y] = XY − YX: 基括号表 + 反称 (81 项穷举)
  - + Jacobi 恒等式 (729 项穷举 — 结合代数交换子恒等式,
  - 逐项 refl 同时校验括号定义)
  - §3 三维旋量李代数 (so(3) 的 GF(3) 离散版): 循环括号
  - [x1,x2]=x3, [x2,x3]=x1, [x3,x1]=x2 — 反称 (9 项) + Jacobi (27 项)
- **导入 (4)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `M9`, `Basis3`
- **顶层签名 (33)**: `Mat2T`, `mzero`, `mtadd`, `mtneg`, `mtmul`, `toMat`, `br`, `brM`, `br-E11-E12`, `br-E11-E21`, `br-E12-E21`, `br-I2-any`, `br-I2-E12`, `br-E12-E12`, `asym`, `jacobi`, `Lie3`, `br3`, `add3`, `zero3`, `cyc12`, `cyc23`, `cyc31`, `neg3v`, `br3-x1x1`, `br3-x2x2`, `br3-x3x3`, `br3-x1x3`, `br3-x2x1`, `br3-x3x2`, `asym3`, `toVec`, `jacobi3`
- **质量**: `refl`×1583；无 postulate / 无 hole

## `src/Sovereign/Algebra/Lie/LieGroup.agda`

- **module**: `Sovereign.Algebra.Lie.LieGroup`
- **行数**: 437（代码 294 / 注释 41）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Lie.LieGroup
  - 离散李群 — 指数映射与有限群载体 (0 postulate)
  - 与 jac_LieGroup (Jacobian 家族) 分开的独立建立; D₄ 部分为有意重复。
  - 结构:
  - §1 离散指数映射 (一维): exp_C4 : Z/4 → Z[i] 单位群 C₄ (生成元 i)
  - + 单参子群律 exp(t+s) = exp(t)·exp(s) (16 项穷举)
  - §2 exp_C6 : Z/6 → Z[ω] 单位群 C₆ (生成元 1+ω) + 单参子群律 (36 项)
  - §3 D₄ 离散李群 ({±I,±αI}×C₂ 半直积, 扭结 σ(α)=−α):
  - 生成关系 + 64 项封闭表 — 与 jac_LieGroup §3c 同构重复
  - 对应关系 (离散李群-李代数):
  - 连续: exp: g → G, 单参子群 exp((t+s)X) = exp(tX)exp(sX)
  - 离散: exp_C4/exp_C6 为有限周期单参子群 (C₄/C₆), 同态律逐项 refl
- **导入 (7)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.RootMath.Gaussian`, `Sovereign.RootMath.Eisenstein`
- **顶层签名 (87)**: `next4g`, `expC4`, `expC4-hom`, `next6g`, `expC6`, `expC6-hom`, `Mat2G`, `gf9z`, `gf9one`, `neg-gf9`, `m2mul`, `sigm2`, `SDElem`, `neg2g`, `gen-a-square`, `gen-a-order4`, `gen-b-order2`, `twist-order2`, `d4-conjugation`, `sdE-cl-sdE`, `sdE-cl-sdS`, `sdE-cl-sdM`, `sdE-cl-sdMS`, `sdE-cl-sdA`, `sdE-cl-sdAS`, `sdE-cl-sdMA`, `sdE-cl-sdMAS`, `sdS-cl-sdE`, `sdS-cl-sdS`, `sdS-cl-sdM`, `sdS-cl-sdMS`, `sdS-cl-sdA`, `sdS-cl-sdAS`, `sdS-cl-sdMA`, `sdS-cl-sdMAS`, `sdM-cl-sdE`, `sdM-cl-sdS`, `sdM-cl-sdM`, `sdM-cl-sdMS`, `sdM-cl-sdA`, `sdM-cl-sdAS`, `sdM-cl-sdMA`, `sdM-cl-sdMAS`, `sdMS-cl-sdE`, `sdMS-cl-sdS`, `sdMS-cl-sdM`, `sdMS-cl-sdMS`, `sdMS-cl-sdA`, `sdMS-cl-sdAS`, `sdMS-cl-sdMA`, `sdMS-cl-sdMAS`, `sdA-cl-sdE`, `sdA-cl-sdS`, `sdA-cl-sdM`, `sdA-cl-sdMS`, `sdA-cl-sdA`, `sdA-cl-sdAS`, `sdA-cl-sdMA`, `sdA-cl-sdMAS`, `sdAS-cl-sdE`
  - … 其余 27 项
- **质量**: `refl`×126；无 postulate / 无 hole
