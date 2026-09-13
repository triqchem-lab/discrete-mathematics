# 目录 `src/Sovereign/Problem/Kakeya/` 逐模块审计记录

共 4 个模块。


## `src/Sovereign/Problem/Kakeya/KakeyaGF3.agda`

- **module**: `Sovereign.Problem.Kakeya.KakeyaGF3`
- **行数**: 204（代码 68 / 注释 98）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | KakeyaGF3 — 挂谷猜想的 GF(3) 基座: 向量空间/方向/直线/Dvir下界
  - 数学背景:
  - Dvir (2008): |K| ≥ C_n q^n, 任意有限域 F_q, 2页纸多项式方法
  - 王虹 & Zahl (2025): ℝ³ 挂谷猜想, 127页解析学
  - 本模块只处理 GF(3) 上的结构 (无共轭):
  - GF(3)^n 向量空间, 射影方向空间, 直线, Dvir 下界
  - GF(9) Frobenius 共轭见 KakeyaGF9.agda
  - 复用:
  - Sovereign.Base.Trit — GF(3) 底层
  - Sovereign.Algebra.Jacobian.jac_Pigeonhole — 鸽巢原理
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `Dir2`
- **顶层签名 (30)**: `GF3Vec`, `GF3¹`, `GF3²`, `GF3³`, `card-GF3¹`, `card-GF3²`, `card-GF3³`, `card-GF3¹-ok`, `card-GF3²-ok`, `card-GF3³-ok`, `dir2-card`, `dir2-card-formula`, `dir3-card`, `dir3-card-formula`, `Point2`, `DirVec2`, `line-point`, `line-size`, `line-nonempty`, `dvir-bound-2`, `dvir-bound-3`, `dvir-2-valid`, `dvir-3-valid`, `overlap-arithmetic`, `pathology-continuum`, `healing-discrete-n2`, `healing-discrete-n3`, `pathology-witness`, `healing-n2`, `healing-n3`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Problem/Kakeya/KakeyaGF9.agda`

- **module**: `Sovereign.Problem.Kakeya.KakeyaGF9`
- **行数**: 180（代码 52 / 注释 102）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | KakeyaGF9 — 挂谷猜想的 GF(9) 原生共轭结构 (大衍独有)
  - GF(9) = GF(3)[α]/(α²+1), Gal(GF(9)/GF(3)) ≅ C₂
  - Frobenius 自同构 σ(a+bα) = a-bα 是原生 Galois 共轭
  - 与 Dvir 的核心区别:
  - Dvir 的多项式方法对任意 F_q 成立, 不依赖共轭
  - 大衍锁定 GF(9): σ 是原生共轭, 对应复共轭的离散投影
  - GF(2) 反例: GF(2) 无非平凡自同构, Dvir 仍成立 → 他不依赖共轭
  - 连续统特征0: 无 Frobenius → 共轭缺失 → 病态根因
  - 复用: Sovereign.Algebra.GF9 — 全部 Frobenius/范数/迹/乘法群定理
  - 0 postulate.
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (14)**: `σ`, `σ²-id`, `σ-mul`, `σ-α`, `α²-neg1`, `norm-in-gf3`, `norm-conj-inv`, `trace-in-gf3`, `fixed-pt-gf3`, `α-not-fixed`, `gf3-self-conjugate`, `gf9star-cyclic`, `σ-on-directions`, `horiz-fixed`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Problem/Kakeya/KakeyaMF.agda`

- **module**: `Sovereign.Problem.Kakeya.KakeyaMF`
- **行数**: 258（代码 84 / 注释 140）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | KakeyaMF — M_F 全局编码: 大衍框架独有的挂谷判定协议
  - 核心定理: det(M_F) ≠ 0 ⟺ F 双射 ⟺ 挂谷集完备
  - 与 Dvir 的本质区别:
  - Dvir: 多项式因子定理 → 点集大小下界 (专病专治)
  - 大衍: M_F 全局编码 → 任意映射的双射性判定 (通用协议)
  - 16年空白的根因:
  - Dvir 的方法是"局域化计数", 不是"全局映射编码"
  - 没有人将挂谷问题翻译为 M_F 的行列式判定
  - 大衍框架首次完成这一翻译
  - 复用:
  - jac_Pigeonhole — encode9/decode9 (GF3² ↔ Fin 9 双射)
  - jac_CRTDet — det2-gf3 (GF(3) 2×2 行列式)
  - GF9 — galoisConjugate (Frobenius 共轭)
  - KakeyaGF3 — Dir2/方向空间
  - 0 postulate.
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Jacobian.jac_Pigeonhole`, `Sovereign.Algebra.Jacobian.jac_CRTDet`, `Sovereign.Problem.Kakeya.KakeyaGF3`
- **顶层签名 (17)**: `MF3`, `if-eq3`, `MF3-id`, `encode9-bijection`, `decode9-bijection`, `encode9-inj`, `pigeonhole-gf3`, `det-I₂-nonzero`, `det-I₂-eq-1`, `KakeyaChoice`, `KakeyaSet`, `σ-mat`, `σ-preserves-mul`, `σ-involutive`, `id-det-nonzero`, `continuum-cannot-MF`, `continuum-cannot-MF-witness`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Problem/Kakeya/KakeyaPathology.agda`

- **module**: `Sovereign.Problem.Kakeya.KakeyaPathology`
- **行数**: 272（代码 101 / 注释 135）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | KakeyaPathology — 挂谷猜想的三重完备性病态诊断
  - 元诊断标尺 (大衍框架核心):
  - 1. 几何闭包: 空间是否紧致闭合, 是否存在无穷远逃逸
  - 2. 原生共轭: 是否存在 Frobenius 自同构提供代数刚性
  - 3. 描述完备: 方向空间是否有限, 能否构造全局矩阵
  - 诊断结论:
  - 连续统 ℝⁿ: 三重缺失 → 病态 (127页解析拉锯)
  - 离散 GF(3)ⁿ/GF(9): 三重自愈 → 健康 (2页代数闭合)
  - 复用:
  - Sovereign.Algebra.GF9 — galoisConjugate/Frobenius 同态/范数/迹
  - Sovereign.Base.Trit — GF(3) 底层
  - KakeyaGF3 — 方向空间/直线/Dvir 下界
  - 0 postulate.
- **导入 (9)**: `Data.Nat`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Problem.Kakeya.KakeyaGF3`
- **data 类型**: `Completeness`
- **record 类型**: `Diagnosis`
- **顶层签名 (22)**: `continuum-diagnosis`, `continuum-pathological`, `continuum-no-conjugation`, `continuum-uncountable`, `discrete-diagnosis`, `discrete-has-closure`, `discrete-has-conjugation`, `discrete-has-completeness`, `σ`, `σ-involutive`, `σ-multiplicative`, `σ-negates-alpha`, `α-sq-neg1`, `norm-σ-invariant`, `fixed-pts-are-gf3`, `α-not-in-gf3`, `gf3-self-conj`, `continuum-pages`, `discrete-pages`, `pathology-ratio-exceeds-1`, `continuum-triple-failure`, `discrete-triple-healing`
- **质量**: `refl`×8；无 postulate / 无 hole
