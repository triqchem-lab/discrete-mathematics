# 四个形式化定理 — 离散数学独立成果

> 全部 0 postulate, Agda 2.9.0 编译通过, $\sim$10,500 行代码

## 定理一：离散矩阵置换判定定理

**陈述**：设 $S$ 为有限集, $|S|=N$, $F:S\to S$, $M_F$ 为函数表矩阵（每列是基向量）。
则 $\det(M_F)\neq0 \iff F$ 是双射。

**价值**：把图论转移矩阵的满秩与代数置换群的封闭性严格绑定。
证明链（鸽巢原理→置换矩阵→行列式交错性）在 Agda 中 0 postulate 打通。

**Agda 模块**（位于 `Sovereign/Algebra/Jacobian/`）:
- `jac_NMatrix.agda` — 9×9 函数表矩阵构造 (toTrit)
- `jac_Matrix.agda` — 2×2 行列式全理论 (7215 行)
- `jac_Pigeonhole.agda` — 鸽巢原理 Fin 9→8
- `jac_Injectivity.agda` — 单射 ⟺ 满射

---

## 定理二：BCW 矩阵代数的离散离心定理

**陈述**：在 $\mathrm{GF}(3)/\mathrm{GF}(9)$ 上, BCW 幂零规约 $J(H)$ 存在局部退化族——
$y^3\equiv y$ 导致导数失真, 连续切空间的局部微元矩阵无法作为离散双射的单射流判据。

**价值**：否决性定理 (No-Go)。在代数上严格证明：经典 JC 的"局部→全局"范式在离散空间必然失效。

**Agda 模块**:
- `jac_GF3.agda` — $\mathrm{GF}(3)^2$ 形式导数反例
- `jac_FrobeniusBlind.agda` — $\mathrm{GF}(9)^2$ 差分算子反例 (81 点全覆盖)
- `jac_Discrete.agda` — 三种"雅可比"的区分

---

## 定理三：T⁶ 离散环面的代数闭包与无无穷远定理

**陈述**：在 $T^6=(\mathrm{GF}(3))^6$ 与原生 $\sigma(x)=x^3$ 下,
映射空间满足几何闭包 + 代数共轭 + 描述完备。无根点逃逸。

**价值**：打破经典复分析依赖"射影无穷远逃逸"的假设。
形式化验证了一个彻底没有"外部"与"无穷远"的完美有限宇宙。

**Agda 模块**:
- `jac_4320DClosure.agda` — 729 点鸽巢原理推广
- `jac_EscapeAnalysis.agda` — Alpöge 反例逃逸分析
- `Structology/T6.agda` — $T^6$ 双射编码 (1497 行)
- `Structology/TorusClosure.agda` — 三重闭包形式化 (新)
- `Structology/BurnsideT6.agda` — 轨道分解 $1\times27+13\times54=729$

---

## 定理四：0-Postulate 鸽巢原理的形式化泛函化

**陈述**：在 Agda 类型论下, 将 $\mathrm{Fin}\;N\to\mathrm{Fin}\;N$ 的内射/满射等价性
无缝映射到 $N\times N$ 矩阵行列式的代数特征上。

**价值**：cs.LO 社区的高效构造性 proof-assistant 模板。
解决高维状态机在定理证明器中的爆炸问题。

**Agda 模块**:
- `jac_Pigeonhole.agda` — REWRITE `decode9-encode9` 技巧
- `jac_Injectivity.agda` — 右逆构造 (满射→内射)
- `jac_4320DClosure.agda` — 附录 6 引用分离策略
