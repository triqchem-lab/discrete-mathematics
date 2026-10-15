# D1 verdict（**裁决已下：取一般图答案路线**——`_PEH14` 施工中）

> 2026-10-13 晚 | 人类裁决原话：「坚持一般图答案 ，开工 ，桥件甲1」
> ⇒ **选草案 §四 裁法乙方向**（不接受「实例面已收即结案」）：目标 = 一般图上 `π₂ᵈ` 拼接交换性/阿贝尔性的**机器级判定**；施工件 `src/_PEH14.agda`（先 oracle 精确枚举找分离对 → 再在 Agda 里把分离器不变量形式化 → 导出 `¬ (∀ q r → add2⁺ q r ≡ add2⁺ r q)` 型反证）。
> 权威 = `proof_dag` 台账 + 回执；本文档为投影。E6（selfloop 单点性）由 `_PEH9` 走**反裁**路线（该件尚**未编译通过**，其「单点性为假」**不得预先援引**）。

---

## 一、判据 D1 的原始形式

人类 2026-10-13 指定：**计算 π₂ᵈ(Gcmp)** —— 决定 A1c（πₙᵈ 阿贝尔性）是否依赖 A2（分水岭/backtrack）。判据 = 「π₂ᵈ(Gcmp, selfloop-walk) 的商类数是否 > 1」。

## 二、已到手的证据（全部回执绑定）

| # | 事实 | 证据 | 状态 |
|---|---|---|---|
| E1 | `π₂ᵈ` 基点 **nil 侧平凡**：正长链不入口 nil（通用图） | `no-chain-into-nil : Pos (len w) → Ω2Walk G x w (nil x) → ⊥`（`c2.gcmp-selfloop-neighborhood`，回执 `8e9c0119…`） | proven |
| E2 | Ω₂ᵈ 载体单点（Σ-PathP，左刚右自由 flex-rigid） | `routeB.SP-singleton`（回执 `aca63ab1…`） | proven |
| E3 | 细商级 suffix 全形 `[cons2 s (cons2 s̄ c)] ≡ [c]`（内消） | `Y.xian-pi2-wr-suffix`（回执 `e5f1fd08…`） | proven |
| E4 | 粗商/细商同核 + 三商一致性（两向点级恒等） | `Y2.wr-plus-coherent-bij`（回执 `60de5454…`） | proven |
| E5 | selfloop 邻域枚举 + `twoloop` 出口 witness（链结构不再是纯交替） | `D1.selfloop-batch1`（回执 `7a455e11…`） | proven（batch1） |
| E6 | **selfloop 商类列举主定理** | `_PEH9`（子代理在飞） | **待填** |
| E7 | π₁ᵈ(Gcmp) 恰两类 + 与单点不同构（类型级） | `PN2.pio1-noiso`（回执 `def297f4…`） | proven |

## 三、E6 空槽（_PEH9 回报后填入）

```
pi2-gcmp-selfloop-singleton : (c : Ω2Walk Gcmp selfloop-walk selfloop-walk)
                            → [ c ] ≡ [ nil2 selfloop-walk ]
状态：**已结（机器反裁）**——`src/_PEH9.agda` 回执 `80cdc7a5…`（exit 0 / 12.3s / 0 postulate / 0 hole），台账节点 `D1.selfloop-refuted`（A 级 proven）。
 结论：**batch1 的单点性命题被机器否证**——`¬ ((c : Ω2Walk Gcmp fzero SL SL) → [ c ] ≡ [ nil2 SL ])`（细商 `no-pi2-gcmp-selfloop-singleton` 与粗商 `…-singleton⁺` **两面各一份**，另有 `D1-refuted` 原形反证）。
 构造：four-cycle 反例 + 可计算 xor 折叠不变量 F（φ = AStep 三角数据值）+ F 在 `Ω3Walk-wr`／`Ω3Step⁺` 下不变 ⇒ 双面 rec 提升 `F-rec`/`F-rec⁺`；计算件 `chk-F-c4 : F four-cycle ≡ true`、`chk-F-nil2 : F (nil2 SL) ≡ false`。
 **附带否证**：batch1 的前提「出口闭包 ∈ {SL, twoloop}」**为假**（expand 出口集含 TW/T4 型目标）⇒ 其归纳路线不通。
 **接管记录**：子代理 cdabee4e 静默 19 分钟后失联且稿不编译（K 墙：`resp-wrF` 双链共基点 `wa wa` ⇒ 自反式 `wa = wa` 不可消）；主台按判定死亡协议 v3.1 接管，**一处修型即通**（签名改双独立索引 `{wa wb}`——陈述严格更强，证明体逐字未动）。
```

## 四、两种裁法（依 E6 结果分支）

**裁法 甲（E6 = 单点 ⇒ π₂ᵈ(Gcmp, selfloop) 平凡）**
- 则 Gcmp 上 π₂ᵈ **平凡**，阿贝尔性无信息量；D1 → 「Gcmp 实例**无法**分辨阿贝尔性 vs 逆元存在性」；
- 结论：**A1c 与 A2 的解耦问题在 Gcmp 上不可判**，须换更强实例（≥3 顶点 + 双平行边，或 G×G）——转入「D1 一般化」（= D1D3 报告的 Mergeable 判据面）。
- A1c 的**可独立证成分** = E–H 弱形式五件（已收，见 §五）。

**裁法 乙（E6 = 多类 ⇒ π₂ᵈ(Gcmp, selfloop) 非平凡）** ← **本轮实测命中此支（E6 = 机器反裁 ⇒ 至少两类）**
- 则 π₂ᵈ(Gcmp) 有真正的 2-腔类；结合 E1（nil 侧平凡）⇒ **基点分歧**现象在类型级成立（π₂ᵈ 依赖基点）；
- 进一步：π₁ᵈ(Gcmp) 是幂等幺半群（无逆）⇒ Ω² 层拼接无逆 ⇒ 该 2-腔类**不是群**（幂等/无逆）；
- 结论：**A1c 的「群结构」部分依赖 A2**（逆元供给）；「阿贝尔性」部分仍可独立（限于分类坍缩实例）。

## 五、E–H 独立面已收（本轮定稿、**含一处关键证伪**）

五件记录收案（`EH-WeakForm`，`_PEH10`，回执 `dfbbb20e…`）：

| 件 | 内容 | 状态 |
|---|---|---|
| e1 | 商层 suffix 良定义（泛基，粗商） | proven（`_PEH4` 回执 `67054b9f…`） |
| e2 | `AStep-++w-comm`（+ 对偶 commˡ + 基步 AStep-cong-cons） | proven（`_PEH8` 回执 `c265cafd…`） |
| e3 | `E-H-interchange`（AHomotopy 闭包层 `trans' (gen∘) (gen∘)`） | proven（同 e2） |
| e4 | 拼接交换性：**泛型形被证伪**；Gcmp 实例成立（分类坍缩承载） | proven（`PEH10.e4-abelian`） |
| e5 | 幂等传导：`idem-conduct`（walk 级全称）+ 商级全类幂等；Gskel 侧边界定谳 `no-idem-sk` | proven（`PEH10.e5-idem`） |

**⚠ 关键澄清（推翻会话早前的乐观陈述）**：经典 Eckmann–Hilton 的阿贝尔性来自**两个不同的幺半运算**（两个拼接各自成群）；本库 walk 层**只有一个拼接运算**，故「单位 + interchange ⇒ 交换」在**一般图上不成立**（非交换幺半群结构性存在），仅在**分类坍缩的实例**（如 Gcmp 恰两类）上成立。**因此 A1c 不能表述为「πₙᵈ 阿贝尔（一般图）」**——正确表述见下。

## 六、A1c 的精确分解（本草案的裁定句）

```
A1c = A1c-a（阿贝尔性，实例面）  ∧  A1c-b（逆元/群结构，接口面）
其中：
  A1c-a = 「分类坍缩实例上 π₁ᵈ/π₂ᵈ 的拼接交换」（_PEH10 已证 Gcmp 实例 + 泛型单位件）
  A1c-b = 「π₂ᵈ 有逆」 ⇔ A2 域反射/backtrack 面在 Ω² 层生效（**未证**；与顺序②桥件同根）
```

**给人类的裁决要点**：
1. 若接受「A1c 仅在实例面 + 逆元接口归 A2」的分解 ⇒ 现在即可**结束 D1 判据**（不必再算一般图 π₂ᵈ），A1c 的半份（A1c-a）已 proven 收案；
2. 若坚持要**一般图**上的答案 ⇒ 需开「D1 一般化」（Mergeable 判据 + ≥3 顶点双平行边实例的机器化反例），估 150-250 行，且首要是**反例搜索**（可能直接证伪一般阿贝尔性——本草案 §五 已给出反例的数学依据）。

---

**「已证/未证」分界**：§二 全表有回执；§五 五件有回执；E6 空槽、A1c-b、D1 一般化均**未证**。本文档任何「裁定」均为**待人类裁决的方案**，不是定理。
