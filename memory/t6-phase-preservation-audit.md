# T⁶ 相位保真审计：判据第③层（维数塌缩截断）形式化锚定 ｜2026-09-24

> **问题**：T⁶ 侧哪些命题显式承载 3D+ 球谐矢量相位（本源），哪些只是投影，
> 哪些是已拒绝的截断？检索词表：T⁶/环面/相位/球谐/矢量/零冥/投影/维数/表示/特征标。

## 一、本源承载（显式携带 3D+ 矢量相位信息）

| 承载点 | 内容 | 锚点 |
| --- | --- | --- |
| C₄ 相位纤维 | DuodecPoint = GF(3)×C₄ 平凡丛：每元素不可约携带 90° 旋转状态 | `DuodecClock.agda:210`；12 号定义 2.6 |
| **A₄ 矢量表示** | `A4Irrep`：`dim V3 = 3`（l=1 矢量表示）+ 三个 1 维标量 + `dimSqSum ≡ 12` + 特征标表 + ⟨χ,χ⟩=12 判据 | `A4Representations.agda:94-109` |
| T⁶ 格点 + 谱投影 | orbitStabilizer：Orbit=空间域轨迹，Stab=频率域驻波，A₄/Stab=**相位等价类** | `T6.agda:1010-1036` |
| **π₁ 不截断** | `π₁(T⁶) ≅ T⁶Lattice`（离散格点加法群本身；**非 ℤ⁶ 数值缠绕**） | `HoTT/T6Homotopy.agda:9,143-148,191` |
| 零冥族 | 多维相位同时归零（五字段；归零是矢量相位回归的**动态过程**） | `DCGroup.agda:120`；`Algebra/ZeroCrossing.agda:7,16`；`Tetration.agda:160` |
| 球谐方向编码 | TQ10 `wuxing_mask` 高 5 位 = 球谐方向索引（0–11） | `Format/TQ10.agda:121`；`Coupling/TQ10.agda:50` |
| 相位场 | NSEPhaseField `phase-irreducible:102`（C₄ 不可约，禁压成幅度） | `Physics/NSEPhaseField.agda:102` |
| 仲吕相位同步 | 零冥族三源之一（归零的第三种形态） | `Coupling/ZhonglvPhaseSync.agda` |
| 通用表示层 | `Representation`/`Character`/`VerifiedRepresentationTheory` records | `Algebra/Holographic/Representation.agda:33,39,97` |

## 二、投影（合法，须带屏障，禁止回流本源）

`SignProjection`（C₄→C₂，跨层屏障）｜`toDuodec`（→C₁₂，有损投影标记）｜R₁₂/Doz｜
Platonics 的 S² 投影结构（:472「非坐标映射，是拓扑不变量保留」）｜
orbitStabilizer 的**计数应用**侧（4320D、144/46 数值）｜17 号 DC-Fourier（频域投影工具）。

## 三、已拒绝的截断（库内有警告记录）

- **2D 投影面编码球谐相位**：`Platonics.agda:468`「它试图在投影面上编码球谐相位，
  但相位信息在 S³ 中」「tetrahedralCell 在 2D 层提问本身就是方向错误」。
- **π₁ 截断（高维同伦砍到一维）**：`Platonics.agda:470`「HoTT/Cubical 拒绝 π₁ 截断
  正是此意」；T6Homotopy 的格点版 π₁ 取代「圆周率基本群」式 ℤ 缠绕数。
- **C₄→C₂ 非忠实商**：相位不可约性元公理禁（memory/crt 文档 :77）。
- **NSEOnT6 纯幅度建模**：memory/nse-t6-discrete-findings.md:69 记录过违规与修正。

## 四、完整性缺口（≠截断：信息在，统一对象缺）

球谐矢量内容**分布式承载**于 C₄ 纤维 + A4Irrep V3 + TQ10 方向索引 + T⁶ 格点，
但**统一命名对象**（如 `SphericalVector` record：T⁶ 相位格点 × C₄ 纤维 × V3 表示的
绑定）**不存在**。判为**完整性缺口**（bridge 类，would_help 关系），非信息截断
——截断是丢信息，这里信息各就各位、缺的是一句「它们是同一个对象」的桥。

## 五、结论

判据第③层在库内**有形式化锚定且无违规**：T⁶ 离散商空间 + C₄ 纤维 + A₄ 矢量表示
+ 格点版 π₁ 联手保住 3D+ 相位；已拒截断均有警告记录。遗留 = 一个统一桥对象
（登记 `T6.spherical-vector-bridge`），供后续裁决是否补形式化。
