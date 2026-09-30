# 文献来源清单 — 代码理论根据、论文与原文收集

口径：本清单只登记**本库代码/文档实际使用的理论来源**（源码注释点名者为 A 组，理论基座按《理论-代码对应审计》的组件映射为 C 组）。原文 PDF 归档于 `docs/文献/pdf/`，**全部经 %PDF 头 + 文本层抽验**（作者/标题核对后才入册）。
抓取通路：直连 + 代理 `127.0.0.1:10808`（2026-09 会话）。
版权提示：原文仅供内部研究与溯源参考，版权归原出版方；arXiv 件按各论文自述 license。**不随库再分发。**
⚠ 不可获取者一律转 **[概要卡](概要卡.md)**（自撰概要·非原文·不可作引用出处）；概要卡附录含 **DOI 级精确出处勘误表**与**外供标识符核验记录**（外供 arXiv 号实测 3/5 有误，凡错号已删件改正）。

---

## A. 代码直接引用（源码/文档注释点名）

| 理论组件 | 代码/文档锚点 | 书目 | 标识符 | 本地原文 | 状态 |
|---|---|---|---|---|---|
| Dvir 有限域挂谷下界（多项式方法） | `src/Sovereign/Problem/Kakeya/KakeyaGF3.agda:6,126-179`、`KakeyaPathology.agda:122`、`docs/Kakeya-元诊断…md:177` | Dvir, Z. *On the size of Kakeya sets in finite fields*. J. Amer. Math. Soc. 22 (2009), 1093–1097 | 期刊（无 arXiv） | `pdf/Dvir2009_Kakeya-finite-fields.pdf`（公开课程副本） | ✅ |
| 挂谷 R³ 突破（「王虹 127 页」对照件） | `KakeyaGF3.agda:70` | Wang, H.; Zahl, J. *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*. | arXiv:2502.17655 | `pdf/Wang-Zahl2025_Kakeya-R3_2502.17655.pdf` | ✅ |
| Liouville/Goldbach vs ABC 屏障背景 | `docs/duodecimal/25-liouville-goldbach-vs-abc-barrier.md:8` | Mangerel, L. 2024 | arXiv:2404.12117 | `pdf/Mangerel2024_2404.12117.pdf` | ✅ |
| DC12 论文（定理 1 幂周期闭包 / 定理 4 正确投影版） | `src/Sovereign/Problem/Fermat/FermatL4_Mod12Cycle.agda:6,17,236` | **内部件**：`docs/duodecimal/14-fermat-proof-path.md`、`16-dc12-layer-adjudication.md` | 内部 | 本地路径（见 F 组） | ✅ 内部 |

## B. 形式化平台与工具链

| 理论组件 | 锚点 | 书目 | 标识符 | 本地原文 | 状态 |
|---|---|---|---|---|---|
| Cubical Agda（HIT/univalence，A4Group 等 Cubical 模块的平台基础） | `src/Sovereign/Structology/A4Group.agda`（--cubical） | Vezzosi, A.; Mörtberg, U.; Abel, A. *Cubical Agda: A dependently typed PL with univalence and HITs*. ICFP 2019 / J. Funct. Program. 31 | DOI 10.1145/3341691 | `pdf/Vezzosi-Mortberg-Abel_CubicalAgda-JFP.pdf` | ✅ |
| 合成上同调形式化（计算版） | HoTT 系 roadmap 对照件 | Ljungström, S.; Mörtberg, A. *Computational Synthetic Cohomology Theory in HoTT* (2024; MSCS 2025) | arXiv:2401.16336 | `pdf/Ljungstrom-Mortberg2024_synthetic-cohomology_2401.16336.pdf` | ✅（⚠ 作者两人——外供「Brunerie 三人」名单与文本层不符） |
| 合成上同调 CPP 2022（Steenrod 平方） | 同上 | Brunerie, G.; Ljungström, S.; Mörtberg, A. CPP 2022, 202–217 | DOI 10.1145/3497775.3503678（⚠ 外供 arXiv:2110.04029 系错号） | — | ❌ → 概要卡（ACM 付费墙） |
| Agda 模式匹配 elaboration | `docs/agda-compiler-architecture.md:250` | Cockx, J.; Devriese, B.; Piessens, F. ICFP 2016 | DOI 10.1145/2951913.2951934 | — | ❌ → 概要卡 |
| HoTT 入门（1lab 参考轨） | `docs/1lab-README.md:232` | Rijke, E. (2022) | arXiv:2212.11082 | `pdf/Rijke2022_HoTT-intro_2212.11082.pdf` | ✅ |

## C. 理论基座：离散代数拓扑谱系（审计报告组件→文献映射）

| 理论组件 | 库内落点 | 书目 | 标识符 | 本地原文 | 状态 |
|---|---|---|---|---|---|
| 离散空间同调论（偏序集复形、边界算子） | `jac_Topology.agda` 边界矩阵/ker-span/rank 谱系 | Alexandroff, P. S. *Diskrete Räume*. Mat. Sb. N.S. 2(44):3 (1937), 501–519 | mathnet.ru:5579 | `pdf/Alexandroff1937_Diskrete-Raeume.pdf` | ✅ |
| 有限拓扑空间同伦型 — beat point/core | `Structology/T6`、`HoTT/T6Homotopy` 谱系 | Stong, R. E. *Finite topological spaces*. Trans. AMS **123(2)** (1966), 325–340 | DOI 10.1090/S0002-9947-1966-0195042-2 | `pdf/Stong1966_finite-topological-spaces.pdf`（AMS 免费，扫描件无文本层，按 DOI 标识） | ✅ |
| 有限拓扑空间弱等价 | 同上 | McCord, M. C. Duke Math. J. 33(3) (1966), 465–474 | DOI 10.1215/S0012-7094-66-03352-7 | — | ❌ → 概要卡 §4 |
| 离散同伦基本群(oid)（A-同伦） | `HoTT/HomotopyPi1.agda`、`HoTT/T6Homotopy.agda` 谱系 | Kapulkin, K.; Mavinkurve, U. *The fundamental group in discrete homotopy theory* | **arXiv:2303.06029**（文本层已验题） | `pdf/Kapulkin-Mavinkurve2023_A-homotopy-pi1_2303.06029.pdf` | ✅（⚠ 外供 arXiv:2408.05289 系错配——那是同作者《Homotopy n-types of cubical sets and graphs》，另收存档） |
| A-同伦理论源头 | 同上 | Atkin 1974（DOI 10.1068/b010051）；Barceló–Kramer–Laubenbacher–Weaver, Adv. Appl. Math. 26(2) (2001), 97–128（DOI 10.1006/aama.2000.0713） | 期刊 | — | ❌ → 概要卡 §6–7 |
| 有限偏序集离散同伦/同调 | 同上（离散 Hurewicz 对应） | Gao, Jing-Wen; Yang, Xiao-Song. *Discrete homotopy and homology theories for finite posets* | arXiv:2410.16948 | `pdf/Gao-Yang2024_discrete-homotopy-posets_2410.16948.pdf` | ✅（文本层验为二作者；外供六人名单疑为另一篇，**待人类裁决**） |
| 路径同调/digraph 同调（有向扩展点） | `jac_Topology` 潜在扩展 | Grigor'yan, A.; Lin, Y.; Muranov, Yu.; Yau, S.-T. *Homologies of path complexes and digraphs* | arXiv:1207.2834 | `pdf/Grigoryan-Lin-Muranov-Yau_homologies-path-complexes-digraphs_1207.2834.pdf` | ✅（⚠ 外供「Muranov 2022, arXiv:2203.02012」系错号且题名未见 arXiv） |
| 不忠实表示丢信息（红线先例） | `Algebra/GroupTheory/SignProjection.agda:24,98`、`Algebra/DegenerationRisk.agda:575+` | Bigelow 1999（arXiv:math/9904100 全文；另有 CRAS 329(1), 19–22）；Moody, Bull. AMS **25(2)** (1991), 379–384；Long–Paton, Topology **32(2)** (1993), 439–447 | arXiv:math/9904100 / DOI 各见勘误表 | `pdf/Bigelow1999_Burau-n5_math9904100.pdf` | ✅ Bigelow；Moody/Long-Paton ❌ → 概要卡 §1–2（⚠ `BullAMS24-2-1991-scan-unverified.pdf` 与 Moody 无关，疑可删） |
| Postnikov 塔 | `HoTT/*` roadmap 对照 | Postnikov, M. M. Тр. МИАН СССР 46 (1955), 3–158 | mathnet.ru:tm-1182 | `pdf/Postnikov1955_homotopy-theory-tm1182.pdf` | ✅ |
| 离散 Hodge 分解 | `Problem/Hodge/*`、`jac_Topology` dimH/χ | Kirchhoff 1847（DOI 10.1002/andp.18471481202）；Eckmann 1944, Comment. Math. Helv. 17(1), 240–255；Dodziuk 1976, Amer. J. Math. 98(1), 79–104 | 各 DOI 见勘误表 | — | ❌ → 概要卡 §10–11（付费墙） |
| 离散 Morse / 局部证书 | `jac_Topology` 秩下界 2×2 子式证书谱系 | Forman 1998, Adv. Math. 134(1), 90–145（DOI 10.1006/aima.1997.1650）；Panina–Zhukova, *Discrete Morse theory for moduli spaces of flexible polygons* | arXiv:1504.05139 | `pdf/Panina-Zhukova2015_discrete-morse-flexible-polygons_1504.05139.pdf` | ✅ Panina–Zhukova（⚠ 与外供 EJC 33(3) 2012 条目的对应待核对）；Forman ❌ → 概要卡 §3 |
| CRT 行列式多模算法谱系 | `jac_CRTDet.agda` 拱顶石的算法先例 | McClellan 1973, JACM 20(4), 563–588（DOI 10.1145/321784.321796，开放 TR136 副本 503 待重试）；Dixon 1982, **Math. Comp.** 38(157), 137–144 | 各 DOI 见勘误表 | — | ❌ → 概要卡 §12–13 |
| Hodge/Frobenius colevel | `Algebra/GF9.agda`、`Problem/Hodge/DeligneHodge.agda` | Wan, D.; Zhang, D. (2023–) | arXiv:2309.16290 | `pdf/Wan-Zhang2024_Hodge-Frobenius-colevel_2309.16290.pdf` | ✅ |
| McKay 对应（五重结构语境参照） | `Structology/Platonics.agda` | McKay, J. PSPUM 37 (1980), 183–186 | DOI 10.1090/pspum/037/604577 | — | ❌ → 概要卡 §16（⚠ 库内「两两不可约」是自证命题，非 McKay 推论） |
| 算法信息论（M_F 概念对照） | `jac_FunctionTable` | Chaitin 1975, JACM 22(3), 329–340 | DOI 10.1145/321892.321894 | — | ❌ → 概要卡 §17（无直接依赖） |

## D. RH 元诊断线（`docs/Riemann/RH-GRH-文献检索与元理论断层诊断.md` 引用）

| 路线 | 书目 | 标识符 | 本地原文 | 状态 |
|---|---|---|---|---|
| 几何化 Langlands / Z 的几何 | Borger, J.（Selecta Math. 2011 前身稿） | arXiv:0906.3146 | `pdf/Borger2009_geometry-of-Z_0906.3146.pdf` | ✅ |
| Deninger 动力系统 / 正则化行列式 | Deninger, C. | arXiv:1807.06400 | `pdf/Deninger2018_1807.06400.pdf` | ✅ |
| Connes 阿代尔类空间 | Connes, A. (Selecta Math. 1996–1999) | arXiv:math/9811068 | `pdf/Connes1999_adele-class-space_math9811068.pdf` | ✅ |

## E. 物理锚定（`docs/creation-law-from-gf3.md` / `造物法则` 引用）

| 锚定 | 书目 | 标识符 | 本地原文 | 状态 |
|---|---|---|---|---|
| QCD 真空熔化/再冻结（实验锚定登记） | ALICE Collaboration (2024) | arXiv:2403.11318 | `pdf/ALICE2024_QCD-vacuum_2403.11318.pdf` | ✅ |

## F. 内部理论原文（本地已有，不需下载）

| 理论根据 | 路径 |
|---|---|
| 展示群八要素 / 类型论展示群（权威定义） | `docs/duodecimal/11-type-theory-presentation.md`、`12-rigorous-type-theory.md`、`20-dc-type-theory-positioning.md` |
| 术语红线 / 本体论（DC 本源 vs C₁₂/R₁₂/Doz 投影） | `docs/duodecimal/08-terminology.md` §7 |
| 代数复数五种 / 范数坍缩 / FLT 边界 | `docs/duodecimal/09`、`10`、`13/15/16`（含 DC12 L5 反例、L7 不可证） |
| CRT = 物理波系统（非模运算定理） | `memory/crt-wave-physics-not-modular-arithmetic.md` |
| 相位不可约性元公理（「规则 40」外部编号的库内实名） | 同上 + `docs/duodecimal/19-full-green-26-fix.md`（本体论裁定 08f508c） |
| REWRITE 语义设计合法性 | `/data/work/docs/wiki/02-geometric-pole.md` C.3.1 |
| 离散代数拓扑宪法 / 元诊断三重完备性 | `docs/离散代数拓扑宪法.md`、`docs/Kakeya-元诊断-连续统病态vs离散自愈.md` |
| 三层裁决（Agda 通过 ≠ 数学通过） | proof_dag 流水 325 + proof-engineer SKILL 附录 9 |

## G. 收录终态与统计（第三轮）

- **原文已获 20 件**（全部 %PDF + 文本层抽验；Stong 为无文本层扫描件、按 DOI 标识）：A 组 3 + B 组 3 + C 组 9（Alexandroff、Stong、Kapulkin 2303.06029、Kapulkin 2408.05289 存档、Gao-Yang、GLMY 1207.2834、Bigelow、Postnikov、Panina-Zhukova、Wan-Zhang）+ D 组 3 + E 组 1。
- **身份待确认 1 件**：`pdf/BullAMS24-2-1991-scan-unverified.pdf`（Bull. AMS 24(2) 刊头扫描；**已证与 Moody 无关**，疑可删，留证待人类处置）。
- **转概要卡**：McCord、Moody、Long-Paton、Forman、McClellan、Dixon、Kirchhoff、Eckmann、Dodziuk、Atkin、Barceló 系、McKay、Chaitin、CPP 2022 合成上同调、CW/Serre 形式化（出处待核对）——见 [概要卡](概要卡.md) 及其**勘误附录（DOI 级）**。
- **外供标识符核验记录**：arXiv 号 3/5 错（2203.02012 / math/0511116 / 2110.04029）、1 处张冠李戴（2408.05289）、卷期页码 2 处错（Moody 25(2)、Long-Paton 32(2)）——详见概要卡附录 §2；**Gao 作者组冲突待人类裁决**。
- **教科书级背景（不下载）**：Lidl–Niederreiter《Finite Fields》、标准同调代数教材。⚠ CRT 本体层=物理波系统（F 组），`crt12` 环同构是投影层工具，引用勿混。

---
（收集人：math-proof 会话；清单与《理论-代码对应审计-大衍离散全息框架.md》组件编号互为索引。）
