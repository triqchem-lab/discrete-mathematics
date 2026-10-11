# QUALITY.batch0-machine —— 全库机器统计底料

> 生成：2026-10-11｜工具：`engineering/quality_stats.py`（可复跑）｜零源码改动
> 口径：剥注释计数｜多行签名容错（`^name :` + 续行合并）｜定理形 = 类型含 ≡/≢/¬/≤/</↔/≃/⊥

## 一、全库总量

| 指标 | 值 |
|---|---|
| 模块数 | 836 |
| 总行数 | 167002 |
| 顶层签名 | 14814 |
| 定理形签名 | 9031 |
| 证明活动标记 | 33640 |
| postulate 计数（模块内出现） | 57 |
| hole（{!）计数 | 1 |
| 跨文件重复顶层名组 | 902 |

## 二、按目录分组

| 目录 | 模块 | 行 | 签名 | 定理形 | 活动 | 活动/定理 | post | hole |
|---|---|---|---|---|---|---|---|---|
| (root) | 38 | 3910 | 386 | 225 | 931 | 4.1 | 4 | 0 |
| AI | 1 | 418 | 22 | 9 | 4 | 0.4 | 0 | 0 |
| Algebra | 258 | 66633 | 6092 | 3972 | 16571 | 4.2 | 2 | 0 |
| Analysis | 42 | 7703 | 662 | 440 | 1367 | 3.1 | 0 | 0 |
| Applied | 41 | 7163 | 656 | 540 | 1013 | 1.9 | 0 | 0 |
| Arithmetic | 3 | 201 | 16 | 4 | 45 | 11.2 | 0 | 0 |
| Base | 7 | 769 | 81 | 35 | 161 | 4.6 | 0 | 0 |
| Coding | 8 | 2828 | 208 | 143 | 632 | 4.4 | 0 | 0 |
| Completeness | 3 | 507 | 34 | 16 | 26 | 1.6 | 0 | 0 |
| Constitution | 5 | 1073 | 76 | 40 | 76 | 1.9 | 1 | 0 |
| Coupling | 11 | 2875 | 206 | 78 | 336 | 4.3 | 18 | 0 |
| Cubical | 3 | 338 | 34 | 32 | 103 | 3.2 | 0 | 0 |
| Density | 2 | 494 | 32 | 6 | 15 | 2.5 | 0 | 0 |
| Diagnosis | 1 | 259 | 11 | 1 | 3 | 3.0 | 0 | 0 |
| Engine | 2 | 334 | 11 | 1 | 71 | 71.0 | 0 | 0 |
| Format | 8 | 1792 | 204 | 121 | 287 | 2.4 | 0 | 0 |
| Foundation | 1 | 159 | 0 | 0 | 1 | 0.0 | 0 | 0 |
| Geometry | 14 | 1298 | 147 | 51 | 182 | 3.6 | 7 | 0 |
| HoTT | 26 | 4532 | 331 | 164 | 613 | 3.7 | 9 | 0 |
| MetaStructure | 2 | 411 | 18 | 4 | 16 | 4.0 | 0 | 0 |
| PDE | 4 | 1324 | 68 | 39 | 281 | 7.2 | 0 | 0 |
| Physics | 63 | 13864 | 1168 | 659 | 1832 | 2.8 | 3 | 0 |
| Problem | 118 | 16052 | 1505 | 917 | 2335 | 2.5 | 0 | 0 |
| Projection | 4 | 462 | 32 | 18 | 74 | 4.1 | 0 | 0 |
| Quantum | 5 | 1635 | 177 | 103 | 129 | 1.3 | 0 | 0 |
| RootMath | 8 | 2320 | 225 | 98 | 367 | 3.7 | 0 | 0 |
| Structology | 73 | 18732 | 1686 | 956 | 4900 | 5.1 | 12 | 0 |
| Topology | 52 | 6610 | 528 | 241 | 819 | 3.4 | 0 | 0 |
| Trust | 11 | 999 | 53 | 29 | 47 | 1.6 | 1 | 0 |
| Verify | 2 | 291 | 39 | 0 | 0 | 0.0 | 0 | 0 |
| _archive | 20 | 1016 | 106 | 89 | 403 | 4.5 | 0 | 1 |

## 三、异常清单

### 3.1 postulate>0（25 模块——kind 登记面）
- `src/Generated/T6Verification.agda` post=1
- `src/Sovereign/Algebra/CartanMatrix.agda` post=2
- `src/Sovereign/Constitution/WindingAsymmetry.agda` post=1
- `src/Sovereign/Coupling/CartanTorsion.agda` post=8
- `src/Sovereign/Coupling/Entanglement.agda` post=3
- `src/Sovereign/Coupling/TQ10.agda` post=3
- `src/Sovereign/Coupling/Zhonglv.agda` post=3
- `src/Sovereign/Coupling/ZhonglvPhaseSync.agda` post=1
- `src/Sovereign/Geometry/ConformalCore.agda` post=2
- `src/Sovereign/Geometry/ProjectiveCore.agda` post=1
- `src/Sovereign/Geometry/ProjectiveOrbit.agda` post=4
- `src/Sovereign/HoTT/CRTFiberWinding.agda` post=7
- `src/Sovereign/HoTT/DiscreteCCHM.agda` post=2
- `src/Sovereign/Physics/QuartzPhonon.agda` post=3
- `src/Sovereign/Structology/Aether.agda` post=2
- `src/Sovereign/Structology/MagicSquareM4.agda` post=1
- `src/Sovereign/Structology/Platonics.agda` post=3
- `src/Sovereign/Structology/T6.agda` post=2
- `src/Sovereign/Structology/T6Rewrite.agda` post=1
- `src/Sovereign/Structology/XuanwuAbsorption.agda` post=2
- `src/Sovereign/Structology/XuanwuAbsorptionRewrite.agda` post=1
- `src/Sovereign/Trust/TwoViewRewritten.agda` post=1
- `src/Techniques/GapProbe10.agda` post=1
- `src/Techniques/GapProbe9.agda` post=1
- `src/Techniques/Pgm2.agda` post=1

### 3.2 hole>0（1 模块）
- `src/Sovereign/_archive/probes-tmp/ProbeJ.agda` hole=1

### 3.3 活动=0 且签名>0（32 模块——空壳嫌疑面，需人工四问）
- `src/ProbeH.agda` sigs=1（其中定理形 1）
- `src/Sovereign/Algebra/DiscreteJacobi.agda` sigs=1（其中定理形 0）
- `src/Sovereign/Algebra/HenselMigration129140163.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration14348907.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration1594323.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration177147.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration243.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration43046721.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration4782969.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration531441.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration59049.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration6561.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration729.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/HenselMigration81.agda` sigs=6（其中定理形 4）
- `src/Sovereign/Algebra/LaurentBase.agda` sigs=10（其中定理形 0）
- `src/Sovereign/Algebra/Matrix2.agda` sigs=6（其中定理形 0）
- `src/Sovereign/Base/Invariants.agda` sigs=10（其中定理形 0）
- `src/Sovereign/Base/Lü.agda` sigs=2（其中定理形 0）
- `src/Sovereign/Format/TQ10.agda` sigs=12（其中定理形 0）
- `src/Sovereign/Geometry/Tryte.agda` sigs=10（其中定理形 1）
- `src/Sovereign/HoTT/Bundle.agda` sigs=6（其中定理形 1）
- `src/Sovereign/Physics/FineStructureMapping.agda` sigs=11（其中定理形 0）
- `src/Sovereign/Physics/Scaling.agda` sigs=6（其中定理形 0）
- `src/Sovereign/Projection/Decimal/Axioms.agda` sigs=8（其中定理形 0）
- `src/Sovereign/Structology/MatrixZω.agda` sigs=6（其中定理形 0）
- `src/Sovereign/Trust/External.agda` sigs=14（其中定理形 0）
- `src/Sovereign/Verify/DuodecOracle.agda` sigs=23（其中定理形 0）
- `src/Sovereign/Verify/KernelOracle.agda` sigs=16（其中定理形 0）
- `src/Sovereign/_archive/probes-tmp/ProbeH.agda` sigs=1（其中定理形 1）
- `src/Sovereign/_archive/probes-tmp/ProbeI.agda` sigs=2（其中定理形 1）
- `src/Techniques/T3.agda` sigs=1（其中定理形 0）
- `src/_archive/test_chiral.agda` sigs=2（其中定理形 0）

## 四、跨文件重复顶层名（同名≠重复——dup-names 判例口径，交人工判）

共 902 组；按涉及文件数降序前 30：

- `root-1` ×15
- `mig-root-0` ×13
- `mig-nonRoot-4` ×11
- `mig-nonRoot-3` ×11
- `mig-root-last` ×11
- `mig-nonRoot-2` ×11
- `mig-nonRoot-1` ×11
- `1≢0` ×10
- `negate-⊕` ×10
- `_↔_` ×10
- `_≢_` ×9
- `step` ×9
- `assocP` ×8
- `shift` ×8
- `sum3` ×8
- `frobenius-is-cube` ×7
- `_+₃_` ×7
- `iterate` ×7
- `M` ×7
- `SOVEREIGN_LCM` ×7
- `swap3` ×6
- `T₀≢T₁` ×6
- `alpha` ×6
- `act` ×6
- `sum4` ×6
- `add3` ×6
- `q3` ×6
- `bubble4` ×5
- `bubble6` ×5
- `bubble3` ×5

## 五、结构 lint 汇总（外部工具 `check_structure_lint.sh`，2026-10-11 实跑）

- **ERROR 44 / WARN 1**——主类：`_archive/` 目录分量非法（归档面固有，非库内债）+ module 名≠路径残件 + where 滥用；
- 修法口径照工具输出（路径↔module 对齐；where 只留函数子句）；
- ⚠ 归档面（`src/Sovereign/_archive/`）不入模块空间属设计，其 ERROR 不计入库债——batch1-8 评分时按「库内/归档面」分列。

## 六、口径备注（供 batch1-8 引用）
1. **多行签名容错**已内置（`^name :` + 续行合并——第三案教训）；
2. **活动=0 ≠ 空壳**：具名委托型（body=上游引理引用，如 HenselMigration 族）活动为 0 但可能是真委托——**四问人工判**（IntByParts 先例：委托别名非空壳）；
3. post=57 为**出现次数**（含多行块内多个名）——kind 登记面按块/名逐个核；
4. 重复顶层名 902 组为**同名≠重复**表象（dup-names 判例口径）——交人工判三型。

> ⚠ **「定理形签名」口径警示**：9,031 = 按**类型形状**过滤（签名类型文本含 ≡/≢/¬/≤/</↔/≃/⊥ 族符号）——**类型形状判据，非证明体判据**（「看起来像定理」而非「结构定义的定理」）。真定理计数以台账 proven（482）为准；活动/定理比（3.7）为深度参照非定理判据。
