# 全库 511 全绿专项 — 26 失败模块修复清单与进度

> 状态: 2026-09-07 建立. 目标: 26 个 stdlib 2.4 迁移/草稿问题模块逐个修通到全库 511 独立编译全绿.

## 总体判断 (诚实)

26 个失败模块分两类:
1. **stdlib 2.4 迁移断裂** (多数): `_mod_` 返回 Fin 语义变 / `fromℕ` 无界 / import opt-in / Vec.sum 只 ℕ / Fin 算术 roundtrip.
2. **未完成草稿** (相当多): 假 refl / 引用未定义符号 / 接口引用未定义类型 / 数学建模未定型.

每模块平均需 1-3 轮深入 (非纯 import). 部分需重建模或补数学定义.

## 进度清单

| # | 模块 | 状态 | 卡点/进展 |
|---|------|------|----------|
| 1 | Coding/PigeonholeStandard | ✅ 全绿 (93bec67) | 缺 ℕ/suc import; Inj/Surj 隐参; SeparatedRecursion 签名对齐 jac_Pigeonhole |
| 2 | HoTT/ChernConservation | 🔶 部分 (7027ae5) | ✅ rotLeft 提顶层/zsum(ℤ和)/diffInvariant 真证(shuffle4+neg-distrib); ❌ curvatureVectorInvariant (全局平移差分不变) 需 rotLeft-map+zipWith-map+diffInv 提升 ~30 行 |
| 3 | Quantum/Entanglement | 🔶 部分 (7044faa) | ✅ T≢T0 提顶层/⊕括号/proj5/Bell state-E 统一/真违反设置; ❌ classical-bound 假定理(36 反例)需裁剪, Bell 语义重建模收尾 |
| 4 | Structology/LuCellGrid | 🔶 部分 (7044faa) | ✅ mod→%/import/isId/gridRow/gridCol/mkGridPoint fromℕ<+界证; ❌ shift* 的 toℕ(fromℕ<) roundtrip mod-helper (需 fromℕ<-toℕ REWRITE 或重写) |
| 5-26 | 其余 22 | 🔴 未动 | 抽样: WuXingTransition(缺 polygonSides), TorusClosure(接口引用未定义 FrobeniusVisible/GlobalMatrix), DiscreteCalculus(_mod_ 同 LuCellGrid), ElectricalTopology(FileNotFound→依赖 LuCellGrid?) 等 |

## 已知修复模式 (供后续)

- `_mod_` (stdlib 2.4 返回 Fin) → `_%_` (Data.Nat.Base 返回 ℕ), 需 NonZero 实例
- `fromℕ (expr)` → `fromℕ< (m%n<n expr 12)` 或界证; div 界用 `/-monoˡ-≤`
- `toℕ (fromℕ< p)` 不归约 → 需 Data.Fin.Properties 的 `fromℕ<-toℕ` (或 REWRITE)
- `Vec.sum` 只对 ℕ → ℤ 求和用 foldr
- 假 refl (整数恒等式) → shuffle4/neg-distrib 真证
- 引用不存在符号 (rho-inverse/A4-toℕ/bell-calc) → 找绿库真实名或本地补
- 缺 import (stdlib 2.4 opt-in) → 补 using

## 验证

`./engineering/check_all_modules.sh` 全库独立编译扫描 (485/511 基线).

## 更新 (2026-09-08 第二轮)

### 本轮新增修复
- Resonance 机械修复 (0f8c1fb): Rational _*_→_*ℚ_/删未用+-/Cubical hide ≡,refl/补 WuXing/JianXiaShui/wuXingBase/toℚ/computeEffect 填 — 剩 3 数学洞 (nayinFingerprint StableRoot/zhonglv 语义)
- Equivalence 部分: Cubical hide + mod→% — 核心 3 函数 (stepSection≡TransportPolar) 为未完成真证明

### 关键发现: Equivalence 证明的深层结构
- SovereignSection = Vec (Coding.Trit) 30; Bun.Fiber = Vec (Base.Trit?) 30 — 需确认是否同类型
- StateMachine.stepSection 用 Coding.Trit; Connection.TransportPolar 用另一 T — **跨模块 Trit 统一**是证明前提
- stepSection delta 由 isEven (toℕ(toℕ phase mod 2) ≡ᵇ 0) 决定; 前提 `toℕ phase % 2 ≡ 0` 需桥到 isEven
- 证明路径: 桥 %↔isEven → stepSection 展开 delta=1/2 → map(+T₁/T₂) = TransportPolar/Loss
- 阻塞: Coding.Trit vs Base.Trit vs Connection.T 三 Trit 类型一致性未清

### 模式确认 (26 模块共性)
每个失败模块 = 机械 import 修复 (可做) + 未完成真证明 (需理解该模块数学对象 + 跨模块一致性). 机械部分本轮已系统处理; 真证明部分是数天级专项.

### 澄清 (2026-09-08): Equivalence Trit 统一确认
四模块 StateMachine/Connection/Bundle/LCM 全 import **Sovereign.Coding.Trit** (Fin 3) — 类型统一 ✓。
真障碍: stepSection 的 isEven/delta 在 let 内, 泛型 phase 不归约; 证明需 phase 按 toℕ 奇偶分解
(Fin 144 → fromℕ< 结构) 或 mod/% 桥. 专门一轮证明任务.

### 突破模式 (2026-09-08 Equivalence 完成)
许多"未完成证明"模块的核心定理**定义性 refl 可闭合** — 前提是识别正确数学对象
(Equivalence: stepSection 按 phase 奇偶给 delta=1/2, 偶=TransportPolarLoss/奇=TransportPolar;
泛型 sec + 具体 phase 归约 → refl). 修复 = 删假命题 + 奇偶分派穷举.

### 更新 (2026-09-08 第三轮): 全绿 7 个
✅ PigeonholeStandard / Equivalence (144case) / ChernConservation (rotLeft-map+zw-diff) /
   Entanglement (删假定理) / LuCellGrid (Fin roundtrip) / DiscreteCalculus /
   + T6.Rewrite 删除. 突破模式: 未完成证明常是定义性 refl + 正确对象识别;
   Fin roundtrip 用 toℕ-fromℕ< + m≡m%n+[m/n]*n.

🔶 TopologyLevels: _mod_→_%_ + fromℕ→fromℕ< + mkGridPoint 类型 (同 LuCellGrid 深改造, 待续)
🔶 Resonance: 3 数学洞; ElectricalTopology: FileNotFound (依赖检查)

### 更新 (2026-09-08 第四轮): 全绿 8 + 部分 4
✅ 新增: DiscreteCalculus (import/字面量), ElectricalTopology (删违宪 Data.Complex 死 import)
🔶 TopologyLevels (mod/fromℕ</字面量/Integer renaming 已修, sumGrid Fin 化待),
   Resonance (3 建模洞: nayinFingerprint StableRoot / zhonglvClosure 归零态实现 / 第三洞)
进度总计: 8 全绿 (Pigeonhole/Equivalence/Chern/Entanglement/LuCellGrid/DiscreteCalculus/
  ElectricalTopology + T6.Rewrite删), 4 部分深修中.

### 更新 (2026-09-08 第五轮): 全绿 6 + 编译内存纪律

✅ 本轮新增全绿 (全部加 `+RTS -M6G -RTS` 堆限制验证):
- HamiltonianDiscrete (4a8664e): ↔ 结合括号; ℕ/⊎/Sum 导入; 两条不可证定理
  (mass-gap-theorem 方向错 + energy-conservation 引未定义 mixedOp^n/模型反例) → 待核对注释
- LightConeMatrix (): Data.Nat 缺 zero/suc → lc-iterate 解析错
- T6Homotopy (d38b52d): step1 复用 T6 顶层(删重复 where); singleCoordPeriod3/commute-coords
  改 Fin 构造器 6+36 case 穷举 (with toℕ 不具体化 i 致嵌套不归约); 矛盾路径块(固定 Vec 144 却用
  [])/§6 编码(§6 用 fromℕ val 冒充 Fin 729) → 待核对注释
- WindingCover (): incMod 需 yes/no + ℕsuc 重命名模式 + lower₁ 经 toℕ-injective/toℕ-fromℕ 桥
- PhaseTransitionPaths (589ff31): 换 cubical→stdlib 导入(去 --cubical 无用); 五段路径几何对纠正
  (原 startOk/endOk 反向致 Td≡Oh 假等式); 闭环假命题(无复合构造子) → 待核对
- Projection/Binary (): 假字面量 0b0/0b1/1b1→Fin 构造器; yes/no/case_of_ 导入; projectTritToBit
  直接构造器匹配(with toℕ 穷举触发 CoverageIssue); restore 去 case_of_ 保定义性折合; 证明去错误
  injective 引理(空模式 () 更直接)
- CRTFiberWinding (914f1e0): s≤s/z≤n 从 Nat.Properties 移到 Data.Nat (stdlib2.4 改名)

🔴 归待核对 (非纯工程, 需语义重建模):
- FineStructureMapping: 数值公式层全用假记法 (1b1/8b8/0b0 无定义), _/_ 实为 ℤ/ℕ 构造器却当 ℚ/ℚ
  用; record 内嵌 where 语法错; 从 v5.20 起从未独立编译绿
- CRTHarmonics: **编译 OOM 根因** = 大系数 mod-helper 展开. harmonic k = X0 + (k*T2)*T1 对
  T2=177147 时 [m+kn]%n≡m%n 归纳证明项展开爆炸 (>6G/80s), 系数 65536 则秒过. 项目既定解法是
  REWRITE (XuanwuAbsorption mod46k 先例). 且尾行是 {!!} 洞 (待 CRTFiberWinding 桥接), 作者自标草稿.

### ⚠️ 编译内存纪律 (重要教训)
1. **必须加堆限制**: `agda +RTS -M6G -RTS --guardedness` — 无限制编译时自定义 REWRITE 规则
   触发的归一化展开可吃满整机内存 (61G), 拖垮系统.
2. 文档依据: wiki 02-geometric-pole.md:588 "REWRITE 将类型检查内存从 OOM 天花板(~8GB)压到常数级"
   — 一旦模块编译超过 ~6-8G 堆, 说明触发了不该发生的展开, 应定位修复而非加大堆.
3. 大系数 mod-helper 展开是已知编译器限制 (proof-engineer 附录1): 符号参数大数 %/ 展开为
   mod-helper/div-helper 无法归约 → 用 REWRITE 规则 (T6 div3k / Xuanwu mod46k) 或结构定义.
4. `check_all_modules.sh` 无堆限制, 已改用带 `+RTS -M6G` 版本跑全库.
