# 待核对清单 (2026-09-08 全库修复专项)

> 这些项不是纯编译问题, 需要语义/物理/数学核对后才能修复.
> 均已在源码中标注 `待核对` 或 `[待核对·...]` 注释保留原文.
> 修复原则: 不删改物理定义; 编译通过 ≠ 物理正确; 真命题可证, 假命题裁剪.

## A. 数值/公式建模未定型 (需核对物理/数学公式)

### A1. FineStructureMapping.agda (从未独立编译绿)
- 数值公式层全用假记法: `1b1`/`8b8`/`4b4`/`3b3`/`2b2` 无定义 (作者想写 1/8 等)
- `_/_` 实为 ℤ/ℕ 构造器 (stdlib), 却被当 ℚ/ℚ 除法用 → 需改用 `_÷_` (真 ℚ 除法)
- `record CategoryPhaseSync` 内嵌 `where` 语法错 (需提顶层)
- `AlphaElectricApprox` 用 `_<_`/`_<ᵇ_` 混用 Rational 序
- 从 v5.20 起从未独立编译, 公式正确性本身待验

### A2. Resonance.agda (已修绿, 5 处建模未定型转注释)
- nanluIso: JianXiaShui 落在 Nayin 默认分支 (freq=144) 但声称 = 432 → 需核对
  JianXiaShui 是否应在 Nayin.nayinPreferredHarmonic 表映射到 3 次谐波
- widthProportionalToBase: resonanceWidth 定义与 alpha×(base/5) 公式矛盾 (仅 Earth 真)
- zhonglvCausesDecoherence: 洞 + 未定义 applyZhonglvPhaseSync, 语义需核对
- standardHouQiTube: nayinFingerprint = ? 需 StableRoot 数学
- h2oC60Instance: energySplit 原为 56632/65536 想 ≡ halfGapExact(postulate), 改绑 halfGapExact

### A3. CRTHarmonics.agda (编译 OOM, 需 REWRITE)
- harmonic k = X0 + k·M, M 大系数 (T2=177147) 触发 mod-helper 无界展开 → 6G OOM
- 项目既定解法: REWRITE (XuanwuAbsorption mod46k 先例) 或结构定义
- 尾部 alignment-implies-standing-wave 是 {!!} 洞 (作者自标待 CRTFiberWinding 桥接)
- 但 CRTFiberWinding 已绿; 需补 fiberContains 引理才能闭合

### A4. TopologyLevels.agda (sumGrid 待 Fin 化)
- sumGrid 用 ℕ 遍历 12×12 + `fromℕ x` 冒充 Fin 12 (无界)
- chern2Proof = refl 依赖编译器做 144 格点×4 连接求值 (设计脆弱)
- 需改 Fin 12×Fin 12 结构遍历 + 计算引理

## B. 接口/API 假设失效 (需按新 API 重写)

### B1. Integration.agda (旧 StateMachine API)
- SM.run/SM.block/SM.acc 在 StateMachine 重构 (7 字段 record) 后不存在
- 集成测试需按新 API (evolve + SovereignState.phase 等) 重写
- 已注释保留原文

### B2. TorusClosure.agda (已修绿, 接口占位)
- FrobeniusVisible/GlobalMatrix 原为未定义类型, 补了占位接口定义
- decode 字段补上 (原 closed 引用未定义 decode)
- 语义实现待 jac_4320DClosure 对接

## C. 已裁定假定理 (不可恢复)

### C1. Entanglement classical-bound (已恢复 937bca0 权威裁定)
- classical-bell-sum 用 ⊗ 乘法关联, 81 策略中 36 个和 ≠ T₀ → 假定理
- 权威版: 删 classical-bound/no-violation, 保留 bell-violation-proof (37 真违反)

### C2. HamiltonianDiscrete (已修绿)
- mass-gap-theorem: 方向错 (零集⊆{e} 推不出 H(e)=T₀), 需重述
- energy-conservation: 引未定义 mixedOp^n; 单步演化模型反例 → 需按真实生成元重述

## D. 草稿矛盾块 (已注释保留)

### D1. T6Homotopy.agda (已修绿)
- §2-3 路径块: Vec StepDir 144 固定长却用 []/3步/replicate zero=[] → 自相矛盾
- §6 encodeT6: fromℕ val 冒充 Fin 729 (T6.agda 已有权威 t6ToFin)

### D2. WuXingTransition (已修绿)
- FacePolygon/polygonSides 前移消除前向引用
- SphereA4 (S²/A₄ 商空间) 无正多面体稳定子, 4 函数补占位分支
- SphereA4 的 faceStabilizer/vertexStabilizer 值 (3/3) 是占位, 需核对 S²/A₄ 商空间几何
