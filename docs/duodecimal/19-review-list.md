# 待核对清单 (2026-09-08 全库修复专项)

> 这些项不是纯编译问题, 需要语义/物理/数学核对后才能修复.
> 均已在源码中标注 `待核对` 或 `[待核对·...]` 注释保留原文.
> 修复原则: 不删改物理定义; 编译通过 ≠ 物理正确; 真命题可证, 假命题裁剪.

## A. 数值/公式建模未定型 (需核对物理/数学公式)

### A1. FineStructureMapping.agda (✅ 已修绿 a8dcc3d, 部分转待核对)
- 假记法 1b1/8b8 等 → 真 ℚ 字面量; `_/_` 修正为 (+ n)/ℚ (QuartzPhonon 惯例 renaming)
- CategoryPhaseSync computable 证明字段移除 (record 字段实例化触发 ℚ 常量链 whnf OOM;
  其 refl 是同义反复) → 纯数据记录
- FineStructureSplitting/AnomalousMagneticMoment 数值草稿: 符号除需 NonZero / ℚ normalize
  OOM / _^_ 无此算子 → 转待核对注释 (公式原文在编译隔离中丢失, 见 git 历史)

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

### A4. TopologyLevels.agda (✅ 已修绿 a03f70c, chern 段转待核对)
- 原 sumGrid 用 ℕ 遍历 + fromℕ 冒充 Fin 12 (类型错) — 移除
- chern2Proof 深层裁定: chern2Connection (起点 (0,0)/(6,6) 边权 +1) 在 plaquette
  曲率和下总涡量 = 0 (几何模拟: 单源点边权被 4 相邻 plaquette +1-1+1-1 相消),
  ≠ 声称的 +2 → refl 不仅暴力且陈述假. "陈数锁定 C=2"需重新设计 Connection
  使 plaquette 涡量局部化为两个 +1 源 (离散环面陈类构造, 物理建模问题)
- NeutralTopology 卷 chern 段转待核对注释; 其余卷 (Magnetic/Holographic) 保留

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

### C1. Entanglement classical-bound (已删, 归因订正为起点层占位)
- 原稿 81 case 逐 refl 失败 → 编译层已删 (恢复 937bca0)
- **归因订正**: 不是"GF(3) 乘法做不到经典界"。乘法结构分层:
  - GF(3) = 损益起点层 (特征3, 模3乘) — 无 90° 相位
  - DC 乘法 = ⟨α⟩ ≅ C₄ = 90° 旋转群 (AlphaPower={1,α,α²=-1,α³=-α},
    mulAlpha=α^{i+j mod 4}, DuodecClock §1) — 相位信息活在此旋转群
  - GF(9)* = C₈ ⊇ C₄ — α 的域锚定 (GF9:25 "α 阶 4, 90° 生光")
- classical-correlation = a⊗b 无 α 相位 = 复现传统模型"压成 ±1 丢 90° 相位"之错,
  故起点层无法构成经典界; 完备表述待带 α 相位的关联 (DC/GF9 层) 承接
- 占位层可见真违反: bell-violation-proof (设置和 ≠ T₀) 保留

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
