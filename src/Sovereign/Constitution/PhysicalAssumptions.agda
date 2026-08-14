{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Constitution.PhysicalAssumptions
-- 物理锚定登记处（轨道 B）— 全库 postulate 三分类的集中登记
--
-- 依据: docs/Postulate审计报告.md 三分类 + 2026-08-14 编译器实测
-- 权威层级: Agda 编译器 > 本登记 > 各模块注释
-- 原则: 零宣称必须带范围; 物理输入是合法公理, 但必须显式登记, 不得冒充定理。
--
-- 三分类定义:
--   ① 机械约束: 可证但因 Agda REWRITE/跨模块路径机制无法替换 — 保留
--   ② 物理锚定: 实验常数的离散编码, 不可代数推导 — genuine bridge, 登记
--   ③ 可闭合:   数学上可证, 证明未实现 — 优先歼灭目标
--
-- 本模块不 import 任何物理模块（避免耦合与编译链膨胀）,
-- 仅作 grep-able 的集中登记。每个站点都必须能回答: 属于哪类? 依据是什么?

module Sovereign.Constitution.PhysicalAssumptions where

-- 三分类类型（文档化用, 不参与数学）
data PostulateClass : Set where
  mechanical   : PostulateClass   -- ① 机械约束（保留）
  physical     : PostulateClass   -- ② 物理锚定（genuine bridge）
  closable     : PostulateClass   -- ③ 可闭合（歼灭目标）
  eliminated   : PostulateClass   -- ✅ 已清除（本会话）

------------------------------------------------------------------------------
-- 登记表（2026-08-14 实测）
------------------------------------------------------------------------------

-- ① 机械约束（保留, 非缺陷）:
--   T6.agda: div3k / mod3k / gf3Toℕ-A4-inv（REWRITE 规则, 4320D 归约加速）
--   XuanwuAbsorption.agda: mod46k / div46k / mod-a+598（REWRITE）
--   jac_Pigeonhole.agda: decode9-encode9（REWRITE）
--   Format/CRT.agda: crtSec-restricted / crtRet-restricted（cubical 桥, 2 条）
--     — 2026-08-14 实测尝试构造性版本: ΣPathP+J 桥因 Agda 2.9.0 跨模块
--       路径差异（隐参逃逸）失败, 与原注释警告一致。crtSec 方向的
--       命题层恒等式 crtSec-restricted-prop 已构造性证明 ✅

-- ② 物理锚定（genuine bridge, 合法公理, 需保留边界注释）:
--   Coupling/Zhonglv.agda:153/186/222 — chernInvariant(=+2)、
--     polarClosure(144)/torusClosure(46)、energyGap(=√3)（实验锚定）
--   Structology/Platonics.agda:428/471/479 — 正多面体群阶（几何常数）
--   Structology/Aether.agda:316/340 — 以太常数
--   Structology/XuanwuAbsorption.agda:7/228 — 玄武吸收谱
--   Structology/MagicSquareM4.agda:254 — ±16 本征向量 (CRT 模域锚定, B 登记注释;
--     原 :345 manifold-orth 空洞公理已删、:381 projection-orthogonality 已改字段)
--   Structology/MagicSquare144.agda:114/154/271 — 幻方常数（144/46 原子对已
--     由 HolographicPi 原子类型承担 ✅, 其余为幻方拓扑不变量）
--   Physics/QuartzPhonon.agda:360/398/458 — 石英声子共振常数
--   处置: 保持 postulate; 每处加 "物理锚定·来源注释"（B 轨道登记标记）;
--   禁止在导出文档中把它们计入"0 postulate"宣称（范围纪律）。

-- ③ 可闭合（优先歼灭）— 进展:
--   ✅ Geometry/ProjectiveCore.agda: 群公理 4 条 + 轨道三性质 7 条
--     （2026-08-14 全部构造性证明; g-mul 由直接积修正为真半直积,
--      修复了 ~g-trans 假命题）
--   ✅ Geometry/ProjectiveOrbit.agda: orbit-* 3 条改为重导出; 
--     orbit-count-is-4320 假命题删除
--   ✅ Quantum/Foundation.agda: experimental-anchoring 空洞类型删除
--   ✅ HolographicPi.agda: k>1-contr / electricCannotExpressHoloPi 假命题删除,
--     cannotUpgradePi 改构造性证明
--   ✅ 2026-08 P0 追加: MagicSquareM4.orthogonal-basis-complete 构造性证明
--     (4 个显式整数见证); manifold-orth-replaces-coprime 空洞 Set 公理删除;
--     projection-orthogonality 假公理 (对任意实例 1·1·1·1≠6624) 改为 record 字段
--   ✅ 2026-08 P0 追加: Quantum/Foundation.phonon-* 4 条 → 构造性定义
--     (propagate/interference/standing-wave/collapse, 0 postulate)
--   ✅ 2026-08 P0 追加: TQ10.polarMod144/toroidalMod46 → refl 证明
--   ✅ 2026-08 P0 追加: CartanTorsion 4 处未解 hole 闭合 (Z₃ 群公理 27+3+3 case
--     refl; closeTorsion 挠率矛盾重设计为 ClosedTorsion 记录); cartanLegal
--     hole 升级为显式公理 (B 登记注释)
--   ✅ 2026-08 P0 追加: HolographicSpace.agda 补 --rewriting 头, InfectiveImport
--     消除, theorem-maximality-4320 编译绿

-- ④ 已清除（eliminated, 证据）:
--   toroidalHolonomy（7 月已修）; k>1-contr; electricCannotExpressHoloPi;
--   orbit-count-is-4320 + total-orbits; experimental-anchoring;
--   ProjectiveOrbit 的 3 条重复轨道公理（改重导出）
--   2026-08 P0 轨道 A 假命题（⊥ 可导出, 已删除）:
--   windingNotDecomposed（MagicSquare144: ¬(144≡120+24), refl 反证）;
--   polarIndecomposable（Boundaries: 见证 a=120,b=24）;
--   holoPiIrreducible（Boundaries: 见证 k=2, 144=2·72 ∧ 46=2·23）;
--   Anchor_EnergyGap_H2O（DataAnchors: 断言 867/1000 ≡ 5/10, 数值反驳）
--   —— 教义（不可拆解/禁约分/≈锚定）保留为注释宪法条款, 不以假命题驻留。

-- 计数锚点（2026-08-15 P0 轮实测）: 全库 postulate 块 101 处,
--   其中机械约束 (REWRITE 系列) + 物理锚定 = 主体（合法）,
--   可闭合待办 = holonomyLemma (ZhonglvPhaseSync, 真但未证, 需 LCM 引理),
--   已知假/空 = 0。
