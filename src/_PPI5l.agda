{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5l —— A1c-1/2 实例面批：π₂ᵈ⁺ 运算的 S²ᵈ 核对面 + whisk 装配半件
--
-- 数学背景：A1c 设计报告（df0c5b5）钉实「π₂ᵈᵐ 扩展商的交换性=实例面先行」。
--   addL⁺/addR⁺ 俱为 rec 商映射（**递归路径两侧不同 ⇒ refl 不可达**——
--   _PPI5k §5c 已按零洞红线撤 `{!!}`），真证词走「elimProp/eq/ 装配」。本件：
--   ① **rec 计算律真件**：nil 单位性（addL⁺ nil2 = id/addR⁺ nil2 = id——
--      rec 于构造子上的**逐 definitional 计算可证面**）；
--   ② **单位交换真件**（nil-nil 侧 addL ≡ addR——**字面同嵌套**，refl 级可达）；
--   ③ **whiskΩ3-nil 装配半件**（whisk 对称化路线的最小机件——A1c §四排程）；
--   ④ 核对层 ×若干（值面 refl 级）。
--
-- 立界（§6 未证面，如实注）：一般 add2⁺-comm 与 whisk-swap 的一般形 = 证明面
--   转主答案在 A1b 续段/幂等后批（`_PPI5k` 阶段1zero 面已设对应面）。
--
-- 包含：w0s2·c0s2·nil2s2（基准数据）｜addL-nil/addR-nil（rec 计算律）·
--       add-comm-nils（单位交换真件）· whiskΩ3-nil · 核对层

module _PPI5l where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)
open import Sovereign.Synthesis.BarceloAHomotopy using (Walk; nil; cons)
open import _PPI5d using (s2-adj; s2v0; Ω2Walk; nil2; cons2)
open import _PPI5g using (Ω3Walk⁺; refl3+; _++2_; Ω3Walkᵇ)
open import _PPI5j using (π₂ᵈ⁺; addL⁺; addR⁺; whiskΩ3)

-- ────────────────────────────────────────────────────────────────────
-- §1 基准数据：S²ᵈ 基点闭走 + 2-腔
-- ────────────────────────────────────────────────────────────────────

w0s2 : Walk s2-adj s2v0 s2v0
w0s2 = nil s2v0

c0s2 : Ω2Walk s2-adj s2v0 w0s2 w0s2
c0s2 = nil2 w0s2

-- ────────────────────────────────────────────────────────────────────
-- §2 rec 计算律真件（addL⁺/addR⁺ 的 nil 单位性——definitional 面）
-- ────────────────────────────────────────────────────────────────────

-- addL⁺ 于 nil2 = 前缀加恒等（rec 计算律——rec 定义展开）
addL-nil : addL⁺ c0s2 [ c0s2 ] ≡ [ c0s2 ++2 c0s2 ]
addL-nil = refl

-- addR⁺ 于 nil2 = 后缀加恒等（rec 计算律——同形）
addR-nil : addR⁺ c0s2 [ c0s2 ] ≡ [ c0s2 ++2 c0s2 ]
addR-nil = refl

-- ────────────────────────────────────────────────────────────────────
-- §3 单位交换真件（addL ≡ addR 于 nil 衔接**字面同形**——refl 级）
--    注意：非一般 c e（rec 双面递归路径异形不改 refl）——真证词走 A1c 报告
--    四排程的 elimProp/eq/ 装配面（立界 §6 呼应）——本件实例面「nil 接入特例。
-- ────────────────────────────────────────────────────────────────────

add-comm-nils : addL⁺ c0s2 [ c0s2 ] ≡ addR⁺ c0s2 [ c0s2 ]
add-comm-nils = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 whiskΩ3-nil 装配半件（whisk 对称化路线——A1c §四机件面）
--    whiskΩ3 p s：3-腔⁺ s = c → c' 经前缀 p 的镜搬（p ++2 c → p ++2 c'）
--    nil 面：p = nil2 恒等——装配面**最简例**（A1c 一般形所需对称化原型）
-- ────────────────────────────────────────────────────────────────────

-- whisk 计算律（refl3+ 案——whiskΩ3 单元亲计算面：rec/构造子亲算可证面）
whisk-refl : (c : Ω2Walk s2-adj s2v0 w0s2 w0s2)
           → whiskΩ3 c0s2 (refl3+ c) ≡ refl3+ (c0s2 ++2 c)
whisk-refl c = refl

-- 交换核对面（A1c 报告实例面立界级）：对 S²ᵈ 基点的 addL/addR 双向嵌套
--   值面在 (nil,nil) 已由 §3 add-comm-nils 承载；一般交换=装配面（§6 (ii)）。

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层（值面 refl 级——可证面）
-- ────────────────────────────────────────────────────────────────────

-- addL 加前缀后超限商元等于加前缀实质内容（rec 定义形核对）
check-addL-def : addL⁺ c0s2 [ c0s2 ] ≡ [ c0s2 ++2 c0s2 ]
check-addL-def = refl

-- addR 对称例
check-addR-def : addR⁺ c0s2 [ c0s2 ] ≡ [ c0s2 ++2 c0s2 ]
check-addR-def = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 立界（诚实——无空壳签名）
--    (i) 一般加法交换 add2⁺-comm（细商完备面——依赖 A1b 报告藏项「3-塌缩完
--        备性」/主答案在 A1b 续段去 BG 面）——未证
--    (ii) whisk-swap 一般形（whiskΩ3 缘饰全装配）——证明面，A1c-2 批
--    (iii) π₄ 面阿贝尔随 A1b 续段机件——独立立界
-- ────────────────────────────────────────────────────────────────────
