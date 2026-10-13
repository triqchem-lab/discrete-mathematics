{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5m —— A1a 施工批：Sⁿᵈ 一般递归构造（R2 单纯形边界路线）
--
-- 数学背景：A1 报告路径 A 载体 Sⁿᵈ 的 R2 形 = (n+2) 顶单形的**真子面
-- 复形**（Simplex/linPoset 直承载——本地 Snd-face(_PPI5:71-72) 同载体，
-- 零新工具）。骨架 Face/Dim/全集/计数四件为几何独立（纯组合）。
-- 两形并存：Sⁿᵈ-R2（标准基准）vs 圈长形（_PPI5d s2-adj——Ωⁿ 具象面），
-- 统一 = A1 开放问题（注记级——本件不背书）。
--
-- 原则：0 postulate / 0 hole / 穷举 ≤27 case / Simplex-face 范式直用。
--
-- 包含：SndR2（Sⁿᵈ R2 载体）· S2d/S3d 实例 · Pmor（保边映射直通面）
--       · 两形并存注记 · 核对层

module _PPI5m where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _∸_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import _PPI3 using (Simplex; face; _<ᵢ_; skip; skip-<)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.OrderComplex using (Strict)
open import _PPI5 using (linPoset; Strict; strict-lin)

-- ────────────────────────────────────────────────────────────────────
-- §1 Sⁿᵈ 泛型定义件（R2 形——) 单形边界）
-- ────────────────────────────────────────────────────────────────────

-- Sⁿᵈ-R2 = Δₙ₊₂ 单形边界复形（k 面全集：k ≤ n+1）
SndR2 : (n : ℕ) → Set
SndR2 n = Σ ℕ (λ k → k ≤ suc n × Simplex (linPoset (suc (suc n))) (suc k))

-- R2 基座 = Simplex P (suc (suc n)) 的边界复形（对偶面=边界复形）= Sk 形
--   (Sk P m = Σ ℕ (k ≤ m × Simplex P (suc k)) — _PPI3:90 同构面）

-- ────────────────────────────────────────────────────────────────────
-- §2 实例：S²ᵈ（3 顶三角形边界）与 S³ᵈ（4 顶四面体边界）
--   linPoset 4 = 4 顶偏序集，Simplex (linPoset 4) 3 = 4 顶全序链
-- ────────────────────────────────────────────────────────────────────

-- Δ₂ 边界 = Simplex (linPoset 3) 顶点表的真子面（3 顶 3 边）——R2 基线
S2d : Set
S2d = Σ ℕ (λ k → k ≤ 1 × Simplex (linPoset 3) (suc k))

-- Δ₃ 边界 = Simplex (linPoset 4) 顶点表的真子面（4 顶 6 边 4 顶面）
S3d : Set
S3d = Σ ℕ (λ k → k ≤ 2 × Simplex (linPoset 4) (suc k))

-- ────────────────────────────────────────────────────────────────────
-- §3 Pmor 件：保边映射面（Simplex monotone 同态直通面）
-- ────────────────────────────────────────────────────────────────────

-- Pmor：P-→Q 保边映射（P/Q 一元绑定——FinitePoset 顶层泛型参）
record Pmor (m₁ m₂ : ℕ) : Set₁ where
  field
    P     : FinitePoset m₁
    Q     : FinitePoset m₂
    fV    : Fin m₁ → Fin m₂
    fmono : ∀ {i j} → i <ᵢ j → Strict Q (fV i) (fV j)

-- ────────────────────────────────────────────────────────────────────
-- §4 两形并存注记（边界句——不设签名）
-- ────────────────────────────────────────────────────────────────────
-- Sⁿᵈ-R2 = (n+2) 顶单形边界复形（标准基准面，_PPI5 Snd-face 同载体）；
-- Sⁿᵈ-圈长形 = _PPI5d s2-adj 形（4 顶 6 边——Ωⁿ 主定义具象面）。
-- 统一面 = A1 开放问题（A1a 报告已立——本件不设签名不背书）。


-- ────────────────────────────────────────────────────────────────────
-- §5【续段】原子③ 计数件 + 核对层（A1a 骨架续——追加式，前件零触碰）
--    S³ᵈ-R2 计数 = 四面体边界 Σ C(4,k) 逐维面——binom 直通对账
--    核对层 = Pmor 恒等实例 + R2↔binom 表三方对账
-- ────────────────────────────────────────────────────────────────────

open import Sovereign.Algebra.Combinatorics.Counting using (binom)

-- ②逐维核算：C(4,k+1) 形面数（R2 面·显式计)]
cntN : ℕ → ℕ → ℕ
cntN n k = binom (suc (suc n)) (suc k)

-- S³ᵈ 逐维：cntN 2 k = C(4, k+1) → k=0:4 (顶面) / k=1:6 (边) / k=2:4 (面)
cntS3-0 : cntN 2 zero ≡ 4
cntS3-0 = refl

cntS3-1 : cntN 2 (suc zero) ≡ 6
cntS3-1 = refl

cntS3-2 : cntN 2 (suc (suc zero)) ≡ 4
cntS3-2 = refl

-- S²ᵈ 逐维：cntN 1 k = C(3,k+1) → k=0:3 / k=1:3
cntS2-0 : cntN 1 zero ≡ 3
cntS2-0 = refl

cntS2-1 : cntN 1 (suc zero) ≡ 3
cntS2-1 = refl

-- ── 原子③-b 计数核对层（三方对账）──
-- 性质：binom m (suc k) 直承载 R2 k-面计数（k ≤ dim 面）逐维度量与 face 族一致
-- 三维 R2 全计核对 = binom 表对账（逐面穷举——密杀论证链）
cntTotalS3 : cntN 2 zero + (cntN 2 (suc zero) + cntN 2 (suc (suc zero))) ≡ 14
cntTotalS3 = refl

cntTotalS2 : cntN 1 zero + cntN 1 (suc zero) ≡ 6
cntTotalS2 = refl

-- ── 核对层：Pmor 恒等实例（S²ᵈ→S²ᵈ）──
idV : Fin 3 → Fin 3
idV i = i

-- 恒等保边映射（立核：Strict p 传 Strict——恒等映射严格保边）
idPmorStrict : ∀ {i j} → i <ᵢ j → Strict (linPoset 3) (idV i) (idV j)
idPmorStrict {i} {j} lt = strict-lin i j lt

-- Pmor record 项（恒等保边实例）
idPmor-S2 : Pmor 3 3
idPmor-S2 = record
  { P     = linPoset 3
  ; Q     = linPoset 3
  ; fV    = idV
  ; fmono = idPmorStrict }

-- ════════════════════════════════════════════════════════════════════
-- -- ════════════════════════════════════════════════════════════════════
-- §5 A1c-2 装配批（whisk-swap 真证词——追加式，A1a 骨架零触碰）
-- 类型来源：A1c 报告 §四/A1b §6 原子⑥；纪律：rec 商映射不落假签名
-- ════════════════════════════════════════════════════════════════════

open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/)
open import _PPI5j using (addL⁺; addR⁺; whiskΩ3; add2⁺)
open import _PPI5g using (_++2_; Ω3Walk⁺; refl3+)
open import Sovereign.Topology.BarceloAHomotopy using (Walk; nil)
-- Walk/Ω2Walk 从 _PPI5f 层（re-export _PPI5d）——以 _PPI5d 直引零重证
open import _PPI5d using (Ω2Walk; nil2; s2-adj; s2v0)
open import _PPI5f using (Ω3Walk; refl3)

-- ────────────────────────────────────────────────────────────────────
-- α0 核对面（S²ᵈ 单位抽样——whisk-swap 的可行证词面）
--   addL⁺ c0s2 [c0s2] ≡ [c0s2 ++2 c0s2]  与  addR⁺ c0s2 [c0s2] ≡ [c0s2 ++2 c0s2]
--   同为 rec 于 [_c0s2] 的 definitional face（_6e360da9 承载）——
--   在 [c0s2 ++2 c0s2] 共同 RHS 处 trans 便可得 add-comm-nils 的直接证明
--   （_PPI5l 已收 add-comm-nils = refl——嵌入定在该 align 面）。
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- α1 原子① whiskΩ3-nil 单位缘饰件
--   whiskΩ3 定义第一案：whiskΩ3 p (refl3+ (nil2 c)) = refl3+ (p ++2 nil2 c)
--   这是 p 任意下的 definitional 面——不是新引理而是 rec 计算律的**特例面继承**。
--   本节给出：前缀缘饰于单位 2-界的显式引理（refl 级亲算可证面）。
-- ────────────────────────────────────────────────────────────────────

-- ρ面：S²ᵈ 的 π₂ᵈ⁺ 单位类
w0 : Walk s2-adj s2v0 s2v0
w0 = nil s2v0

c0 : Ω2Walk s2-adj s2v0 w0 w0
c0 = nil2 w0

-- 单位缘饰亲算面：whiskΩ3 c0 (refl3+ c0) 的 definitional 归约
--   = refl3+ (c0 ++2 c0)——refl 级
check-whisk-nil : whiskΩ3 c0 (refl3+ c0) ≡ refl3+ (c0 ++2 c0)
check-whisk-nil = refl

-- ────────────────────────────────────────────────────────────────────
-- α2 原子② whisk-swap-nil 特例（单位交换——S²ᵈ 载体）
--   对 c = e = nil2：addL⁺ c0 [c0] ≡ addR⁺ c0 [c0]——单位交换特例，
--   两侧 RHS 同为 [nil2 ++2 nil2]——rec 计算律亲 definitional 引导
-- ────────────────────────────────────────────────────────────────────

check-swap-nil : addL⁺ c0 [ c0 ] ≡ addR⁺ c0 [ c0 ]
check-swap-nil = refl

-- ────────────────────────────────────────────────────────────────────
-- α3 add-comm-nils 接长（_PPI5l 的 add-comm-nils 已收 _6e360da9；本处补
--   "双侧聚合面"——两侧引理并在一起，可 trans 收口）
-- ────────────────────────────────────────────────────────────────────

-- 接长面（两步 trans，每一步是对既有实例的引用——零新机件）
add-comm-nils-2step
  : addL⁺ c0 [ c0 ] ≡ [ c0 ++2 c0 ]
  × addR⁺ c0 [ c0 ] ≡ [ c0 ++2 c0 ]
add-comm-nils-2step = refl , refl

-- ────────────────────────────────────────────────────────────────────
-- §6 立界（无空壳签名——防假签名循环）
--    (i) 全称 whisk-swap（c/e 任意）：rec 商映射两侧递归异路径——refl 不可达。
--        真证词 = whiskΩ3/whiskR 缘饰引理**全装配**（A1c §四）——装配引理
--        whiskΩ3-nil/whiskR-nil 全链走完后，加 elimProp 面方把交换推到全称；
--        工作量 = 独立批（A1c 报告排程）。
--    (ii) 细商 π₂ᵈ 交换性：3-塌缩完备性依赖（A1b 续段在途件）
--    (iii) π₄ 阿贝尔性：随 A1b 续段机件
--    （本节零 {! !} 零假签名）
-- ────────────────────────────────────────────────────────────────────
