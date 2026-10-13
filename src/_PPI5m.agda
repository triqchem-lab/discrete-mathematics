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
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import _PPI3 using (Simplex; face; _<ᵢ_; skip; skip-<)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.OrderComplex using (Strict)
open import _PPI5 using (linPoset; strict-lin; vchain-1case)

-- ────────────────────────────────────────────────────────────────────
-- §1 Sⁿᵈ 泛型定义件（R2 形——) 单形边界）
-- ────────────────────────────────────────────────────────────────────

-- SndR2 = Δₙ₊₁ 全体面复形（**闭形**——k ≤ suc n 含 (n+2) 顶全链层；
--   = Sk (linPoset (suc (suc n))) (suc n) 同构面——_PPI3:90）
-- v2 语义对齐（设计稿 proper 语义）：真边界复形 = k ≤ n（排除全链）
--   ——新名 SndBd（骨架版 SndR2 界宽一档，保留作闭形对照件；
--   下游 _PPI5n 仅注释引用，签名零触碰）
SndR2 : (n : ℕ) → Set
SndR2 n = Σ ℕ (λ k → k ≤ suc n × Simplex (linPoset (suc (suc n))) (suc k))

-- 真边界复形泛型（R2 载体——k 维面 = (k+1) 顶链，k ≤ n 排除全链）
SndBd : (n : ℕ) → Set
SndBd n = Σ ℕ (λ k → k ≤ n × Simplex (linPoset (suc (suc n))) (suc k))

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

-- Pmor：P-→Q 保边映射（v2 签名修正：fmono 带 Strict P 前提——
--   保边 = 边映到边；骨架版丢前提 = 单调映射形态混入——对 linPoset 载体
--   两形等价（strict-lin 桥），对泛型 FinitePoset 前提必要）
record Pmor (m₁ m₂ : ℕ) : Set₁ where
  field
    P     : FinitePoset m₁
    Q     : FinitePoset m₂
    fV    : Fin m₁ → Fin m₂
    fmono : ∀ {i j} → i <ᵢ j → Strict P i j → Strict Q (fV i) (fV j)

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

-- 恒等保边映射（v2 签名同步：Strict P 前提直传——idV 应用 β 后同项）
idPmorStrict : ∀ {i j} → i <ᵢ j → Strict (linPoset 3) i j →
               Strict (linPoset 3) (idV i) (idV j)
idPmorStrict lt st = st

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

-- ════════════════════════════════════════════════════════════════════
-- §A【v2 增量段】A1a 批施工（R2 真边界 + Δ₄ 分层核对 + 对接弯——追加式，
--    既有段零触碰）。原子①补真边界泛型件/全链件；原子②Δ₄ 分层 witness；
--    原子③smor 直通面；原子④圈长形↔R2 对接弯件。
-- ════════════════════════════════════════════════════════════════════

open import Data.Nat.Properties
  using (n≤1+n; 1+n≢n; 1+n≰n; ≤-antisym; ≤-trans)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; cong; subst; _≢_)
open import _PPI5d using (S2edge; s2v0; s2v1; s2v2; s2v3;
                          s01; s10; s02; s20; s03; s30; s12; s21; s13; s31; s23; s32)

-- ── A§1 闭形对照 + 真边界分离件（原子①）──────────────────────────

-- 全链 witness（顶点表 = identity——linPoset m 的 m 顶升链恰一条，闭形顶层）
linChain : (m : ℕ) → Simplex (linPoset m) m
linChain m = record { vert = λ i → i ; vchain = λ i j p → strict-lin i j p }

-- 边界排外核（真子面过滤的定义性分离——k ≡ suc n 层的 k ≤ n 反证）
topExcl : ∀ n → ¬ Σ ℕ (λ k → k ≡ suc n × k ≤ n)
topExcl n (k , ek , le) = 1+n≰n (subst (λ z → Data.Nat._≤_ z n) ek le)

-- Δ₄ 闭形顶层 witness（FullSnd/SndR2 3 的 4-单形层——「四面体=1」闭形口径）
full-top4 : SndR2 3
full-top4 = 4 , ≤4refl , linChain 5
  where
    ≤4refl : 4 ≤ 4
    ≤4refl = s≤s (s≤s (s≤s (s≤s z≤n)))

-- Δ₄ 边界排外核对：5 顶全链层 ∉ S3dR2（k ≡ 4 层的 k ≤ 3 反证）
s3-no-top : ¬ Σ ℕ (λ k → k ≡ 4 × k ≤ 3)
s3-no-top (k , ek , le) = topExcl 3 (k , ek , le)

-- ── A§2 分层构造子（顶/边/三角/四面体统一件——泛型 m）────────────

-- linPoset 上 Strict 的传递桥（≤-trans + antisym 非退化）
strict-trans : ∀ {m} (a b c : Fin m) → Strict (linPoset m) a b →
               Strict (linPoset m) b c → Strict (linPoset m) a c
strict-trans a b c (le₁ , ne₁) (le₂ , ne₂) = ≤-trans le₁ le₂ , ne
  where
    ne : a ≢ c
    ne eq = ne₁ (toℕ-injective (≤-antisym le₁ le''))
      where
        le'' : toℕ b ≤ toℕ a
        le'' = subst (λ z → toℕ b ≤ z) (cong toℕ (sym eq)) le₂

-- 3 顶链分派器：3 真实案（01/02/12）+ 6 空案——穷举 9 ≤ 27
r2vc3 : ∀ {m} (f : Fin 3 → Fin m)
         (s₁₂ : Strict (linPoset m) (f fzero) (f (fsuc fzero)))
         (s₂₃ : Strict (linPoset m) (f (fsuc fzero)) (f (fsuc (fsuc fzero))))
         (i j : Fin 3) → i <ᵢ j → Strict (linPoset m) (f i) (f j)
r2vc3 f s₁₂ s₂₃ fzero (fsuc fzero) p = s₁₂
r2vc3 f s₁₂ s₂₃ fzero (fsuc (fsuc fzero)) p =
  strict-trans (f fzero) (f (fsuc fzero)) (f (fsuc (fsuc fzero))) s₁₂ s₂₃
r2vc3 f s₁₂ s₂₃ (fsuc fzero) (fsuc (fsuc fzero)) p = s₂₃
r2vc3 f s₁₂ s₂₃ fzero fzero ()
r2vc3 f s₁₂ s₂₃ (fsuc fzero) fzero ()
r2vc3 f s₁₂ s₂₃ (fsuc fzero) (fsuc fzero) (s≤s ())
r2vc3 f s₁₂ s₂₃ (fsuc (fsuc fzero)) fzero ()
r2vc3 f s₁₂ s₂₃ (fsuc (fsuc fzero)) (fsuc fzero) ()
r2vc3 f s₁₂ s₂₃ (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) (s≤s ())

-- 4 顶链分派器：6 真实案 + 10 空案——穷举 16 ≤ 27
r2vc4 : ∀ {m} (f : Fin 4 → Fin m)
         (s₁₂ : Strict (linPoset m) (f fzero) (f (fsuc fzero)))
         (s₂₃ : Strict (linPoset m) (f (fsuc fzero)) (f (fsuc (fsuc fzero))))
         (s₃₄ : Strict (linPoset m) (f (fsuc (fsuc fzero))) (f (fsuc (fsuc (fsuc fzero)))))
         (i j : Fin 4) → i <ᵢ j → Strict (linPoset m) (f i) (f j)
r2vc4 f s₁₂ s₂₃ s₃₄ fzero (fsuc fzero) p = s₁₂
r2vc4 f s₁₂ s₂₃ s₃₄ fzero (fsuc (fsuc fzero)) p =
  strict-trans (f fzero) (f (fsuc fzero)) (f (fsuc (fsuc fzero))) s₁₂ s₂₃
r2vc4 f s₁₂ s₂₃ s₃₄ fzero (fsuc (fsuc (fsuc fzero))) p =
  strict-trans (f fzero) (f (fsuc (fsuc fzero))) (f (fsuc (fsuc (fsuc fzero))))
    (strict-trans (f fzero) (f (fsuc fzero)) (f (fsuc (fsuc fzero))) s₁₂ s₂₃) s₃₄
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc fzero) (fsuc (fsuc fzero)) p = s₂₃
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc fzero) (fsuc (fsuc (fsuc fzero))) p =
  strict-trans (f (fsuc fzero)) (f (fsuc (fsuc fzero))) (f (fsuc (fsuc (fsuc fzero)))) s₂₃ s₃₄
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) p = s₃₄
r2vc4 f s₁₂ s₂₃ s₃₄ fzero fzero ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc fzero) fzero ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc fzero) (fsuc fzero) (s≤s ())
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc fzero)) fzero ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc fzero)) (fsuc fzero) ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) (s≤s ())
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc (fsuc fzero))) fzero ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc (fsuc fzero))) (fsuc fzero) ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) ()
r2vc4 f s₁₂ s₂₃ s₃₄ (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) (s≤s ())

-- 顶点表命名件（升链表——泛型 m）
r2vert2 : ∀ {m} → Fin m → Fin m → Fin 2 → Fin m
r2vert2 a b fzero = a
r2vert2 a b (fsuc fzero) = b

r2vert3 : ∀ {m} → Fin m → Fin m → Fin m → Fin 3 → Fin m
r2vert3 a b c fzero = a
r2vert3 a b c (fsuc fzero) = b
r2vert3 a b c (fsuc (fsuc fzero)) = c

r2vert4 : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin 4 → Fin m
r2vert4 a b c d fzero = a
r2vert4 a b c d (fsuc fzero) = b
r2vert4 a b c d (fsuc (fsuc fzero)) = c
r2vert4 a b c d (fsuc (fsuc (fsuc fzero))) = d

-- 2 顶链分派器（顶层化——where 块对外层隐式变元不可见，_PPI3 face-Sk 范式）
r2vc2 : ∀ {m} (g : Fin 2 → Fin m) → toℕ (g fzero) ≤ toℕ (g (fsuc fzero)) →
        g fzero ≢ g (fsuc fzero) →
        (i j : Fin 2) → i <ᵢ j → Strict (linPoset m) (g i) (g j)
r2vc2 g le ne fzero (fsuc fzero) p = le , ne
r2vc2 g le ne fzero fzero ()
r2vc2 g le ne (fsuc fzero) fzero ()
r2vc2 g le ne (fsuc fzero) (fsuc fzero) (s≤s ())

-- 分层构造子：边（2 顶）/ 三角（3 顶）/ 四面体（4 顶）——相邻序证入参
r2edge : ∀ {m} (a b : Fin m) → Strict (linPoset m) a b → Simplex (linPoset m) 2
r2edge a b sab = record
  { vert   = r2vert2 a b
  ; vchain = r2vc2 (r2vert2 a b) (proj₁ sab) (proj₂ sab) }

r2tri : ∀ {m} (a b c : Fin m) → Strict (linPoset m) a b → Strict (linPoset m) b c →
        Simplex (linPoset m) 3
r2tri a b c sab sbc = record { vert = r2vert3 a b c ; vchain = r2vc3 (r2vert3 a b c) sab sbc }

r2tet : ∀ {m} (a b c d : Fin m) → Strict (linPoset m) a b → Strict (linPoset m) b c →
        Strict (linPoset m) c d → Simplex (linPoset m) 4
r2tet a b c d sab sbc scd =
  record { vert = r2vert4 a b c d ; vchain = r2vc4 (r2vert4 a b c d) sab sbc scd }

-- ── A§3 泛化 o-面件（A1b/A1c 载体预置：维数分层 + ∂ 封闭）────────

-- oFace n k = k 维面的过滤层（维数界 + 单形——SndBd 的分维度取出）
oFace : (n k : ℕ) → Set
oFace n k = Σ (Simplex (linPoset (suc (suc n))) (suc k)) (λ _ → k ≤ n)

-- o-面 → 真边界复形（维数显式注入）
oFace→Bd : ∀ {n k} → oFace n k → SndBd n
oFace→Bd {n} {k} (s , le) = k , le , s

-- ∂ 封闭机件（suc d ≤ n → d ≤ n）
pred-le : ∀ {d n} → suc d ≤ n → d ≤ n
pred-le {d} {suc n'} (s≤s p) = n≤1+n p
pred-le {d} {zero} ()

-- R2-∂：边界复形 ∂ 封闭（d 维面的 ∂ᵢ = (d-1) 维面，仍在边界——复用
--   _PPI3 face 零重证；d ≥ 1 时顶点的 ∂ = 空单形不入面族）
R2-∂ : ∀ {n d} → suc d ≤ n → (s : Simplex (linPoset (suc (suc n))) (suc (suc d))) →
       (i : Fin (suc (suc d))) → SndBd n
R2-∂ {n} {d} le s i = d , pred-le le , face (linPoset (suc (suc n))) s i

-- ── A§4 smor 直通面（原子③——P-¹ morph；Pmor 已 v2 修正签名）────

-- smor：保边映射在单形上的直通提升（链保形——泛型 FinitePoset）
smor : ∀ {m₁ m₂} (P : FinitePoset m₁) (Q : FinitePoset m₂)
       (fV : Fin m₁ → Fin m₂)
       (fm : ∀ {i j} → i <ᵢ j → Strict P i j → Strict Q (fV i) (fV j))
       {k} (s : Simplex P k) → Simplex Q k
smor P Q fV fm s = record
  { vert   = λ i → fV (Simplex.vert s i)
  ; vchain = λ i j lt → fm lt (Simplex.vchain s i j lt) }

-- 直通核对：identity 保边映射提升 = 自身（record η + β——refl 级）
smor-id : ∀ {m k} (s : Simplex (linPoset m) k) →
          smor (linPoset m) (linPoset m) (λ i → i) (λ lt st → st) s ≡ s
smor-id s = refl

-- 函子性核对：smor 与 ∂ 交换（P-¹ morph 的 ∂ 迹保持——refl 级）
smor-face : ∀ {m₁ m₂} (P : FinitePoset m₁) (Q : FinitePoset m₂)
            (fV : Fin m₁ → Fin m₂)
            (fm : ∀ {i j} → i <ᵢ j → Strict P i j → Strict Q (fV i) (fV j))
            {k} (s : Simplex P (suc k)) (i : Fin (suc k)) →
            smor P Q fV fm (face P s i) ≡ face Q (smor P Q fV fm s) i
smor-face P Q fV fm s i = refl

-- ── A§5 三例对齐名（Snd-face n 载体 = linPoset (n+2) 的维度语义）──

S1dR2 S2dR2 S3dR2 : Set
S1dR2 = SndBd 1    -- ∂Δ₂ = 3 顶 3 边（= S2d 同型——命名对齐层）
S2dR2 = SndBd 2    -- ∂Δ₃ = 4 顶 6 边 4 三角（= S3d 同型）
S3dR2 = SndBd 3    -- ∂Δ₄ = 5 顶 10 边 10 三角 5 四面体（原子②最小实例）

-- ── A§6 Δ₃ 边界数据件（S²ᵈ-R2——圈长形同载体 Fin 4）─────────────

-- 1-面层 6 边（C(4,2)=6——升链 witness 全枚举）
s2e01 : Simplex (linPoset 4) 2
s2e01 = r2edge s2v0 s2v1 (strict-lin s2v0 s2v1 (s≤s z≤n))
s2e02 : Simplex (linPoset 4) 2
s2e02 = r2edge s2v0 s2v2 (strict-lin s2v0 s2v2 (s≤s z≤n))
s2e03 : Simplex (linPoset 4) 2
s2e03 = r2edge s2v0 s2v3 (strict-lin s2v0 s2v3 (s≤s z≤n))
s2e12 : Simplex (linPoset 4) 2
s2e12 = r2edge s2v1 s2v2 (strict-lin s2v1 s2v2 (s≤s (s≤s z≤n)))
s2e13 : Simplex (linPoset 4) 2
s2e13 = r2edge s2v1 s2v3 (strict-lin s2v1 s2v3 (s≤s (s≤s z≤n)))
s2e23 : Simplex (linPoset 4) 2
s2e23 = r2edge s2v2 s2v3 (strict-lin s2v2 s2v3 (s≤s (s≤s z≤n)))

-- 2-面层 4 三角（C(4,3)=4）
s2t012 : Simplex (linPoset 4) 3
s2t012 = r2tri s2v0 s2v1 s2v2 (strict-lin s2v0 s2v1 (s≤s z≤n)) (strict-lin s2v1 s2v2 (s≤s (s≤s z≤n)))
s2t013 : Simplex (linPoset 4) 3
s2t013 = r2tri s2v0 s2v1 s2v3 (strict-lin s2v0 s2v1 (s≤s z≤n)) (strict-lin s2v1 s2v3 (s≤s (s≤s z≤n)))
s2t023 : Simplex (linPoset 4) 3
s2t023 = r2tri s2v0 s2v2 s2v3 (strict-lin s2v0 s2v2 (s≤s z≤n)) (strict-lin s2v2 s2v3 (s≤s (s≤s z≤n)))
s2t123 : Simplex (linPoset 4) 3
s2t123 = r2tri s2v1 s2v2 s2v3 (strict-lin s2v1 s2v2 (s≤s (s≤s z≤n))) (strict-lin s2v2 s2v3 (s≤s (s≤s z≤n)))

-- ── A§7 Δ₄ 边界数据件（S³ᵈ-R2——原子②分层核对）─────────────────

-- Δ₄ 顶点（Fin 5——5 顶 4-单形边界载体的节点）
s3v0 s3v1 s3v2 s3v3 s3v4 : Fin 5
s3v0 = fzero
s3v1 = fsuc fzero
s3v2 = fsuc (fsuc fzero)
s3v3 = fsuc (fsuc (fsuc fzero))
s3v4 = fsuc (fsuc (fsuc (fsuc fzero)))

-- 0-面层 5 顶（1 顶链 witness——顶点数核对 = Fin 5 参数化恰 5 件）
s3vv0 : Simplex (linPoset 5) 1
s3vv0 = record { vert = λ _ → s3v0 ; vchain = vchain-1case (λ _ → s3v0) }
s3vv1 : Simplex (linPoset 5) 1
s3vv1 = record { vert = λ _ → s3v1 ; vchain = vchain-1case (λ _ → s3v1) }
s3vv2 : Simplex (linPoset 5) 1
s3vv2 = record { vert = λ _ → s3v2 ; vchain = vchain-1case (λ _ → s3v2) }
s3vv3 : Simplex (linPoset 5) 1
s3vv3 = record { vert = λ _ → s3v3 ; vchain = vchain-1case (λ _ → s3v3) }
s3vv4 : Simplex (linPoset 5) 1
s3vv4 = record { vert = λ _ → s3v4 ; vchain = vchain-1case (λ _ → s3v4) }

-- 1-面层 10 边（C(5,2)=10——升对 witness 全枚举）
s3e01 : Simplex (linPoset 5) 2
s3e01 = r2edge s3v0 s3v1 (strict-lin s3v0 s3v1 (s≤s z≤n))
s3e02 : Simplex (linPoset 5) 2
s3e02 = r2edge s3v0 s3v2 (strict-lin s3v0 s3v2 (s≤s z≤n))
s3e03 : Simplex (linPoset 5) 2
s3e03 = r2edge s3v0 s3v3 (strict-lin s3v0 s3v3 (s≤s z≤n))
s3e04 : Simplex (linPoset 5) 2
s3e04 = r2edge s3v0 s3v4 (strict-lin s3v0 s3v4 (s≤s z≤n))
s3e12 : Simplex (linPoset 5) 2
s3e12 = r2edge s3v1 s3v2 (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n)))
s3e13 : Simplex (linPoset 5) 2
s3e13 = r2edge s3v1 s3v3 (strict-lin s3v1 s3v3 (s≤s (s≤s z≤n)))
s3e14 : Simplex (linPoset 5) 2
s3e14 = r2edge s3v1 s3v4 (strict-lin s3v1 s3v4 (s≤s (s≤s z≤n)))
s3e23 : Simplex (linPoset 5) 2
s3e23 = r2edge s3v2 s3v3 (strict-lin s3v2 s3v3 (s≤s (s≤s (s≤s z≤n))))
s3e24 : Simplex (linPoset 5) 2
s3e24 = r2edge s3v2 s3v4 (strict-lin s3v2 s3v4 (s≤s (s≤s (s≤s z≤n))))
s3e34 : Simplex (linPoset 5) 2
s3e34 = r2edge s3v3 s3v4 (strict-lin s3v3 s3v4 (s≤s (s≤s (s≤s (s≤s z≤n)))))

-- 2-面层 10 三角（C(5,3)=10——3 顶升链 witness 全枚举）
s3t012 : Simplex (linPoset 5) 3
s3t012 = r2tri s3v0 s3v1 s3v2 (strict-lin s3v0 s3v1 (s≤s z≤n)) (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n)))
s3t013 : Simplex (linPoset 5) 3
s3t013 = r2tri s3v0 s3v1 s3v3 (strict-lin s3v0 s3v1 (s≤s z≤n)) (strict-lin s3v1 s3v3 (s≤s (s≤s z≤n)))
s3t014 : Simplex (linPoset 5) 3
s3t014 = r2tri s3v0 s3v1 s3v4 (strict-lin s3v0 s3v1 (s≤s z≤n)) (strict-lin s3v1 s3v4 (s≤s (s≤s z≤n)))
s3t023 : Simplex (linPoset 5) 3
s3t023 = r2tri s3v0 s3v2 s3v3 (strict-lin s3v0 s3v2 (s≤s z≤n)) (strict-lin s3v2 s3v3 (s≤s (s≤s z≤n)))
s3t024 : Simplex (linPoset 5) 3
s3t024 = r2tri s3v0 s3v2 s3v4 (strict-lin s3v0 s3v2 (s≤s z≤n)) (strict-lin s3v2 s3v4 (s≤s (s≤s z≤n)))
s3t034 : Simplex (linPoset 5) 3
s3t034 = r2tri s3v0 s3v3 s3v4 (strict-lin s3v0 s3v3 (s≤s z≤n)) (strict-lin s3v3 s3v4 (s≤s (s≤s (s≤s z≤n))))
s3t123 : Simplex (linPoset 5) 3
s3t123 = r2tri s3v1 s3v2 s3v3 (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n))) (strict-lin s3v2 s3v3 (s≤s (s≤s z≤n)))
s3t124 : Simplex (linPoset 5) 3
s3t124 = r2tri s3v1 s3v2 s3v4 (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n))) (strict-lin s3v2 s3v4 (s≤s (s≤s z≤n)))
s3t134 : Simplex (linPoset 5) 3
s3t134 = r2tri s3v1 s3v3 s3v4 (strict-lin s3v1 s3v3 (s≤s (s≤s z≤n))) (strict-lin s3v3 s3v4 (s≤s (s≤s (s≤s z≤n))))
s3t234 : Simplex (linPoset 5) 3
s3t234 = r2tri s3v2 s3v3 s3v4 (strict-lin s3v2 s3v3 (s≤s (s≤s z≤n))) (strict-lin s3v3 s3v4 (s≤s (s≤s z≤n)))

-- 3-面层 5 四面体（C(5,4)=5——4 顶升链 witness 全枚举：边界复形顶层）
s3w0123 : Simplex (linPoset 5) 4
s3w0123 = r2tet s3v0 s3v1 s3v2 s3v3 (strict-lin s3v0 s3v1 (s≤s z≤n))
  (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n))) (strict-lin s3v2 s3v3 (s≤s (s≤s z≤n)))
s3w0124 : Simplex (linPoset 5) 4
s3w0124 = r2tet s3v0 s3v1 s3v2 s3v4 (strict-lin s3v0 s3v1 (s≤s z≤n))
  (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n))) (strict-lin s3v2 s3v4 (s≤s (s≤s z≤n)))
s3w0134 : Simplex (linPoset 5) 4
s3w0134 = r2tet s3v0 s3v1 s3v3 s3v4 (strict-lin s3v0 s3v1 (s≤s z≤n))
  (strict-lin s3v1 s3v3 (s≤s (s≤s z≤n))) (strict-lin s3v3 s3v4 (s≤s (s≤s z≤n)))
s3w0234 : Simplex (linPoset 5) 4
s3w0234 = r2tet s3v0 s3v2 s3v3 s3v4 (strict-lin s3v0 s3v2 (s≤s z≤n))
  (strict-lin s3v2 s3v3 (s≤s (s≤s z≤n))) (strict-lin s3v3 s3v4 (s≤s (s≤s z≤n)))
s3w1234 : Simplex (linPoset 5) 4
s3w1234 = r2tet s3v1 s3v2 s3v3 s3v4 (strict-lin s3v1 s3v2 (s≤s (s≤s z≤n)))
  (strict-lin s3v2 s3v3 (s≤s (s≤s z≤n))) (strict-lin s3v3 s3v4 (s≤s (s≤s z≤n)))

-- ── A§8 对接弯件：圈长形 ↔ R2 标准形（原子④）────────────────────

-- 圈长形 s2-adj = 12 有向边（Fin 4 双向 K4——_PPI5d）；R2 形 = 6 升链。
-- 弯件 = 有向边 → 升链边（方向裂分：sXY/sYX 同映升对——R2 形顶点表必升，
-- 降对不入——见 r2edge-ord）
s2e→R2 : ∀ {a b : Fin 4} → S2edge a b → Simplex (linPoset 4) 2
s2e→R2 s01 = s2e01
s2e→R2 s10 = s2e01
s2e→R2 s02 = s2e02
s2e→R2 s20 = s2e02
s2e→R2 s03 = s2e03
s2e→R2 s30 = s2e03
s2e→R2 s12 = s2e12
s2e→R2 s21 = s2e12
s2e→R2 s13 = s2e13
s2e→R2 s31 = s2e13
s2e→R2 s23 = s2e23
s2e→R2 s32 = s2e23

-- 方向分裂核对（2 有向边 ↦ 同一升链——「12 有向 = 2×6 无向」的证物）
check-split01 : s2e→R2 s01 ≡ s2e→R2 s10
check-split01 = refl

-- 方向敏感核：R2 升链单向性（圈长形双向 vs R2 单向的结构差——两形
-- 不合一的具体面；统一需边方向商，= A1 开放问题）
r2edge-ord : ∀ {m} (s : Simplex (linPoset m) 2) →
  Strict (linPoset m) (Simplex.vert s fzero) (Simplex.vert s (fsuc fzero))
r2edge-ord s = Simplex.vchain s fzero (fsuc fzero) (s≤s z≤n)

-- ── A§9 核对层（refl 级——对抗验证协议具体点实例比对）───────────

-- Δ₃ 边界核对：∂₀(e01) = 顶点 1（删首点——_PPI5 check-face0-v01 同型）
check-∂-e01 : toℕ (Simplex.vert (face (linPoset 4) s2e01 fzero) fzero) ≡ 1
check-∂-e01 = refl

-- Δ₃ 边界核对：∂₀(t012) = (1,2) 边（三角首边删 0 顶）
check-∂-t012 : toℕ (Simplex.vert (face (linPoset 4) s2t012 fzero) fzero) ≡ 1
check-∂-t012 = refl

-- Δ₄ 顶点核对：s3vv4 的顶 = 4
check-s3vv4 : toℕ (Simplex.vert s3vv4 fzero) ≡ 4
check-s3vv4 = refl

-- Δ₄ 边核对：s3e34 的顶点表 = (3,4)
check-s3e34 : toℕ (Simplex.vert s3e34 (fsuc fzero)) ≡ 4
check-s3e34 = refl

-- Δ₄ 三角核对：s3t234 顶点表 = (2,3,4)
check-s3t234 : toℕ (Simplex.vert s3t234 (fsuc (fsuc fzero))) ≡ 4
check-s3t234 = refl

-- Δ₄ 四面体核对：s3w1234 顶点表 = (1,2,3,4)
check-s3w1234 : toℕ (Simplex.vert s3w1234 (fsuc (fsuc (fsuc fzero)))) ≡ 4
check-s3w1234 = refl

-- 闭形全链核对：linChain 5 的顶点表 = identity（顶 i ↦ i）
check-linChain5 : toℕ (Simplex.vert (linChain 5) s3v4) ≡ 4
check-linChain5 = refl

-- ∂ 封闭核对：∂₀(s3w0123) 是 S3dR2 的 2-面（四面体 → 三角——边界降维）
check-R2-∂ : toℕ (Simplex.vert
  (proj₂ (proj₂ (R2-∂ (s≤s (s≤s (s≤s z≤n))) s3w0123 fzero))) fzero) ≡ 1
check-R2-∂ = refl

-- smor 直通核对（identity 保边——S¹ᵈ 基线顶点单形）
check-smor : toℕ (Simplex.vert (smor (linPoset 3) (linPoset 3) (λ i → i)
  (λ lt st → st) (record { vert = λ _ → fzero
  ; vchain = vchain-1case (λ _ → fzero) }) fzero) fzero) ≡ 0
check-smor = refl

-- ── A§10 v2 注记更新（原子④边界句——不设签名不背书）─────────────
-- Sⁿᵈ-R2 真边界复形 = SndBd（k ≤ n——设计稿 proper 语义）；SndR2 = 闭形对照。
-- 两形在 S²ᵈ 层同载体（Fin 4 顶）但结构分化：圈长形双向边图（s01/s10 独立
-- 构造子）vs R2 单向升链（方向由顶点表序自带——r2edge-ord）。
-- 统一面 = A1 开放问题（A1a 报告已立——本件不设签名不背书）。
