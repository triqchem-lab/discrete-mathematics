{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4b —— (d) 骨架实证 v2：附⑤ 反证 + Gskel/Gcmp 分离件 + 无同构路线定基
--
-- 数学背景（v2 修正——v1 的 subsingleton 声称有误已撤回）：
--   _PPI4 骨架列待证四件 + 附⑤（自环收缩）。实证发现**附⑤为假**：
--   单自环 walk `cons loop nil` 与 `nil` 之间无 AStep 步可达（len≥1 不变量，
--   与 _PPI2 ⑥节 inv-law-false 同根：nil 是 AHomotopy 孤立点）⇒ 自环段不能收缩。
--   ⚠ v1 曾声称「Gskel 侧 walk 只有 nil」——**错误**：Gskel two-chain 有 0→1→0 型
--   偶长 walk（对称骨架双向边）⇒ π₁ᵈ(Gskel) 非单点。真分离路线（v2）：
--   Gskel two-chain 上 **AStep 完全为空**（slide/expand 的捷径边必为自环型而 KEdge 无自环）
--   ⇒ AHomotopy = 逐点相等（len 为不变量）⇒ 偶长 walk 两两不同类（≥3 类）；
--   Gcmp 侧 slide 可并类（[e01,e10] ∼ [loop]）且全类幂等（分类引理待证）⇒ 两侧结构不同构。
--
-- 核心原则：
-- 1. 否决型交付优先：反证件替代硬证（红线① statement_wrong 流程）
-- 2. 零洞零 postulate；假声称撤回留档（v1 记录不删——账面诚实）
-- 3. 双 ≡ 世界显式钉（KEdge 的 ≢ 是 Builtin ≡——reflᴱ 区分；CRT 教训同款）
-- 4. K 禁用：消解走字段提取（x≢x reflᴱ）与测度法，无 absurd 模式
--
-- 包含：§1 自环反证件（walk 级 + 商级）；§2 Gskel 两点图 AStep 为空（核心新件）；
--       §3 分离件与并类件（Gskel 偶长两两异类 / Gcmp slide 并类）；§4 无同构路线与剩余
module _PPI4b where

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
-- KEdge/Strict 的 ≢ 是 Builtin ≡ 世界（OrderComplex 线）——与 Cubical _≡_ 双世界并存，
-- 自环消解处显式钉 reflᴱ（双 ≡ 缺桥教训：CRT 双世界同款）
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_; subst)
open import Cubical.HITs.SetQuotients using ([_]; squash/; elimProp; eq/)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.McCordCore using (cmpEdge)
open import Sovereign.Topology._PMc2 using (KEdge)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; AHomotopy; AStep; AH-refl)
open import _PPI2
  using (π₁ᵈ; len; Pos; Q; Q-hom; S̄; true≢false)
open import _PPI4
  using (Gskel; Gcmp)

--------------------------------------------------------------------------------
-- §1 自环反证件（two-chain 的 fzero 自环——cmpEdge 反身自环 vs KEdge x≢y 分离）
--------------------------------------------------------------------------------

-- 自环边：⊑ 反身给 cmpEdge x x（inj₁ 分支——McCordCore 的 cmpEdge = x⊑y ⊎ y⊑x）
loop-e : cmpEdge two-chain fzero fzero
loop-e = inj₁ (FinitePoset.⊑-refl two-chain fzero)

-- 单自环 walk（len = 1）
selfloop-walk : Walk (Gcmp two-chain) fzero fzero
selfloop-walk = cons loop-e (nil fzero)

-- 核对件：len = suc zero（defeq 闭合）
check-len-loop : _≡_ {A = ℕ} (len selfloop-walk) (suc zero)
check-len-loop = refl

-- walk 级反证件：自环单段与 nil 之间无 AHomotopy
--   （Q 分离器直引——Q-hom 四案归纳已证「同零长 ⊕ 同正长」不变；
--    nil 侧零长、自环侧正长 ⇒ inj₁ 用 subst 搬运 Pos 矛盾、inj₂ 直消解）
selfloop-≁nil : AHomotopy (Gcmp two-chain) selfloop-walk (nil fzero) → ⊥
selfloop-≁nil h = go (Q-hom h)
  where
  go : Q selfloop-walk (nil fzero) → ⊥
  go (inj₁ (ez , _)) = ⊥-elim (subst Pos ez tt)
  go (inj₂ (_ , pn)) = ⊥-elim pn

-- 商级反证件：[nil] ≠ [selfloop]（S̄ = isZeroB ∘ len 分离器——_PPI2 ⑥节现成）
selfloop-quot-≠ : _≡_ {A = π₁ᵈ (Gcmp two-chain) fzero} [ nil fzero ] [ selfloop-walk ] → ⊥
selfloop-quot-≠ p = true≢false (cong S̄ p)
--   S̄ [nil] = isZeroB 0 = true；S̄ [selfloop] = isZeroB 1 = false ⇒ cong S̄ p : true ≡ false

--------------------------------------------------------------------------------
-- §2 无同构路线（v2 立界——半成品不入编译面，防半成品冒充交付）
--------------------------------------------------------------------------------

-- 核心新件（路线基石，待实证）：Gskel two-chain 上 AStep **完全为空**
--   slide/expand 的捷径边 e3 : edge x z 中，x→y→z 三点两两相异（Gskel 边严格）
--   ——两点集上必有 z ≡ x ⇒ e3 : edge x x（KEdge 自环型为空）⇒ 矛盾。
--   实证形：edgeGskel-strict（两端相异，双 ≡ 世界 Builtin 形）+ Fin 2 三点 8 组合消解
--   ⇒ AStep-sk-empty（~40-60 行——附录 17 双世界钉参 + 测度法）。
--
-- 分离件（Gskel ≥3 类）：AStep 空 ⇒ len 不变量（gen 案消解即得）⇒
--   [e01∷e10∷nil]（len 2）与 [4 边]（len 4）不同类（twoB = isZeroB ∘ (_∸ 2) 分离器），
--   与 [nil] 亦不同（S̄ 分离器）——两两可分（~20-30 行）。
--
-- 并类件（Gcmp 侧）：gen (slide nil nil e01 e10 loop-e) : [e01∷e10∷nil] ≡ [selfloop]
--   （slide 经自环捷径并类，~10 行）+ **分类引理**（Gcmp fzero-walk 全部 ∼ nil 或 ∼ loop，
--   walk 归纳 + slide 情形——~60-80 行，无同构证明的唯一重件）。
--
-- 无同构汇合（分类引理就绪后 ~30 行）：MonoidIso 全类幂等传递（B 侧幂等 ⇒ A 侧幂等）
--   而 [e01∷e10∷nil] ⊞ [e01∷e10∷nil] = [4 边] ≠ [2 边]（Gskel 非幂等）⇒ 矛盾。
--
-- 工时汇总：AStep-sk-empty 40-60 + 分离件 20-30 + 分类引理 60-80 + 汇合 30 ≈ **150-250 行**
--   ——比骨架原估（100-160）多出的量恰是「附⑤为假」逼出的替代路线成本（修正依赖：无
--   backtrack 时 iso 原路不可走，此为现行 AStep 下的真分离路线；backtrack（修正案 A）
--   路线下附⑤复活、原 iso 路线成本回落 ~100-160 行）。
--
-- v1 假声称撤回记录（不删史）：「π₁ᵈ(Gskel two-chain) fzero 单点」错误——Gskel 有
--   0→1→0 型偶长 walk；v1 的 subsingleton/不可居留主件随撤回（其依赖链断裂）。
--------------------------------------------------------------------------------
