{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra.PresentationV2
--
-- **展示群定义 v2**：把 `docs/duodecimal/42-presentation-group-definition.md` 的
-- 加强版定义落成**可编译的 record**，并给出 DC 的**本源实例**。
--
-- ## 为什么需要 v2（v1 = `Presentation.agda` 的 13 字段版）
--
-- v1 有 7 处约束不足（G1–G7）。2026-10-21 审核发现 v1 文档的两条判断有误：
--
-- **① `rigidity-hom` + `rigidity-invol` 排除不了 `ρ`** ✗
--   库内已证：`rho-mixedOp`（DuodecClock:734，ρ 是自同构）、
--            `rho-involution`（:699，ρ 是对合）、`rho-is-inv`（:739，ρ = 群反转）。
--   ⇒ 「自同构 + 对合」是**交换群上逆映射也满足**的弱条件 ⇒ 没有判别力 ✗
--
-- **② 唯一判别式是 `add (rigidity x) ≡ add x`**（N10）✓
--   `μ` 是域自同构的运输、固定素域 GF(3) ⇒ 加法分量不动；
--   `ρ` 把 `t ↦ -t` ⇒ 不是 Frobenius 的运输（见 docs/39）。
--
-- ## ★ 核心洞察：`add` 一个字段闭合三个本体论缺口
--
-- ```
--        add : A → Trit
--             │
--    ┌────────┼────────┐
--    ▼        ▼        ▼
--  ② 生成元  ⑥ 归零   ⑦ 刚性
--  来源     ⊕³ 层    判别 μ vs ρ
-- ```
--   · ② 生成元来源：`add-hom`（加法分量是 step 的同态）
--   · ⑥ 归零（加法层）：`add-oblivion`（`(x⊞x)⊞x = T₀`）—— 逐字就是 `tritCycle`
--   · ⑦ 刚性判别：`rigidity-fixes-add`（排除 ρ）
--
-- ⚠ **四层归零里两层 v1 已有**：`phase-cycle`（α⁴）与 `clock-cycle`（¹²）就是归零 ✗
--   v1 文档说「record 只覆盖第三种」不准确 —— 缺的只是**加法层** ⊕³ ✓
--
-- ## 诚实边界
--
--   · 本模块是**新增**，不改 `Presentation.agda` ⇒ **零级联** ✓
--   · DC 侧 14 条约束**全部有内核回执**，0 postulate / 0 hole ✓
--   · `clock-min` 用 `Fin clock` 形式（clock 以下无正周期），与 `<` 形式判别力等价 ✓
--   · 尚未迁移 `Presentation` 本体（G7 的完整闭合需替换旧 record，见 42 号文 §6.2）

module Sovereign.Algebra.UniversalAlgebra.PresentationV2 where

open import Data.Nat using (ℕ; _<_; s≤s; z≤n)
open import Data.Fin using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)

-- ⚠ 不在本模块重复声明 `infixl 6 _⊕_`：fixity 随 Base.Trit 导入即可，
--   重复声明会触发 UnknownNamesInFixityDecl（2026-10-21 实测）
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.GroupTheory.DuodecClock
  using (DuodecPoint; AlphaPower; a0; a1; a2; a3;
         mixedOp; duodec-e; mulAlpha; alphaInv; mu; rho;
         mixedOp-assoc; mixedOp-identityˡ; mixedOp-identityʳ;
         rho-alphaInv-homo;
         ZeroOblivion; zero-oblivion-instance)
open import Sovereign.Algebra.UniversalAlgebra.Presentation
  using (iterate; dc-phase; dc-phase-cycle; dc-clock-cycle;
         dc-phase-step-comm; dc-phase-g-comm; dc-clock-neq-phase)

--------------------------------------------------------------------------------
-- §1. 展示群定义 v2（28 字段）
--------------------------------------------------------------------------------

record PresentationV2 (A : Set) : Set₁ where
  field
    -- ═══ ② 生成元（联合运算 + 生成元 + **加法分量来源**）══════════════
    step  : A → A → A
    g     : A
    unit  : A
    add   : A → Trit
    add-op : Trit → Trit → Trit
    add-hom  : ∀ x y → add (step x y) ≡ add-op (add x) (add y)
    add-zero : add unit ≡ T₀

    -- ═══ ③ 关系（结合律 + 单位律）═══════════════════════════════════
    assoc  : ∀ x y z → step (step x y) z ≡ step x (step y z)
    zeroˡ  : ∀ x → step unit x ≡ x
    zeroʳ  : ∀ x → step x unit ≡ x

    -- ═══ ④ 相位（分量级旋转）═══════════════════════════════════════
    phase            : A → A
    phase-order      : ℕ
    phase-cycle      : ∀ x → iterate phase phase-order x ≡ x
    phase-nontrivial : 1 < phase-order
    phase-hom        : ∀ x y → phase (step x y) ≡ step (phase x) y   -- 单边（双边为假）
    phase-g-comm     : ∀ x → phase (step g x) ≡ step g (phase x)

    -- ═══ ⑤ 时钟（联合周期 + 极小性 + 联合性）═══════════════════════
    clock           : ℕ
    clock-cycle     : ∀ x → iterate (λ y → step y g) clock x ≡ x
    clock-min       : ∀ (k : Fin clock) → 0 < toℕ k
                    → ¬ (∀ x → iterate (λ y → step y g) (toℕ k) x ≡ x)
    clock-phase     : phase-order ∣ clock
    clock-neq-phase : phase-order < clock

    -- ═══ ② 生成性（g 生成整个载体 —— 本体论级）═════════════════════
    generated : ∀ x → ∃ (λ n → iterate (λ y → step y g) n unit ≡ x)

    -- ═══ ⑥ 归零（加法层；相位层/联合层由 phase-cycle / clock-cycle 承载）═══
    add-oblivion : ∀ x → add-op (add-op (add x) (add x)) (add x) ≡ T₀

    -- ═══ ⑦ 刚性（域自同构的运输）═══════════════════════════════════
    rigidity           : A → A
    rigidity-hom       : ∀ x y → rigidity (step x y) ≡ step (rigidity x) (rigidity y)
    rigidity-invol     : ∀ x → rigidity (rigidity x) ≡ x
    rigidity-fixes-add : ∀ x → add (rigidity x) ≡ add x   -- ★ 唯一能排除 ρ 的字段

    -- ═══ ⑧ 核对（refl 层，不产生结构）══════════════════════════════
    check : ∀ x → step x unit ≡ x

open PresentationV2 public

--------------------------------------------------------------------------------
-- §2. DC 的本源实例：14 条新约束全部有内核回执
--------------------------------------------------------------------------------

dc-g : DuodecPoint
dc-g = (T₁ , a1)

dc-gStep : DuodecPoint → DuodecPoint
dc-gStep y = mixedOp y dc-g

-- ② add 四件套
dc-add : DuodecPoint → Trit
dc-add = proj₁

dc-add-hom : ∀ x y → dc-add (mixedOp x y) ≡ dc-add x ⊕ dc-add y
dc-add-hom (t , a) (u , b) = refl

dc-add-zero : dc-add duodec-e ≡ T₀
dc-add-zero = refl

-- ⑥ 加法层归零 ⊕³ —— 逐字就是 ZeroOblivion.tritCycle（零新证）
dc-add-oblivion : ∀ x → (dc-add x ⊕ dc-add x) ⊕ dc-add x ≡ T₀
dc-add-oblivion x = ZeroOblivion.tritCycle zero-oblivion-instance (dc-add x)

-- ⑦ N10：μ 固定加法分量（ρ 在此失败 ⇒ 排除 ρ）
dc-rigidity-fixes-add : ∀ x → dc-add (mu x) ≡ dc-add x
dc-rigidity-fixes-add (t , a) = refl

-- ⑦ N5：μ 是自同构（相位侧复用 rho-alphaInv-homo —— 该引理与 ρ 无关）
dc-rigidity-hom : ∀ x y → mu (mixedOp x y) ≡ mixedOp (mu x) (mu y)
dc-rigidity-hom (t , a) (u , b) = cong₂ _,_ refl (rho-alphaInv-homo a b)

-- ⑦ N6：μ 是对合
dc-rigidity-invol : ∀ x → mu (mu x) ≡ x
dc-rigidity-invol (T₀ , a0) = refl
dc-rigidity-invol (T₀ , a1) = refl
dc-rigidity-invol (T₀ , a2) = refl
dc-rigidity-invol (T₀ , a3) = refl
dc-rigidity-invol (T₁ , a0) = refl
dc-rigidity-invol (T₁ , a1) = refl
dc-rigidity-invol (T₁ , a2) = refl
dc-rigidity-invol (T₁ , a3) = refl
dc-rigidity-invol (T₂ , a0) = refl
dc-rigidity-invol (T₂ , a1) = refl
dc-rigidity-invol (T₂ , a2) = refl
dc-rigidity-invol (T₂ , a3) = refl

-- ② N4：g 的 12 次幂覆盖全部 12 个元素 ⇒ g 生成整个载体
dc-generated : ∀ x → ∃ (λ n → iterate dc-gStep n duodec-e ≡ x)
dc-generated (T₀ , a0) = 0 , refl
dc-generated (T₀ , a1) = 9 , refl
dc-generated (T₀ , a2) = 6 , refl
dc-generated (T₀ , a3) = 3 , refl
dc-generated (T₁ , a0) = 4 , refl
dc-generated (T₁ , a1) = 1 , refl
dc-generated (T₁ , a2) = 10 , refl
dc-generated (T₁ , a3) = 7 , refl
dc-generated (T₂ , a0) = 8 , refl
dc-generated (T₂ , a1) = 5 , refl
dc-generated (T₂ , a2) = 2 , refl
dc-generated (T₂ , a3) = 11 , refl

-- ⑤ N2：时钟极小性 —— clock = 12 以下没有正周期
-- Fin 形式与「k < clock」判别力等价；Fin 形式免去 k ≥ 12 的空情形
dc-T₁≢T₀ : T₁ ≡ T₀ → ⊥
dc-T₁≢T₀ ()
dc-T₂≢T₀ : T₂ ≡ T₀ → ⊥
dc-T₂≢T₀ ()
dc-a₁≢a₀ : a1 ≡ a0 → ⊥
dc-a₁≢a₀ ()
dc-a₂≢a₀ : a2 ≡ a0 → ⊥
dc-a₂≢a₀ ()
dc-a₃≢a₀ : a3 ≡ a0 → ⊥
dc-a₃≢a₀ ()

dc-clock-min : ∀ (k : Fin 12) → 0 < toℕ k
             → ¬ (∀ x → iterate dc-gStep (toℕ k) x ≡ x)
dc-clock-min Fin.zero () _
dc-clock-min (Fin.suc Fin.zero) _ h = dc-T₁≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc Fin.zero)) _ h = dc-T₂≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc Fin.zero))) _ h = dc-a₃≢a₀ (cong proj₂ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) _ h = dc-T₁≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) _ h = dc-T₂≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) _ h = dc-a₂≢a₀ (cong proj₂ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) _ h = dc-T₁≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))) _ h = dc-T₂≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))) _ h = dc-a₁≢a₀ (cong proj₂ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))) _ h = dc-T₁≢T₀ (cong proj₁ (h (T₀ , a0)))
dc-clock-min (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))) _ h = dc-T₂≢T₀ (cong proj₁ (h (T₀ , a0)))

-- ④ N1：相位非平凡（1 < 4）
dc-phase-nontrivial : 1 < 4
dc-phase-nontrivial = s≤s (s≤s z≤n)

-- ⑤ N3：相位阶整除时钟（4 ∣ 12）
dc-clock-phase : 4 ∣ 12
dc-clock-phase = divides 3 refl

-- ═══ 本源实例 ═══
dc-presentation-v2 : PresentationV2 DuodecPoint
dc-presentation-v2 = record
  { step             = mixedOp
  ; g                = dc-g
  ; add              = dc-add
  ; add-op           = _⊕_
  ; add-hom          = dc-add-hom
  ; add-zero         = dc-add-zero
  ; assoc            = mixedOp-assoc
  ; unit             = duodec-e
  ; zeroˡ            = mixedOp-identityˡ
  ; zeroʳ            = mixedOp-identityʳ
  ; phase            = dc-phase
  ; phase-order      = 4
  ; phase-cycle      = dc-phase-cycle
  ; phase-nontrivial = dc-phase-nontrivial
  ; phase-hom        = dc-phase-step-comm
  ; phase-g-comm     = dc-phase-g-comm
  ; clock            = 12
  ; clock-cycle      = dc-clock-cycle
  ; clock-min        = dc-clock-min
  ; clock-phase      = dc-clock-phase
  ; clock-neq-phase  = dc-clock-neq-phase
  ; generated        = dc-generated
  ; add-oblivion     = dc-add-oblivion
  ; rigidity         = mu
  ; rigidity-hom     = dc-rigidity-hom
  ; rigidity-invol   = dc-rigidity-invol
  ; rigidity-fixes-add = dc-rigidity-fixes-add
  ; check            = mixedOp-identityʳ
  }

-- ★★ N10 的**判别力**（内核级证据）：ρ = λ∘μ 满足 N5+N6，但违反 N10 ⇒ 被排除
--   ρ (T₁ , a0) = (negate T₁ , a0) = (T₂ , a0)  ⇒  add (ρ x) = T₂ ≠ T₁ = add x
dc-T₂≢T₁ : T₂ ≡ T₁ → ⊥
dc-T₂≢T₁ ()

dc-rho-not-fixes-add : ∃ (λ x → dc-add (rho x) ≢ dc-add x)
dc-rho-not-fixes-add = (T₁ , a0) , dc-T₂≢T₁
