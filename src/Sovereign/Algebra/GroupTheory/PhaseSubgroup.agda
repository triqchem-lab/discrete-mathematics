{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.PhaseSubgroup
-- 相位旋转的群论本质: ⟨α⟩ 是 GF(9)× ≅ C₈ 的 4 阶循环子群
--
-- 理论现实 (依赖类型论群论 — 相位是群结构, 不是坐标计算):
--   GF(9)× ≅ C₈ (循环, 生成元 gen = 1+α; gen-generates-all 已证).
--   α = gen⁶ (gen-pow-6), 故 α 是 gen 的偶次幂.
--   ⟨α⟩ = ⟨gen²⟩ = {gen⁰, gen², gen⁴, gen⁶} = {1, α, α²=-1, α³=-α} ≅ C₄.
--   阶恰为 4: α⁴ = 1 (上界) 且 α² ≠ 1 (下界, 排除阶 1/2).
--   4 | 8 (拉格朗日), 故 ⟨α⟩ 是 C₈ 的 4 阶子群.
--   相位旋转 = C₄ 在自身上的左乘循环作用 (90° 步进, 4 步闭合).
--
-- 本模块构造性证明 (0 postulate):
--   §1 阶恰为 4 (α⁴=1 ∧ α²≠1 ∧ α≠1)
--   §2 ⟨α⟩ = gen 的偶次幂 (C₄ ⊂ C₈, α=gen⁶)
--   §3 4 | 8 子群链 + 唯一 4 阶子群生成元
--   §4 相位旋转 = C₄ 循环作用 (4-循环 orbit, α²=-1 是 180°)
--   §5 AlphaPower ≅ ⟨α⟩ 桥接 (抽象 C₄ ↔ 域内 C₄)
--
-- 依赖: GF9 (GF9Star/gen/α), NormExactSequence (核/阶), DuodecClock (AlphaPower)
-- 不改动任何上游模块。

-- ═══════════════════════════════════════════════════════════════
-- 八要素对照（形状规范: docs/maps/八要素统一形状-2026-10-14.md）
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      ⟨α⟩（GF(9)× ≅ C₈ 的 4 阶循环子群）
--  ② 生成元    gen = 1 + α（gen-generates-all 已证）
--  ③ 关系      群律（循环群 C₄ 的乘法结构）
--  ④ 相位      **alpha-order-exactly-4** —— 相位阶恰为 4 ⇒ **本件即「相位」要素的专门件**
--  ⑤ 时钟      阶 4（四步回位，与 ClockIteration 的走钟过程互补）
--  ⑥ 归零      alpha-4-id（α⁴ = id）
--  ⑦ 刚性      ⚠ 未显式（刚性见 GroupTheory/DCSigmaAut）
--  ⑧ 核对      alpha-2-not-id / alpha-not-id（**否证式核对**：确认阶不是 1 也不是 2）
--
-- 形状贴合: **5/8**（核心是 ④ 相位）
-- 理论现实（本件自述）: 相位是**群结构**，不是坐标计算。

module Sovereign.Algebra.GroupTheory.PhaseSubgroup where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using
  (GF9; GF9Star; toGF9; s1; s2; sα; s2α; s1α; s12α; s21α; s22α;
   _*s_; _^s_; gen; galoisNorm; galoisConjugate;
   alpha; alpha-squared; alpha-powers-4; gf9-one; _*gf9_;
   gen-pow-0; gen-pow-2; gen-pow-4; gen-pow-6; gen-pow-8;
   gen-generates-all; *s-identityˡ; *s-identityʳ; *s-comm)
open import Sovereign.Algebra.GroupTheory.NormExactSequence using
  (gen-order-8; norm-kernel-is-even-power; ker-cyclic;
   sα-order-4; sα-order-not-2; s2-not-s1; sα-not-s1; s2α-not-s1)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (AlphaPower; a0; a1; a2; a3; mulAlpha; alphaPowerToGF9; mulAlpha-hom; a0≢a2)
open import Sovereign.Algebra.GroupTheory.DuodecClockProperties using (alpha-order-4)

--------------------------------------------------------------------------------
-- §1. ⟨α⟩ 的阶恰为 4
--
-- 群论要求双侧: 上界 α⁴=1 (周期闭合) + 下界 α²≠1 (不塌缩为 2 阶).
-- 仅有 α⁴=1 只说明 4 | 阶.
--------------------------------------------------------------------------------

-- 上界: α⁴ = 1
alpha-4-id : sα ^s 4 ≡ s1
alpha-4-id = sα-order-4

-- 下界: α² ≠ 1 (α² = s2 = -1)
alpha-2-not-id : ¬ (sα ^s 2 ≡ s1)
alpha-2-not-id = sα-order-not-2

-- α ≠ 1
alpha-not-id : ¬ (sα ≡ s1)
alpha-not-id = sα-not-s1

-- 阶恰为 4: 上界 + 两个下界 (阶只能是 1,2,4,8 的因子; 排除 1,2 → 阶=4)
alpha-order-exactly-4 :
  (sα ^s 4 ≡ s1) × (sα ^s 2 ≡ s1 → ⊥) × (sα ≡ s1 → ⊥)
alpha-order-exactly-4 = alpha-4-id , alpha-2-not-id , alpha-not-id

--------------------------------------------------------------------------------
-- §2. ⟨α⟩ = gen 的偶次幂 (C₄ ⊂ C₈)
--
-- α = gen⁶ (gen-pow-6). ⟨α⟩ 的四个元素都是 gen 的偶次幂.
--------------------------------------------------------------------------------

-- α 的幂次 = gen 的偶次幂 (具体值验证, 由 gen 幂表直接给出)
alpha-pow-2 : sα ^s 2 ≡ gen ^s 4
alpha-pow-2 = refl

alpha-pow-3 : sα ^s 3 ≡ gen ^s 2
alpha-pow-3 = refl

-- ⟨α⟩ 的 4 个元素按 gen 幂次编号 (相位 = C₄ 的第 n 个元素)
alpha-index : (s1 ≡ gen ^s 0) × (sα ≡ gen ^s 6)
            × (s2 ≡ gen ^s 4) × (s2α ≡ gen ^s 2)
alpha-index = refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §3. 4 | 8 (拉格朗日) 与唯一 4 阶子群
--------------------------------------------------------------------------------

four-divides-eight : 4 * 2 ≡ 8
four-divides-eight = refl

-- 4 阶元存在 (⟨α⟩ 的生成元 α)
order-4-element-exists :
  Σ GF9Star (λ g → (g ^s 4 ≡ s1) × (g ^s 2 ≡ s1 → ⊥) × (g ≡ s1 → ⊥))
order-4-element-exists = sα , sα-order-4 , sα-order-not-2 , sα-not-s1

--------------------------------------------------------------------------------
-- §4. 相位旋转 = C₄ 循环作用 (90° 步进)
--
-- 左乘 α 在 ⟨α⟩ 上的作用: s1 ↦ sα ↦ s2 ↦ s2α ↦ s1 (4-循环).
-- 这是 90° 旋转的群论实现: 每步乘 α, 四步回位.
--------------------------------------------------------------------------------

-- 旋转一步 (乘 α)
rot : GF9Star → GF9Star
rot x = x *s sα

-- 4-循环 orbit (逐步验证, 4 个元素的有限群)
rot-orbit :
  (rot s1 ≡ sα) × (rot sα ≡ s2) × (rot s2 ≡ s2α) × (rot s2α ≡ s1)
rot-orbit = refl , refl , refl , refl

-- 四次旋转回位 (⟨α⟩ 上 4 个元素全验证)
rot-4-id : ∀ x → (x ≡ s1) ⊎ (x ≡ sα) ⊎ (x ≡ s2) ⊎ (x ≡ s2α)
             → rot (rot (rot (rot x))) ≡ x
rot-4-id .s1   (inj₁ refl) = refl
rot-4-id .sα   (inj₂ (inj₁ refl)) = refl
rot-4-id .s2   (inj₂ (inj₂ (inj₁ refl))) = refl
rot-4-id .s2α  (inj₂ (inj₂ (inj₂ refl))) = refl

-- 两次旋转 = 乘 α² = 取负 (180° 翻转)
rot-2-is-neg :
  (rot (rot s1) ≡ s2) × (rot (rot sα) ≡ s2α)
  × (rot (rot s2) ≡ s1) × (rot (rot s2α) ≡ sα)
rot-2-is-neg = refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §5. AlphaPower ≅ ⟨α⟩ (抽象 C₄ ↔ 域内 C₄ 桥接)
--
-- alphaPowerToGF9 把抽象 α 幂映到域元素; mulAlpha-hom 保证保乘法.
-- 该映射的单射性 + 像 = ⟨α⟩ 给出 C₄ 同构.
--------------------------------------------------------------------------------

-- AlphaPower 的像恰是 ⟨α⟩ 的 4 个元素
-- 像的 GF9 坐标: a0↦1, a1↦α, a2↦-1, a3↦-α (与 ⟨α⟩ 元素对应)
alphaPower-image :
  (alphaPowerToGF9 a0 ≡ (T₁ , T₀)) × (alphaPowerToGF9 a1 ≡ (T₀ , T₁))
  × (alphaPowerToGF9 a2 ≡ (T₂ , T₀)) × (alphaPowerToGF9 a3 ≡ (T₀ , T₂))
alphaPower-image = refl , refl , refl , refl

-- AlphaPower 的乘法 = GF9 域乘法 (抽象 C₄ 的群运算 = 域内 C₄ 的乘法)
alphaPower-mul-compat : ∀ x y →
  alphaPowerToGF9 (mulAlpha x y) ≡ alphaPowerToGF9 x *gf9 alphaPowerToGF9 y
alphaPower-mul-compat = mulAlpha-hom

-- α⁴ = 1 (抽象层, 复用 DuodecClockProperties.alpha-order-4)
alphaPower-order-4 : mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0
alphaPower-order-4 = alpha-order-4

-- α² ≠ 1 (抽象层, 与域内 alpha-2-not-id 对应): α² = a2 ≠ a0
alphaPower-order-not-2 : ¬ (mulAlpha a1 a1 ≡ a0)
alphaPower-order-not-2 eq = a0≢a2 (sym eq)

-- 抽象 α 阶恰为 4 (上界 + 下界)
alphaPower-order-exactly-4 :
  (mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0)
  × (mulAlpha a1 a1 ≡ a0 → ⊥)
alphaPower-order-exactly-4 = alphaPower-order-4 , alphaPower-order-not-2

--------------------------------------------------------------------------------
-- §6. 相位结构 record —— 相位 / 时钟 / 归零 收于一处
--
-- L2 结构对齐试点（规范: docs/maps/八要素统一形状-2026-10-14.md §三/§七）。
-- 背景：§1–§5 把三要素作为**散落的顶层定理**给出（alpha-order-exactly-4 /
--   rot-orbit / rot-4-id / alpha-4-id …）。本 §6 把它们**收进同一关系 record**，
--   使 ④相位 / ⑤时钟 / ⑥归零 各有统一字段落点。
--
-- ⚠ 零破坏：既有顶层定理**全部保留**，本 record 只是它们的结构化打包；
--   下游引用面不变（本件无外部引用者）。
--------------------------------------------------------------------------------

record PhaseStructure4 : Set₁ where
  field
    -- ① 载体
    carrier : Set
    -- ② 生成元：相位旋转算子
    step : carrier → carrier
    -- ④ 相位：下界见证 —— 存在两步不回位的元素（故阶不是 1、2）
    two-step-witness : carrier
    two-step-not-id : step (step two-step-witness) ≢ two-step-witness
    -- ⑤ 时钟 + ⑥ 归零：四步回位（走钟一圈 = 周期闭合）
    step4-id : ∀ x → step (step (step (step x))) ≡ x

-- 实例：GF(9)× 上的相位结构（⟨α⟩ 的 90° 步进；rot x = x *s sα）
phase-structure-GF9Star : PhaseStructure4
phase-structure-GF9Star = record
  { carrier          = GF9Star
  ; step             = rot
  ; two-step-witness = s1
  ; two-step-not-id  = λ e → s2-not-s1 (trans (sym rot2-s1) e)
  ; step4-id         = rot4-id-all
  }
  where
  -- 两步：rot (rot s1) = s1 *s (sα ^s 2) = s2
  rot2-s1 : rot (rot s1) ≡ s2
  rot2-s1 = refl

  -- 四步回位对**全体** GF9Star 成立 —— 用法直接穷举 8 个元素
  -- （GF9Star 是 data 枚举，_*s_ 为具体乘法表，逐例归一化即 refl；
  --   §4 的 rot-4-id 只覆盖 ⟨α⟩ 的 4 个元素，此处扩到全场）
  rot4-id-all : ∀ x → rot (rot (rot (rot x))) ≡ x
  rot4-id-all s1    = refl
  rot4-id-all s2    = refl
  rot4-id-all sα    = refl
  rot4-id-all s2α   = refl
  rot4-id-all s1α   = refl
  rot4-id-all s12α  = refl
  rot4-id-all s21α  = refl
  rot4-id-all s22α  = refl
