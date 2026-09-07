{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.NormExactSequence
-- 范数坍缩的群论本质: 短正合列 1 → C₄ → C₈ → C₂ → 1 不分裂
--
-- 理论现实 (依赖类型论群论):
--   GF(9)× ≅ C₈ (循环, 生成元 gen = 1+α, 已证 gen-generates-all).
--   范数 N : GF(9)× → GF(3)× 是乘法同态 (norm-mul, 已证).
--   核 ker N = ⟨α⟩ ≅ C₄ = {s1, sα, s2, s2α} (4 个相位元坍缩到范数 1).
--   像 = {T₁, T₂} ≅ C₂ (满射).
--   短正合列 1 → C₄ → C₈ → C₂ → 1 不分裂:
--     因 C₈ 是循环群, 2 阶元唯一 (gen⁴ = α² = -1); 而 C₄×C₂ 有 3 个 2 阶元.
--
-- 本模块构造性证明 (全部 0 postulate, 穷举 refl):
--   P1 gen-order-8   : gen 阶恰为 8 (gen⁸=1 且 gen⁴≠1)
--   P2 unique-2-torsion : C₈ 中 x²=1 ⟹ x ∈ {s1, s2} (唯一非平凡 2 阶元 = s2)
--   P3 norm-kernel   : N(x)=1 ⟹ x ∈ {s1, sα, s2, s2α} (核 ≅ C₄)
--   P4 norm-surj     : 范数满射到 {T₁, T₂} (像 ≅ C₂)
--
-- 依赖: GF9 (GF9Star, gen, galoisNorm, toGF9, norm-mul) — 已完成体系

module Sovereign.Algebra.GroupTheory.NormExactSequence where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using
  (GF9; GF9Star; toGF9; s1; s2; sα; s2α; s1α; s12α; s21α; s22α;
   _*s_; _^s_; gen; galoisNorm;
   gen-pow-0; gen-pow-2; gen-pow-4; gen-pow-6; gen-pow-8; gen-generates-all)

--------------------------------------------------------------------------------
-- 构造子不相交 (穷举基础)
--------------------------------------------------------------------------------

s2-not-s1 : s2 ≡ s1 → ⊥
s2-not-s1 ()

T₂-not-T₁ : T₂ ≡ T₁ → ⊥
T₂-not-T₁ ()

s2α-not-s1 : s2α ≡ s1 → ⊥
s2α-not-s1 ()

sα-not-s1 : sα ≡ s1 → ⊥
sα-not-s1 ()

-- 逻辑等价 (本地, 双向蕴含)
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

--------------------------------------------------------------------------------
-- P1. gen 的阶恰为 8
--------------------------------------------------------------------------------

-- gen⁸ = 1 (已有 gen-pow-8), 且 gen⁴ ≠ 1 (gen⁴ = s2 ≠ s1)
gen-order-8 : (gen ^s 8 ≡ s1) × (gen ^s 4 ≡ s1 → ⊥)
gen-order-8 = gen-pow-8 , λ eq → s2-not-s1 (trans (sym gen-pow-4) eq)

-- gen 的阶不是 1 或 2: gen ≠ 1 (gen^1 = s1α ≠ s1), gen² ≠ 1 (gen² = s2α ≠ s1)
gen-not-order-1 : gen ≡ s1 → ⊥
gen-not-order-1 ()

gen-not-order-2 : (gen ^s 2) ≡ s1 → ⊥
gen-not-order-2 ()

--------------------------------------------------------------------------------
-- P2. C₈ 的唯一 2 阶元
--
-- x *s x = s1 的 8 个 case: 只有 s1 (平凡) 和 s2 (2 阶元) 满足.
-- 其余 6 个元素的平方 ∈ {s2, s2α, sα} ≠ s1.
--------------------------------------------------------------------------------

unique-2-torsion : ∀ x → x *s x ≡ s1 → x ≡ s1 ⊎ x ≡ s2
unique-2-torsion s1   _  = inj₁ refl
unique-2-torsion s2   _  = inj₂ refl
unique-2-torsion sα   eq = ⊥-elim (s2-not-s1 eq)   -- sα *s sα = s2 ≠ s1
unique-2-torsion s2α  eq = ⊥-elim (s2-not-s1 eq)   -- s2α *s s2α = s2 ≠ s1
unique-2-torsion s1α  eq = ⊥-elim (s2α-not-s1 eq)  -- s1α *s s1α = s2α ≠ s1
unique-2-torsion s12α eq = ⊥-elim (sα-not-s1 eq)   -- s12α *s s12α = sα ≠ s1
unique-2-torsion s21α eq = ⊥-elim (sα-not-s1 eq)   -- s21α *s s21α = sα ≠ s1
unique-2-torsion s22α eq = ⊥-elim (s2α-not-s1 eq)   -- s22α *s s22α = s2α ≠ s1

--------------------------------------------------------------------------------
-- P3. 范数核 = ⟨α⟩ ≅ C₄
--
-- galoisNorm (toGF9 x) = T₁ 的 8 个 case:
--   核 = {s1, s2, sα, s2α} (范数 1), 其余 4 个范数 = T₂.
--   {s1, sα, s2, s2α} = {gen⁰, gen⁶, gen⁴, gen²} = gen 的偶数幂 = ⟨sα⟩.
--------------------------------------------------------------------------------

norm-kernel : ∀ x → galoisNorm (toGF9 x) ≡ T₁ →
             x ≡ s1 ⊎ x ≡ s2 ⊎ x ≡ sα ⊎ x ≡ s2α
norm-kernel s1   _  = inj₁ refl
norm-kernel s2   _  = inj₂ (inj₁ refl)
norm-kernel sα   _  = inj₂ (inj₂ (inj₁ refl))
norm-kernel s2α  _  = inj₂ (inj₂ (inj₂ refl))
norm-kernel s1α  eq = ⊥-elim (T₂-not-T₁ eq)   -- N(1+α)  = 2 = T₂
norm-kernel s12α eq = ⊥-elim (T₂-not-T₁ eq)   -- N(1+2α) = 2 = T₂
norm-kernel s21α eq = ⊥-elim (T₂-not-T₁ eq)   -- N(2+α)  = 2 = T₂
norm-kernel s22α eq = ⊥-elim (T₂-not-T₁ eq)   -- N(2+2α) = 2 = T₂

-- 核的 4 个元素恰是 gen 的偶数幂 (核 = ⟨gen²⟩ = ⟨sα⟩ ≅ C₄)
-- 对应关系: s1=gen⁰, s2α=gen², s2=gen⁴, sα=gen⁶ (按 gen 幂序)
norm-kernel-is-even-power : ∀ x → galoisNorm (toGF9 x) ≡ T₁ →
  (x ≡ gen ^s 0) ⊎ (x ≡ gen ^s 2) ⊎ (x ≡ gen ^s 4) ⊎ (x ≡ gen ^s 6)
norm-kernel-is-even-power s1   _  = inj₁ refl                              -- s1  = gen⁰
norm-kernel-is-even-power s2   _  = inj₂ (inj₂ (inj₁ refl))               -- s2  = gen⁴
norm-kernel-is-even-power sα   _  = inj₂ (inj₂ (inj₂ refl))               -- sα  = gen⁶
norm-kernel-is-even-power s2α  _  = inj₂ (inj₁ refl)                      -- s2α = gen²
norm-kernel-is-even-power s1α  eq = ⊥-elim (T₂-not-T₁ eq)
norm-kernel-is-even-power s12α eq = ⊥-elim (T₂-not-T₁ eq)
norm-kernel-is-even-power s21α eq = ⊥-elim (T₂-not-T₁ eq)
norm-kernel-is-even-power s22α eq = ⊥-elim (T₂-not-T₁ eq)

--------------------------------------------------------------------------------
-- P4. 范数满射 C₈ → C₂ (像 = {T₁, T₂})
--------------------------------------------------------------------------------

-- 每个 GF(3)× 值 {T₁, T₂} 都有 GF9Star 原像
norm-surjective : (Σ GF9Star (λ x → galoisNorm (toGF9 x) ≡ T₁))
                  × (Σ GF9Star (λ x → galoisNorm (toGF9 x) ≡ T₂))
norm-surjective = (s1 , refl) , (s1α , refl)
  -- N(s1) = 1²+0² = T₁; N(s1α) = 1²+1² = 2 = T₂

--------------------------------------------------------------------------------
-- P5. 短正合列不分裂 (元定理形式)
--
-- 1 → C₄ → C₈ → C₂ → 1 不分裂 ⟺ 不存在截面 s : C₂ → C₈ 使 N ∘ s = id.
-- 等价于: 不存在 2 阶元 x ∈ C₈ 使 N(x) = T₂ (截面必须把 C₂ 的 2 阶元
-- 映到 C₈ 的 2 阶元且范数非平凡). 由 P2: C₈ 的 2 阶元只有 s2, 而 N(s2)=T₁,
-- 故无截面 → 不分裂.
--------------------------------------------------------------------------------

-- C₈ 的唯一 2 阶元 s2 的范数 = T₁ (不在像 C₂ 的非平凡原像)
torsion-norm-trivial : galoisNorm (toGF9 s2) ≡ T₁
torsion-norm-trivial = refl

-- 不分裂: 不存在截面 (2 阶元 s2 的范数为 1, 无法映到 C₂ 的生成元 T₂)
-- 形式化: 若截面 s 满足 N(s(x))=x 且 s 保序, 则 s 把 T₂ 映到某 2 阶元 y,
--         但 y 的范数 = T₁ ≠ T₂, 矛盾.
nonsplitting : ¬ (Σ GF9Star (λ y → (y *s y ≡ s1) × (galoisNorm (toGF9 y) ≡ T₂)))
nonsplitting (y , (y2 , ny)) with unique-2-torsion y y2
nonsplitting (y , (y2 , ny)) | inj₁ y=s1 = T₂-not-T₁ (sym (trans (cong (λ z → galoisNorm (toGF9 z)) (sym y=s1)) ny))
nonsplitting (y , (y2 , ny)) | inj₂ y=s2 = T₂-not-T₁ (sym (trans (cong (λ z → galoisNorm (toGF9 z)) (sym y=s2)) ny))

--------------------------------------------------------------------------------
-- P6. 核 ≅ C₄ 的循环结构 (sα 阶 4, 核由 sα 生成)
--------------------------------------------------------------------------------

-- sα (= α) 的阶为 4: α¹ = α, α² = s2, α³ = s2α, α⁴ = s1
sα-order-4 : sα ^s 4 ≡ s1
sα-order-4 = refl

sα-order-not-2 : (sα ^s 2) ≡ s1 → ⊥
sα-order-not-2 eq = s2-not-s1 eq   -- sα² = s2 ≠ s1

-- 核的每个元素都是 sα 的幂 (核 ≅ C₄ 循环, 生成元 sα)
ker-cyclic : ∀ x → galoisNorm (toGF9 x) ≡ T₁ → Σ ℕ (λ n → sα ^s n ≡ x)
ker-cyclic s1   _  = 0 , refl    -- s1  = sα⁰
ker-cyclic sα   _  = 1 , refl    -- sα  = sα¹
ker-cyclic s2   _  = 2 , refl    -- s2  = sα²
ker-cyclic s2α  _  = 3 , refl    -- s2α = sα³
ker-cyclic s1α  eq = ⊥-elim (T₂-not-T₁ eq)
ker-cyclic s12α eq = ⊥-elim (T₂-not-T₁ eq)
ker-cyclic s21α eq = ⊥-elim (T₂-not-T₁ eq)
ker-cyclic s22α eq = ⊥-elim (T₂-not-T₁ eq)

--------------------------------------------------------------------------------
-- P7. 范数值域 = {T₁, T₂} (像 ≅ C₂) — 8 case 穷举
--------------------------------------------------------------------------------

norm-value-in-C2 : ∀ x → galoisNorm (toGF9 x) ≡ T₁ ⊎ galoisNorm (toGF9 x) ≡ T₂
norm-value-in-C2 s1   = inj₁ refl   -- N(1)    = 1
norm-value-in-C2 s2   = inj₁ refl   -- N(2)    = 2² = 1
norm-value-in-C2 sα   = inj₁ refl   -- N(α)    = 0²+1² = 1
norm-value-in-C2 s2α  = inj₁ refl   -- N(2α)   = 0²+2² = 1
norm-value-in-C2 s1α  = inj₂ refl   -- N(1+α)  = 1²+1² = 2
norm-value-in-C2 s12α = inj₂ refl   -- N(1+2α) = 1²+2² = 2
norm-value-in-C2 s21α = inj₂ refl   -- N(2+α)  = 2²+1² = 2
norm-value-in-C2 s22α = inj₂ refl   -- N(2+2α) = 2²+2² = 2

--------------------------------------------------------------------------------
-- P8. 核的双向刻画 (正向 = norm-kernel, 反向 = 核元素范数确为 1)
--------------------------------------------------------------------------------

norm-kernel-reverse : ∀ x → (x ≡ s1 ⊎ x ≡ s2 ⊎ x ≡ sα ⊎ x ≡ s2α)
                    → galoisNorm (toGF9 x) ≡ T₁
norm-kernel-reverse s1   _  = refl
norm-kernel-reverse s2   _  = refl
norm-kernel-reverse sα   _  = refl
norm-kernel-reverse s2α  _  = refl
norm-kernel-reverse s1α  (inj₁ ())
norm-kernel-reverse s1α  (inj₂ (inj₁ ()))
norm-kernel-reverse s1α  (inj₂ (inj₂ (inj₁ ())))
norm-kernel-reverse s1α  (inj₂ (inj₂ (inj₂ ())))
norm-kernel-reverse s12α (inj₁ ())
norm-kernel-reverse s12α (inj₂ (inj₁ ()))
norm-kernel-reverse s12α (inj₂ (inj₂ (inj₁ ())))
norm-kernel-reverse s12α (inj₂ (inj₂ (inj₂ ())))
norm-kernel-reverse s21α (inj₁ ())
norm-kernel-reverse s21α (inj₂ (inj₁ ()))
norm-kernel-reverse s21α (inj₂ (inj₂ (inj₁ ())))
norm-kernel-reverse s21α (inj₂ (inj₂ (inj₂ ())))
norm-kernel-reverse s22α (inj₁ ())
norm-kernel-reverse s22α (inj₂ (inj₁ ()))
norm-kernel-reverse s22α (inj₂ (inj₂ (inj₁ ())))
norm-kernel-reverse s22α (inj₂ (inj₂ (inj₂ ())))

-- 核的双向刻画: N(x)=T₁ ⟺ x ∈ {s1,s2,sα,s2α}
norm-kernel-iff : ∀ x → (galoisNorm (toGF9 x) ≡ T₁)
                 ↔ (x ≡ s1 ⊎ x ≡ s2 ⊎ x ≡ sα ⊎ x ≡ s2α)
norm-kernel-iff x = norm-kernel x , norm-kernel-reverse x

-- 0 postulate.
