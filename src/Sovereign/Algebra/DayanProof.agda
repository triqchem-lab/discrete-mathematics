{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanProof
-- 大衍求一术 L2 完整证明——div-rel 反转版（消除消去步骤）
--
-- 核心策略：div-rel 用 r ≡ rb - q×rt 形式（定义式），非 rb ≡ q×rt + r。
-- 这消除了消去引理的需要——proof 只需三步 trans。
module Sovereign.Algebra.DayanProof where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ; _+_; _*_; _-_; -_)
open import Data.Integer.Properties using
  ( *-identityˡ; *-zeroˡ; +-identityʳ
  ; *-distribʳ-+; *-distribˡ-+
  ; neg-distribˡ-*; neg-distrib-+
  ; +-assoc; +-comm; *-assoc; +-inverseʳ
  )
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Product using (Σ; _×_; _,_)

--------------------------------------------------------------------------------
-- §1. 不变量
--------------------------------------------------------------------------------

Inv : ℕ → ℕ → ℤ → ℕ → Set
Inv 奇₀ 定₀ s rt = Σ ℤ (λ k → s * (+ 奇₀) + k * (+ 定₀) ≡ + rt)

--------------------------------------------------------------------------------
-- §2. step-invariant
--------------------------------------------------------------------------------

step-invariant : ∀ (奇₀ 定₀ : ℕ) (lt lb : ℤ) (rt rb : ℕ) (q : ℤ) (r : ℕ) →
  Inv 奇₀ 定₀ lt rt →       -- lt×奇 + k₁×定 = rt
  Inv 奇₀ 定₀ lb rb →       -- lb×奇 + k₂×定 = rb
  (+ r) ≡ (+ rb) - (q * (+ rt)) →  -- r 的定义
  Inv 奇₀ 定₀ (lb + (- (q * lt))) r

step-invariant 奇₀ 定₀ lt lb rt rb q r
  (k₁ , inv-cur) (k₂ , inv-prev) div-rel =
  (k₂ + (- (q * k₁)) , proof)

  where

    -- Step 1（唯一 hole）：分配律展开 + 重排
    -- 将 (lb + (-(q*lt)))*奇 + (k₂ + (-(q*k₁)))*定
    -- 化为 (lb*奇 + k₂*定) + (-(q*(lt*奇 + k₁*定)))
    --
    -- 需要的引理：
    --   *-distribʳ-+ ×2（展开两个乘积）
    --   neg-distribˡ-* ×2（(-(q*lt))*奇 → -((q*lt)*奇)）
    --   neg-distrib-+（-(A)+-(B) → -(A+B)）
    --   +-assoc/+-comm（重排）
    --   *-distribˡ-+ 反向（q*(lt*奇)+q*(k₁*定) → q*(lt*奇+k₁*定)）

    -- 辅助引理：ℤ 加法交换重排
    -- (a+b)+(c+d) ≡ (a+c)+(b+d)
    +ℤ-swap : ∀ (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
    +ℤ-swap a b c d =
      trans (+-assoc a b (c + d))
      (trans (cong (λ x → a + x) (sym (+-assoc b c d)))
      (trans (cong (λ x → a + (x + d)) (+-comm b c))
      (trans (cong (λ x → a + x) (+-assoc c b d))
             (sym (+-assoc a c (b + d))))))
    -- (a+b)+(c+d) → a+(b+(c+d)) → a+((b+c)+d) → a+((c+b)+d) → a+(c+(b+d)) → (a+c)+(b+d)

    rearranged :
      (lb + (- (q * lt))) * (+ 奇₀) + (k₂ + (- (q * k₁))) * (+ 定₀)
      ≡ (lb * (+ 奇₀) + k₂ * (+ 定₀)) + (- (q * (lt * (+ 奇₀) + k₁ * (+ 定₀))))
    rearranged =
      -- Step 1: 展开
      let -- 显式类型注解帮助 Agda 推断
          dist₁ : (lb + (- (q * lt))) * (+ 奇₀) ≡ lb * (+ 奇₀) + (- (q * lt)) * (+ 奇₀)
          dist₁ = *-distribʳ-+ (+ 奇₀) lb (- (q * lt))

          dist₂ : (k₂ + (- (q * k₁))) * (+ 定₀) ≡ k₂ * (+ 定₀) + (- (q * k₁)) * (+ 定₀)
          dist₂ = *-distribʳ-+ (+ 定₀) k₂ (- (q * k₁))

          step₁ : (lb + (- (q * lt))) * (+ 奇₀) + (k₂ + (- (q * k₁))) * (+ 定₀)
                 ≡ (lb * (+ 奇₀) + (- (q * lt)) * (+ 奇₀)) + (k₂ * (+ 定₀) + (- (q * k₁)) * (+ 定₀))
          step₁ = cong₂ _+_ dist₁ dist₂

          -- Step 2: 负号分配 (neg-distribˡ-* 对两个负项)
          --   (-(q*lt)) * 奇₀ ≡ -((q*lt) * 奇₀) ≡ -(q * (lt*奇₀))
          neg₁ : (- (q * lt)) * (+ 奇₀) ≡ (- (q * (lt * (+ 奇₀))))
          neg₁ = trans (sym (neg-distribˡ-* (q * lt) (+ 奇₀)))
                       (cong (-_) (*-assoc q lt (+ 奇₀)))

          neg₂ : (- (q * k₁)) * (+ 定₀) ≡ (- (q * (k₁ * (+ 定₀))))
          neg₂ = trans (sym (neg-distribˡ-* (q * k₁) (+ 定₀)))
                       (cong (-_) (*-assoc q k₁ (+ 定₀)))

          step₂ : (lb * (+ 奇₀) + (- (q * lt)) * (+ 奇₀)) + (k₂ * (+ 定₀) + (- (q * k₁)) * (+ 定₀))
                 ≡ (lb * (+ 奇₀) + (- (q * (lt * (+ 奇₀))))) + (k₂ * (+ 定₀) + (- (q * (k₁ * (+ 定₀)))))
          step₂ = cong₂ _+_ (cong (λ x → lb * (+ 奇₀) + x) neg₁)
                            (cong (λ x → k₂ * (+ 定₀) + x) neg₂)

          -- Step 3: 重排 (用 +ℤ-swap)
          -- (A + -(B)) + (C + -(D)) → (A + C) + (-(B) + -(D))
          step₃ : (lb * (+ 奇₀) + (- (q * (lt * (+ 奇₀))))) + (k₂ * (+ 定₀) + (- (q * (k₁ * (+ 定₀)))))
                 ≡ (lb * (+ 奇₀) + k₂ * (+ 定₀)) + ((- (q * (lt * (+ 奇₀)))) + (- (q * (k₁ * (+ 定₀)))))
          step₃ = +ℤ-swap (lb * (+ 奇₀)) (- (q * (lt * (+ 奇₀))))
                          (k₂ * (+ 定₀)) (- (q * (k₁ * (+ 定₀))))

          -- Step 4a: 合并负项 (neg-distrib-+ 反向)
          -- -(B) + -(D) → -(B + D)
          step₄a : ((- (q * (lt * (+ 奇₀))))) + ((- (q * (k₁ * (+ 定₀)))))
                  ≡ (- ((q * (lt * (+ 奇₀))) + (q * (k₁ * (+ 定₀)))))
          step₄a = sym (neg-distrib-+ (q * (lt * (+ 奇₀))) (q * (k₁ * (+ 定₀))))

          -- Step 4b: 提取公因子 q (*-distribˡ-+ 反向)
          -- q*(lt*奇₀) + q*(k₁*定₀) → q*(lt*奇₀ + k₁*定₀)
          step₄b : (q * (lt * (+ 奇₀))) + (q * (k₁ * (+ 定₀)))
                  ≡ q * (lt * (+ 奇₀) + k₁ * (+ 定₀))
          step₄b = sym (*-distribˡ-+ q (lt * (+ 奇₀)) (k₁ * (+ 定₀)))

          -- 组装 Step 3+4
          step₃₄ : (lb * (+ 奇₀) + (- (q * (lt * (+ 奇₀))))) + (k₂ * (+ 定₀) + (- (q * (k₁ * (+ 定₀)))))
                 ≡ (lb * (+ 奇₀) + k₂ * (+ 定₀)) + (- (q * (lt * (+ 奇₀) + k₁ * (+ 定₀))))
          step₃₄ = trans step₃
                         (trans (cong (λ x → (lb * (+ 奇₀) + k₂ * (+ 定₀)) + x) step₄a)
                                (cong (λ x → (lb * (+ 奇₀) + k₂ * (+ 定₀)) + (- x)) step₄b))

      in trans step₁ (trans step₂ step₃₄)

    -- Step 2：代入不变量（inv-prev 替换第一项，inv-cur 替换 -q* 里的第二项）
    -- Step 3：用 div-rel 的反转（r ≡ rb - q×rt）直接匹配
    proof : (lb + (- (q * lt))) * (+ 奇₀) + (k₂ + (- (q * k₁))) * (+ 定₀) ≡ + r
    proof = trans rearranged
                   (trans (cong₂ (λ u v → u + (- (q * v))) inv-prev inv-cur)
                          (sym div-rel))

--------------------------------------------------------------------------------
-- §3. terminate-correct——恒等映射（✅ 完成证明）
--------------------------------------------------------------------------------

-- 乘率性质（mod 关系形式）：lt×奇₀ = 1 + k×定₀
-- 这与 Bezout 关系 lt×奇₀ + k'×定₀ = 1 等价（取 k = -k'）
terminate-correct : ∀ (奇₀ 定₀ : ℕ) (lt : ℤ) →
  Inv 奇₀ 定₀ lt 1 →
  Σ ℤ (λ k → lt * (+ 奇₀) ≡ (+ 1) + k * (+ 定₀))
terminate-correct 奇₀ 定₀ lt (k' , bezout) =
  (- k' , proof)

  where
    -- 从 Bezout 推导 mod 关系（5 步 ℤ 代数）：
    -- lt×奇 ≡ (lt×奇) + 0ℤ                    [sym +-identityʳ]
    --       ≡ (lt×奇) + (k'*定 + -(k'*定))      [cong, sym +-inverseʳ]
    --       ≡ ((lt×奇) + k'*定) + -(k'*定)       [sym +-assoc]
    --       ≡ 1 + -(k'*定)                       [cong, bezout]
    --       ≡ 1 + (-k')*定                       [cong, neg-distribˡ-*]

    proof : lt * (+ 奇₀) ≡ (+ 1) + (- k') * (+ 定₀)
    proof =
      trans (sym (+-identityʳ (lt * (+ 奇₀))))
      -- lt*奇₀ ≡ lt*奇₀ + 0ℤ
      (trans (cong (λ x → (lt * (+ 奇₀)) + x) (sym (+-inverseʳ (k' * (+ 定₀)))))
      -- lt*奇₀ + 0ℤ ≡ lt*奇₀ + (k'*定₀ + (-(k'*定₀)))
      (trans (sym (+-assoc (lt * (+ 奇₀)) (k' * (+ 定₀)) (- (k' * (+ 定₀)))))
      -- ≡ (lt*奇₀ + k'*定₀) + (-(k'*定₀))
      (trans (cong (λ x → x + (- (k' * (+ 定₀)))) bezout)
      -- ≡ 1 + (-(k'*定₀))
      (cong (λ x → (+ 1) + x) (neg-distribˡ-* k' (+ 定₀))))))
      -- ≡ 1 + (-k')*定₀ ✓

--------------------------------------------------------------------------------
-- §4. 完成度
--
--   ✅ step-invariant 签名+witness：编译通过
--   ✅ step-invariant proof 主体（Step 2+3）：编译通过
--   ⚠ step-invariant `rearranged`：唯一 hole（ℤ 分配律+重排 ≈30行）
--   ✅ terminate-correct：恒等映射（完成证明）
--   ✅ init-invariant：在 DayanInvariant.agda 中（完成证明）
--
--   数学证明100%完成——Agda 项只差 rearranged 的机械展开。
--------------------------------------------------------------------------------
