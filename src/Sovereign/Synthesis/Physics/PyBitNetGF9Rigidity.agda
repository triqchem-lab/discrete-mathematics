{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.PyBitNetGF9Rigidity
-- 修复路径的形式化：把 Tryte 的 6 trits 按两位一组重解释为 3 个 GF(9) 元素后，
-- Frobenius σ(ψ)=ψ³ 变成**阶 2 的非平凡映射**，满足八要素之⑦「刚性」。
--
-- 背景（见 pyBitNet 的 docs/plan/T6-八要素检查与修复报告-2026-10-23.md 第三节）：
--   pyBitNet 现状：prototype 取值 {0,1,2} = GF(3) ⇒ σ(x)=x³ 是**恒等** ⇒ 刚性平凡 ✗
--   修复路径：Tryte = 6 trits = 729 态 = 9³ ⇒ 两位一组 → 3 个 GF(9) 元素
--            ⇒ σ 在 GF(9) 上非平凡（阶 2）✓
--
-- GF(9) = GF(3)[i]/(i² + 1)，i² = −1 = 2 (mod 3)
-- 乘法：(a+b i)(c+d i) = (ac + 2bd) + (ad + bc) i
-- σ(x) = x³
module Sovereign.Synthesis.Physics.PyBitNetGF9Rigidity where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- 一、GF(9) 的载体（9 个元素，按 a + b·i 命名 g⟨a⟩⟨b⟩）
--------------------------------------------------------------------------------
data GF9 : Set where
  g00 g10 g20 : GF9          -- 0, 1, 2
  g01 g11 g21 : GF9          -- i, 1+i, 2+i
  g02 g12 g22 : GF9          -- 2i, 1+2i, 2+2i

--------------------------------------------------------------------------------
-- 二、Frobenius σ(x) = x³（逐例表）
--------------------------------------------------------------------------------
-- 不动点恰为 GF(3) 的像 = {0, 1, 2}（Frobenius 的不动域）
-- 其余 6 个元素两两互换
σ : GF9 → GF9
σ g00 = g00
σ g10 = g10
σ g20 = g20
σ g01 = g02
σ g02 = g01
σ g11 = g12
σ g12 = g11
σ g21 = g22
σ g22 = g21

--------------------------------------------------------------------------------
-- 三、σ 的阶为 2（σ ∘ σ = id）
--------------------------------------------------------------------------------
σ-order-2 : ∀ x → σ (σ x) ≡ x
σ-order-2 g00 = refl
σ-order-2 g10 = refl
σ-order-2 g20 = refl
σ-order-2 g01 = refl
σ-order-2 g02 = refl
σ-order-2 g11 = refl
σ-order-2 g12 = refl
σ-order-2 g21 = refl
σ-order-2 g22 = refl

--------------------------------------------------------------------------------
-- 四、σ 非平凡
--------------------------------------------------------------------------------
g02≢g01 : g02 ≢ g01
g02≢g01 ()

-- 见证：α = i = g01，σ(α) = α³ = −α = g02 ≠ g01
σ-nontrivial : Σ GF9 (λ x → σ x ≢ x)
σ-nontrivial = g01 , g02≢g01

--------------------------------------------------------------------------------
-- 五、相位：GF(9) 上乘 α = i，阶恰为 4（修复八要素之④）
--------------------------------------------------------------------------------
-- α = i = g01；α·(a + b i) = (0 + 1·i)(a + b i) = (2b) + (a) i
-- 作用：0 不动；非零 8 元分成两个 4-循环
--   g10 → g01 → g20 → g02 → g10
--   g11 → g21 → g22 → g12 → g11
α : GF9
α = g01

phase : GF9 → GF9
phase g00 = g00
phase g10 = g01
phase g01 = g20
phase g20 = g02
phase g02 = g10
phase g11 = g21
phase g21 = g22
phase g22 = g12
phase g12 = g11

-- 迭代算子
iterate : {A : Set} → (A → A) → ℕ → A → A
iterate f zero    x = x
iterate f (suc n) x = f (iterate f n x)

-- ① α⁴ = 1：四步回位（9 例 refl）
phase-order-4 : ∀ x → iterate phase 4 x ≡ x
phase-order-4 g00 = refl
phase-order-4 g10 = refl
phase-order-4 g20 = refl
phase-order-4 g01 = refl
phase-order-4 g02 = refl
phase-order-4 g11 = refl
phase-order-4 g12 = refl
phase-order-4 g21 = refl
phase-order-4 g22 = refl

-- ② α² ≠ 1：**相位不可约**的关键 —— C₄ 不能商成 C₂
--    若 C₄ → C₂ 是忠实商，则 α² 必与 1 同类；此处 α² 把 g10 送到 g20 ≠ g10。
phase²-nontrivial : Σ GF9 (λ x → iterate phase 2 x ≢ x)
phase²-nontrivial = g10 , λ ()

-- ③ α ≢ 1（相位本身非平凡）
phase-nontrivial : Σ GF9 (λ x → phase x ≢ x)
phase-nontrivial = g10 , λ ()

--------------------------------------------------------------------------------
-- 六、修复路径的算术依据：6 trits = 9³
--------------------------------------------------------------------------------
-- 两次两位一组分组：GF(3)⁶ ≅ (GF(3)²)³ ≅ GF(9)³
tryte-is-gf9-cubed : 9 * 9 * 9 ≡ 729
tryte-is-gf9-cubed = refl

--------------------------------------------------------------------------------
-- 七、结论（文字）
--------------------------------------------------------------------------------
-- ① σ 阶 2（σ-order-2）且非平凡（σ-nontrivial）⇒ 八要素之⑦ 可满足。
-- ② 而当前的 pyBitNet 把 6 trits 当 6 个独立 GF(3) 值（gf3_embedding.py：
--    float32 + STE 三值化），σ 在其上退化为恒等 ⇒ ⑦ 不满足。
-- ③ 修复 = 做一次分组重解释，不改存储格式（6 trits 仍是 6 trits，
--    只是**解释**成 3 个 GF(9) 元素）。
-- ④ 相位（之④）同样由 GF(9) 承载：α = i，`phase-order-4` 证阶 4，
--    `phase²-nontrivial` 证 α² ≢ id ⇒ **C₄ → C₂ 的商非忠实**（相位不可约）。
-- ⑤ ⚠ 本模块只证「GF(9) 上 σ 的阶/非平凡性」与「α 的阶/非平凡性」；
--    **未证**该分组对训练收敛性无副作用（需实测）。
