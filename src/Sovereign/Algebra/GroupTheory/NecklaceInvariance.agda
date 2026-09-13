{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.NecklaceInvariance
--
-- 块 6 应用：**项链计数与编码/旋转方向无关**。
--
-- 块 5（BurnsideNecklace.agda）的模块头明写了一条诚实边界：
--   「rot 的『颜色语义』是本模块选定的一种编码（低位 = 第 0 珠）；
--     换编码得同构的作用，本模块不证编码无关性。」
-- 本模块把它补上。
--
-- 做法：定义**反向旋转**作用
--       C4-necklace-inv：  g · x = rot³·ᵗᵒℕ ᵍ x = act (inv₄ g) x
-- （inv₄ g = 3g 是 C₄ 中 g 的逆），再用 **bit-reversal** rev（把 4-bit 串左右翻）
-- 把两个作用证成同构：
--       rev (rot x)  ≡ rot⁻¹ (rev x)          （rev-rot）
--       rev (rot⁻¹ x) ≡ rot (rev x)           （rev-roti）
-- 于是 rev 是 C4-necklace → C4-necklace-inv 的等变双射，由 §1 的同构不变性得
--       numOrbitsOf C4 C4-necklace-inv ≡ numOrbitsOf C4 C4-necklace
--
-- 意义：块 5 算出的 **6** 不再依赖「往哪个方向转」「低位算第几珠」这类编码选择。
--
-- 核心原则：
--   1. **不穷举 256**：rev-act / back-act 只按 g 分 4 个 case（旋转是 rot 的迭代），
--      每个 case 归约到两个 16-case 引理 rev-rot / rev-roti 与 rot⁴
--   2. inv₄-hom（inv₄ 是群同态，16 case refl）是 ·-⊙ 的全部内容 ——
--      C₄ 交换，故 (g+h)⁻¹ = g⁻¹ + h⁻¹ 无需 inv-⊙ 反序引理
--   3. rev-inj 由 rev-invol（对合）导出，不另做 16 case
--   4. 0 postulate / 0 hole；无 funExt；不引 Choice
--
-- 诚实边界：
--   只证了「正向旋转作用 ≅ 反向旋转作用」这一对编码；一般「任意编码」的无关性
--   需要先把「编码」形式化成 G-集同构类（本模块不做）。
--   #orbits 相等是结论；本模块不证 p ≡ q（两者同为 16，但那不是本定理的内容）。
--
-- 包含：roti / inv₄ / inv₄-hom / C4-necklace-inv
--       rev / rev-invol / rev-inj / rev-rot / rev-roti
--       rev-act / back-act / necklace-direction-free /
--       necklace-inv-numOrbits / necklace-encoding-free

module Sovereign.Algebra.GroupTheory.NecklaceInvariance where

open import Data.Nat using (ℕ; _+_; _*_; _%_; _/_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup; C4; _+4_)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)
open import Sovereign.Algebra.GroupTheory.BurnsideMain using (numOrbitsOf)
open import Sovereign.Algebra.GroupTheory.BurnsideNecklace
  using (f16; rot; rot⁴; act; C4-necklace)
open import Sovereign.Algebra.GroupTheory.ActionIsomorphism using (action-iso-invariant)

--------------------------------------------------------------------------------
-- §1. 反向旋转作用
--------------------------------------------------------------------------------

-- rot 的逆 = rot³（rot 是 4 阶置换）
roti : Fin 16 → Fin 16
roti x = rot (rot (rot x))

-- C₄ 中的逆元：inv₄ g = 3g = (g +4 g) +4 g
inv₄ : Fin 4 → Fin 4
inv₄ g = (g +4 g) +4 g

-- inv₄ 是群同态（16 case refl ≤ 27）；C₄ 交换故不需要反序引理
inv₄-hom : ∀ g h → inv₄ (g +4 h) ≡ inv₄ g +4 inv₄ h
inv₄-hom (fzero) (fzero) = refl
inv₄-hom (fzero) (fsuc (fzero)) = refl
inv₄-hom (fzero) (fsuc (fsuc (fzero))) = refl
inv₄-hom (fzero) (fsuc (fsuc (fsuc (fzero)))) = refl
inv₄-hom (fsuc (fzero)) (fzero) = refl
inv₄-hom (fsuc (fzero)) (fsuc (fzero)) = refl
inv₄-hom (fsuc (fzero)) (fsuc (fsuc (fzero))) = refl
inv₄-hom (fsuc (fzero)) (fsuc (fsuc (fsuc (fzero)))) = refl
inv₄-hom (fsuc (fsuc (fzero))) (fzero) = refl
inv₄-hom (fsuc (fsuc (fzero))) (fsuc (fzero)) = refl
inv₄-hom (fsuc (fsuc (fzero))) (fsuc (fsuc (fzero))) = refl
inv₄-hom (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fzero)))) = refl
inv₄-hom (fsuc (fsuc (fsuc (fzero)))) (fzero) = refl
inv₄-hom (fsuc (fsuc (fsuc (fzero)))) (fsuc (fzero)) = refl
inv₄-hom (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fzero))) = refl
inv₄-hom (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fzero)))) = refl

C4-necklace-inv : Action C4 (Fin 16)
C4-necklace-inv = record
  { _·_ = λ g x → act (inv₄ g) x
  ; ·-ε = λ x → refl
  ; ·-⊙ = λ g h x → trans (cong (λ z → act z x) (inv₄-hom g h))
                           (Action.·-⊙ C4-necklace (inv₄ g) (inv₄ h) x)
  }

--------------------------------------------------------------------------------
-- §2. bit-reversal：把旋转共轭到反向旋转
--------------------------------------------------------------------------------

-- 4-bit 串左右翻（第 i 位搬到第 3-i 位）
rev : Fin 16 → Fin 16
rev n = f16 (toℕ n % 2 * 8
             + (toℕ n / 2 % 2) * 4
             + (toℕ n / 4 % 2) * 2
             + (toℕ n / 8 % 2))

rev-invol : ∀ x → rev (rev x) ≡ x
rev-invol (fzero) = refl
rev-invol (fsuc (fzero)) = refl
rev-invol (fsuc (fsuc (fzero))) = refl
rev-invol (fsuc (fsuc (fsuc (fzero)))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fzero))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) = refl
rev-invol (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) = refl

-- 对合 ⟹ 单射（不必另做 16 case）
rev-inj : Injective _≡_ _≡_ rev
rev-inj {x} {y} e = trans (sym (rev-invol x)) (trans (cong rev e) (rev-invol y))

-- rev ∘ rot ≡ rot⁻¹ ∘ rev
rev-rot : ∀ x → rev (rot x) ≡ roti (rev x)
rev-rot (fzero) = refl
rev-rot (fsuc (fzero)) = refl
rev-rot (fsuc (fsuc (fzero))) = refl
rev-rot (fsuc (fsuc (fsuc (fzero)))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fzero))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) = refl
rev-rot (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) = refl

-- rev ∘ rot⁻¹ ≡ rot ∘ rev（由 rev-rot 在两端的复合导出）
rev-roti : ∀ x → rev (roti x) ≡ rot (rev x)
rev-roti (fzero) = refl
rev-roti (fsuc (fzero)) = refl
rev-roti (fsuc (fsuc (fzero))) = refl
rev-roti (fsuc (fsuc (fsuc (fzero)))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fzero))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) = refl
rev-roti (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) = refl

--------------------------------------------------------------------------------
-- §3. 两个作用同构（只按 g 分 4 个 case）
--------------------------------------------------------------------------------

-- rev (act g x) ≡ act (inv₄ g) (rev x)
rev-act : ∀ g x → rev (act g x) ≡ act (inv₄ g) (rev x)
rev-act fzero x = refl
rev-act (fsuc fzero) x = rev-rot x
rev-act (fsuc (fsuc fzero)) x =
  trans (trans (rev-rot (rot x)) (cong roti (rev-rot x)))
        (rot⁴ (rot (rot (rev x))))
rev-act (fsuc (fsuc (fsuc fzero))) x = rev-roti x

-- 反向：rev (act (inv₄ h) y) ≡ act h (rev y)
back-act : ∀ h y → rev (act (inv₄ h) y) ≡ act h (rev y)
back-act fzero y = refl
back-act (fsuc fzero) y = rev-roti y
back-act (fsuc (fsuc fzero)) y =
  trans (trans (rev-rot (rot y)) (cong roti (rev-rot y)))
        (rot⁴ (rot (rot (rev y))))
back-act (fsuc (fsuc (fsuc fzero))) y = rev-rot y

--------------------------------------------------------------------------------
-- §4. 对抗验证：具体点 refl 交叉比对
--------------------------------------------------------------------------------

-- ① 两个作用同构 ⟹ 同一个 #orbits（定理实例）
necklace-direction-free : numOrbitsOf C4 C4-necklace ≡ numOrbitsOf C4 C4-necklace-inv
necklace-direction-free =
  action-iso-invariant C4 C4-necklace C4-necklace-inv
    rev rev-inj rev-act rev rev-inj back-act

-- ② 反向编码**独立**算出 6（不是靠定理推出来的）
necklace-inv-numOrbits : numOrbitsOf C4 C4-necklace-inv ≡ 6
necklace-inv-numOrbits = refl

-- ③ 块 5 的诚实边界闭合：项链数与旋转方向（编码）无关，两者都是 6
necklace-encoding-free : numOrbitsOf C4 C4-necklace-inv ≡ numOrbitsOf C4 C4-necklace
necklace-encoding-free = sym necklace-direction-free

-- 注：不再重复声明「反向编码 ≡ 6」——那与 necklace-inv-numOrbits 是同一命题，
-- 而每个这样的 refl 都要跑一次完整的 orbRep 最小元搜索（实测很贵，见 memory 的编译热点记录）。
