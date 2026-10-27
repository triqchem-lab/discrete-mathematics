{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SL23Conjugacy
--
-- **`classOf2A4` 恰好是共轭类划分**（补齐「共轭 ⇒ 同类」的反向）
--
-- `SL23Inverse.classConj` 已给一个方向：`classOf2A4 (h·x·h⁻¹) ≡ classOf2A4 x`。
-- 本文件证反向：**同类 ⇒ 共轭**，即同类里任意两个元素 x, y 都存在 h 使
--   y ≡ (h ⊗ x) ⊗ invSL h
-- 于是 `classOf2A4` 不再只是"共轭不变函数"，而是真正的共轭类划分。
--
-- 证明组织（避免 24×24 三表铺开）：
--   ① 每个类写成成员表 `c0L … c6L`，定义成员关系 `_∈_`；
--   ② `classMembers`：每个元素在自己类的表里（24 案，位置由表序定）；
--   ③ `orbit-gK`：固定 x = gK，对**成员表里的每个位置**给出共轭元 h（共 102 案，
--      位置模式 `here / there here / …` 把 y 钉死，故每案只需 `refl`）；
--   ④ `conj-witness`：用前提 `classOf x ≡ classOf y` 把"y 在自己类里"搬到
--      "y 在 x 的类里"，再交给 ③。
--   好处：**不同类的 474 种组合根本不需要出现**——成员关系直接排除了它们
--   （对比之下，逐对铺开要 576 案，其中 474 案是空模式）。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SL23Conjugacy where

open import Data.List using (List; _∷_; [])
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
open import Sovereign.Synthesis.A4.SL23Inverse using (invSL; classConj)
open import Sovereign.Synthesis.A4.CharTable2A4
  using (Cls; κ0; κ1; κ2; κ3; κ4; κ5; κ6; classOf2A4)

--------------------------------------------------------------------------------
-- ① 成员关系与七个类的成员表
--
--   表序 = `classOf2A4` 的计算序（g0..g23 中首次出现）：
--     c0 = [g0,g3,g10,g14,g19,g23]（6）  c1 = [g1,g11,g17,g18]（4）
--     c2 = [g2,g8,g9,g20]（4）            c3 = [g4,g13,g16,g21]（4）
--     c4 = [g5,g7,g12,g22]（4）           c5 = [g6]（1）   c6 = [g15]（1）
--------------------------------------------------------------------------------

infix 4 _∈_

data _∈_ (a : SL23) : List SL23 → Set where
  here  : ∀ {xs} → a ∈ a ∷ xs
  there : ∀ {b xs} → a ∈ xs → a ∈ b ∷ xs

c0L c1L c2L c3L c4L c5L c6L : List SL23
c0L = g0 ∷ g3 ∷ g10 ∷ g14 ∷ g19 ∷ g23 ∷ []
c1L = g1 ∷ g11 ∷ g17 ∷ g18 ∷ []
c2L = g2 ∷ g8 ∷ g9 ∷ g20 ∷ []
c3L = g4 ∷ g13 ∷ g16 ∷ g21 ∷ []
c4L = g5 ∷ g7 ∷ g12 ∷ g22 ∷ []
c5L = g6 ∷ []
c6L = g15 ∷ []

membersOf : Cls → List SL23
membersOf κ0 = c0L
membersOf κ1 = c1L
membersOf κ2 = c2L
membersOf κ3 = c3L
membersOf κ4 = c4L
membersOf κ5 = c5L
membersOf κ6 = c6L

--------------------------------------------------------------------------------
-- ② 每个元素在自己类的成员表里（24 案；案数 = 该元素在表内的位置）
--------------------------------------------------------------------------------

classMembers : ∀ (x : SL23) → x ∈ membersOf (classOf2A4 x)
classMembers g0  = here
classMembers g1  = here
classMembers g2  = here
classMembers g3  = there here
classMembers g4  = here
classMembers g5  = here
classMembers g6  = here
classMembers g7  = there here
classMembers g8  = there here
classMembers g9  = there (there here)
classMembers g10 = there (there here)
classMembers g11 = there here
classMembers g12 = there (there here)
classMembers g13 = there here
classMembers g14 = there (there (there here))
classMembers g15 = here
classMembers g16 = there (there here)
classMembers g17 = there (there here)
classMembers g18 = there (there (there here))
classMembers g19 = there (there (there (there here)))
classMembers g20 = there (there (there here))
classMembers g21 = there (there (there here))
classMembers g22 = there (there (there here))
classMembers g23 = there (there (there (there (there here))))

--------------------------------------------------------------------------------
-- ③ 每个 x：同类元素都能由某个 h 共轭得到（共 102 案）
--
--    位置模式把 y 钉死，故每案只需给出 h 并 `refl` 检查
--    （(h·x)·h⁻¹ 在表上就是 y）。
--------------------------------------------------------------------------------

orbit-g0 : ∀ {y : SL23} → y ∈ c0L → Σ SL23 (λ h → y ≡ (h ⊗ g0) ⊗ invSL h)
orbit-g0 here                            = g0 , refl
orbit-g0 (there here)                    = g10 , refl
orbit-g0 (there (there here))            = g2 , refl
orbit-g0 (there (there (there here)))    = g11 , refl
orbit-g0 (there (there (there (there here)))) = g1 , refl
orbit-g0 (there (there (there (there (there here))))) = g9 , refl

orbit-g1 : ∀ {y : SL23} → y ∈ c1L → Σ SL23 (λ h → y ≡ (h ⊗ g1) ⊗ invSL h)
orbit-g1 here                            = g1 , refl
orbit-g1 (there here)                    = g0 , refl
orbit-g1 (there (there here))            = g9 , refl
orbit-g1 (there (there (there here)))    = g2 , refl

orbit-g2 : ∀ {y : SL23} → y ∈ c2L → Σ SL23 (λ h → y ≡ (h ⊗ g2) ⊗ invSL h)
orbit-g2 here                            = g2 , refl
orbit-g2 (there here)                    = g12 , refl
orbit-g2 (there (there here))            = g1 , refl
orbit-g2 (there (there (there here)))    = g0 , refl

orbit-g3 : ∀ {y : SL23} → y ∈ c0L → Σ SL23 (λ h → y ≡ (h ⊗ g3) ⊗ invSL h)
orbit-g3 here                            = g10 , refl
orbit-g3 (there here)                    = g0 , refl
orbit-g3 (there (there here))            = g9 , refl
orbit-g3 (there (there (there here)))    = g1 , refl
orbit-g3 (there (there (there (there here)))) = g11 , refl
orbit-g3 (there (there (there (there (there here))))) = g2 , refl

orbit-g4 : ∀ {y : SL23} → y ∈ c3L → Σ SL23 (λ h → y ≡ (h ⊗ g4) ⊗ invSL h)
orbit-g4 here                            = g2 , refl
orbit-g4 (there here)                    = g0 , refl
orbit-g4 (there (there here))            = g12 , refl
orbit-g4 (there (there (there here)))    = g1 , refl

orbit-g5 : ∀ {y : SL23} → y ∈ c4L → Σ SL23 (λ h → y ≡ (h ⊗ g5) ⊗ invSL h)
orbit-g5 here                            = g1 , refl
orbit-g5 (there here)                    = g9 , refl
orbit-g5 (there (there here))            = g2 , refl
orbit-g5 (there (there (there here)))    = g0 , refl

orbit-g6 : ∀ {y : SL23} → y ∈ c5L → Σ SL23 (λ h → y ≡ (h ⊗ g6) ⊗ invSL h)
orbit-g6 here                            = g0 , refl

orbit-g7 : ∀ {y : SL23} → y ∈ c4L → Σ SL23 (λ h → y ≡ (h ⊗ g7) ⊗ invSL h)
orbit-g7 here                            = g2 , refl
orbit-g7 (there here)                    = g6 , refl
orbit-g7 (there (there here))            = g0 , refl
orbit-g7 (there (there (there here)))    = g1 , refl

orbit-g8 : ∀ {y : SL23} → y ∈ c2L → Σ SL23 (λ h → y ≡ (h ⊗ g8) ⊗ invSL h)
orbit-g8 here                            = g1 , refl
orbit-g8 (there here)                    = g6 , refl
orbit-g8 (there (there here))            = g0 , refl
orbit-g8 (there (there (there here)))    = g2 , refl

orbit-g9 : ∀ {y : SL23} → y ∈ c2L → Σ SL23 (λ h → y ≡ (h ⊗ g9) ⊗ invSL h)
orbit-g9 here                            = g7 , refl
orbit-g9 (there here)                    = g0 , refl
orbit-g9 (there (there here))            = g6 , refl
orbit-g9 (there (there (there here)))    = g8 , refl

orbit-g10 : ∀ {y : SL23} → y ∈ c0L → Σ SL23 (λ h → y ≡ (h ⊗ g10) ⊗ invSL h)
orbit-g10 here                            = g7 , refl
orbit-g10 (there here)                    = g1 , refl
orbit-g10 (there (there here))            = g6 , refl
orbit-g10 (there (there (there here)))    = g2 , refl
orbit-g10 (there (there (there (there here)))) = g8 , refl
orbit-g10 (there (there (there (there (there here))))) = g0 , refl

orbit-g11 : ∀ {y : SL23} → y ∈ c1L → Σ SL23 (λ h → y ≡ (h ⊗ g11) ⊗ invSL h)
orbit-g11 here                            = g0 , refl
orbit-g11 (there here)                    = g2 , refl
orbit-g11 (there (there here))            = g12 , refl
orbit-g11 (there (there (there here)))    = g1 , refl

orbit-g12 : ∀ {y : SL23} → y ∈ c4L → Σ SL23 (λ h → y ≡ (h ⊗ g12) ⊗ invSL h)
orbit-g12 here                            = g8 , refl
orbit-g12 (there here)                    = g0 , refl
orbit-g12 (there (there here))            = g6 , refl
orbit-g12 (there (there (there here)))    = g7 , refl

orbit-g13 : ∀ {y : SL23} → y ∈ c3L → Σ SL23 (λ h → y ≡ (h ⊗ g13) ⊗ invSL h)
orbit-g13 here                            = g0 , refl
orbit-g13 (there here)                    = g1 , refl
orbit-g13 (there (there here))            = g9 , refl
orbit-g13 (there (there (there here)))    = g2 , refl

orbit-g14 : ∀ {y : SL23} → y ∈ c0L → Σ SL23 (λ h → y ≡ (h ⊗ g14) ⊗ invSL h)
orbit-g14 here                            = g2 , refl
orbit-g14 (there here)                    = g8 , refl
orbit-g14 (there (there here))            = g1 , refl
orbit-g14 (there (there (there here)))    = g6 , refl
orbit-g14 (there (there (there (there here)))) = g0 , refl
orbit-g14 (there (there (there (there (there here))))) = g7 , refl

orbit-g15 : ∀ {y : SL23} → y ∈ c6L → Σ SL23 (λ h → y ≡ (h ⊗ g15) ⊗ invSL h)
orbit-g15 here                            = g0 , refl

orbit-g16 : ∀ {y : SL23} → y ∈ c3L → Σ SL23 (λ h → y ≡ (h ⊗ g16) ⊗ invSL h)
orbit-g16 here                            = g1 , refl
orbit-g16 (there here)                    = g2 , refl
orbit-g16 (there (there here))            = g6 , refl
orbit-g16 (there (there (there here)))    = g0 , refl

orbit-g17 : ∀ {y : SL23} → y ∈ c1L → Σ SL23 (λ h → y ≡ (h ⊗ g17) ⊗ invSL h)
orbit-g17 here                            = g2 , refl
orbit-g17 (there here)                    = g1 , refl
orbit-g17 (there (there here))            = g6 , refl
orbit-g17 (there (there (there here)))    = g0 , refl

orbit-g18 : ∀ {y : SL23} → y ∈ c1L → Σ SL23 (λ h → y ≡ (h ⊗ g18) ⊗ invSL h)
orbit-g18 here                            = g8 , refl
orbit-g18 (there here)                    = g7 , refl
orbit-g18 (there (there here))            = g0 , refl
orbit-g18 (there (there (there here)))    = g6 , refl

orbit-g19 : ∀ {y : SL23} → y ∈ c0L → Σ SL23 (λ h → y ≡ (h ⊗ g19) ⊗ invSL h)
orbit-g19 here                            = g8 , refl
orbit-g19 (there here)                    = g2 , refl
orbit-g19 (there (there here))            = g7 , refl
orbit-g19 (there (there (there here)))    = g0 , refl
orbit-g19 (there (there (there (there here)))) = g6 , refl
orbit-g19 (there (there (there (there (there here))))) = g1 , refl

orbit-g20 : ∀ {y : SL23} → y ∈ c2L → Σ SL23 (λ h → y ≡ (h ⊗ g20) ⊗ invSL h)
orbit-g20 here                            = g0 , refl
orbit-g20 (there here)                    = g9 , refl
orbit-g20 (there (there here))            = g2 , refl
orbit-g20 (there (there (there here)))    = g1 , refl

orbit-g21 : ∀ {y : SL23} → y ∈ c3L → Σ SL23 (λ h → y ≡ (h ⊗ g21) ⊗ invSL h)
orbit-g21 here                            = g7 , refl
orbit-g21 (there here)                    = g8 , refl
orbit-g21 (there (there here))            = g0 , refl
orbit-g21 (there (there (there here)))    = g6 , refl

orbit-g22 : ∀ {y : SL23} → y ∈ c4L → Σ SL23 (λ h → y ≡ (h ⊗ g22) ⊗ invSL h)
orbit-g22 here                            = g0 , refl
orbit-g22 (there here)                    = g12 , refl
orbit-g22 (there (there here))            = g1 , refl
orbit-g22 (there (there (there here)))    = g2 , refl

orbit-g23 : ∀ {y : SL23} → y ∈ c0L → Σ SL23 (λ h → y ≡ (h ⊗ g23) ⊗ invSL h)
orbit-g23 here                            = g1 , refl
orbit-g23 (there here)                    = g7 , refl
orbit-g23 (there (there here))            = g0 , refl
orbit-g23 (there (there (there here)))    = g8 , refl
orbit-g23 (there (there (there (there here)))) = g2 , refl
orbit-g23 (there (there (there (there (there here))))) = g6 , refl

--------------------------------------------------------------------------------
-- ④ 主命题：同类 ⇒ 共轭
--
--    前提 `classOf2A4 x ≡ classOf2A4 y` 把"y 在自己类里"搬到"y 在 x 的类里"，
--    剩下交给 ③。**不同类的组合在此结构下根本不出现**。
--------------------------------------------------------------------------------

conj-witness : ∀ (x y : SL23) → classOf2A4 x ≡ classOf2A4 y
             → Σ SL23 (λ h → y ≡ (h ⊗ x) ⊗ invSL h)
conj-witness g0  y e = orbit-g0  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g1  y e = orbit-g1  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g2  y e = orbit-g2  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g3  y e = orbit-g3  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g4  y e = orbit-g4  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g5  y e = orbit-g5  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g6  y e = orbit-g6  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g7  y e = orbit-g7  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g8  y e = orbit-g8  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g9  y e = orbit-g9  (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g10 y e = orbit-g10 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g11 y e = orbit-g11 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g12 y e = orbit-g12 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g13 y e = orbit-g13 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g14 y e = orbit-g14 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g15 y e = orbit-g15 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g16 y e = orbit-g16 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g17 y e = orbit-g17 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g18 y e = orbit-g18 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g19 y e = orbit-g19 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g20 y e = orbit-g20 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g21 y e = orbit-g21 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g22 y e = orbit-g22 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))
conj-witness g23 y e = orbit-g23 (subst (λ k → y ∈ membersOf k) (sym e) (classMembers y))

--------------------------------------------------------------------------------
-- ⑤ 反向方向（已有 `classConj` 的直接改写）：共轭 ⇒ 同类
--------------------------------------------------------------------------------

conj→class : ∀ (x y : SL23)
           → Σ SL23 (λ h → y ≡ (h ⊗ x) ⊗ invSL h)
           → classOf2A4 x ≡ classOf2A4 y
conj→class x y (h , e) = trans (sym (classConj x h)) (cong classOf2A4 (sym e))

--------------------------------------------------------------------------------
-- ⑥ 结论：两个方向都成立 ⇒ classOf2A4 是共轭类划分
--
--    注意到反向不用枚举：`classConj` 已经是「共轭 ⇒ 同类」，
--    本文件新增的是正向（同类 ⇒ 共轭），故两方向的合成即"类 = 共轭轨道"。
--------------------------------------------------------------------------------

class-is-conjugacy : ∀ (x y : SL23)
  → ((classOf2A4 x ≡ classOf2A4 y) → Σ SL23 (λ h → y ≡ (h ⊗ x) ⊗ invSL h))
  × ((Σ SL23 (λ h → y ≡ (h ⊗ x) ⊗ invSL h)) → (classOf2A4 x ≡ classOf2A4 y))
class-is-conjugacy x y = conj-witness x y , conj→class x y
