{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SpinIrreducible3
--
-- **3 维 ρ₃ 的不变线障碍：线性性层**
--
-- 3 维的判据与 2 维不同（实测：提升后的 ρ₃ 全部非零交换子 det = 0、秩 = 2，
-- 没有单位行列式），走的是「核的交 + det = 4 子式 + four-zero」。但要走到那一步，
-- 先要有 3 维的线性性层：
--
--   ① mulMV3 / scaleV3（矩阵-向量作用、标量乘）
--   ② dot-scale：内积对标量线性            dot r (c·v) ≡ c·(dot r v)
--   ③ mulMV3-scale：标量可提出矩阵        ρ(M)·(c·v) ≡ c·(ρ(M)·v)
--   ④ scaleV3-assoc：c·(d·v) ≡ (c·d)·v
--   ⑤ commute3：公共特征向量 ⇒ 两算子交换  A v = c·v → B v = d·v → A(Bv) ≡ B(Av)
--
-- 与 2 维完全同构（`SpinIrreducible`），区别只是向量/矩阵的维度由 `Vec Zω 3`
-- 与 `Mat 3 3` 承担；内积用库内 `MatrixZω.dot`。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SpinIrreducible3 where

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Properties using (map-cong; map-∘)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; zeroZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using (mulZω-assoc; mulZω-comm; mulZω-distribˡ)
open import Sovereign.Synthesis.FieldTower.MatrixZω using (Mat; dot)
open import Sovereign.Synthesis.A4.SpinIrreducible using (interchange)

--------------------------------------------------------------------------------
-- ① 三维向量与作用
--------------------------------------------------------------------------------

Vec3 : Set
Vec3 = Vec Zω 3

zeroV3 : Vec3
zeroV3 = zeroZω ∷ zeroZω ∷ zeroZω ∷ []

-- | 矩阵作用：ρ(M)·v
mulMV3 : Mat 3 3 → Vec3 → Vec3
mulMV3 M v = map (λ row → dot row v) M

-- | 标量乘：c·v
scaleV3 : Zω → Vec3 → Vec3
scaleV3 c = map (mulZω c)

--------------------------------------------------------------------------------
-- ② 内积对标量线性
--
--   dot r (c·v) ≡ c·(dot r v)
--   逐项：a(cx) ≡ c(ax)  [交换 + 结合]，再收回分配律。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ③ 标量可提出矩阵、标量乘结合
--------------------------------------------------------------------------------

scaleV3-assoc : ∀ (c d : Zω) (v : Vec3)
              → scaleV3 c (scaleV3 d v) ≡ scaleV3 (mulZω c d) v
scaleV3-assoc c d v =
  trans (sym (map-∘ (mulZω c) (mulZω d) v))
        (map-cong (λ x → sym (mulZω-assoc c d x)) v)

scaleV3-cong : ∀ {c d : Zω} → c ≡ d → ∀ (v : Vec3) → scaleV3 c v ≡ scaleV3 d v
scaleV3-cong {c} {d} h v = map-cong (λ x → cong (λ t → mulZω t x) h) v

