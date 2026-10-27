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
  using (mulZω-assoc; mulZω-comm; mulZω-distribˡ; mulZω-distribʳ; addZω-identityʳ)
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

--------------------------------------------------------------------------------
-- ③ dot-scale：内积对标量线性（注意 dot 的三项形状带一个尾零）
--
--   dot 的定义是 addZω (x·y) (dot xs ys)，dot [] [] = zeroZω，
--   所以三项的展开是  a + (b + (d + 0))  —— 末尾那个 0 不能省；
--   这也是先前"符号中间形对不上"的真正原因（不是 ℤ 的符号括号）。
--------------------------------------------------------------------------------

dot-scale : ∀ (r v : Vec3) (c : Zω)
          → dot r (map (mulZω c) v) ≡ mulZω c (dot r v)
dot-scale (a ∷ b ∷ d ∷ []) (x ∷ y ∷ z ∷ []) c = begin
    addZω (mulZω a (mulZω c x))
          (addZω (mulZω b (mulZω c y)) (addZω (mulZω d (mulZω c z)) zeroZω))
  ≡⟨ cong (λ t → addZω (mulZω a (mulZω c x))
                       (addZω (mulZω b (mulZω c y)) t))
          (addZω-identityʳ (mulZω d (mulZω c z))) ⟩
    addZω (mulZω a (mulZω c x))
          (addZω (mulZω b (mulZω c y)) (mulZω d (mulZω c z)))
  ≡⟨ cong (λ t → addZω (mulZω a (mulZω c x))
                       (addZω (mulZω b (mulZω c y)) t))
          (interchange d c z) ⟩
    addZω (mulZω a (mulZω c x))
          (addZω (mulZω b (mulZω c y)) (mulZω c (mulZω d z)))
  ≡⟨ cong (λ t → addZω (mulZω a (mulZω c x))
                       (addZω t (mulZω c (mulZω d z))))
          (interchange b c y) ⟩
    addZω (mulZω a (mulZω c x))
          (addZω (mulZω c (mulZω b y)) (mulZω c (mulZω d z)))
  ≡⟨ cong (λ t → addZω t
                       (addZω (mulZω c (mulZω b y)) (mulZω c (mulZω d z))))
          (interchange a c x) ⟩
    addZω (mulZω c (mulZω a x))
          (addZω (mulZω c (mulZω b y)) (mulZω c (mulZω d z)))
  ≡⟨ cong (λ t → addZω (mulZω c (mulZω a x)) t)
          (sym (mulZω-distribˡ c (mulZω b y) (mulZω d z))) ⟩
    addZω (mulZω c (mulZω a x))
          (mulZω c (addZω (mulZω b y) (mulZω d z)))
  ≡⟨ sym (mulZω-distribˡ c (mulZω a x) (addZω (mulZω b y) (mulZω d z))) ⟩
    mulZω c (addZω (mulZω a x) (addZω (mulZω b y) (mulZω d z)))
  ≡⟨ sym (cong (mulZω c)
               (cong (λ t → addZω (mulZω a x) (addZω (mulZω b y) t))
                     (addZω-identityʳ (mulZω d z)))) ⟩
    mulZω c (addZω (mulZω a x) (addZω (mulZω b y) (addZω (mulZω d z) zeroZω)))
  ∎

--------------------------------------------------------------------------------
-- ④ 标量可提出矩阵、关键交换引理
--------------------------------------------------------------------------------

mulMV3-scale : ∀ (M : Mat 3 3) (c : Zω) (v : Vec3)
             → mulMV3 M (scaleV3 c v) ≡ scaleV3 c (mulMV3 M v)
mulMV3-scale M c v =
  trans (map-cong (λ row → dot-scale row v c) M)
        (map-∘ (mulZω c) (λ row → dot row v) M)

AB3-form : ∀ (A B : Mat 3 3) (v : Vec3) (c d : Zω)
         → mulMV3 A v ≡ scaleV3 c v
         → mulMV3 B v ≡ scaleV3 d v
         → mulMV3 A (mulMV3 B v) ≡ scaleV3 (mulZω d c) v
AB3-form A B v c d Av Bv =
  trans (cong (mulMV3 A) Bv)
    (trans (mulMV3-scale A d v)
      (trans (cong (scaleV3 d) Av) (scaleV3-assoc d c v)))

BA3-form : ∀ (A B : Mat 3 3) (v : Vec3) (c d : Zω)
         → mulMV3 A v ≡ scaleV3 c v
         → mulMV3 B v ≡ scaleV3 d v
         → mulMV3 B (mulMV3 A v) ≡ scaleV3 (mulZω c d) v
BA3-form A B v c d Av Bv =
  trans (cong (mulMV3 B) Av)
    (trans (mulMV3-scale B c v)
      (trans (cong (scaleV3 c) Bv) (scaleV3-assoc c d v)))

-- | 公共特征向量 ⇒ 两算子交换（3 维）
commute3 : ∀ (A B : Mat 3 3) (v : Vec3) (c d : Zω)
         → mulMV3 A v ≡ scaleV3 c v
         → mulMV3 B v ≡ scaleV3 d v
         → mulMV3 A (mulMV3 B v) ≡ mulMV3 B (mulMV3 A v)
commute3 A B v c d Av Bv =
  trans (AB3-form A B v c d Av Bv)
    (trans (cong (λ t → scaleV3 t v) (mulZω-comm d c))
           (sym (BA3-form A B v c d Av Bv)))

--------------------------------------------------------------------------------
-- ⑤ 3 项求和引理（mulMV3-mulMat 的通用垫脚）
--
--   mulMat 的一行是「列的 3 个内积」，而作用到 v 上要变成「v 的 3 个分量加权」。
--   需要的通用件只有三条：
--     distrib3ʳ : (c₀ ⊕ (c₁ ⊕ c₂))·v ≡ c₀v ⊕ (c₁v ⊕ c₂v)
--     distrib3ˡ : a·(p ⊕ (q ⊕ r))   ≡ ap ⊕ (aq ⊕ ar)
--     row3-action : ((a₀b₀ ⊕ (a₁b₁ ⊕ a₂b₂)))·v ≡ a₀(b₀v) ⊕ (a₁(b₁v) ⊕ a₂(b₂v))
--   第三条 = 第一条 + 三次结合律（(aᵢbᵢ)v ⟶ aᵢ(bᵢv)）。
--------------------------------------------------------------------------------

-- | 三项右分配
distrib3ʳ : ∀ (c₀ c₁ c₂ v : Zω)
          → mulZω (addZω c₀ (addZω c₁ c₂)) v
          ≡ addZω (mulZω c₀ v) (addZω (mulZω c₁ v) (mulZω c₂ v))
distrib3ʳ c₀ c₁ c₂ v =
  trans (mulZω-distribʳ c₀ (addZω c₁ c₂) v)
        (cong (addZω (mulZω c₀ v)) (mulZω-distribʳ c₁ c₂ v))

-- | 三项左分配
distrib3ˡ : ∀ (a p q r : Zω)
          → mulZω a (addZω p (addZω q r))
          ≡ addZω (mulZω a p) (addZω (mulZω a q) (mulZω a r))
distrib3ˡ a p q r =
  trans (mulZω-distribˡ a p (addZω q r))
        (cong (addZω (mulZω a p)) (mulZω-distribˡ a q r))
