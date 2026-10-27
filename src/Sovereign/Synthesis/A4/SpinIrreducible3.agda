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
  using ( mulZω-assoc; mulZω-comm; mulZω-distribˡ; mulZω-distribʳ; mulZω-zeroʳ
        ; addZω-assoc; addZω-identityʳ
        ; add-swap; add-swap4; add-transpose-23 )
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

-- | 一行 × 一列：((a₀b₀ ⊕ (a₁b₁ ⊕ a₂b₂)))·v ≡ a₀(b₀v) ⊕ (a₁(b₁v) ⊕ a₂(b₂v))
--
--   ⚠ 方向：`mulZω-assoc : (x·y)·z ≡ x·(y·z)`，从 (aᵢbᵢ)v 拉成 aᵢ(bᵢv) 要用**正向**，
--   不是 `sym`。先前写成 `sym` 时报的却是"sign ◃ 括号不等"（Agda 把归一化后的
--   ℤ 形态打印出来），极易误认为形状问题——实测 probeC（形状）通过、probeD（方向）失败。
row3-action : ∀ (a₀ a₁ a₂ b₀ b₁ b₂ v : Zω)
            → mulZω (addZω (mulZω a₀ b₀) (addZω (mulZω a₁ b₁) (mulZω a₂ b₂))) v
            ≡ addZω (mulZω a₀ (mulZω b₀ v))
                    (addZω (mulZω a₁ (mulZω b₁ v)) (mulZω a₂ (mulZω b₂ v)))
row3-action a₀ a₁ a₂ b₀ b₁ b₂ v =
  trans (distrib3ʳ (mulZω a₀ b₀) (mulZω a₁ b₁) (mulZω a₂ b₂) v)
    (trans (cong (λ t → addZω t (addZω (mulZω (mulZω a₁ b₁) v)
                                        (mulZω (mulZω a₂ b₂) v)))
                 (mulZω-assoc a₀ b₀ v))
      (trans (cong (λ t → addZω (mulZω a₀ (mulZω b₀ v))
                              (addZω t (mulZω (mulZω a₂ b₂) v)))
                   (mulZω-assoc a₁ b₁ v))
             (cong (λ t → addZω (mulZω a₀ (mulZω b₀ v))
                              (addZω (mulZω a₁ (mulZω b₁ v)) t))
                   (mulZω-assoc a₂ b₂ v))))

--------------------------------------------------------------------------------
-- ⑥ 矩阵乘法与作用相容：ρ(A·B)·v ≡ ρ(A)·(ρ(B)·v)
--
--   `mulMM3` 取**行组合**形式：第 i 行 = aᵢ₀·b₀ ⊕ (aᵢ₁·b₁ ⊕ aᵢ₂·b₂)，其中 bₖ 是 B 的第 k 行。
--   它与「行·列」定义逐条相同（(A·B)ᵢⱼ = Σₖ aᵢₖ·bₖⱼ），但**只**需要 2×3 加法转置
--   （`add-transpose-23`）：第 i 行只依赖 A 的第 i 行，故不会出现 3×3 的整体转置。
--
--   两条分量化前提：
--     dot-scale-left：内积对**第一**个因子线性   dot (c·p) v ≡ c·(dot p v)
--     dot-add      ：内积对第一因子的加法线性   dot (p ⊕ q) v ≡ dot p v ⊕ dot q v
--------------------------------------------------------------------------------

-- | 三分量相等（Vec 的 `cong₂ _∷_` 隐式参数易歧义，用一条专门引理）
vec3-cong : ∀ {a b c a' b' c' : Zω}
          → a ≡ a' → b ≡ b' → c ≡ c'
          → (a ∷ b ∷ c ∷ []) ≡ (a' ∷ b' ∷ c' ∷ [])
vec3-cong refl refl refl = refl

-- | 逐分量相加
addV3 : Vec3 → Vec3 → Vec3
addV3 (a ∷ b ∷ d ∷ []) (x ∷ y ∷ z ∷ []) = addZω a x ∷ addZω b y ∷ addZω d z ∷ []

-- | dot 对**第一**个因子的加法线性（展开到分量）：
--   (p₀⊕q₀)x ⊕ ((p₁⊕q₁)y ⊕ ((p₂⊕q₂)z ⊕ 0))
--     ≡ ((p₀x ⊕ (p₁y ⊕ (p₂z ⊕ 0))) ⊕ (q₀x ⊕ (q₁y ⊕ (q₂z ⊕ 0)))
dot-add3 : ∀ (p₀ p₁ p₂ q₀ q₁ q₂ x y z : Zω)
         → addZω (mulZω (addZω p₀ q₀) x)
                  (addZω (mulZω (addZω p₁ q₁) y)
                         (addZω (mulZω (addZω p₂ q₂) z) zeroZω))
         ≡ addZω (addZω (mulZω p₀ x)
                        (addZω (mulZω p₁ y) (addZω (mulZω p₂ z) zeroZω)))
                  (addZω (mulZω q₀ x)
                         (addZω (mulZω q₁ y) (addZω (mulZω q₂ z) zeroZω)))
dot-add3 p₀ p₁ p₂ q₀ q₁ q₂ x y z = begin
    addZω (mulZω (addZω p₀ q₀) x)
          (addZω (mulZω (addZω p₁ q₁) y) (addZω (mulZω (addZω p₂ q₂) z) zeroZω))
  ≡⟨ cong (λ t → addZω (mulZω (addZω p₀ q₀) x)
                       (addZω (mulZω (addZω p₁ q₁) y) t))
          (addZω-identityʳ (mulZω (addZω p₂ q₂) z)) ⟩
    addZω (mulZω (addZω p₀ q₀) x)
          (addZω (mulZω (addZω p₁ q₁) y) (mulZω (addZω p₂ q₂) z))
  ≡⟨ cong₂ addZω (mulZω-distribʳ p₀ q₀ x)
        (cong₂ addZω (mulZω-distribʳ p₁ q₁ y) (mulZω-distribʳ p₂ q₂ z)) ⟩
    addZω (addZω (mulZω p₀ x) (mulZω q₀ x))
          (addZω (addZω (mulZω p₁ y) (mulZω q₁ y))
                 (addZω (mulZω p₂ z) (mulZω q₂ z)))
  ≡⟨ add-transpose-23 (mulZω p₀ x) (mulZω p₁ y) (mulZω p₂ z)
                      (mulZω q₀ x) (mulZω q₁ y) (mulZω q₂ z) ⟩
    addZω (addZω (mulZω p₀ x) (addZω (mulZω p₁ y) (mulZω p₂ z)))
          (addZω (mulZω q₀ x) (addZω (mulZω q₁ y) (mulZω q₂ z)))
  ≡⟨ cong₂ addZω
        (sym (cong (λ t → addZω (mulZω p₀ x) (addZω (mulZω p₁ y) t))
                   (addZω-identityʳ (mulZω p₂ z))))
        (sym (cong (λ t → addZω (mulZω q₀ x) (addZω (mulZω q₁ y) t))
                   (addZω-identityʳ (mulZω q₂ z)))) ⟩
    addZω (addZω (mulZω p₀ x)
                 (addZω (mulZω p₁ y) (addZω (mulZω p₂ z) zeroZω)))
          (addZω (mulZω q₀ x)
                 (addZω (mulZω q₁ y) (addZω (mulZω q₂ z) zeroZω)))
  ∎

dot-add : ∀ (p q v : Vec3) → dot (addV3 p q) v ≡ addZω (dot p v) (dot q v)
dot-add (p₀ ∷ p₁ ∷ p₂ ∷ []) (q₀ ∷ q₁ ∷ q₂ ∷ []) (x ∷ y ∷ z ∷ []) =
  dot-add3 p₀ p₁ p₂ q₀ q₁ q₂ x y z

-- | 尾零吸收：c·(x ⊕ 0) ≡ (c·x) ⊕ 0
mul-zero-tail : ∀ (c x : Zω) → mulZω c (addZω x zeroZω) ≡ addZω (mulZω c x) zeroZω
mul-zero-tail c x =
  trans (mulZω-distribˡ c x zeroZω)
        (cong (addZω (mulZω c x)) (mulZω-zeroʳ c))

-- | dot 对**第一**个因子的标量线性：dot (c·p) v ≡ c·(dot p v)
--
--   ⚠ `dot` 的三项展开带尾零，故 `distrib3ˡ` 的最内一项是 `p₂z ⊕ 0`（不是 `p₂z`）；
--   中间用 `mul-zero-tail` 把 `c·(p₂z ⊕ 0)` 与 `(c·p₂z) ⊕ 0` 对齐。
dot-scale-left : ∀ (c : Zω) (p v : Vec3)
               → dot (scaleV3 c p) v ≡ mulZω c (dot p v)
dot-scale-left c (p₀ ∷ p₁ ∷ p₂ ∷ []) (x ∷ y ∷ z ∷ []) = begin
    addZω (mulZω (mulZω c p₀) x)
          (addZω (mulZω (mulZω c p₁) y) (addZω (mulZω (mulZω c p₂) z) zeroZω))
  ≡⟨ cong₂ addZω (mulZω-assoc c p₀ x)
        (cong₂ addZω (mulZω-assoc c p₁ y)
          (cong (λ t → addZω t zeroZω) (mulZω-assoc c p₂ z))) ⟩
    addZω (mulZω c (mulZω p₀ x))
          (addZω (mulZω c (mulZω p₁ y)) (addZω (mulZω c (mulZω p₂ z)) zeroZω))
  ≡⟨ cong (λ t → addZω (mulZω c (mulZω p₀ x))
                       (addZω (mulZω c (mulZω p₁ y)) t))
          (sym (mul-zero-tail c (mulZω p₂ z))) ⟩
    addZω (mulZω c (mulZω p₀ x))
          (addZω (mulZω c (mulZω p₁ y)) (mulZω c (addZω (mulZω p₂ z) zeroZω)))
  ≡⟨ sym (distrib3ˡ c (mulZω p₀ x) (mulZω p₁ y)
                     (addZω (mulZω p₂ z) zeroZω)) ⟩
    mulZω c (addZω (mulZω p₀ x)
                   (addZω (mulZω p₁ y) (addZω (mulZω p₂ z) zeroZω)))
  ∎

-- | 行组合：a₀·b₀ ⊕ (a₁·b₁ ⊕ a₂·b₂)（向量层面）
combRow : Vec3 → Mat 3 3 → Vec3
combRow (a₀ ∷ a₁ ∷ a₂ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ []) =
  addV3 (scaleV3 a₀ b₀) (addV3 (scaleV3 a₁ b₁) (scaleV3 a₂ b₂))

-- | 3×3 矩阵乘法（行组合形式；与 Σₖ aᵢₖ·bₖⱼ 逐条相同）
--
--   ⚠ 名不用 `mulM3`：`Sov.Algebra.GroupTheory.PhaseMatrixBridge` 已有同名的
--   GF(3)/`Trit` 版（`Mat3` 记录），载体不同、不可复用；这里按 `mulMV3` 同族取 `mulMM3`。
mulMM3 : Mat 3 3 → Mat 3 3 → Mat 3 3
mulMM3 (a ∷ b ∷ d ∷ []) B = combRow a B ∷ combRow b B ∷ combRow d B ∷ []

-- | 单行相容：dot (combRow a B) v ≡ dot a (mulMV3 B v)
row3-comb : ∀ (a : Vec3) (B : Mat 3 3) (v : Vec3)
          → dot (combRow a B) v ≡ dot a (mulMV3 B v)
row3-comb (a₀ ∷ a₁ ∷ a₂ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ []) v = begin
    dot (addV3 (scaleV3 a₀ b₀) (addV3 (scaleV3 a₁ b₁) (scaleV3 a₂ b₂))) v
  ≡⟨ dot-add (scaleV3 a₀ b₀) (addV3 (scaleV3 a₁ b₁) (scaleV3 a₂ b₂)) v ⟩
    addZω (dot (scaleV3 a₀ b₀) v)
          (dot (addV3 (scaleV3 a₁ b₁) (scaleV3 a₂ b₂)) v)
  ≡⟨ cong₂ addZω (dot-scale-left a₀ b₀ v)
        (trans (dot-add (scaleV3 a₁ b₁) (scaleV3 a₂ b₂) v)
               (cong₂ addZω (dot-scale-left a₁ b₁ v) (dot-scale-left a₂ b₂ v))) ⟩
    addZω (mulZω a₀ (dot b₀ v))
          (addZω (mulZω a₁ (dot b₁ v)) (mulZω a₂ (dot b₂ v)))
  ≡⟨ sym (cong (λ t → addZω (mulZω a₀ (dot b₀ v))
                            (addZω (mulZω a₁ (dot b₁ v)) t))
               (addZω-identityʳ (mulZω a₂ (dot b₂ v)))) ⟩
    dot (a₀ ∷ a₁ ∷ a₂ ∷ []) (mulMV3 (b₀ ∷ b₁ ∷ b₂ ∷ []) v)
  ∎

-- | 矩阵乘法与作用相容：ρ(A·B)·v ≡ ρ(A)·(ρ(B)·v)
mulMV3-mulMM3 : ∀ (A B : Mat 3 3) (v : Vec3)
              → mulMV3 (mulMM3 A B) v ≡ mulMV3 A (mulMV3 B v)
mulMV3-mulMM3 (a ∷ b ∷ d ∷ []) B v =
  vec3-cong (row3-comb a B v) (row3-comb b B v) (row3-comb d B v)

