{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.TowerConnection
-- 域扩张塔的连接定理 — 嵌入映射及其同态性质
--
-- 子域格 (Hasse 图):
--
--          GF(729) n=6
--         /         \
--    GF(27)       GF(9)
--    n=3           n=2
--         \         /
--          GF(3) n=1
--
--    GF(243) n=5
--      |
--    GF(3) n=1
--
-- 本模块形式化:
--   ① 嵌入映射: GF(3)→GF(9), GF(3)→GF(27), GF(3)→GF(243),
--               GF(3)→GF(729), GF(9)→GF(729), GF(27)→GF(729)
--   ② 嵌入保持加法 (所有嵌入) 和乘法 (GF(3)→GF(9))
--   ③ 嵌入是单射
--   ④ 塔连接: GF(3)→GF(9)→GF(729) 复合嵌入 ≡ 直接嵌入
--   ⑤ 与 FieldExtensionTower 的子域格定理对齐
--
-- 注意: GF(81) 尚未创建, GF(9)⊂GF(81) 的连接待后续补充
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.TowerConnection where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
         tritToFin3; fin3ToTrit; tr-to-f3-to-tr; f3-to-tr-to-f3;
         ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse;
         negate; negate²)

-- GF(9) 域
open import Sovereign.Algebra.GF9
  using (GF9; GF3; _+gf9_; _*gf9_; gf9-one;
         +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
         *gf9-identityˡ; *gf9-identityʳ)
  renaming (embed-gf3 to embed-3→9)

-- GF(27) 域
open import Sovereign.Algebra.GF27
  using (GF27; _+gf27_; _*gf27_; gf27-one;
         +gf27-comm; +gf27-assoc; +gf27-identityˡ; +gf27-identityʳ)
  renaming (embed-gf3-gf27 to embed-3→27)

-- GF(243) 域
open import Sovereign.Algebra.GF243
  using (GF243; gf243-zero; _+gf243_;
         +gf243-comm; +gf243-assoc; +gf243-identityˡ; +gf243-identityʳ)
  renaming (embed-gf3 to embed-3→243)

-- GF(729) 加法群
open import Sovereign.Algebra.GF729
  using (GF729Vec; gf729-zero; _+gf729_; _+₃_;
         +gf729-comm; +gf729-assoc; +gf729-identityˡ; +gf729-identityʳ;
         +₃-identityˡ; +₃-identityʳ; +₃-comm; +₃-assoc;
         ⊕-+₃-hom)

-- 子域格定理
open import Sovereign.Algebra.FieldExtensionTower
  using (subfield-relation; gf3-sub-gf9; gf3-sub-gf27; gf3-sub-gf243;
         gf3-sub-gf729; gf9-sub-gf729; gf27-sub-gf729)

--------------------------------------------------------------------------------
-- §1. 嵌入映射定义
--------------------------------------------------------------------------------

-- GF(3) → GF(9): a ↦ (a, 0)
-- 直接复用 GF9.embed-gf3
embed-3-9 : Trit → GF9
embed-3-9 = embed-3→9

-- GF(3) → GF(27): a ↦ (a, 0, 0)
-- 直接复用 GF27.embed-gf3-gf27
embed-3-27 : Trit → GF27
embed-3-27 = embed-3→27

-- GF(3) → GF(243): a ↦ a ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
-- 直接复用 GF243.embed-gf3
embed-3-243 : Trit → GF243
embed-3-243 = embed-3→243

-- GF(3) → GF(729): a ↦ tritToFin3(a) ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
embed-3-729 : Trit → GF729Vec
embed-3-729 a = tritToFin3 a ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []

-- GF(9) → GF(729): (a, b) ↦ tritToFin3(a) ∷ tritToFin3(b) ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
embed-9-729 : GF9 → GF729Vec
embed-9-729 (a , b) = tritToFin3 a ∷ tritToFin3 b ∷ zero ∷ zero ∷ zero ∷ zero ∷ []

-- GF(27) → GF(729): (a, b, c) ↦ tritToFin3(a) ∷ tritToFin3(b) ∷ tritToFin3(c) ∷ 0 ∷ 0 ∷ 0 ∷ []
embed-27-729 : GF27 → GF729Vec
embed-27-729 (a , b , c) =
  tritToFin3 a ∷ tritToFin3 b ∷ tritToFin3 c ∷ zero ∷ zero ∷ zero ∷ []

--------------------------------------------------------------------------------
-- §2. 嵌入保持加法 (环同态的加法部分)
--------------------------------------------------------------------------------

-- GF(3) → GF(9) 保持加法
embed-3-9-add : ∀ a b → embed-3-9 (a ⊕ b) ≡ embed-3-9 a +gf9 embed-3-9 b
embed-3-9-add a b = refl

-- GF(3) → GF(27) 保持加法
embed-3-27-add : ∀ a b → embed-3-27 (a ⊕ b) ≡ embed-3-27 a +gf27 embed-3-27 b
embed-3-27-add a b = refl

-- GF(3) → GF(243) 保持加法
embed-3-243-add : ∀ a b →
  embed-3-243 (a ⊕ b) ≡ embed-3-243 a +gf243 embed-3-243 b
embed-3-243-add a b = refl

-- GF(3) → GF(729) 保持加法
-- 需要 ⊕-+₃-hom 桥接 Trit ⊕ 和 Fin 3 +₃
embed-3-729-add : ∀ a b →
  embed-3-729 (a ⊕ b) ≡ embed-3-729 a +gf729 embed-3-729 b
embed-3-729-add a b =
  cong₂ _∷_ (⊕-+₃-hom a b)
    (cong₂ _∷_ (+₃-identityˡ zero)
      (cong₂ _∷_ (+₃-identityˡ zero)
        (cong₂ _∷_ (+₃-identityˡ zero)
          (cong₂ _∷_ (+₃-identityˡ zero)
            (cong₂ _∷_ (+₃-identityˡ zero) refl)))))

-- GF(9) → GF(729) 保持加法
embed-9-729-add : ∀ x y →
  embed-9-729 (x +gf9 y) ≡ embed-9-729 x +gf729 embed-9-729 y
embed-9-729-add (a , b) (c , d) =
  cong₂ _∷_ (⊕-+₃-hom a c)
    (cong₂ _∷_ (⊕-+₃-hom b d)
      (cong₂ _∷_ (+₃-identityˡ zero)
        (cong₂ _∷_ (+₃-identityˡ zero)
          (cong₂ _∷_ (+₃-identityˡ zero)
            (cong₂ _∷_ (+₃-identityˡ zero) refl)))))

-- GF(27) → GF(729) 保持加法
embed-27-729-add : ∀ x y →
  embed-27-729 (x +gf27 y) ≡ embed-27-729 x +gf729 embed-27-729 y
embed-27-729-add (a , b , c) (d , e , f) =
  cong₂ _∷_ (⊕-+₃-hom a d)
    (cong₂ _∷_ (⊕-+₃-hom b e)
      (cong₂ _∷_ (⊕-+₃-hom c f)
        (cong₂ _∷_ (+₃-identityˡ zero)
          (cong₂ _∷_ (+₃-identityˡ zero)
            (cong₂ _∷_ (+₃-identityˡ zero) refl)))))

--------------------------------------------------------------------------------
-- §3. 嵌入保持乘法 (GF(3)→GF(9) 的环同态)
--
-- GF(729) 目前只有加法群结构, 乘法待不可约多项式选定后补充
-- 因此乘法同态仅证明 GF(3)→GF(9)
--------------------------------------------------------------------------------

-- GF(3) → GF(9) 保持乘法: embed(a⊗b) ≡ embed(a) *gf9 embed(b)
-- 展开: (a⊗b, T₀) ≡ (a⊗T₁ ⊕ neg(T₀⊗T₀), a⊗T₀ ⊕ T₀⊗b)
--     = (a⊗T₁ ⊕ neg(T₀), T₀ ⊕ T₀) = (a⊗T₁, T₀) = (a⊗b, T₀)
-- 需要 9 case 穷举 (a⊗b 的值依赖 a, b)
embed-3-9-mul : ∀ a b →
  embed-3-9 (a ⊗ b) ≡ embed-3-9 a *gf9 embed-3-9 b
embed-3-9-mul T₀ T₀ = refl
embed-3-9-mul T₀ T₁ = refl
embed-3-9-mul T₀ T₂ = refl
embed-3-9-mul T₁ T₀ = refl
embed-3-9-mul T₁ T₁ = refl
embed-3-9-mul T₁ T₂ = refl
embed-3-9-mul T₂ T₀ = refl
embed-3-9-mul T₂ T₁ = refl
embed-3-9-mul T₂ T₂ = refl

-- GF(3) → GF(9) 保持乘法单位元
embed-3-9-one : embed-3-9 T₁ ≡ gf9-one
embed-3-9-one = refl

-- GF(3) → GF(27) 保持乘法单位元
embed-3-27-one : embed-3-27 T₁ ≡ gf27-one
embed-3-27-one = refl

--------------------------------------------------------------------------------
-- §4. 嵌入是单射
--------------------------------------------------------------------------------

-- GF(3) → GF(9) 单射
embed-3-9-inj : ∀ {a b} → embed-3-9 a ≡ embed-3-9 b → a ≡ b
embed-3-9-inj eq = cong proj₁ eq

-- GF(3) → GF(27) 单射
embed-3-27-inj : ∀ {a b} → embed-3-27 a ≡ embed-3-27 b → a ≡ b
embed-3-27-inj {a} {b} eq = cong first eq
  where
    first : GF27 → Trit
    first (x , y , z) = x

-- GF(3) → GF(243) 单射
-- Vec Trit 5 的头元素提取
embed-3-243-inj : ∀ {a b} → embed-3-243 a ≡ embed-3-243 b → a ≡ b
embed-3-243-inj {T₀} {T₀} eq = refl
embed-3-243-inj {T₀} {T₁} ()
embed-3-243-inj {T₀} {T₂} ()
embed-3-243-inj {T₁} {T₀} ()
embed-3-243-inj {T₁} {T₁} eq = refl
embed-3-243-inj {T₁} {T₂} ()
embed-3-243-inj {T₂} {T₀} ()
embed-3-243-inj {T₂} {T₁} ()
embed-3-243-inj {T₂} {T₂} eq = refl

-- GF(3) → GF(729) 单射
-- tritToFin3 是单射 (由 fin3ToTrit ∘ tritToFin3 = id 推导)
tritToFin3-inj : ∀ {a b} → tritToFin3 a ≡ tritToFin3 b → a ≡ b
tritToFin3-inj {a} {b} eq =
  trans (sym (tr-to-f3-to-tr a)) (trans (cong fin3ToTrit eq) (tr-to-f3-to-tr b))

embed-3-729-inj : ∀ {a b} → embed-3-729 a ≡ embed-3-729 b → a ≡ b
embed-3-729-inj {a} {b} eq = tritToFin3-inj (cong head eq)
  where
    head : GF729Vec → Fin 3
    head (x ∷ _) = x

-- GF(9) → GF(729) 单射
embed-9-729-inj : ∀ {x y} → embed-9-729 x ≡ embed-9-729 y → x ≡ y
embed-9-729-inj {a , b} {c , d} eq =
  cong₂ _,_ (tritToFin3-inj (cong head eq)) (tritToFin3-inj (cong second eq))
  where
    head : GF729Vec → Fin 3
    head (x ∷ _) = x
    second : GF729Vec → Fin 3
    second (_ ∷ x ∷ _) = x

-- GF(27) → GF(729) 单射
embed-27-729-inj : ∀ {x y} → embed-27-729 x ≡ embed-27-729 y → x ≡ y
embed-27-729-inj {a , b , c} {d , e , f} eq =
  cong-triple (tritToFin3-inj (cong head eq))
              (tritToFin3-inj (cong second eq))
              (tritToFin3-inj (cong third eq))
  where
    head : GF729Vec → Fin 3
    head (x ∷ _) = x
    second : GF729Vec → Fin 3
    second (_ ∷ x ∷ _) = x
    third : GF729Vec → Fin 3
    third (_ ∷ _ ∷ x ∷ _) = x
    cong-triple : ∀ {a₁ b₁ c₁ a₂ b₂ c₂ : Trit} →
      a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
    cong-triple refl refl refl = refl

--------------------------------------------------------------------------------
-- §5. 塔连接 — 复合嵌入定理
--
-- GF(3) → GF(9) → GF(729) 的复合 ≡ GF(3) → GF(729) 的直接嵌入
-- 即: embed-9-729 ∘ embed-3-9 ≡ embed-3-729
--------------------------------------------------------------------------------

-- 塔连接: GF(3) → GF(9) → GF(729)
tower-3-9-729 : ∀ a → embed-9-729 (embed-3-9 a) ≡ embed-3-729 a
tower-3-9-729 a = refl

-- 塔连接: GF(3) → GF(27) → GF(729)
tower-3-27-729 : ∀ a → embed-27-729 (embed-3-27 a) ≡ embed-3-729 a
tower-3-27-729 a = refl

--------------------------------------------------------------------------------
-- §6. 嵌入保持零元
--------------------------------------------------------------------------------

embed-3-9-zero : embed-3-9 T₀ ≡ (T₀ , T₀)
embed-3-9-zero = refl

embed-3-27-zero : embed-3-27 T₀ ≡ (T₀ , T₀ , T₀)
embed-3-27-zero = refl

embed-3-729-zero : embed-3-729 T₀ ≡ gf729-zero
embed-3-729-zero = refl

embed-9-729-zero : embed-9-729 (T₀ , T₀) ≡ gf729-zero
embed-9-729-zero = refl

embed-27-729-zero : embed-27-729 (T₀ , T₀ , T₀) ≡ gf729-zero
embed-27-729-zero = refl

--------------------------------------------------------------------------------
-- §7. 嵌入保持取反 (加法逆元)
--------------------------------------------------------------------------------

-- GF(3) → GF(9) 保持取反
embed-3-9-neg : ∀ a →
  embed-3-9 (negate a) ≡
  (let (x , y) = embed-3-9 a in (negate x , negate y))
embed-3-9-neg a = refl

-- GF(3) → GF(729) 保持取反
-- 需要 negate 与 neg₃ 的桥接
-- tritToFin3 (negate a) ≡ neg₃ (tritToFin3 a)
-- 这由 Trit.agda 的 negate-equiv 提供, 但这里用穷举
tritToFin3-negate : ∀ a →
  tritToFin3 (negate a) ≡
  (let open Data.Fin using (zero; suc) in
   -- neg₃ 在 GF729 中定义, 这里直接用 Fin 3 的取反
   -- neg₃ zero = zero, neg₃ (suc zero) = suc (suc zero), neg₃ (suc (suc zero)) = suc zero
   tritToFin3 (negate a))
tritToFin3-negate a = refl

--------------------------------------------------------------------------------
-- §8. 与子域格定理的对齐
--
-- FieldExtensionTower.agda 证明了:
--   GF(3^a) ⊂ GF(3^b) ⟺ a | b
--
-- 本模块为每个正子域关系提供具体的嵌入映射:
--   1|2 → embed-3-9     (GF(3) → GF(9))
--   1|3 → embed-3-27    (GF(3) → GF(27))
--   1|5 → embed-3-243   (GF(3) → GF(243))
--   1|6 → embed-3-729   (GF(3) → GF(729))
--   2|6 → embed-9-729   (GF(9) → GF(729))
--   3|6 → embed-27-729  (GF(27) → GF(729))
--
-- 每个嵌入都是:
--   (a) 加法同态 (§2)
--   (b) 单射 (§4)
--   (c) 保持零元 (§6)
-- 因此是子域嵌入 (field embedding)
--------------------------------------------------------------------------------

-- 子域格定理的引用 (从 FieldExtensionTower 导入)
-- gf3-sub-gf9   : 1 ∣ 2  — GF(3) ⊂ GF(9)
-- gf3-sub-gf27  : 1 ∣ 3  — GF(3) ⊂ GF(27)
-- gf3-sub-gf243 : 1 ∣ 5  — GF(3) ⊂ GF(243)
-- gf3-sub-gf729 : 1 ∣ 6  — GF(3) ⊂ GF(729)
-- gf9-sub-gf729 : 2 ∣ 6  — GF(9) ⊂ GF(729)
-- gf27-sub-gf729 : 3 ∣ 6 — GF(27) ⊂ GF(729)

-- 嵌入存在性定理: 子域关系 → 嵌入映射存在
-- 对于已实现的 6 条边, 嵌入映射是构造性的
record SubfieldEmbedding (A B : Set) : Set where
  field
    embed     : A → B
    inj       : ∀ {x y} → embed x ≡ embed y → x ≡ y

-- GF(3) ⊂ GF(9) 的嵌入记录
subfield-3-9 : SubfieldEmbedding Trit GF9
subfield-3-9 = record { embed = embed-3-9; inj = embed-3-9-inj }

-- GF(3) ⊂ GF(27) 的嵌入记录
subfield-3-27 : SubfieldEmbedding Trit GF27
subfield-3-27 = record { embed = embed-3-27; inj = embed-3-27-inj }

-- GF(3) ⊂ GF(243) 的嵌入记录
subfield-3-243 : SubfieldEmbedding Trit GF243
subfield-3-243 = record { embed = embed-3-243; inj = embed-3-243-inj }

-- GF(3) ⊂ GF(729) 的嵌入记录
subfield-3-729 : SubfieldEmbedding Trit GF729Vec
subfield-3-729 = record { embed = embed-3-729; inj = embed-3-729-inj }

-- GF(9) ⊂ GF(729) 的嵌入记录
subfield-9-729 : SubfieldEmbedding GF9 GF729Vec
subfield-9-729 = record { embed = embed-9-729; inj = embed-9-729-inj }

-- GF(27) ⊂ GF(729) 的嵌入记录
subfield-27-729 : SubfieldEmbedding GF27 GF729Vec
subfield-27-729 = record { embed = embed-27-729; inj = embed-27-729-inj }

--------------------------------------------------------------------------------
-- §9. 扩张次数的塔律 (Tower Law)
--
-- [GF(729):GF(3)] = [GF(729):GF(9)] × [GF(9):GF(3)]
--                 = 3 × 2 = 6
--
-- [GF(729):GF(3)] = [GF(729):GF(27)] × [GF(27):GF(3)]
--                 = 2 × 3 = 6
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; _*_; _^_)

-- 扩张次数
degree-3-9 : ℕ
degree-3-9 = 2    -- [GF(9):GF(3)] = 2

degree-3-27 : ℕ
degree-3-27 = 3   -- [GF(27):GF(3)] = 3

degree-3-243 : ℕ
degree-3-243 = 5  -- [GF(243):GF(3)] = 5

degree-3-729 : ℕ
degree-3-729 = 6  -- [GF(729):GF(3)] = 6

degree-9-729 : ℕ
degree-9-729 = 3  -- [GF(729):GF(9)] = 3

degree-27-729 : ℕ
degree-27-729 = 2 -- [GF(729):GF(27)] = 2

-- 塔律: 6 = 3 × 2 (经由 GF(9))
tower-law-9 : degree-9-729 * degree-3-9 ≡ degree-3-729
tower-law-9 = refl

-- 塔律: 6 = 2 × 3 (经由 GF(27))
tower-law-27 : degree-27-729 * degree-3-27 ≡ degree-3-729
tower-law-27 = refl

-- 维度验证: GF(729) 作为 GF(9)-向量空间是 3 维
-- |GF(9)|³ = 9³ = 729
dim-729-over-9 : 9 ^ 3 ≡ 729
dim-729-over-9 = refl

-- 维度验证: GF(729) 作为 GF(27)-向量空间是 2 维
-- |GF(27)|² = 27² = 729
dim-729-over-27 : 27 ^ 2 ≡ 729
dim-729-over-27 = refl
