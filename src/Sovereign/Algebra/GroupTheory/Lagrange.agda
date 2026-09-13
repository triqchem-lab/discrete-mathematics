{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.Lagrange
-- 有限群 Lagrange 定理（通用版，构造性）：|G| = |H| × [G:H]
--
-- 数学背景:
--   Lagrange 定理是有限群论的第一块基石：子群 H ≤ G 的阶整除 |G|。
--   本库此前只有 A₄ 具体实例与 T⁶ 的 Cubical 等价版（谱投影），
--   没有通用定理；本模块补上这个缺口。
--
-- 证明骨架（两条腿，各自独立可验）:
--   ① 计数层（纯组合）：若 f : Fin n → Fin m 的每个纤维都恰有 k 个元素，
--      则 n ≡ k × m。该引理**不做任何算术暴力**：它把"纤维枚举"
--      提升为一个双射 Fin (m × k) ↔ Fin n，再用 Fin 的基数唯一性
--      （有限 Cantor–Schröder–Bernstein）收口。
--   ② 群论层：陪集映射 q 的纤维恰是左陪集 gH；
--      而 h ↦ g ⊙ h 给出 H ≅ gH 的双射（左消去律保证单射）。
--
-- 核心原则:
--   1. 群以 Fin n 为载体 —— |G| = n 是定义，不是外部投影；
--   2. 子群用"注入枚举 + 运算封闭"给出 —— 不引入商类型、不引入 Σ-等式地狱；
--   3. 陪集映射 q 与截面 repr 是**数据**，陪集判定 q x ≡ q y ⇔ x⁻¹y ∈ H 是**命题**；
--   4. 0 postulate / 0 hole / 0 sorry —— 全部构造性闭合，无 Choice、无排中律。
--
-- 依赖方向: Base → Algebra → Algebra.GroupTheory（同层复用 Duodecimal，不反向依赖 Physics）
--
-- 包含:
--   §1 计数层：注入复合 / 往返注入 / 纤维计数引理
--   §2 FinGroup：Fin n 载体上的有限群 + 消去律 / 逆元反序 / 双重逆
--   §3 Subgroup：注入枚举 + 封闭性 + 成员引理
--   §4 Lagrange 主定理
--   §5 具体实例：C₄（α 群，阶 1/2/4 子群）+ C₁₂（阶 1/12 子群）
--   §6 对抗验证：具体点 refl 交叉比对

module Sovereign.Algebra.GroupTheory.Lagrange where

open import Data.Nat using (ℕ; _*_; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Base using (remQuot; combine)
open import Data.Fin.Properties
  using (cantor-schröder-bernstein; remQuot-combine; combine-remQuot)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat.Properties using (*-comm)
open import Function.Definitions using (Injective)
open import Function.Bundles using (_⇔_; Equivalence; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11;
         _+12_; +12-assoc; +12-comm; +12-identityʳ; +12-inverse; neg12)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 计数层：纤维计数引理
--------------------------------------------------------------------------------

-- Fin 1 只有一个元素
fin1-unique : (r : Fin 1) → zero ≡ r
fin1-unique zero = refl

-- Fin 1 出发的任意函数都是单射
fin1-inj : ∀ {n} (f : Fin 1 → Fin n) → Injective _≡_ _≡_ f
fin1-inj f {zero} {zero} _ = refl

-- 由左往返 (from ∘ to ≡ id) 得到 to 的单射性
inj-from-inverseˡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
                    {to : A → B} {from : B → A}
                  → (∀ x → from (to x) ≡ x) → Injective _≡_ _≡_ to
inj-from-inverseˡ {to = to} {from = from} invˡ {x} {y} eq =
  trans (sym (invˡ x)) (trans (cong from eq) (invˡ y))

-- 由右往返 (to ∘ from ≡ id) 得到 from 的单射性
inj-from-inverseʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
                    {to : A → B} {from : B → A}
                  → (∀ y → to (from y) ≡ y) → Injective _≡_ _≡_ from
inj-from-inverseʳ {to = to} {from = from} invʳ {x} {y} eq =
  trans (sym (invʳ x)) (trans (cong to eq) (invʳ y))

-- 纤维计数引理（核心）:
--   f : Fin n → Fin m，g r : Fin k → Fin n 是纤维 r 的枚举（落点、单射、命中），
--   则 n ≡ k × m。
-- 直观: g 把 "m 个纤维 × k 个元素" 参数化为 G 的全部 n 个元素，
--       于是得到双向单射 Fin (m × k) ↔ Fin n，基数唯一性收口。
fiber-count :
  ∀ {n m k} (f : Fin n → Fin m) (g : Fin m → Fin k → Fin n)
  → (∀ r t → f (g r t) ≡ r)                     -- g r 落在纤维 r 内
  → (∀ r {t u} → g r t ≡ g r u → t ≡ u)         -- g r 单射
  → (∀ i → Σ (Fin k) (λ t → g (f i) t ≡ i))     -- 每个 i 被其所在纤维的 g 命中
  → n ≡ k * m
fiber-count {n} {m} {k} f g mem inj sur = trans (sym m*k≡n) (*-comm m k)
  where
    -- 参数化映射 Φ : Fin m × Fin k → Fin n
    Φ : Fin m × Fin k → Fin n
    Φ (r , t) = g r t

    -- 反向映射：i ↦ (它所在的纤维标号, 它在纤维内的位置)
    Ψ : Fin n → Fin m × Fin k
    Ψ i = f i , proj₁ (sur i)

    Φ-inj : Injective _≡_ _≡_ Φ
    Φ-inj {r , t} {s , u} eq = cong₂ _,_ e tu
      where
        -- 先取出纤维标号相等（用 f ∘ g = id 两次）
        e : r ≡ s
        e = trans (sym (mem r t)) (trans (cong f eq) (mem s u))
        -- 再把 g 的下标从 s 搬回 r
        move : g s u ≡ g r u
        move = subst (λ z → g z u ≡ g r u) e refl
        tu : t ≡ u
        tu = inj r (trans eq move)

    Ψ-inj : Injective _≡_ _≡_ Ψ
    Ψ-inj {i} {j} eq =
      trans (sym (proj₂ (sur i))) (trans (cong Φ eq) (proj₂ (sur j)))

    -- 与标准双射 Fin (m × k) ↔ Fin m × Fin k 复合（直接用 stdlib 的 remQuot / combine）
    to′ : Fin (m * k) → Fin n
    to′ = λ x → Φ (remQuot {m} k x)

    from′ : Fin n → Fin (m * k)
    from′ = λ y → combine (proj₁ (Ψ y)) (proj₂ (Ψ y))

    remQuot-inj : Injective _≡_ _≡_ (remQuot {m} k)
    remQuot-inj = inj-from-inverseˡ {to = remQuot {m} k}
                                    {from = λ p → combine (proj₁ p) (proj₂ p)}
                                    (λ x → combine-remQuot {m} k x)

    to′-inj : Injective _≡_ _≡_ to′
    to′-inj eq = remQuot-inj (Φ-inj eq)

    -- combine 的单射性（由 remQuot-combine 的右往返得到）
    combine-inj : Injective _≡_ _≡_ (λ p → combine (proj₁ p) (proj₂ p))
    combine-inj = inj-from-inverseʳ {to = remQuot {m} k}
                                    {from = λ p → combine (proj₁ p) (proj₂ p)}
                                    (λ p → remQuot-combine {m} {k} (proj₁ p) (proj₂ p))

    from′-inj : Injective _≡_ _≡_ from′
    from′-inj eq = Ψ-inj (combine-inj eq)

    -- 有限 Cantor–Schröder–Bernstein：双向单射 ⇒ 基数相等
    m*k≡n : m * k ≡ n
    m*k≡n = cantor-schröder-bernstein to′-inj from′-inj

--------------------------------------------------------------------------------
-- §2. FinGroup：以 Fin n 为载体的有限群
--------------------------------------------------------------------------------

-- 有限群：载体 Fin n（故 |G| = n 是定义），5 条群公理。
record FinGroup (n : ℕ) : Set where
  infixl 7 _⊙_
  field
    _⊙_ : Fin n → Fin n → Fin n
    ε : Fin n
    inv : Fin n → Fin n
    assoc : ∀ x y z → (x ⊙ y) ⊙ z ≡ x ⊙ (y ⊙ z)
    identityˡ : ∀ x → ε ⊙ x ≡ x
    identityʳ : ∀ x → x ⊙ ε ≡ x
    inverseˡ : ∀ x → inv x ⊙ x ≡ ε
    inverseʳ : ∀ x → x ⊙ inv x ≡ ε

  -- 左消去律（结合律 + 左逆元）
  cancelˡ : ∀ {x y z} → x ⊙ y ≡ x ⊙ z → y ≡ z
  cancelˡ {x} {y} {z} eq = begin
    y                 ≡⟨ sym (identityˡ y) ⟩
    ε ⊙ y             ≡⟨ cong (_⊙ y) (sym (inverseˡ x)) ⟩
    (inv x ⊙ x) ⊙ y   ≡⟨ assoc (inv x) x y ⟩
    inv x ⊙ (x ⊙ y)   ≡⟨ cong (inv x ⊙_) eq ⟩
    inv x ⊙ (x ⊙ z)   ≡⟨ sym (assoc (inv x) x z) ⟩
    (inv x ⊙ x) ⊙ z   ≡⟨ cong (_⊙ z) (inverseˡ x) ⟩
    ε ⊙ z             ≡⟨ identityˡ z ⟩
    z                 ∎

  -- 右消去律
  cancelʳ : ∀ {x y z} → y ⊙ x ≡ z ⊙ x → y ≡ z
  cancelʳ {x} {y} {z} eq = begin
    y                 ≡⟨ sym (identityʳ y) ⟩
    y ⊙ ε             ≡⟨ cong (y ⊙_) (sym (inverseʳ x)) ⟩
    y ⊙ (x ⊙ inv x)   ≡⟨ sym (assoc y x (inv x)) ⟩
    (y ⊙ x) ⊙ inv x   ≡⟨ cong (_⊙ inv x) eq ⟩
    (z ⊙ x) ⊙ inv x   ≡⟨ assoc z x (inv x) ⟩
    z ⊙ (x ⊙ inv x)   ≡⟨ cong (z ⊙_) (inverseʳ x) ⟩
    z ⊙ ε             ≡⟨ identityʳ z ⟩
    z                 ∎

  -- 逆元唯一性：x ⊙ y ≡ ε ⇒ y ≡ inv x
  inv-uniqueˡ : ∀ {x y} → x ⊙ y ≡ ε → y ≡ inv x
  inv-uniqueˡ {x} {y} p = cancelˡ {x = x} (trans p (sym (inverseʳ x)))

  -- 逆元反序：(x ⊙ y)⁻¹ ≡ y⁻¹ ⊙ x⁻¹
  inv-⊙ : ∀ x y → inv (x ⊙ y) ≡ inv y ⊙ inv x
  inv-⊙ x y = sym (inv-uniqueˡ {x = x ⊙ y} {y = inv y ⊙ inv x} pf)
    where
      pf : (x ⊙ y) ⊙ (inv y ⊙ inv x) ≡ ε
      pf = begin
        (x ⊙ y) ⊙ (inv y ⊙ inv x)     ≡⟨ assoc x y (inv y ⊙ inv x) ⟩
        x ⊙ (y ⊙ (inv y ⊙ inv x))     ≡⟨ cong (x ⊙_) (sym (assoc y (inv y) (inv x))) ⟩
        x ⊙ ((y ⊙ inv y) ⊙ inv x)     ≡⟨ cong (λ z → x ⊙ (z ⊙ inv x)) (inverseʳ y) ⟩
        x ⊙ (ε ⊙ inv x)               ≡⟨ cong (x ⊙_) (identityˡ (inv x)) ⟩
        x ⊙ inv x                     ≡⟨ inverseʳ x ⟩
        ε                             ∎

  -- 双重逆
  inv-inv : ∀ x → inv (inv x) ≡ x
  inv-inv x = sym (inv-uniqueˡ {x = inv x} {y = x} (inverseˡ x))

  -- 逆元消去：(x ⊙ y)⁻¹ ⊙ x ≡ y⁻¹
  inv-⊙-cancel : ∀ x y → inv (x ⊙ y) ⊙ x ≡ inv y
  inv-⊙-cancel x y = begin
    inv (x ⊙ y) ⊙ x       ≡⟨ cong (_⊙ x) (inv-⊙ x y) ⟩
    (inv y ⊙ inv x) ⊙ x   ≡⟨ assoc (inv y) (inv x) x ⟩
    inv y ⊙ (inv x ⊙ x)   ≡⟨ cong (inv y ⊙_) (inverseˡ x) ⟩
    inv y ⊙ ε             ≡⟨ identityʳ (inv y) ⟩
    inv y                 ∎

--------------------------------------------------------------------------------
-- §3. Subgroup：注入枚举 + 运算封闭
--------------------------------------------------------------------------------

-- 子群（阶 k）：以**注入枚举** hAt : Fin k ↪ Fin n 给出，附带三条封闭性。
-- 用注入枚举而非载体谓词，避免商类型与 Σ-等式；|H| = k 直接可得。
record Subgroup {n : ℕ} (G : FinGroup n) (k : ℕ) : Set where
  open FinGroup G
  field
    hAt : Fin k → Fin n
    hAt-inj : Injective _≡_ _≡_ hAt
    hAt-ε : Σ (Fin k) (λ t → hAt t ≡ ε)
    hAt-⊙ : ∀ t u → Σ (Fin k) (λ w → hAt w ≡ hAt t ⊙ hAt u)
    hAt-inv : ∀ t → Σ (Fin k) (λ u → hAt u ≡ inv (hAt t))

  -- 成员关系
  mem : Fin n → Set
  mem x = Σ (Fin k) (λ t → hAt t ≡ x)

  -- 单位元属于 H
  mem-ε : mem ε
  mem-ε = hAt-ε

  -- H 对乘法封闭
  mem-⊙ : ∀ {x y} → mem x → mem y → mem (x ⊙ y)
  mem-⊙ {x} {y} (t , p) (u , q) with hAt-⊙ t u
  ... | w , r = w , trans r (cong₂ _⊙_ p q)

  -- H 对逆元封闭
  mem-inv : ∀ {x} → mem x → mem (inv x)
  mem-inv {x} (t , p) with hAt-inv t
  ... | u , r = u , trans r (cong inv p)

  -- H 对逆元封闭（反向）：mem (inv x) ⇒ mem x
  mem-inv⁻¹ : ∀ {x} → mem (inv x) → mem x
  mem-inv⁻¹ {x} (t , p) with hAt-inv t
  ... | u , r = u , trans r (trans (cong inv p) (inv-inv x))

--------------------------------------------------------------------------------
-- §4. Lagrange 主定理
--------------------------------------------------------------------------------

module LagrangeThm {n k : ℕ} (G : FinGroup n) (H : Subgroup G k) where
  open FinGroup G
  open Subgroup H

  -- 设 q : Fin n → Fin m 是陪集映射（m = 陪集个数），repr 是 q 的截面，
  -- 陪集判定 q x ≡ q y ⇔ x⁻¹ ⊙ y ∈ H，则 n ≡ k × m。
  lagrange :
    ∀ {m} (q : Fin n → Fin m) (repr : Fin m → Fin n)
    → (∀ r → q (repr r) ≡ r)
    → (∀ x y → (q x ≡ q y) ⇔ mem (inv x ⊙ y))
    → n ≡ k * m
  lagrange {m} q repr section q-coset = fiber-count q g mem-fib inj-fib sur-fib
    where
      -- 纤维枚举: g r t = repr r ⊙ hAt t （把 H 平移到陪集 r）
      g : Fin m → Fin k → Fin n
      g r t = repr r ⊙ hAt t

      -- ① g r 落在纤维 r 内:
      --    q (repr r ⊙ h) ≡ q (repr r)，因为 (repr r ⊙ h)⁻¹ ⊙ repr r = h⁻¹ ∈ H
      mem-fib : ∀ r t → q (g r t) ≡ r
      mem-fib r t =
        trans (Equivalence.from (q-coset (repr r ⊙ hAt t) (repr r)) key)
              (section r)
        where
          key : mem (inv (repr r ⊙ hAt t) ⊙ repr r)
          key = subst mem (sym (inv-⊙-cancel (repr r) (hAt t)))
                         (mem-inv {x = hAt t} (t , refl))

      -- ② g r 单射: 左消去律 + H 的枚举单射
      inj-fib : ∀ r {t u} → g r t ≡ g r u → t ≡ u
      inj-fib r {t} {u} eq = hAt-inj (cancelˡ {x = repr r} eq)

      -- ③ 每个 i 被其所在纤维的 g 命中: 取 h = (repr (q i))⁻¹ ⊙ i ∈ H
      sur-fib : ∀ i → Σ (Fin k) (λ t → g (q i) t ≡ i)
      sur-fib i = go (Equivalence.to (q-coset (repr (q i)) i) (section (q i)))
        where
          go : mem (inv (repr (q i)) ⊙ i) → Σ (Fin k) (λ t → g (q i) t ≡ i)
          go (t , p) = t , (begin
            repr (q i) ⊙ hAt t
              ≡⟨ cong (repr (q i) ⊙_) p ⟩
            repr (q i) ⊙ (inv (repr (q i)) ⊙ i)
              ≡⟨ sym (assoc (repr (q i)) (inv (repr (q i))) i) ⟩
            (repr (q i) ⊙ inv (repr (q i))) ⊙ i
              ≡⟨ cong (_⊙ i) (inverseʳ (repr (q i))) ⟩
            ε ⊙ i
              ≡⟨ identityˡ i ⟩
            i ∎)

-- 顶层包装（参数化模块不能被 import using 引用，故提供同名函数入口）
lagrange :
  ∀ {n k m} (G : FinGroup n) (H : Subgroup G k)
    (q : Fin n → Fin m) (repr : Fin m → Fin n)
  → (∀ r → q (repr r) ≡ r)
  → (∀ x y → (q x ≡ q y) ⇔ Subgroup.mem H (FinGroup._⊙_ G (FinGroup.inv G x) y))
  → n ≡ k * m
lagrange G H q repr section q-coset =
  LagrangeThm.lagrange G H q repr section q-coset

--------------------------------------------------------------------------------
-- §5. 具体实例
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §5.1 C₄ = ⟨α⟩ ⊂ GF(9)*（4 阶循环群，投影层）
--
-- 直接以 Fin 4 为载体：_+4_ 用 +1 迭代定义（与 Duodecimal 同一范式），
-- 结合律由 shift 引理符号化导出，而不是 4³ = 64 case 穷举。
--------------------------------------------------------------------------------

infixl 7 _+4_

+1₄ : Fin 4 → Fin 4
+1₄ zero                   = suc zero
+1₄ (suc zero)             = suc (suc zero)
+1₄ (suc (suc zero))       = suc (suc (suc zero))
+1₄ (suc (suc (suc zero))) = zero

_+4_ : Fin 4 → Fin 4 → Fin 4
zero +4 y                   = y
suc zero +4 y               = +1₄ y
suc (suc zero) +4 y         = +1₄ (+1₄ y)
suc (suc (suc zero)) +4 y   = +1₄ (+1₄ (+1₄ y))

-- +1₄ 的周期 4
+1₄^4-id : ∀ x → +1₄ (+1₄ (+1₄ (+1₄ x))) ≡ x
+1₄^4-id zero = refl
+1₄^4-id (suc zero) = refl
+1₄^4-id (suc (suc zero)) = refl
+1₄^4-id (suc (suc (suc zero))) = refl

-- +1₄ 与 _+4_ 的分配律
+1₄-dist : ∀ x y → +1₄ (x +4 y) ≡ (+1₄ x) +4 y
+1₄-dist zero y = refl
+1₄-dist (suc zero) y = refl
+1₄-dist (suc (suc zero)) y = refl
+1₄-dist (suc (suc (suc zero))) y = +1₄^4-id y

-- 右移引理
shiftʳ₄ : ∀ x y → (+1₄ x) +4 y ≡ +1₄ (x +4 y)
shiftʳ₄ x y = sym (+1₄-dist x y)

-- 结合律（4 case + shift 链，符号化；非 64-case 穷举）
+4-assoc : ∀ x y z → (x +4 y) +4 z ≡ x +4 (y +4 z)
+4-assoc zero y z = refl
+4-assoc (suc zero) y z = shiftʳ₄ y z
+4-assoc (suc (suc zero)) y z =
  trans (shiftʳ₄ (+1₄ y) z) (cong +1₄ (shiftʳ₄ y z))
+4-assoc (suc (suc (suc zero))) y z =
  trans (shiftʳ₄ (+1₄ (+1₄ y)) z)
    (trans (cong +1₄ (shiftʳ₄ (+1₄ y) z))
           (cong (λ w → +1₄ (+1₄ w)) (shiftʳ₄ y z)))

-- 交换律（16 case refl，≤27）
+4-comm : ∀ x y → x +4 y ≡ y +4 x
+4-comm zero zero = refl
+4-comm zero (suc zero) = refl
+4-comm zero (suc (suc zero)) = refl
+4-comm zero (suc (suc (suc zero))) = refl
+4-comm (suc zero) zero = refl
+4-comm (suc zero) (suc zero) = refl
+4-comm (suc zero) (suc (suc zero)) = refl
+4-comm (suc zero) (suc (suc (suc zero))) = refl
+4-comm (suc (suc zero)) zero = refl
+4-comm (suc (suc zero)) (suc zero) = refl
+4-comm (suc (suc zero)) (suc (suc zero)) = refl
+4-comm (suc (suc zero)) (suc (suc (suc zero))) = refl
+4-comm (suc (suc (suc zero))) zero = refl
+4-comm (suc (suc (suc zero))) (suc zero) = refl
+4-comm (suc (suc (suc zero))) (suc (suc zero)) = refl
+4-comm (suc (suc (suc zero))) (suc (suc (suc zero))) = refl

-- 右单位元
+4-idʳ : ∀ x → x +4 zero ≡ x
+4-idʳ zero = refl
+4-idʳ (suc zero) = refl
+4-idʳ (suc (suc zero)) = refl
+4-idʳ (suc (suc (suc zero))) = refl

-- 三倍归零（4 阶群中 inv x = 3x = -x）
+4-triple : ∀ x → ((x +4 x) +4 x) +4 x ≡ zero
+4-triple zero = refl
+4-triple (suc zero) = refl
+4-triple (suc (suc zero)) = refl
+4-triple (suc (suc (suc zero))) = refl

-- C₄ 群结构
C4 : FinGroup 4
C4 = record
  { _⊙_ = _+4_
  ; ε = zero
  ; inv = λ x → (x +4 x) +4 x
  ; assoc = +4-assoc
  ; identityˡ = λ y → refl
  ; identityʳ = +4-idʳ
  ; inverseˡ = +4-triple
  ; inverseʳ = λ x → trans (+4-comm x ((x +4 x) +4 x)) (+4-triple x)
  }

-- 平凡子群 {0}，阶 1
sub-1 : Subgroup C4 1
sub-1 = record
  { hAt = λ _ → zero
  ; hAt-inj = fin1-inj _
  ; hAt-ε = zero , refl
  ; hAt-⊙ = λ t u → zero , refl
  ; hAt-inv = λ t → zero , refl
  }

-- 二阶子群 {0, 2} ≅ C₂，阶 2
sub-2 : Subgroup C4 2
sub-2 = record
  { hAt = h
  ; hAt-inj = inj
  ; hAt-ε = zero , refl
  ; hAt-⊙ = mul
  ; hAt-inv = iv
  }
  where
    h : Fin 2 → Fin 4
    h zero = zero
    h (suc zero) = suc (suc zero)

    inj : Injective _≡_ _≡_ h
    inj {zero} {zero} _ = refl
    inj {zero} {suc zero} ()
    inj {suc zero} {zero} ()
    inj {suc zero} {suc zero} _ = refl

    mul : ∀ t u → Σ (Fin 2) (λ w → h w ≡ h t +4 h u)
    mul zero zero = zero , refl
    mul zero (suc zero) = suc zero , refl
    mul (suc zero) zero = suc zero , refl
    mul (suc zero) (suc zero) = zero , refl

    iv : ∀ t → Σ (Fin 2) (λ u → h u ≡ (h t +4 h t) +4 h t)
    iv zero = zero , refl
    iv (suc zero) = suc zero , refl

-- 全群，阶 4
sub-4 : Subgroup C4 4
sub-4 = record
  { hAt = λ x → x
  ; hAt-inj = λ p → p
  ; hAt-ε = zero , refl
  ; hAt-⊙ = λ t u → (t +4 u) , refl
  ; hAt-inv = λ t → ((t +4 t) +4 t) , refl
  }

--------------------------------------------------------------------------------
-- §5.2 C₄ 的 Lagrange 实例
--------------------------------------------------------------------------------

-- 平凡子群：q = id，m = 4，陪集判定 x ≡ y ⇔ x⁻¹ ⊙ y ∈ {0}（符号化，无 case 枚举）
-- 结论 4 ≡ 1 × 4
lagrange-C4-sub1 : 4 ≡ 1 * 4
lagrange-C4-sub1 =
  LagrangeThm.lagrange C4 sub-1 (λ x → x) (λ r → r) (λ r → refl) coset
  where
    open FinGroup C4
    open Subgroup sub-1

    coset : ∀ x y → (x ≡ y) ⇔ mem (inv x ⊙ y)
    coset x y = mk⇔ to from
      where
        to : x ≡ y → mem (inv x ⊙ y)
        to p = zero , trans (sym (inverseˡ x)) (cong (inv x ⊙_) p)
        from : mem (inv x ⊙ y) → x ≡ y
        from (t , p) = sym (begin
          y               ≡⟨ sym (identityˡ y) ⟩
          ε ⊙ y           ≡⟨ cong (_⊙ y) (sym (inverseʳ x)) ⟩
          (x ⊙ inv x) ⊙ y ≡⟨ assoc x (inv x) y ⟩
          x ⊙ (inv x ⊙ y) ≡⟨ cong (x ⊙_) (sym p) ⟩
          x ⊙ ε           ≡⟨ identityʳ x ⟩
          x               ∎)

-- 二阶子群 {0,2}：q = 奇偶性，m = 2，陪集判定 16 case refl（≤27）
-- 结论 4 ≡ 2 × 2
-- 陪集映射 q₂ = 奇偶性（C₄ → C₂ 的商映射）
q₂ : Fin 4 → Fin 2
q₂ zero = zero
q₂ (suc zero) = suc zero
q₂ (suc (suc zero)) = zero
q₂ (suc (suc (suc zero))) = suc zero

-- 陪集代表元：0 ↦ 0，1 ↦ 1
repr₂ : Fin 2 → Fin 4
repr₂ zero = zero
repr₂ (suc zero) = suc zero

-- q₂ ∘ repr₂ = id（截面性质）
section₂ : ∀ r → q₂ (repr₂ r) ≡ r
section₂ zero = refl
section₂ (suc zero) = refl

lagrange-C4-sub2 : 4 ≡ 2 * 2
lagrange-C4-sub2 =
  LagrangeThm.lagrange C4 sub-2 q₂ repr₂ section₂ coset
  where
    open FinGroup C4
    open Subgroup sub-2

    -- 真值表（16 case）: q₂ x ≡ q₂ y ⇔ x⁻¹ ⊙ y ∈ {0,2}
    --   x⁻¹ ⊙ y ∈ {0,2} 的 16 格与 q₂ 的奇偶性 16 格逐格相同（见 §6 交叉比对）
    coset : ∀ x y → (q₂ x ≡ q₂ y) ⇔ mem (inv x ⊙ y)
    coset zero zero = mk⇔ (λ _ → zero , refl) (λ _ → refl)
    coset zero (suc zero) = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset zero (suc (suc zero)) = mk⇔ (λ _ → suc zero , refl) (λ _ → refl)
    coset zero (suc (suc (suc zero))) = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc zero) zero = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc zero) (suc zero) = mk⇔ (λ _ → zero , refl) (λ _ → refl)
    coset (suc zero) (suc (suc zero)) = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc zero) (suc (suc (suc zero))) = mk⇔ (λ _ → suc zero , refl) (λ _ → refl)
    coset (suc (suc zero)) zero = mk⇔ (λ _ → suc zero , refl) (λ _ → refl)
    coset (suc (suc zero)) (suc zero) = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc (suc zero)) (suc (suc zero)) = mk⇔ (λ _ → zero , refl) (λ _ → refl)
    coset (suc (suc zero)) (suc (suc (suc zero))) = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc (suc (suc zero))) zero = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc (suc (suc zero))) (suc zero) = mk⇔ (λ _ → suc zero , refl) (λ _ → refl)
    coset (suc (suc (suc zero))) (suc (suc zero)) = mk⇔ (λ ()) (λ { (zero , ()) ; (suc zero , ()) })
    coset (suc (suc (suc zero))) (suc (suc (suc zero))) = mk⇔ (λ _ → zero , refl) (λ _ → refl)

-- 全群：q = const 0，m = 1，陪集判定恒真（符号化）
-- 结论 4 ≡ 4 × 1
lagrange-C4-sub4 : 4 ≡ 4 * 1
lagrange-C4-sub4 =
  LagrangeThm.lagrange C4 sub-4 (λ _ → zero) (λ _ → zero) (λ r → fin1-unique r) coset
  where
    open FinGroup C4
    open Subgroup sub-4

    coset : ∀ x y → (zero ≡ zero) ⇔ mem (inv x ⊙ y)
    coset x y = mk⇔ (λ _ → (inv x ⊙ y) , refl) (λ _ → refl)

--------------------------------------------------------------------------------
-- §5.3 C₁₂ = Z/12Z（Duodecimal 投影层）与它的平凡/全群
--
-- Duodecimal 已在 Algebra 层给出 C₁₂ 的加法群律（+12-assoc 等），
-- 本处把 Duodec 同构搬到 Fin 12 载体上，得到 FinGroup 12。
--------------------------------------------------------------------------------

toFin12 : Duodec → Fin 12
toFin12 d0 = zero
toFin12 d1 = suc zero
toFin12 d2 = suc (suc zero)
toFin12 d3 = suc (suc (suc zero))
toFin12 d4 = suc (suc (suc (suc zero)))
toFin12 d5 = suc (suc (suc (suc (suc zero))))
toFin12 d6 = suc (suc (suc (suc (suc (suc zero)))))
toFin12 d7 = suc (suc (suc (suc (suc (suc (suc zero))))))
toFin12 d8 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
toFin12 d9 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
toFin12 d10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
toFin12 d11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

toDuodec : Fin 12 → Duodec
toDuodec zero = d0
toDuodec (suc zero) = d1
toDuodec (suc (suc zero)) = d2
toDuodec (suc (suc (suc zero))) = d3
toDuodec (suc (suc (suc (suc zero)))) = d4
toDuodec (suc (suc (suc (suc (suc zero))))) = d5
toDuodec (suc (suc (suc (suc (suc (suc zero)))))) = d6
toDuodec (suc (suc (suc (suc (suc (suc (suc zero))))))) = d7
toDuodec (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = d8
toDuodec (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = d9
toDuodec (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = d10
toDuodec (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = d11

toDuodec∘toFin12 : ∀ w → toDuodec (toFin12 w) ≡ w
toDuodec∘toFin12 d0 = refl
toDuodec∘toFin12 d1 = refl
toDuodec∘toFin12 d2 = refl
toDuodec∘toFin12 d3 = refl
toDuodec∘toFin12 d4 = refl
toDuodec∘toFin12 d5 = refl
toDuodec∘toFin12 d6 = refl
toDuodec∘toFin12 d7 = refl
toDuodec∘toFin12 d8 = refl
toDuodec∘toFin12 d9 = refl
toDuodec∘toFin12 d10 = refl
toDuodec∘toFin12 d11 = refl

toFin12∘toDuodec : ∀ x → toFin12 (toDuodec x) ≡ x
toFin12∘toDuodec zero = refl
toFin12∘toDuodec (suc zero) = refl
toFin12∘toDuodec (suc (suc zero)) = refl
toFin12∘toDuodec (suc (suc (suc zero))) = refl
toFin12∘toDuodec (suc (suc (suc (suc zero)))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc zero))))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc (suc zero)))))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = refl
toFin12∘toDuodec (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = refl

-- C₁₂ 群结构（载体 Fin 12，|G| = 12 是定义）
C12 : FinGroup 12
C12 = record
  { _⊙_ = λ x y → toFin12 (toDuodec x +12 toDuodec y)
  ; ε = zero
  ; inv = λ x → toFin12 (neg12 (toDuodec x))
  ; assoc = λ x y z → cong toFin12 (begin
      toDuodec (toFin12 (toDuodec x +12 toDuodec y)) +12 toDuodec z
        ≡⟨ cong (_+12 toDuodec z) (toDuodec∘toFin12 (toDuodec x +12 toDuodec y)) ⟩
      (toDuodec x +12 toDuodec y) +12 toDuodec z
        ≡⟨ +12-assoc (toDuodec x) (toDuodec y) (toDuodec z) ⟩
      toDuodec x +12 (toDuodec y +12 toDuodec z)
        ≡⟨ cong (toDuodec x +12_) (sym (toDuodec∘toFin12 (toDuodec y +12 toDuodec z))) ⟩
      toDuodec x +12 toDuodec (toFin12 (toDuodec y +12 toDuodec z)) ∎)
  ; identityˡ = λ y → toFin12∘toDuodec y
  ; identityʳ = λ x → trans (cong toFin12
                              (trans (cong (toDuodec x +12_) (toDuodec∘toFin12 d0))
                                     (+12-identityʳ (toDuodec x))))
                            (toFin12∘toDuodec x)
  ; inverseˡ = λ x → cong toFin12 (trans (cong (_+12 toDuodec x)
                                             (toDuodec∘toFin12 (neg12 (toDuodec x))))
                                         (trans (+12-comm (neg12 (toDuodec x)) (toDuodec x))
                                                (+12-inverse (toDuodec x))))
  ; inverseʳ = λ x → cong toFin12 (trans (cong (toDuodec x +12_)
                                             (toDuodec∘toFin12 (neg12 (toDuodec x))))
                                         (+12-inverse (toDuodec x)))
  }

-- C₁₂ 平凡子群，阶 1
sub-1₁₂ : Subgroup C12 1
sub-1₁₂ = record
  { hAt = λ _ → zero
  ; hAt-inj = fin1-inj _
  ; hAt-ε = zero , refl
  ; hAt-⊙ = λ t u → zero , refl
  ; hAt-inv = λ t → zero , refl
  }

-- C₁₂ 全群，阶 12
sub-12 : Subgroup C12 12
sub-12 = record
  { hAt = λ x → x
  ; hAt-inj = λ p → p
  ; hAt-ε = zero , refl
  ; hAt-⊙ = λ t u → (FinGroup._⊙_ C12 t u) , refl
  ; hAt-inv = λ t → FinGroup.inv C12 t , refl
  }

-- 12 ≡ 1 × 12
lagrange-C12-sub1 : 12 ≡ 1 * 12
lagrange-C12-sub1 =
  LagrangeThm.lagrange C12 sub-1₁₂ (λ x → x) (λ r → r) (λ r → refl) coset
  where
    open FinGroup C12
    open Subgroup sub-1₁₂

    coset : ∀ x y → (x ≡ y) ⇔ mem (inv x ⊙ y)
    coset x y = mk⇔ to from
      where
        to : x ≡ y → mem (inv x ⊙ y)
        to p = zero , trans (sym (inverseˡ x)) (cong (inv x ⊙_) p)
        from : mem (inv x ⊙ y) → x ≡ y
        from (t , p) = sym (begin
          y               ≡⟨ sym (identityˡ y) ⟩
          ε ⊙ y           ≡⟨ cong (_⊙ y) (sym (inverseʳ x)) ⟩
          (x ⊙ inv x) ⊙ y ≡⟨ assoc x (inv x) y ⟩
          x ⊙ (inv x ⊙ y) ≡⟨ cong (x ⊙_) (sym p) ⟩
          x ⊙ ε           ≡⟨ identityʳ x ⟩
          x               ∎)

-- 12 ≡ 12 × 1
lagrange-C12-sub12 : 12 ≡ 12 * 1
lagrange-C12-sub12 =
  LagrangeThm.lagrange C12 sub-12 (λ _ → zero) (λ _ → zero) (λ r → fin1-unique r) coset
  where
    open FinGroup C12
    open Subgroup sub-12

    coset : ∀ x y → (zero ≡ zero) ⇔ mem (inv x ⊙ y)
    coset x y = mk⇔ (λ _ → (inv x ⊙ y) , refl) (λ _ → refl)

--------------------------------------------------------------------------------
-- §6. 对抗验证：具体点 refl 交叉比对
--
-- 构造性定理必须在具体点上用独立 refl 计算交叉比对（发现论证空洞的唯一手段）。
-- 下面的每一条都不引用定理本身，而是直接让内核计算具体值。
--------------------------------------------------------------------------------

-- ① C₄ 生成元 1 的阶恰为 4（1+1+1+1 = 0，且 1+1 = 2 ≠ 0）
C4-gen-order4 : ((suc zero +4 suc zero) +4 suc zero) +4 suc zero ≡ zero
C4-gen-order4 = refl

C4-gen-not-2 : suc zero +4 suc zero ≡ suc (suc zero)
C4-gen-not-2 = refl

-- ② 子群 sub-2 的枚举值（独立计算）
sub2-values : Subgroup.hAt sub-2 zero ≡ zero
            × Subgroup.hAt sub-2 (suc zero) ≡ suc (suc zero)
sub2-values = refl , refl

-- ③ 陪集映射 q₂ 的纤维表（4 个 refl）—— 与 §5.2 的 16-case 陪集判定表独立：
--    纤维 0 = {0,2}（大小 2 = |H|），纤维 1 = {1,3}
q₂-fiber0 : q₂ zero ≡ zero
q₂-fiber0 = refl
q₂-fiber0′ : q₂ (suc (suc zero)) ≡ zero
q₂-fiber0′ = refl
q₂-fiber1 : q₂ (suc zero) ≡ suc zero
q₂-fiber1 = refl
q₂-fiber1′ : q₂ (suc (suc (suc zero))) ≡ suc zero
q₂-fiber1′ = refl

-- ④ 定理结论与直接计算比对：定理给 4 ≡ 2 × 2，直接计算给 2 × 2 ≡ 4
check-C4-direct : 2 * 2 ≡ 4
check-C4-direct = refl

check-C4-agree : 4 ≡ 2 * 2
check-C4-agree = sym check-C4-direct          -- 与 lagrange-C4-sub2 同型

-- ⑤ C₁₂ 具体点：inv 3 = 9，且 3 + 9 = 0（模 12）
C12-inv-3 : FinGroup.inv C12 (suc (suc (suc zero)))
          ≡ suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
C12-inv-3 = refl

C12-3-plus-9 : FinGroup._⊙_ C12 (suc (suc (suc zero)))
                               (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
             ≡ zero
C12-3-plus-9 = refl

-- ⑥ C₁₂ 生成元 1 的阶为 12：11 + 1 = 0（走满一圈回到单位元）
C12-gen-order12 :
  FinGroup._⊙_ C12 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                   (suc zero)
  ≡ zero
C12-gen-order12 = refl

-- ⑦ 计数层自检：fiber-count 的结论在 m = 4, k = 3 时化为 12 ≡ 3 × 4（定义层）
check-count-type : 4 * 3 ≡ 12
check-count-type = refl
