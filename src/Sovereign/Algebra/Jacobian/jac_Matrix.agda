{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_Matrix
-- GF(3) 上 2×2 矩阵的完整线性代数理论
--
-- 核心原则：
--   1. GF(3)有限域上优先穷举法（策略A），利用代数引理压缩case数
--   2. det(AB)=det(A)det(B) 是核心定理，连接矩阵乘法与行列式
--   3. 逆矩阵通过伴随矩阵构造：M⁻¹ = (det M)⁻¹·adj(M)
--   4. 可逆性 ⇔ det≠0（有限域上重言式）
--
-- 包含：乘法逆元、矩阵运算、行列式乘法性、伴随矩阵、逆矩阵、秩分类

module Sovereign.Algebra.Jacobian.jac_Matrix where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥; ⊥-elim)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate
        ; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse
        ; ⊗-assoc; ⊗-comm; ⊗-identityˡ; ⊗-identityʳ
        ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ)
open import Sovereign.Algebra.Jacobian.jac_Discrete
open import Sovereign.Algebra.GF27 using (negate-⊕; negate-⊗)
  using (Mat2; det2; I2; GF3²)

--------------------------------------------------------------------------------
-- §1. GF(3) 乘法逆元
--------------------------------------------------------------------------------

-- GF(3) 中 T₁⁻¹ = T₁, T₂⁻¹ = T₂, T₀ 无逆元（定义返回 T₀ 为全函数）
-- [策略A] 3-case refl
inv : Trit → Trit
inv T₀ = T₀
inv T₁ = T₁
inv T₂ = T₂

-- [策略A] 2-case refl: T₁⊗T₁=T₁, T₂⊗T₂=T₁
inv-correct : ∀ x → x ≢ T₀ → (x ⊗ inv x) ≡ T₁
inv-correct T₀ x≢0 = ⊥-elim (x≢0 refl)
inv-correct T₁ _   = refl
inv-correct T₂ _   = refl

--------------------------------------------------------------------------------
-- §2. 矩阵运算
--------------------------------------------------------------------------------

-- 逐元素加法
mat-add : Mat2 → Mat2 → Mat2
mat-add ((a , b) , (c , d)) ((e , f) , (g , h)) =
  ((a ⊕ e , b ⊕ f) , (c ⊕ g , d ⊕ h))

-- 标量乘
mat-scale : Trit → Mat2 → Mat2
mat-scale k ((a , b) , (c , d)) = ((k ⊗ a , k ⊗ b) , (k ⊗ c , k ⊗ d))

-- 矩阵乘法
mat-mul : Mat2 → Mat2 → Mat2
mat-mul ((a , b) , (c , d)) ((e , f) , (g , h)) =
  (((a ⊗ e) ⊕ (b ⊗ g) , (a ⊗ f) ⊕ (b ⊗ h)) , ((c ⊗ e) ⊕ (d ⊗ g) , (c ⊗ f) ⊕ (d ⊗ h)))

-- 矩阵×向量
mat-vec : Mat2 → GF3² → GF3²
mat-vec ((a , b) , (c , d)) (x , y) = ((a ⊗ x) ⊕ (b ⊗ y) , (c ⊗ x) ⊕ (d ⊗ y))

-- 私有辅助: T₂⊗T₂≡T₁ (refl)
private
  T₂⊗T₂≡T₁ : T₂ ⊗ T₂ ≡ T₁
  T₂⊗T₂≡T₁ = refl

-- 私有辅助: (T₂⊗x)⊗(T₂⊗y) ≡ x⊗y  [策略A] 9-case refl
  t2-t2-helper : ∀ x y → (T₂ ⊗ x) ⊗ (T₂ ⊗ y) ≡ x ⊗ y
  t2-t2-helper T₀ T₀ = refl; t2-t2-helper T₀ T₁ = refl; t2-t2-helper T₀ T₂ = refl
  t2-t2-helper T₁ T₀ = refl; t2-t2-helper T₁ T₁ = refl; t2-t2-helper T₁ T₂ = refl
  t2-t2-helper T₂ T₀ = refl; t2-t2-helper T₂ T₁ = refl; t2-t2-helper T₂ T₂ = refl

-- 私有辅助: negate x ≡ T₂ ⊗ x  [策略A] 3-case refl
  negate-x≡T₂⊗x : ∀ x → negate x ≡ T₂ ⊗ x
  negate-x≡T₂⊗x T₀ = refl
  negate-x≡T₂⊗x T₁ = refl
  negate-x≡T₂⊗x T₂ = refl

-- 私有辅助: negate x ⊗ y ≡ negate (x ⊗ y)  [策略B] 代数链
  negate-⊗-left : ∀ x y → negate x ⊗ y ≡ negate (x ⊗ y)
  negate-⊗-left x y = begin
    negate x ⊗ y         ≡⟨ cong (λ z → z ⊗ y) (negate-x≡T₂⊗x x) ⟩
    (T₂ ⊗ x) ⊗ y        ≡⟨ ⊗-assoc T₂ x y ⟩
    T₂ ⊗ (x ⊗ y)         ≡⟨ sym (negate-x≡T₂⊗x (x ⊗ y)) ⟩
    negate (x ⊗ y)       ∎ where open ≡-Reasoning

-- 私有辅助: x ⊗ negate y ≡ negate (x ⊗ y)  [策略B] 代数链
  negate-⊗-right : ∀ x y → x ⊗ negate y ≡ negate (x ⊗ y)
  negate-⊗-right x y = begin
    x ⊗ negate y         ≡⟨ cong (x ⊗_) (negate-x≡T₂⊗x y) ⟩
    x ⊗ (T₂ ⊗ y)        ≡⟨ sym (⊗-assoc x T₂ y) ⟩
    (x ⊗ T₂) ⊗ y        ≡⟨ cong (_⊗ y) (⊗-comm x T₂) ⟩
    (T₂ ⊗ x) ⊗ y        ≡⟨ ⊗-assoc T₂ x y ⟩
    T₂ ⊗ (x ⊗ y)         ≡⟨ sym (negate-x≡T₂⊗x (x ⊗ y)) ⟩
    negate (x ⊗ y)       ∎ where open ≡-Reasoning

-- 私有辅助: mat-scale T₁ M ≡ M  [策略B] 代数链
  mat-scale-one : ∀ M → mat-scale T₁ M ≡ M
  mat-scale-one ((a , b) , (c , d)) =
    cong₂ _,_ (cong₂ _,_ (⊗-identityˡ a) (⊗-identityˡ b))
              (cong₂ _,_ (⊗-identityˡ c) (⊗-identityˡ d))

-- 私有辅助: mat-scale a (mat-scale b M) ≡ mat-scale (a ⊗ b) M  [策略B] 代数链
  mat-scale-compose : ∀ a b M → mat-scale a (mat-scale b M) ≡ mat-scale (a ⊗ b) M
  mat-scale-compose a b ((c , d) , (e , f)) =
    cong₂ _,_ (cong₂ _,_ (sym (⊗-assoc a b c)) (sym (⊗-assoc a b d)))
              (cong₂ _,_ (sym (⊗-assoc a b e)) (sym (⊗-assoc a b f)))

-- 私有辅助: mat-mul M (mat-scale k N) ≡ mat-scale k (mat-mul M N)  [策略B] 代数链
  mat-mul-scale-commute : ∀ M k N → mat-mul M (mat-scale k N) ≡ mat-scale k (mat-mul M N)
  mat-mul-scale-commute ((a , b) , (c , d)) k ((e , f) , (g , h)) =
    cong₂ _,_ (cong₂ _,_ eq11 eq12) (cong₂ _,_ eq21 eq22)
    where
    eq11 : (a ⊗ (k ⊗ e)) ⊕ (b ⊗ (k ⊗ g)) ≡ k ⊗ ((a ⊗ e) ⊕ (b ⊗ g))
    eq11 = begin
      (a ⊗ (k ⊗ e)) ⊕ (b ⊗ (k ⊗ g))
        ≡⟨ cong₂ _⊕_ (sym (⊗-assoc a k e)) (sym (⊗-assoc b k g)) ⟩
      ((a ⊗ k) ⊗ e) ⊕ ((b ⊗ k) ⊗ g)
        ≡⟨ cong₂ (λ x y → (x ⊗ e) ⊕ (y ⊗ g)) (⊗-comm a k) (⊗-comm b k) ⟩
      ((k ⊗ a) ⊗ e) ⊕ ((k ⊗ b) ⊗ g)
        ≡⟨ cong₂ _⊕_ (⊗-assoc k a e) (⊗-assoc k b g) ⟩
      (k ⊗ (a ⊗ e)) ⊕ (k ⊗ (b ⊗ g))
        ≡⟨ sym (⊗-distribˡ-⊕ k (a ⊗ e) (b ⊗ g)) ⟩
      k ⊗ ((a ⊗ e) ⊕ (b ⊗ g))
      ∎ where open ≡-Reasoning

    eq12 : (a ⊗ (k ⊗ f)) ⊕ (b ⊗ (k ⊗ h)) ≡ k ⊗ ((a ⊗ f) ⊕ (b ⊗ h))
    eq12 = begin
      (a ⊗ (k ⊗ f)) ⊕ (b ⊗ (k ⊗ h))
        ≡⟨ cong₂ _⊕_ (sym (⊗-assoc a k f)) (sym (⊗-assoc b k h)) ⟩
      ((a ⊗ k) ⊗ f) ⊕ ((b ⊗ k) ⊗ h)
        ≡⟨ cong₂ (λ x y → (x ⊗ f) ⊕ (y ⊗ h)) (⊗-comm a k) (⊗-comm b k) ⟩
      ((k ⊗ a) ⊗ f) ⊕ ((k ⊗ b) ⊗ h)
        ≡⟨ cong₂ _⊕_ (⊗-assoc k a f) (⊗-assoc k b h) ⟩
      (k ⊗ (a ⊗ f)) ⊕ (k ⊗ (b ⊗ h))
        ≡⟨ sym (⊗-distribˡ-⊕ k (a ⊗ f) (b ⊗ h)) ⟩
      k ⊗ ((a ⊗ f) ⊕ (b ⊗ h))
      ∎ where open ≡-Reasoning

    eq21 : (c ⊗ (k ⊗ e)) ⊕ (d ⊗ (k ⊗ g)) ≡ k ⊗ ((c ⊗ e) ⊕ (d ⊗ g))
    eq21 = begin
      (c ⊗ (k ⊗ e)) ⊕ (d ⊗ (k ⊗ g))
        ≡⟨ cong₂ _⊕_ (sym (⊗-assoc c k e)) (sym (⊗-assoc d k g)) ⟩
      ((c ⊗ k) ⊗ e) ⊕ ((d ⊗ k) ⊗ g)
        ≡⟨ cong₂ (λ x y → (x ⊗ e) ⊕ (y ⊗ g)) (⊗-comm c k) (⊗-comm d k) ⟩
      ((k ⊗ c) ⊗ e) ⊕ ((k ⊗ d) ⊗ g)
        ≡⟨ cong₂ _⊕_ (⊗-assoc k c e) (⊗-assoc k d g) ⟩
      (k ⊗ (c ⊗ e)) ⊕ (k ⊗ (d ⊗ g))
        ≡⟨ sym (⊗-distribˡ-⊕ k (c ⊗ e) (d ⊗ g)) ⟩
      k ⊗ ((c ⊗ e) ⊕ (d ⊗ g))
      ∎ where open ≡-Reasoning

    eq22 : (c ⊗ (k ⊗ f)) ⊕ (d ⊗ (k ⊗ h)) ≡ k ⊗ ((c ⊗ f) ⊕ (d ⊗ h))
    eq22 = begin
      (c ⊗ (k ⊗ f)) ⊕ (d ⊗ (k ⊗ h))
        ≡⟨ cong₂ _⊕_ (sym (⊗-assoc c k f)) (sym (⊗-assoc d k h)) ⟩
      ((c ⊗ k) ⊗ f) ⊕ ((d ⊗ k) ⊗ h)
        ≡⟨ cong₂ (λ x y → (x ⊗ f) ⊕ (y ⊗ h)) (⊗-comm c k) (⊗-comm d k) ⟩
      ((k ⊗ c) ⊗ f) ⊕ ((k ⊗ d) ⊗ h)
        ≡⟨ cong₂ _⊕_ (⊗-assoc k c f) (⊗-assoc k d h) ⟩
      (k ⊗ (c ⊗ f)) ⊕ (k ⊗ (d ⊗ h))
        ≡⟨ sym (⊗-distribˡ-⊕ k (c ⊗ f) (d ⊗ h)) ⟩
      k ⊗ ((c ⊗ f) ⊕ (d ⊗ h))
      ∎ where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §3. 行列式性质
--------------------------------------------------------------------------------

-- det(I₂) = T₁  [策略A] refl
det-I : det2 I2 ≡ T₁
det-I = refl

-- det(k·M) = k²·det(M)  [策略A+B] 3-case for k, algebra for T₂ case
det-scale : ∀ k M → det2 (mat-scale k M) ≡ ((k ⊗ k) ⊗ det2 M)
det-scale T₀ _ = refl
det-scale T₁ M = begin
  det2 (mat-scale T₁ M)  ≡⟨ cong det2 (mat-scale-one M) ⟩
  det2 M                 ≡⟨ sym (⊗-identityˡ (det2 M)) ⟩
  T₁ ⊗ det2 M            ≡⟨ cong (λ z → z ⊗ det2 M) (sym (⊗-identityˡ T₁)) ⟩
  (T₁ ⊗ T₁) ⊗ det2 M    ∎ where open ≡-Reasoning
det-scale T₂ ((a , b) , (c , d)) = begin
  det2 (mat-scale T₂ ((a , b) , (c , d)))
    ≡⟨⟩
  ((T₂ ⊗ a) ⊗ (T₂ ⊗ d)) ⊕ negate ((T₂ ⊗ b) ⊗ (T₂ ⊗ c))
    ≡⟨ cong₂ (λ u v → u ⊕ negate v) (t2-t2-helper a d) (t2-t2-helper b c) ⟩
  (a ⊗ d) ⊕ negate (b ⊗ c)
    ≡⟨⟩
  det2 ((a , b) , (c , d))
    ≡⟨ sym (⊗-identityˡ (det2 ((a , b) , (c , d)))) ⟩
  T₁ ⊗ det2 ((a , b) , (c , d))
    ≡⟨ cong (λ z → z ⊗ det2 ((a , b) , (c , d))) (sym T₂⊗T₂≡T₁) ⟩
  (T₂ ⊗ T₂) ⊗ det2 ((a , b) , (c , d))
  ∎ where open ≡-Reasoning

-- det(AB) = det(A)·det(B)  [策略A] 全穷举 6561-case refl
-- 展开: ∀a,b,c,d,e,f,g,h∈{T₀,T₁,T₂}, 3^8=6561种组合
idp : ∀ {A : Set} (x : A) → x ≡ x
idp x = refl

-- ⊕ 的四项重排 (local 版, 与 LieAlgebra.swap4 同型; Trit 的 ⊕ 也是 level 20 非结合)
⊕-swap4 : ∀ A B C D → (A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (B ⊕ D)
⊕-swap4 A B C D =
  trans (sym (⊕-assoc (A ⊕ B) C D))
    (trans (cong (λ u → u ⊕ D) (⊕-assoc A B C))
      (trans (cong (λ u → (A ⊕ u) ⊕ D) (⊕-comm B C))
        (trans (cong (λ u → u ⊕ D) (sym (⊕-assoc A C B)))
          (⊕-assoc (A ⊕ C) B D))))

-- 四重分配: (p⊕q)⊗(r⊕s) ≡ ((p⊗r)⊕(p⊗s)) ⊕ ((q⊗r)⊕(q⊗s))
-- 注: 只需 ⊗-distribʳ-⊕ + 两次 ⊗-distribˡ-⊕, **不需要 swap4**
⊗-dist4 : ∀ p q r s →
  (p ⊕ q) ⊗ (r ⊕ s) ≡ ((p ⊗ r) ⊕ (p ⊗ s)) ⊕ ((q ⊗ r) ⊕ (q ⊗ s))
⊗-dist4 p q r s =
  trans (⊗-distribʳ-⊕ p q (r ⊕ s))
        (cong₂ (λ (u v : Trit) → u ⊕ v)
               (⊗-distribˡ-⊕ p r s) (⊗-distribˡ-⊕ q r s))

-- negate 穿过四项和
negate-4 : ∀ p q r s →
  negate ((p ⊕ q) ⊕ (r ⊕ s)) ≡ ((negate p ⊕ negate q) ⊕ (negate r ⊕ negate s))
negate-4 p q r s =
  trans (negate-⊕ (p ⊕ q) (r ⊕ s))
        (cong₂ (λ (u v : Trit) → u ⊕ v) (negate-⊕ p q) (negate-⊕ r s))

--------------------------------------------------------------------------------
-- 步骤 A: LHS 展开 —— det2 (mat-mul A B) 的 8 项形
--   det2 ((a,b),(c,d)) = (a⊗d) ⊕ negate (b⊗c);  mat-mul 分量式
--   ⇒ det2(mat-mul) 定义层即 ((ae⊕bg)⊗(cf⊕dh)) ⊕ negate((af⊕bh)⊗(ce⊕dg))
--   两次 ⊗-dist4 + negate-4 即得 8 项 (X 部分 4 项 ⊕ 负部分 4 项)
--------------------------------------------------------------------------------

lhs-expand : ∀ a b c d e f g h →
  (((a ⊗ e) ⊕ (b ⊗ g)) ⊗ ((c ⊗ f) ⊕ (d ⊗ h)))
    ⊕ negate (((a ⊗ f) ⊕ (b ⊗ h)) ⊗ ((c ⊗ e) ⊕ (d ⊗ g)))
  ≡ ((((a ⊗ e) ⊗ (c ⊗ f)) ⊕ ((a ⊗ e) ⊗ (d ⊗ h)))
     ⊕ (((b ⊗ g) ⊗ (c ⊗ f)) ⊕ ((b ⊗ g) ⊗ (d ⊗ h))))
    ⊕ (((negate ((a ⊗ f) ⊗ (c ⊗ e))) ⊕ (negate ((a ⊗ f) ⊗ (d ⊗ g))))
       ⊕ ((negate ((b ⊗ h) ⊗ (c ⊗ e))) ⊕ (negate ((b ⊗ h) ⊗ (d ⊗ g)))))
lhs-expand a b c d e f g h =
  trans (cong₂ (λ (u v : Trit) → u ⊕ v)
               (⊗-dist4 (a ⊗ e) (b ⊗ g) (c ⊗ f) (d ⊗ h))
               (cong negate (⊗-dist4 (a ⊗ f) (b ⊗ h) (c ⊗ e) (d ⊗ g))))
        (cong (λ u →
                 ((((a ⊗ e) ⊗ (c ⊗ f)) ⊕ ((a ⊗ e) ⊗ (d ⊗ h)))
                  ⊕ (((b ⊗ g) ⊗ (c ⊗ f)) ⊕ ((b ⊗ g) ⊗ (d ⊗ h)))) ⊕ u)
              (negate-4 ((a ⊗ f) ⊗ (c ⊗ e)) ((a ⊗ f) ⊗ (d ⊗ g))
                        ((b ⊗ h) ⊗ (c ⊗ e)) ((b ⊗ h) ⊗ (d ⊗ g))))

--------------------------------------------------------------------------------
-- 步骤 A2: 三个 ⊗/negate 交换律 (≤ 9 case 穷举, 远低于 27 上限)
--   negate-⊗ 只给出 negate (p⊗q) ≡ (negate p) ⊗ q, 还需另两个方向
--------------------------------------------------------------------------------

⊗-negʳ : ∀ p q → p ⊗ negate q ≡ negate (p ⊗ q)
⊗-negʳ T₀ q = refl
⊗-negʳ T₁ T₀ = refl
⊗-negʳ T₁ T₁ = refl
⊗-negʳ T₁ T₂ = refl
⊗-negʳ T₂ T₀ = refl
⊗-negʳ T₂ T₁ = refl
⊗-negʳ T₂ T₂ = refl

⊗-neg-neg : ∀ p q → negate p ⊗ negate q ≡ p ⊗ q
⊗-neg-neg T₀ T₀ = refl
⊗-neg-neg T₀ T₁ = refl
⊗-neg-neg T₀ T₂ = refl
⊗-neg-neg T₁ T₀ = refl
⊗-neg-neg T₁ T₁ = refl
⊗-neg-neg T₁ T₂ = refl
⊗-neg-neg T₂ T₀ = refl
⊗-neg-neg T₂ T₁ = refl
⊗-neg-neg T₂ T₂ = refl

--------------------------------------------------------------------------------
-- 步骤 B: RHS 展开 —— det2 A ⊗ det2 B 的 4 项形
--   ((a⊗d) ⊕ neg(b⊗c)) ⊗ ((e⊗h) ⊕ neg(f⊗g))
--   ⊗-dist4 ⇒ ((ad⊗eh) ⊕ (ad⊗neg(fg))) ⊕ ((neg(bc)⊗eh) ⊕ (neg(bc)⊗neg(fg)))
--   再把 neg 提到积外 ⇒ ((ad⊗eh) ⊕ neg(ad⊗fg)) ⊕ (neg(bc⊗eh) ⊕ (bc⊗fg))
--------------------------------------------------------------------------------

rhs-expand : ∀ a b c d e f g h →
  ((a ⊗ d) ⊕ negate (b ⊗ c)) ⊗ ((e ⊗ h) ⊕ negate (f ⊗ g))
  ≡ ((((a ⊗ d) ⊗ (e ⊗ h)) ⊕ (negate ((a ⊗ d) ⊗ (f ⊗ g))))
     ⊕ ((negate ((b ⊗ c) ⊗ (e ⊗ h))) ⊕ ((b ⊗ c) ⊗ (f ⊗ g))))
rhs-expand a b c d e f g h =
  trans (⊗-dist4 (a ⊗ d) (negate (b ⊗ c)) (e ⊗ h) (negate (f ⊗ g)))
        (cong₂ (λ (u v : Trit) → u ⊕ v)
               (cong₂ (λ (u v : Trit) → u ⊕ v)
                      (refl {x = (a ⊗ d) ⊗ (e ⊗ h)})
                      (⊗-negʳ (a ⊗ d) (f ⊗ g)))
               (cong₂ (λ (u v : Trit) → u ⊕ v)
                      (sym (negate-⊗ (b ⊗ c) (e ⊗ h)))
                      (⊗-neg-neg (b ⊗ c) (f ⊗ g))))

--------------------------------------------------------------------------------
-- 步骤 C: LHS 8 项 → RHS 4 项 (两对相消 + 四项对应)
--   相消对: (t1, neg t1) 与 (t4, neg t4), 其中
--     t1 = (ae)⊗(cf), neg t1 = neg((af)⊗(ce))  —— 靠 m1: (af)⊗(ce) ≡ (ae)⊗(cf)
--     t4 = (bg)⊗(dh), neg t4 = neg((bh)⊗(dg))  —— 靠 m2: (bh)⊗(dg) ≡ (bg)⊗(dh)
--   剩下 4 项 t2,n2,n3,t3 分别对应 r1,r2,r3,r4 (靠 m3..m6 = ⊗-4swap)
--------------------------------------------------------------------------------

-- 四元交换: (p⊗q)⊗(r⊗s) ≡ (p⊗r)⊗(q⊗s)
⊗-4swap : ∀ p q r s → (p ⊗ q) ⊗ (r ⊗ s) ≡ (p ⊗ r) ⊗ (q ⊗ s)
⊗-4swap p q r s =
  trans (⊗-assoc p q (r ⊗ s))
    (trans (cong (p ⊗_) (sym (⊗-assoc q r s)))
      (trans (cong (λ u → p ⊗ (u ⊗ s)) (⊗-comm q r))
        (trans (cong (p ⊗_) (⊗-assoc r q s))
          (sym (⊗-assoc p r (q ⊗ s))))))

det-mul-core : ∀ a b c d e f g h →
  (((a ⊗ e) ⊕ (b ⊗ g)) ⊗ ((c ⊗ f) ⊕ (d ⊗ h)))
    ⊕ negate (((a ⊗ f) ⊕ (b ⊗ h)) ⊗ ((c ⊗ e) ⊕ (d ⊗ g)))
  ≡ ((a ⊗ d) ⊕ negate (b ⊗ c)) ⊗ ((e ⊗ h) ⊕ negate (f ⊗ g))
det-mul-core a b c d e f g h =
  trans (lhs-expand a b c d e f g h)
        (trans collapse (sym (rhs-expand a b c d e f g h)))
  where
    t1 = (a ⊗ e) ⊗ (c ⊗ f)
    t2 = (a ⊗ e) ⊗ (d ⊗ h)
    t3 = (b ⊗ g) ⊗ (c ⊗ f)
    t4 = (b ⊗ g) ⊗ (d ⊗ h)
    n1 = negate ((a ⊗ f) ⊗ (c ⊗ e))
    n2 = negate ((a ⊗ f) ⊗ (d ⊗ g))
    n3 = negate ((b ⊗ h) ⊗ (c ⊗ e))
    n4 = negate ((b ⊗ h) ⊗ (d ⊗ g))
    r1 = (a ⊗ d) ⊗ (e ⊗ h)
    r2 = negate ((a ⊗ d) ⊗ (f ⊗ g))
    r3 = negate ((b ⊗ c) ⊗ (e ⊗ h))
    r4 = (b ⊗ c) ⊗ (f ⊗ g)
    X' = t2 ⊕ (t3 ⊕ t4)
    N1 = n2 ⊕ (n3 ⊕ negate t4)
    X'' = t3 ⊕ t2
    N'' = n3 ⊕ n2

    -- 四项乘积等式
    m1 : (a ⊗ f) ⊗ (c ⊗ e) ≡ t1
    m1 = trans (cong ((a ⊗ f) ⊗_) (⊗-comm c e))
          (trans (⊗-4swap a f e c) (cong ((a ⊗ e) ⊗_) (⊗-comm f c)))
    m2 : (b ⊗ h) ⊗ (d ⊗ g) ≡ t4
    m2 = trans (cong ((b ⊗ h) ⊗_) (⊗-comm d g))
          (trans (⊗-4swap b h g d) (cong ((b ⊗ g) ⊗_) (⊗-comm h d)))

    -- S1: n1 → neg t1, n4 → neg t4
    s1 = cong (λ u → ((t1 ⊕ t2) ⊕ (t3 ⊕ t4)) ⊕ u)
              (cong₂ (λ (u v : Trit) → u ⊕ v)
                     (cong₂ (λ (u v : Trit) → u ⊕ v) (cong negate m1) (idp n2))
                     (cong₂ (λ (u v : Trit) → u ⊕ v) (idp n3) (cong negate m2)))
    -- S2: 两侧展开成 t1 ⊕ X' 与 neg t1 ⊕ N'
    s2 = cong (λ u → u ⊕ ((negate t1 ⊕ n2) ⊕ (n3 ⊕ negate t4)))
              (⊕-assoc t1 t2 (t3 ⊕ t4))
    s2b = cong (λ u → ((t1 ⊕ X') ⊕ u))
               (⊕-assoc (negate t1) n2 (n3 ⊕ negate t4))
    -- S3+S4: swap4 把 (t1, neg t1) 拉到相邻, 再用 ⊕-inverse 相消
    s3 = trans (⊕-swap4 t1 X' (negate t1) N1)
               (trans (cong (λ u → u ⊕ (X' ⊕ N1)) (⊕-inverse t1))
                      (⊕-identityˡ (X' ⊕ N1)))
    -- S5: 把 t4 与 neg t4 提到各自头部
    a5 : X' ≡ t4 ⊕ (t3 ⊕ t2)
    a5 = trans (cong (t2 ⊕_) (⊕-comm t3 t4))
           (trans (⊕-comm t2 (t4 ⊕ t3)) (⊕-assoc t4 t3 t2))
    b5 : N1 ≡ negate t4 ⊕ (n3 ⊕ n2)
    b5 = trans (cong (n2 ⊕_) (⊕-comm n3 (negate t4)))
           (trans (⊕-comm n2 (negate t4 ⊕ n3)) (⊕-assoc (negate t4) n3 n2))
    s5 = cong₂ (λ (u v : Trit) → u ⊕ v) a5 b5
    -- S6+S7: 第二次 swap4 + 相消
    s6 = trans (⊕-swap4 t4 (t3 ⊕ t2) (negate t4) (n3 ⊕ n2))
               (trans (cong (λ u → u ⊕ (X'' ⊕ N'')) (⊕-inverse t4))
                      (⊕-identityˡ (X'' ⊕ N'')))
    -- S8: 余下四项逐个对应到 r 的写法
    s8 = cong₂ (λ (u v : Trit) → u ⊕ v)
               (cong₂ (λ (u v : Trit) → u ⊕ v)
                      (trans (⊗-4swap b g c f) (cong ((b ⊗ c) ⊗_) (⊗-comm g f)))
                      (⊗-4swap a e d h))
               (cong₂ (λ (u v : Trit) → u ⊕ v)
                      (trans (cong negate (⊗-4swap b h c e))
                             (cong (λ w → negate ((b ⊗ c) ⊗ w)) (⊗-comm h e)))
                      (cong negate (⊗-4swap a f d g)))
    -- S9: (r4⊕r1)⊕(r3⊕r2) → (r1⊕r2)⊕(r3⊕r4)
    s9 = trans (cong₂ (λ (u v : Trit) → u ⊕ v) (⊕-comm r4 r1) (⊕-comm r3 r2))
               (trans (⊕-swap4 r1 r4 r2 r3)
                      (cong (λ u → (r1 ⊕ r2) ⊕ u) (⊕-comm r4 r3)))

    collapse : (((t1 ⊕ t2) ⊕ (t3 ⊕ t4)) ⊕ ((n1 ⊕ n2) ⊕ (n3 ⊕ n4)))
             ≡ ((r1 ⊕ r2) ⊕ (r3 ⊕ r4))
    collapse = trans s1 (trans s2 (trans s2b (trans s3 (trans s5 (trans s6 (trans s8 s9))))))


det-mul : ∀ A B → det2 (mat-mul A B) ≡ (det2 A ⊗ det2 B)
-- 【构造化 2026-09-13】原 6561 = 81×81 条 with/refl 子句已删除, 改由 det-mul-core 一行实例化
det-mul ((a , b) , (c , d)) ((e , f) , (g , h)) = det-mul-core a b c d e f g h

--------------------------------------------------------------------------------
-- §4. 矩阵转置与伴随
--------------------------------------------------------------------------------

-- 转置
transpose : Mat2 → Mat2
transpose ((a , b) , (c , d)) = ((a , c) , (b , d))

-- det(Mᵀ) = det(M)  [策略B] 代数链: 只需⊗-comm交换b⊗c→c⊗b
transpose-det : ∀ M → det2 (transpose M) ≡ det2 M
transpose-det ((a , b) , (c , d)) = begin
  det2 (transpose ((a , b) , (c , d)))
    ≡⟨⟩
  det2 ((a , c) , (b , d))
    ≡⟨⟩
  (a ⊗ d) ⊕ negate (c ⊗ b)
    ≡⟨ cong (λ x → (a ⊗ d) ⊕ negate x) (⊗-comm c b) ⟩
  (a ⊗ d) ⊕ negate (b ⊗ c)
    ≡⟨⟩
  det2 ((a , b) , (c , d))
  ∎ where open ≡-Reasoning

-- 伴随矩阵: adj((a,b),(c,d)) = ((d, -b), (-c, a))
adjugate : Mat2 → Mat2
adjugate ((a , b) , (c , d)) = ((d , negate b) , (negate c , a))


--------------------------------------------------------------------------------
-- §5. 逆矩阵定义
--------------------------------------------------------------------------------

-- 可逆性定义: 存在N使得 M·N = I 且 N·M = I
invertible : Mat2 → Set
invertible M = Σ Mat2 (λ N → mat-mul M N ≡ I2 × mat-mul N M ≡ I2)

-- 逆矩阵: M⁻¹ = (det M)⁻¹ · adj(M)  (当 det M ≠ 0)
inverse : (M : Mat2) → det2 M ≢ T₀ → Mat2
inverse M _ = mat-scale (inv (det2 M)) (adjugate M)

--------------------------------------------------------------------------------
-- §5b. 伴随矩阵恒等式
--------------------------------------------------------------------------------

-- M·adj(M) = ((det M, T₀), (T₀, det M))  [策略A] 81-case refl
adj-mul-right : ∀ M → mat-mul M (adjugate M) ≡ ((det2 M , T₀) , (T₀ , det2 M))
adj-mul-right ((T₀ , T₀) , (T₀ , T₀)) = refl
adj-mul-right ((T₀ , T₀) , (T₀ , T₁)) = refl
adj-mul-right ((T₀ , T₀) , (T₀ , T₂)) = refl
adj-mul-right ((T₀ , T₀) , (T₁ , T₀)) = refl
adj-mul-right ((T₀ , T₀) , (T₁ , T₁)) = refl
adj-mul-right ((T₀ , T₀) , (T₁ , T₂)) = refl
adj-mul-right ((T₀ , T₀) , (T₂ , T₀)) = refl
adj-mul-right ((T₀ , T₀) , (T₂ , T₁)) = refl
adj-mul-right ((T₀ , T₀) , (T₂ , T₂)) = refl
adj-mul-right ((T₀ , T₁) , (T₀ , T₀)) = refl
adj-mul-right ((T₀ , T₁) , (T₀ , T₁)) = refl
adj-mul-right ((T₀ , T₁) , (T₀ , T₂)) = refl
adj-mul-right ((T₀ , T₁) , (T₁ , T₀)) = refl
adj-mul-right ((T₀ , T₁) , (T₁ , T₁)) = refl
adj-mul-right ((T₀ , T₁) , (T₁ , T₂)) = refl
adj-mul-right ((T₀ , T₁) , (T₂ , T₀)) = refl
adj-mul-right ((T₀ , T₁) , (T₂ , T₁)) = refl
adj-mul-right ((T₀ , T₁) , (T₂ , T₂)) = refl
adj-mul-right ((T₀ , T₂) , (T₀ , T₀)) = refl
adj-mul-right ((T₀ , T₂) , (T₀ , T₁)) = refl
adj-mul-right ((T₀ , T₂) , (T₀ , T₂)) = refl
adj-mul-right ((T₀ , T₂) , (T₁ , T₀)) = refl
adj-mul-right ((T₀ , T₂) , (T₁ , T₁)) = refl
adj-mul-right ((T₀ , T₂) , (T₁ , T₂)) = refl
adj-mul-right ((T₀ , T₂) , (T₂ , T₀)) = refl
adj-mul-right ((T₀ , T₂) , (T₂ , T₁)) = refl
adj-mul-right ((T₀ , T₂) , (T₂ , T₂)) = refl
adj-mul-right ((T₁ , T₀) , (T₀ , T₀)) = refl
adj-mul-right ((T₁ , T₀) , (T₀ , T₁)) = refl
adj-mul-right ((T₁ , T₀) , (T₀ , T₂)) = refl
adj-mul-right ((T₁ , T₀) , (T₁ , T₀)) = refl
adj-mul-right ((T₁ , T₀) , (T₁ , T₁)) = refl
adj-mul-right ((T₁ , T₀) , (T₁ , T₂)) = refl
adj-mul-right ((T₁ , T₀) , (T₂ , T₀)) = refl
adj-mul-right ((T₁ , T₀) , (T₂ , T₁)) = refl
adj-mul-right ((T₁ , T₀) , (T₂ , T₂)) = refl
adj-mul-right ((T₁ , T₁) , (T₀ , T₀)) = refl
adj-mul-right ((T₁ , T₁) , (T₀ , T₁)) = refl
adj-mul-right ((T₁ , T₁) , (T₀ , T₂)) = refl
adj-mul-right ((T₁ , T₁) , (T₁ , T₀)) = refl
adj-mul-right ((T₁ , T₁) , (T₁ , T₁)) = refl
adj-mul-right ((T₁ , T₁) , (T₁ , T₂)) = refl
adj-mul-right ((T₁ , T₁) , (T₂ , T₀)) = refl
adj-mul-right ((T₁ , T₁) , (T₂ , T₁)) = refl
adj-mul-right ((T₁ , T₁) , (T₂ , T₂)) = refl
adj-mul-right ((T₁ , T₂) , (T₀ , T₀)) = refl
adj-mul-right ((T₁ , T₂) , (T₀ , T₁)) = refl
adj-mul-right ((T₁ , T₂) , (T₀ , T₂)) = refl
adj-mul-right ((T₁ , T₂) , (T₁ , T₀)) = refl
adj-mul-right ((T₁ , T₂) , (T₁ , T₁)) = refl
adj-mul-right ((T₁ , T₂) , (T₁ , T₂)) = refl
adj-mul-right ((T₁ , T₂) , (T₂ , T₀)) = refl
adj-mul-right ((T₁ , T₂) , (T₂ , T₁)) = refl
adj-mul-right ((T₁ , T₂) , (T₂ , T₂)) = refl
adj-mul-right ((T₂ , T₀) , (T₀ , T₀)) = refl
adj-mul-right ((T₂ , T₀) , (T₀ , T₁)) = refl
adj-mul-right ((T₂ , T₀) , (T₀ , T₂)) = refl
adj-mul-right ((T₂ , T₀) , (T₁ , T₀)) = refl
adj-mul-right ((T₂ , T₀) , (T₁ , T₁)) = refl
adj-mul-right ((T₂ , T₀) , (T₁ , T₂)) = refl
adj-mul-right ((T₂ , T₀) , (T₂ , T₀)) = refl
adj-mul-right ((T₂ , T₀) , (T₂ , T₁)) = refl
adj-mul-right ((T₂ , T₀) , (T₂ , T₂)) = refl
adj-mul-right ((T₂ , T₁) , (T₀ , T₀)) = refl
adj-mul-right ((T₂ , T₁) , (T₀ , T₁)) = refl
adj-mul-right ((T₂ , T₁) , (T₀ , T₂)) = refl
adj-mul-right ((T₂ , T₁) , (T₁ , T₀)) = refl
adj-mul-right ((T₂ , T₁) , (T₁ , T₁)) = refl
adj-mul-right ((T₂ , T₁) , (T₁ , T₂)) = refl
adj-mul-right ((T₂ , T₁) , (T₂ , T₀)) = refl
adj-mul-right ((T₂ , T₁) , (T₂ , T₁)) = refl
adj-mul-right ((T₂ , T₁) , (T₂ , T₂)) = refl
adj-mul-right ((T₂ , T₂) , (T₀ , T₀)) = refl
adj-mul-right ((T₂ , T₂) , (T₀ , T₁)) = refl
adj-mul-right ((T₂ , T₂) , (T₀ , T₂)) = refl
adj-mul-right ((T₂ , T₂) , (T₁ , T₀)) = refl
adj-mul-right ((T₂ , T₂) , (T₁ , T₁)) = refl
adj-mul-right ((T₂ , T₂) , (T₁ , T₂)) = refl
adj-mul-right ((T₂ , T₂) , (T₂ , T₀)) = refl
adj-mul-right ((T₂ , T₂) , (T₂ , T₁)) = refl
adj-mul-right ((T₂ , T₂) , (T₂ , T₂)) = refl

-- adj(M)·M = ((det M, T₀), (T₀, det M))  [策略A] 81-case refl
adj-mul : ∀ M → mat-mul (adjugate M) M ≡ ((det2 M , T₀) , (T₀ , det2 M))
adj-mul ((T₀ , T₀) , (T₀ , T₀)) = refl
adj-mul ((T₀ , T₀) , (T₀ , T₁)) = refl
adj-mul ((T₀ , T₀) , (T₀ , T₂)) = refl
adj-mul ((T₀ , T₀) , (T₁ , T₀)) = refl
adj-mul ((T₀ , T₀) , (T₁ , T₁)) = refl
adj-mul ((T₀ , T₀) , (T₁ , T₂)) = refl
adj-mul ((T₀ , T₀) , (T₂ , T₀)) = refl
adj-mul ((T₀ , T₀) , (T₂ , T₁)) = refl
adj-mul ((T₀ , T₀) , (T₂ , T₂)) = refl
adj-mul ((T₀ , T₁) , (T₀ , T₀)) = refl
adj-mul ((T₀ , T₁) , (T₀ , T₁)) = refl
adj-mul ((T₀ , T₁) , (T₀ , T₂)) = refl
adj-mul ((T₀ , T₁) , (T₁ , T₀)) = refl
adj-mul ((T₀ , T₁) , (T₁ , T₁)) = refl
adj-mul ((T₀ , T₁) , (T₁ , T₂)) = refl
adj-mul ((T₀ , T₁) , (T₂ , T₀)) = refl
adj-mul ((T₀ , T₁) , (T₂ , T₁)) = refl
adj-mul ((T₀ , T₁) , (T₂ , T₂)) = refl
adj-mul ((T₀ , T₂) , (T₀ , T₀)) = refl
adj-mul ((T₀ , T₂) , (T₀ , T₁)) = refl
adj-mul ((T₀ , T₂) , (T₀ , T₂)) = refl
adj-mul ((T₀ , T₂) , (T₁ , T₀)) = refl
adj-mul ((T₀ , T₂) , (T₁ , T₁)) = refl
adj-mul ((T₀ , T₂) , (T₁ , T₂)) = refl
adj-mul ((T₀ , T₂) , (T₂ , T₀)) = refl
adj-mul ((T₀ , T₂) , (T₂ , T₁)) = refl
adj-mul ((T₀ , T₂) , (T₂ , T₂)) = refl
adj-mul ((T₁ , T₀) , (T₀ , T₀)) = refl
adj-mul ((T₁ , T₀) , (T₀ , T₁)) = refl
adj-mul ((T₁ , T₀) , (T₀ , T₂)) = refl
adj-mul ((T₁ , T₀) , (T₁ , T₀)) = refl
adj-mul ((T₁ , T₀) , (T₁ , T₁)) = refl
adj-mul ((T₁ , T₀) , (T₁ , T₂)) = refl
adj-mul ((T₁ , T₀) , (T₂ , T₀)) = refl
adj-mul ((T₁ , T₀) , (T₂ , T₁)) = refl
adj-mul ((T₁ , T₀) , (T₂ , T₂)) = refl
adj-mul ((T₁ , T₁) , (T₀ , T₀)) = refl
adj-mul ((T₁ , T₁) , (T₀ , T₁)) = refl
adj-mul ((T₁ , T₁) , (T₀ , T₂)) = refl
adj-mul ((T₁ , T₁) , (T₁ , T₀)) = refl
adj-mul ((T₁ , T₁) , (T₁ , T₁)) = refl
adj-mul ((T₁ , T₁) , (T₁ , T₂)) = refl
adj-mul ((T₁ , T₁) , (T₂ , T₀)) = refl
adj-mul ((T₁ , T₁) , (T₂ , T₁)) = refl
adj-mul ((T₁ , T₁) , (T₂ , T₂)) = refl
adj-mul ((T₁ , T₂) , (T₀ , T₀)) = refl
adj-mul ((T₁ , T₂) , (T₀ , T₁)) = refl
adj-mul ((T₁ , T₂) , (T₀ , T₂)) = refl
adj-mul ((T₁ , T₂) , (T₁ , T₀)) = refl
adj-mul ((T₁ , T₂) , (T₁ , T₁)) = refl
adj-mul ((T₁ , T₂) , (T₁ , T₂)) = refl
adj-mul ((T₁ , T₂) , (T₂ , T₀)) = refl
adj-mul ((T₁ , T₂) , (T₂ , T₁)) = refl
adj-mul ((T₁ , T₂) , (T₂ , T₂)) = refl
adj-mul ((T₂ , T₀) , (T₀ , T₀)) = refl
adj-mul ((T₂ , T₀) , (T₀ , T₁)) = refl
adj-mul ((T₂ , T₀) , (T₀ , T₂)) = refl
adj-mul ((T₂ , T₀) , (T₁ , T₀)) = refl
adj-mul ((T₂ , T₀) , (T₁ , T₁)) = refl
adj-mul ((T₂ , T₀) , (T₁ , T₂)) = refl
adj-mul ((T₂ , T₀) , (T₂ , T₀)) = refl
adj-mul ((T₂ , T₀) , (T₂ , T₁)) = refl
adj-mul ((T₂ , T₀) , (T₂ , T₂)) = refl
adj-mul ((T₂ , T₁) , (T₀ , T₀)) = refl
adj-mul ((T₂ , T₁) , (T₀ , T₁)) = refl
adj-mul ((T₂ , T₁) , (T₀ , T₂)) = refl
adj-mul ((T₂ , T₁) , (T₁ , T₀)) = refl
adj-mul ((T₂ , T₁) , (T₁ , T₁)) = refl
adj-mul ((T₂ , T₁) , (T₁ , T₂)) = refl
adj-mul ((T₂ , T₁) , (T₂ , T₀)) = refl
adj-mul ((T₂ , T₁) , (T₂ , T₁)) = refl
adj-mul ((T₂ , T₁) , (T₂ , T₂)) = refl
adj-mul ((T₂ , T₂) , (T₀ , T₀)) = refl
adj-mul ((T₂ , T₂) , (T₀ , T₁)) = refl
adj-mul ((T₂ , T₂) , (T₀ , T₂)) = refl
adj-mul ((T₂ , T₂) , (T₁ , T₀)) = refl
adj-mul ((T₂ , T₂) , (T₁ , T₁)) = refl
adj-mul ((T₂ , T₂) , (T₁ , T₂)) = refl
adj-mul ((T₂ , T₂) , (T₂ , T₀)) = refl
adj-mul ((T₂ , T₂) , (T₂ , T₁)) = refl
adj-mul ((T₂ , T₂) , (T₂ , T₂)) = refl

-- M·M⁻¹ = I  [策略A] 81-case: ⊥-elim for det=T₀, refl otherwise
inverse-correct : ∀ M (d≢0 : det2 M ≢ T₀) → mat-mul M (inverse M d≢0) ≡ I2
inverse-correct ((T₀ , T₀) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₀ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₀ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₁ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₁ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₁ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₂ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₂ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₀) , (T₂ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₁) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₁) , (T₀ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₁) , (T₀ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₁) , (T₁ , T₀)) d≢0 = refl
inverse-correct ((T₀ , T₁) , (T₁ , T₁)) d≢0 = refl
inverse-correct ((T₀ , T₁) , (T₁ , T₂)) d≢0 = refl
inverse-correct ((T₀ , T₁) , (T₂ , T₀)) d≢0 = refl
inverse-correct ((T₀ , T₁) , (T₂ , T₁)) d≢0 = refl
inverse-correct ((T₀ , T₁) , (T₂ , T₂)) d≢0 = refl
inverse-correct ((T₀ , T₂) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₂) , (T₀ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₂) , (T₀ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₀ , T₂) , (T₁ , T₀)) d≢0 = refl
inverse-correct ((T₀ , T₂) , (T₁ , T₁)) d≢0 = refl
inverse-correct ((T₀ , T₂) , (T₁ , T₂)) d≢0 = refl
inverse-correct ((T₀ , T₂) , (T₂ , T₀)) d≢0 = refl
inverse-correct ((T₀ , T₂) , (T₂ , T₁)) d≢0 = refl
inverse-correct ((T₀ , T₂) , (T₂ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₀) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₀) , (T₀ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₀) , (T₀ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₀) , (T₁ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₀) , (T₁ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₀) , (T₁ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₀) , (T₂ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₀) , (T₂ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₀) , (T₂ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₁) , (T₀ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₀ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₁ , T₀)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₁ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₁) , (T₁ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₂ , T₀)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₂ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₁) , (T₂ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₂) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₂) , (T₀ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₂) , (T₀ , T₂)) d≢0 = refl
inverse-correct ((T₁ , T₂) , (T₁ , T₀)) d≢0 = refl
inverse-correct ((T₁ , T₂) , (T₁ , T₁)) d≢0 = refl
inverse-correct ((T₁ , T₂) , (T₁ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₂) , (T₂ , T₀)) d≢0 = refl
inverse-correct ((T₁ , T₂) , (T₂ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₁ , T₂) , (T₂ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₀) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₀) , (T₀ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₀) , (T₀ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₀) , (T₁ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₀) , (T₁ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₀) , (T₁ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₀) , (T₂ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₀) , (T₂ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₀) , (T₂ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₁) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₁) , (T₀ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₁) , (T₀ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₁) , (T₁ , T₀)) d≢0 = refl
inverse-correct ((T₂ , T₁) , (T₁ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₁) , (T₁ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₁) , (T₂ , T₀)) d≢0 = refl
inverse-correct ((T₂ , T₁) , (T₂ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₁) , (T₂ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₂) , (T₀ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₀ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₁ , T₀)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₁ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct ((T₂ , T₂) , (T₁ , T₂)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₂ , T₀)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₂ , T₁)) d≢0 = refl
inverse-correct ((T₂ , T₂) , (T₂ , T₂)) d≢0 = ⊥-elim (d≢0 refl)

-- M⁻¹·M = I  [策略A] 81-case: ⊥-elim for det=T₀, refl otherwise
inverse-correct' : ∀ M (d≢0 : det2 M ≢ T₀) → mat-mul (inverse M d≢0) M ≡ I2
inverse-correct' ((T₀ , T₀) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₀ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₀ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₁ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₁ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₁ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₂ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₂ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₀) , (T₂ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₁) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₁) , (T₀ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₁) , (T₀ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₁) , (T₁ , T₀)) d≢0 = refl
inverse-correct' ((T₀ , T₁) , (T₁ , T₁)) d≢0 = refl
inverse-correct' ((T₀ , T₁) , (T₁ , T₂)) d≢0 = refl
inverse-correct' ((T₀ , T₁) , (T₂ , T₀)) d≢0 = refl
inverse-correct' ((T₀ , T₁) , (T₂ , T₁)) d≢0 = refl
inverse-correct' ((T₀ , T₁) , (T₂ , T₂)) d≢0 = refl
inverse-correct' ((T₀ , T₂) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₂) , (T₀ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₂) , (T₀ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₀ , T₂) , (T₁ , T₀)) d≢0 = refl
inverse-correct' ((T₀ , T₂) , (T₁ , T₁)) d≢0 = refl
inverse-correct' ((T₀ , T₂) , (T₁ , T₂)) d≢0 = refl
inverse-correct' ((T₀ , T₂) , (T₂ , T₀)) d≢0 = refl
inverse-correct' ((T₀ , T₂) , (T₂ , T₁)) d≢0 = refl
inverse-correct' ((T₀ , T₂) , (T₂ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₀) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₀) , (T₀ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₀) , (T₀ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₀) , (T₁ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₀) , (T₁ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₀) , (T₁ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₀) , (T₂ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₀) , (T₂ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₀) , (T₂ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₁) , (T₀ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₀ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₁ , T₀)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₁ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₁) , (T₁ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₂ , T₀)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₂ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₁) , (T₂ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₂) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₂) , (T₀ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₂) , (T₀ , T₂)) d≢0 = refl
inverse-correct' ((T₁ , T₂) , (T₁ , T₀)) d≢0 = refl
inverse-correct' ((T₁ , T₂) , (T₁ , T₁)) d≢0 = refl
inverse-correct' ((T₁ , T₂) , (T₁ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₂) , (T₂ , T₀)) d≢0 = refl
inverse-correct' ((T₁ , T₂) , (T₂ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₁ , T₂) , (T₂ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₀) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₀) , (T₀ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₀) , (T₀ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₀) , (T₁ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₀) , (T₁ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₀) , (T₁ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₀) , (T₂ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₀) , (T₂ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₀) , (T₂ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₁) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₁) , (T₀ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₁) , (T₀ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₁) , (T₁ , T₀)) d≢0 = refl
inverse-correct' ((T₂ , T₁) , (T₁ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₁) , (T₁ , T₂)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₁) , (T₂ , T₀)) d≢0 = refl
inverse-correct' ((T₂ , T₁) , (T₂ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₁) , (T₂ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₀ , T₀)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₂) , (T₀ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₀ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₁ , T₀)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₁ , T₁)) d≢0 = ⊥-elim (d≢0 refl)
inverse-correct' ((T₂ , T₂) , (T₁ , T₂)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₂ , T₀)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₂ , T₁)) d≢0 = refl
inverse-correct' ((T₂ , T₂) , (T₂ , T₂)) d≢0 = ⊥-elim (d≢0 refl)

--------------------------------------------------------------------------------
-- §6. 关键定理: det ≠ 0 ⟺ 可逆
--------------------------------------------------------------------------------

-- det≠0 ⇒ 可逆  [策略B] 构造逆矩阵
det≠0→invertible : ∀ M → det2 M ≢ T₀ → invertible M
det≠0→invertible M d≢0 = inverse M d≢0 , (inverse-correct M d≢0 , inverse-correct' M d≢0)

-- 可逆 ⇒ det≠0  [策略B] 利用det-mul: det(M)·det(N)=det(I)=T₁, 故det(M)≠T₀
invertible→det≠0 : ∀ M → invertible M → det2 M ≢ T₀
invertible→det≠0 M (N , (MN≡I , _)) detM≡0 = T₀≢T₁ (begin
  T₀
    ≡⟨ sym (⊗-zeroˡ (det2 N)) ⟩
  T₀ ⊗ det2 N
    ≡⟨ sym (cong (λ x → x ⊗ det2 N) detM≡0) ⟩
  det2 M ⊗ det2 N
    ≡⟨ sym (det-mul M N) ⟩
  det2 (mat-mul M N)
    ≡⟨ cong det2 MN≡I ⟩
  det2 I2
    ≡⟨ det-I ⟩
  T₁
  ∎)
  where
  open ≡-Reasoning
  T₀≢T₁ : T₀ ≡ T₁ → ⊥
  T₀≢T₁ ()

--------------------------------------------------------------------------------
-- §7. 相同列 → det = 0
--------------------------------------------------------------------------------

-- 两列相同时行列式为0  [策略B] 代数链: a⊗d ⊕ negate(a⊗d) = T₀
same-columns→det≡0 : ∀ a d → det2 ((a , a) , (d , d)) ≡ T₀
same-columns→det≡0 a d = begin
  det2 ((a , a) , (d , d))
    ≡⟨⟩
  (a ⊗ d) ⊕ negate (a ⊗ d)
    ≡⟨ ⊕-inverse (a ⊗ d) ⟩
  T₀
  ∎ where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §8. 秩分类
--------------------------------------------------------------------------------

-- 秩: rank2(det≠0), rank1(det=0且非零矩阵), rank0(零矩阵)
data Rank : Set where
  rank0 rank1 rank2 : Rank

rank : Mat2 → Rank
rank M with det2 M
... | T₁ = rank2
... | T₂ = rank2
... | T₀ with M
... | (T₀ , T₀) , (T₀ , T₀) = rank0
... | _ = rank1

-- det≠0 → rank2: by definition, det≠0 means det∈{T₁,T₂}, rank returns rank2
det≠0→rank2 : ∀ M → det2 M ≢ T₀ → rank M ≡ rank2
det≠0→rank2 M d≢0 with det2 M
... | T₀ = ⊥-elim (d≢0 refl)
... | T₁ = refl
... | T₂ = refl

-- rank2 → det≠0: by definition of rank, rank2 only when det2 M ∈ {T₁,T₂}
-- 该定理从 rank 定义直接成立 (rank 在 det=T₀ 时只返回 rank0/rank1)
-- Agda with-abstraction 阻止了 rank M 的归约, 故此方向不形式化
-- det≠0→rank2 已完整证明, 提供了 det ≠ 0 ⟹ rank 2 的构造性方向
