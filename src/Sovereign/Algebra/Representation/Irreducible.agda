{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Representation.Irreducible
--
-- **不可约表示谓词（GF(3) 载体）与 C₄ 二维闭合实例** —— PvsNP 路线图 W4b①
--
-- 数学背景：设 ρ : G → GL(V) 是群 G 在域 F 上向量空间 V 的线性表示。
--   · 不变线：1 维 ρ-稳定子空间 span(v) = {c·v | c ∈ F}（v ≠ 0）。
--   · 二维不可约 ⟺ 无不变线（二维的真非零子空间恰为线）；
--     三维还须排除不变面，故 NoInvariantSubspace3 以枚举子空间形式定义。
--   · 本模块载体取 GF(3)（律算基础域），实例群取 C₄ —— **不是 C₃**：
--     GF(3) 上 x³ − 1 = (x − 1)³ 只有单根，C₃ 的任何 GF(3)-表示都可上
--     三角化，必有不变线（文字边界 B1，不形式化）；而 x² + 1 在 GF(3)
--     上不可约（平方 0,1,1 不含 2），故旋转 R = [[0,−1],[1,0]]
--     （R² = −I，R⁴ = I）给出 C₄ 的二维不可约表示。
--
-- 分级交付（诚实分级，同 TimeBound/GF3K 约定）：
--   §1 GF(3) 算术………………【refl 枚举】Fin 3 加法/求负/消律（单引理 ≤27 案）
--   §2 F3Space 抽象加法群……【结构定义】+【结构证明】消去/负元唯一/shuffle
--   §3 V₂ 载体与标量乘………【结构证明】smul 分配/零化；mul3ᴵ 标量乘法表
--   §4 C₄ 作用 ρc₄………………【refl 枚举】R/R²/R³ 逐点 +【结构证明】ρ-add
--   §5 谓词………………………【纯定义】NoInvariantLine（二维）、
--                     NoInvariantSubspace3（三维，枚举子空间形式）
--   §6 C₄ 实例闭合……………【结构证明】c4-no-invariant-line（3 案特征值消元）
--   §7 对抗验证 + 尾注………【refl 枚举】
--
-- 诚实边界（立界清单，本模块不做的事）：
--   B1 C₃ 表示可上三角化（GF(3) 特殊性）只有头注文字，未形式化。
--   B2 NoInvariantSubspace3 只定义不实例化。三维实例的构造路径：
--      取 x³ + 2x + 1 ∈ GF(3)[x] 的友矩阵（该三次式在 GF(3) 无根故不可约，
--      见 PvsNP 目录 §3——引用边界：那是 GF(3) 代数模拟文件，非复杂性类
--      分离），其友矩阵在 GF(27)* 中生成 13 或 26 阶循环子群，给出三维
--      不可约实例；本模块预算内不闭合。
--   B3 ρc₄ 的 Cayley 同态表（ρ(g+h) = ρ(g)ρ(h)）未逐对展开；
--      以 R⁴ = id（§4）作为 C₄-作用适定性的证书。
--   B4 「无不变线 ⟹ 可判定不可约 ⟹ 弱 Schur」的桥在 Schur.agda 闭合，
--      本模块只供载体与谓词。
--   B5 Span1/Span2 的封闭性引理（smul3ᴵ 加法分配等）未建——§5 纯定义。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.Representation.Irreducible where

open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- §1. GF(3) = Fin 3 算术 〔refl 枚举〕
--------------------------------------------------------------------------------

0₃ 1₃ 2₃ : Fin 3
0₃ = zero
1₃ = suc zero
2₃ = suc (suc zero)

neg₃ᴵ : Fin 3 → Fin 3
neg₃ᴵ zero = zero
neg₃ᴵ (suc zero) = suc (suc zero)
neg₃ᴵ (suc (suc zero)) = suc zero

_+₃ᴵ_ : Fin 3 → Fin 3 → Fin 3
zero +₃ᴵ m = m
suc zero +₃ᴵ zero = suc zero
suc zero +₃ᴵ suc zero = suc (suc zero)
suc zero +₃ᴵ suc (suc zero) = zero
suc (suc zero) +₃ᴵ zero = suc (suc zero)
suc (suc zero) +₃ᴵ suc zero = zero
suc (suc zero) +₃ᴵ suc (suc zero) = suc zero

mul3ᴵ : Fin 3 → Fin 3 → Fin 3
mul3ᴵ zero _ = zero
mul3ᴵ (suc zero) m = m
mul3ᴵ (suc (suc zero)) zero = zero
mul3ᴵ (suc (suc zero)) (suc zero) = suc (suc zero)
mul3ᴵ (suc (suc zero)) (suc (suc zero)) = suc zero

+₃-idˡᴵ : ∀ a → 0₃ +₃ᴵ a ≡ a
+₃-idˡᴵ a = refl

+₃-idʳᴵ : ∀ a → a +₃ᴵ 0₃ ≡ a
+₃-idʳᴵ zero = refl
+₃-idʳᴵ (suc zero) = refl
+₃-idʳᴵ (suc (suc zero)) = refl

+₃-invˡ : ∀ a → neg₃ᴵ a +₃ᴵ a ≡ 0₃
+₃-invˡ zero = refl
+₃-invˡ (suc zero) = refl
+₃-invˡ (suc (suc zero)) = refl

+₃-commᴵ : ∀ a b → a +₃ᴵ b ≡ b +₃ᴵ a
+₃-commᴵ zero b = sym (+₃-idʳᴵ b)
+₃-commᴵ (suc zero) zero = refl
+₃-commᴵ (suc zero) (suc zero) = refl
+₃-commᴵ (suc zero) (suc (suc zero)) = refl
+₃-commᴵ (suc (suc zero)) zero = refl
+₃-commᴵ (suc (suc zero)) (suc zero) = refl
+₃-commᴵ (suc (suc zero)) (suc (suc zero)) = refl

+₃-assocᴵ : ∀ a b c → (a +₃ᴵ b) +₃ᴵ c ≡ a +₃ᴵ (b +₃ᴵ c)
+₃-assocᴵ zero b c = refl
+₃-assocᴵ (suc zero) zero c = refl
+₃-assocᴵ (suc zero) (suc zero) zero = refl
+₃-assocᴵ (suc zero) (suc zero) (suc zero) = refl
+₃-assocᴵ (suc zero) (suc zero) (suc (suc zero)) = refl
+₃-assocᴵ (suc zero) (suc (suc zero)) zero = refl
+₃-assocᴵ (suc zero) (suc (suc zero)) (suc zero) = refl
+₃-assocᴵ (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
+₃-assocᴵ (suc (suc zero)) zero c = refl
+₃-assocᴵ (suc (suc zero)) (suc zero) zero = refl
+₃-assocᴵ (suc (suc zero)) (suc zero) (suc zero) = refl
+₃-assocᴵ (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
+₃-assocᴵ (suc (suc zero)) (suc (suc zero)) zero = refl
+₃-assocᴵ (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
+₃-assocᴵ (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

neg₃ᴵ-involutive : ∀ a → neg₃ᴵ (neg₃ᴵ a) ≡ a
neg₃ᴵ-involutive zero = refl
neg₃ᴵ-involutive (suc zero) = refl
neg₃ᴵ-involutive (suc (suc zero)) = refl

-- 求负对加法的分配：−(a+b) ≡ (−a)+(−b)
neg₃ᴵ-distr : ∀ a b → neg₃ᴵ (a +₃ᴵ b) ≡ neg₃ᴵ a +₃ᴵ neg₃ᴵ b
neg₃ᴵ-distr zero b = refl
neg₃ᴵ-distr (suc zero) zero = refl
neg₃ᴵ-distr (suc zero) (suc zero) = refl
neg₃ᴵ-distr (suc zero) (suc (suc zero)) = refl
neg₃ᴵ-distr (suc (suc zero)) zero = refl
neg₃ᴵ-distr (suc (suc zero)) (suc zero) = refl
neg₃ᴵ-distr (suc (suc zero)) (suc (suc zero)) = refl

-- 3·a ≡ 0 的两种结合形态
triple-zeroᴵ : ∀ a → (a +₃ᴵ a) +₃ᴵ a ≡ 0₃
triple-zeroᴵ zero = refl
triple-zeroᴵ (suc zero) = refl
triple-zeroᴵ (suc (suc zero)) = refl

sum-three : ∀ a → a +₃ᴵ (a +₃ᴵ a) ≡ 0₃
sum-three a = trans (+₃-commᴵ a (a +₃ᴵ a)) (triple-zeroᴵ a)

-- 4·a ≡ a（GF(3) 特征）
four≡one : ∀ a → (a +₃ᴵ a) +₃ᴵ (a +₃ᴵ a) ≡ a
four≡one zero = refl
four≡one (suc zero) = refl
four≡one (suc (suc zero)) = refl

-- 2-无挠（GF(3) 版）：2a ≡ 0 ⟹ a ≡ 0
half3 : ∀ a → a +₃ᴵ a ≡ 0₃ → a ≡ 0₃
half3 zero e = refl
half3 (suc zero) ()
half3 (suc (suc zero)) ()

-- a = −a ⟹ a ≡ 0
self-neg₃ᴵ : ∀ a → neg₃ᴵ a ≡ a → a ≡ 0₃
self-neg₃ᴵ zero e = refl
self-neg₃ᴵ (suc zero) ()
self-neg₃ᴵ (suc (suc zero)) ()

-- −a ≡ 0 ⟹ a ≡ 0
neg-eq0 : ∀ a → neg₃ᴵ a ≡ 0₃ → a ≡ 0₃
neg-eq0 zero e = refl
neg-eq0 (suc zero) ()
neg-eq0 (suc (suc zero)) ()

-- 差消去：a + (−b) ≡ 0 ⟹ a ≡ b（符号链，无案拆分）
diff-zero : ∀ a b → a +₃ᴵ neg₃ᴵ b ≡ 0₃ → a ≡ b
diff-zero a b h =
  begin
    a
      ≡⟨ sym (+₃-idʳᴵ a) ⟩
    a +₃ᴵ 0₃
      ≡⟨ cong (a +₃ᴵ_) (sym (+₃-invˡ b)) ⟩
    a +₃ᴵ (neg₃ᴵ b +₃ᴵ b)
      ≡⟨ sym (+₃-assocᴵ a (neg₃ᴵ b) b) ⟩
    (a +₃ᴵ neg₃ᴵ b) +₃ᴵ b
      ≡⟨ cong (_+₃ᴵ b) h ⟩
    0₃ +₃ᴵ b
      ≡⟨ +₃-idˡᴵ b ⟩
    b
  ∎
  where open ≡-Reasoning

-- 字面不等式（供下游 absurd 消解）
1≢0ᴵ : 1₃ ≢ 0₃
1≢0ᴵ = λ ()

0≢1ᴵ : 0₃ ≢ 1₃
0≢1ᴵ = λ ()

0≢2ᴵ : 0₃ ≢ 2₃
0≢2ᴵ = λ ()

--------------------------------------------------------------------------------
-- §2. F3Space：GF(3)-加性群（带负元）〔结构定义 + 结构证明〕
--
-- 注：Maschke.agda §3 的 F2Space 以 +ᵥ-self（v+v ≡ 0）为场——那是 char-2
-- 专属，对 GF(3) 非平凡载体不可满足（char 3 下 v+v ≡ 0 ⟹ v ≡ 0）。
-- 此处以「带负元的交换群」重建同范式的代数基础设施，供 Schur.agda
-- 的泛型弱 Schur 使用。
--------------------------------------------------------------------------------

record F3Space (V : Set) : Set where
  field
    _+ᵥ_ : V → V → V
    0ᵥ : V
    negᵥ : V → V
    +ᵥ-assoc : ∀ u v w → (u +ᵥ v) +ᵥ w ≡ u +ᵥ (v +ᵥ w)
    +ᵥ-comm : ∀ u v → u +ᵥ v ≡ v +ᵥ u
    +ᵥ-idˡ : ∀ v → 0ᵥ +ᵥ v ≡ v
    +ᵥ-invˡ : ∀ v → negᵥ v +ᵥ v ≡ 0ᵥ

module F3Ops {V : Set} (S : F3Space V) where
  open F3Space S

  +ᵥ-idʳ : ∀ v → v +ᵥ 0ᵥ ≡ v
  +ᵥ-idʳ v = trans (+ᵥ-comm v 0ᵥ) (+ᵥ-idˡ v)

  +ᵥ-invʳ : ∀ v → v +ᵥ negᵥ v ≡ 0ᵥ
  +ᵥ-invʳ v = trans (+ᵥ-comm v (negᵥ v)) (+ᵥ-invˡ v)

  +ᵥ-cancelˡ : ∀ a b c → a +ᵥ b ≡ a +ᵥ c → b ≡ c
  +ᵥ-cancelˡ a b c h = begin
    b
      ≡⟨ sym (+ᵥ-idˡ b) ⟩
    0ᵥ +ᵥ b
      ≡⟨ cong (λ z → z +ᵥ b) (sym (+ᵥ-invˡ a)) ⟩
    (negᵥ a +ᵥ a) +ᵥ b
      ≡⟨ +ᵥ-assoc (negᵥ a) a b ⟩
    negᵥ a +ᵥ (a +ᵥ b)
      ≡⟨ cong (negᵥ a +ᵥ_) h ⟩
    negᵥ a +ᵥ (a +ᵥ c)
      ≡⟨ sym (+ᵥ-assoc (negᵥ a) a c) ⟩
    (negᵥ a +ᵥ a) +ᵥ c
      ≡⟨ cong (λ z → z +ᵥ c) (+ᵥ-invˡ a) ⟩
    0ᵥ +ᵥ c
      ≡⟨ +ᵥ-idˡ c ⟩
    c
    ∎
    where open ≡-Reasoning

  -- v + v ≡ v ⟹ v ≡ 0（幂等消去）
  plus-idem→zero : ∀ v → v +ᵥ v ≡ v → v ≡ 0ᵥ
  plus-idem→zero v h = +ᵥ-cancelˡ v v 0ᵥ (trans h (sym (+ᵥ-idʳ v)))
  -- 注：「v + v ≡ 0 ⟹ v ≡ 0」在纯加性群上不可证（Z/2 反例），
  -- 需 GF(3) 特征信息；V₂ 的分量版见 double-zero2（§3）。

  -- 负元唯一：a + b ≡ 0 ⟹ b ≡ −a
  neg-unique : ∀ a b → a +ᵥ b ≡ 0ᵥ → b ≡ negᵥ a
  neg-unique a b h = begin
    b
      ≡⟨ sym (+ᵥ-idˡ b) ⟩
    0ᵥ +ᵥ b
      ≡⟨ cong (λ z → z +ᵥ b) (sym (+ᵥ-invˡ a)) ⟩
    (negᵥ a +ᵥ a) +ᵥ b
      ≡⟨ +ᵥ-assoc (negᵥ a) a b ⟩
    negᵥ a +ᵥ (a +ᵥ b)
      ≡⟨ cong (negᵥ a +ᵥ_) h ⟩
    negᵥ a +ᵥ 0ᵥ
      ≡⟨ +ᵥ-idʳ (negᵥ a) ⟩
    negᵥ a
    ∎
    where open ≡-Reasoning

  -- 对偶形态：a + b ≡ 0 ⟹ a ≡ −b
  add-neg-flip : ∀ a b → a +ᵥ b ≡ 0ᵥ → a ≡ negᵥ b
  add-neg-flip a b h = neg-unique b a (trans (+ᵥ-comm b a) h)

  -- 负元对合
  neg-involutiveᵥ : ∀ v → v ≡ negᵥ (negᵥ v)
  neg-involutiveᵥ v = neg-unique (negᵥ v) v (+ᵥ-invˡ v)

  neg-zeroᵥ : negᵥ 0ᵥ ≡ 0ᵥ
  neg-zeroᵥ = sym (add-neg-flip 0ᵥ 0ᵥ (+ᵥ-idˡ 0ᵥ))

  -- 四项换位：(a+b)+(c+d) ≡ (a+c)+(b+d)
  +ᵥ-shuffle : ∀ a b c d → (a +ᵥ b) +ᵥ (c +ᵥ d) ≡ (a +ᵥ c) +ᵥ (b +ᵥ d)
  +ᵥ-shuffle a b c d = begin
    (a +ᵥ b) +ᵥ (c +ᵥ d)
      ≡⟨ +ᵥ-assoc a b (c +ᵥ d) ⟩
    a +ᵥ (b +ᵥ (c +ᵥ d))
      ≡⟨ cong (a +ᵥ_) (sym (+ᵥ-assoc b c d)) ⟩
    a +ᵥ ((b +ᵥ c) +ᵥ d)
      ≡⟨ cong (a +ᵥ_) (cong (_+ᵥ d) (+ᵥ-comm b c)) ⟩
    a +ᵥ ((c +ᵥ b) +ᵥ d)
      ≡⟨ cong (a +ᵥ_) (+ᵥ-assoc c b d) ⟩
    a +ᵥ (c +ᵥ (b +ᵥ d))
      ≡⟨ sym (+ᵥ-assoc a c (b +ᵥ d)) ⟩
    (a +ᵥ c) +ᵥ (b +ᵥ d)
    ∎
    where open ≡-Reasoning

  -- 负元对加法分配：−(u+v) ≡ (−u)+(−v)
  neg-add : ∀ u v → negᵥ (u +ᵥ v) ≡ negᵥ u +ᵥ negᵥ v
  neg-add u v =
    sym (add-neg-flip (negᵥ u +ᵥ negᵥ v) (u +ᵥ v)
      (begin
        (negᵥ u +ᵥ negᵥ v) +ᵥ (u +ᵥ v)
          ≡⟨ +ᵥ-shuffle (negᵥ u) (negᵥ v) u v ⟩
        (negᵥ u +ᵥ u) +ᵥ (negᵥ v +ᵥ v)
          ≡⟨ cong₂ _+ᵥ_ (+ᵥ-invˡ u) (+ᵥ-invˡ v) ⟩
        0ᵥ +ᵥ 0ᵥ
          ≡⟨ +ᵥ-idˡ 0ᵥ ⟩
        0ᵥ
      ∎))
    where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §3. V₂ = GF(3)² 载体与标量乘 〔结构证明〕
--------------------------------------------------------------------------------

record V2 : Set where
  constructor v2
  field
    x y : Fin 3

open V2

v2-ext : ∀ {a b a' b'} → a ≡ a' → b ≡ b' → v2 a b ≡ v2 a' b'
v2-ext refl refl = refl

0ᵥ2 : V2
0ᵥ2 = v2 0₃ 0₃

_+ᵥ2_ : V2 → V2 → V2
v2 a b +ᵥ2 v2 a' b' = v2 (a +₃ᴵ a') (b +₃ᴵ b')

negᵥ2 : V2 → V2
negᵥ2 (v2 a b) = v2 (neg₃ᴵ a) (neg₃ᴵ b)

-- GF(3) 标量乘（按标量分派；2·v 定义为 v+v 以保持首参归约）
smul2 : Fin 3 → V2 → V2
smul2 zero _ = 0ᵥ2
smul2 (suc zero) v = v
smul2 (suc (suc zero)) v = v +ᵥ2 v

V2Space : F3Space V2
V2Space = record
  { _+ᵥ_ = _+ᵥ2_
  ; 0ᵥ = 0ᵥ2
  ; negᵥ = negᵥ2
  ; +ᵥ-assoc = λ { (v2 a b) (v2 a' b') (v2 a'' b'')
                     → v2-ext (+₃-assocᴵ a a' a'') (+₃-assocᴵ b b' b'') }
  ; +ᵥ-comm = λ { (v2 a b) (v2 a' b') → v2-ext (+₃-commᴵ a a') (+₃-commᴵ b b') }
  ; +ᵥ-idˡ = λ { (v2 a b) → v2-ext refl refl }
  ; +ᵥ-invˡ = λ { (v2 a b) → v2-ext (+₃-invˡ a) (+₃-invˡ b) }
  }

+ᵥ2-idˡ : ∀ v → 0ᵥ2 +ᵥ2 v ≡ v
+ᵥ2-idˡ = F3Space.+ᵥ-idˡ V2Space

-- V2 上的抽象群引理即时可用（对 Schur.agda 公开）
open F3Ops V2Space public

-- smul 分配：a·v + b·v ≡ (a+b)·v（9 案，逐案退化到 +₃ᴵ 引理）
smul2-add : ∀ a b v → smul2 a v +ᵥ2 smul2 b v ≡ smul2 (a +₃ᴵ b) v
smul2-add zero b v = +ᵥ2-idˡ (smul2 b v)
smul2-add (suc zero) zero v = +ᵥ-idʳ v
smul2-add (suc zero) (suc zero) v = refl
smul2-add (suc zero) (suc (suc zero)) (v2 a b) = v2-ext (sum-three a) (sum-three b)
smul2-add (suc (suc zero)) zero v = +ᵥ-idʳ (v +ᵥ2 v)
smul2-add (suc (suc zero)) (suc zero) (v2 a b) = v2-ext (triple-zeroᴵ a) (triple-zeroᴵ b)
smul2-add (suc (suc zero)) (suc (suc zero)) (v2 a b) = v2-ext (four≡one a) (four≡one b)

smul2-zeroᵥ : ∀ c → smul2 c 0ᵥ2 ≡ 0ᵥ2
smul2-zeroᵥ zero = refl
smul2-zeroᵥ (suc zero) = refl
smul2-zeroᵥ (suc (suc zero)) = refl

-- −v ≡ 2·v
neg≡2· : ∀ a → neg₃ᴵ a ≡ a +₃ᴵ a
neg≡2· zero = refl
neg≡2· (suc zero) = refl
neg≡2· (suc (suc zero)) = refl

neg≡2ᵥ : ∀ v → negᵥ2 v ≡ v +ᵥ2 v
neg≡2ᵥ (v2 a b) = v2-ext (neg≡2· a) (neg≡2· b)

-- 4·v ≡ v（向量版）
double-four : ∀ v → (v +ᵥ2 v) +ᵥ2 (v +ᵥ2 v) ≡ v
double-four (v2 a b) = v2-ext (four≡one a) (four≡one b)

-- 标量乘与负元交换：−(c·v) ≡ (−c)·v
smul-neg : ∀ c v → negᵥ2 (smul2 c v) ≡ smul2 (neg₃ᴵ c) v
smul-neg zero v = neg-zeroᵥ
smul-neg (suc zero) v = neg≡2ᵥ v
smul-neg (suc (suc zero)) v =
  trans (neg-add v v)
    (trans (cong₂ _+ᵥ2_ (neg≡2ᵥ v) (neg≡2ᵥ v)) (double-four v))

-- 标量乘复合：c·(d·v) ≡ (cd)·v
smul-mul : ∀ c d v → smul2 c (smul2 d v) ≡ smul2 (mul3ᴵ c d) v
smul-mul zero d v = refl
smul-mul (suc zero) zero v = refl
smul-mul (suc zero) (suc zero) v = refl
smul-mul (suc zero) (suc (suc zero)) v = refl
smul-mul (suc (suc zero)) zero v = refl
smul-mul (suc (suc zero)) (suc zero) v = refl
smul-mul (suc (suc zero)) (suc (suc zero)) (v2 a b) = v2-ext (four≡one a) (four≡one b)

-- 非零向量不被非零标量零化
double-zero2 : ∀ u → u +ᵥ2 u ≡ 0ᵥ2 → u ≡ 0ᵥ2
double-zero2 (v2 a b) e = v2-ext (half3 a (cong x e)) (half3 b (cong y e))

smul-zero-split : ∀ u → u ≢ 0ᵥ2 → ∀ c → smul2 c u ≡ 0ᵥ2 → c ≡ 0₃
smul-zero-split u nz zero e = refl
smul-zero-split u nz (suc zero) e = ⊥-elim (nz e)
smul-zero-split u nz (suc (suc zero)) e = ⊥-elim (nz (double-zero2 u e))

--------------------------------------------------------------------------------
-- §4. C₄ 作用：旋转表示 ρc₄ 〔refl 枚举 + 结构证明〕
--------------------------------------------------------------------------------

R2 : V2 → V2
R2 (v2 a b) = v2 (neg₃ᴵ b) a

RR2 : V2 → V2
RR2 (v2 a b) = v2 (neg₃ᴵ a) (neg₃ᴵ b)

RRR2 : V2 → V2
RRR2 (v2 a b) = v2 b (neg₃ᴵ a)

ρc4 : Fin 4 → V2 → V2
ρc4 zero v = v
ρc4 (suc zero) v = R2 v
ρc4 (suc (suc zero)) v = RR2 v
ρc4 (suc (suc (suc zero))) v = RRR2 v

-- R⁴ = id（C₄ 作用适定性证书；Cayley 同态表见头注 B3）
R⁴-id : ∀ v → R2 (R2 (R2 (R2 v))) ≡ v
R⁴-id (v2 a b) = v2-ext (neg₃ᴵ-involutive a) (neg₃ᴵ-involutive b)

-- 作用加性
ρc4-add : ∀ g v w → ρc4 g (v +ᵥ2 w) ≡ ρc4 g v +ᵥ2 ρc4 g w
ρc4-add zero v w = refl
ρc4-add (suc zero) (v2 a b) (v2 a' b') = v2-ext (neg₃ᴵ-distr b b') refl
ρc4-add (suc (suc zero)) (v2 a b) (v2 a' b') = v2-ext (neg₃ᴵ-distr a a') (neg₃ᴵ-distr b b')
ρc4-add (suc (suc (suc zero))) (v2 a b) (v2 a' b') = v2-ext refl (neg₃ᴵ-distr a a')

ρc4-zero : ∀ g → ρc4 g 0ᵥ2 ≡ 0ᵥ2
ρc4-zero zero = refl
ρc4-zero (suc zero) = refl
ρc4-zero (suc (suc zero)) = refl
ρc4-zero (suc (suc (suc zero))) = refl

-- R 与标量乘交换
R-smulᴵ : ∀ c v → R2 (smul2 c v) ≡ smul2 c (R2 v)
R-smulᴵ zero v = refl
R-smulᴵ (suc zero) v = refl
R-smulᴵ (suc (suc zero)) (v2 a b) = v2-ext (neg₃ᴵ-distr b b) refl

-- RRR2 = R ∘ RR
RRR2≡R∘RR : ∀ v → RRR2 v ≡ R2 (RR2 v)
RRR2≡R∘RR (v2 a b) = v2-ext (sym (neg₃ᴵ-involutive b)) refl

--------------------------------------------------------------------------------
-- §5. 不可约性谓词 〔纯定义〕
--------------------------------------------------------------------------------

-- 二维：无不变线（不存在非零公共特征向量）
NoInvariantLine : (G : Set) → (G → V2 → V2) → Set
NoInvariantLine G ρ =
  ¬ Σ V2 (λ v → (v ≢ 0ᵥ2) × (∀ g → Σ (Fin 3) (λ c → ρ g v ≡ smul2 c v)))

--------------------------------------------------------------------------------
-- §5b. 三维载体 V₃ 与枚举子空间形式 〔纯定义〕
--------------------------------------------------------------------------------

record V3 : Set where
  constructor v3
  field
    x₀ x₁ x₂ : Fin 3

open V3

v3-extᴵ : ∀ {a b c a' b' c'} → a ≡ a' → b ≡ b' → c ≡ c' → v3 a b c ≡ v3 a' b' c'
v3-extᴵ refl refl refl = refl

0ᵥ3 : V3
0ᵥ3 = v3 zero zero zero

_+ᵥ3_ : V3 → V3 → V3
v3 a b c +ᵥ3 v3 a' b' c' = v3 (a +₃ᴵ a') (b +₃ᴵ b') (c +₃ᴵ c')

smul3ᴵ : Fin 3 → V3 → V3
smul3ᴵ zero _ = 0ᵥ3
smul3ᴵ (suc zero) v = v
smul3ᴵ (suc (suc zero)) v = v +ᵥ3 v

-- 1 维子空间：w ∈ span(u) ⟺ ∃c, w ≡ c·u
Span1 : V3 → V3 → Set
Span1 u w = Σ (Fin 3) (λ c → w ≡ smul3ᴵ c u)

-- 2 维子空间（枚举形式）：w ∈ span(u,t) ⟺ ∃ab, w ≡ a·u + b·t
Span2 : V3 → V3 → V3 → Set
Span2 u t w = Σ (Fin 3) (λ a → Σ (Fin 3) (λ b → w ≡ smul3ᴵ a u +ᵥ3 smul3ᴵ b t))

-- 线 ρ-稳定：非零 u 的张成把每个 ρ(g) 元素收回张成内
LineStable : (G : Set) → (G → V3 → V3) → V3 → Set
LineStable G ρ u = (u ≢ 0ᵥ3) × (∀ g → Span1 u (ρ g u))

-- 面 ρ-稳定：span(u,t) 逐元素稳定 + 真子空间（不张满 V₃）+ 非零
PlaneStable : (G : Set) → (G → V3 → V3) → V3 → V3 → Set
PlaneStable G ρ u t =
  (∀ g w → Span2 u t w → Span2 u t (ρ g w))
  × ¬ ((w : V3) → Span2 u t w)
  × ((u ≢ 0ᵥ3) ⊎ (t ≢ 0ᵥ3))

-- 三维不可约（枚举子空间形式）：无稳定线且无稳定真面。
-- 注：GF(3)³ 的真非零子空间恰为 13 条线与 13 个面；本谓词按生成元
-- 枚举（线按非零向量，面按带「不张满」证书的生成对），覆盖每一
-- 子空间（有冗余：每条线被 2 个非零代表元枚举，每个面被多对生成元
-- 枚举——冗余不损完备性）。实例化见头注 B2 立界。
NoInvariantSubspace3 : (G : Set) → (G → V3 → V3) → Set
NoInvariantSubspace3 G ρ =
  (∀ u → ¬ LineStable G ρ u) × (∀ u t → ¬ PlaneStable G ρ u t)

--------------------------------------------------------------------------------
-- §6. C₄ 实例闭合：ρc₄ 无不变线 〔结构证明〕
--
-- R·(x,y) = (−y,x) = c·(x,y) 的特征方程：−y = cx 且 x = cy。
-- 消元：2y = c²y；GF(3) 的平方 ∈ {0,1} 不含 2 ⟹ y ≡ 0 ⟹ x ≡ 0。
-- 全程 3 案（对 c），符合「单引理 ≤27 案」纪律。
--------------------------------------------------------------------------------

c4-no-invariant-line : NoInvariantLine (Fin 4) ρc4
c4-no-invariant-line (v2 a b , nz , ev) = aux (ev (suc zero))
  where
    aux : Σ (Fin 3) (λ c → ρc4 (suc zero) (v2 a b) ≡ smul2 c (v2 a b)) → ⊥
    -- c = 0：−y ≡ 0 且 x ≡ 0
    aux (zero , e) = nz (v2-ext (cong y e) (neg-eq0 b (cong x e)))
    -- c = 1：−y ≡ x 且 x ≡ y ⟹ −y ≡ y ⟹ y ≡ 0 ⟹ x ≡ 0
    aux (suc zero , e) =
      nz (v2-ext (trans (cong y e) eb) eb)
      where
        eb : b ≡ 0₃
        eb = self-neg₃ᴵ b (trans (cong x e) (cong y e))
    -- c = 2：x ≡ 2y 且 −y ≡ 2x = 2·2y = y ⟹ y ≡ 0 ⟹ x ≡ 0
    aux (suc (suc zero) , e) =
      nz (v2-ext ea eb)
      where
        eb : b ≡ 0₃
        eb = self-neg₃ᴵ b
               (trans (cong x e)
                 (trans (cong (λ z → z +₃ᴵ z) (cong y e)) (four≡one b)))
        ea : a ≡ 0₃
        ea = trans (cong y e) (cong (λ z → z +₃ᴵ z) eb)

--------------------------------------------------------------------------------
-- §7. 对抗验证（独立 refl 抽查）+ 尾注
--------------------------------------------------------------------------------

_R2-e1 : R2 (v2 (suc zero) zero) ≡ v2 zero (suc zero)
_R2-e1 = refl

_RR2-neg : RR2 (v2 (suc zero) zero) ≡ v2 (suc (suc zero)) zero
_RR2-neg = refl

_R4-id-e1 : R2 (R2 (R2 (R2 (v2 (suc zero) zero)))) ≡ v2 (suc zero) zero
_R4-id-e1 = refl

_ρ-add-spot : ρc4 (suc zero) (v2 (suc zero) zero +ᵥ2 v2 zero (suc zero))
             ≡ ρc4 (suc zero) (v2 (suc zero) zero) +ᵥ2 ρc4 (suc zero) (v2 zero (suc zero))
_ρ-add-spot = refl

_smul2-add-spot : smul2 2₃ (v2 (suc zero) (suc zero)) ≡ v2 2₃ 2₃
_smul2-add-spot = refl

--------------------------------------------------------------------------------
-- 尾注
--
-- 0 postulate / 0 hole / 0 unsolved meta。全部构造性闭合：
--   · §1–§3：Fin 3 / V2 逐案 refl + F3Ops 符号推导（无 postulate）。
--   · §4：ρc4 由 R 的幂显式给出；R⁴-id 为适定性证书（B3 立界仍有效）。
--   · §5：纯定义。
--   · §6：c4-no-invariant-line 为【结构证明】（对特征值 c 的 3 案消元 +
--     2-无挠），非大枚举；特征多项式 x²+1 在 GF(3) 无根是本实例
--     不可约的代数根源（见头注）。
-- 层内纪律：本模块未 import 任何 Synthesis/ 模块 ✓；未修改既有文件 ✓。
--------------------------------------------------------------------------------
