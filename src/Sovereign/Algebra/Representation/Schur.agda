{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Representation.Schur
--
-- **GF(3) 弱 Schur 定理**（不可约 ⟹ 交换算子「可逆或零」）—— PvsNP 路线图 W4b②
--
-- 数学背景（Schur 引理的两版）：
--   · 完整版（代数闭域）：T 与不可约表示 ρ(g) 全交换 ⟹ T = c·I（标量）。
--     **此版在 GF(3) 上为假**：GF(3) 非代数闭，x² + 1 无根，C₄ 旋转
--     ρc₄(1) = R 与一切 ρc₄(g) 交换却非标量（§6 反例，refl 闭合）。
--     特征值 ±i 不落在基域里——这既是表示不可约的代数根源，也正是
--     标量化失败的根源。
--   · **真定理是「可逆或零」版**：T 交换一切 ⟹ ker T 与 im T 都是
--     ρ-稳定子空间（§1 符号证明）；不可约性排除真核/真像 ⟹ T ≡ 0
--     或 T 双射。二维实例（C₄ 作用）完全闭合（§2–§5）。
--   · **单向函数屏障引用边界**：「交换 ⟹ 可逆或零」是不可约表示上
--     交换算子的刚性，对应 PvsNP 目录「不可约多项式 = 单向函数屏障」
--     的表示论侧面（引用边界：PvsNP_Separation §3 是 GF(3) 代数模拟而非
--     复杂性类分离，本模块同其口径，不宣称 P ≠ NP）。
--
-- 分级交付（诚实分级）：
--   §1 SchurCore 泛型核…………【结构定义】Irreducible（任意子谓词三闭合
--                     + 二择一）；【结构证明】act-zero/T-zero/T-neg、
--                     ker/im 稳定、weak-schur（T ≡ 0 ⊎ 单射×满射）
--   §2 V₂ ≅ Fin 9 有限抽屉……【refl 枚举】编码表 +【结构证明】单射⇒满射
--                     （stdlib pigeonhole + punchOut/punchIn 装配）
--   §3 可判定搜索………………【refl 枚举 + any?】v2-dec、full-or-miss、
--                     nonzero-or-trivial
--   §4 象限排除…………………【结构证明】quadrant-kill：case-1 特征值
--                     消元反证（接 c4-no-invariant-line）；case-2 独立对
--                     ⟹ 抽屉满射 ⟹ Q = V 反证
--   §5 C₄ 实例组合……………【结构证明】c4-irreducible-dec、c4-weak-schur
--   §6 完整 Schur 反例………【refl 枚举】commute-not-scalar、R-bijective
--   §7 对抗验证 + 尾注
--
-- 诚实边界（立界清单）：
--   B1 完整 Schur 的反例只对 ρc₄ 显式给出（GF(3) 上一般情形由本例代表）。
--   B2 三维弱 Schur 未实例化：抽象 Irreducible 已泛型，但 NoInvariantSubspace3
--      （Irreducible.agda §5b）到抽象 Irreducible 的三维桥未建。
--   B3 Maschke §3 分裂引理**未直接复用**：其 F2Space 场 +ᵥ-self（v+v ≡ 0）
--      是 char-2 专属，GF(3) 载体不可满足；弱 Schur 链条消费的是
--      ker/im 稳定性（§1）而非投影分裂。char-3 分裂移植
--      （v ≡ p v + (v − p v)）立界不设空壳签名。
--   B4 V₂↔Fin 9 编码是脚手架：任何 9 元可判定载体均可替换。
--   B5 泛型核的 Irreducible 不含可判定性条件（对抽象 V 不可要求），
--      实例侧改走可判定子谓词路线（§3）——两条路线在本模块并存，
--      各自闭合，不互相伪装。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.Representation.Schur where

open import Data.Fin using (Fin; zero; suc; punchOut; punchIn)
  renaming (_<_ to _<ᶠ_)
open import Data.Nat using (ℕ; zero; suc; _<_; s<s; z<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Fin.Properties using (pigeonhole; punchIn-punchOut; any?; _≟_)
  renaming (<-irrefl to <ᶠ-irrefl)
open import Data.Nat.Properties using (<-irrefl)
open import Function.Base using (_∘_; _∘₂_)

-- F3Ops 在 Irreducible 以 V2Space 实例化并 public 再导出；此处隐藏实例级
-- 名字，使 §1 SchurCore 内 open F3Ops S（抽象实例）无歧义。具体侧需要时
-- 经 V2Ops 限定引用。
open import Sovereign.Algebra.Representation.Irreducible
  hiding (+ᵥ-idʳ; +ᵥ-invʳ; +ᵥ-cancelˡ; plus-idem→zero; neg-unique; add-neg-flip
         ; neg-involutiveᵥ; neg-zeroᵥ; neg-add; +ᵥ-shuffle)

module V2Ops = F3Ops V2Space

open V2 using (x; y)

--------------------------------------------------------------------------------
-- §1. SchurCore：泛型弱 Schur（任意 F3Space + 任意加性作用）〔结构证明〕
--------------------------------------------------------------------------------

module SchurCore {V G : Set} (S : F3Space V) (act : G → V → V)
                 (act-add : ∀ g v w
                    → act g (F3Space._+ᵥ_ S v w)
                    ≡ F3Space._+ᵥ_ S (act g v) (act g w)) where
  open F3Space S
  open F3Ops S

  -- 抽象不可约：任意子谓词 + 三闭合（0、加法、ρ-稳定）⟹ 全空间 或 仅零
  Irreducible : Set₁
  Irreducible =
    ∀ (sub : V → Set)
    → sub 0ᵥ
    → (∀ u v → sub u → sub v → sub (u +ᵥ v))
    → (∀ g u → sub u → sub (act g u))
    → (∀ v → sub v) ⊎ (∀ u → sub u → u ≡ 0ᵥ)

  -- 作用零元
  act-zero : ∀ g → act g 0ᵥ ≡ 0ᵥ
  act-zero g = plus-idem→zero (act g 0ᵥ)
    (begin
      act g 0ᵥ +ᵥ act g 0ᵥ
        ≡⟨ sym (act-add g 0ᵥ 0ᵥ) ⟩
      act g (0ᵥ +ᵥ 0ᵥ)
        ≡⟨ cong (act g) (+ᵥ-idˡ 0ᵥ) ⟩
      act g 0ᵥ
    ∎)
    where open ≡-Reasoning

  -- 作用与负元交换
  act-neg : ∀ g v → act g (negᵥ v) ≡ negᵥ (act g v)
  act-neg g v =
    add-neg-flip (act g (negᵥ v)) (act g v)
      (begin
        act g (negᵥ v) +ᵥ act g v
          ≡⟨ sym (act-add g (negᵥ v) v) ⟩
        act g (negᵥ v +ᵥ v)
          ≡⟨ cong (act g) (+ᵥ-comm (negᵥ v) v) ⟩
        act g (v +ᵥ negᵥ v)
          ≡⟨ cong (act g) (+ᵥ-invʳ v) ⟩
        act g 0ᵥ
          ≡⟨ act-zero g ⟩
        0ᵥ
      ∎)
    where open ≡-Reasoning

  -- 交换算子 T 的三条基本引理
  T-zero : (T : V → V) → (∀ v w → T (v +ᵥ w) ≡ T v +ᵥ T w) → T 0ᵥ ≡ 0ᵥ
  T-zero T T-add = plus-idem→zero (T 0ᵥ)
    (begin
      T 0ᵥ +ᵥ T 0ᵥ
        ≡⟨ sym (T-add 0ᵥ 0ᵥ) ⟩
      T (0ᵥ +ᵥ 0ᵥ)
        ≡⟨ cong T (+ᵥ-idˡ 0ᵥ) ⟩
      T 0ᵥ
    ∎)
    where open ≡-Reasoning

  T-neg : (T : V → V) → (∀ v w → T (v +ᵥ w) ≡ T v +ᵥ T w)
        → ∀ v → T (negᵥ v) ≡ negᵥ (T v)
  T-neg T T-add v =
    add-neg-flip (T (negᵥ v)) (T v)
      (begin
        T (negᵥ v) +ᵥ T v
          ≡⟨ sym (T-add (negᵥ v) v) ⟩
        T (negᵥ v +ᵥ v)
          ≡⟨ cong T (+ᵥ-comm (negᵥ v) v) ⟩
        T (v +ᵥ negᵥ v)
          ≡⟨ cong T (+ᵥ-invʳ v) ⟩
        T 0ᵥ
          ≡⟨ T-zero T T-add ⟩
        0ᵥ
      ∎)
    where open ≡-Reasoning

  -- 核心链条①：交换 ⟹ ker T ρ-稳定
  comm-ker-stable : (T : V → V)
    → (∀ g v → T (act g v) ≡ act g (T v))
    → ∀ g v → T v ≡ 0ᵥ → T (act g v) ≡ 0ᵥ
  comm-ker-stable T T-comm g v e =
    trans (T-comm g v) (trans (cong (act g) e) (act-zero g))

  -- 核心链条②：交换 ⟹ im T ρ-稳定（T v 的像在作用后仍在像中）
  comm-im-stable : (T : V → V)
    → (∀ g v → T (act g v) ≡ act g (T v))
    → ∀ g v → Σ V (λ u → act g (T v) ≡ T u)
  comm-im-stable T T-comm g v = act g v , sym (T-comm g v)

  -- ker 谓词对加法闭合
  ker-sub-add : (T : V → V) → (∀ v w → T (v +ᵥ w) ≡ T v +ᵥ T w)
    → ∀ u v → T u ≡ 0ᵥ → T v ≡ 0ᵥ → T (u +ᵥ v) ≡ 0ᵥ
  ker-sub-add T T-add u v eu ev =
    trans (T-add u v) (trans (cong₂ _+ᵥ_ eu ev) (+ᵥ-idˡ 0ᵥ))

  -- im 谓词三闭合
  im-sub-add : (T : V → V) → (∀ v w → T (v +ᵥ w) ≡ T v +ᵥ T w)
    → ∀ u v → Σ V (λ x → T x ≡ u) → Σ V (λ x → T x ≡ v)
    → Σ V (λ x → T x ≡ u +ᵥ v)
  im-sub-add T T-add u v (x₁ , e₁) (x₂ , e₂) =
    x₁ +ᵥ x₂ , trans (T-add x₁ x₂) (cong₂ _+ᵥ_ e₁ e₂)

  im-sub-act : (T : V → V)
    → (∀ g v → T (act g v) ≡ act g (T v))
    → ∀ g u → Σ V (λ x → T x ≡ u) → Σ V (λ x → T x ≡ act g u)
  im-sub-act T T-comm g u (x , e) =
    act g x , trans (T-comm g x) (cong (act g) e)

  -- ker ≡ {0} ⟹ T 单射
  ker-triv-injective : (T : V → V)
    → (∀ v w → T (v +ᵥ w) ≡ T v +ᵥ T w)
    → (∀ u → T u ≡ 0ᵥ → u ≡ 0ᵥ)
    → ∀ u v → T u ≡ T v → u ≡ v
  ker-triv-injective T T-add ker-triv u v e =
    trans (neg-involutiveᵥ u)
      (trans (cong negᵥ (sym hv)) (sym (neg-involutiveᵥ v)))
    where
      h : T (u +ᵥ negᵥ v) ≡ 0ᵥ
      h = trans (T-add u (negᵥ v))
            (trans (cong (T u +ᵥ_) (T-neg T T-add v))
              (trans (cong (λ z → T u +ᵥ negᵥ z) (sym e)) (+ᵥ-invʳ (T u))))
      hv : negᵥ v ≡ negᵥ u
      hv = neg-unique u (negᵥ v) (ker-triv (u +ᵥ negᵥ v) h)

  -- **泛型弱 Schur**：T 加性、与作用交换、表示不可约
  -- ⟹ T ≡ 0 或 T 双射（单射 × 满射）。
  weak-schur : (T : V → V)
    → (∀ v w → T (v +ᵥ w) ≡ T v +ᵥ T w)
    → (∀ g v → T (act g v) ≡ act g (T v))
    → Irreducible
    → (∀ v → T v ≡ 0ᵥ)
      ⊎ ((∀ u v → T u ≡ T v → u ≡ v) × (∀ v → Σ V (λ u → T u ≡ v)))
  weak-schur T T-add T-comm irred
    with irred (λ v → T v ≡ 0ᵥ) (T-zero T T-add) (ker-sub-add T T-add)
               (comm-ker-stable T T-comm)
  ... | inj₁ full = inj₁ full
  ... | inj₂ ker-triv
      with irred (λ v → Σ V (λ u → T u ≡ v)) (0ᵥ , T-zero T T-add)
                 (im-sub-add T T-add) (im-sub-act T T-comm)
  ...   | inj₁ im-full = inj₂ (ker-triv-injective T T-add ker-triv , im-full)
  ...   | inj₂ im-triv = inj₁ (λ v → im-triv (T v) (v , refl))

-- C₄ 作用上的 SchurCore 实例（供 §5 具体装配）
module C4Schur = SchurCore V2Space ρc4 ρc4-add

--------------------------------------------------------------------------------
-- §2. V₂ ≅ Fin 9 有限抽屉 〔refl 枚举 + 结构证明〕
--------------------------------------------------------------------------------

to9 : V2 → Fin 9
to9 (v2 zero zero) = zero
to9 (v2 zero (suc zero)) = suc zero
to9 (v2 zero (suc (suc zero))) = suc (suc zero)
to9 (v2 (suc zero) zero) = suc (suc (suc zero))
to9 (v2 (suc zero) (suc zero)) = suc (suc (suc (suc zero)))
to9 (v2 (suc zero) (suc (suc zero))) = suc (suc (suc (suc (suc zero))))
to9 (v2 (suc (suc zero)) zero) = suc (suc (suc (suc (suc (suc zero)))))
to9 (v2 (suc (suc zero)) (suc zero)) = suc (suc (suc (suc (suc (suc (suc zero))))))
to9 (v2 (suc (suc zero)) (suc (suc zero))) =
  suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

from9 : Fin 9 → V2
from9 zero = v2 0₃ 0₃
from9 (suc zero) = v2 0₃ 1₃
from9 (suc (suc zero)) = v2 0₃ 2₃
from9 (suc (suc (suc zero))) = v2 1₃ 0₃
from9 (suc (suc (suc (suc zero)))) = v2 1₃ 1₃
from9 (suc (suc (suc (suc (suc zero))))) = v2 1₃ 2₃
from9 (suc (suc (suc (suc (suc (suc zero)))))) = v2 2₃ 0₃
from9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = v2 2₃ 1₃
from9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = v2 2₃ 2₃

from9-to9 : ∀ (v : V2) → from9 (to9 v) ≡ v
from9-to9 (v2 zero zero) = refl
from9-to9 (v2 zero (suc zero)) = refl
from9-to9 (v2 zero (suc (suc zero))) = refl
from9-to9 (v2 (suc zero) zero) = refl
from9-to9 (v2 (suc zero) (suc zero)) = refl
from9-to9 (v2 (suc zero) (suc (suc zero))) = refl
from9-to9 (v2 (suc (suc zero)) zero) = refl
from9-to9 (v2 (suc (suc zero)) (suc zero)) = refl
from9-to9 (v2 (suc (suc zero)) (suc (suc zero))) = refl

to9-from9 : ∀ (i : Fin 9) → to9 (from9 i) ≡ i
to9-from9 zero = refl
to9-from9 (suc zero) = refl
to9-from9 (suc (suc zero)) = refl
to9-from9 (suc (suc (suc zero))) = refl
to9-from9 (suc (suc (suc (suc zero)))) = refl
to9-from9 (suc (suc (suc (suc (suc zero))))) = refl
to9-from9 (suc (suc (suc (suc (suc (suc zero)))))) = refl
to9-from9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
to9-from9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl

to9-inj : ∀ {u w : V2} → to9 u ≡ to9 w → u ≡ w
to9-inj {u} {w} e =
  trans (sym (from9-to9 u)) (trans (cong from9 e) (from9-to9 w))

-- Fin 9 单射 ⇒ 满射（stdlib pigeonhole 的碰撞形式 + punchOut/punchIn 装配）
fin9-inj⇒surj : (f : Fin 9 → Fin 9)
  → (∀ x y → f x ≡ f y → x ≡ y)
  → ∀ z → Σ (Fin 9) (λ x → f x ≡ z)
fin9-inj⇒surj f finj z with any? (λ x → f x ≟ z)
... | yes (x , e) = x , e
... | no miss = ⊥-elim (contra (pigeonhole 8<9 g))
  where
    z≢fx : ∀ x → z ≢ f x
    z≢fx x e = miss (x , sym e)

    g : Fin 9 → Fin 8
    g x = punchOut (z≢fx x)

    8<9 : 8 < 9
    8<9 = s<s (s<s (s<s (s<s (s<s (s<s (s<s (s<s z<s)))))))

    contra : (∃₂ λ i j → i <ᶠ j × g i ≡ g j) → ⊥
    contra (i , j , i<j , gi≡gj) = <ᶠ-irrefl i≡j i<j
      where
        fi : punchIn z (g i) ≡ f i
        fi = punchIn-punchOut (z≢fx i)
        fj : punchIn z (g j) ≡ f j
        fj = punchIn-punchOut (z≢fx j)
        fi≡fj : f i ≡ f j
        fi≡fj = trans (sym fi) (trans (cong (punchIn z) gi≡gj) fj)
        i≡j : i ≡ j
        i≡j = finj i j fi≡fj

private
  s9inj : (s : V2 → V2) → (∀ x y → s x ≡ s y → x ≡ y)
        → ∀ x y → (to9 ∘ s ∘ from9) x ≡ (to9 ∘ s ∘ from9) y → x ≡ y
  s9inj s sinj x y e =
    trans (sym (to9-from9 x))
      (trans (cong to9 (sinj (from9 x) (from9 y) (to9-inj e))) (to9-from9 y))

-- V₂ 单射 ⇒ 满射（9 元载体的抽屉原理）
injV2⇒surjV2 : (s : V2 → V2)
  → (∀ x y → s x ≡ s y → x ≡ y)
  → ∀ z → Σ V2 (λ x → s x ≡ z)
injV2⇒surjV2 s sinj z with fin9-inj⇒surj (to9 ∘ s ∘ from9) (s9inj s sinj) (to9 z)
... | x , e = from9 x , to9-inj e

--------------------------------------------------------------------------------
-- §3. V₂ 上的可判定搜索 〔refl 枚举 + any?〕
--------------------------------------------------------------------------------

v2-dec : (u w : V2) → (u ≡ w) ⊎ (u ≢ w)
v2-dec (v2 a b) (v2 a' b') with a ≟ a' | b ≟ b'
... | yes ea | yes eb = inj₁ (v2-ext ea eb)
... | yes ea | no nb  = inj₂ (λ e → nb (cong y e))
... | no na  | _      = inj₂ (λ e → na (cong x e))

fin3-tri : ∀ (c : Fin 3) → c ≡ 0₃ ⊎ (c ≡ 1₃ ⊎ c ≡ 2₃)
fin3-tri zero = inj₁ refl
fin3-tri (suc zero) = inj₂ (inj₁ refl)
fin3-tri (suc (suc zero)) = inj₂ (inj₂ refl)

dec-neg : ∀ {A : Set} → Dec A → Dec (¬ A)
dec-neg (yes a) = no (λ f → f a)
dec-neg (no na) = yes na

dec-conj : ∀ {A B : Set} → Dec A → (A → Dec B) → Dec (A × B)
dec-conj (yes a) f with f a
... | yes b = yes (a , b)
... | no nb = no (λ p → nb (proj₂ p))
dec-conj (no na) _ = no (λ p → na (proj₁ p))

dec-ne0 : (u : V2) → Dec (u ≢ 0ᵥ2)
dec-ne0 u with v2-dec u 0ᵥ2
... | inj₁ e  = no (λ f → f e)
... | inj₂ ne = yes ne

-- 二择一搜索①：Q 全空间，或给出 ¬Q 的反例点
full-or-miss : (Q : V2 → Set) → (∀ v → Dec (Q v))
  → (∀ v → Q v) ⊎ (Σ V2 (λ v → ¬ Q v))
full-or-miss Q decQ with any? (λ i → dec-neg (decQ (from9 i)))
... | yes (i , nQi) = inj₂ (from9 i , nQi)
... | no miss = inj₁ cover
  where
    cover : ∀ v → Q v
    cover v with decQ v
    ... | yes q = q
    ... | no nq = ⊥-elim (miss (to9 v , λ q' → nq (subst Q (from9-to9 v) q')))

-- 二择一搜索②：Q 有非零元，或 Q 全为零
nonzero-or-trivial : (Q : V2 → Set) → (∀ v → Dec (Q v))
  → (Σ V2 (λ u → Q u × u ≢ 0ᵥ2)) ⊎ (∀ u → Q u → u ≡ 0ᵥ2)
nonzero-or-trivial Q decQ
  with any? (λ i → dec-conj (dec-ne0 (from9 i)) (λ ne → decQ (from9 i)))
... | yes (i , ne , Qi) = inj₁ (from9 i , Qi , ne)
... | no miss = inj₂ triv
  where
    triv : ∀ u → Q u → u ≡ 0ᵥ2
    triv u Qu with dec-ne0 u | v2-dec u 0ᵥ2
    ... | yes ne | inj₁ eq = ⊥-elim (ne eq)
    ... | yes ne | inj₂ ineq = ⊥-elim (miss (to9 u ,
        (λ h → ne (subst (λ w → w ≡ 0ᵥ2) (from9-to9 u) h)) ,
        subst Q (sym (from9-to9 u)) Qu))
    ... | no nne | inj₁ eq = eq
    ... | no nne | inj₂ ineq = ⊥-elim (nne ineq)

--------------------------------------------------------------------------------
-- §4. 象限排除 〔结构证明〕
--
-- 排除「Q 含非零元 u₀ 且漏掉 v₀」：否则 u₀ 是公共特征向量（case-1，
-- 与 c4-no-invariant-line 矛盾），或 {u₀, Ru₀} 独立 ⟹ 九和盖满 V₂
-- （case-2，抽屉原理）⟹ Q = V。
--------------------------------------------------------------------------------

private
  span-not-elim : ∀ (u₀ w : V2)
    → w ≢ smul2 0₃ u₀ → w ≢ smul2 1₃ u₀ → w ≢ smul2 2₃ u₀
    → ¬ Σ (Fin 3) (λ c → w ≡ smul2 c u₀)
  span-not-elim u₀ w n0 n1 n2 (zero , e) = n0 e
  span-not-elim u₀ w n0 n1 n2 (suc zero , e) = n1 e
  span-not-elim u₀ w n0 n1 n2 (suc (suc zero) , e) = n2 e

  span-dec : ∀ (u₀ w : V2) → Dec (Σ (Fin 3) (λ c → w ≡ smul2 c u₀))
  span-dec u₀ w with v2-dec w (smul2 0₃ u₀) | v2-dec w (smul2 1₃ u₀) | v2-dec w (smul2 2₃ u₀)
  span-dec u₀ w | inj₁ e | _ | _ = yes (zero , e)
  span-dec u₀ w | inj₂ _ | inj₁ e | _ = yes (suc zero , e)
  span-dec u₀ w | inj₂ _ | inj₂ _ | inj₁ e = yes (suc (suc zero) , e)
  span-dec u₀ w | inj₂ n0 | inj₂ n1 | inj₂ n2 = no (span-not-elim u₀ w n0 n1 n2)

quadrant-kill : (Q : V2 → Set)
  → Q 0ᵥ2
  → (∀ u v → Q u → Q v → Q (u +ᵥ2 v))
  → (∀ g u → Q u → Q (ρc4 g u))
  → Σ V2 (λ u₀ → Q u₀ × u₀ ≢ 0ᵥ2)
  → Σ V2 (λ v₀ → ¬ Q v₀)
  → ⊥
quadrant-kill Q Q0 Qadd Qact (u₀ , Qu₀ , u₀nz) (v₀ , ¬Qv₀)
  with span-dec u₀ (R2 u₀)
... | yes (c , e) = ⊥-elim (c4-no-invariant-line (u₀ , u₀nz , eig))
  where
    -- case-1：Ru₀ = c·u₀ ⟹ u₀ 是全部 ρc₄(g) 的公共特征向量
    eig : ∀ g → Σ (Fin 3) (λ c' → ρc4 g u₀ ≡ smul2 c' u₀)
    eig zero = 1₃ , refl
    eig (suc zero) = c , e
    eig (suc (suc zero)) = 2₃ , neg≡2ᵥ u₀
    eig (suc (suc (suc zero))) = mul3ᴵ 2₃ c , RR-chain
      where
        RR-chain : ρc4 (suc (suc (suc zero))) u₀ ≡ smul2 (mul3ᴵ 2₃ c) u₀
        RR-chain =
          begin
            RRR2 u₀
              ≡⟨ RRR2≡R∘RR u₀ ⟩
            R2 (RR2 u₀)
              ≡⟨ cong R2 (neg≡2ᵥ u₀) ⟩
            R2 (smul2 2₃ u₀)
              ≡⟨ R-smulᴵ 2₃ u₀ ⟩
            smul2 2₃ (R2 u₀)
              ≡⟨ cong (smul2 2₃) e ⟩
            smul2 2₃ (smul2 c u₀)
              ≡⟨ smul-mul 2₃ c u₀ ⟩
            smul2 (mul3ᴵ 2₃ c) u₀
          ∎
          where open ≡-Reasoning
... | no ∉span = ⊥-elim (¬Qv₀ (Qcover v₀))
  where
    -- case-2：Ru₀ ∉ span(u₀) ⟹ (a,b) ↦ a·u₀ + b·Ru₀ 单射 ⟹ 满射
    --        ⟹ Q 含全部九个和 ⟹ Q = V ⟹ 与 ¬Qv₀ 矛盾
    w : V2
    w = R2 u₀

    Qw : Q w
    Qw = Qact (suc zero) u₀ Qu₀

    s : V2 → V2
    s (v2 p q) = smul2 p u₀ +ᵥ2 smul2 q w

    cancel-neg : ∀ x y → x ≡ y → x +ᵥ2 negᵥ2 y ≡ 0ᵥ2
    cancel-neg x y e = trans (cong (λ z → z +ᵥ2 negᵥ2 y) e)
                             (V2Ops.+ᵥ-invʳ y)

    -- 差标准化：s x ≡ s y ⟹ (da)·u₀ + (db)·w ≡ 0
    step1 : ∀ p q p' q' → s (v2 p q) ≡ s (v2 p' q')
      → smul2 (p +₃ᴵ neg₃ᴵ p') u₀ +ᵥ2 smul2 (q +₃ᴵ neg₃ᴵ q') w ≡ 0ᵥ2
    step1 p q p' q' e =
      begin
        smul2 (p +₃ᴵ neg₃ᴵ p') u₀ +ᵥ2 smul2 (q +₃ᴵ neg₃ᴵ q') w
          ≡⟨ cong₂ _+ᵥ2_ (sym (smul2-add p (neg₃ᴵ p') u₀))
                         (sym (smul2-add q (neg₃ᴵ q') w)) ⟩
        (smul2 p u₀ +ᵥ2 smul2 (neg₃ᴵ p') u₀)
          +ᵥ2 (smul2 q w +ᵥ2 smul2 (neg₃ᴵ q') w)
          ≡⟨ cong₂ _+ᵥ2_ (cong (smul2 p u₀ +ᵥ2_) (sym (smul-neg p' u₀)))
                         (cong (smul2 q w +ᵥ2_) (sym (smul-neg q' w))) ⟩
        (smul2 p u₀ +ᵥ2 negᵥ2 (smul2 p' u₀))
          +ᵥ2 (smul2 q w +ᵥ2 negᵥ2 (smul2 q' w))
          ≡⟨ V2Ops.+ᵥ-shuffle (smul2 p u₀) (negᵥ2 (smul2 p' u₀))
                              (smul2 q w) (negᵥ2 (smul2 q' w)) ⟩
        (smul2 p u₀ +ᵥ2 smul2 q w)
          +ᵥ2 (negᵥ2 (smul2 p' u₀) +ᵥ2 negᵥ2 (smul2 q' w))
          ≡⟨ cong ((smul2 p u₀ +ᵥ2 smul2 q w) +ᵥ2_)
                   (sym (V2Ops.neg-add (smul2 p' u₀) (smul2 q' w))) ⟩
        (smul2 p u₀ +ᵥ2 smul2 q w)
          +ᵥ2 negᵥ2 (smul2 p' u₀ +ᵥ2 smul2 q' w)
          ≡⟨ cancel-neg (smul2 p u₀ +ᵥ2 smul2 q w)
                        (smul2 p' u₀ +ᵥ2 smul2 q' w) e ⟩
        0ᵥ2
      ∎
      where open ≡-Reasoning

    -- db 分支公共件：w ≡ (−da)·u₀（即 w ∈ span(u₀)，与 ∉span 矛盾）
    w-in-span : ∀ da → smul2 da u₀ +ᵥ2 w ≡ 0ᵥ2
              → w ≡ smul2 (neg₃ᴵ da) u₀
    w-in-span da h =
      trans (V2Ops.neg-involutiveᵥ w)
        (trans (cong negᵥ2 (sym (V2Ops.add-neg-flip (smul2 da u₀) w h)))
               (smul-neg da u₀))

    s-inj : ∀ x y → s x ≡ s y → x ≡ y
    s-inj (v2 p q) (v2 p' q') e with fin3-tri (q +₃ᴵ neg₃ᴵ q')
    ... | inj₁ db≡0 = v2-ext p≡p' q≡q'
      where
        da : Fin 3
        da = p +₃ᴵ neg₃ᴵ p'
        -- step1 的 db 槽改写为 0₃（smul2 0₃ w ≡ 0ᵥ2 定义性）
        h₀ : smul2 da u₀ ≡ 0ᵥ2
        h₀ = trans (sym (V2Ops.+ᵥ-idʳ (smul2 da u₀)))
               (trans (cong (λ z → smul2 da u₀ +ᵥ2 smul2 z w) (sym db≡0))
                      (step1 p q p' q' e))
        p≡p' : p ≡ p'
        p≡p' = diff-zero p p' (smul-zero-split u₀ u₀nz da h₀)
        q≡q' : q ≡ q'
        q≡q' = diff-zero q q' db≡0
    ... | inj₂ (inj₁ db≡1) = ⊥-elim (∉span (neg₃ᴵ da , w≡span))
      where
        da : Fin 3
        da = p +₃ᴵ neg₃ᴵ p'
        h₀ : smul2 da u₀ +ᵥ2 w ≡ 0ᵥ2
        h₀ = trans (sym (cong (λ z → smul2 da u₀ +ᵥ2 smul2 z w) db≡1))
               (step1 p q p' q' e)
        w≡span : w ≡ smul2 (neg₃ᴵ da) u₀
        w≡span = w-in-span da h₀
    ... | inj₂ (inj₂ db≡2) = ⊥-elim (∉span (neg₃ᴵ (mul3ᴵ 2₃ da) , w≡span))
      where
        da : Fin 3
        da = p +₃ᴵ neg₃ᴵ p'
        -- h : da·u₀ + 2·w ≡ 0；两侧乘 2：2·da·u₀ + w ≡ 0（2·2 = 1）
        h₁ : smul2 da u₀ +ᵥ2 smul2 2₃ w ≡ 0ᵥ2
        h₁ = trans (sym (cong (λ z → smul2 da u₀ +ᵥ2 smul2 z w) db≡2))
               (step1 p q p' q' e)
        h₃ : smul2 (mul3ᴵ 2₃ da) u₀ +ᵥ2 w ≡ 0ᵥ2
        h₃ =
          trans (cong₂ _+ᵥ2_ (sym (smul-mul 2₃ da u₀)) (sym (smul-mul 2₃ 2₃ w)))
            (trans (V2Ops.+ᵥ-shuffle (smul2 da u₀) (smul2 da u₀)
                               (smul2 2₃ w) (smul2 2₃ w))
              (trans (cong (smul2 2₃) h₁) (smul2-zeroᵥ 2₃)))
        w≡span : w ≡ smul2 (neg₃ᴵ (mul3ᴵ 2₃ da)) u₀
        w≡span = w-in-span (mul3ᴵ 2₃ da) h₃

    spanQ : ∀ c → Q (smul2 c u₀)
    spanQ zero = Q0
    spanQ (suc zero) = Qu₀
    spanQ (suc (suc zero)) = Qadd u₀ u₀ Qu₀ Qu₀

    spanQw : ∀ c → Q (smul2 c w)
    spanQw zero = Q0
    spanQw (suc zero) = Qw
    spanQw (suc (suc zero)) = Qadd w w Qw Qw

    Qcover : ∀ z → Q z
    Qcover z with injV2⇒surjV2 s s-inj z
    ... | (v2 p q , e) = subst Q e (Qadd (smul2 p u₀) (smul2 q w) (spanQ p) (spanQw q))

    surj-v₀ : Σ V2 (λ u → s u ≡ v₀)
    surj-v₀ = injV2⇒surjV2 s s-inj v₀

--------------------------------------------------------------------------------
-- §5. C₄ 实例组合 〔结构证明〕
--------------------------------------------------------------------------------

-- ρc₄ 满足（可判定版）抽象不可约：接 c4-no-invariant-line
c4-irreducible-dec : (Q : V2 → Set)
  → (∀ v → Dec (Q v))
  → Q 0ᵥ2
  → (∀ u v → Q u → Q v → Q (u +ᵥ2 v))
  → (∀ g u → Q u → Q (ρc4 g u))
  → (∀ v → Q v) ⊎ (∀ u → Q u → u ≡ 0ᵥ2)
c4-irreducible-dec Q decQ Q0 Qadd Qact with full-or-miss Q decQ
... | inj₁ full = inj₁ full
... | inj₂ (v₀ , ¬Qv₀) with nonzero-or-trivial Q decQ
...   | inj₂ triv = inj₂ triv
...   | inj₁ (u₀ , Qu₀ , u₀nz) =
          ⊥-elim (quadrant-kill Q Q0 Qadd Qact (u₀ , Qu₀ , u₀nz) (v₀ , ¬Qv₀))

private
  -- v2-dec 的 ⊎ 形与 Dec 的桥（本地 stdlib 无现成 from-⊎）
  ⊎→Dec : ∀ {A : Set} → A ⊎ (A → ⊥) → Dec A
  ⊎→Dec (inj₁ a) = yes a
  ⊎→Dec (inj₂ na) = no na

  c4-ker-dichotomy : (T : V2 → V2)
    → (∀ v w → T (v +ᵥ2 w) ≡ T v +ᵥ2 T w)
    → (∀ g v → T (ρc4 g v) ≡ ρc4 g (T v))
    → (∀ v → T v ≡ 0ᵥ2) ⊎ (∀ u → T u ≡ 0ᵥ2 → u ≡ 0ᵥ2)
  c4-ker-dichotomy T T-add T-comm =
    c4-irreducible-dec (λ v → T v ≡ 0ᵥ2)
      (λ v → ⊎→Dec (v2-dec (T v) 0ᵥ2))
      (C4Schur.T-zero T T-add)
      (λ u v eu ev → trans (T-add u v) (trans (cong₂ _+ᵥ2_ eu ev) (+ᵥ2-idˡ _)))
      (λ g u eu → trans (T-comm g u) (trans (cong (ρc4 g) eu) (ρc4-zero g)))

-- **二维弱 Schur（C₄ 实例，完全闭合）**：T 与一切 ρc₄(g) 交换
-- ⟹ T ≡ 0 或 T 双射。
c4-weak-schur : (T : V2 → V2)
  → (∀ v w → T (v +ᵥ2 w) ≡ T v +ᵥ2 T w)
  → (∀ g v → T (ρc4 g v) ≡ ρc4 g (T v))
  → (∀ v → T v ≡ 0ᵥ2)
    ⊎ ((∀ u v → T u ≡ T v → u ≡ v) × (∀ v → Σ V2 (λ u → T u ≡ v)))
c4-weak-schur T T-add T-comm with c4-ker-dichotomy T T-add T-comm
... | inj₁ full = inj₁ full
... | inj₂ ker-triv =
      inj₂ ( C4Schur.ker-triv-injective T T-add ker-triv
           , injV2⇒surjV2 T (C4Schur.ker-triv-injective T T-add ker-triv) )

--------------------------------------------------------------------------------
-- §6. 完整 Schur 在 GF(3) 上为假：交换非标量的反例 〔refl 枚举〕
--
-- T := ρc₄(1) = R。与一切 ρc₄(g) 交换（C₄ 交换 + R⁴ = id），
-- 但 R ≠ c·I 对一切 c ∈ GF(3)（特征值 ±i ∉ GF(3)）。
-- 同时 R 双射——弱 Schur 的「可逆」支仍然成立，两者相容。
--------------------------------------------------------------------------------

R-comm : ∀ (g : Fin 4) (v : V2) → R2 (ρc4 g v) ≡ ρc4 g (R2 v)
R-comm zero v = refl
R-comm (suc zero) v = refl
R-comm (suc (suc zero)) v = refl
R-comm (suc (suc (suc zero))) (v2 a b) =
  v2-ext (neg₃ᴵ-involutive a) (sym (neg₃ᴵ-involutive b))

R-not-scalar : ∀ c → ¬ (∀ v → R2 v ≡ smul2 c v)
R-not-scalar zero h = ⊥-elim (1≢0ᴵ (cong y (h (v2 1₃ 0₃))))
R-not-scalar (suc zero) h = ⊥-elim (0≢1ᴵ (cong x (h (v2 1₃ 0₃))))
R-not-scalar (suc (suc zero)) h = ⊥-elim (0≢2ᴵ (cong x (h (v2 1₃ 0₃))))

R-invertible : ∀ v → R2 (RRR2 v) ≡ v
R-invertible (v2 a b) = v2-ext (neg₃ᴵ-involutive a) refl

-- 反例包：交换 + 非标量
commute-not-scalar :
  Σ (V2 → V2) (λ T → (∀ g v → T (ρc4 g v) ≡ ρc4 g (T v))
                   × (∀ c → ¬ (∀ v → T v ≡ smul2 c v)))
commute-not-scalar = R2 , R-comm , R-not-scalar

-- 反例与弱 Schur 相容：R 落在「可逆」支（单射 × 满射）
R-bijective : (∀ u v → R2 u ≡ R2 v → u ≡ v) × (∀ v → Σ V2 (λ u → R2 u ≡ v))
R-bijective = Rinj , RRR2-surj
  where
    R2-RRR2 : ∀ v → RRR2 (R2 v) ≡ v
    R2-RRR2 (v2 a b) = v2-ext refl (neg₃ᴵ-involutive b)
    Rinj : ∀ u v → R2 u ≡ R2 v → u ≡ v
    Rinj u v e = trans (sym (R2-RRR2 u)) (trans (cong RRR2 e) (R2-RRR2 v))
    RRR2-surj : ∀ z → Σ V2 (λ u → R2 u ≡ z)
    RRR2-surj z = RRR2 z , R-invertible z

--------------------------------------------------------------------------------
-- §7. 对抗验证（独立 refl 抽查）+ 尾注
--------------------------------------------------------------------------------

_R-comm-spot : R2 (ρc4 (suc (suc zero)) (v2 1₃ 0₃))
              ≡ ρc4 (suc (suc zero)) (R2 (v2 1₃ 0₃))
_R-comm-spot = refl

_R-invertible-spot : R2 (RRR2 (v2 1₃ 2₃)) ≡ v2 1₃ 2₃
_R-invertible-spot = refl

_to9-from9-spot : to9 (from9 (suc (suc (suc (suc zero))))) ≡ suc (suc (suc (suc zero)))
_to9-from9-spot = refl

--------------------------------------------------------------------------------
-- 尾注
--
-- 0 postulate / 0 hole / 0 unsolved meta。全部构造性闭合：
--   · §1 SchurCore：泛型弱 Schur（符号证明，无案拆分，无 postulate）。
--   · §2 抽屉：stdlib pigeonhole（Fin 9 → Fin 8 碰撞形式）+ punchOut/
--     punchIn 往返装配；V₂↔Fin 9 九案编码表。
--   · §3 搜索：any? + 可判定合取；每条引理 ≤3 案。
--   · §4 象限排除：case-1 为 4 案特征值枚举（接 §Irreducible §6 实例）；
--     case-2 为符号消元链（step1 六步 + finish 3 案）。
--   · §5–§6：组合与反例。
-- 与 BilinearSchur2A4 无重复：彼为 Z[ω] 矩阵系数的正交关系
-- （Σ_g ρᵢⱼ·ρₖₗ = 12·εᵢₖ·εⱼₗ，双线性型），本模块为端态环刚性
-- （交换 ⟹ 可逆或零）——同名「Schur」不同定理，且彼在 Synthesis 层
-- （层内纪律：本模块未 import 任何 Synthesis/ 模块 ✓）。
-- 未修改任何既有文件 ✓；未执行 git 操作 ✓。
--------------------------------------------------------------------------------
