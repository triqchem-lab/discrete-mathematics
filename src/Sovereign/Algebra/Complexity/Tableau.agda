{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.Tableau
-- Tableau 的局部编码层：抽象原子上的 CNF + 「每格恰好一个值」—— 里程碑 M3a
--
-- 【本件在 Cook–Levin 里的位置】M2 给了机器级 NP（`InNP-TM`）；M3 要把「p n 步内
-- 接受」编成 CNF。编码的第一层就是**每格恰一值**（每时刻每格恰有一个符号、
-- 每时刻恰有一个状态），本件只做这一层 + 它到 `CNF.Formula'` 的搬运。
--
-- 【架构决定（写进设计，避免后期返工）】
--   · **原子用乘积类型**：tableau 的原子天然是 `(时刻, 格子, 值)` 这种乘积，
--     而 `Lit m = Sign × Fin (suc m)` 要求线性下标。本件把「抽象原子上的 CNF」
--     与「线性化」分开：组合工作都在抽象原子上做（§1–§4），线性化只做**一次**（§5）。
--   · **搬运只需要一个函数**：`AtoCNF-sat` 对**任意** `e : A → Fin (suc m)` 成立
--     ——不需要 `e` 单射或满射。单射/上界只在「`e` 必须落在 `Fin` 内」时才用
--     （M3c 一处算术），不是每族子句各来一次。这条把「变量编号」从全局风险
--     降成一处局部义务。
--
-- 【三值语义带来的编码形态（与二值 CNF 不同，必须记）】本库赋值是 {T₀,T₁,T₂}：
-- 文字真 ⟺ 值为 T₁（正文字）/ T₂（负文字）。于是「某格取 x」要说成
--   · 至少一个：`⋁_v (v)`（长子句 ⟹ 落到 3-CNF 需 M1 的 `tseitin-split`）；
--   · 至多一个：成对 `¬u ∨ ¬v`——它**强制**未被选中的值是 **T₂**（不是 T₀）：
--     若 u 为 T₁ 而 v 为 T₀，则 `¬u` 与 `¬v` 都假 ⟹ 子句假。
-- 所以「满足赋值」= 每格恰好一个 T₁、同族其余为 T₂，与 GF(3) 的 +1/−1 读法一致。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.Tableau where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Bool.Properties using (∨-assoc; ∧-assoc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; lookup) renaming ([] to vNil; _∷_ to _v∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; Lit; Asg; evalLit; isT₁)
open import Sovereign.Algebra.Complexity.CNF using (Formula'; satClause'; satFormula')
open import Sovereign.Algebra.Complexity.CNF-Tseitin using (Bool-⊥; ∧-trueˡ; ∧-trueʳ)

-- ────────────────────────────────────────────────────────────────────
-- §1 抽象原子上的 CNF〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 与 CNF.agda 同构，但原子类型是参数：赋值是 `A → Trit` 而非 `Vec Trit`。

TEnv : Set → Set
TEnv A = A → Trit

ALit : Set → Set
ALit A = Sign × A

satALit : ∀ {A : Set} → TEnv A → ALit A → Bool
satALit env (σ₊ , x) = isT₁ (env x)
satALit env (σ₋ , x) = isT₁ (negate (env x))

satAClause : ∀ {A : Set} → TEnv A → List (ALit A) → Bool
satAClause env []       = false
satAClause env (l ∷ ls) = satALit env l ∨ satAClause env ls

satAFormula : ∀ {A : Set} → TEnv A → List (List (ALit A)) → Bool
satAFormula env []       = true
satAFormula env (cl ∷ φ) = satAClause env cl ∧ satAFormula env φ

-- 三值的「真」只有 T₁（用 SATMember 的 `isT₁`：与 `satClause'`/`evalLit` 同源）
Tr-isT₁-true : ∀ (t : Trit) → isT₁ t ≡ true → t ≡ T₁
Tr-isT₁-true T₀ ()
Tr-isT₁-true T₁ h = refl
Tr-isT₁-true T₂ ()

-- ────────────────────────────────────────────────────────────────────
-- §2 拼接、成员、全真投影〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

satAClause-++ : ∀ {A : Set} (env : TEnv A) (xs ys : List (ALit A))
              → satAClause env (xs ++ ys) ≡ (satAClause env xs ∨ satAClause env ys)
satAClause-++ env []       ys = refl
satAClause-++ env (x ∷ xs) ys =
  trans (cong (satALit env x ∨_) (satAClause-++ env xs ys))
        (sym (∨-assoc (satALit env x) (satAClause env xs) (satAClause env ys)))

satAFormula-++ : ∀ {A : Set} (env : TEnv A) (φ ψ : List (List (ALit A)))
               → satAFormula env (φ ++ ψ) ≡ (satAFormula env φ ∧ satAFormula env ψ)
satAFormula-++ env []       ψ = refl
satAFormula-++ env (cl ∷ φ) ψ =
  trans (cong (satAClause env cl ∧_) (satAFormula-++ env φ ψ))
        (sym (∧-assoc (satAClause env cl) (satAFormula env φ) (satAFormula env ψ)))

-- 成员关系（本件自用，避免与库内命题化 `_∈_` 纠缠）
_∈ᴸ_ : ∀ {A : Set} → A → List A → Set
x ∈ᴸ []       = ⊥
x ∈ᴸ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ᴸ ys)

∈ᴸ-here : ∀ {A : Set} {x y : A} {ys} → x ≡ y → x ∈ᴸ (y ∷ ys)
∈ᴸ-here = inj₁

∈ᴸ-there : ∀ {A : Set} {x y : A} {ys} → x ∈ᴸ ys → x ∈ᴸ (y ∷ ys)
∈ᴸ-there = inj₂

∈ᴸ-map : ∀ {A B : Set} (f : A → B) {x : A} {xs : List A}
       → x ∈ᴸ xs → f x ∈ᴸ map f xs
∈ᴸ-map f {xs = []}     ()
∈ᴸ-map f {xs = y ∷ ys} (inj₁ refl) = ∈ᴸ-here refl
∈ᴸ-map f {xs = y ∷ ys} (inj₂ q)    = ∈ᴸ-there (∈ᴸ-map f q)

∈ᴸ-++ˡ : ∀ {A : Set} {x : A} (xs ys : List A) → x ∈ᴸ xs → x ∈ᴸ (xs ++ ys)
∈ᴸ-++ˡ []       ys ()
∈ᴸ-++ˡ (z ∷ xs) ys (inj₁ refl) = ∈ᴸ-here refl
∈ᴸ-++ˡ (z ∷ xs) ys (inj₂ q)    = ∈ᴸ-there (∈ᴸ-++ˡ xs ys q)

-- 公式全真 ⟹ 任何成员子句为真
satAFormula-all : ∀ {A : Set} (env : TEnv A) (φ : List (List (ALit A))) (cl : List (ALit A))
                → satAFormula env φ ≡ true → cl ∈ᴸ φ → satAClause env cl ≡ true
satAFormula-all env []       cl h ()
satAFormula-all env (cl ∷ φ) .cl h (inj₁ refl)  = ∧-trueˡ h
satAFormula-all env (cl ∷ φ) cl′ h (inj₂ q)     = satAFormula-all env φ cl′ (∧-trueʳ h) q

-- ────────────────────────────────────────────────────────────────────
-- §3 至多一个：成对 `¬u ∨ ¬v`〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

pairsWith : ∀ {A : Set} → List A → List (List (ALit A))
pairsWith []       = []
pairsWith (x ∷ xs) = map (λ y → (σ₋ , x) ∷ ((σ₋ , y) ∷ [])) xs ++ pairsWith xs

-- `pairsWith` 里确实含「x 与某个 y」那一对
pairsWith-pair : ∀ {A : Set} (x y : A) (xs : List A)
               → y ∈ᴸ xs → ((σ₋ , x) ∷ ((σ₋ , y) ∷ [])) ∈ᴸ pairsWith (x ∷ xs)
pairsWith-pair x y xs q = ∈ᴸ-++ˡ _ _ (∈ᴸ-map (λ z → (σ₋ , x) ∷ ((σ₋ , z) ∷ [])) q)

-- 两个都为真 ⟹ 它们的成对子句为假（与「全真」矛盾）
notBoth : ∀ {A : Set} (env : TEnv A) (x y : A)
        → env x ≡ T₁ → env y ≡ T₁
        → satAClause env ((σ₋ , x) ∷ ((σ₋ , y) ∷ [])) ≡ true → ⊥
notBoth env x y ex ey h =
  Bool-⊥ (trans (sym (trans
             (cong (λ z → isT₁ (negate z) ∨ (isT₁ (negate (env y)) ∨ false)) ex)
             (cong (λ z → isT₁ (negate T₁) ∨ (isT₁ (negate z) ∨ false)) ey))) h)

-- 「值为假」+「值等于 T₁」矛盾
not-true : ∀ (t : Trit) → isT₁ t ≡ false → t ≡ T₁ → ⊥
not-true T₀ e ()
not-true T₁ e _ = Bool-⊥ (sym e)
not-true T₂ e ()

-- ────────────────────────────────────────────────────────────────────
-- §4 恰好一个（`oneHot`）与提取〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 长子句（至少一个）+ 成对子句（至多一个）。长子句长度 = |vs| ⟹ 落到 3-CNF 需
-- M1 的 `tseitin-split`（本层先不拆；尾注 (ii)）。

oneHot : ∀ {A : Set} → List A → List (List (ALit A))
oneHot vs = map (σ₊ ,_) vs ∷ pairsWith vs

-- 对 Bool 值的两案派发（一次性做完，避免 `with` 渗透到结论里）
bool-case : ∀ (b : Bool) {P : Set} → (b ≡ true → P) → (b ≡ false → P) → P
bool-case true  yes no = yes refl
bool-case false yes no = no refl

-- ★ 提取：`oneHot` 全真 ⟹ 存在**唯一**的 T₁ 取值成员
oneHot-sat : ∀ {A : Set} (env : TEnv A) (vs : List A)
           → satAFormula env (oneHot vs) ≡ true
           → Σ A (λ v → (v ∈ᴸ vs)
                         × (env v ≡ T₁)
                         × (∀ w → w ∈ᴸ vs → env w ≡ T₁ → v ≡ w))
oneHot-sat env [] h = ⊥-elim (Bool-⊥ h)
oneHot-sat {A} env (x ∷ xs) h = bool-case (isT₁ (env x)) branch-true branch-false
  where
  hL : satAClause env (map (σ₊ ,_) (x ∷ xs)) ≡ true
  hL = ∧-trueˡ h

  hR : satAFormula env (pairsWith (x ∷ xs)) ≡ true
  hR = ∧-trueʳ h

  uniq-from-x : env x ≡ T₁ → ∀ w → w ∈ᴸ (x ∷ xs) → env w ≡ T₁ → x ≡ w
  uniq-from-x ex w (inj₁ refl) _ = refl
  uniq-from-x ex w (inj₂ q) ew =
    ⊥-elim (notBoth env x w ex ew
              (satAFormula-all env (pairsWith (x ∷ xs))
                 ((σ₋ , x) ∷ ((σ₋ , w) ∷ [])) hR (pairsWith-pair x w xs q)))

  branch-true : isT₁ (env x) ≡ true → Σ A (λ v → (v ∈ᴸ (x ∷ xs))
                         × (env v ≡ T₁)
                         × (∀ w → w ∈ᴸ (x ∷ xs) → env w ≡ T₁ → v ≡ w))
  branch-true e =
    x , ∈ᴸ-here refl , Tr-isT₁-true (env x) e , uniq-from-x (Tr-isT₁-true (env x) e)

  branch-false : isT₁ (env x) ≡ false → Σ A (λ v → (v ∈ᴸ (x ∷ xs))
                         × (env v ≡ T₁)
                         × (∀ w → w ∈ᴸ (x ∷ xs) → env w ≡ T₁ → v ≡ w))
  branch-false e =
    proj₁ ih , ∈ᴸ-there (proj₁ (proj₂ ih)) , proj₁ (proj₂ (proj₂ ih)) , uniq
    where
    rest : satAClause env (map (σ₊ ,_) xs) ≡ true
    rest = trans (sym (cong (_∨ satAClause env (map (σ₊ ,_) xs)) e)) hL

    hR′ : satAFormula env (pairsWith xs) ≡ true
    hR′ = ∧-trueʳ (trans (sym (satAFormula-++
                     env (map (λ y → (σ₋ , x) ∷ ((σ₋ , y) ∷ [])) xs) (pairsWith xs))) hR)

    ih : Σ A (λ v → (v ∈ᴸ xs) × (env v ≡ T₁)
                      × (∀ w → w ∈ᴸ xs → env w ≡ T₁ → v ≡ w))
    ih = oneHot-sat env xs (cong₂ _∧_ rest hR′)

    uniq : ∀ w → w ∈ᴸ (x ∷ xs) → env w ≡ T₁ → proj₁ ih ≡ w
    uniq w (inj₁ refl) ew = ⊥-elim (not-true (env x) e ew)
    uniq w (inj₂ q) ew    = proj₂ (proj₂ (proj₂ ih)) w q ew

-- ────────────────────────────────────────────────────────────────────
-- §5 一次性搬运到 `CNF.Formula'`〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 只需要一个函数 `e : A → Fin (suc m)`——不需要单射/满射。

renLit : ∀ {A : Set} {m : ℕ} → (A → Fin (suc m)) → ALit A → Lit m
renLit e (s , x) = s , e x

AtoCNF : ∀ {A : Set} {m : ℕ} → (A → Fin (suc m))
       → List (List (ALit A)) → Formula' m
AtoCNF e φ = map (map (renLit e)) φ

satALit-ren : ∀ {A : Set} {m : ℕ} (e : A → Fin (suc m)) (a : Asg m) (l : ALit A)
            → satALit (λ x → lookup a (e x)) l ≡ isT₁ (evalLit a (renLit e l))
satALit-ren e a (σ₊ , x) = refl
satALit-ren e a (σ₋ , x) = refl

satAClause-ren : ∀ {A : Set} {m : ℕ} (e : A → Fin (suc m)) (a : Asg m)
                   (cl : List (ALit A))
               → satAClause (λ x → lookup a (e x)) cl
                 ≡ satClause' a (map (renLit e) cl)
satAClause-ren e a []       = refl
satAClause-ren e a (l ∷ ls) =
  cong₂ _∨_ (satALit-ren e a l) (satAClause-ren e a ls)

-- ★ 搬运保真：抽象原子上的满足 ⟺ 线性化后的 `Formula'` 满足（同一个 `Asg`）
AtoCNF-sat : ∀ {A : Set} {m : ℕ} (e : A → Fin (suc m)) (a : Asg m)
               (φ : List (List (ALit A)))
           → satAFormula (λ x → lookup a (e x)) φ ≡ satFormula' a (AtoCNF e φ)
AtoCNF-sat e a []       = refl
AtoCNF-sat e a (cl ∷ φ) =
  cong₂ _∧_ (satAClause-ren e a cl) (AtoCNF-sat e a φ)

-- ────────────────────────────────────────────────────────────────────
-- §6 核对层〔refl 枚举〕（A = Trit：值就是 trit 本身）
-- ────────────────────────────────────────────────────────────────────

-- 单值格：至少一个 ⟹ 真
Tr-check-single : satAFormula (λ (t : Trit) → t) (oneHot (T₁ ∷ [])) ≡ true
Tr-check-single = refl

-- 取 (T₁, T₂)：两个子句族都满足（T₂ 使 ¬ 为真——三值语义下的「假」）
Tr-check-two-true : satAFormula (λ (t : Trit) → t) (oneHot (T₁ ∷ (T₂ ∷ []))) ≡ true
Tr-check-two-true = refl

-- 两格都取 T₁：至多一个被违反 ⟹ 公式假
Tr-check-two-false : satAFormula (λ (_ : Trit) → T₁) (oneHot (T₁ ∷ (T₂ ∷ []))) ≡ false
Tr-check-two-false = refl

-- 提取落出第一个取 T₁ 的成员
Tr-check-extract : proj₁ (oneHot-sat (λ (t : Trit) → t) (T₁ ∷ (T₂ ∷ [])) refl) ≡ T₁
Tr-check-extract = refl

-- 搬运：抽象层与 `Formula'` 层同值（池 0 号位 = fzero）
Tr-check-transport :
  satAFormula (λ (t : Trit) → t) (oneHot (T₁ ∷ []))
  ≡ satFormula' (T₁ v∷ vNil) (AtoCNF (λ (_ : Trit) → fzero) (oneHot (T₁ ∷ [])))
Tr-check-transport = refl

-- ────────────────────────────────────────────────────────────────────
-- §7 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   本件只做「每格恰一值」这一层，**不含** tableau 的其余子句族
--       （转移一致性、初始/终止格局、非头部不变），也不含「满足 ⟹ 运行存在」的
--       提取归纳——这些是 M3b/M3c。本件不声称 CL 已闭合。
-- (ii)  长子句（至少一个，长度 |vs|）**未拆分**为 3-子句：落到 3-CNF 需要
--       M1 的 `tseitin-split` + 辅助变元的新鲜/互异（需要编号 ⟹ M3c）。
--       本层的语义是**一般 CNF**（CNF.agda §1），不是 3-CNF。
-- (iii) 承载层只给「抽象 ⟹ 线性」的保真（`AtoCNF-sat`）；它其实两边都成立
--       （同一个等式），但**没有**证明 `e` 的单射/上界——那是 M3c 的编号义务。
-- (iv)  三值语义使「未被选中的值为 T₂」成为**强制**（见头注）：这是本库
--       Kleene-强口径的直接后果，不是本件的额外选择。
-- (v)   原子乘积（`(时刻, 格子, 值)`）的**具体构造**未在此出现：本件对 `A` 完全
--       抽象，M3b 才把 `A` 实例化为 `Fin T × Fin W × Fin Γ` 并给六族子句。

-- 0 postulate / 0 hole。
