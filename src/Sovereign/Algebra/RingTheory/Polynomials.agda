{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.RingTheory.Polynomials
-- 数学背景：GF(3)[X]——系数在 GF(3) 的一元多项式环。
--   表示 = 上升序系数表 List Trit（LaurentBase「项列表」范式的单变量 GF(3) 形：
--   指数由位置承载）。例：[] = 0；T₁ ∷ [] = 1；T₀ ∷ T₁ ∷ [] = X；T₁ ∷ T₀ ∷ T₁ ∷ [] = 1 + X²。
-- 核心原则：
--   1. 0 postulate / 0 hole；
--   2. 表定义运算（加=逐点、乘=卷积）——环律由 Trit 表律逐点搬运（≤27 case 全用）；
--   3. 带余除法走 monic 线性因子（合成除法）——一般除法恒等式立界（§5）；
--   4. 复用优先：Trit 环律（⊕-identityˡ/ʳ、⊕-comm、⊕-assoc）直用零重证。
-- 包含：§0 Trit 表律补件｜§1 Poly 定义层｜§2 eval 同态三定理｜§3 合成除法与根｜§4 核对层｜§5 立界注记

module Sovereign.Algebra.RingTheory.Polynomials where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc)

-- ────────────────────────────────────────────────────────────────────
-- §0 Trit 表律补件（基础件层——Trit 未导出的乘法面律，≤27 case 表定义形）
-- ────────────────────────────────────────────────────────────────────

⊗-zeroˡ : ∀ x → T₀ ⊗ x ≡ T₀
⊗-zeroˡ T₀ = refl; ⊗-zeroˡ T₁ = refl; ⊗-zeroˡ T₂ = refl

⊗-zeroʳ : ∀ x → x ⊗ T₀ ≡ T₀
⊗-zeroʳ T₀ = refl; ⊗-zeroʳ T₁ = refl; ⊗-zeroʳ T₂ = refl

⊗-oneˡ : ∀ x → T₁ ⊗ x ≡ x
⊗-oneˡ T₀ = refl; ⊗-oneˡ T₁ = refl; ⊗-oneˡ T₂ = refl

⊗-swap : ∀ x y → x ⊗ y ≡ y ⊗ x
⊗-swap T₀ T₀ = refl; ⊗-swap T₀ T₁ = refl; ⊗-swap T₀ T₂ = refl
⊗-swap T₁ T₀ = refl; ⊗-swap T₁ T₁ = refl; ⊗-swap T₁ T₂ = refl
⊗-swap T₂ T₀ = refl; ⊗-swap T₂ T₁ = refl; ⊗-swap T₂ T₂ = refl

⊗-assoc : ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
⊗-assoc T₀ y z = refl
⊗-assoc T₁ T₀ z = refl; ⊗-assoc T₁ T₁ T₀ = refl; ⊗-assoc T₁ T₁ T₁ = refl; ⊗-assoc T₁ T₁ T₂ = refl
⊗-assoc T₁ T₂ T₀ = refl; ⊗-assoc T₁ T₂ T₁ = refl; ⊗-assoc T₁ T₂ T₂ = refl
⊗-assoc T₂ T₀ z = refl
⊗-assoc T₂ T₁ T₀ = refl; ⊗-assoc T₂ T₁ T₁ = refl; ⊗-assoc T₂ T₁ T₂ = refl
⊗-assoc T₂ T₂ T₀ = refl; ⊗-assoc T₂ T₂ T₁ = refl; ⊗-assoc T₂ T₂ T₂ = refl

⊗-distˡ : ∀ x y z → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)
⊗-distˡ T₀ T₀ T₀ = refl; ⊗-distˡ T₀ T₀ T₁ = refl; ⊗-distˡ T₀ T₀ T₂ = refl
⊗-distˡ T₀ T₁ T₀ = refl; ⊗-distˡ T₀ T₁ T₁ = refl; ⊗-distˡ T₀ T₁ T₂ = refl
⊗-distˡ T₀ T₂ T₀ = refl; ⊗-distˡ T₀ T₂ T₁ = refl; ⊗-distˡ T₀ T₂ T₂ = refl
⊗-distˡ T₁ T₀ T₀ = refl; ⊗-distˡ T₁ T₀ T₁ = refl; ⊗-distˡ T₁ T₀ T₂ = refl
⊗-distˡ T₁ T₁ T₀ = refl; ⊗-distˡ T₁ T₁ T₁ = refl; ⊗-distˡ T₁ T₁ T₂ = refl
⊗-distˡ T₁ T₂ T₀ = refl; ⊗-distˡ T₁ T₂ T₁ = refl; ⊗-distˡ T₁ T₂ T₂ = refl
⊗-distˡ T₂ T₀ T₀ = refl; ⊗-distˡ T₂ T₀ T₁ = refl; ⊗-distˡ T₂ T₀ T₂ = refl
⊗-distˡ T₂ T₁ T₀ = refl; ⊗-distˡ T₂ T₁ T₁ = refl; ⊗-distˡ T₂ T₁ T₂ = refl
⊗-distˡ T₂ T₂ T₀ = refl; ⊗-distˡ T₂ T₂ T₁ = refl; ⊗-distˡ T₂ T₂ T₂ = refl

-- 右分配（交换 + 左分配导出——3 步链）
-- 策略：(y⊕z)⊗q →q⊗(y⊕z) [swap] → (q⊗y)⊕(q⊗z) [distˡ] → (y⊗q)⊕(z⊗q) [cong₂ swap]
⊗-distʳ : ∀ q y z → (y ⊕ z) ⊗ q ≡ (y ⊗ q) ⊕ (z ⊗ q)
⊗-distʳ q y z =
  trans (⊗-swap (y ⊕ z) q)
    (trans (⊗-distˡ q y z) (cong₂ _⊕_ (⊗-swap q y) (⊗-swap q z)))

-- 中项交换：x⊗(c⊗e) ≡ c⊗(x⊗e)——assoc+swap 三步
-- 策略：x⊗(c⊗e) → (x⊗c)⊗e [sym assoc] → (c⊗x)⊗e [cong swap] → c⊗(x⊗e) [assoc]
swap-mid : ∀ x c e → x ⊗ (c ⊗ e) ≡ c ⊗ (x ⊗ e)
swap-mid x c e =
  trans (sym (⊗-assoc x c e)) (trans (cong (_⊗ e) (⊗-swap x c)) (⊗-assoc c x e))

-- 四项重排：(c⊕d)⊕(p⊕q) ≡ (c⊕p)⊕(d⊕q)（eval-+ 的代数核心）
-- 策略：(c⊕d)⊕(p⊕q) → c⊕(d⊕(p⊕q)) [assoc] → c⊕((p⊕d)⊕q) [cong (d⊕-) 换序]
--      → c⊕(p⊕(d⊕q)) [cong assoc] → (c⊕p)⊕(d⊕q) [sym assoc]
shuffle : ∀ c d p q → (c ⊕ d) ⊕ (p ⊕ q) ≡ (c ⊕ p) ⊕ (d ⊕ q)
shuffle c d p q =
  trans (⊕-assoc c d (p ⊕ q))
    (trans (cong (c ⊕_) step₂)
      (trans (cong (c ⊕_) (⊕-assoc p d q))
        (sym (⊕-assoc c p (d ⊕ q)))))
  where
  step₂ : d ⊕ (p ⊕ q) ≡ (p ⊕ d) ⊕ q
  step₂ = trans (sym (⊕-assoc d p q)) (cong (_⊕ q) (⊕-comm d p))

-- ────────────────────────────────────────────────────────────────────
-- §1 Poly 定义层（定义层——表运算）
-- ────────────────────────────────────────────────────────────────────

Poly : Set
Poly = List Trit

-- 逐点加（长度取最长——短侧零延拓）
infixl 7 _+p_
_+p_ : Poly → Poly → Poly
[] +p ys = ys
xs +p [] = xs
(x ∷ xs) +p (y ∷ ys) = (x ⊕ y) ∷ (xs +p ys)

-- 标量乘（数乘）
scale : Trit → Poly → Poly
scale c [] = []
scale c (x ∷ xs) = (c ⊗ x) ∷ scale c xs

-- 卷积乘（低位先）
infixl 7 _*p_
_*p_ : Poly → Poly → Poly
[] *p ys = []
xs *p [] = []
(x ∷ xs) *p ys = (scale x ys) +p (T₀ ∷ (xs *p ys))

-- Horner 求值
eval : Poly → Trit → Trit
eval [] x = T₀
eval (c ∷ cs) x = c ⊕ (x ⊗ eval cs x)

-- ────────────────────────────────────────────────────────────────────
-- §2 eval 同态三定理（主引理层）
-- ────────────────────────────────────────────────────────────────────

-- ① eval 加法同态
-- 策略：p=[] 走 identityˡ；q=[] 走 identityʳ；双非空走
--      (c⊕d)⊕(x⊗(e₁⊕e₂)) → (c⊕d)⊕((x⊗e₁)⊕(x⊗e₂)) [IH + distˡ] → shuffle
eval-+ : ∀ p q x → eval (p +p q) x ≡ eval p x ⊕ eval q x
eval-+ [] q x = sym (⊕-identityˡ (eval q x))
eval-+ (c ∷ cs) [] x = sym (⊕-identityʳ (eval (c ∷ cs) x))
eval-+ (c ∷ cs) (d ∷ ds) x =
  trans (cong ((c ⊕ d) ⊕_) (trans (cong (x ⊗_) (eval-+ cs ds x)) (⊗-distˡ x (eval cs x) (eval ds x))))
    (shuffle c d (x ⊗ eval cs x) (x ⊗ eval ds x))

-- ② eval 数乘引理
-- 策略：[] 走 sym ⊗-zeroʳ；cons 走 IH + swap-mid + sym distˡ
--      (c⊗y)⊕(x⊗(c⊗e)) → (c⊗y)⊕(c⊗(x⊗e)) [swap-mid] → c⊗(y⊕(x⊗e)) [sym distˡ]
eval-scale : ∀ c p x → eval (scale c p) x ≡ c ⊗ eval p x
eval-scale c [] x = sym (⊗-zeroʳ c)
eval-scale c (y ∷ ys) x =
  trans (cong ((c ⊗ y) ⊕_) (trans (cong (x ⊗_) (eval-scale c ys x)) (swap-mid x c (eval ys x))))
    (sym (⊗-distˡ c y (x ⊗ eval ys x)))

-- ③ eval 乘法同态（环同态核心）
-- 策略：cons 案 = eval-+（卷积两项）+ eval-scale + IH
--      (c⊗Q)⊕(x⊗(E⊗Q)) → (c⊗Q)⊕((x⊗E)⊗Q) [sym assoc] → (c⊕x⊗E)⊗Q [sym distʳ]
eval-* : ∀ p q x → eval (p *p q) x ≡ eval p x ⊗ eval q x
eval-* [] q x = sym (⊗-zeroˡ (eval q x))
-- q 分案（子句重叠防卡：*p 的 xs*[] 与 (x∷xs)*ys 在 q=[] 不一致——中性 q 卡展开，
--   故 cons 案按 q 显式分案使 *_p_ 定义展开可用）
eval-* (c ∷ cs) [] x = sym (⊗-zeroʳ (eval (c ∷ cs) x))
eval-* (c ∷ cs) (d ∷ ds) x =
  trans (eval-+ (scale c (d ∷ ds)) (T₀ ∷ (cs *p (d ∷ ds))) x)
    (trans (cong₂ _⊕_ (eval-scale c (d ∷ ds) x) lift₀)
      (trans (cong ((c ⊗ eval (d ∷ ds) x) ⊕_)
               (trans (cong (x ⊗_) (eval-* cs (d ∷ ds) x)) (sym (⊗-assoc x (eval cs x) (eval (d ∷ ds) x)))))
        (sym (⊗-distʳ (eval (d ∷ ds) x) c (x ⊗ eval cs x)))))
  where
  lift₀ : eval (T₀ ∷ (cs *p (d ∷ ds))) x ≡ x ⊗ eval (cs *p (d ∷ ds)) x
  lift₀ = ⊕-identityˡ (x ⊗ eval (cs *p (d ∷ ds)) x)

-- ────────────────────────────────────────────────────────────────────
-- §3 合成除法与根（组合层）
--   divmodL p r = (q , rem)：p = (X ⊖ r)·q + [rem]（monic 线性因子合成除法）
--   内部走下降序（reverse 后高位先）——合成除法标准形
-- ────────────────────────────────────────────────────────────────────

divmodL : Poly → Trit → Poly × Trit
divmodL p r with reverse p
... | [] = ([] , T₀)
... | a ∷ [] = ([] , a)
... | a ∷ rest@(_ ∷ _) = finish (go rest a)
  where
  go : List Trit → Trit → List Trit × Trit
  go (z ∷ []) b = ([] , z ⊕ (r ⊗ b))
  go (z ∷ zs@(_ ∷ _)) b = let b′ = z ⊕ (r ⊗ b) in
    let (bs , rem) = go zs b′ in (b′ ∷ bs , rem)
  go [] b = ([] , b)
  finish : List Trit × Trit → Poly × Trit
  finish (bs , rem) = (reverse (a ∷ bs) , rem)

-- 根：r 是 p 的根 ⟺ eval p r = 0
root : Poly → Trit → Set
root p r = eval p r ≡ T₀

-- 余式定理（计算形核对段）：合成除法的余式 = 求值
-- ——一般恒等式（余式=值 + 因式分解）见 §5 立界

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层（refl 级——defeq 通道）
-- ────────────────────────────────────────────────────────────────────

p-demo : Poly
p-demo = T₁ ∷ T₀ ∷ T₁ ∷ []        -- 1 + X²

-- (1+X²) ÷ (X⊖T₁)：q = X+1，rem = T₂（验算：(X−1)(X+1) = X²−1，差 2 ≡ T₂）
check-div-demo : divmodL p-demo T₁ ≡ (T₁ ∷ T₁ ∷ [] , T₂)
check-div-demo = refl

-- 退化恒等式（可证形）：零次多项式的除法恒等式 definitional 成立
-- 策略：(X⊖r)·[] + [a] = [] +p [a] = [a]——乘零 annihilator + 加零
linear-id-const : ∀ a r →
  let (q , rem) = divmodL (a ∷ []) r in
  ((negate r ∷ T₁ ∷ []) *p q) +p (rem ∷ []) ≡ a ∷ []
linear-id-const a r = refl

-- 求值同态核对（demo 点）
check-eval-+ : eval (p-demo +p p-demo) T₁ ≡ eval p-demo T₁ ⊕ eval p-demo T₁
check-eval-+ = refl

check-eval-* : eval (p-demo *p p-demo) T₂ ≡ eval p-demo T₂ ⊗ eval p-demo T₂
check-eval-* = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记（诚实边界）
--   (i)  余式=值定理（synthetic remainder ≡ eval）——需反序 Horner 等价引理 ~40-60 行；
--   (ii) 一般因式恒等式 (X⊖r)·q + [rem] ≡ p——需合成除法归纳携带 ~60-100 行
--        （构造携带形范式——Gskel cutZ 先例）；
--   (iii) 一般带余除法（任意除子 + deg 递减 + 唯一性）——~80-120 行；
--   (iv) 根-因式定理（root r → p ≡ (X⊖r)·q）——由 (ii) + rem≡T₀ 即得（依赖 (i)(ii)）。
-- ────────────────────────────────────────────────────────────────────
