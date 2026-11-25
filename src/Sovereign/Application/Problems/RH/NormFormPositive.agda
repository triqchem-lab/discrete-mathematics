{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.NormFormPositive
-- M12·W3 骨架: 范数型配方恒等式的「正性来源可定位」ℤ 承证（W-筛网形式化件之一）
--
-- 数学背景（W-筛网见 docs/Riemann/RH-GRH-五路线见证性诊断-2026-11-25.md）:
--   · 特征多项式 x² − tx + q（Vieta: α+ᾱ = t, αᾱ = q）的序上范数型
--     N = a² + t·ab + q·b²——E/F₃ 八类 t ∈ {−3..3}, q = 3;
--   · ★ 正性来源可定位（W3）= 配方恒等式: 4N = (2a+tb)² + c·b²（c = 4q − t²）,
--     4N 的 + 形由两个平方项承证（Schwarz 型——平方根屏障的序上算术骨架）;
--   · 解析侧 |α| = √q 不在本库（无 ℂ, 0-postulate 边界）——本件是其序上
--     算术投影的证书形。
--
-- 工程纪要（nightly 坑 #8 实证）: 望远镜未用变量（q 仅在结论类型）+ 算子 section
-- + 三层和重排的组合卡 meta——本件全顶层显式 + λ 替代 section + 泛化 W 形收绿;
-- ≡-Reasoning 中间行括号全显式。
-- 诚实边界: 退化分析（等号情形 a=b=0 的刻画）未展开 [构造性缺席·候选级]。

module Sovereign.Application.Problems.RH.NormFormPositive where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Integer using (ℤ; +_; -[1+_]; 0ℤ; _≡_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Data.Integer.Properties
  using (*-distribʳ-+; *-distribˡ-+; *-assoc; *-comm; +-assoc; +-comm)
open import Data.Integer.Base using (_◃_)
open import Data.Sign.Base using (Sign)
open ≡-Reasoning

--------------------------------------------------------------------------------
-- §0. 载体: 范数型的 4·N 展开（各段具名）
--------------------------------------------------------------------------------

P1form : ℤ → ℤ → ℤ
P1form a t = a *ℤ a +ℤ ((a *ℤ a +ℤ a *ℤ a) +ℤ a *ℤ a)

M4form : ℤ → ℤ → ℤ → ℤ
M4form t a b = (t *ℤ (a *ℤ b) +ℤ t *ℤ (a *ℤ b))
             +ℤ (t *ℤ (a *ℤ b) +ℤ t *ℤ (a *ℤ b))

ttbb : ℤ → ℤ → ℤ
ttbb t b = (t *ℤ t) *ℤ (b *ℤ b)

RHS : ℤ → ℕ → ℤ → ℤ → ℤ
RHS t c a b = ((a +ℤ a +ℤ t *ℤ b) *ℤ (a +ℤ a +ℤ t *ℤ b)) +ℤ ((+ c) *ℤ (b *ℤ b))

--------------------------------------------------------------------------------
-- §1. 辅助件（全顶层）
--------------------------------------------------------------------------------

-- ℕ 级析取: Sign.+ ◃ (n*n) 的 + 形证书（◃ 首子句吞 ℕ.zero, 抽象 n 卡死 → 案析取绕行）
◃+ : ∀ n → Σ ℕ (λ m → (Sign.+ Data.Integer.Base.◃ (n * n)) ≡ + m)
◃+ zero = zero , refl
◃+ (suc n) = suc n * suc n , refl

-- 平方有 + 形（任意 ℤ 的平方可写成 + n——正性证书的原料）
sq+ : ∀ i → Σ ℕ (λ n → i *ℤ i ≡ + n)
sq+ (+ n) = ◃+ n
sq+ -[1+ n ] = ◃+ (suc n)

-- 交换再结合: a * (t * b) ≡ t * (a * b)
ab-reassoc : ∀ a t b → a *ℤ (t *ℤ b) ≡ t *ℤ (a *ℤ b)
ab-reassoc a t b =
  trans (sym (*-assoc a t b))
  (trans (cong (λ w → w *ℤ b) (*-comm a t))
         (*-assoc t a b))

-- 平方再结合: (t*b)*(t*b) ≡ (t*t)*(b*b)
sq-reassoc : ∀ t b → (t *ℤ b) *ℤ (t *ℤ b) ≡ (t *ℤ t) *ℤ (b *ℤ b)
sq-reassoc t b =
  trans (*-assoc t b (t *ℤ b))
  (trans (cong (λ w → t *ℤ w) (*-comm b (t *ℤ b)))
  (trans (cong (λ w → t *ℤ w) (*-assoc t b b))
         (sym (*-assoc t t (b *ℤ b)))))

-- M0 ≡ tab+tab（distribʳ + ab-reassoc×2）
M0-lemma : ∀ a t b → (a +ℤ a) *ℤ (t *ℤ b) ≡ (t *ℤ (a *ℤ b) +ℤ t *ℤ (a *ℤ b))
M0-lemma a t b =
  trans (*-distribʳ-+ (t *ℤ b) a a)
        (cong₂ _+ℤ_ (ab-reassoc a t b) (ab-reassoc a t b))

-- 中段合并: (M0×2 + S) ≡ (M4form + ttbb)
merge : ∀ t a b
  → (((a +ℤ a) *ℤ (t *ℤ b) +ℤ (a +ℤ a) *ℤ (t *ℤ b)) +ℤ ((t *ℤ b) *ℤ (t *ℤ b)))
  ≡ ((M4form t a b) +ℤ (ttbb t b))
merge t a b =
  trans (cong (λ w → (w +ℤ w) +ℤ ((t *ℤ b) *ℤ (t *ℤ b))) (M0-lemma a t b))
        (cong (λ w → (M4form t a b) +ℤ w) (sq-reassoc t b))

-- S + part ≡ W·b²（prem 承载; distribʳ 对称 + prem 乘入; 泛化 W 免未用变量）
S-partW : ∀ t c b W → ((t *ℤ t) +ℤ (+ c)) ≡ W
        → (ttbb t b +ℤ ((+ c) *ℤ (b *ℤ b))) ≡ (W *ℤ (b *ℤ b))
S-partW t c b W prem =
  trans (sym (*-distribʳ-+ (b *ℤ b) (t *ℤ t) (+ c)))
        (cong (λ w → w *ℤ (b *ℤ b)) prem)

-- 平方展开: (x+y)² ≡ x² + (xy + xy) + y²
sq2 : ∀ x y → (x +ℤ y) *ℤ (x +ℤ y) ≡ (x *ℤ x) +ℤ ((x *ℤ y +ℤ x *ℤ y) +ℤ (y *ℤ y))
sq2 x y =
  trans (*-distribˡ-+ (x +ℤ y) x y)
  (trans (cong₂ _+ℤ_ (*-distribʳ-+ x x y) (*-distribʳ-+ y x y))
  (trans (+-assoc (x *ℤ x) (y *ℤ x) (x *ℤ y +ℤ y *ℤ y))
  (trans (cong (λ w → x *ℤ x +ℤ (w +ℤ (x *ℤ y +ℤ y *ℤ y))) (*-comm y x))
         (cong (λ w → x *ℤ x +ℤ w) (sym (+-assoc (x *ℤ y) (x *ℤ y) (y *ℤ y)))))))

-- sq2 展开的段名化: (2a+tb)² ≡ P1form + (M4form + ttbb)
sq2-comb : ∀ t a b
  → ((a +ℤ a +ℤ t *ℤ b) *ℤ (a +ℤ a +ℤ t *ℤ b))
  ≡ ((P1form a t) +ℤ ((M4form t a b) +ℤ (ttbb t b)))
sq2-comb t a b =
  trans (sq2 (a +ℤ a) (t *ℤ b))
  (trans (cong (λ w → w +ℤ (((a +ℤ a) *ℤ (t *ℤ b) +ℤ (a +ℤ a) *ℤ (t *ℤ b)) +ℤ ((t *ℤ b) *ℤ (t *ℤ b))))
               (sq2 a a))
         (cong (λ w → (P1form a t) +ℤ w) (merge t a b)))

--------------------------------------------------------------------------------
-- §2. ★ 配方恒等式（W3 正性来源定位; 泛化 W 形态）
--------------------------------------------------------------------------------

-- 步骤 1: RHS 的平方项配方（全签名顶层; Mini13 形态——签名钉死两侧）
step1 : ∀ t q c a b → ((t *ℤ t) +ℤ (+ c)) ≡ ((+ 4) *ℤ (+ q))
      → RHS t c a b
        ≡ (((P1form a t) +ℤ ((M4form t a b) +ℤ (ttbb t b))) +ℤ ((+ c) *ℤ (b *ℤ b)))
step1 t q c a b prem =
  cong (λ w → w +ℤ ((+ c) *ℤ (b *ℤ b))) (sq2-comb t a b)

-- 步骤 2: 第一层结合律
step2 : ∀ t q c a b → ((t *ℤ t) +ℤ (+ c)) ≡ ((+ 4) *ℤ (+ q))
      → (((P1form a t) +ℤ ((M4form t a b) +ℤ (ttbb t b))) +ℤ ((+ c) *ℤ (b *ℤ b)))
        ≡ ((P1form a t) +ℤ (((M4form t a b) +ℤ (ttbb t b)) +ℤ ((+ c) *ℤ (b *ℤ b))))
step2 t q c a b prem =
  +-assoc (P1form a t) ((M4form t a b) +ℤ (ttbb t b)) ((+ c) *ℤ (b *ℤ b))

-- 步骤 3: 第二层结合律
step3 : ∀ t q c a b → ((t *ℤ t) +ℤ (+ c)) ≡ ((+ 4) *ℤ (+ q))
      → ((P1form a t) +ℤ (((M4form t a b) +ℤ (ttbb t b)) +ℤ ((+ c) *ℤ (b *ℤ b))))
        ≡ ((P1form a t) +ℤ ((M4form t a b) +ℤ ((ttbb t b) +ℤ ((+ c) *ℤ (b *ℤ b)))))
step3 t q c a b prem =
  cong (λ w → (P1form a t) +ℤ w) (+-assoc (M4form t a b) (ttbb t b) ((+ c) *ℤ (b *ℤ b)))

-- 步骤 4: prem 乘入（S-partW）
step4 : ∀ t q c a b → ((t *ℤ t) +ℤ (+ c)) ≡ ((+ 4) *ℤ (+ q))
      → ((P1form a t) +ℤ ((M4form t a b) +ℤ ((ttbb t b) +ℤ ((+ c) *ℤ (b *ℤ b)))))
        ≡ ((P1form a t) +ℤ ((M4form t a b) +ℤ (((+ 4) *ℤ (+ q)) *ℤ (b *ℤ b))))
step4 t q c a b prem =
  cong (λ w → (P1form a t) +ℤ ((M4form t a b) +ℤ w))
       (S-partW t c b ((+ 4) *ℤ (+ q)) prem)

-- ★ W3 骨架（纯组合; 四步全签名）
W3-skeleton : ∀ t q c a b → ((t *ℤ t) +ℤ (+ c)) ≡ ((+ 4) *ℤ (+ q))
            → RHS t c a b
              ≡ ((P1form a t) +ℤ ((M4form t a b) +ℤ (((+ 4) *ℤ (+ q)) *ℤ (b *ℤ b))))
W3-skeleton t q c a b prem =
  trans (step1 t q c a b prem)
  (trans (step2 t q c a b prem)
  (trans (step3 t q c a b prem)
         (step4 t q c a b prem)))

--------------------------------------------------------------------------------
-- §3. 实例: E/F₃ 八类 (t ∈ {−3..3}, q = 3) 的 c 证书（premise 全 refl）
--------------------------------------------------------------------------------

prem-t0  : ((+ 0) *ℤ (+ 0)) +ℤ (+ 12) ≡ (+ 4) *ℤ (+ 3)
prem-t0  = refl
prem-t1  : ((+ 1) *ℤ (+ 1)) +ℤ (+ 11) ≡ (+ 4) *ℤ (+ 3)
prem-t1  = refl
prem-t2  : ((+ 2) *ℤ (+ 2)) +ℤ (+ 8) ≡ (+ 4) *ℤ (+ 3)
prem-t2  = refl
prem-t3  : ((+ 3) *ℤ (+ 3)) +ℤ (+ 3) ≡ (+ 4) *ℤ (+ 3)
prem-t3  = refl
prem-t-1 : ((-[1+ 0 ]) *ℤ (-[1+ 0 ])) +ℤ (+ 11) ≡ (+ 4) *ℤ (+ 3)
prem-t-1 = refl
prem-t-2 : ((-[1+ 1 ]) *ℤ (-[1+ 1 ])) +ℤ (+ 8) ≡ (+ 4) *ℤ (+ 3)
prem-t-2 = refl
prem-t-3 : ((-[1+ 2 ]) *ℤ (-[1+ 2 ])) +ℤ (+ 3) ≡ (+ 4) *ℤ (+ 3)
prem-t-3 = refl

-- 八类实例（W := 4·3; c = 12/11/8/3 全为正 → 模锁定的序上算术骨架;
-- a/b 取示范点 (2,1)——W3-skeleton 对 ∀ a b 全称, 实例点任选）
a-ax b-ax : ℤ
a-ax = (+ 2)
b-ax = (+ 1)

W3-t0  = W3-skeleton (+ 0) 3 12 a-ax b-ax prem-t0
W3-t1  = W3-skeleton (+ 1) 3 11 a-ax b-ax prem-t1
W3-t2  = W3-skeleton (+ 2) 3 8 a-ax b-ax prem-t2
W3-t3  = W3-skeleton (+ 3) 3 3 a-ax b-ax prem-t3
W3-t-1 = W3-skeleton -[1+ 0 ] 3 11 a-ax b-ax prem-t-1
W3-t-2 = W3-skeleton -[1+ 1 ] 3 8 a-ax b-ax prem-t-2
W3-t-3 = W3-skeleton -[1+ 2 ] 3 3 a-ax b-ax prem-t-3
