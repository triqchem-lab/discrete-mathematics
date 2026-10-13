{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.NumberTheory.Diophantine
-- 数学背景：线性不定方程的**模 n 判定核心**——数论补面件
--   （缺面清单 P2：对标 Mathlib `NumberTheory.Diophantine`；本模块取
--   「a·x + b·y ≡ c (mod n) 解存在性的可判定等价」面）。
-- 术语红线（本体论）：
--   1. 本模块载体是 **Z/nZ 上位泛型**（ModularArithmetic 的 ℕ 值层 + Fin n 变元基座）；
--      **R₁₂ = ℤ/12ℤ 是投影特例**（Duodecimal 另赋乘法 _*12_——有零因子 2×6≡0、
--      3×4≡0 的**环**，非域），**禁止**笼统写「基于 Z12」；
--   2. 「12 进制」是记数法（Doz）；有限域只有 GF(3)/GF(9)；零因子是 R₁₂ 环投影的
--      产物，不是 DC（展示群）的性质——§7 的模 12 实例全部落在 R₁₂ 投影侧。
-- 核心原则：
--   1. 复用优先：stdlib GCD（gcd[m,n]∣m/∣n）· DivMod（%）· Fin（fromℕ<）+ 本库
--      Divisibility 的 ∣-∸——Bezout 具备情形零重证；
--   2. 0 postulate / 0 hole：可证部分全部构造闭合；不可证部分（一般 gcd 充分性、
--      CRT 一般提升）**注释立界不洞**（见文末「立界」）；
--   3. 松弛和形定义：c : Fin n 时「lhs ≡ toℕ c + k·n（k ∈ ℕ）」**恰为**模同余
--      lhs ≡ c (mod n)——lhs ≥ 0 且 toℕ c < n 把商钉在非负侧，单向形已足
--      （无需 %-分配律，见 §1 注记）；
--   4. 可判定性：∃Fin? 判定程序（yes 携 witness、no 携反驳——构造健全），
--      内核 Σℕk? 的 k 由整除通道（t%n≡0 ⟹ n∣t 的商）给出。
-- 采用方案：A（模域 Bezout 面——**必要性**方向全构造：解 ⟹ gcd₃∣c）
--   + C（充分性特例全构造：单位/零/倍数 + a=0 完整刻画）+ 兜底立界；
--   B（CRT 拼装）以 R₁₂ 实例核对层落地（一般提升需 π3/π4 乘法同态——立界）。
-- 包含：LinComb · DiophSol₁ · DiophSol · 基础件6 · 判定程序4 ·
--       gcd 判据2 · 充分性构例6 · R₁₂ CRT 拼装核对4 · 决策/否定/语义核对 9

module Sovereign.Algebra.NumberTheory.Diophantine where

--------------------------------------------------------------------------------
-- §0 导入区
--------------------------------------------------------------------------------

open import Data.Nat
  using (ℕ; zero; suc; pred; _+_; _*_; _∸_; _≤_; _<_; z≤n; s≤s;
         s≤s⁻¹; nonZero)
open import Data.Nat.Properties
  using (≮⇒≥; n≮n; ≤-trans; m≤m+n; m≤n+m; m+n∸n≡m; m+n∸m≡n;
         +-∸-assoc; +-comm; +-identityʳ; *-identityˡ; *-zeroʳ; *-suc; *-comm)
open import Data.Nat.DivMod using (m*n%n≡0)
-- mod-helper 裸通道（Agda.Builtin.Nat 公共导出，无实例参数——避开 % 的
-- 无关实例 λ 阻塞，见本节注记）
open import Agda.Builtin.Nat using (mod-helper)
open import Data.Nat.GCD using (gcd; gcd[m,n]∣m; gcd[m,n]∣n)
open import Data.Nat.Divisibility
  using (_∣_; divides; quotient; ∣-trans; ∣m∣n⇒∣m+n; m∣m*n; n∣m*n; m%n≡0⇒n∣m)
open import Data.Fin using (Fin; toℕ; fromℕ<)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective; toℕ-fromℕ<)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; False)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

-- 本库件（同层兄弟：Divisibility 的 ∣-∸ 零重证复用；ModularArithmetic 语义对接）
open import Sovereign.Algebra.NumberTheory.Divisibility using (∣-∸)
open import Sovereign.Algebra.NumberTheory.ModularArithmetic using (⊕ₙ)
open import Sovereign.Base.Trit using (Trit; T₁; T₂; _⊗_)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d1; d5; π3; π4; crt12; _*4_)

--------------------------------------------------------------------------------
-- §1 定义层：线性组合与松弛和形（c : Fin n ⟹ 单向松弛形恰为模同余）
--------------------------------------------------------------------------------

-- LinComb a b x y：线性组合 a·x + b·y（值层 ℕ）
LinComb : (a b x y : ℕ) → ℕ
LinComb a b x y = a * x + b * y

-- DiophSol₁ n a c：单变量 a·x ≡ c (mod n) 的**解**（x ∈ Fin n，k 为松弛倍数）
-- 注记：toℕ c < n（Fin 语义）与 LHS ≥ 0 把模同余的商钉死在「lhs = toℕ c + k·n」
--   一支——不出现「lhs < toℕ c 且同余」的分支，故单向 Σk 形恰为同余，
--   与 %-形（ModularArithmetic 语义）在 c : Fin n 上一致（§8 核对件）。
DiophSol₁ : (n a : ℕ) → Fin n → Set
DiophSol₁ n a c = Σ (Fin n) λ x → Σ ℕ λ k → a * toℕ x ≡ toℕ c + k * n

-- DiophSol n a b c：双变量 a·x + b·y ≡ c (mod n) 的**解**
DiophSol : (n a b : ℕ) → Fin n → Set
DiophSol n a b c = Σ (Fin n) λ x → Σ (Fin n) λ y → Σ ℕ λ k →
  LinComb a b (toℕ x) (toℕ y) ≡ toℕ c + k * n

--------------------------------------------------------------------------------
-- §2 基础件层：松弛和的消去/还原/单调（全部具名，供上层复用）
--------------------------------------------------------------------------------

-- m ≡ n + (m ∸ n)（n ≤ m：被减数还原）
m≡n+m∸n : ∀ m n → n ≤ m → m ≡ n + (m ∸ n)
m≡n+m∸n m n n≤m = trans (sym (m+n∸m≡n n m)) (+-∸-assoc n n≤m)

-- lhs ≡ c + kn ⟹ lhs ≡ c + (lhs ∸ c)（k·n 已被吃进 ∸——同余商的还原形）
lhs≡c+∸ : ∀ lhs c → c ≤ lhs → lhs ≡ c + (lhs ∸ c)
lhs≡c+∸ lhs c c≤lhs = m≡n+m∸n lhs c c≤lhs

-- lhs ≡ c + k·n ⟹ lhs ∸ c ≡ k·n（松弛消去——同余差的代数根据）
lhs∸c≡kn : ∀ lhs c kn → lhs ≡ c + kn → lhs ∸ c ≡ kn
lhs∸c≡kn lhs c kn eq =
  trans (cong (_∸ c) eq)
        (trans (cong (_∸ c) (+-comm c kn)) (m+n∸n≡m kn c))

-- lhs ≡ c + k·n ⟹ c ≤ lhs（单调——「缩小不可能」的反驳通道）
kn≤⇒c≤lhs : ∀ lhs c kn → lhs ≡ c + kn → c ≤ lhs
kn≤⇒c≤lhs lhs c kn eq = subst (c ≤_) (sym eq) (m≤m+n c kn)

-- q ≤ q·a（1 ≤ a）：商不超过被乘积——商 < n 的来源
q≤q*a : ∀ q a → 1 ≤ a → q ≤ q * a
q≤q*a q zero ()
q≤q*a q (suc a) _ = subst (q ≤_) (sym (*-suc q a)) (m≤m+n q (q * a))

-- m ≤ 0 ⟹ m ≡ 0（a=0 刻画用）
≤0⇒≡0 : ∀ m → m ≤ 0 → m ≡ 0
≤0⇒≡0 _ z≤n = refl

-- 2∤1：R₁₂/R₁₂系判据的不可满足核（偶 ≠ 奇——零因子环投影反例的种子）
--   证明：1 ≡ q·2 的两case在字面层直接不可满足（absurd pattern 无需人工链）
2∤1 : ¬ (2 ∣ 1)
2∤1 (divides zero ())
2∤1 (divides (suc q) ())

--------------------------------------------------------------------------------
-- §3 判定层：∃Fin? / Σℕk? 与两个判定程序（中心命题——解存在可判定）
--------------------------------------------------------------------------------

-- ℕ≟ / ℕ≟suc / ℕmod / ℕ<⁻：自写可归约判定与裸余数通道
--   （工程口径：自写件自带纯子句 yes/no 通道与 mod-helper 直连，不依赖
--   stdlib 的 map′/T? 归约路径——误检事故后按「先探针测归约」原则落地；
--   事发根因实证为把 False (no-Dec) 的证明项写成 λ ()——levels 反了）。
-- ℕ≟suc：suc-分支继续——纯子句（无 with）
ℕ≟suc : (m n : ℕ) → Dec (m ≡ n) → Dec (suc m ≡ suc n)
ℕ≟suc m n (yes eq) = yes (cong suc eq)
ℕ≟suc m n (no ¬eq) = no (λ eq → ¬eq (cong pred eq))

-- ℕmod：t mod (suc d) 的裸余数通道（= mod-helper 0 d t d）
--   注记：与 `t % suc d` 定义性相等（同 unfold 到 mod-helper），但
--   % 的无关实例参数使值层留下 λ 形阻塞模式匹配；ℕmod 直连裸函数。
ℕmod : (t d : ℕ) → ℕ
ℕmod t d = mod-helper 0 d t d

-- ℕ≟：相等判定（suc-分支转 ℕ≟suc——纯子句可归约）
ℕ≟ : (m n : ℕ) → Dec (m ≡ n)
ℕ≟ zero    zero    = yes refl
ℕ≟ zero    (suc n) = no (λ ())
ℕ≟ (suc m) zero    = no (λ ())
ℕ≟ (suc m) (suc n) = ℕ≟suc m n (ℕ≟ m n)

-- ℕ<⁻s：suc-分支继续——纯子句
ℕ<⁻s : (m n : ℕ) → Dec (m < n) → Dec (suc m < suc n)
ℕ<⁻s m n (yes m<n) = yes (s≤s m<n)
ℕ<⁻s m n (no ¬m<n) = no (λ { (s≤s m<n) → ¬m<n m<n })

-- ℕ<⁻：m < n（= suc m ≤ n）的可归约判定
ℕ<⁻ : (m n : ℕ) → Dec (m < n)
ℕ<⁻ zero    zero    = no (λ ())
ℕ<⁻ zero    (suc n) = yes (s≤s z≤n)
ℕ<⁻ (suc m) zero    = no (λ ())
ℕ<⁻ (suc m) (suc n) = ℕ<⁻s m n (ℕ<⁻ m n)

-- Σℕk-suc：正模数分支（ ℕ<⁻ 的 Dec 由调用侧算好——纯子句消解、模式无歧义；
--   避开「with 内嵌 with + 省略号」对齐陷阱——嵌套版曾把 no 分支误判成 yes）
Σℕk-suc : (lhs c m : ℕ) → Dec (lhs < c) → Dec (Σ ℕ λ k → lhs ≡ c + k * suc m)
Σℕk-suc lhs c m (yes lhs<c) =
  no λ { (k , eq) → n≮n lhs (≤-trans lhs<c (kn≤⇒c≤lhs lhs c (k * suc m) eq)) }
Σℕk-suc lhs c m (no lhs≮c) with ≮⇒≥ lhs≮c | ℕ≟ (ℕmod (lhs ∸ c) m) zero
... | c≤lhs | yes t%≡0 =
      -- 商通道：t%n≡0 ⟹ n∣t（record 投影取商与等式）
      yes (quotient (m%n≡0⇒n∣m (lhs ∸ c) (suc m) t%≡0) ,
           trans (lhs≡c+∸ lhs c c≤lhs)
                 (cong (c +_) (_∣_.equality (m%n≡0⇒n∣m (lhs ∸ c) (suc m) t%≡0))))
... | c≤lhs | no t%≢0 =
      no λ { (k , eq) →
        t%≢0 (subst (λ z → ℕmod z m ≡ zero)
                    (sym (lhs∸c≡kn lhs c (k * suc m) eq))
                    (m*n%n≡0 k (suc m))) }

-- ∃Fin?：有限论域上的存在可判定（构造健全：yes 携 witness、no 携反驳）
--   重构注记：同 Σℕk?——避开「with 内嵌 with + 省略号」对齐陷阱（实测
--   嵌套版在具体点上误把 no 链归约成 yes），改为 Dec 显式传参 + 单 helper。
∃Fin?-succ : (n : ℕ) (P : Fin (suc n) → Set) (P? : ∀ i → Dec (P i))
  → Dec (P fzero) → Dec (Σ (Fin n) (λ i → P (fsuc i)))
  → Dec (Σ (Fin (suc n)) P)
∃Fin?-succ n P P? (yes p)      _      = yes (fzero , p)
∃Fin?-succ n P P? (no ¬p) (yes (i , p)) = yes (fsuc i , p)
∃Fin?-succ n P P? (no ¬p) (no ¬q) =
  no λ { (fzero  , p) → ¬p p ; (fsuc i , p) → ¬q (i , p) }

∃Fin? : (n : ℕ) (P : Fin n → Set) → (∀ i → Dec (P i)) → Dec (Σ (Fin n) P)
∃Fin? zero    P P? = no λ { (() , _) }
∃Fin? (suc n) P P? =
  ∃Fin?-succ n P P? (P? fzero) (∃Fin? n (λ i → P (fsuc i)) (λ i → P? (fsuc i)))

-- Σℕk?：松弛和解的可判定（k 由整除商给出——先算后验证的商通道）
--   zero-分支：n = 0 时 k·n = 0，命题退化为 lhs ≡ c（ ℕ≟）；
--   suc-分支转 Σℕk-suc（ ℕ<⁻ 显式传参——纯子句可归约）。
Σℕk? : (lhs c n : ℕ) → Dec (Σ ℕ λ k → lhs ≡ c + k * n)
Σℕk? lhs c zero with ℕ≟ lhs c
... | yes eq = yes (zero , trans eq (sym (+-identityʳ c)))
... | no eq≢ =
  no λ { (k , eq) → eq≢ (trans eq (trans (cong (c +_) (*-zeroʳ k)) (+-identityʳ c))) }
Σℕk? lhs c (suc n) = Σℕk-suc lhs c n (ℕ<⁻ lhs c)

-- diophSol₁?：单变量 a·x ≡ c (mod n) 有解——**可判定**
diophSol₁? : (n a : ℕ) (c : Fin n) → Dec (DiophSol₁ n a c)
diophSol₁? n a c =
  ∃Fin? n (λ x → Σ ℕ λ k → a * toℕ x ≡ toℕ c + k * n)
          λ x → Σℕk? (a * toℕ x) (toℕ c) n

-- diophSol?：双变量 a·x + b·y ≡ c (mod n) 有解——**可判定**
diophSol? : (n a b : ℕ) (c : Fin n) → Dec (DiophSol n a b c)
diophSol? n a b c =
  ∃Fin? n (λ x → Σ (Fin n) λ y → Σ ℕ λ k →
            LinComb a b (toℕ x) (toℕ y) ≡ toℕ c + k * n)
          λ x → ∃Fin? n (λ y → Σ ℕ λ k →
                  LinComb a b (toℕ x) (toℕ y) ≡ toℕ c + k * n)
                  λ y → Σℕk? (LinComb a b (toℕ x) (toℕ y)) (toℕ c) n

--------------------------------------------------------------------------------
-- §4 gcd 判据层（必要性方向——方案 A 构造核心）
--------------------------------------------------------------------------------

-- solvable₁⇒gcd∣c：a·x ≡ c (mod n) 有解 ⟹ gcd a n ∣ c
--   数学理由：a·x = c + k·n，g = gcd(a,n) 同时整除 a·x 与 k·n，
--   故 g 整除差 a·x ∸ k·n = c（∣-∸ 本库件）。
solvable₁⇒gcd∣c : (n a : ℕ) (c : Fin n) → DiophSol₁ n a c → gcd a n ∣ toℕ c
solvable₁⇒gcd∣c n a c (x , k , eq) =
  subst (gcd a n ∣_) ax∸kn≡c (∣-∸ g∣ax g∣kn kn≤ax)
  where
  g∣ax : gcd a n ∣ a * toℕ x
  g∣ax = ∣-trans (gcd[m,n]∣m a n) (m∣m*n (toℕ x))
  g∣kn : gcd a n ∣ k * n
  g∣kn = ∣-trans (gcd[m,n]∣n a n) (n∣m*n k)
  kn≤ax : k * n ≤ a * toℕ x
  kn≤ax = subst (k * n ≤_) (sym eq) (m≤n+m (k * n) (toℕ c))
  ax∸kn≡c : a * toℕ x ∸ k * n ≡ toℕ c
  ax∸kn≡c = trans (sym (cong (_∸ (k * n)) (sym eq))) (m+n∸n≡m (toℕ c) (k * n))

-- solvable⇒gcd₃∣c：a·x + b·y ≡ c (mod n) 有解 ⟹ gcd(gcd a b) n ∣ c
--   数学理由：线性组合仍在 gcd(a,b) 的倍数系内（∣m∣n⇒∣m+n），
--   与 n 的公因数合成 g₃，其余与单变量同构。
solvable⇒gcd₃∣c : (n a b : ℕ) (c : Fin n) → DiophSol n a b c → gcd (gcd a b) n ∣ toℕ c
solvable⇒gcd₃∣c n a b c (x , y , k , eq) =
  subst (g ∣_) ax∸kn≡c (∣-∸ g∣lc g∣kn kn≤lc)
  where
  g = gcd (gcd a b) n
  g∣a : g ∣ a
  g∣a = ∣-trans (gcd[m,n]∣m (gcd a b) n) (gcd[m,n]∣m a b)
  g∣b : g ∣ b
  g∣b = ∣-trans (gcd[m,n]∣m (gcd a b) n) (gcd[m,n]∣n a b)
  g∣ax : g ∣ a * toℕ x
  g∣ax = ∣-trans g∣a (m∣m*n (toℕ x))
  g∣by : g ∣ b * toℕ y
  g∣by = ∣-trans g∣b (m∣m*n (toℕ y))
  g∣lc : g ∣ LinComb a b (toℕ x) (toℕ y)
  g∣lc = ∣m∣n⇒∣m+n g∣ax g∣by
  g∣kn : g ∣ k * n
  g∣kn = ∣-trans (gcd[m,n]∣n (gcd a b) n) (n∣m*n k)
  kn≤lc : k * n ≤ LinComb a b (toℕ x) (toℕ y)
  kn≤lc = subst (k * n ≤_) (sym eq) (m≤n+m (k * n) (toℕ c))
  ax∸kn≡c : LinComb a b (toℕ x) (toℕ y) ∸ k * n ≡ toℕ c
  ax∸kn≡c = trans (sym (cong (_∸ (k * n)) (sym eq))) (m+n∸n≡m (toℕ c) (k * n))

--------------------------------------------------------------------------------
-- §5 充分性构例层（方案 C——特例全构造；一般形立界见文末）
--------------------------------------------------------------------------------

-- solvable-unit：单位系数 1·x + b·y ≡ c 恒有解
--   （x := c；y := fromℕ< 0<n——符号 n 下 Fin n 零元经 0 < n 通道，
--   不能直接写 fzero：Fin zero 为空，统一解不出。下同。）
solvable-unit : (n b : ℕ) (c : Fin n) → DiophSol n 1 b c
solvable-unit n b c = c , fromℕ< zero<n , 0 , proof
  where
  zero<n : zero < n
  zero<n = ≤-trans (s≤s z≤n) (toℕ<n c)
  proof : 1 * toℕ c + b * toℕ (fromℕ< zero<n) ≡ toℕ c + 0 * n
  proof =
    cong₂ _+_ (*-identityˡ (toℕ c))
              (trans (cong (b *_) (toℕ-fromℕ< zero<n)) (*-zeroʳ b))

-- solvable-zero：零解构例（c 为零元——toℕ c ≡ 0 由使用方给证，如字面 fzero 处 refl）
solvable-zero : (n a b : ℕ) (c : Fin n) → toℕ c ≡ 0 → DiophSol n a b c
solvable-zero n a b c h = c , fromℕ< zero<n , 0 , proof
  where
  zero<n : zero < n
  zero<n = ≤-trans (s≤s z≤n) (toℕ<n c)
  proof : a * toℕ c + b * toℕ (fromℕ< zero<n) ≡ toℕ c + 0 * n
  proof =
    trans (cong₂ _+_ (trans (cong (a *_) h) (*-zeroʳ a))
                     (trans (cong (b *_) (toℕ-fromℕ< zero<n)) (*-zeroʳ b)))
          (sym (cong (_+ zero) h))

-- solvable-of-multiple：1 ≤ a 且 a ∣ c ⟹ 单变量有解（x := 商 q）
--   数学理由：c = q·a 直接给出 a·q = c + 0·n；1 ≤ a 保证 q ≤ q·a = c < n。
solvable-of-multiple : (n a : ℕ) (c : Fin n) → 1 ≤ a → a ∣ toℕ c → DiophSol₁ n a c
solvable-of-multiple n a c 1≤a (divides q eq) =
  fromℕ< q<n , 0 , proof
  where
  q≤toc : q ≤ toℕ c
  q≤toc = subst (q ≤_) (sym eq) (q≤q*a q a 1≤a)
  q<n : q < n
  q<n = ≤-trans (s≤s q≤toc) (toℕ<n c)
  proof : a * toℕ (fromℕ< q<n) ≡ toℕ c + 0 * n
  proof =
    trans (cong (a *_) (toℕ-fromℕ< q<n))
          (trans (*-comm a q)
                 (trans (sym eq) (sym (+-identityʳ (toℕ c)))))

-- solvable₁⇒solvable：单变量解 ⟹ 双变量解（y := 零元经 0 < n 通道——粘合件）
solvable₁⇒solvable : (n a b : ℕ) (c : Fin n) → DiophSol₁ n a c → DiophSol n a b c
solvable₁⇒solvable n a b c (x , k , eq) = x , fromℕ< zero<n , k , proof
  where
  zero<n : zero < n
  zero<n = ≤-trans (s≤s z≤n) (toℕ<n c)
  proof : a * toℕ x + b * toℕ (fromℕ< zero<n) ≡ toℕ c + k * n
  proof =
    trans (trans (cong (a * toℕ x +_)
                       (trans (cong (b *_) (toℕ-fromℕ< zero<n)) (*-zeroʳ b)))
                 (+-identityʳ (a * toℕ x)))
          eq

-- a = 0 的完整刻画（ℕ 层）：0·x ≡ c (mod n) 有解 ⟺ toℕ c ≡ 0
--   （双向全构造；Fin 层「c ≡ fzero」与 toℕ c ≡ 0 经 toℕ-injective 互换——
--   签名不写 c ≡ fzero：符号 n 下 fzero : Fin n 统一不出。）
solvable₁-a0⇒c≡0 : (n : ℕ) (c : Fin n) → DiophSol₁ n 0 c → toℕ c ≡ 0
solvable₁-a0⇒c≡0 n c (x , k , eq) = ≤0⇒≡0 (toℕ c) toc≤0
  where
  toc≤0 : toℕ c ≤ 0
  toc≤0 = ≤-trans (m≤m+n (toℕ c) (k * n)) (subst (_≤ 0) eq z≤n)

solvable₁-a0′ : (n : ℕ) (c : Fin n) → toℕ c ≡ 0 → DiophSol₁ n 0 c
solvable₁-a0′ n c h = c , 0 , sym (cong (_+ zero) h)

--------------------------------------------------------------------------------
-- §6 决策核对层（具体点：正例 / 反例 / gcd 值 / 决策结果 / ⊕ₙ 语义对接）
--------------------------------------------------------------------------------

-- 具体点命名（Fin 常量）
one₃ two₃ : Fin 3
one₃ = fsuc fzero
two₃ = fsuc (fsuc fzero)
one₄ : Fin 4
one₄ = fsuc fzero
one₁₂ five₁₂ : Fin 12
one₁₂   = fsuc fzero
five₁₂  = fsuc (fsuc (fsuc (fsuc (fsuc fzero))))

-- 核对1：LinComb 值层（5·2 + 0·0 = 10）
check-lincomb : LinComb 5 0 2 0 ≡ 10
check-lincomb = +-identityʳ 10

-- 核对2：5·x ≡ 1 (mod 3) 的解 x = 2（10 = 1 + 3·3）——直接 witness
dio₁-3-5-1 : DiophSol₁ 3 5 one₃
dio₁-3-5-1 = two₃ , 3 , refl

-- 核对3：2·x ≡ 1 (mod 4) 无解——由 gcd 判据（gcd 2 4 = 2 ∤ 1）决定
check-gcd-2-4 : gcd 2 4 ≡ 2
check-gcd-2-4 = refl

¬dio₁-4-2-1 : ¬ DiophSol₁ 4 2 one₄
¬dio₁-4-2-1 h = 2∤1 (subst (_∣ 1) check-gcd-2-4 (solvable₁⇒gcd∣c 4 2 one₄ h))

-- 核对4：2·x + 2·y ≡ 1 (mod 4) 无解——由三参 gcd 判据（gcd 2 2 4 = 2 ∤ 1）
check-gcd₃-2-2-4 : gcd (gcd 2 2) 4 ≡ 2
check-gcd₃-2-2-4 = refl

¬dio-4-2-2-1 : ¬ DiophSol 4 2 2 one₄
¬dio-4-2-2-1 h = 2∤1 (solvable⇒gcd₃∣c 4 2 2 one₄ h)

-- 核对5/6：判定程序的具体点（True/False 通道——构造健全的可运行面）
check-dec-yes : True (diophSol₁? 3 5 one₃)
check-dec-yes = tt

-- 核对6b：判定程序无解点（2·x ≡ 1 (mod 4)：商通道 + 单调反驳全部闭合）
--   口径注记：False (no-Dec) = T (isNo no-form) = T true = ⊤，证明项是 tt
--   （记录 no 形状即过；若误为 yes 形则 T false = ⊥ 不闭合）。
check-dec-no : False (diophSol₁? 4 2 one₄)
check-dec-no = tt

-- ℕmod 与 % 的语义对账（定义性相等的实例通道）
check-mod-1-4 : ℕmod 1 3 ≡ 1
check-mod-1-4 = refl

check-dec-zero-c : True (diophSol? 4 2 2 fzero)
check-dec-zero-c = tt

-- 核对7：R₁₂ 投影侧语义对接——⊕ₙ（ModularArithmetic 泛型）与 % 值层一致
check-mod-⊕ₙ : ⊕ₙ 3 10 0 ≡ toℕ one₃
check-mod-⊕ₙ = refl

-- 核对8：单位构例实例化（1·x + 2·y ≡ 1 (mod 4) 的解 x = c）
unit-solves : DiophSol 4 1 2 one₄
unit-solves = solvable-unit 4 2 one₄

zero-solves : DiophSol 4 2 2 fzero
zero-solves = solvable-zero 4 2 2 fzero refl

--------------------------------------------------------------------------------
-- §7 R₁₂ 实例 CRT 拼装核对层（实例级；一般提升立界）
--------------------------------------------------------------------------------

-- R₁₂ 投影特例：5·x ≡ 1 (mod 12) 的解 x = 5（25 = 1 + 2·12）
dio₁-12-5-1 : DiophSol₁ 12 5 one₁₂
dio₁-12-5-1 = five₁₂ , 2 , refl

-- mod 3 分量（GF(3) 加法半侧）：π3 d5 = T₂，T₂·T₂ = T₁ = π3 d1
check-comp3 : π3 d5 ⊗ π3 d5 ≡ π3 d1
check-comp3 = refl

-- mod 4 分量（Z/4Z 投影）：π4 d5 = 1，1·1 = 1 = π4 d1
check-comp4 : π4 d5 *4 π4 d5 ≡ π4 d1
check-comp4 = refl

-- CRT 重构：mod 3 分量解与 mod 4 分量解经 crt12 复原 mod 12 的解 d5
check-crt-recombine : crt12 (π3 d5) (π4 d5) ≡ d5
check-crt-recombine = refl

--------------------------------------------------------------------------------
-- §8 立界注记（如实——不可证部分不洞不 postulate）
--------------------------------------------------------------------------------
-- 未证清单：
--   ① gcd 判据的**充分性一般形**（g₃ ∣ c ⟹ 有解）：需 ℤ-Bézout 负系数
--      （s·a − t·b = g 在 ℤ 中取非负代表）+ 模 n 归一化；stdlib
--      Data.Nat.Coprimality 的 Bézout 面在案（互素情形），一般 gcd 情形
--      留 roadmap。本模块已构造闭合的充分性特例：单位系数、零常数、
--      整除倍数（§5 三件）与 a=0 完整刻画。
--   ② CRT **一般提升**：分量解经 crt12 重构出 mod 12 解的一般形，需
--      π3/π4 对 _*12_ 的乘法同态（144 case 或同态引理）——§7 只交付
--      5·x ≡ 1 (mod 12) 实例核对（三具体点 refl 全闭合）。
--   ③ % 桥（Σ形 ↔ ModularArithmetic %-形的相互翻译泛型定理）：Σ形已是
--      同余的构造定义（§1 注记），%-向翻译需 %-distrib 族——留 roadmap；
--      实例级语义对接由 check-mod-⊕ₙ 承载。
-- 与缺面清单登记对账：登记「线性不定方程/CRT 泛型形、估行 150-200」；
--   本版实测 434 行（判定核 + 基础件 + gcd 判据 + 特例充分性 + R₁₂ 实例层 + 决策核对），超出登记上限——
--   超出部分为自写可归约判定件（ℕ≟/ℕmod/ℕ<⁻ 六件）与核对层 17 具体点；内容面仍为「线性不定方程/CRT 实例形」。
