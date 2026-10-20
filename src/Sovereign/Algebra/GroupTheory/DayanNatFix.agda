{-# OPTIONS --rewriting --guardedness #-}

-- | DayanNatFix —— 大衍求一术的 ℕ-内修正形：三义务闭合 + 原版反例
--
-- ## 数学背景（秦九韶《数书九章》卷一「大衍求一术」）
--
-- 术文：「置奇右上，定居右下。立天元一于左上。先以右上除右下，
--        所得商数，与左上一相生入左下。然后乃以右行上下，以少除多，
--        递互除之。所得商数，随即递互累乘，归左行上下。
--        须使右上末后奇一而止。乃验左上所得，以为乘率。」
--
-- 四格布局：左上(天元/乘率) 右上(奇) ／ 左下(累乘) 右下(定)。
-- 目标：求 `乘率` 使 `乘率 × 奇 ≡ 1 (mod 定)`（奇与定互素时）。
--
-- ## 上游之失（本模块要修正的）
--
-- 上游 `Sovereign.Algebra.GroupTheory.DayanState.dayan-step` 的递推为
--     diff = (q * lt) ∸ lb        -- 「累乘取差」，ℕ 饱和减法
--     乘率 = 定 ∸ lt              -- 步数 > 0 时
-- 它把 Bezout 系数当非负整数追踪，却用 `∸` 代替**模加**：符号一旦越过
-- 零点就被截断，剩余类信息丢失。反例 (奇=3, 定=5)：两步后 lt = 0，
-- 乘率 = 5 ∸ 0 = 5，而 3·5 = 15 ≡ 0 (mod 5) ≠ 1（§7 给内核级证明）。
--
-- ## 修正形（本模块的数学内容）
--
-- 核心原则：**系数不是 ℕ 元，而是 ℤ/定ℤ 剩余类的代表元**——因此减法
-- 必须换成模加，且每个系数始终保持落在 [0, 定)。
--
--   q   = rb / rt                （递互除：以少除多）
--   r   = rb % rt                （新右上）
--   A   = (q * lt) % 定          （累乘后的剩余类）
--   lt' = (lb + 定 ∸ A) % 定     （模加 = lb - A mod 定，落在 [0,定)）
--   lb' = lt ,  rt' = r ,  rb' = rt
--   乘率 = lt                    （无后处理：lt 本身即在 [0,定) 的逆元）
--
-- ## 三义务（对应上游 `DayanCorrect.agda` 的三个义务类型）
--
-- 不变量：`Inv 奇 定 s` := `lt·奇 ≡ rt (mod 定)` × `lb·奇 ≡ rb (mod 定)`
--
--   ① `init-invariant`    ：初始态 `(1,0,奇,定)` 满足不变量。
--   ② `step-invariant`    ：单步保持不变量（前提 rt ≠ 0，即状态形如 suc）。
--   ③ `terminate-correct` ：rt ≡ 1 时不变量退化为 `lt·奇 ≡ 1 (mod 定)`。
--
-- ## 关键设计：同余用「存在见证」形式而非 `%` 等式
--
--   `Cong n a b := ∃ p q, a + p·n ≡ b + q·n`（读作 a ≡ b (mod n)）
--
-- 理由：这样「两边同加 c 后消去 c」只需 ℕ 的 `+-cancelʳ-≡` 一步；
-- 若以 `a % n ≡ b % n` 为定义，消去律需要 `%` 的额外边界条件，
-- 反而把证明拖进 case 分析。两种形式的桥接在 §1 末给出
-- （`Cong-mod` 与 `Cong-to-mod`），故并未损失 `%` 形式的结论。
--
-- ## 本体论定位
--
-- 本模块只做**投影层**的算术修正：对象是 `ℤ/定ℤ` 的单位群（剩余类代表元
-- 系统），**不是**展示群 DC / DuodecClock；既不引入 ℤ，也不引入浮点或
-- 超越函数。`定` 是环的模数，与「12 进制」记数法（Doz）无关。
--
-- ## 诚实边界
--
-- · 本模块证明**单步不变量 + 终止正确性**；`right-top` 的严格递减（即整术
--   终止性，上游 roadmap 的 S-D3）**不在本模块范围内，未证**。
-- · 修正形 100% 覆盖率（2 ≤ 定 ≤ 200 共 12231 组互素对）是**外部计算事实**
--   （Python oracle），**不是 Agda 定理**；Agda 只裁决 §5 的三义务、
--   §6 的具体实例与 §7 的反例。
-- · 0 postulate / 0 hole。

module Sovereign.Algebra.GroupTheory.DayanNatFix where

open import Data.Nat
  using (ℕ; zero; suc; _*_; _+_; _∸_; _/_; _%_; _<_; _≤_; z≤n; s≤s; NonZero)
open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityʳ; +-identityˡ; +-cancelˡ-≡
  ; *-assoc; *-comm; *-identityˡ; *-zeroˡ; *-distribʳ-+
  ; m∸n+n≡m; m≤n+m; ≤-trans; <⇒≤ )
open import Data.Nat.DivMod using
  ( m≡m%n+[m/n]*n; m%n<n; m<n⇒m%n≡m; [m+kn]%n≡m%n )
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)

-- 右分配律（统一参数序）。(x + y) · n ≡ x·n + y·n
-- 注：stdlib 的 `*-distrib-+ʳ` 参数序为 `(m n o) ↦ (n + o) * m`，易误用，
-- 故此处固定语义顺序。
*-distrib-+ʳ : ∀ x y n → (x + y) * n ≡ x * n + y * n
*-distrib-+ʳ x y n = *-distribʳ-+ n x y

--------------------------------------------------------------------------------
-- §1. 模同余的「存在见证」形式
--
-- `Cong n a b` 读作 `a ≡ b (mod n)`：存在陪乘 p q，使 `a + p·n ≡ b + q·n`
-- （两边都允许加模数的倍数）。加减乘的相容性因此全部落在 ℕ 的普通代数里。
--------------------------------------------------------------------------------

Cong : ℕ → ℕ → ℕ → Set
Cong n a b = Σ ℕ (λ p → Σ ℕ (λ q → a + p * n ≡ b + q * n))

Cong-refl : ∀ {n a} → Cong n a a
Cong-refl = 0 , 0 , refl

-- 命题相等 ⟹ 同余（陪乘取 0）
Cong-intro : ∀ {n} {a b : ℕ} → a ≡ b → Cong n a b
Cong-intro {n} {a} {b} eq = 0 , 0 , (begin
  a + 0 * n ≡⟨ cong (a +_) (*-zeroˡ n) ⟩
  a + 0     ≡⟨ +-identityʳ a ⟩
  a         ≡⟨ eq ⟩
  b         ≡⟨ sym (+-identityʳ b) ⟩
  b + 0     ≡⟨ cong (b +_) (sym (*-zeroˡ n)) ⟩
  b + 0 * n ∎)

Cong-sym : ∀ {n a b} → Cong n a b → Cong n b a
Cong-sym (p , q , eq) = q , p , sym eq

-- 传递：陪乘取 (p + r) 与 (s + q)
-- 辅助：(b + X) + Y ≡ (b + Y) + X
+-swap-mid : ∀ b X Y → (b + X) + Y ≡ (b + Y) + X
+-swap-mid b X Y = begin
  (b + X) + Y ≡⟨ +-assoc b X Y ⟩
  b + (X + Y) ≡⟨ cong (b +_) (+-comm X Y) ⟩
  b + (Y + X) ≡⟨ sym (+-assoc b Y X) ⟩
  (b + Y) + X ∎

Cong-trans : ∀ {n a b c} → Cong n a b → Cong n b c → Cong n a c
Cong-trans {n} {a} {b} {c} (p , q , e1) (r , s , e2) = (p + r) , (s + q) , (begin
  a + (p + r) * n       ≡⟨ cong (a +_) (*-distrib-+ʳ p r n) ⟩
  a + (p * n + r * n)   ≡⟨ sym (+-assoc a (p * n) (r * n)) ⟩
  (a + p * n) + r * n   ≡⟨ cong (_+ r * n) e1 ⟩
  (b + q * n) + r * n   ≡⟨ +-swap-mid b (q * n) (r * n) ⟩
  (b + r * n) + q * n   ≡⟨ cong (_+ q * n) e2 ⟩
  (c + s * n) + q * n   ≡⟨ +-assoc c (s * n) (q * n) ⟩
  c + (s * n + q * n)   ≡⟨ cong (c +_) (sym (*-distrib-+ʳ s q n)) ⟩
  c + (s + q) * n       ∎)

-- 结合律的两个方向（显式命名，避免与 stdlib 的 `+-assoc` 方向混淆）
-- stdlib 约定：`+-assoc x y z : (x + y) + z ≡ x + (y + z)`（已实测确认）
+-assoc→ : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc→ = +-assoc

+-assoc← : ∀ x y z → x + (y + z) ≡ (x + y) + z
+-assoc← x y z = sym (+-assoc x y z)

-- 辅助置换：(a + c) + (X + Y) ≡ (a + X) + (c + Y)
+-shuffle : ∀ a c X Y → (a + c) + (X + Y) ≡ (a + X) + (c + Y)
+-shuffle a c X Y = begin
  (a + c) + (X + Y)   ≡⟨ +-assoc← (a + c) X Y ⟩
  ((a + c) + X) + Y   ≡⟨ cong (_+ Y) (cong (_+ X) (+-comm a c)) ⟩
  ((c + a) + X) + Y   ≡⟨ cong (_+ Y) (+-assoc→ c a X) ⟩
  (c + (a + X)) + Y   ≡⟨ cong (_+ Y) (+-comm c (a + X)) ⟩
  ((a + X) + c) + Y   ≡⟨ +-assoc→ (a + X) c Y ⟩
  (a + X) + (c + Y)   ∎

Cong-+-both : ∀ {n a b c d} → Cong n a b → Cong n c d → Cong n (a + c) (b + d)
Cong-+-both {n} {a} {b} {c = c} {d} (p , q , e1) (r , s , e2) = (p + r) , (q + s) , (begin
  a + c + (p + r) * n       ≡⟨ cong (a + c +_) (*-distrib-+ʳ p r n) ⟩
  a + c + (p * n + r * n)   ≡⟨ +-shuffle a c (p * n) (r * n) ⟩
  (a + p * n) + (c + r * n) ≡⟨ cong₂ _+_ e1 e2 ⟩
  (b + q * n) + (d + s * n) ≡⟨ sym (+-shuffle b d (q * n) (s * n)) ⟩
  b + d + (q * n + s * n)   ≡⟨ cong (b + d +_) (sym (*-distrib-+ʳ q s n)) ⟩
  b + d + (q + s) * n       ∎)

-- 辅助换位：(p * k) * n ≡ (p * n) * k
*-swap-n : ∀ p k n → (p * k) * n ≡ (p * n) * k
*-swap-n p k n = begin
  (p * k) * n ≡⟨ *-assoc p k n ⟩
  p * (k * n) ≡⟨ cong (p *_) (*-comm k n) ⟩
  p * (n * k) ≡⟨ sym (*-assoc p n k) ⟩
  (p * n) * k ∎

Cong-*-ʳ : ∀ {n a b} → Cong n a b → ∀ k → Cong n (a * k) (b * k)
Cong-*-ʳ {n} {a} {b} (p , q , eq) k = (p * k) , (q * k) , (begin
  a * k + (p * k) * n ≡⟨ cong (a * k +_) (*-swap-n p k n) ⟩
  a * k + (p * n) * k ≡⟨ sym (*-distrib-+ʳ a (p * n) k) ⟩
  (a + p * n) * k     ≡⟨ cong (_* k) eq ⟩
  (b + q * n) * k     ≡⟨ *-distrib-+ʳ b (q * n) k ⟩
  b * k + (q * n) * k ≡⟨ cong (b * k +_) (*-swap-n q n k) ⟩
  b * k + (q * k) * n ∎)

-- 左边乘常数（由交换律归约到 `Cong-*-ʳ`）
Cong-*-ˡ : ∀ {n a b} → Cong n a b → ∀ k → Cong n (k * a) (k * b)
Cong-*-ˡ {n} {a} {b} h k =
  Cong-trans (Cong-intro (sym (*-comm a k)))
    (Cong-trans (Cong-*-ʳ h k) (Cong-intro (*-comm b k)))

-- 右边加常数（陪乘不变）
Cong-+-ʳ : ∀ {n a b} → Cong n a b → ∀ c → Cong n (a + c) (b + c)
Cong-+-ʳ {n} {a} {b} (p , q , eq) c = p , q , (begin
  a + c + p * n   ≡⟨ +-assoc a c (p * n) ⟩
  a + (c + p * n) ≡⟨ cong (a +_) (+-comm c (p * n)) ⟩
  a + (p * n + c) ≡⟨ sym (+-assoc a (p * n) c) ⟩
  a + p * n + c   ≡⟨ cong (_+ c) eq ⟩
  b + q * n + c   ≡⟨ +-assoc b (q * n) c ⟩
  b + (q * n + c) ≡⟨ cong (b +_) (+-comm (q * n) c) ⟩
  b + (c + q * n) ≡⟨ sym (+-assoc b c (q * n)) ⟩
  b + c + q * n   ∎)

-- 右侧消去：x + z ≡ y + z ⟹ x ≡ y（以 +-cancelˡ-≡ 为基，方向自明）
+-cancel-right : ∀ x y z → x + z ≡ y + z → x ≡ y
+-cancel-right x y z h = +-cancelˡ-≡ z x y (begin
  z + x ≡⟨ +-comm z x ⟩
  x + z ≡⟨ h ⟩
  y + z ≡⟨ +-comm y z ⟩
  z + y ∎)

-- 消去右侧公共加项——「模加代替截断减法」的技术核心
Cong-cancel-+ʳ : ∀ {n a b c} → Cong n (a + c) (b + c) → Cong n a b
Cong-cancel-+ʳ {n} {a} {b} {c} (p , q , eq) = p , q ,
  +-cancel-right (a + p * n) (b + q * n) c (begin
    (a + p * n) + c ≡⟨ +-assoc a (p * n) c ⟩
    a + (p * n + c) ≡⟨ cong (a +_) (+-comm (p * n) c) ⟩
    a + (c + p * n) ≡⟨ sym (+-assoc a c (p * n)) ⟩
    a + c + p * n   ≡⟨ eq ⟩
    b + c + q * n   ≡⟨ +-assoc b c (q * n) ⟩
    b + (c + q * n) ≡⟨ cong (b +_) (+-comm c (q * n)) ⟩
    b + (q * n + c) ≡⟨ sym (+-assoc b (q * n) c) ⟩
    (b + q * n) + c ∎)

-- 模数的倍数可丢：X + n·Y ≡ X (mod n)
Cong-n-mult : ∀ n X Y → Cong n (X + n * Y) X
Cong-n-mult n X Y = 0 , Y , (begin
  X + n * Y + 0 * n ≡⟨ cong (X + n * Y +_) (*-zeroˡ n) ⟩
  X + n * Y + 0     ≡⟨ +-identityʳ (X + n * Y) ⟩
  X + n * Y         ≡⟨ cong (X +_) (*-comm n Y) ⟩
  X + Y * n         ∎)

-- 取模不改变同余类：a % n ≡ a (mod n)
Cong-mod : ∀ (a n : ℕ) → .{{_ : NonZero n}} → Cong n (a % n) a
Cong-mod a n = (a / n) , 0 , (begin
  a % n + (a / n) * n ≡⟨ sym (m≡m%n+[m/n]*n a n) ⟩
  a                   ≡⟨ sym (+-identityʳ a) ⟩
  a + 0               ≡⟨ cong (a +_) (sym (*-zeroˡ n)) ⟩
  a + 0 * n           ∎)

-- 桥接：存在见证形式 ⟹ `%` 形式
Cong-to-mod : ∀ {n a b} → .{{_ : NonZero n}} → Cong n a b → a % n ≡ b % n
Cong-to-mod {n} {a} {b} (p , q , eq) =
  trans (sym ([m+kn]%n≡m%n a p n))
        (trans (cong (_% n) eq) ([m+kn]%n≡m%n b q n))

--------------------------------------------------------------------------------
-- §2. 四格状态（修正形）
--
--   ┌──────────┬────────────┐
--   │ 左上 lt  │ 右上 rt(奇)│  lt = 乘率候选（恒 ∈ [0,定)）
--   ├──────────┼────────────┤  lb = 递互累乘的伴随系数
--   │ 左下 lb  │ 右下 rb(定)│  rt → 1 即「奇一而止」
--   └──────────┴────────────┘
--------------------------------------------------------------------------------

record DayanN : Set where
  constructor dn
  field
    lt lb rt rb : ℕ

open DayanN public

-- 「立天元一于左上，置奇右上，定居右下」
dayanN-init : (奇 定 : ℕ) → DayanN
dayanN-init 奇 定 = dn 1 0 奇 定

--------------------------------------------------------------------------------
-- §3. 修正形单步——「以少除多，递互除之，递互累乘」
--
-- 相对上游只有两处差别，且是同一件事的两面：
--   · `diff = (q*lt) ∸ lb`      →  `lt' = (lb + 定 ∸ ((q*lt) % 定)) % 定`
--   · `乘率 = 定 ∸ lt`（后处理）→  `乘率 = lt`（lt 已在 [0,定)）
--------------------------------------------------------------------------------

dayanN-step : (定 : ℕ) .{{_ : NonZero 定}} → DayanN → DayanN
dayanN-step 定 (dn lt lb rt rb) with rt
... | zero    = dn lt lb rt rb
... | suc rt' =
  dn ((lb + 定 ∸ (((rb / suc rt') * lt) % 定)) % 定)
     lt
     (rb % suc rt')
     (suc rt')

--------------------------------------------------------------------------------
-- §4. 不变量
--
--   `Inv 奇 定 s` : lt·奇 与 rt 同余，且 lb·奇 与 rb 同余（模 定）。
--
-- 两条为何**同时**成立：初始 lb = 0 而 rb = 定 ≡ 0 (mod 定)；单步把
-- (lt,lb) 与 (rt,rb) 整体对换（递互），两条同余在递互中互相支撑——
-- 这正是「递互累乘」的结构语义，也是上游只追踪一条而失败的原因。
--------------------------------------------------------------------------------

Inv : (奇 定 : ℕ) → DayanN → Set
Inv 奇 定 s = Cong 定 (lt s * 奇) (rt s) × Cong 定 (lb s * 奇) (rb s)

--------------------------------------------------------------------------------
-- §5. 三义务
--------------------------------------------------------------------------------

-- 义务 ①：初始态满足不变量
Cong-zero-定 : ∀ 定 → Cong 定 0 定
Cong-zero-定 定 = 1 , 0 , (begin
  0 + 1 * 定 ≡⟨ cong (0 +_) (*-identityˡ 定) ⟩
  0 + 定     ≡⟨ +-identityˡ 定 ⟩
  定         ≡⟨ sym (+-identityʳ 定) ⟩
  定 + 0     ≡⟨ cong (定 +_) (sym (*-zeroˡ 定)) ⟩
  定 + 0 * 定 ∎)

init-invariant : ∀ (奇 定 : ℕ) → Inv 奇 定 (dayanN-init 奇 定)
init-invariant 奇 定 = Cong-intro (*-identityˡ 奇) , Cong-zero-定 定

-- 义务 ②：单步保持不变量（状态形如 rt = suc rt'，即 rt ≠ 0）
--
-- 证明主线（全部在 ℕ 内，靠 Cong 的存在见证形式 + 消去律）：
--   记 q = rb / rt⁺，r = rb % rt⁺，A = (q·lt) % 定，B = lb + 定 ∸ A。
--   (i)   B + A ≡ lb + 定                  （A < 定 ≤ lb + 定，m∸n+n≡m）
--   (ii)  B·奇 + A·奇 ≡ lb·奇 + 定·奇        （(i) 两边乘 奇 后分配）
--   (iii) lb·奇 + 定·奇 ≡ lb·奇              （定·奇 是模数的倍数）
--   (iv)  lb·奇 ≡ rb ≡ r + q·rt⁺            （不变量假设 + 除法恒等式）
--   (v)   q·rt⁺ ≡ q·(lt·奇) = (q·lt)·奇 ≡ A·奇
--         （第一条同余 ×q；(·奇) 结合；A ≡ q·lt 再乘 奇）
--   (vi)  (ii)(iii)(iv)(v) ⟹ B·奇 + A·奇 ≡ r + A·奇
--   (vii) 消去右端 A·奇 ⟹ B·奇 ≡ r
--   (viii) (B % 定)·奇 ≡ B·奇               （取模不改变同余类）
step-invariant-core :
  ∀ (奇 定 : ℕ) .{{_ : NonZero 定}} (lt lb rt' rb : ℕ)
  → Inv 奇 定 (dn lt lb (suc rt') rb)
  → Inv 奇 定 (dayanN-step 定 (dn lt lb (suc rt') rb))
step-invariant-core 奇 定 lt lb rt' rb (h1 , h2) = main , h1
  where
  q : ℕ
  q = rb / suc rt'
  r : ℕ
  r = rb % suc rt'
  A : ℕ
  A = (q * lt) % 定
  B : ℕ
  B = lb + 定 ∸ A

  -- (i) A ≤ lb + 定
  A≤ : A ≤ lb + 定
  A≤ = ≤-trans (<⇒≤ (m%n<n (q * lt) 定)) (m≤n+m 定 lb)

  BA : B + A ≡ lb + 定
  BA = m∸n+n≡m {lb + 定} {A} A≤

  -- (ii) 展开 (B + A)·奇
  cBA : Cong 定 (B * 奇 + A * 奇) (lb * 奇 + 定 * 奇)
  cBA = Cong-intro (begin
    B * 奇 + A * 奇   ≡⟨ sym (*-distrib-+ʳ B A 奇) ⟩
    (B + A) * 奇      ≡⟨ cong (_* 奇) BA ⟩
    (lb + 定) * 奇    ≡⟨ *-distrib-+ʳ lb 定 奇 ⟩
    lb * 奇 + 定 * 奇 ∎)

  -- (iii) 定·奇 ≡ 0
  cd : Cong 定 (lb * 奇 + 定 * 奇) (lb * 奇)
  cd = Cong-n-mult 定 (lb * 奇) 奇

  -- (iv) 除法恒等式：rb ≡ r + q·rt⁺
  ce2 : Cong 定 rb (r + q * suc rt')
  ce2 = Cong-intro (m≡m%n+[m/n]*n rb (suc rt'))

  -- (v) 三段合成：r + q·rt⁺ ≡ r + q·(lt·奇) ≡ r + (q·lt)·奇 ≡ r + A·奇
  cf : Cong 定 (r + q * suc rt') (r + q * (lt * 奇))
  cf = Cong-+-both Cong-refl (Cong-*-ˡ (Cong-sym h1) q)

  cg : Cong 定 (r + q * (lt * 奇)) (r + (q * lt) * 奇)
  cg = Cong-+-both Cong-refl (Cong-intro (sym (*-assoc q lt 奇)))

  ch : Cong 定 (r + (q * lt) * 奇) (r + A * 奇)
  ch = Cong-+-both Cong-refl (Cong-sym (Cong-*-ʳ (Cong-mod (q * lt) 定) 奇))

  ci : Cong 定 (r + q * suc rt') (r + A * 奇)
  ci = Cong-trans cf (Cong-trans cg ch)

  -- (vi) lb·奇 ≡ rb ≡ r + q·rt⁺ ≡ r + A·奇
  ck : Cong 定 (lb * 奇) (r + A * 奇)
  ck = Cong-trans h2 (Cong-trans ce2 ci)

  cl : Cong 定 (B * 奇 + A * 奇) (r + A * 奇)
  cl = Cong-trans cBA (Cong-trans cd ck)

  -- (vii) 消去右端公共加项 A·奇
  cm : Cong 定 (B * 奇) r
  cm = Cong-cancel-+ʳ cl

  -- (viii) 取模不改变同余类
  ca : Cong 定 ((B % 定) * 奇) (B * 奇)
  ca = Cong-*-ʳ (Cong-mod B 定) 奇

  main : Cong 定 ((B % 定) * 奇) r
  main = Cong-trans ca cm

-- 对任意状态重述：`0 < rt s` 逼出状态形如 `rt s = suc _`
step-invariant :
  ∀ (奇 定 : ℕ) .{{_ : NonZero 定}} (s : DayanN)
  → 0 < rt s → Inv 奇 定 s → Inv 奇 定 (dayanN-step 定 s)
step-invariant 奇 定 (dn lt lb rt rb) (s≤s _) h =
  step-invariant-core 奇 定 lt lb _ rb h

-- 义务 ③：终止（右上 = 1）⟹ 乘率性质
--   写成 `≡ 1 % 定`，以免额外假设 定 ≥ 2（定 = 1 时一切 ≡ 0，恒真）。
terminate-correct :
  ∀ (奇 定 : ℕ) .{{_ : NonZero 定}} (s : DayanN)
  → Inv 奇 定 s → rt s ≡ 1 → (lt s * 奇) % 定 ≡ 1 % 定
terminate-correct 奇 定 s (h1 , h2) rt≡1 = trans (Cong-to-mod h1) (cong (_% 定) rt≡1)

-- 推论（定 ≥ 2 的定式）：左上所得即乘率，乘率·奇 ≡ 1 (mod 定)
dayan-correct :
  ∀ (奇 定 : ℕ) .{{_ : NonZero 定}} (s : DayanN)
  → 1 < 定 → Inv 奇 定 s → rt s ≡ 1 → (lt s * 奇) % 定 ≡ 1
dayan-correct 奇 定 s 1<定 h rt≡1 =
  trans (terminate-correct 奇 定 s h rt≡1) (m<n⇒m%n≡m 1<定)

--------------------------------------------------------------------------------
-- §6. 对抗验证：在具体点上独立 refl 计算，与 §5 定理实例交叉比对
--
-- 实例 (奇=3, 定=5)：修正形两步抵达 rt = 1
--   初始 (1,0,3,5)
--     → 步1 q=1 A=1 B=4 ⟹ (4,1,2,3)
--     → 步2 q=1 A=4 B=2 ⟹ (2,4,1,2)   ⟵ 奇一而止
--   乘率 = lt = 2，且 3·2 = 6 ≡ 1 (mod 5)。
--------------------------------------------------------------------------------

修正-1步 : DayanN
修正-1步 = dayanN-step 5 (dayanN-init 3 5)

修正-2步 : DayanN
修正-2步 = dayanN-step 5 修正-1步

修正-1步-值 : 修正-1步 ≡ dn 4 1 2 3
修正-1步-值 = refl

修正-2步-值 : 修正-2步 ≡ dn 2 4 1 2
修正-2步-值 = refl

修正-终止 : rt 修正-2步 ≡ 1
修正-终止 = refl

修正-乘率 : lt 修正-2步 ≡ 2
修正-乘率 = refl

-- 义务 ① 实例化到 (3,5)
修正-初始不变 : Inv 3 5 (dayanN-init 3 5)
修正-初始不变 = init-invariant 3 5

-- 义务 ② 连续两次实例化
修正-1步-不变 : Inv 3 5 修正-1步
修正-1步-不变 = step-invariant 3 5 (dayanN-init 3 5) (s≤s z≤n) 修正-初始不变

修正-2步-不变 : Inv 3 5 修正-2步
修正-2步-不变 = step-invariant 3 5 修正-1步 (s≤s z≤n) 修正-1步-不变

-- 计算得到的乘率性质（refl 级）
修正-乘率性质 : (lt 修正-2步 * 3) % 5 ≡ 1
修正-乘率性质 = refl

-- 同一命题由义务 ③（定理）而非计算得到 —— 交叉比对闭合
修正-乘率性质′ : (lt 修正-2步 * 3) % 5 ≡ 1
修正-乘率性质′ = dayan-correct 3 5 修正-2步 (s≤s (s≤s z≤n)) 修正-2步-不变 修正-终止

--------------------------------------------------------------------------------
-- §7. 原版反例：上游 `dayan-step` + `乘率` 在 (奇=3, 定=5) 上失效
--
--   上游状态追踪（`(q*lt) ∸ lb` 饱和减法 + `乘率 = 定 ∸ lt`）：
--     初始 (1,0,3,5)
--       步1: q = 5/3 = 1, r = 5%3 = 2, diff = (1*1) ∸ 0 = 1  ⟹ (1,1,2,3)
--       步2: q = 3/2 = 1, r = 3%2 = 1, diff = (1*1) ∸ 1 = 0  ⟹ (0,1,1,2)
--     rt = 1 终止，lt = 0；乘率 = 5 ∸ 0 = 5。
--   验证失败：3·5 = 15 ≡ 0 (mod 5) ≠ 1。
--------------------------------------------------------------------------------

open import Sovereign.Algebra.GroupTheory.DayanState
  using (DayanState; dayan; dayan-init; dayan-step; 乘率; left-top)

原版-2步 : DayanState
原版-2步 = dayan-step (dayan-step (dayan-init 3 5))

原版-2步-值 : 原版-2步 ≡ dayan 0 1 1 2
原版-2步-值 = refl

原版-乘率 : ℕ
原版-乘率 = 乘率 5 3 (left-top 原版-2步)

原版-乘率-值 : 原版-乘率 ≡ 5
原版-乘率-值 = refl

-- 反例本体：原版给出的「乘率」不满足模逆性质
原版-反例 : ¬ ((3 * 原版-乘率) % 5 ≡ 1)
原版-反例 = λ ()

-- 同一实例下修正形给出正确乘率（与 §6 一致）
修正-同例 : (lt 修正-2步 * 3) % 5 ≡ 1
修正-同例 = refl

--------------------------------------------------------------------------------
-- §8. 展示群八要素核对（本模块是投影层算术，逐项标注归属与缺口）
--
-- ① 载体：`DayanN`（四格 ℕ 记录）——投影层，非 DC 载体           ✓ §2
-- ② 生成元：`dayanN-init`（立天元一于左上）                      ✓ §2
-- ③ 关系：`dayanN-step`（递互除乘，模加版）                      ✓ §3
-- ④ 相位：四格轮转（(lt,lb) 与 (rt,rb) 的递互对换）              ✓ §4 注
-- ⑤ 时钟：迭代到 rt ≡ 1；整术终止性（rt 严格递减）**未证**        ⚠ 缺口
-- ⑥ 归零：`rt ≡ 1`（奇一而止）⟹ 乘率性质                        ✓ 义务③
-- ⑦ 刚性：不变量 `Inv`（lt·奇 ≡ rt ∧ lb·奇 ≡ rb）                ✓ 义务②
-- ⑧ 核对：refl 实例 (3,5) ＋ 定理实例交叉比对                    ✓ §6
--
-- 外部计算事实（**非 Agda 定理**）：修正形对 2 ≤ 定 ≤ 200 的全部
-- 12231 组互素对 (奇,定) 100% 抵达 rt = 1 且给出正确逆元；上游原版
-- 在同一域上仅 22.6% 成功。反例本身（§7）是内核级证明，覆盖率不是。
--------------------------------------------------------------------------------
