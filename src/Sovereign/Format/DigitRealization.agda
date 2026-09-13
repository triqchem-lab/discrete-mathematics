{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Format.DigitRealization where

-- | Sovereign.Format.DigitRealization —— **桥：位域 ↔ 进制**
--
-- 本模块**不是**任一范畴的内部事实，而是两个范畴之间的桥：
--   · 左：`Sovereign.Format.DigitField` —— 位域（字段状态数、划分）
--   · 右：`Sovereign.Format.Positional` / `Doz` —— 进制（权重 `b^k`、位值 `0..b−1`、逢 b 进一）
--
-- 桥只有两句话，而且**都是双射或不等式，不是相等**：
--
--   1. **承载**：一个 12 态位域 ⇄ 1 个三态域 + 2 个二态域。
--      由库里已证的 CRT 双射给出（`crt12` / `π3` / `π4` 的两个往返）；本模块只搬运，
--      不重新证明任何数学。
--   2. **容量 ⇒ 位数**：容量为 C 的位域能承载多少位**以 12 为底**的数位。
--      这是位域容量与进制基数之间的换算，属桥，不属任一侧。
--
-- ⚠️ 桥不是同一（范畴红线，见 `docs/duodecimal/08-terminology.md` §7.5）：
--    `realize`/`separate` 是双射，于是「12 态位域」与「一位十二进制数位」**一一对应**；
--    但前者是字段容量、后者是记数法的位。写成等号就是范畴错误。
--    同理，容量 `12⁹ = 3⁹·2¹⁸` 是**位域**事实，不等于「12 进制 = 3 进制 × 2 进制」。

open import Data.Nat using (ℕ; suc; _+_; _*_; _^_)
open import Data.Fin using (Fin)
import Data.Fin as F
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

import Sovereign.Base.Trit as T
import Sovereign.Algebra.Duodecimal as Duo

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 承载：12 态位域 ⇄ 1 个三态域 + 2 个二态域
--------------------------------------------------------------------------------

-- 两个二态域 ↔ 4 态位域（显式双射，4 个 case）
bitsToFin4 : Fin 2 → Fin 2 → Fin 4
bitsToFin4 F.zero    F.zero    = F.zero
bitsToFin4 F.zero    (F.suc _) = F.suc F.zero
bitsToFin4 (F.suc _) F.zero    = F.suc (F.suc F.zero)
bitsToFin4 (F.suc _) (F.suc _) = F.suc (F.suc (F.suc F.zero))

fin4ToBits : Fin 4 → Fin 2 × Fin 2
fin4ToBits F.zero                    = F.zero , F.zero
fin4ToBits (F.suc F.zero)            = F.zero , F.suc F.zero
fin4ToBits (F.suc (F.suc F.zero))    = F.suc F.zero , F.zero
fin4ToBits (F.suc (F.suc (F.suc _))) = F.suc F.zero , F.suc F.zero

fin4-roundtrip : ∀ b → fin4ToBits (bitsToFin4 (proj₁ b) (proj₂ b)) ≡ b
fin4-roundtrip (F.zero , F.zero)             = refl
fin4-roundtrip (F.zero , F.suc F.zero)       = refl
fin4-roundtrip (F.suc F.zero , F.zero)       = refl
fin4-roundtrip (F.suc F.zero , F.suc F.zero) = refl

-- 分离位域：1 个三态域 × 1 个「二阶字段」（= 两个二态域）
SepField : Set
SepField = T.Trit × Fin 4

-- 12 元**载体**（库里已有的 `Duodec`）——它是 12 态位域的标签集，不是记数法的位
Realized : Set
Realized = Duo.Duodec

-- 桥：分离位域 → 12 元载体（就是库里的 crt12 = (4a + 9b) mod 12）
realize : SepField → Realized
realize (t , b) = Duo.crt12 t b

-- 桥：12 元载体 → 分离位域（mod 3 与 mod 4）
separate : Realized → SepField
separate n = Duo.π3 n , Duo.π4 n

-- 双向往返（复用库中已证的 CRT 引理）
realize-separate : ∀ n → realize (separate n) ≡ n
realize-separate n = Duo.crt12-roundtrip n

separate-realize : ∀ d → separate (realize d) ≡ d
separate-realize (t , b) = cong₂ _,_ (Duo.crt12-inv-π3 t b) (Duo.crt12-inv-π4 t b)

--------------------------------------------------------------------------------
-- §2. 容量 ⇒ 位数：位域容量与进制基数之间的换算
--------------------------------------------------------------------------------

-- 写法：`C ≡ 12^11 + k`（k ≥ 0）即 `12^11 ≤ C`；`12^12 ≡ suc C + k'` 即 `C < 12^12`。
-- 合起来：容量 C 恰好装得下 11 位以 12 为底的数位。
-- C 的取值来自 `DigitField`（位域层），这里只做「容量 ↔ 位数」的换算。

-- 27 个三态域（C = 3^27）
doz11-in-27trit : 3 ^ 27 ≡ 12 ^ 11 + 6882589114299
doz11-in-27trit = refl

doz12-not-in-27trit : 12 ^ 12 ≡ suc (3 ^ 27) + 1290502963268
doz12-not-in-27trit = refl

-- 43 个二态域（C = 2^43）
doz11-in-43bit : 2 ^ 43 ≡ 12 ^ 11 + 8053084651520
doz11-in-43bit = refl

doz12-not-in-43bit : 12 ^ 12 ≡ suc (2 ^ 43) + 120007426047
doz12-not-in-43bit = refl

-- 混合位域（9 个三态域 + 18 个二态域）的容量恰等于 12⁹ ⇒ 恰好 9 位，余量为零
mixed-exact : 3 ^ 9 * 2 ^ 18 ≡ 12 ^ 9
mixed-exact = refl

-- 对照：固定「每位数位占 3 个三态域」的交织布局下，9 位占 27 个三态域，
-- 而容量上只需 ⌈9·log₃12⌉ = 21 个三态域（3^20 < 12^9 < 3^21，见下），故有冗余。
-- 这两条把「布局」与「容量」也分开：冗余来自**布局**，不是来自**进制**。
-- 20 个三态域装不下 9 位（12^9 > 3^20）⇒ 至少要 21 个
doz9-not-in-20trit : 12 ^ 9 ≡ 3 ^ 20 + 1672995951
doz9-not-in-20trit = refl

-- 21 个三态域装得下（12^9 ≤ 3^21）
doz9-fits-21trit : 3 ^ 21 ≡ 12 ^ 9 + 5300572851
doz9-fits-21trit = refl

--------------------------------------------------------------------------------
-- §3. 经过桥读数值：换算保值（位表在两条承载之间翻译，数不变）
--------------------------------------------------------------------------------

-- 位域承载的位表的值：以 12 为底的权重（权重来自**进制层**，此处只是通过桥读取）
valueByField : List SepField → ℕ
valueByField []       = 0
valueByField (d ∷ ds) = Duo.toℕ₁₂ (realize d) + 12 * valueByField ds

-- 进制位表的值（纯进制层口径）
valueByDigits : List Realized → ℕ
valueByDigits []       = 0
valueByDigits (n ∷ ns) = Duo.toℕ₁₂ n + 12 * valueByDigits ns

-- 换算保值（位域 → 进制）：把每一位的位域实现翻译成数位，数不变
value-field-hom : ∀ xs → valueByField xs ≡ valueByDigits (map realize xs)
value-field-hom [] = refl
value-field-hom (d ∷ ds) =
  cong (λ z → Duo.toℕ₁₂ (realize d) + 12 * z) (value-field-hom ds)

-- 换算保值（进制 → 位域）：反向翻译同样不改数
value-digits-hom : ∀ ns → valueByDigits ns ≡ valueByField (map separate ns)
value-digits-hom [] = refl
value-digits-hom (n ∷ ns) =
  cong₂ (λ a b → a + 12 * b)
        (cong Duo.toℕ₁₂ (sym (realize-separate n)))
        (value-digits-hom ns)
