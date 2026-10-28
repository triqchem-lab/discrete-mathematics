{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.T6Iso —— T⁶ 格点群与 GF(3⁶) 的群级同构
--
-- == 命题（把「729 = 3⁶ 的同一性」从集合级升到群级）
--
-- T⁶ 格点 = (Z/3)⁶ = 729 点（6-trit 机器字）；GF(3⁶) = GF(3)[θ]/(θ⁶+θ+2)
-- = 729 元域（GF36.agda）。两者**作为带结构对象**的关系，本模块钉两层：
--
-- 1. **加法群同构**（结构层）：(T⁶, +t6) ≅ (GF(3⁶), +gf36)。
--    同态 = 坐标恒等映射（两运算同为逐分量 ⊕，定义性一致）；
--    双射：单射（恒等映像）+ 满射（to-t6 为逆）。729 点的集合同一性
--    由此带上群结构——不再只是「都是 729 个」。
-- 2. **乘法巡游**（计算层）：GF(3⁶)\* ≅ C₇₂₈，生成元 = **θ 本身**
--    （全 729 元中最稀疏者，坐标 (0,1,0,0,0,0)；728 = 8·7·13）。
--    幂序列 θ⁰, θ¹, …, θ⁷²⁷ 遍历全部 728 个非零格点各一次，θ⁷²⁸ = 1——
--    这就是「T⁶ 巡游」的 GF(3⁶) 算术形式：巡游 = {零元} + C₇₂₈ 循环，
--    可由 ISA 乘法单元直接执行（重复乘 θ 即可，无需专门寻址）。
--
-- == 口径（遵 2026-10-28 handoff 口径第一条）
--
-- · 加法同态/双射/σ-传输：坐标恒等，`refl` 即定义性成立（两种运算的
--   定义展开式逐分量同一）——这是**结构事实**，非暴力枚举；
-- · 巡游三 pin（θ⁷²⁸=1 / 728 项互异 / 零元缺席）：**全枚举校验编码**
--   （约 26 万次域乘的归约，Python 独立复算互证），引用写「全枚举」。
--   循环群遍历由两点计数成立：728 个互异非零元落在一个恰有 728 个
--   非零元的域里 ⇒ 遍历全部非零元各一次。
--
-- == 与既有件的对接
--
-- · GF36.agda：域运算、σ、子域驻留谓词、all729 枚举；
-- · Embed36.agda：GF(9)/GF(27) 通道（子域结构是 GF(3⁶) 的附加结构，
--   普通 T⁶ 格点上没有——同构只是加法群的，勿过度声称）；
-- · ternary 仓 gf36.rs 与 trha：机器字 6-trit 即 T⁶ 点即 GF(3⁶) 元，
--   三读法一物。
--
-- 依赖：GF36 / Trit。0 postulate。
module Sovereign.Algebra.FieldTower.T6Iso where

open import Data.Bool
  using (Bool; true; false; not; _∧_; _≡ᵇ_; if_then_else_)
open import Data.List using (List; _∷_; []; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Algebra.FieldTower.GF36
  using (GF36; frobenius36; gf36-zero; gf36-one; theta36; _+gf36_; _*gf36_;
         _==ᵗ⁶_; _==³⁶_; keepIf36; dedup36; all729;
         subfield1; subfield2; subfield3)

--------------------------------------------------------------------------------
-- §1. T⁶ 格点群：(Z/3)⁶ 六重直积
--
-- T⁶ 与 GF36 的载体是同一形状的 6-trit 元组；差别只在结构来源——
-- T⁶ 的加法从 C₃ 直积定义（本节），GF(3⁶) 的加法是域的加法（GF36 §2）。
--------------------------------------------------------------------------------

T6 : Set
T6 = Trit × Trit × Trit × Trit × Trit × Trit

t6-zero : T6
t6-zero = T₀ , T₀ , T₀ , T₀ , T₀ , T₀

infixl 6 _+t6_
_+t6_ : T6 → T6 → T6
(a₀ , a₁ , a₂ , a₃ , a₄ , a₅) +t6 (b₀ , b₁ , b₂ , b₃ , b₄ , b₅) =
  (a₀ ⊕ b₀) , (a₁ ⊕ b₁) , (a₂ ⊕ b₂) , (a₃ ⊕ b₃) , (a₄ ⊕ b₄) , (a₅ ⊕ b₅)

--------------------------------------------------------------------------------
-- §2. 加法群同构：to-gf36 = 坐标恒等（结构事实，refl 级）
--------------------------------------------------------------------------------

to-gf36 : T6 → GF36
to-gf36 x = x

to-t6 : GF36 → T6
to-t6 x = x

-- 同态：T⁶ 加法 ↦ GF(3⁶) 加法
to-gf36-hom : ∀ x y → to-gf36 (x +t6 y) ≡ to-gf36 x +gf36 to-gf36 y
to-gf36-hom x y = refl

-- 单射：恒等映射
to-gf36-injective : ∀ x y → to-gf36 x ≡ to-gf36 y → x ≡ y
to-gf36-injective _ _ eq = eq

-- 满射：to-t6 是逆
to-gf36-surjective : ∀ x → to-gf36 (to-t6 x) ≡ x
to-gf36-surjective x = refl

-- 零元传输
to-gf36-zero : to-gf36 t6-zero ≡ gf36-zero
to-gf36-zero = refl

--------------------------------------------------------------------------------
-- §3. σ-传输：格点上的 Frobenius 算子经同构与域侧一致
--
-- frobenius-t6 与 frobenius36 是同一坐标闭式（GF36 §Frobenius）；
-- 传输定理为定义性成立（refl）。
--------------------------------------------------------------------------------

frobenius-t6 : T6 → T6
frobenius-t6 (a₀ , a₁ , a₂ , a₃ , a₄ , a₅) =
    ((a₀ ⊕ a₂) ⊕ a₄)
  , ((negate a₂) ⊕ a₄)
  , a₄
  , ((a₁ ⊕ a₃) ⊕ a₅)
  , ((negate a₃) ⊕ a₅)
  , a₅

to-gf36-σ : ∀ x → to-gf36 (frobenius-t6 x) ≡ frobenius36 (to-gf36 x)
to-gf36-σ x = refl

--------------------------------------------------------------------------------
-- §4. 乘法巡游：GF(3⁶)\* = C₇₂₈，生成元 = θ（728 阶）
--
-- pin-36-fix-* 已证 |GF(3⁶)| = 729；本节证：
--   (a) θ⁷²⁸ = 1（闭合）；
--   (b) θ⁰ … θ⁷²⁷ 互异（728 项去重仍 728）；
--   (c) 巡游不含零元。
-- 计数收束：728 个互异非零元 = GF(3⁶) 非零元全体 ⇒ 巡游遍历全部
-- 非零格点各一次（Python 独立复算互证；口径：全枚举校验编码）。
--------------------------------------------------------------------------------

gen36 : GF36
gen36 = theta36

pow36 : GF36 → ℕ → GF36
pow36 _ zero = gf36-one
pow36 g (suc n) = g *gf36 pow36 g n

-- 降序自然数列 [n−1, …, 1, 0]（巡游索引用；避免与库内名单撞车）
idx-down36 : ℕ → List ℕ
idx-down36 zero = []
idx-down36 (suc n) = n ∷ idx-down36 n

tour36 : ℕ → List GF36
tour36 n = map (pow36 gen36) (idx-down36 n)

pin-tour-closes : pow36 gen36 728 ≡ gf36-one
pin-tour-closes = refl

pin-tour-728-distinct : length (dedup36 (tour36 728)) ≡ 728
pin-tour-728-distinct = refl

pin-tour-nonzero : length (keepIf36 (λ x → x ==³⁶ gf36-zero) (tour36 728)) ≡ 0
pin-tour-nonzero = refl

--------------------------------------------------------------------------------
-- §5. 驻留谓词经同构的传输（子域结构是域侧附加结构，经 σ 带到格点）
--
-- 格点侧谓词（subfield-d-t6，经 frobenius-t6 迭代定义）与域侧谓词
-- （GF36 subfield1/2/3）在同构下逐点一致：全部 729 点上三条谓词的
-- Bool 相等全枚举 pin。
--------------------------------------------------------------------------------

subfield1-t6 : T6 → Bool
subfield1-t6 x = to-gf36 (frobenius-t6 x) ==³⁶ to-gf36 x

subfield2-t6 : T6 → Bool
subfield2-t6 x = to-gf36 (frobenius-t6 (frobenius-t6 x)) ==³⁶ to-gf36 x

subfield3-t6 : T6 → Bool
subfield3-t6 x =
  to-gf36 (frobenius-t6 (frobenius-t6 (frobenius-t6 x))) ==³⁶ to-gf36 x

-- 传输 pin：三条格点侧谓词与域侧谓词在全部 729 点上逐点一致
-- （「格点谓词成立 ⇔ 域谓词成立」的 Bool 代数式，std 无 Bool 相等算子故用
--  if/not/∧ 组合表达）
pin-subfield-transport : length (keepIf36 (λ x →
  (if subfield1-t6 x then subfield1 x else not (subfield1 x)) ∧
  (if subfield2-t6 x then subfield2 x else not (subfield2 x)) ∧
  (if subfield3-t6 x then subfield3 x else not (subfield3 x))) all729) ≡ 729
pin-subfield-transport = refl
