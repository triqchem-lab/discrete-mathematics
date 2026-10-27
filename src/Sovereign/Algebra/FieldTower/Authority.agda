{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.Authority —— 授权迁移闭包定理
--
-- == 定位（架构文档「Frobenius 拦截」的可证重建·第二卷）
--
-- Intercept.agda 已证：Frobenius 不动点 = 基域 GF(3) 嵌入像（T2）、
-- 非基域乘子必破坏交换性（T5）。本模块补**授权迁移闭包**——把「合法跃迁 /
-- 非法跃迁」从自由变元变成有主定义，并证明其封闭性与拦截可判定性：
--
-- 1. **授权乘子集**（有主定义）= 基域可逆标量 {one, 2}。2 = −1 = α¹³，
--    2·2 = 1，构成 C₂ 群。选它作授权集的代数理由：基域是 GF(27) 与
--    GF(9) 的唯一公共子域（GF27.agda §10：2 ∤ 3 故 GF(9) ⊄ GF(27)），
--    基域标量乘因此是「双塔通用」的迁移。
-- 2. **组合封闭**（T-A）：{one, 2} 在域乘法下封闭（C₂ 群，4 对组合 pin）
--    ——授权迁移可任意复合而不出圈。
-- 3. **σ-等变**（T-B）：授权乘子与 Frobenius 在**全部 27 元素**上交换
--    ——授权迁移保持 Frobenius 轨道结构（轨道里的态授权迁移后仍在轨道里）。
-- 4. **正闭包**（T-C）：授权乘法保持基域驻留性（对全体 27 元素的蕴含 pin）。
-- 5. **负闭包 = 拦截定理**（T-D）：25 个非授权乘子作用于基域驻留态 one——
--    · 24 个非基域 a：a·1 = a **必非基域驻留** ⇒ 被 baseResident 检验捕获；
--    · 零乘子：0·1 = 0，落入**吸收态**（架构文档的状态 0 拒绝）。
--    两种偏差都可由一次乘法 + 一次驻留检验判定（27 步可判定）。
-- 6. **与 T5 的桥**（T-E）：授权乘子必交换（authorized ⇒ commuteWithσ），
--    且交换而非授权者恰为 {零乘子}——授权集 = 交换集 ∖ {0}。
--
-- == 枚举完备性守卫
--
-- `dedup27 all27 ≡ 27`（去重后仍 27 项）拦截「枚举表含重复/漏元素」这类
-- 缺陷： Intercept.agda 的 all27 曾把 (T₂,T₂,T₁) 误写成 (T₂,T₁,T₁)（重复
-- + 漏项），各 pin 结论碰巧不受影响，但「27 元素全覆盖」口径失效——本
-- pin 即该缺陷的回归测试。
--
-- 复用：all27 / ==²⁷ / keepIf / commuteWithσ 来自 Intercept.agda；
-- σ 与 σ³ = id 来自 GF27.agda §5b。全部 pin 为闭项 refl。0 postulate。
module Sovereign.Algebra.FieldTower.Authority where

open import Data.Bool
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; _∷_; []; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.FieldTower.GF27
  using (GF27; frobenius; gf27-zero; gf27-one; embed-gf3-gf27; _*gf27_)
open import Sovereign.Algebra.FieldTower.Intercept
  using (all27; _==ᵗ_; _==²⁷_; keepIf; commuteWithσ)

--------------------------------------------------------------------------------
-- 授权乘子集：基域可逆标量 {one, 2}
--------------------------------------------------------------------------------

authTwo : GF27
authTwo = embed-gf3-gf27 T₂

authorized : GF27 → Bool
authorized a = (a ==²⁷ gf27-one) ∨ (a ==²⁷ authTwo)

--------------------------------------------------------------------------------
-- 基域驻留检验（拦截的可执行判据）：x = (a,b,c) 驻留 ⟺ b = c = 0
-- 即 Intercept T2 的不动点列表（零、一、二）的特征谓词。
--------------------------------------------------------------------------------

baseResident : GF27 → Bool
baseResident (a , b , c) = (b ==ᵗ T₀) ∧ (c ==ᵗ T₀)

--------------------------------------------------------------------------------
-- 枚举完备性守卫：all27 无重复（27 项去重后仍 27 项）
--------------------------------------------------------------------------------

elem27 : GF27 → List GF27 → Bool
elem27 _ [] = false
elem27 x (y ∷ ys) = (x ==²⁷ y) ∨ elem27 x ys

dedup27 : List GF27 → List GF27
dedup27 [] = []
dedup27 (x ∷ xs) = if elem27 x xs then dedup27 xs else x ∷ dedup27 xs

pin-auth-all27-length : length all27 ≡ 27
pin-auth-all27-length = refl

pin-auth-all27-nodup : length (dedup27 all27) ≡ 27
pin-auth-all27-nodup = refl

--------------------------------------------------------------------------------
-- T-A：组合封闭——{one, 2} 在域乘法下封闭（C₂ 群，2·2 = 1）
--------------------------------------------------------------------------------

pin-auth-compose-11 : authorized (gf27-one *gf27 gf27-one) ≡ true
pin-auth-compose-11 = refl

pin-auth-compose-12 : authorized (gf27-one *gf27 authTwo) ≡ true
pin-auth-compose-12 = refl

pin-auth-compose-21 : authorized (authTwo *gf27 gf27-one) ≡ true
pin-auth-compose-21 = refl

pin-auth-compose-22 : authorized (authTwo *gf27 authTwo) ≡ true
pin-auth-compose-22 = refl

--------------------------------------------------------------------------------
-- T-B：σ-等变——授权乘子与 Frobenius 在全部 27 元素上交换
--
-- σ(1·x) = σ(x)（1 被 σ 固定）；σ(2·x) = 2·σ(x)（2 = α¹³，σ(α¹³) = α³⁹
-- = α¹³ (mod 26)）。坐标直证：2·x 逐分量取负，negate 与 σ 的分量式交换。
--
-- ⇒ 授权迁移保持 Frobenius 轨道结构。
--------------------------------------------------------------------------------

pin-auth-σ-equiv-one : length (keepIf (λ x →
  frobenius (gf27-one *gf27 x) ==²⁷ (gf27-one *gf27 (frobenius x))) all27) ≡ 27
pin-auth-σ-equiv-one = refl

pin-auth-σ-equiv-two : length (keepIf (λ x →
  frobenius (authTwo *gf27 x) ==²⁷ (authTwo *gf27 (frobenius x))) all27) ≡ 27
pin-auth-σ-equiv-two = refl

--------------------------------------------------------------------------------
-- T-C：正闭包——授权乘法保持基域驻留性（全体 27 元素的蕴含式 pin）
--------------------------------------------------------------------------------

pin-auth-keeps-base : length (keepIf (λ x →
  if baseResident x then baseResident (authTwo *gf27 x) else true) all27) ≡ 27
pin-auth-keeps-base = refl

--------------------------------------------------------------------------------
-- T-D：负闭包 = 拦截定理
--
-- 非授权乘子 a 作用于基域驻留态 one（a·1 = a）：
--   · 24 个非基域 a：结果非基域驻留 ⇒ 拦截判据捕获；
--   · 零乘子：0·1 = 0 吸收态（文档的状态 0 拒绝），驻留但可由零检验捕获。
--------------------------------------------------------------------------------

pin-auth-escape : length (keepIf (λ a →
  not (authorized a) ∧ not (baseResident (a *gf27 gf27-one))) all27) ≡ 24
pin-auth-escape = refl

pin-auth-absorb-zero : (gf27-zero *gf27 gf27-one) ==²⁷ gf27-zero ≡ true
pin-auth-absorb-zero = refl

--------------------------------------------------------------------------------
-- T-E：与 Intercept T5 的桥——授权集 = 交换集 ∖ {零乘子}
--
-- 交换集（commuteWithσ）= 基域嵌入像 {0, 1, 2}（Intercept pin-commute）；
-- 去掉零乘子即授权集。双向各一枚举 pin。
--------------------------------------------------------------------------------

pin-auth-subset-commute : length (keepIf (λ a →
  if authorized a then commuteWithσ a else true) all27) ≡ 27
pin-auth-subset-commute = refl

pin-auth-commute-minus-auth : length (keepIf (λ a →
  not (authorized a) ∧ commuteWithσ a) all27) ≡ 1
pin-auth-commute-minus-auth = refl
