{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.Embed36 —— GF(9)/GF(27) 嵌入 GF(3⁶) 的同态定理
--
-- == 定位（三进制 L1 统一域的塔完备性）
--
-- GF36.agda 确立 GF(3⁶) 的塔结构（fixed(σᵈ) = 3ᵈ，d∣6）与嵌入种子
-- （β² = 2、γ³ = γ+2）。本模块把种子升格为**完整域嵌入**并证明：
--
--   · emb9  : GF9  → GF36,  (a,b)     ↦ a + b·β      （β² = 2 = α₉²）
--   · emb27 : GF27 → GF36,  (a,b,c)   ↦ a + b·γ + c·γ²（γ³ = γ+2 = α₂₇³）
--
-- 各卷内容与**口径分层**（遵 2026-10-28 handoff 口径第一条 / 范式文档纪律二
-- 「算术冒充证明禁令」）：
--
--   · §3 单位元/命名对应：定义自洽的闭项 refl；
--   · §4 标量乘引理：**t 全枚举 3-case 闭合归约**（\*gf36 对 (t,0,0,0,0,0)
--     交叉项全 ⊗0 消失、无 θ⁶ 约化项；分配律非定义性，故逐 case）；
--   · §5 加法性 / §6 乘法性：**有限集全枚举**（81 / 729 对，电性层校验编
--     号）。结构理由：emb(d·f) = 多项式在 β/γ 处求值；γ³ = γ+2 与 α³ = α+2
--     （GF27 alpha-cubed-struct）、β² = 2 与 α₉² = 2 是**同一生成关系**，
--     且 emb 为 GF(3)-线性映射之和（§4）故保 ⊕——升格为坐标级结构证明留
--     待后续，当前引用写「全枚举」；
--   · §7 Frobenius 相容：全枚举（9 / 27 对）——emb(σx) = σ(emb x)；
--   · §8 像 ⊆ σ^(6/d)-不动子域 + §9 单射：全枚举；
--   · §10 计数收束：|GF(d)| = 3ᵈ = |fixed(σ^(6/d))|（GF36 已证）+ 单射
--     ⇒ **像恰为该不动子域**。GF(9) ⊆ GF(3⁶)、GF(27) ⊆ GF(3⁶) 从此是
--     带见证的定理；与 GF27 §10「GF(9) ⊄ GF(27)」（2 ∤ 3）合成完整塔图：
--     GF(3) ⊂ GF(9) ⊂ GF(3⁶) ← GF(27) ⊂ GF(3⁶)。
--
-- == 与三进制 ISA 的对应（纲领 §3 层 1）
--
-- 6-trit 寄存器 = GF(3⁶) 机器字；emb9/emb27 即「2-trit GF(9) 通道」与
-- 「3-trit GF(27) 通道」通向机器字的语义映射——两条通道都活在一个域内，
-- 子域驻留指令（GF36.subfield1/2/3）就是它们的类型判别器。
--
-- 依赖：GF9 / GF27 / GF36 / Intercept（all27、==²⁷）。0 postulate。
module Sovereign.Algebra.FieldTower.Embed36 where

open import Data.Bool
  using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; _∷_; []; map; concatMap; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.FieldTower.GF9
  using (GF9; _+gf9_; _*gf9_; gf9-one; alpha; embed-gf3; galoisConjugate)
open import Sovereign.Algebra.FieldTower.GF27
  using (GF27; gf27-zero; gf27-one; alpha-sq; frobenius; _+gf27_; _*gf27_)
open import Sovereign.Algebra.FieldTower.GF36
  using (GF36; frobenius36; gf36-zero; gf36-one; embed-gf3-gf36;
         _+gf36_; _*gf36_; _==³⁶_; _==ᵗ⁶_; subfield2; subfield3; beta36; gamma36)
open import Sovereign.Algebra.FieldTower.Intercept using (all27; _==ᵗ_; _==²⁷_)

--------------------------------------------------------------------------------
-- §1. 嵌入定义
--------------------------------------------------------------------------------

emb9 : GF9 → GF36
emb9 (a , b) = embed-gf3-gf36 a +gf36 (beta36 *gf36 embed-gf3-gf36 b)

emb27 : GF27 → GF36
emb27 (a , b , c) =
  (embed-gf3-gf36 a +gf36 (gamma36 *gf36 embed-gf3-gf36 b))
    +gf36 ((gamma36 *gf36 gamma36) *gf36 embed-gf3-gf36 c)

--------------------------------------------------------------------------------
-- §2. 枚举辅助
--------------------------------------------------------------------------------

_==⁹_ : GF9 → GF9 → Bool
(a , b) ==⁹ (c , d) = (a ==ᵗ c) ∧ (b ==ᵗ d)

all9 : List GF9
all9 =
  (T₀ , T₀) ∷ (T₁ , T₀) ∷ (T₂ , T₀) ∷
  (T₀ , T₁) ∷ (T₁ , T₁) ∷ (T₂ , T₁) ∷
  (T₀ , T₂) ∷ (T₁ , T₂) ∷ (T₂ , T₂) ∷ []

keepEmb : {A : Set} → (A → Bool) → List A → List A
keepEmb p [] = []
keepEmb p (x ∷ xs) = if p x then x ∷ keepEmb p xs else keepEmb p xs

pairs9 : List (GF9 × GF9)
pairs9 = concatMap (λ x → map (x ,_) all9) all9

pairs27 : List (GF27 × GF27)
pairs27 = concatMap (λ x → map (x ,_) all27) all27

--------------------------------------------------------------------------------
-- §3. 单位元 / 命名对应（定义自洽）
--------------------------------------------------------------------------------

pin-emb9-alpha : emb9 alpha ≡ beta36
pin-emb9-alpha = refl

-- α₂₇ = (T₀,T₁,T₀)（GF27.agda 的 alpha 值；不导入其名以避与 GF9.alpha 撞名）
pin-emb27-alpha : emb27 (T₀ , T₁ , T₀) ≡ gamma36
pin-emb27-alpha = refl

pin-emb9-one : emb9 gf9-one ≡ gf36-one
pin-emb9-one = refl

pin-emb27-one : emb27 gf27-one ≡ gf36-one
pin-emb27-one = refl

pin-emb27-alpha-sq : emb27 alpha-sq ≡ gamma36 *gf36 gamma36
pin-emb27-alpha-sq = refl

--------------------------------------------------------------------------------
-- §4. 标量乘引理（结构）：基域标量与 β/γ 的乘积 = 逐分量标量作用
--
-- embed t = (t,0,0,0,0,0) 与任意 w 的乘积按 *gf36 公式退化为逐分量 wᵢ⊗t
-- （交叉项全 ⊗0 消失，无 θ⁶ 约化项）。
--------------------------------------------------------------------------------

beta-scalar : ∀ t →
  beta36 *gf36 embed-gf3-gf36 t
    ≡ ((T₀ ⊗ t) , (T₁ ⊗ t) , (T₂ ⊗ t) , (T₁ ⊗ t) , (T₁ ⊗ t) , (T₀ ⊗ t))
beta-scalar T₀ = refl
beta-scalar T₁ = refl
beta-scalar T₂ = refl

gamma-scalar : ∀ t →
  gamma36 *gf36 embed-gf3-gf36 t
    ≡ ((T₀ ⊗ t) , (T₀ ⊗ t) , (T₁ ⊗ t) , (T₂ ⊗ t) , (T₁ ⊗ t) , (T₀ ⊗ t))
gamma-scalar T₀ = refl
gamma-scalar T₁ = refl
gamma-scalar T₂ = refl

--------------------------------------------------------------------------------
-- §5. 加法性（全枚举校验：81 / 729 对；结构注记）
--
-- 结构注记：emb9/emb27 都是 GF(3)-线性映射之和（§4 标量乘引理 + 基嵌入的
-- 逐分量线性），线性映射保 ⊕——升格为坐标级结构证明留待后续，当前为全枚举。
--------------------------------------------------------------------------------

pin-emb9-add : length (keepEmb (λ p ->
  emb9 (proj₁ p +gf9 proj₂ p) ==³⁶ (emb9 (proj₁ p) +gf36 emb9 (proj₂ p))) pairs9) ≡ 81
pin-emb9-add = refl

pin-emb27-add : length (keepEmb (λ p ->
  emb27 (proj₁ p +gf27 proj₂ p) ==³⁶ (emb27 (proj₁ p) +gf36 emb27 (proj₂ p))) pairs27) ≡ 729
pin-emb27-add = refl

--------------------------------------------------------------------------------
-- §6. 乘法性（全枚举校验：81 / 729 对）
--
-- 结构理由（注记，非本模块证明）：emb(d·f) = 多项式在 β/γ 处求值；
-- β² = 2 与 α₉² = 2、γ³ = γ+2 与 α³ = α+2 为同一生成关系（前者见
-- GF36 pin-36-beta-sq，后者见 pin-36-gamma-cube 与 GF27 alpha-cubed-struct），
-- 求值同态由此保乘法。以下全枚举为电性层校验编码，引用写「全枚举」。
--------------------------------------------------------------------------------

pin-emb9-mul : length (keepEmb (λ p ->
  emb9 (proj₁ p *gf9 proj₂ p) ==³⁶ (emb9 (proj₁ p) *gf36 emb9 (proj₂ p))) pairs9) ≡ 81
pin-emb9-mul = refl

pin-emb27-mul : length (keepEmb (λ p ->
  emb27 (proj₁ p *gf27 proj₂ p) ==³⁶ (emb27 (proj₁ p) *gf36 emb27 (proj₂ p))) pairs27) ≡ 729
pin-emb27-mul = refl

--------------------------------------------------------------------------------
-- §7. Frobenius 相容（全枚举：9 / 27 对）
--
-- 域同态在特征 3 下自动交换 x ↦ x³：emb(σx) = emb(x³) = emb(x)³。
-- GF9 侧 σ = galoisConjugate；GF27 侧 σ = frobenius。
--------------------------------------------------------------------------------

pin-emb9-σ : length (keepEmb (λ x →
  emb9 (galoisConjugate x) ==³⁶ frobenius36 (emb9 x)) all9) ≡ 9
pin-emb9-σ = refl

pin-emb27-σ : length (keepEmb (λ x →
  emb27 (frobenius x) ==³⁶ frobenius36 (emb27 x)) all27) ≡ 27
pin-emb27-σ = refl

--------------------------------------------------------------------------------
-- §8. 像 ⊆ σ^(6/d)-不动子域（全枚举）
--------------------------------------------------------------------------------

pin-emb9-image-fixed : length (keepEmb (λ x → subfield2 (emb9 x)) all9) ≡ 9
pin-emb9-image-fixed = refl

pin-emb27-image-fixed : length (keepEmb (λ x → subfield3 (emb27 x)) all27) ≡ 27
pin-emb27-image-fixed = refl

--------------------------------------------------------------------------------
-- §9. 单射（全枚举：x ≠ y ⇒ emb x ≠ emb y，计数 0 反例）
--------------------------------------------------------------------------------

pin-emb9-injective : length (keepEmb (λ p ->
  not (proj₁ p ==⁹ proj₂ p) ∧ (emb9 (proj₁ p) ==³⁶ emb9 (proj₂ p))) pairs9) ≡ 0
pin-emb9-injective = refl

pin-emb27-injective : length (keepEmb (λ p ->
  not (proj₁ p ==²⁷ proj₂ p) ∧ (emb27 (proj₁ p) ==³⁶ emb27 (proj₂ p))) pairs27) ≡ 0
pin-emb27-injective = refl

--------------------------------------------------------------------------------
-- §10. 计数收束（头注重述）
--
-- pin-emb27-injective（像含 27 个互异元素）+ pin-emb27-image-fixed（像 ⊆
-- σ³-不动集）+ GF36 pin-36-fix-σ³（σ³-不动集恰 27 元）
-- ⇒ 像 = σ³-不动子域 = GF(27) 在 GF(3⁶) 中的驻留面。
-- GF9 侧同构论证（9 = 9）。▫
--------------------------------------------------------------------------------

pin-pairs27-card : length pairs27 ≡ 729
pin-pairs27-card = refl

pin-pairs9-card : length pairs9 ≡ 81
pin-pairs9-card = refl
