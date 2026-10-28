{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.Embed36 —— GF(9)/GF(27) 嵌入 GF(3⁶) 的同态定理
--   （v2：坐标级结构证明升格）
--
-- == v2 升格内容（2026-10-28）
--
-- v1 的 emb9/emb27 经域运算（embed + beta36 *gf36 embed b）定义——对变量
-- 卡归约，加乘同态只能全枚举。v2 重定义为**坐标级闭式**（β/γ 坐标直接进
-- 定义，消掉 stuck-mul）：
--
--   · emb9 (a , b)      = a , b , (T₂ ⊗ b) , b , b , T₀
--     （= embed a +f36 B·embed b 的逐分量归约形；B = beta36）
--   · emb27 (a , b , c) = a , c , b , ((T₂ ⊗ b) ⊕ (T₂ ⊗ c)) , (b ⊕ c) , c
--     （= embed a +f36 G·embed b +f36 G²·embed c 的逐分量归约形；
--       G = gamma36，G² = gamma36 *gf36 gamma36；γ-平面把 b/c 换位）
--
-- == 口径分层（遵 2026-10-28 handoff 口径第一条）
--
--   · §3 标量乘引理：结构证明（⊗-zeroˡ / ⊗-identityˡ 闭 B/G，3-case）；
--   · §4 加法同态：**结构证明**（refl ×4 + ⊗-distribˡ-⊕ + sum4-swap）；
--   · §5 乘法同态：**构造子全 case 归约**（3⁴ = 81 / 3⁶ = 729 子句，全部
--     refl；与 Trit.agda ⊕-assoc 27-case 同法——有限型全称命题的标准
--     构造子归约证明，非数值表对拍）。证明体在
--     `Embed36MulClauses.agda`（生成文件），本模块引用；
--   · §6 Frobenius 相容 / §7 像⊆不动域 / §8 单射 / §9 计数收束：
--     全枚举校验（沿用 v1），同时是 v2 新定义的**交叉校验**（枚举 pin
--     结论不变即坐标级改写无回归）。
--
-- == 数学内容（不变）
--
-- GF(3⁶) = GF(3)[θ]/(θ⁶+θ+2) 统一域（GF36.agda）；emb9: GF(9) → GF(3⁶)
-- （β² = 2 = α₉²），emb27: GF(27) → GF(3⁶)（γ³ = γ+2 = α₂₇³）；
-- 保加乘幺 + Frobenius 相容 + 单射 ⇒ 像 = σ^(6/d)-不动子域（计数收束）：
-- GF(9) ⊂ GF(3⁶) ← GF(27) ⊂ GF(3⁶) 塔图完备。
--
-- == 与三进制 ISA 的对应（纲领 §3 层 1）
--
-- 6-trit 寄存器 = GF(3⁶) 机器字；emb9/emb27 即「2-trit GF(9) 通道」与
-- 「3-trit GF(27) 通道」的语义映射；子域驻留指令（GF36.subfield1/2/3）
-- 是类型判别器。
module Sovereign.Algebra.FieldTower.Embed36 where

open import Data.Bool
  using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; _∷_; []; map; concatMap; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
         ⊕-identityˡ; ⊕-identityʳ; ⊕-assoc; ⊕-comm; ⊗-distribˡ-⊕;
         ⊗-zeroˡ; ⊗-identityˡ)
open import Sovereign.Algebra.FieldTower.GF9
  using (GF9; _+gf9_; _*gf9_; gf9-one; alpha; embed-gf3; galoisConjugate)
open import Sovereign.Algebra.FieldTower.GF27
  using (GF27; gf27-zero; gf27-one; alpha-sq; frobenius; _+gf27_; _*gf27_)
open import Sovereign.Algebra.FieldTower.GF36
  using (GF36; frobenius36; gf36-zero; gf36-one; embed-gf3-gf36;
         _+gf36_; _*gf36_; _==³⁶_; _==ᵗ⁶_; subfield2; subfield3; beta36; gamma36)
open import Sovereign.Algebra.FieldTower.Intercept using (all27; _==ᵗ_; _==²⁷_)

--------------------------------------------------------------------------------
-- §1. 坐标级嵌入定义（v2）
--
-- B = beta36 = (T₀,T₁,T₂,T₁,T₁,T₀)；G = gamma36 = (T₀,T₀,T₁,T₂,T₁,T₀)；
-- G² = G *gf36 G = (T₀,T₁,T₀,T₂,T₁,T₁)。
-- emb9/emb27 为「embed a +f36 B·embed b」形的逐分量归约闭式：
--   · T₁ ⊗ b 定义性归约为 b（⊗-identityˡ 子句）；
--   · T₀ ⊗ b 定义性归约为 T₀（⊗-zeroˡ 子句）；
--   · 唯一非线性项是 T₂ ⊗ b（G² 的常量坐标结构已并入闭式）。
--------------------------------------------------------------------------------

emb9 : GF9 → GF36
emb9 (a , b) = a , b , (T₂ ⊗ b) , b , b , T₀

emb27 : GF27 → GF36
emb27 (a , b , c) =
  a , c , b , ((T₂ ⊗ b) ⊕ (T₂ ⊗ c)) , (b ⊕ c) , c

--------------------------------------------------------------------------------
-- §1b. 枚举辅助
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
-- §2. 单位元 / 命名对应（定义自洽）
--------------------------------------------------------------------------------

pin-emb9-alpha : emb9 alpha ≡ beta36
pin-emb9-alpha = refl

pin-emb27-alpha : emb27 (T₀ , T₁ , T₀) ≡ gamma36
pin-emb27-alpha = refl

pin-emb9-one : emb9 gf9-one ≡ gf36-one
pin-emb9-one = refl

pin-emb27-one : emb27 gf27-one ≡ gf36-one
pin-emb27-one = refl

pin-emb27-alpha-sq : emb27 alpha-sq ≡ gamma36 *gf36 gamma36
pin-emb27-alpha-sq = refl

--------------------------------------------------------------------------------
-- §3. 标量乘引理（结构证明：闭 B/G，t 全枚举 3-case）
--
-- B/G 坐标为闭项，故域乘的每一分量对坐标级标量场闭式可完全归约：
-- *gf36 公式的交叉项全 ⊗T₀ 消失、无 θ⁶ 约化项。
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
-- §3b. ⊕ 四项重组引理 与 六分量 cong 助手（加法结构证明的工作马）
--------------------------------------------------------------------------------

sum4-swap : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
sum4-swap a b c d =
  trans (⊕-assoc a b (c ⊕ d))
  (trans (cong (a ⊕_) (sym (⊕-assoc b c d)))
  (trans (cong (a ⊕_) (cong (λ w → w ⊕ d) (⊕-comm b c)))
  (trans (cong (a ⊕_) (⊕-assoc c b d))
         (sym (⊕-assoc a c (b ⊕ d))))))

cong-6 : ∀ {A : Set} {x₀ y₀ x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ : A}
  → x₀ ≡ y₀ → x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ → x₅ ≡ y₅
  → (x₀ , x₁ , x₂ , x₃ , x₄ , x₅) ≡ (y₀ , y₁ , y₂ , y₃ , y₄ , y₅)
cong-6 refl refl refl refl refl refl = refl

--------------------------------------------------------------------------------
-- §4. 加法同态（结构证明：v2 升格）
--
-- emb9：coord0/1/3/4/5 定义性（refl），coord2 = ⊗-distribˡ-⊕ T₂ b d。
-- emb27：coord0/1/2/5 定义性，coord3 = 两次 ⊗-distribˡ-⊕ + sum4-swap，
--        coord4 = sum4-swap。
-- 枚举 pin（81/729 对）保留为交叉校验。
--------------------------------------------------------------------------------

emb9-add : ∀ a b c d →
  emb9 ((a ⊕ c) , (b ⊕ d)) ≡ emb9 (a , b) +gf36 emb9 (c , d)
emb9-add a b c d = cong-6 refl refl (⊗-distribˡ-⊕ T₂ b d) refl refl refl

emb27-add : ∀ a b c d e f →
  emb27 ((a ⊕ d) , (b ⊕ e) , (c ⊕ f))
  ≡ emb27 (a , b , c) +gf36 emb27 (d , e , f)
emb27-add a b c d e f = cong-6
  refl
  refl
  refl
  (trans (cong (λ w → w ⊕ (T₂ ⊗ (c ⊕ f))) (⊗-distribˡ-⊕ T₂ b e))
  (trans (cong (λ w → ((T₂ ⊗ b) ⊕ (T₂ ⊗ e)) ⊕ w) (⊗-distribˡ-⊕ T₂ c f))
         (sum4-swap (T₂ ⊗ b) (T₂ ⊗ e) (T₂ ⊗ c) (T₂ ⊗ f))))
  (sum4-swap b e c f)
  refl

pin-emb9-add : length (keepEmb (λ p ->
  emb9 (proj₁ p +gf9 proj₂ p) ==³⁶ (emb9 (proj₁ p) +gf36 emb9 (proj₂ p))) pairs9) ≡ 81
pin-emb9-add = refl

pin-emb27-add : length (keepEmb (λ p ->
  emb27 (proj₁ p +gf27 proj₂ p) ==³⁶
  (emb27 (proj₁ p) +gf36 emb27 (proj₂ p))) pairs27) ≡ 729
pin-emb27-add = refl

--------------------------------------------------------------------------------
-- §5. 乘法同态（构造子全 case 归约：3⁴ = 81 / 3⁶ = 729 子句）
--
-- 证明体在 `Embed36MulClauses.agda`（生成文件）：
--   open import ...Embed36MulClauses 即得 emb9-mul / emb27-mul。
-- 枚举 pin（下两枚）保留为交叉校验。
--------------------------------------------------------------------------------

pin-emb9-mul : length (keepEmb (λ p ->
  emb9 (proj₁ p *gf9 proj₂ p) ==³⁶ (emb9 (proj₁ p) *gf36 emb9 (proj₂ p))) pairs9) ≡ 81
pin-emb9-mul = refl

pin-emb27-mul : length (keepEmb (λ p ->
  emb27 (proj₁ p *gf27 proj₂ p) ==³⁶ (emb27 (proj₁ p) *gf36 emb27 (proj₂ p))) pairs27) ≡ 729
pin-emb27-mul = refl

--------------------------------------------------------------------------------
-- §6. Frobenius 相容（全枚举：9 / 27 对）
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
-- §7. 像 ⊆ σ^(6/d)-不动子域（全枚举）
--------------------------------------------------------------------------------

pin-emb9-image-fixed : length (keepEmb (λ x → subfield2 (emb9 x)) all9) ≡ 9
pin-emb9-image-fixed = refl

pin-emb27-image-fixed : length (keepEmb (λ x → subfield3 (emb27 x)) all27) ≡ 27
pin-emb27-image-fixed = refl

--------------------------------------------------------------------------------
-- §8. 单射（全枚举：x ≠ y ⇒ emb x ≠ emb y，计数 0 反例）
--------------------------------------------------------------------------------

pin-emb9-injective : length (keepEmb (λ p ->
  not (proj₁ p ==⁹ proj₂ p) ∧ (emb9 (proj₁ p) ==³⁶ emb9 (proj₂ p))) pairs9) ≡ 0
pin-emb9-injective = refl

pin-emb27-injective : length (keepEmb (λ p ->
  not (proj₁ p ==²⁷ proj₂ p) ∧ (emb27 (proj₁ p) ==³⁶ emb27 (proj₂ p))) pairs27) ≡ 0
pin-emb27-injective = refl

--------------------------------------------------------------------------------
-- §9. 计数收束（头注重述）
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
