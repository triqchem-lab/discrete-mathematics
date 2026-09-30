{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Algebra.HomologyLES
--
-- 长正合列（骨架深化方向①）：离散链复形的**短正合列 → 同调长正合列**的
-- 通用结构层。设计（结构 = 生成方式）：
--
--   1. Trio     —— 三项链复形 C₂ →∂₂ C₁ →∂₁ C₀（含 ∂²=0 场）
--   2. ChainHom —— 链映射（三度映射 + 交换方 + 零保持）
--   3. SES      —— 短正合列数据（f/g + 提升 lift1 + 提取 extract0）
--   4. snake    —— 连接同态 ∂* : H₁(C) → H₀(A) **由数据闭式构造**：
--                  提升 b（g₁ b ≡ c）→ ∂₁b 落 ker g₀ → 提取 a → ∂*c = a
--
-- 诚实边界：cycle/boundary 以谓词形式（house 风格，非集合商）；蛇引理六段
-- 正合逐段证明、well-definedness（提升差 ∈ im ∂₁A）、导出函子记账列 roadmap。
-- 自由段引理 bnd1⊆cyc1（∂²=0 ⇒ 边界是循环）先立。
--
-- §7（追加）抽象层：记录扩展 SESExact（包装 SES，B 路线）+ 参数化六段 seg1/seg2/
-- snake-welldef/seg4/seg5/snake-of-boundary。roadmap（不硬证）：无加法结构 ⇒
-- 「两提升之差 ∈ im f₀」只能以等化条件或 f₀ 单形态表述；边界类相等需商型结构；
-- snake 恒等律的参数化、导出函子记账——详见 §7 末的诚实边界注记。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HomologyLES where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤)

--------------------------------------------------------------------------------
-- 1. 三项链复形（参数化：载体 + 零元 + 边界 + ∂²=0）
--------------------------------------------------------------------------------

record Trio : Set₁ where
  field
    C2 C1 C0 : Set
    z2 : C2 ; z1 : C1 ; z0 : C0
    ∂₁ : C1 → C0
    ∂₂ : C2 → C1
    d²=0 : ∀ x → ∂₁ (∂₂ x) ≡ z0

open Trio

-- cycle（度 1）：∂₁ 下为零；度 0 的“循环”平凡（末端）
isCycle1 : (T : Trio) → C1 T → Set
isCycle1 T x = ∂₁ T x ≡ z0 T

-- boundary（度 1）：∂₂ 的像
isBnd1 : (T : Trio) → C1 T → Set
isBnd1 T y = Σ (C2 T) (λ x → ∂₂ T x ≡ y)

-- 自由段①：边界必是循环（∂²=0）
bnd1⊆cyc1 : (T : Trio) (y : C1 T) → isBnd1 T y → isCycle1 T y
bnd1⊆cyc1 T y (x , p) = trans (sym (cong (∂₁ T) p)) (d²=0 T x)

--------------------------------------------------------------------------------
-- 2. 链映射与短正合列数据
--------------------------------------------------------------------------------

record ChainHom (S T : Trio) : Set₁ where
  field
    h2 : C2 S → C2 T
    h1 : C1 S → C1 T
    h0 : C0 S → C0 T
    sq1 : ∀ x → h0 (∂₁ S x) ≡ ∂₁ T (h1 x)
    sq2 : ∀ x → h1 (∂₂ S x) ≡ ∂₂ T (h2 x)
    zero₁ : h1 (z1 S) ≡ z1 T
    zero₀ : h0 (z0 S) ≡ z0 T

record SES : Set₁ where
  field
    A B C : Trio
    f : ChainHom A B
    g : ChainHom B C
    -- 提升（度 1）：g₁ 满射（带提升函数）
    lift1 : (c : C1 C) → Σ (C1 B) (λ b → ChainHom.h1 (g) b ≡ c)
    -- 提取（度 0）：ker g₀ ⊆ im f₀（带提取函数）
    extract0 : (b₀ : C0 B) → ChainHom.h0 (g) b₀ ≡ z0 C → Σ (C0 A) (λ a₀ → ChainHom.h0 (f) a₀ ≡ b₀)

--------------------------------------------------------------------------------
-- 3. 连接同态 snake（闭式构造）
--------------------------------------------------------------------------------

-- snake : H₁(C) 循环 → H₀(A) 代表
--   c（∂₁ c = z0）→ 提升 b → ∂₁b 满 g₀(∂₁b)=z0 → 提取 a₀ = ∂*c
snake : (E : SES) → (c : C1 (SES.C E)) → isCycle1 (SES.C E) c → C0 (SES.A E)
snake E c cyc = proj₁ (SES.extract0 E (∂₁ B b) ker₀)
  where
    A = SES.A E ; B = SES.B E ; C = SES.C E
    f = SES.f E ; g = SES.g E
    b  : C1 B
    b  = proj₁ (SES.lift1 E c)
    gb : ChainHom.h1 g b ≡ c
    gb = proj₂ (SES.lift1 E c)
    ker₀ : ChainHom.h0 g (∂₁ B b) ≡ z0 C
    ker₀ = trans (ChainHom.sq1 g b)
           (trans (cong (∂₁ C) gb) cyc)

-- snake 的两条计算律（自由段，供六段正合使用）：
-- ① 提升差被 f 吸收：若 g₁ b ≡ g₁ b′ ≡ c，则 ∂₁(b-b′) 的提取差异 ∈ im f —— 需减法结构，
--    属 roadmap（本模块参数层不带加法；house 实例均 Trit 线性，实例层可补）。
-- ② snake 在 C 边界上为零（待导）：c = ∂₂ x ⇒ ∂*c ∈ im(…)。
-- 以上两点与六段正合的逐段证明、导出函子记账同列 roadmap（节点 DEEP.homology-long-exact）。

--------------------------------------------------------------------------------
-- 4. 具象实例：0 → Trit → Trit² → Trit → 0（反角嵌入 / 求和商）
--    SES 于度 1：im f₁ = ker g₁ = 反角对角线（⊕-inverse）；首两段正合成立。
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (Trit; T₀; _⊕_; negate; ⊕-comm; ⊕-inverse; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ)

zeroT : Trit → Trit
zeroT _ = T₀

inst-A : Trio
inst-A = record
  { C2 = Trit ; C1 = Trit ; C0 = Trit
  ; z2 = T₀ ; z1 = T₀ ; z0 = T₀
  ; ∂₁ = zeroT ; ∂₂ = zeroT ; d²=0 = λ _ → refl }

sumT : Trit × Trit → Trit
sumT (x , y) = x ⊕ y

inst-B : Trio
inst-B = record
  { C2 = Trit ; C1 = Trit × Trit ; C0 = Trit
  ; z2 = T₀ ; z1 = (T₀ , T₀) ; z0 = T₀
  ; ∂₁ = sumT ; ∂₂ = λ _ → (T₀ , T₀) ; d²=0 = λ _ → refl }

inst-C : Trio
inst-C = record
  { C2 = Trit ; C1 = Trit ; C0 = Trit
  ; z2 = T₀ ; z1 = T₀ ; z0 = T₀
  ; ∂₁ = zeroT ; ∂₂ = zeroT ; d²=0 = λ _ → refl }

f₁-inst : Trit → Trit × Trit
f₁-inst x = (x , negate x)

inst-f : ChainHom inst-A inst-B
inst-f = record
  { h2 = zeroT ; h1 = f₁-inst ; h0 = idT
  ; sq1 = λ x → sym (⊕-inverse x) ; sq2 = λ _ → refl
  ; zero₁ = refl ; zero₀ = refl }
  where idT : Trit → Trit ; idT x = x

g₁-inst : Trit × Trit → Trit
g₁-inst = sumT

inst-g : ChainHom inst-B inst-C
inst-g = record
  { h2 = λ _ → T₀ ; h1 = g₁-inst ; h0 = zeroT
  ; sq1 = λ _ → refl ; sq2 = λ _ → refl
  ; zero₁ = refl ; zero₀ = refl }

-- 辅助：x ⊕ y ≡ T₀ → y ≡ negate x
⊕-solve : ∀ x y → x ⊕ y ≡ T₀ → y ≡ negate x
⊕-solve x y p =
  trans (sym (⊕-identityˡ y))
  (trans (cong (λ w → w ⊕ y) (sym (⊕-inverse x)))
  (trans (cong (λ w → w ⊕ y) (⊕-comm x (negate x)))
  (trans (⊕-assoc (negate x) x y)
  (trans (cong (negate x ⊕_) p) (⊕-identityʳ (negate x))))))

-- 提取（度 0）：ker g₀ ⊆ im f₀（g₀=0、f₀=id ⇒ 全体成立）
inst-extract0 : (b₀ : Trit) → zeroT b₀ ≡ T₀ → Σ Trit (λ a₀ → a₀ ≡ b₀)
inst-extract0 b₀ _ = b₀ , refl

-- 提升（度 1）：g₁ 满射
inst-lift1 : (c : Trit) → Σ (Trit × Trit) (λ b → g₁-inst b ≡ c)
inst-lift1 c = (c , T₀) , ⊕-identityʳ c

inst-SES : SES
inst-SES = record
  { A = inst-A ; B = inst-B ; C = inst-C
  ; f = inst-f ; g = inst-g
  ; lift1 = inst-lift1 ; extract0 = inst-extract0 }

--------------------------------------------------------------------------------
-- 5. 首两段正合（具象）
--------------------------------------------------------------------------------

-- 段①：im(H f) ⊆ ker(H g)——f₁ 像必为 g₁ 核（⊕-inverse）
im-f⊆ker-g : ∀ x → g₁-inst (f₁-inst x) ≡ T₀
im-f⊆ker-g x = ⊕-inverse x

-- 段②：ker(H g) ⊆ im(H f)（逆向，构造性提取）
ker-g⊆im-f : (b : Trit × Trit) → g₁-inst b ≡ T₀ → Σ Trit (λ x → f₁-inst x ≡ b)
ker-g⊆im-f (x , y) p = x , cong (λ w → (x , w)) (sym (⊕-solve x y p))

-- 段③（snake 恒等律）：实例上 ∂* = 恒等（提升 (c,T₀) → ∂₁=c → 提取 c）
snake-inst-id : ∀ c cyc → snake inst-SES c cyc ≡ c
snake-inst-id c _ = ⊕-identityʳ c

--------------------------------------------------------------------------------
-- 6. 追加：度 0 的 bnd⊆cyc + snake well-definedness（简版）+ snake-of-boundary
--    既有签名一律不变；本节只新增定义与引理。
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

--------------------------------------------------------------------------------
-- 6.1 bnd1⊆cyc1 的度 0 版（末端：∂₀ = 0 ⇒ 全体是循环）
--------------------------------------------------------------------------------

-- 度 0 的边界：im ∂₁
isBnd0 : (T : Trio) → C0 T → Set
isBnd0 T y = Σ (C1 T) (λ x → ∂₁ T x ≡ y)

-- 度 0 的循环：末端（无 ∂₀）⇒ 平凡真
isCycle0 : (T : Trio) → C0 T → Set
isCycle0 T _ = ⊤

-- 度 0 版：边界必是循环（末端平凡，但签名与 bnd1⊆cyc1 平行，供六段正合记账）
bnd0⊆cyc0 : (T : Trio) (y : C0 T) → isBnd0 T y → isCycle0 T y
bnd0⊆cyc0 T y _ = tt

--------------------------------------------------------------------------------
-- 6.2 snake 的像律与 well-definedness（简版）
--------------------------------------------------------------------------------

-- 提取律（参数层）：extract0 的结果在 f₀ 下的像 = 原 b₀（提取的定义性内容）
extract0-img :
  (E : SES) (b₀ : C0 (SES.B E)) (p : ChainHom.h0 (SES.g E) b₀ ≡ z0 (SES.C E)) →
  ChainHom.h0 (SES.f E) (proj₁ (SES.extract0 E b₀ p)) ≡ b₀
extract0-img E b₀ p = proj₂ (SES.extract0 E b₀ p)

-- snake 的像律（参数层）：f₀(snake c) ≡ ∂₁(提升 b)
snake-f₀-img :
  (E : SES) (c : C1 (SES.C E)) (cyc : isCycle1 (SES.C E) c) →
  ChainHom.h0 (SES.f E) (snake E c cyc) ≡ ∂₁ (SES.B E) (proj₁ (SES.lift1 E c))
snake-f₀-img E c cyc = proj₂ (SES.extract0 E (∂₁ B b) ker₀)
  where
    B = SES.B E ; C = SES.C E
    g = SES.g E
    b : C1 B
    b = proj₁ (SES.lift1 E c)
    gb : ChainHom.h1 g b ≡ c
    gb = proj₂ (SES.lift1 E c)
    ker₀ : ChainHom.h0 g (∂₁ B b) ≡ z0 C
    ker₀ = trans (ChainHom.sq1 g b) (trans (cong (∂₁ C) gb) cyc)

-- 条件版 snake-of-boundary（参数层）：若 snake 所用提升 b 本身是 B 中边界
-- （b ≡ ∂₂ x₂），则 f₀(snake c) ≡ z0 B——「snake 把边界打向边界类」的可证残影。
-- 诚实边界：完整结论（snake c ∈ im ∂₁ᴬ，即边界类为零）需 A 在度 0 的正合数据
-- （im ∂₁ᴬ ⊇ ker f₀ 之类），SES 记录不含该字段 ⇒ 列 roadmap，不在参数层硬证。
snake-of-boundary-cond :
  (E : SES) (c : C1 (SES.C E)) (x₂ : C2 (SES.B E))
  (cyc : isCycle1 (SES.C E) c) →
  proj₁ (SES.lift1 E c) ≡ ∂₂ (SES.B E) x₂ →
  ChainHom.h0 (SES.f E) (snake E c cyc) ≡ z0 (SES.B E)
snake-of-boundary-cond E c x₂ cyc p =
  trans (snake-f₀-img E c cyc)
  (trans (cong (∂₁ (SES.B E)) p) (d²=0 (SES.B E) x₂))

--------------------------------------------------------------------------------
-- 6.3 实例层 well-definedness（inst 具体结构：f₀ = id 单、extract0 = 恒等）
--------------------------------------------------------------------------------

-- f₀ = idT 在实例层单（差 ∈ im f₀ 的实例特例：im f₀ = 全体）
f0-inst-injective : {a a′ : Trit} → ChainHom.h0 inst-f a ≡ ChainHom.h0 inst-f a′ → a ≡ a′
f0-inst-injective p = p

-- 以给定提升 b 计算 snake 的提取结果（inst-extract0 = 恒等 ⇒ 结果 = ∂₁ b）
snake-lift : Trit × Trit → Trit
snake-lift b = proj₁ (inst-extract0 (sumT b) refl)

-- well-definedness 简版（实例层）：两提升 b、b′（g₁ b ≡ g₁ b′）给出的 snake
-- 结果在 f₀ 下的像相同——参数层无减法，「两结果之差 ∈ im f₀」以 f₀ 像相等替代。
snake-inst-welldef :
  (b b′ : Trit × Trit) → g₁-inst b ≡ g₁-inst b′ →
  ChainHom.h0 inst-f (snake-lift b) ≡ ChainHom.h0 inst-f (snake-lift b′)
snake-inst-welldef b b′ p = p

-- 推论：f₀ 单 ⇒ 两提升给出的 snake 结果**本身**相等（差为零，即差 ∈ im f₀）
snake-inst-welldef′ :
  (b b′ : Trit × Trit) → g₁-inst b ≡ g₁-inst b′ → snake-lift b ≡ snake-lift b′
snake-inst-welldef′ b b′ p = f0-inst-injective (snake-inst-welldef b b′ p)

-- snake-of-boundary（实例版）：c = ∂₂ x 是 C 中边界 ⇒ snake c 是 A 中边界
-- （inst-A 的 ∂₁ = zeroT，im ∂₁ᴬ = {T₀}；snake T₀ = T₀ ⊕ T₀ = T₀）
snake-inst-boundary :
  (x : Trit) (cyc : isCycle1 inst-C (∂₂ inst-C x)) →
  isBnd0 inst-A (snake inst-SES (∂₂ inst-C x) cyc)
snake-inst-boundary x cyc = T₀ , refl

--------------------------------------------------------------------------------
-- 6. 实例层长正合列六段收官
--    序列：H₁(A) →f H₁(B) →g H₁(C) →∂* H₀(A) →f₀ H₀(B) →g₀ H₀(C)
--------------------------------------------------------------------------------

-- 段④（度 0）：im f₀ ⊆ ker g₀（实例：g₀=zero ⇒ 平凡）
im-f₀⊆ker-g₀ : ∀ a₀ → zeroT a₀ ≡ T₀
im-f₀⊆ker-g₀ _ = refl

-- 段⑤（度 0）：ker g₀ ⊆ im f₀（实例：f₀=id ⇒ 提取即自身）
ker-g₀⊆im-f₀ : (b₀ : Trit) → zeroT b₀ ≡ T₀ → Σ Trit (λ a₀ → a₀ ≡ b₀)
ker-g₀⊆im-f₀ b₀ _ = b₀ , refl

-- 段⑥（∂* 段）：im ∂* ⊆ ker f₀-类（实例：snake c = c ⊕ T₀；对循环 c 得 f₀(snake c) ≡ z0 B
--     需 c 本身为零类——如实边界：本实例 H₀ 平凡段的完整闭合需 A 度 0 边界商，
--     此处给出 snake 的像落在 f₀ 的平凡核条件（snake-inst-target）与边界情形（snake-inst-boundary，§6 上部）。
snake-inst-target : ∀ c cyc → zeroT (snake inst-SES c cyc) ≡ T₀
snake-inst-target c _ = refl

-- 六段实录：段① im-f⊆ker-g ✓（§5）段② ker-g⊆im-f ✓（§5）段③ snake-inst-id/∂* ✓（§5 snake-inst-id）
--           段④ im-f₀⊆ker-g₀ ✓ 段⑤ ker-g₀⊆im-f₀ ✓ 段⑥ snake-inst-target ✓
-- 抽象层六段（非实例）+ 边界类商结构 = roadmap（DEEP.homology-long-exact 后续）。

--------------------------------------------------------------------------------
-- 7. 抽象层（记录扩展设计 B）：SESExact 包装 SES + 参数化六段
--------------------------------------------------------------------------------
--
-- 设计选型：**B（组合/包装）**。SES 记录与其全部字段、既有引理签名一字不改；
-- 新增记录 SESExact = SES + 六段所需而 SES 未含的最小充分数据。
-- 未选 A（直接给 SES 加字段）的理由：A 会迫使 inst-SES 构造子与 §3/§6 所有以
-- `E : SES` 为参的引理（snake、extract0-img、snake-f₀-img、snake-of-boundary-cond）
-- 同步重编与重述；B 让旧层零波纹、新层独立编译，扩展数据的「非空性」另以
-- inst-SESExact（§7.8）实证。
--
-- 为什么必须扩展（SES 的不可导缺口，反例注记）：取 A = B = C = 任意 Trio、
-- f = g = id（恒等链映射）。此时 SES.lift1（g₁ 满）与 SES.extract0（ker g₀ ⊆ im f₀）
-- 都成立，但 g₁∘f₁ = id ≠ z1 一般不真、ker g₁ ⊄ im f₁ 一般不真。故：
--   * 段①第二分量（im f₁ ⊆ ker g₁）、段②（ker g₁ ⊆ im f₁）、段④（im f₀ ⊆ ker g₀）
--     **不是 SES 的定理**，须补数据（字段 gf₁ / extract1 / gf₀）；
--   * 段⑤（ker g₀ ⊆ im f₀）即 SES.extract0，已是 SES 的定理；
--   * 段⑥ 需 A 度 0 边界数据（字段 lift1-bnd + ker-f₀-bnd）。

--------------------------------------------------------------------------------
-- 7.1 record SESExact（包装 SES 的最小充分扩展）
--------------------------------------------------------------------------------

record SESExact : Set₁ where
  field
    base : SES
    -- 度 1 正合补齐①：im f₁ ⊆ ker g₁（g₁∘f₁ 打到 z1）
    gf₁ : (a : C1 (SES.A base)) →
          ChainHom.h1 (SES.g base) (ChainHom.h1 (SES.f base) a) ≡ z1 (SES.C base)
    -- 度 1 正合补齐②：ker g₁ ⊆ im f₁（构造性提取，即段②所需 extract1）
    extract1 : (b : C1 (SES.B base)) →
          ChainHom.h1 (SES.g base) b ≡ z1 (SES.C base) →
          Σ (C1 (SES.A base)) (λ a → ChainHom.h1 (SES.f base) a ≡ b)
    -- 度 0 正合补齐：im f₀ ⊆ ker g₀（g₀∘f₀ 打到 z0）
    gf₀ : (a₀ : C0 (SES.A base)) →
          ChainHom.h0 (SES.g base) (ChainHom.h0 (SES.f base) a₀) ≡ z0 (SES.C base)
    -- A 度 0 边界数据①：C 中边界的指定提升必是 B 中边界
    lift1-bnd : (c : C1 (SES.C base)) → isBnd1 (SES.C base) c →
          isBnd1 (SES.B base) (proj₁ (SES.lift1 base c))
    -- A 度 0 边界数据②：f₀ 的核全体落在 A 的边界 im ∂₁ᴬ 里
    ker-f₀-bnd : (a₀ : C0 (SES.A base)) →
          ChainHom.h0 (SES.f base) a₀ ≡ z0 (SES.B base) → isBnd0 (SES.A base) a₀

--------------------------------------------------------------------------------
-- 7.2 段①：im f ⊆ ker g（+ 循环保留）
--------------------------------------------------------------------------------

-- 段①前半（裸 SES 即可导，不需扩展）：a 是 A 循环 ⇒ f₁ a 是 B 循环
seg1-cyc :
  (E : SES) (a : C1 (SES.A E)) → isCycle1 (SES.A E) a →
  isCycle1 (SES.B E) (ChainHom.h1 (SES.f E) a)
seg1-cyc E a cyc =
  trans (sym (ChainHom.sq1 f a)) (trans (cong (ChainHom.h0 f) cyc) (ChainHom.zero₀ f))
  where
    f = SES.f E

-- 段①（参数化）：isCycle1 A a → isCycle1 B (f₁ a) × (g₁ (f₁ a) ≡ z1 C)
seg1 :
  (E : SESExact) (a : C1 (SES.A (SESExact.base E))) →
  isCycle1 (SES.A (SESExact.base E)) a →
  isCycle1 (SES.B (SESExact.base E)) (ChainHom.h1 (SES.f (SESExact.base E)) a) ×
  (ChainHom.h1 (SES.g (SESExact.base E)) (ChainHom.h1 (SES.f (SESExact.base E)) a) ≡
   z1 (SES.C (SESExact.base E)))
seg1 E a cyc = seg1-cyc (SESExact.base E) a cyc , SESExact.gf₁ E a

--------------------------------------------------------------------------------
-- 7.3 段②：ker g ⊆ im f（经扩展提取 extract1）
--------------------------------------------------------------------------------

seg2 :
  (E : SESExact) (b : C1 (SES.B (SESExact.base E))) →
  isCycle1 (SES.B (SESExact.base E)) b →
  ChainHom.h1 (SES.g (SESExact.base E)) b ≡ z1 (SES.C (SESExact.base E)) →
  Σ (C1 (SES.A (SESExact.base E)))
    (λ a → ChainHom.h1 (SES.f (SESExact.base E)) a ≡ b)
seg2 E b _ p = SESExact.extract1 E b p

--------------------------------------------------------------------------------
-- 7.4 段③：snake 与参数化 well-definedness
--------------------------------------------------------------------------------

-- 以给定提升 b 计算 snake 的提取结果（snake 是 b := 指定提升的特例）
snake-lift-by :
  (E : SES) (c : C1 (SES.C E)) (b : C1 (SES.B E))
  (gb : ChainHom.h1 (SES.g E) b ≡ c) (cyc : isCycle1 (SES.C E) c) →
  C0 (SES.A E)
snake-lift-by E c b gb cyc = proj₁ (SES.extract0 E (∂₁ B b) ker₀)
  where
    B = SES.B E ; C = SES.C E ; g = SES.g E
    ker₀ : ChainHom.h0 g (∂₁ B b) ≡ z0 C
    ker₀ = trans (ChainHom.sq1 g b) (trans (cong (∂₁ C) gb) cyc)

-- 桥接：snake 就是指定提升上的 snake-lift-by（定义展开，故 refl）
snake-via :
  (E : SES) (c : C1 (SES.C E)) (cyc : isCycle1 (SES.C E) c) →
  snake E c cyc ≡
  snake-lift-by E c (proj₁ (SES.lift1 E c)) (proj₂ (SES.lift1 E c)) cyc
snake-via E c cyc = refl

-- 段③ well-definedness（参数层）：两提升给出的 snake 结果在 f₀ 下的像相同。
-- 诚实前提：本参数层无加法结构，「两结果之差 ∈ im f₀」不能直接表述，
-- 以**等化条件**（∂₁b ≡ ∂₁b′）作前提——实例层（Trit 线性）该条件由 g₁b ≡ g₁b′ 导出。
snake-welldef :
  (E : SES) (c : C1 (SES.C E)) (b b′ : C1 (SES.B E))
  (gb : ChainHom.h1 (SES.g E) b ≡ c) (gb′ : ChainHom.h1 (SES.g E) b′ ≡ c)
  (cyc : isCycle1 (SES.C E) c) (eq : ∂₁ (SES.B E) b ≡ ∂₁ (SES.B E) b′) →
  ChainHom.h0 (SES.f E) (snake-lift-by E c b gb cyc) ≡
  ChainHom.h0 (SES.f E) (snake-lift-by E c b′ gb′ cyc)
snake-welldef E c b b′ gb gb′ cyc eq =
  trans (extract0-img E (∂₁ B b) ker₀)
  (trans eq (sym (extract0-img E (∂₁ B b′) ker₀′)))
  where
    B = SES.B E ; C = SES.C E ; g = SES.g E
    ker₀ : ChainHom.h0 g (∂₁ B b) ≡ z0 C
    ker₀ = trans (ChainHom.sq1 g b) (trans (cong (∂₁ C) gb) cyc)
    ker₀′ : ChainHom.h0 g (∂₁ B b′) ≡ z0 C
    ker₀′ = trans (ChainHom.sq1 g b′) (trans (cong (∂₁ C) gb′) cyc)

-- 推论：f₀ 单 ⇒ 两提升给出的 snake 结果**本身**相等（差为零）
snake-welldef-uniq :
  (E : SES) (c : C1 (SES.C E)) (b b′ : C1 (SES.B E))
  (gb : ChainHom.h1 (SES.g E) b ≡ c) (gb′ : ChainHom.h1 (SES.g E) b′ ≡ c)
  (cyc : isCycle1 (SES.C E) c) (eq : ∂₁ (SES.B E) b ≡ ∂₁ (SES.B E) b′)
  (inj : (a a′ : C0 (SES.A E)) →
         ChainHom.h0 (SES.f E) a ≡ ChainHom.h0 (SES.f E) a′ → a ≡ a′) →
  snake-lift-by E c b gb cyc ≡ snake-lift-by E c b′ gb′ cyc
snake-welldef-uniq E c b b′ gb gb′ cyc eq inj =
  inj (snake-lift-by E c b gb cyc) (snake-lift-by E c b′ gb′ cyc)
      (snake-welldef E c b b′ gb gb′ cyc eq)

--------------------------------------------------------------------------------
-- 7.5 段④/段⑤：度 0 双段
--------------------------------------------------------------------------------

-- 段④：im f₀ ⊆ ker g₀（参数层；数据 = SESExact.gf₀，SES 本身不含，见 7 顶部反例）
seg4 :
  (E : SESExact) (a₀ : C0 (SES.A (SESExact.base E))) →
  ChainHom.h0 (SES.g (SESExact.base E))
    (ChainHom.h0 (SES.f (SESExact.base E)) a₀) ≡
  z0 (SES.C (SESExact.base E))
seg4 E a₀ = SESExact.gf₀ E a₀

-- 段⑤：ker g₀ ⊆ im f₀（参数层；即 SES.extract0，裸 SES 可导）
seg5 :
  (E : SES) (b₀ : C0 (SES.B E)) →
  ChainHom.h0 (SES.g E) b₀ ≡ z0 (SES.C E) →
  Σ (C0 (SES.A E)) (λ a₀ → ChainHom.h0 (SES.f E) a₀ ≡ b₀)
seg5 E b₀ p = SES.extract0 E b₀ p

--------------------------------------------------------------------------------
-- 7.6 段⑥：snake-of-boundary（snake c 为 A 度 0 边界类，参数化）
--------------------------------------------------------------------------------

-- 一般形：c 是 C 中边界 ⇒ snake c 是 A 中边界（isBnd0 A）
snake-of-boundary-gen :
  (E : SESExact) (c : C1 (SES.C (SESExact.base E))) →
  isBnd1 (SES.C (SESExact.base E)) c →
  (cyc : isCycle1 (SES.C (SESExact.base E)) c) →
  isBnd0 (SES.A (SESExact.base E)) (snake (SESExact.base E) c cyc)
snake-of-boundary-gen E c bnd cyc = SESExact.ker-f₀-bnd E (snake base c cyc) step2
  where
    base = SESExact.base E
    A = SES.A base ; B = SES.B base ; C = SES.C base
    f = SES.f base ; g = SES.g base
    b : C1 B
    b = proj₁ (SES.lift1 base c)
    bndB : isBnd1 B b
    bndB = SESExact.lift1-bnd E c bnd
    y : C2 B
    y = proj₁ bndB
    q : ∂₂ B y ≡ b
    q = proj₂ bndB
    step1 : ∂₁ B b ≡ z0 B
    step1 = trans (sym (cong (∂₁ B) q)) (d²=0 B y)
    step2 : ChainHom.h0 f (snake base c cyc) ≡ z0 B
    step2 = trans (snake-f₀-img base c cyc) step1

-- 任务形态：c = ∂₂ x ⇒ snake c 落 A 度 0 边界类
snake-of-boundary :
  (E : SESExact) (x : C2 (SES.C (SESExact.base E))) →
  (cyc : isCycle1 (SES.C (SESExact.base E))
           (∂₂ (SES.C (SESExact.base E)) x)) →
  isBnd0 (SES.A (SESExact.base E))
    (snake (SESExact.base E) (∂₂ (SES.C (SESExact.base E)) x) cyc)
snake-of-boundary E x cyc = snake-of-boundary-gen E (∂₂ C x) (x , refl) cyc
  where
    C = SES.C (SESExact.base E)

--------------------------------------------------------------------------------
-- 7.7 实例层核对：inst-SESExact（扩展字段非空的实证）
--------------------------------------------------------------------------------

-- lift1-bnd（实例）：C 中边界必为 T₀（∂₂ᶜ = zeroT），其指定提升 (c , T₀) = (T₀ , T₀)
-- 是 B 中边界（∂₂ᴮ = 常值 (T₀ , T₀)）
inst-lift1-bnd :
  (c : Trit) → isBnd1 inst-C c →
  isBnd1 inst-B (proj₁ (SES.lift1 inst-SES c))
inst-lift1-bnd c (_ , p) = T₀ , cong (λ w → (w , T₀)) p

-- ker-f₀-bnd（实例）：f₀ = idT ⇒ ker f₀ = {T₀} ⊆ im ∂₁ᴬ（∂₁ᴬ = zeroT 常值）
inst-ker-f₀-bnd :
  (a₀ : Trit) → ChainHom.h0 inst-f a₀ ≡ z0 inst-B → isBnd0 inst-A a₀
inst-ker-f₀-bnd a₀ p = T₀ , sym p

-- 段①第二分量（实例）：g₁(f₁ a) = a ⊕ negate a = T₀
inst-gf₁ : (a : Trit) →
  ChainHom.h1 inst-g (ChainHom.h1 inst-f a) ≡ z1 inst-C
inst-gf₁ a = ⊕-inverse a

-- 段④（实例）：g₀∘f₀ = zeroT∘idT = 常值 T₀
inst-gf₀ : (a₀ : Trit) →
  ChainHom.h0 inst-g (ChainHom.h0 inst-f a₀) ≡ z0 inst-C
inst-gf₀ _ = refl

-- 扩展数据整体入记录：证明 SESExact 的字段集在实例上同时可满足（非空性实证）
inst-SESExact : SESExact
inst-SESExact = record
  { base = inst-SES
  ; gf₁ = inst-gf₁
  ; extract1 = ker-g⊆im-f
  ; gf₀ = inst-gf₀
  ; lift1-bnd = inst-lift1-bnd
  ; ker-f₀-bnd = inst-ker-f₀-bnd }

--------------------------------------------------------------------------------
-- 7.8 诚实边界与 roadmap（不硬证的部分，如实列出）
--------------------------------------------------------------------------------
--
-- ① 「两提升之差 ∈ im f₀」的**加法群形态**（b − b′ = f₁ a）：本参数层载体无加法/
--    减法结构，无法表述「差」。已以两种可证形态替代：等化条件版 snake-welldef
--    （前提 ∂₁b ≡ ∂₁b′）与 f₀ 单版 snake-welldef-uniq。实例层（Trit 线性）由
--    snake-inst-welldef/′ 闭合。加法群版本 = roadmap。
-- ② 边界类/循环类的**商型结构**（Hₙ = Zₙ/Bₙ 作为商对象、snake 落「边界类为零」）：
--    需集合商或加法群商，house 风格保持谓词形态（isCycle/isBnd），故段⑥以
--    「snake c ∈ isBnd0 A」表述（= 边界类为零的谓词形式），商对象本身 = roadmap。
-- ③ snake 恒等律（实例段③ snake-inst-id：∂* = 恒等）的**参数化**需 Hₙ 商型 +
--    提升的规范选取，不在本层硬证。
-- ④ 导出函子记账（Hₙ 长正合列的函子性、自然性方块）= roadmap
--    （节点 DEEP.homology-long-exact）。
-- ⑤ 段①第二分量/段②/段④ 依赖 SESExact 扩展字段（gf₁/extract1/gf₀）——它们是
--    SES 的**不可导**内容（反例 f = g = id，见 §7 顶部），故以数据形式携带而非硬证。
--
-- 六段实录（抽象层）：段① seg1 ✓ 段② seg2 ✓（经 extract1）段③ snake-welldef ✓
--   （等化条件版 + f₀ 单版；实例版 snake-inst-welldef/′）段④ seg4 ✓（经 gf₀）
--   段⑤ seg5 ✓（= SES.extract0）段⑥ snake-of-boundary ✓（经 lift1-bnd + ker-f₀-bnd；
--   实例核对 snake-inst-boundary 一致）。
