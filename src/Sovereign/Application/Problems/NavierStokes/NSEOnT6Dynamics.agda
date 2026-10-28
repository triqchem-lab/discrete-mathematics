{-# OPTIONS --rewriting #-}

-- | Sovereign.Application.Problems.NavierStokes.NSEOnT6Dynamics
--   —— nsStep⁹ = id 形式化·第一卷：nsStep 线性性（逐点相等传输架构）
--
-- == 定理目标（数值发现 → FML 定理，2026-10-28 seeded 动力学研究）
--
-- NSEOnT6 的 nsStep（v ↦ v +F grad (div v)）在 (Z/3)⁶ 载体上满足
-- **nsStep⁹ = id**：所有轨道周期整除 9，通用轨道最小周期恰 9
-- （40 种子数值验证：最小周期分布 {9: 40}，无一例外）。
--
-- == 证明路线图（本模块按卷推进）
--
--   · 卷一（本模块）：**nsStep 线性性**——逐点相等传输架构：
--       diffF-≈（差分传输）→ grad-≈-pt（grad 分量传输）→
--       vk-grad-add（grad 分量加法）→ nsStep-add-comp（组装）。
--     地基：NSEOnT6 §3 现成的 div-+F（div 加法性）+ diffF-+S（差分线性）。
--   · 卷二（本模块）：**散度流定律** div (nsStep v) x = div v x ⊕ 2·Δ(div v) x：
--       dyn-six-zero（6z ≡ 0）→ dyn-axisLap-3pt（单轴三点展开）→
--       dyn-div-grad（div∘grad 倍增，卷二主引理）→ dyn-flow-law（组装）。
--     地基：NSEOnT6 §4c axisLap-formula（negate² 相消已完成的三点展开）
--     + §2/§3 sum6/sum6-+/cong6'。数值 729/729 已验，本卷给结构证明。
--   · 卷三：lap₃ 零幂性 lap₃² 相关零化链（mod 3）。
--   · 卷四：freshman's dream——(I + GD)⁹ = I + (GD)⁹（C(9,k) ≡ 0，
--     线性性的九步推论）。
--   · 卷五：组装 nsStep⁹ = (I+GD)⁹ = I + (GD)⁹ = I
--     （卷三零幂 + 卷四二项式系数消去）。
--
-- == 逐点相等传输架构（本卷核心技法）
--
-- Trit 的 ⊕/⊗ 顺序匹配对变量卡归约——变量级代数链不可行。正道是把
-- 「两个场逐点相等」作为**假设**传输过算子（diffF/grad/div 都尊重逐点
-- 相等——各自的证明只用 cong₂ 于有限个查看点），再在最终点实例化。
-- 这绕开所有卡归约问题，且与 NSEOnT6 §3 的 ≈ 风格一致。
--
-- 依赖：NSEOnT6（载体/算子/§3 引理 div-+F/diffF-+S）。0 postulate。
module Sovereign.Application.Problems.NavierStokes.NSEOnT6Dynamics where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-identityʳ; ⊕-assoc; ⊕-comm)
open import Sovereign.Application.Problems.NavierStokes.NSEOnT6
  using (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6;
         _+S_; _+F_; diffF; div; grad; nsStep; div-+F; shiftAt; diffF-+S;
         axisLap; axisLap-formula; sum6; sum6-+; cong6')

--------------------------------------------------------------------------------
-- §0. ⊕ 四项重组（工作马；与 Embed36.sum4-swap 同构，独立命名避撞车）
--------------------------------------------------------------------------------

sum4-swap-nse : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
sum4-swap-nse a b c d =
  trans (⊕-assoc a b (c ⊕ d))
  (trans (cong (a ⊕_) (sym (⊕-assoc b c d)))
  (trans (cong (a ⊕_) (cong (λ w → w ⊕ d) (⊕-comm b c)))
  (trans (cong (a ⊕_) (⊕-assoc c b d))
         (sym (⊕-assoc a c (b ⊕ d))))))

--------------------------------------------------------------------------------
-- §1. 差分尊重逐点相等
--------------------------------------------------------------------------------

diffF-≈ : ∀ (f g : ScalarField) → (∀ p → f p ≡ g p)
        → ∀ (i : C3) (x : Torus6) → diffF i f x ≡ diffF i g x
diffF-≈ f g h i x = cong₂ _⊕_ (h (shiftAt i x)) (cong negate (h x))

--------------------------------------------------------------------------------
-- §2. grad 分量尊重逐点相等（参数化于分量投影 vk 与其轴 ax）
--
-- 前置 hvk : vk (grad f) x ≡ diffF ax f x（grad 的 mkField 展开与 vk 投影
-- 互消——对 v1..v6 六例全部定义性 refl）。
--------------------------------------------------------------------------------

grad-≈-pt : ∀ (vk : Field → ScalarField) (ax : C3)
  → (∀ f x → vk (grad f) x ≡ diffF ax f x)
  → ∀ (f g : ScalarField) → (∀ p → f p ≡ g p)
  → ∀ x → vk (grad f) x ≡ vk (grad g) x
grad-≈-pt vk ax hvk f g h x =
  trans (hvk f x)
  (trans (cong₂ _⊕_ (h (shiftAt ax x)) (cong negate (h x)))
         (sym (hvk g x)))

--------------------------------------------------------------------------------
-- §3. grad 分量加法（diffF-+S 的分量化）
--------------------------------------------------------------------------------

grad-comp-add : ∀ (vk : Field → ScalarField) (ax : C3)
  → (∀ f x → vk (grad f) x ≡ diffF ax f x)
  → ∀ (f g : ScalarField) x
  → vk (grad (f +S g)) x ≡ vk (grad f) x ⊕ vk (grad g) x
grad-comp-add vk ax hvk f g x =
  trans (hvk (f +S g) x)
  (trans (diffF-+S ax f g x)
         (cong₂ _⊕_ (sym (hvk f x)) (sym (hvk g x))))

--------------------------------------------------------------------------------
-- §4. nsStep 分量线性性（卷一主定理：六分量实例）
--
-- ⚠ 证明结构说明：通用引理（opaque vk 参数化）原理上不可证——vk 不透明
-- 时 vk (nsStep u) x 无法定义性展开。正道 = 对六个具体投影逐一证明：
-- v1 (nsStep u) x 定义性归约为 v1 u x ⊕ v1 (grad (div u)) x（mkField
-- 展开互消），再经 grad-≈-pt / grad-comp-add / sum4-swap-nse 组装。
--------------------------------------------------------------------------------

nsStep-add-v1 : ∀ v w x → v1 (nsStep (v +F w)) x ≡ v1 (nsStep v) x ⊕ v1 (nsStep w) x
nsStep-add-v1 v w x =
  trans (cong (λ u → (v1 v x ⊕ v1 w x) ⊕ u) step1)
        (sum4-swap-nse (v1 v x) (v1 w x)
                       (v1 (grad (div v)) x) (v1 (grad (div w)) x))
  where
    step1 : v1 (grad (div (v +F w))) x
           ≡ v1 (grad (div v)) x ⊕ v1 (grad (div w)) x
    step1 = trans (grad-≈-pt v1 zero (λ f x → refl)
                                 (div (v +F w)) (div v +S div w) (div-+F v w) x)
                  (grad-comp-add v1 zero (λ f x → refl) (div v) (div w) x)

nsStep-add-v2 : ∀ v w x → v2 (nsStep (v +F w)) x ≡ v2 (nsStep v) x ⊕ v2 (nsStep w) x
nsStep-add-v2 v w x =
  trans (cong (λ u → (v2 v x ⊕ v2 w x) ⊕ u) step1)
        (sum4-swap-nse (v2 v x) (v2 w x)
                       (v2 (grad (div v)) x) (v2 (grad (div w)) x))
  where
    step1 : v2 (grad (div (v +F w))) x
           ≡ v2 (grad (div v)) x ⊕ v2 (grad (div w)) x
    step1 = trans (grad-≈-pt v2 (suc zero) (λ f x → refl)
                                 (div (v +F w)) (div v +S div w) (div-+F v w) x)
                  (grad-comp-add v2 (suc zero) (λ f x → refl) (div v) (div w) x)

nsStep-add-v3 : ∀ v w x → v3 (nsStep (v +F w)) x ≡ v3 (nsStep v) x ⊕ v3 (nsStep w) x
nsStep-add-v3 v w x =
  trans (cong (λ u → (v3 v x ⊕ v3 w x) ⊕ u) step1)
        (sum4-swap-nse (v3 v x) (v3 w x)
                       (v3 (grad (div v)) x) (v3 (grad (div w)) x))
  where
    step1 : v3 (grad (div (v +F w))) x
           ≡ v3 (grad (div v)) x ⊕ v3 (grad (div w)) x
    step1 = trans (grad-≈-pt v3 (suc (suc zero)) (λ f x → refl)
                                 (div (v +F w)) (div v +S div w) (div-+F v w) x)
                  (grad-comp-add v3 (suc (suc zero)) (λ f x → refl) (div v) (div w) x)

nsStep-add-v4 : ∀ v w x → v4 (nsStep (v +F w)) x ≡ v4 (nsStep v) x ⊕ v4 (nsStep w) x
nsStep-add-v4 v w x =
  trans (cong (λ u → (v4 v x ⊕ v4 w x) ⊕ u) step1)
        (sum4-swap-nse (v4 v x) (v4 w x)
                       (v4 (grad (div v)) x) (v4 (grad (div w)) x))
  where
    step1 : v4 (grad (div (v +F w))) x
           ≡ v4 (grad (div v)) x ⊕ v4 (grad (div w)) x
    step1 = trans (grad-≈-pt v4 zero (λ f x → refl)
                                 (div (v +F w)) (div v +S div w) (div-+F v w) x)
                  (grad-comp-add v4 zero (λ f x → refl) (div v) (div w) x)

nsStep-add-v5 : ∀ v w x → v5 (nsStep (v +F w)) x ≡ v5 (nsStep v) x ⊕ v5 (nsStep w) x
nsStep-add-v5 v w x =
  trans (cong (λ u → (v5 v x ⊕ v5 w x) ⊕ u) step1)
        (sum4-swap-nse (v5 v x) (v5 w x)
                       (v5 (grad (div v)) x) (v5 (grad (div w)) x))
  where
    step1 : v5 (grad (div (v +F w))) x
           ≡ v5 (grad (div v)) x ⊕ v5 (grad (div w)) x
    step1 = trans (grad-≈-pt v5 (suc zero) (λ f x → refl)
                                 (div (v +F w)) (div v +S div w) (div-+F v w) x)
                  (grad-comp-add v5 (suc zero) (λ f x → refl) (div v) (div w) x)

nsStep-add-v6 : ∀ v w x → v6 (nsStep (v +F w)) x ≡ v6 (nsStep v) x ⊕ v6 (nsStep w) x
nsStep-add-v6 v w x =
  trans (cong (λ u → (v6 v x ⊕ v6 w x) ⊕ u) step1)
        (sum4-swap-nse (v6 v x) (v6 w x)
                       (v6 (grad (div v)) x) (v6 (grad (div w)) x))
  where
    step1 : v6 (grad (div (v +F w))) x
           ≡ v6 (grad (div v)) x ⊕ v6 (grad (div w)) x
    step1 = trans (grad-≈-pt v6 (suc (suc zero)) (λ f x → refl)
                                 (div (v +F w)) (div v +S div w) (div-+F v w) x)
                  (grad-comp-add v6 (suc (suc zero)) (λ f x → refl) (div v) (div w) x)

--------------------------------------------------------------------------------
-- §5. 卷二 · 基件：六重相同项求和归零（6·z ≡ 0 (mod 3)）
--
-- 口径：全枚举校验（Trit 3-case，各支定义性 refl；与 Trit.agda 环公理同风格）。
--------------------------------------------------------------------------------

dyn-six-zero : ∀ z → sum6 z z z z z z ≡ T₀
dyn-six-zero T₀ = refl
dyn-six-zero T₁ = refl
dyn-six-zero T₂ = refl

--------------------------------------------------------------------------------
-- §6. 卷二 · 单轴二阶差分三点展开（w-优先形式，供 §7 的 sum6-+ 拆分直接咬合）
--
--   axisLap i f x = diffF i (diffF i f) x ≡ f(x+2eᵢ) ⊕ (f(x+eᵢ) ⊕ f x)
--
-- 数学内容：特征 3 下 D² 的三点系数全为 +1（−2 ≡ 1 (mod 3)）。
-- 证明：NSEOnT6 §4c axisLap-formula 已完成 negate² 相消，给出 u ⊕ (w ⊕ z)
-- （u = f(x+eᵢ)，w = f(x+2eᵢ)，z = f(x)）；此处仅做
-- (u⊕w)⊕z ↔ w⊕(u⊕z) 的结合/交换重排。口径：结构证明。
--------------------------------------------------------------------------------

dyn-axisLap-3pt : ∀ (i : C3) (f : ScalarField) (x : Torus6)
  → diffF i (diffF i f) x ≡ f (shiftAt i (shiftAt i x)) ⊕ (f (shiftAt i x) ⊕ f x)
dyn-axisLap-3pt i f x =
  trans (axisLap-formula i f x)
  (trans (sym (⊕-assoc (f (shiftAt i x)) (f (shiftAt i (shiftAt i x))) (f x)))
  (trans (cong (_⊕ f x)
           (⊕-comm (f (shiftAt i x)) (f (shiftAt i (shiftAt i x)))))
         (⊕-assoc (f (shiftAt i (shiftAt i x))) (f (shiftAt i x)) (f x))))

--------------------------------------------------------------------------------
-- §7. 卷二主引理：div∘grad 倍增——div (grad f) x ≡ 2·Δ f x
--
-- 右端「2·Δ f x」取展开形式 sum6 A₀ A₁ A₂ A₀ A₁ A₂，Aᵢ = f(x+eᵢ) ⊕ f(x+2eᵢ)
-- （NSEOnT6 头部记录的 Δ 精确公式；f(x) 项系数 6 ≡ 0 故不出现；
--   与 NSEOnT6 §5 div-grad：div (grad f) x ≡ laplacian f x 定义性同一）。
--
-- 证明组织（结构证明）：
--   ① div (grad f) x 定义性 = sum6 L₀ L₁ L₂ L₀ L₁ L₂（Lᵢ = axisLap i f x）；
--   ② cong6' 逐轴实例化 dyn-axisLap-3pt：Lᵢ ↝ wᵢ ⊕ (uᵢ ⊕ z)；
--   ③ sum6-+ 两次拆分：↝ Sw ⊕ (Su ⊕ Sz)，Sz = sum6 z ⋯ z = 6·z ≡ T₀
--     （dyn-six-zero）——这一步正是「f(x) 项共 6 个 ≡ 0 消去」的代数内容；
--   ④ 单位元 + ⊕-comm 收尾，sum6-+ 逆用重装成 Aᵢ = uᵢ ⊕ wᵢ 的双份形式。
--------------------------------------------------------------------------------

dyn-div-grad : ∀ (f : ScalarField) (x : Torus6) → div (grad f) x ≡ sum6
  ((f (shiftAt zero x) ⊕ f (shiftAt zero (shiftAt zero x))))
  ((f (shiftAt (suc zero) x) ⊕ f (shiftAt (suc zero) (shiftAt (suc zero) x))))
  ((f (shiftAt (suc (suc zero)) x) ⊕ f (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))))
  ((f (shiftAt zero x) ⊕ f (shiftAt zero (shiftAt zero x))))
  ((f (shiftAt (suc zero) x) ⊕ f (shiftAt (suc zero) (shiftAt (suc zero) x))))
  ((f (shiftAt (suc (suc zero)) x) ⊕ f (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))))
dyn-div-grad f x =
  trans (cong6' (dyn-axisLap-3pt zero f x)
                (dyn-axisLap-3pt (suc zero) f x)
                (dyn-axisLap-3pt (suc (suc zero)) f x)
                (dyn-axisLap-3pt zero f x)
                (dyn-axisLap-3pt (suc zero) f x)
                (dyn-axisLap-3pt (suc (suc zero)) f x))
  (trans (sum6-+ w0 (u0 ⊕ z) w1 (u1 ⊕ z) w2 (u2 ⊕ z)
                 w0 (u0 ⊕ z) w1 (u1 ⊕ z) w2 (u2 ⊕ z))
  (trans (cong (Sw ⊕_) (sum6-+ u0 z u1 z u2 z u0 z u1 z u2 z))
  (trans (cong (Sw ⊕_) (cong (Su ⊕_) (dyn-six-zero z)))
  (trans (cong (Sw ⊕_) (⊕-identityʳ Su))
         (trans (⊕-comm Sw Su)
                (sym (sum6-+ u0 w0 u1 w1 u2 w2 u0 w0 u1 w1 u2 w2)))))))
  where
    u0 = f (shiftAt zero x)
    u1 = f (shiftAt (suc zero) x)
    u2 = f (shiftAt (suc (suc zero)) x)
    w0 = f (shiftAt zero (shiftAt zero x))
    w1 = f (shiftAt (suc zero) (shiftAt (suc zero) x))
    w2 = f (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))
    z  = f x
    Su = sum6 u0 u1 u2 u0 u1 u2
    Sw = sum6 w0 w1 w2 w0 w1 w2

--------------------------------------------------------------------------------
-- §8. 卷二组装：散度流定律 div (nsStep v) x ≡ div v x ⊕ 2·Δ(div v) x
--
-- nsStep v = v +F grad (div v)（定义性）→ div-+F（NSEOnT6 §3）
-- → dyn-div-grad 实例化于 f := div v。口径：结构证明。
--------------------------------------------------------------------------------

dyn-flow-law : ∀ (v : Field) (x : Torus6) → div (nsStep v) x ≡ div v x ⊕ sum6
  ((div v (shiftAt zero x) ⊕ div v (shiftAt zero (shiftAt zero x))))
  ((div v (shiftAt (suc zero) x) ⊕ div v (shiftAt (suc zero) (shiftAt (suc zero) x))))
  ((div v (shiftAt (suc (suc zero)) x) ⊕ div v (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))))
  ((div v (shiftAt zero x) ⊕ div v (shiftAt zero (shiftAt zero x))))
  ((div v (shiftAt (suc zero) x) ⊕ div v (shiftAt (suc zero) (shiftAt (suc zero) x))))
  ((div v (shiftAt (suc (suc zero)) x) ⊕ div v (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))))
dyn-flow-law v x =
  trans (div-+F v (grad (div v)) x)
        (cong (div v x ⊕_) (dyn-div-grad (div v) x))

--------------------------------------------------------------------------------
-- §9. 后续卷预告（nsStep⁹ = id 组装件）
--
-- 卷三：lap₃ 零幂链（mod 3）。
-- 卷四：freshman's dream——(I + GD)⁹ = I + (GD)⁹。
-- 卷五：组装 nsStep⁹ = I。
--------------------------------------------------------------------------------
