{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI5j
-- π₂ᵈ 商面 rec/elim 定理族 + 运算面（_PPI5g 立界件 (ii) 清偿）
--
-- 数学背景：π₂ᵈ = Ω2Walk(w,w)/Ω3Walk 是 SetQuotient。本件给出：
--   ① 消去原理族（rec 一般消去 + elimProp 命题消去 + 双商命题消去）——良定义性由
--      Ω3Walk 三律承载（EqRel3 面零新公理）；
--   ② 运算面：π₂ᵈ⁺ = Ω2Walk/Ω3Walk⁺（扩展生成集商）上的类运算——前缀作用/后缀作用
--      /二元复合 add2⁺（π₂ 加法的离散影）。与 π₂ᵈ 的桥 toπ₂（embed3 诱导）；
--   ③ S²ᵈ 核对（omega2-wit 类的 rec/运算实例）。
--
-- 核心原则：
-- 1. rec/elim 用 Cubical SetQuotients 库件（isSet 目标由 squash/ 承载——_PPI5c 范式）；
-- 2. 运算的尊重性来自 whisk3（前缀）/whiskR（后缀——本件推导主件：Ω3Step 单构造子
--    fill-tri ⇒ bub3 充当任意位右缘饰，whisk3/bub3 案经 ++2-assoc subst 搬运）；
-- 3. 尊重性证明用 elimProp（命题消去免 respect 手续——目标是集合中的路径=命题）。
--
-- 包含：++2-assoc ｜ rec₂ᵈ/elim₂ᵈ/elim2₂ᵈ/rep₂ ｜ π₂ᵈ⁺/toπ₂ ｜ whiskΩ3/whiskR/whiskR-walk
--       ｜ addL⁺/addR⁺/add2⁺ ｜ S²ᵈ 核对 ×5

module _PPI5j where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; funExt; isProp; isSet; subst)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; rec; elimProp; elimProp2)
open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; Walk)
open import _PPI5d using (Ω2Walk; nil2; cons2; s2-adj; s2v0; w3; omega2-wit)
open import _PPI5f using (Ω3Step; fill-tri; Ω3Walk; symm3; π₂ᵈ; chk-π2-wit-triv; omega2-wit-triv)
open import _PPI5g using (_++2_; bub; Ω3Step⁺; base3+; whisk3; bub3; Ω3Walk⁺; refl3+; symm3+; trans3+; gen3+; embed3)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件：++2 结合桥（运算面的搬运代数）
-- ────────────────────────────────────────────────────────────────────

-- 拼接结合律：(a ++2 b) ++2 c ≡ a ++2 (b ++2 c)——对 a 归纳
--   nil2 案：两侧 definitional 同形（nil2 ++2 x ≡ x）；
--   cons2 案：cong (cons2 s) 递归步。
++2-assoc : {G : DiGraph} {x : DiGraph.V G} {w1 w2 w3 w4 : Walk G x x}
            (a : Ω2Walk G x w1 w2) (b : Ω2Walk G x w2 w3) (c : Ω2Walk G x w3 w4)
          → (a ++2 b) ++2 c ≡ a ++2 (b ++2 c)
++2-assoc (nil2 w) b c = refl
++2-assoc (cons2 s a) b c = cong (cons2 s) (++2-assoc a b c)

-- ────────────────────────────────────────────────────────────────────
-- ④ 组合层：rec/elim 定理族（消去原理 + 良定义性）
-- ────────────────────────────────────────────────────────────────────

-- 尊重性类型（良定义性条件——由 Ω3Walk 三律/EqRel3 承载）
resp₂ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} (B : Set)
      → (h : Ω2Walk G x w w → B) → Set
resp₂ {G} {x} {w} B h = (c c' : Ω2Walk G x w w) → Ω3Walk G x c c' → h c ≡ h c'

-- rec 一般消去：尊重函数经商面提升（_PPI5c 的 to₁ 范式同款）
rec₂ᵈ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} (B : Set)
        (set : isSet B) (h : Ω2Walk G x w w → B) (resp : resp₂ B h)
      → π₂ᵈ G x w → B
rec₂ᵈ B set h resp = rec set h resp

-- elimProp 命题消去：命题族自动良定义（免 respect 手续）
elim₂ᵈ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} {P : π₂ᵈ G x w → Set}
         (prop : (q : π₂ᵈ G x w) → isProp (P q)) (f : (c : Ω2Walk G x w w) → P [ c ])
       → (q : π₂ᵈ G x w) → P q
elim₂ᵈ prop f = elimProp prop f

-- 双商命题消去（类对性质——等式型动机的标准形）
elim2₂ᵈ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x}
          {P : π₂ᵈ G x w → π₂ᵈ G x w → Set}
          (prop : (q q' : π₂ᵈ G x w) → isProp (P q q'))
          (f : (c c' : Ω2Walk G x w w) → P [ c ] [ c' ])
        → (q q' : π₂ᵈ G x w) → P q q'
elim2₂ᵈ prop f = elimProp2 prop f

-- rep₂（elim 的真实应用）：若 c 与一切 2-腔 3-同伦，则每个类都等于 [ c ]
rep₂ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} (c : Ω2Walk G x w w)
       (h : (c' : Ω2Walk G x w w) → Ω3Walk G x c c')
     → (q : π₂ᵈ G x w) → q ≡ [ c ]
rep₂ {G} {x} {w} c h = elim₂ᵈ (λ q → squash/ q [ c ]) (λ c' → eq/ c' c (symm3 (h c')))

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 组合层：运算面（π₂ᵈ⁺ 类运算——Ω3Walk⁺ 形）
-- ────────────────────────────────────────────────────────────────────

-- π₂ᵈ⁺：扩展生成集商（Ω3Walk⁺ 关系——bubble-complete/whisk3 装配面）
π₂ᵈ⁺ : (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) → Set
π₂ᵈ⁺ G x w = Ω2Walk G x w w / (λ c c' → Ω3Walk⁺ G x c c')

-- 桥：Ω3Walk ⊆ Ω3Walk⁺（embed3）诱导**粗化** π₂ᵈ → π₂ᵈ⁺（细商→粗商良定义；
--   反向 π₂ᵈ⁺ → π₂ᵈ 需有效化=构造性边界——立界 (iii) 同族，不设）
coarse₂ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} → π₂ᵈ G x w → π₂ᵈ⁺ G x w
coarse₂ = rec squash/ (λ c → [ c ]) (λ c c' r → eq/ c c' (embed3 r))

-- 前缀缘饰（Ω3Walk⁺ 层——whisk3 逐案提升）
whiskΩ3 : {G : DiGraph} {x : DiGraph.V G} {w1 wm w2 : Walk G x x}
          (p : Ω2Walk G x w1 wm) {c c' : Ω2Walk G x wm w2}
        → Ω3Walk⁺ G x c c' → Ω3Walk⁺ G x (p ++2 c) (p ++2 c')
whiskΩ3 p (refl3+ c) = refl3+ (p ++2 c)
whiskΩ3 p (symm3+ q) = symm3+ (whiskΩ3 p q)
whiskΩ3 p (trans3+ q q') = trans3+ (whiskΩ3 p q) (whiskΩ3 p q')
whiskΩ3 p (gen3+ s) = gen3+ (whisk3 p s)

-- 后缀缘饰（生成元层——本件推导主件）：Ω3Step 单构造子 fill-tri ⇒ bub3 充当任意位
-- 右缘饰；whisk3/bub3 案经 ++2-assoc subst 搬运（构造携带形免 K）。
whiskR : {G : DiGraph} {x : DiGraph.V G} {w1 w2 w3 : Walk G x x}
         {c c' : Ω2Walk G x w1 w2} → Ω3Step⁺ G x c c' → (e : Ω2Walk G x w2 w3)
       → Ω3Step⁺ G x (c ++2 e) (c' ++2 e)
whiskR (base3+ (fill-tri s)) e = bub3 (nil2 _) s e
whiskR (whisk3 c₁ {c} {c'} s) e =
  subst (λ u → Ω3Step⁺ _ _ u ((c₁ ++2 c') ++2 e)) (sym (++2-assoc c₁ c e))
    (subst (λ v → Ω3Step⁺ _ _ (c₁ ++2 (c ++2 e)) v) (sym (++2-assoc c₁ c' e))
      (whisk3 c₁ (whiskR s e)))
whiskR (bub3 c₁ s c₂) e =
  subst (λ u → Ω3Step⁺ _ _ u ((c₁ ++2 c₂) ++2 e)) (sym (++2-assoc (c₁ ++2 bub s) c₂ e))
    (subst (λ v → Ω3Step⁺ _ _ ((c₁ ++2 bub s) ++2 (c₂ ++2 e)) v) (sym (++2-assoc c₁ c₂ e))
      (bub3 c₁ s (c₂ ++2 e)))

-- 后缀缘饰（Ω3Walk⁺ 层——三律闭包 + 生成元层）
whiskR-walk : {G : DiGraph} {x : DiGraph.V G} {w1 w2 w3 : Walk G x x}
              {c c' : Ω2Walk G x w1 w2} → Ω3Walk⁺ G x c c' → (e : Ω2Walk G x w2 w3)
            → Ω3Walk⁺ G x (c ++2 e) (c' ++2 e)
whiskR-walk (refl3+ c) e = refl3+ (c ++2 e)
whiskR-walk (symm3+ p) e = symm3+ (whiskR-walk p e)
whiskR-walk (trans3+ p q) e = trans3+ (whiskR-walk p e) (whiskR-walk q e)
whiskR-walk (gen3+ s) e = gen3+ (whiskR s e)

-- 前缀作用（左模面——尊重性在第二变元，whiskΩ3 承载）
addL⁺ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x}
        (c : Ω2Walk G x w w) → π₂ᵈ⁺ G x w → π₂ᵈ⁺ G x w
addL⁺ c = rec squash/ (λ d → [ c ++2 d ]) (λ d d' s → eq/ (c ++2 d) (c ++2 d') (whiskΩ3 c s))

-- 后缀作用（尊重性在第一变元，whiskR-walk 承载）
addR⁺ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x}
        (e : Ω2Walk G x w w) → π₂ᵈ⁺ G x w → π₂ᵈ⁺ G x w
addR⁺ e = rec squash/ (λ c → [ c ++2 e ]) (λ c c' s → eq/ (c ++2 e) (c' ++2 e) (whiskR-walk s e))

-- 二元类运算（π₂ 加法的离散影）：双商 rec——外层尊重性经 elimProp（命题消去）收口
add2⁺ : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x}
      → π₂ᵈ⁺ G x w → π₂ᵈ⁺ G x w → π₂ᵈ⁺ G x w
add2⁺ {G} {x} {w} q r = rec squash/ (λ c → addL⁺ c r) resp-outer q
  where
  resp-outer : (c c' : Ω2Walk G x w w) → Ω3Walk⁺ G x c c' → addL⁺ c r ≡ addL⁺ c' r
  resp-outer c c' s =
    elimProp (λ r' → squash/ (addL⁺ c r') (addL⁺ c' r'))
             (λ d → eq/ (c ++2 d) (c' ++2 d) (whiskR-walk s d)) r

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 核对层：S²ᵈ 实例（omega2-wit 类的 rec/运算核对——全 defeq/refl 级过内核）
-- ────────────────────────────────────────────────────────────────────

-- rec 计算律：rec 于代表元 defeq 归约（[_] 案）
check-rec-id : rec₂ᵈ (π₂ᵈ s2-adj s2v0 w3) (squash/) (λ c → [ c ]) (λ c c' r → eq/ c c' r)
                 [ omega2-wit ] ≡ [ omega2-wit ]
check-rec-id = refl

-- rec 于已知类等式（chk-π2-wit-triv 的同态像——两条路径同端点）
check-rec-on-eq : _≡_ {A = π₂ᵈ s2-adj s2v0 w3} [ omega2-wit ] [ nil2 w3 ]
check-rec-on-eq =
  cong (rec₂ᵈ (π₂ᵈ s2-adj s2v0 w3) (squash/) (λ c → [ c ]) (λ c c' r → eq/ c c' r))
       chk-π2-wit-triv

-- 运算面：单位元左侧（nil2 ++2 c ≡ c definitional）
check-add-nil : add2⁺ {G = s2-adj} {x = s2v0} {w = w3} [ nil2 w3 ] [ omega2-wit ]
              ≡ [ omega2-wit ]
check-add-nil = refl

-- 后缀缘饰自反核对：omega2-wit ++2 nil2 w3 ≡ omega2-wit（defeq——末位 nil2 拼吸收）
check-whR-eq : _≡_ {A = Ω2Walk s2-adj s2v0 w3 w3} (omega2-wit ++2 nil2 w3) omega2-wit
check-whR-eq = refl

-- 桥计算律：toπ₂ 于代表元 defeq
check-coarse-id : _≡_ {A = π₂ᵈ⁺ s2-adj s2v0 w3} (coarse₂ [ omega2-wit ]) [ omega2-wit ]
check-coarse-id = refl

-- ────────────────────────────────────────────────────────────────────
-- ⑦ 立界注记（诚实边界）
-- (i) π₂ᵈ⁺ 是 π₂ᵈ 的**粗化商**（Ω3Walk⁺ 认同更多）——运算面活在粗化商上（尊重性
--     由 whiskΩ3/whiskR 承载）；粗化桥 coarse₂ 单向（embed3），反向需有效化；
--     π₂ᵈ（细商）上的运算需 Ω3Walk 层右缘饰（完备形方向二邻域，_PPI5h Dir2 同族）；
-- (ii) add2⁺ 的交换性/结合性（π₂ 阿贝尔性）：需 bubble-complete 全形（一般面类）——
--     S²ᵈ 气泡可分解面上可证（TriFill 路径），一般形随 _PPI5h 方向二；
-- (iii) rep₂ 的逆向（类相等 ⟹ Ω3Walk）= 商面有效化（构造性边界，_PPI5i 同族）。
-- ────────────────────────────────────────────────────────────────────
