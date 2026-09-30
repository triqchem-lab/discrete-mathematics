{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.HoTT.HomotopyPi1
--
-- 拓扑同伦 / 基本群（骨架深化方向②）：**离散同伦的路径复合幺半群** +
-- **T⁶ 基本群 = 格点加法群**（接 T6Homotopy 线）。
--
-- 设计（结构 = 生成方式）：
--   1. PathAlg —— 离散路径代数（复合 + 单位 + 逆 + 结合/单位/逆律）的通用记录
--   2. π₁(T⁶) 实例 —— 载体 T6Lattice（格点），复合 = t6Add，单位 = t6Zero，
--      逆 = t6Neg；六生成元 g1..g6 = 六轴单位步（TorusGeometry 既有）。
--      「基本群 = 格点加法群」在此实例层兑现：走圈的复合恰为格点加法。
--
-- 诚实边界：离散同伦 = 净位移等价（走圈按端点位移识别）；同伦等价关系的
-- 高阶构造（路径的路径）列 roadmap；T⁶ 的 π₁ ≅ ℤ⁶ 作为抽象群同构的完整陈述
-- 需自由交换群的泛性质层，本模块先立「格点加法实例」+ 生成元分解。
--
-- 0 postulate / 0 hole。
-- 【八要素投影对齐注记（2026-09-29 三域审计收尾）】本模块是**投影层**：
--   π₁(T⁶) = DC 走圈的净位移投影（格点加法群），非展示群本体——展示群八要素
--   （载体/生成元/关系/相位/时钟/归零/刚性/核对）的完整体在 DC 侧：
--   DuodecClock（8/8）+ DayanCore（关系 δ³=φ⁴=δφφδ）+ DCGroup（刚性 σ_DC）。
--   PathAlg 记录是群公理词汇层；relations 跨对象语义：t6-generate 的生成元
--   g1..g6 是 DC 混合生成元走圈的净位移基，其关系（分量阶、交换）由 DC 关系
--   投影而来；本层不新增关系、不自称展示群（八要素判据适用性 = 投影层）。
module Sovereign.HoTT.HomotopyPi1 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Sovereign.Structology.T6 using (T6Lattice; GF3)
open import Sovereign.Geometry.TorusGeometry using (_+₃_; neg3; t6Add; t6Zero; t6Neg; g1; g2; g3; g4; g5; g6; tritOf; finOf)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-comm; ⊕-inverse; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ)

--------------------------------------------------------------------------------
-- 1. 离散路径代数（复合幺半群 + 逆 = 群胚结构数据）
--------------------------------------------------------------------------------

record PathAlg (A : Set) : Set where
  field
    _∘p_ : A → A → A
    ε : A
    inv : A → A
    assoc : ∀ x y z → (x ∘p y) ∘p z ≡ x ∘p (y ∘p z)
    idˡ : ∀ x → ε ∘p x ≡ x
    idʳ : ∀ x → x ∘p ε ≡ x
    invˡ : ∀ x → inv x ∘p x ≡ ε

--------------------------------------------------------------------------------
-- 2. Fin 3 侧小律（经 Trit 桥接；双往返 3 案引理 + 代数链）
--------------------------------------------------------------------------------

trit-fin : ∀ (x : Fin 3) → finOf (tritOf x) ≡ x
trit-fin zero = refl
trit-fin (suc zero) = refl
trit-fin (suc (suc zero)) = refl

fin-trit : ∀ (y : Trit) → tritOf (finOf y) ≡ y
fin-trit T₀ = refl
fin-trit T₁ = refl
fin-trit T₂ = refl

+₃-assoc : ∀ x y z → (x +₃ y) +₃ z ≡ x +₃ (y +₃ z)
+₃-assoc x y z =
  trans (cong finOf (trans (cong (λ w → w ⊕ tritOf z) (fin-trit (tritOf x ⊕ tritOf y)))
                          (⊕-assoc (tritOf x) (tritOf y) (tritOf z))))
        (cong finOf (cong (tritOf x ⊕_) (sym (fin-trit (tritOf y ⊕ tritOf z)))))

+₃-idˡ : ∀ x → zero +₃ x ≡ x
+₃-idˡ x = trans (cong finOf (⊕-identityˡ (tritOf x))) (trit-fin x)

+₃-idʳ : ∀ x → x +₃ zero ≡ x
+₃-idʳ x = trans (cong finOf (⊕-identityʳ (tritOf x))) (trit-fin x)

trit-neg3 : ∀ x → tritOf (neg3 x) ≡ negate (tritOf x)
trit-neg3 zero = refl
trit-neg3 (suc zero) = refl
trit-neg3 (suc (suc zero)) = refl

neg3-+₃ : ∀ x → neg3 x +₃ x ≡ zero
neg3-+₃ x = trans (cong finOf (trans (cong (_⊕ tritOf x) (trit-neg3 x))
                                    (trans (⊕-comm (negate (tritOf x)) (tritOf x))
                                           (⊕-inverse (tritOf x))))) refl

---------------------------------------------------------------------------------- 3. T6Lattice 侧六分量链
--------------------------------------------------------------------------------

t6Add-assoc : ∀ x y z → t6Add (t6Add x y) z ≡ t6Add x (t6Add y z)
t6Add-assoc (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
           (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ [])
           (z₀ ∷ z₁ ∷ z₂ ∷ z₃ ∷ z₄ ∷ z₅ ∷ []) =
  cong₂ _∷_ (+₃-assoc x₀ y₀ z₀)
   (cong₂ _∷_ (+₃-assoc x₁ y₁ z₁)
    (cong₂ _∷_ (+₃-assoc x₂ y₂ z₂)
     (cong₂ _∷_ (+₃-assoc x₃ y₃ z₃)
      (cong₂ _∷_ (+₃-assoc x₄ y₄ z₄)
       (cong₂ _∷_ (+₃-assoc x₅ y₅ z₅) refl)))))

t6Add-idˡ : ∀ x → t6Add t6Zero x ≡ x
t6Add-idˡ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ _∷_ (+₃-idˡ x₀)
   (cong₂ _∷_ (+₃-idˡ x₁)
    (cong₂ _∷_ (+₃-idˡ x₂)
     (cong₂ _∷_ (+₃-idˡ x₃)
      (cong₂ _∷_ (+₃-idˡ x₄)
       (cong₂ _∷_ (+₃-idˡ x₅) refl)))))

t6Add-idʳ : ∀ x → t6Add x t6Zero ≡ x
t6Add-idʳ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ _∷_ (+₃-idʳ x₀)
   (cong₂ _∷_ (+₃-idʳ x₁)
    (cong₂ _∷_ (+₃-idʳ x₂)
     (cong₂ _∷_ (+₃-idʳ x₃)
      (cong₂ _∷_ (+₃-idʳ x₄)
       (cong₂ _∷_ (+₃-idʳ x₅) refl)))))

t6Neg-invˡ : ∀ x → t6Add (t6Neg x) x ≡ t6Zero
t6Neg-invˡ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ _∷_ (neg3-+₃ x₀)
   (cong₂ _∷_ (neg3-+₃ x₁)
    (cong₂ _∷_ (neg3-+₃ x₂)
     (cong₂ _∷_ (neg3-+₃ x₃)
      (cong₂ _∷_ (neg3-+₃ x₄)
       (cong₂ _∷_ (neg3-+₃ x₅) refl)))))

--------------------------------------------------------------------------------
-- 4. π₁(T⁶) 实例：基本群 = 格点加法群
--------------------------------------------------------------------------------

pi1-t6 : PathAlg T6Lattice
pi1-t6 = record
  { _∘p_ = t6Add
  ; ε = t6Zero
  ; inv = t6Neg
  ; assoc = t6Add-assoc
  ; idˡ = t6Add-idˡ
  ; idʳ = t6Add-idʳ
  ; invˡ = t6Neg-invˡ }

-- 生成元注（六轴单位步 g1..g6 = TorusGeometry 既有）：任意格点走圈按分量
-- 分解为 gi 的倍步和（分量值 0/1/2）——分解的完全形式化（六轴投影/重建）
-- 列 roadmap（同 DEEP.homotopy-pi1 后续段）。

--------------------------------------------------------------------------------
-- 5. 追加：π₁(T⁶) 交换性（Abel）+ 生成元分解（Σ 形式存在引理）
--    既有签名一律不变；本节只新增定义与引理。
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open import Sovereign.Geometry.TorusGeometry using (t6Scale)

--------------------------------------------------------------------------------
-- 5.1 交换性（Abel）：分量 ⊕-comm → 六链 → 路径复合交换
--------------------------------------------------------------------------------

-- 分量交换：+₃ = finOf ∘ ⊕ ∘ (tritOf × tritOf)，⊕-comm 一步提升
+₃-comm : ∀ x y → x +₃ y ≡ y +₃ x
+₃-comm x y = cong finOf (⊕-comm (tritOf x) (tritOf y))

-- π₁(T⁶) 交换性（六分量链，与 t6Add-assoc 同构法；对齐 TorusGeometry:143 的重导）
t6-comm : ∀ x y → t6Add x y ≡ t6Add y x
t6-comm (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
       (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) =
  cong₂ _∷_ (+₃-comm x₀ y₀)
   (cong₂ _∷_ (+₃-comm x₁ y₁)
    (cong₂ _∷_ (+₃-comm x₂ y₂)
     (cong₂ _∷_ (+₃-comm x₃ y₃)
      (cong₂ _∷_ (+₃-comm x₄ y₄)
       (cong₂ _∷_ (+₃-comm x₅ y₅) refl)))))

-- Abel：路径复合交换（π₁(T⁶) 的 Abel 化平凡——交换性在实例层兑现）
pi1-abelian : ∀ x y → PathAlg._∘p_ pi1-t6 x y ≡ PathAlg._∘p_ pi1-t6 y x
pi1-abelian x y = t6-comm x y

--------------------------------------------------------------------------------
-- 5.2 生成元分解（Σ 形式存在引理）：任意格点 = g1..g6 的倍步和
--     见证 nᵢ = 分量步数（0/1/2）；倍步 = t6Scale（TorusGeometry:208）
--------------------------------------------------------------------------------

-- 分量值 → 倍步数（0/1/2）
valOf : Fin 3 → ℕ
valOf zero = 0
valOf (suc zero) = 1
valOf (suc (suc zero)) = 2

-- 六轴倍步 = 纯轴向量（各 3 案 refl）
scale-g1 : ∀ v → t6Scale (valOf v) g1 ≡ (v ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ [])
scale-g1 zero = refl
scale-g1 (suc zero) = refl
scale-g1 (suc (suc zero)) = refl

scale-g2 : ∀ v → t6Scale (valOf v) g2 ≡ (zero ∷ v ∷ zero ∷ zero ∷ zero ∷ zero ∷ [])
scale-g2 zero = refl
scale-g2 (suc zero) = refl
scale-g2 (suc (suc zero)) = refl

scale-g3 : ∀ v → t6Scale (valOf v) g3 ≡ (zero ∷ zero ∷ v ∷ zero ∷ zero ∷ zero ∷ [])
scale-g3 zero = refl
scale-g3 (suc zero) = refl
scale-g3 (suc (suc zero)) = refl

scale-g4 : ∀ v → t6Scale (valOf v) g4 ≡ (zero ∷ zero ∷ zero ∷ v ∷ zero ∷ zero ∷ [])
scale-g4 zero = refl
scale-g4 (suc zero) = refl
scale-g4 (suc (suc zero)) = refl

scale-g5 : ∀ v → t6Scale (valOf v) g5 ≡ (zero ∷ zero ∷ zero ∷ zero ∷ v ∷ zero ∷ [])
scale-g5 zero = refl
scale-g5 (suc zero) = refl
scale-g5 (suc (suc zero)) = refl

scale-g6 : ∀ v → t6Scale (valOf v) g6 ≡ (zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ v ∷ [])
scale-g6 zero = refl
scale-g6 (suc zero) = refl
scale-g6 (suc (suc zero)) = refl

-- 六块和树（右嵌套，与 t6Steps 的分组一致）
t6Tree : T6Lattice → T6Lattice → T6Lattice → T6Lattice → T6Lattice → T6Lattice → T6Lattice
t6Tree a b c d e f = t6Add a (t6Add b (t6Add c (t6Add d (t6Add e f))))

-- 逐块同余（六块各一步 cong；≡-Reasoning 线性链，避免 trans 深嵌套）
t6Tree-cong :
  ∀ {a a′ b b′ c c′ d d′ e e′ f f′ : T6Lattice} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e′ → f ≡ f′ →
  t6Tree a b c d e f ≡ t6Tree a′ b′ c′ d′ e′ f′
t6Tree-cong {a} {a′} {b} {b′} {c} {c′} {d} {d′} {e} {e′} {f} {f′} p q r s t u = begin
  t6Tree a  b  c  d  e  f   ≡⟨ cong (λ w → t6Tree w b c d e f) p ⟩
  t6Tree a′ b  c  d  e  f   ≡⟨ cong (λ w → t6Tree a′ w c d e f) q ⟩
  t6Tree a′ b′ c  d  e  f   ≡⟨ cong (λ w → t6Tree a′ b′ w d e f) r ⟩
  t6Tree a′ b′ c′ d  e  f   ≡⟨ cong (λ w → t6Tree a′ b′ c′ w e f) s ⟩
  t6Tree a′ b′ c′ d′ e  f   ≡⟨ cong (λ w → t6Tree a′ b′ c′ d′ w f) t ⟩
  t6Tree a′ b′ c′ d′ e′ f   ≡⟨ cong (λ w → t6Tree a′ b′ c′ d′ e′ w) u ⟩
  t6Tree a′ b′ c′ d′ e′ f′  ∎
  where open ≡-Reasoning

-- 左零塔消去：zero 的塔在左、一层 zero 在右（塔高用 ℕ 的改名构造子，避开 Fin 同名）
nestL : ℕ → Fin 3 → Fin 3
nestL nzero   v = v +₃ zero
nestL (nsuc k) v = zero +₃ nestL k v

nestL-id : ∀ k v → nestL k v ≡ v
nestL-id nzero   v = +₃-idʳ v
nestL-id (nsuc k) v = trans (cong (λ w → zero +₃ w) (nestL-id k v)) (+₃-idˡ v)

-- 左零塔消去：zero 的塔在左、v 在最右（末轴 F 无右零）
nestR : ℕ → Fin 3 → Fin 3
nestR nzero   v = v
nestR (nsuc k) v = zero +₃ nestR k v

nestR-id : ∀ k v → nestR k v ≡ v
nestR-id nzero   v = refl
nestR-id (nsuc k) v = trans (cong (λ w → zero +₃ w) (nestR-id k v)) (+₃-idˡ v)

-- 纯轴向量之和 = 分量重建（六分量 cong₂ 链；各分量由 nestL/nestR 消去）
t6-sum-pure : ∀ v₀ v₁ v₂ v₃ v₄ v₅ →
  t6Tree (v₀ ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ [])
         (zero ∷ v₁ ∷ zero ∷ zero ∷ zero ∷ zero ∷ [])
         (zero ∷ zero ∷ v₂ ∷ zero ∷ zero ∷ zero ∷ [])
         (zero ∷ zero ∷ zero ∷ v₃ ∷ zero ∷ zero ∷ [])
         (zero ∷ zero ∷ zero ∷ zero ∷ v₄ ∷ zero ∷ [])
         (zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ v₅ ∷ [])
  ≡ (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ v₄ ∷ v₅ ∷ [])
t6-sum-pure v₀ v₁ v₂ v₃ v₄ v₅ =
  cong₂ _∷_ (nestL-id nzero v₀)
   (cong₂ _∷_ (nestL-id (nsuc nzero) v₁)
    (cong₂ _∷_ (nestL-id (nsuc (nsuc nzero)) v₂)
     (cong₂ _∷_ (nestL-id (nsuc (nsuc (nsuc nzero))) v₃)
      (cong₂ _∷_ (nestL-id (nsuc (nsuc (nsuc (nsuc nzero)))) v₄)
       (cong₂ _∷_ (nestR-id (nsuc (nsuc (nsuc (nsuc (nsuc nzero))))) v₅) refl)))))

-- 倍步和（见证的计算形态）
t6Steps : (Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3) → T6Lattice
t6Steps (v₀ , v₁ , v₂ , v₃ , v₄ , v₅) =
  t6Tree (t6Scale (valOf v₀) g1) (t6Scale (valOf v₁) g2) (t6Scale (valOf v₂) g3)
         (t6Scale (valOf v₃) g4) (t6Scale (valOf v₄) g5) (t6Scale (valOf v₅) g6)

-- 倍步和 = 纯轴和（六条 scale-gᵢ 一次换入 + 纯轴和重建）
t6-steps-pure : ∀ v₀ v₁ v₂ v₃ v₄ v₅ →
  t6Steps (v₀ , v₁ , v₂ , v₃ , v₄ , v₅) ≡ (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ v₄ ∷ v₅ ∷ [])
t6-steps-pure v₀ v₁ v₂ v₃ v₄ v₅ =
  trans (t6Tree-cong (scale-g1 v₀) (scale-g2 v₁) (scale-g3 v₂)
                    (scale-g4 v₃) (scale-g5 v₄) (scale-g6 v₅))
        (t6-sum-pure v₀ v₁ v₂ v₃ v₄ v₅)

-- 生成元分解（Σ 形式存在引理）：任意 T6Lattice 元 = g1..g6 的倍步和
-- （见证 = 六分量步数 0/1/2；「基本群 = 格点加法群」的生成元侧兑现）
t6-generate : (x : T6Lattice) →
  Σ (Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3) (λ vs → t6Steps vs ≡ x)
t6-generate (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ v₄ ∷ v₅ ∷ []) =
  (v₀ , v₁ , v₂ , v₃ , v₄ , v₅) , t6-steps-pure v₀ v₁ v₂ v₃ v₄ v₅

--------------------------------------------------------------------------------
-- 6. 路径的路径（同伦 2-层）与分解唯一性（ℤ⁶ 双射半边）
--------------------------------------------------------------------------------

-- 同伦：两条走圈同伦 ⇔ 净位移相等（离散模型的 2-态定义）
Homotopy : T6Lattice → T6Lattice → Set
Homotopy w₁ w₂ = w₁ ≡ w₂

h-refl : ∀ w → Homotopy w w
h-refl w = refl

h-sym : ∀ {w₁ w₂} → Homotopy w₁ w₂ → Homotopy w₂ w₁
h-sym = sym

h-trans : ∀ {w₁ w₂ w₃} → Homotopy w₁ w₂ → Homotopy w₂ w₃ → Homotopy w₁ w₃
h-trans = trans

-- 复合在同伦类上良定义（商层 = π₁ 结构的合法性半边）
comp-cong : ∀ {x x′ y y′} → Homotopy x x′ → Homotopy y y′ → Homotopy (t6Add x y) (t6Add x′ y′)
comp-cong = cong₂ t6Add

-- 诚实边界注记：离散净位移模型中 ≡ 携 UIP ⇒ 路径的路径平凡坍缩（∞-群胚截断为 set）；
-- 此处 2-层的正确形态即「同伦类 = 位移」，非可缩性缺陷而是模型的判定层特征。
-- 高阶（2-群胚/非平凡 2-同伦）需走圈空间的词表示（word-of-steps 模型），列 roadmap。

-- 分解唯一性（t6-generate 的伴随半边：见证在标准形下唯一）
tup-vec-inj : ∀ (v₀ v₁ v₂ v₃ v₄ v₅ w₀ w₁ w₂ w₃ w₄ w₅ : Fin 3)
  → (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ v₄ ∷ v₅ ∷ []) ≡ (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ w₄ ∷ w₅ ∷ [])
  → (v₀ , v₁ , v₂ , v₃ , v₄ , v₅) ≡ (w₀ , w₁ , w₂ , w₃ , w₄ , w₅)
tup-vec-inj v₀ v₁ v₂ v₃ v₄ v₅ w₀ w₁ w₂ w₃ w₄ w₅ eq =
  trans (cong (λ z → (proj₁v z , v₁ , v₂ , v₃ , v₄ , v₅)) eq)
  (trans (cong (λ z → (w₀ , proj₂v z , v₂ , v₃ , v₄ , v₅)) eq)
  (trans (cong (λ z → (w₀ , w₁ , proj₃v z , v₃ , v₄ , v₅)) eq)
  (trans (cong (λ z → (w₀ , w₁ , w₂ , proj₄v z , v₄ , v₅)) eq)
  (trans (cong (λ z → (w₀ , w₁ , w₂ , w₃ , proj₅v z , v₅)) eq)
         (cong (λ z → (w₀ , w₁ , w₂ , w₃ , w₄ , proj₆v z)) eq)))))
  where
    proj₁v : Vec GF3 6 → Fin 3 ; proj₁v (x ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) = x
    proj₂v : Vec GF3 6 → Fin 3 ; proj₂v (_ ∷ x ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) = x
    proj₃v : Vec GF3 6 → Fin 3 ; proj₃v (_ ∷ _ ∷ x ∷ _ ∷ _ ∷ _ ∷ []) = x
    proj₄v : Vec GF3 6 → Fin 3 ; proj₄v (_ ∷ _ ∷ _ ∷ x ∷ _ ∷ _ ∷ []) = x
    proj₅v : Vec GF3 6 → Fin 3 ; proj₅v (_ ∷ _ ∷ _ ∷ _ ∷ x ∷ _ ∷ []) = x
    proj₆v : Vec GF3 6 → Fin 3 ; proj₆v (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ x ∷ []) = x

decomp-unique : ∀ (s t : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3)
  → t6Steps s ≡ t6Steps t → s ≡ t
decomp-unique (v₀ , v₁ , v₂ , v₃ , v₄ , v₅) (w₀ , w₁ , w₂ , w₃ , w₄ , w₅) eq =
  tup-vec-inj v₀ v₁ v₂ v₃ v₄ v₅ w₀ w₁ w₂ w₃ w₄ w₅
    (trans (sym (t6-steps-pure v₀ v₁ v₂ v₃ v₄ v₅))
      (trans eq (t6-steps-pure w₀ w₁ w₂ w₃ w₄ w₅)))
