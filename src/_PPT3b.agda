{-# OPTIONS --rewriting --guardedness #-}

-- | _PPT3b
-- PT-3 立界件 (i)：一般形 transport 机件——StageEq 见证下的 MonoidIso 搬运
--
-- 数学背景：PT-3 实例塔 Xₙ(suc n) = π₁ᵈ G x 为**定义同型**，同构 = id-π₁-iso
--   definitional 直承载；一般塔仅「等式非定义同型」时，同构需沿阶段等式
--   e : Xₙ(suc n) ≡ π₁ᵈ G x 做 transport-of-structure：阶段载体上的运算
--   定义为「拉回的 π₁ᵈ 运算」（tr⁻¹ ∘ ⊞ᵈ ∘ (tr × tr)）——关系入定义口径：
--   阶段结构由搬运定义，非外来数据。于是 to = tr 恰为同构，往返由
--   subst 双消去（tr-trinv/trinv-tr）收口。
--
-- 核心原则：
-- 1. transport 件泛型化（A B 抽象变量——J 规则 refl 匹配合法非 K）
-- 2. 阶段结构随等式拉回（关系入定义：·ₙ 由 e 定义）
-- 3. 实例塔特例核对（definitional 形——与 _PPT3 iso-gskel 对账）
-- 4. i≥2 承载照旧立界（迭代 Ω 截断性质——不硬拱）
--
-- 包含：tr≡/tr≡-inv/tr-trinv/trinv-tr（transport 件）｜
--       General 模块（tower-pi-iso-general 一般形同构）｜特例核对 ×2
module _PPT3b where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; nil)
open import Cubical.HITs.SetQuotients using ([_])
open import Cubical.Data.Equality as CE using (eqToPath; pathToEq)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_)
open import _PPI4 using (MonoidIso; Gskel)
open import _PPT2 using (PostnikovTower; tower-gskel)
open import _PPT3 using (StageEq; stage-eq-gskel)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)

--------------------------------------------------------------------------------
-- §1 transport 件（泛型——A B 抽象变量，J 规则 refl 匹配）
--------------------------------------------------------------------------------

-- 沿类型等式搬运元素
tr≡ : {A B : Set} → A ≡ B → A → B
tr≡ p = subst (λ X → X) p

-- 逆向搬运
tr≡-inv : {A B : Set} → A ≡ B → B → A
tr≡-inv p = subst (λ X → X) (sym p)

-- 双消去（右）：tr (tr⁻¹ b) ≡ b
tr-trinv : {A B : Set} (p : A ≡ B) (b : B) → tr≡ p (tr≡-inv p b) ≡ b
tr-trinv refl b = refl

-- 双消去（左）：tr⁻¹ (tr a) ≡ a
trinv-tr : {A B : Set} (p : A ≡ B) (a : A) → tr≡-inv p (tr≡ p a) ≡ a
trinv-tr refl a = refl

-- 双≡桥（_PPI3d 先例同款）：PropEq≡ ↔ Builtin≡(CE) ↔ Cubical Path
toCE : {A : Set} {a b : A} → a ≡ b → a CE.≡ b
toCE refl = CE.refl

frCE : {A : Set} {a b : A} → a CE.≡ b → a ≡ b
frCE CE.refl = refl

--------------------------------------------------------------------------------
-- §2 一般形同构定理骨架（tower-pi-iso-general）
--    见证 se : StageEq x tower（每阶 n：Xₙ(suc n) ≡ π₁ᵈ G x）→
--    阶段载体拉回结构 + to = tr 的同构收口
--------------------------------------------------------------------------------

module Transport {A Y : Set} (e : A ≡ Y) (_⊞Y_ : Y → Y → Y) (eY : Y) where

  trA : A → Y
  trA = tr≡ e

  trA⁻ : Y → A
  trA⁻ = tr≡-inv e

  -- 拉回结构（关系入定义：A 侧运算 = Y 侧运算经 tr 搬回）
  ·A : A → A → A
  ·A u v = trA⁻ (trA u ⊞Y trA v)

  eA : A
  eA = trA⁻ eY

  -- 泛型 transport 同构（to = trA 收口——往返全由双消去承载）
  iso-general : MonoidIso A Y ·A eA _⊞Y_ eY
  iso-general = record
    { to      = trA
    ; from    = trA⁻
    ; to-·    = λ u v → eqToPath (toCE (tr-trinv e (trA u ⊞Y trA v)))
    ; to-e    = eqToPath (toCE (tr-trinv e eY))
    ; from-·  = λ a b → eqToPath (toCE (sym (cong trA⁻ (cong₂ _⊞Y_ (tr-trinv e a) (tr-trinv e b)))))
    ; from-e  = refl
    ; to∘from = λ a → eqToPath (toCE (tr-trinv e a))
    ; from∘to = λ u → eqToPath (toCE (trinv-tr e u))
    }

-- 塔面实例化（StageEq 见证 + 拉回结构——一般形同构骨架）
module General {G : DiGraph} (x : DiGraph.V G)
               (tower : PostnikovTower G x) (se : StageEq {G = G} x tower) where

  tower-pi-iso-general : (n : ℕ) →
    MonoidIso (PostnikovTower.Xₙ tower (suc n)) (π₁ᵈ G x)
      (Transport.·A (se n) (_⊞ᵈ_ {G = G}) [ nil {G = G} x ])
      (Transport.eA (se n) (_⊞ᵈ_ {G = G}) [ nil {G = G} x ])
      _⊞ᵈ_ [ nil {G = G} x ]
  tower-pi-iso-general n =
    Transport.iso-general (se n) (_⊞ᵈ_ {G = G}) [ nil {G = G} x ]

--------------------------------------------------------------------------------
-- §3 实例塔特例核对（definitional 形——与 _PPT3 iso-gskel 对账）
--    tower-gskel 的 se = λ n → refl ⇒ trₙ = id / trₙ⁻ = id（definitional）⇒
--    一般形在实例塔上退化为恒等形（字段级核对）
--------------------------------------------------------------------------------

open General {G = Gskel two-chain} fzero tower-gskel stage-eq-gskel
  renaming (tower-pi-iso-general to iso-gskel-general)

-- 特例核对①：to 逐点恒等（tr≡ refl ≡ id definitional）
check-to-gskel : (n : ℕ) (z : PostnikovTower.Xₙ tower-gskel (suc n)) →
  MonoidIso.to (iso-gskel-general n) z ≡ z
check-to-gskel n z = refl

-- 特例核对②：单位搬运恒等（eₙ ↦ [ nil fzero ]）
check-e-gskel : (n : ℕ) →
  Transport.eA (stage-eq-gskel n) (_⊞ᵈ_ {G = Gskel two-chain}) [ nil {G = Gskel two-chain} fzero ]
    ≡ [ nil fzero ]
check-e-gskel n = refl

--------------------------------------------------------------------------------
-- §4 立界注记（照 PT-3 §4 不变）
-- (i) 本件已清（transport 机件——tr-trinv/trinv-tr + 拉回结构 + 同构收口）；
-- (ii) i≥2 承载：需 PT-2 立界的迭代 Ω 截断性质（塔阶段现为裸 Set，
--      πᵢᵈ i≥2 承载需阶段带图结构）——不硬拱；
-- (iii) S²ᵈ π₂ 塔阶对齐随 (ii)。
--------------------------------------------------------------------------------
