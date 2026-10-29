{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATRed
-- 归约族（SATFam 立界 (v) 的可证部分）——归约框架 + NP 封闭 + 真归约族实例
--
-- 【边界声明（头注，必须先读）】本件**不**证明 SAT 族的 NP-完备性。完备性 =
-- NP-难（∀ L ∈ NP，L ≤ₚ SAT 族）+ SAT 族 ∈ NP（后者已在 SATFam §6 闭合）。
-- 前者 = Cook–Levin：需要把**任意**验证器变成 CNF（tableau 构造）。本库 InNP
-- 的 np-verifier 是**任意 Agda 总函数**（无转移表、无机器），函数 → CNF 的
-- 编码即「计算迹编码」，属 W2 深件（库内 TM 亦无通用机构造，TuringMachine
-- §5(iii) 立界）。故本件交付 (v) 的三块可证部分：
--
--   ① 归约关系框架 Reduces（多项式界 + 计数代价 + 双向正确性）：
--      自归约 red-refl、复合 red-trans（界 n ↦ q₁ n + q₂(q₁ n)）；
--   ② **NP 对多项式归约封闭**（red-preserves-NP）：L ≤ₚ L′ 且 L′ ∈ NP
--      ⟹ L ∈ NP——「NP-完备性」的另一半骨架，标准且非平凡；
--   ③ **真归约族实例**（§4）：L-Head₁ ≤ₚ L-SAT 3，输出长恒 24，而
--      SF-wlog3 24 ≡ 3 ⟹ 目标恰是 SATFam 渐近族在 n = 24 的成员
--      （SVR-fam-member / SVR-head-fam 的族形版本），即归约确实落进**族**里；
--      推论 SVR-head-in-NP 由「SAT_3 ∈ NP + 本归约」经 red-preserves-NP 落出。
--
-- 【诚实边界（尾注 §6）】
--   (i)   NP-难（∀ L ∈ NP）未证：缺 tableau/Cook–Levin 构造（W2）。
--   (ii)  归约输出长取 n-only（r-out : ℕ → ℕ）——length-respecting 归约；
--         输出长随内容变的归约需要见证集 cast（NPClass §5(ii) 同立的 Vec
--         截断/重填 API）。
--   (iii) 归约映射的「多项式时间」以计数代价 r-cost（steps ≤ r-bound n）承载
--         ——与 PClass/NPClass 同一记账口径；机器可执行性维持 SATMBridge 边界。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATRed where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n⇒m≤1+n; +-comm)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; StepsLE; Mono; Pos; mono-+ˡ; mono-+ʳ)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass using (TritLang; headT; L-Head₁; isT₁)
open import Sovereign.Algebra.Complexity.NPClass using (InNP)
open import Data.Nat.DivMod using (_/_)
open import Sovereign.Algebra.Complexity.SATMember
  using (Asg; satFormula; decFormula; L-SAT; clauseW; sat-in-NP)
open import Sovereign.Algebra.Complexity.SATFam using (SF-wlog3; SF-LSAT-fam)
-- 复用库内既有 `_⇔_`（Foundation/DecisionSoundness §0；重名门禁要求不新建）
open import Sovereign.Foundation.DecisionSoundness using (_⇔_)

-- ────────────────────────────────────────────────────────────────────
-- §1 命题双向与计数复合〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 计数复合：先跑 c 得 a，再按 a 跑 f；账目相加（值/账目皆定义性可读）
SVR-bind : ∀ {A B} → Counted A → (A → Counted B) → Counted B
SVR-bind (mkCnt a k) f = mkCnt (value (f a)) (k + steps (f a))

-- ────────────────────────────────────────────────────────────────────
-- §2 归约关系〔结构定义〕——多项式界 + 计数代价 + 双向正确性
-- ────────────────────────────────────────────────────────────────────

record Reduces (L L′ : TritLang) : Set₁ where
  field
    r-out     : ℕ → ℕ                              -- 输出长度（仅依赖输入长）
    r-mono-out : Mono r-out                        -- 输出长随输入长单调
    r-map     : (n : ℕ) → Vec Trit n → Counted (Vec Trit (r-out n))
    r-bound   : ℕ → ℕ                              -- 多项式界
    r-mono    : Mono r-bound
    r-pos     : Pos r-bound
    r-len     : ∀ n → r-out n ≤ r-bound n          -- 输出长不超界
    r-cost    : ∀ n x → StepsLE (r-map n x) (r-bound n)
    r-correct : ∀ n x → L n x ⇔ L′ (r-out n) (value (r-map n x))

-- ────────────────────────────────────────────────────────────────────
-- §3 框架闭合：自归约 / 复合 / NP 封闭〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 自归约：恒等映射（输出长 = 输入长），界 suc n
red-refl : ∀ L → Reduces L L
red-refl L = record
  { r-out = λ n → n
  ; r-mono-out = λ {a} {b} a≤b → a≤b
  ; r-map = λ n x → mkCnt x 0
  ; r-bound = suc
  ; r-mono = s≤s
  ; r-pos = λ n → s≤s z≤n
  ; r-len = λ n → m≤n⇒m≤1+n ≤-refl
  ; r-cost = λ n x → z≤n
  ; r-correct = λ n x → (λ l → l) , (λ l → l) }

-- 复合：输出长 r₂∘r₁；界 q₁ n + q₂(q₁ n)（先付第一段的界，再付第二段）。
-- 正确性由 ⇔ 传递；账目 = 两段相加。
red-trans : ∀ {L L′ L″} → Reduces L L′ → Reduces L′ L″ → Reduces L L″
red-trans {L} {L′} {L″} r₁ r₂ = record
  { r-out = λ n → Reduces.r-out r₂ (Reduces.r-out r₁ n)
  ; r-mono-out = λ {a} {b} a≤b → Reduces.r-mono-out r₂ (Reduces.r-mono-out r₁ a≤b)
  ; r-map = λ n x → SVR-bind (Reduces.r-map r₁ n x)
                             (Reduces.r-map r₂ (Reduces.r-out r₁ n))
  ; r-bound = λ n → Reduces.r-bound r₁ n
                     + Reduces.r-bound r₂ (Reduces.r-bound r₁ n)
  ; r-mono = λ {a} {b} a≤b →
      ≤-trans (mono-+ʳ (Reduces.r-bound r₂ (Reduces.r-bound r₁ a))
                       (Reduces.r-mono r₁ a≤b))
              (mono-+ˡ (Reduces.r-bound r₁ b)
                       (Reduces.r-mono r₂ (Reduces.r-mono r₁ a≤b)))
  ; r-pos = λ n →
      ≤-trans (Reduces.r-pos r₁ n)
              (m≤m+n (Reduces.r-bound r₁ n)
                     (Reduces.r-bound r₂ (Reduces.r-bound r₁ n)))
  ; r-len = λ n →
      ≤-trans (≤-trans (Reduces.r-len r₂ (Reduces.r-out r₁ n))
                       (Reduces.r-mono r₂ (Reduces.r-len r₁ n)))
              (≤-trans (m≤m+n (Reduces.r-bound r₂ (Reduces.r-bound r₁ n))
                              (Reduces.r-bound r₁ n))
                       (≤-reflexive (+-comm (Reduces.r-bound r₂ (Reduces.r-bound r₁ n))
                                            (Reduces.r-bound r₁ n))))
  ; r-cost = λ n x →
      ≤-trans (≤-trans (mono-+ʳ
                          (steps (Reduces.r-map r₂ (Reduces.r-out r₁ n)
                                   (value (Reduces.r-map r₁ n x))))
                          (Reduces.r-cost r₁ n x))
                       (mono-+ˡ (Reduces.r-bound r₁ n)
                         (Reduces.r-cost r₂ (Reduces.r-out r₁ n)
                                        (value (Reduces.r-map r₁ n x)))))
              (mono-+ˡ (Reduces.r-bound r₁ n)
                (Reduces.r-mono r₂ (Reduces.r-len r₁ n)))
  ; r-correct = λ n x →
      (λ l → proj₁ (Reduces.r-correct r₂ (Reduces.r-out r₁ n)
                      (value (Reduces.r-map r₁ n x)))
                 (proj₁ (Reduces.r-correct r₁ n x) l))
      , (λ l → proj₂ (Reduces.r-correct r₁ n x)
                 (proj₂ (Reduces.r-correct r₂ (Reduces.r-out r₁ n)
                          (value (Reduces.r-map r₁ n x))) l)) }

-- ★ NP 对多项式归约封闭：L ≤ₚ L′ 且 L′ ∈ NP ⟹ L ∈ NP
-- 验证器 = 先算映射（账目 ≤ r-bound n），再把映射结果交给 L′ 的验证器；
-- 界 n ↦ r-bound n + p(r-bound n)。
red-preserves-NP : ∀ {L L′} → InNP L′ → Reduces L L′ → InNP L
red-preserves-NP {L} {L′} dp rd = record
  { np-p = λ n → Reduces.r-bound rd n + InNP.np-p dp (Reduces.r-bound rd n)
  ; np-p-mono = λ {a} {b} a≤b →
      ≤-trans (mono-+ʳ (InNP.np-p dp (Reduces.r-bound rd a))
                       (Reduces.r-mono rd a≤b))
              (mono-+ˡ (Reduces.r-bound rd b)
                       (InNP.np-p-mono dp (Reduces.r-mono rd a≤b)))
  ; np-p-pos = λ n →
      ≤-trans (Reduces.r-pos rd n)
              (m≤m+n (Reduces.r-bound rd n)
                     (InNP.np-p dp (Reduces.r-bound rd n)))
  ; np-witLen = λ n → InNP.np-witLen dp (Reduces.r-out rd n)
  ; np-w-mono = λ {a} {b} a≤b → InNP.np-w-mono dp (Reduces.r-mono-out rd a≤b)
  ; np-verifier = λ n x w →
      SVR-bind (Reduces.r-map rd n x)
               (λ y → InNP.np-verifier dp (Reduces.r-out rd n) y w)
  ; np-complete = λ n x l →
      proj₁ (InNP.np-complete dp (Reduces.r-out rd n)
               (value (Reduces.r-map rd n x))
               (proj₁ (Reduces.r-correct rd n x) l))
      , proj₂ (InNP.np-complete dp (Reduces.r-out rd n)
                 (value (Reduces.r-map rd n x))
                 (proj₁ (Reduces.r-correct rd n x) l))
  ; np-sound = λ n x w v →
      proj₂ (Reduces.r-correct rd n x)
            (InNP.np-sound dp (Reduces.r-out rd n)
                            (value (Reduces.r-map rd n x)) w v)
  ; np-cost = λ n x w →
      ≤-trans (≤-trans (mono-+ʳ
                          (steps (InNP.np-verifier dp (Reduces.r-out rd n)
                                   (value (Reduces.r-map rd n x)) w))
                          (Reduces.r-cost rd n x))
                       (mono-+ˡ (Reduces.r-bound rd n)
                         (InNP.np-cost dp (Reduces.r-out rd n)
                                       (value (Reduces.r-map rd n x)) w)))
              (mono-+ˡ (Reduces.r-bound rd n)
                (InNP.np-p-mono dp (Reduces.r-len rd n))) }

-- ────────────────────────────────────────────────────────────────────
-- §4 真归约族实例：L-Head₁ ≤ₚ L-SAT 3（输出长恒 24，落进族成员 n=24）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 编码（24 格 = 池 3 的 clauseW 12 × 2 子句）：
--   真串 = 全 T₁   ⟹ 两子句皆 (σ₊,0)³ ⟹ 可满足（a₀ = T₁）
--   假串 = 前 12 全 T₁（子句 A = (σ₊,0)³）+ 后 12 按 [T₀,T₁,·] 三组
--          （子句 B = (σ₋,0)³）⟹ A 要 a₀ = T₁、B 要 a₀ = T₂ ⟹ 不可满足
-- 关键点：每文字只需「sign 格 + onehot 首格」，故 24 格落在池 3 的
-- 重叠编码（stride 3、宽 m+2）下依然解出 (σ₊,0) / (σ₋,0)。

SVR-true24 : Vec Trit 24
SVR-true24 = T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  []

SVR-false24 : Vec Trit 24
SVR-false24 = T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₀ ∷
  T₁ ∷
  T₁ ∷
  T₀ ∷
  T₁ ∷
  T₁ ∷
  T₀ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  T₁ ∷
  []

-- 池核对：n = 24 的族池恰为 3 ⟹ 目标就是 SF-LSAT-fam 24
SVR-check-pool : SF-wlog3 24 ≡ 3
SVR-check-pool = refl

-- 子句数核对：24 / clauseW 3 = 2
SVR-check-clauses : 24 / clauseW 3 ≡ 2
SVR-check-clauses = refl

-- 真串可满足：见证 a = (T₁,T₁,T₁,T₁)
SVR-true-sat : Σ (Asg 3) (λ a → satFormula a (decFormula 3 24 SVR-true24) ≡ true)
SVR-true-sat = (T₁ ∷ T₁ ∷ T₁ ∷ T₁ ∷ []) , refl

-- 假串不可满足：三值 a₀ 全灭（A 要 T₁、B 要 T₂）
SVR-false-unsat : ∀ (a : Asg 3) → satFormula a (decFormula 3 24 SVR-false24) ≡ false
SVR-false-unsat (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) with a₀
... | T₀ = refl
... | T₁ = refl
... | T₂ = refl

-- 归约映射：看首位（记账 1 步），输出 24 格真串或假串
SVR-map : (n : ℕ) → Vec Trit n → Counted (Vec Trit 24)
SVR-map n x = mkCnt (if isT₁ (headT x) then SVR-true24 else SVR-false24) 1

-- 族成员同一：池 3 = w(24) ⟹ L-SAT 3 就是族在 n = 24 的成员
SVR-fam-member : ∀ (y : Vec Trit 24) → L-SAT 3 24 y ⇔ SF-LSAT-fam 24 y
SVR-fam-member y = (λ l → l) , (λ l → l)

-- →：首位 T₁ ⟹ 输出真串 ⟹ 可满足
SVR-→ : ∀ (n : ℕ) (x : Vec Trit n)
  → headT x ≡ T₁ → L-SAT 3 24 (value (SVR-map n x))
SVR-→ n x h rewrite h = SVR-true-sat

-- 假 ≡ 真 无居民（任意目标由它空洞成立）
SVR-no : ∀ {A : Set} → false ≡ true → A
SVR-no ()

-- ←：可满足 ⟹ 首位 T₁（T₀/T₂ 时输出假串，而假串对一切见证为假）
SVR-← : ∀ (n : ℕ) (x : Vec Trit n)
  → L-SAT 3 24 (value (SVR-map n x)) → headT x ≡ T₁
SVR-← n x (a , eq) with headT x
... | T₁ = refl
... | T₀ = SVR-no (trans (sym (SVR-false-unsat a)) eq)
... | T₂ = SVR-no (trans (sym (SVR-false-unsat a)) eq)

-- ★ 归约：L-Head₁ ≤ₚ L-SAT 3（SAT 归约的最小真实例）
SVR-head-SAT : Reduces L-Head₁ (L-SAT 3)
SVR-head-SAT = record
  { r-out = λ _ → 24
  ; r-mono-out = λ _ → ≤-refl
  ; r-map = SVR-map
  ; r-bound = λ _ → 24
  ; r-mono = λ _ → ≤-refl
  ; r-pos = λ _ → s≤s z≤n
  ; r-len = λ _ → ≤-refl
  ; r-cost = λ _ _ → s≤s z≤n
  ; r-correct = λ n x → SVR-→ n x , SVR-← n x }

-- ★ 族形：同一归约，目标显式写成渐近族（n = 24 的成员）
SVR-head-fam : Reduces L-Head₁ (λ n y → SF-LSAT-fam n y)
SVR-head-fam = record
  { r-out = λ _ → 24
  ; r-mono-out = λ _ → ≤-refl
  ; r-map = SVR-map
  ; r-bound = λ _ → 24
  ; r-mono = λ _ → ≤-refl
  ; r-pos = λ _ → s≤s z≤n
  ; r-len = λ _ → ≤-refl
  ; r-cost = λ _ _ → s≤s z≤n
  ; r-correct = λ n x →
      (λ l → proj₁ (SVR-fam-member (value (SVR-map n x))) (SVR-→ n x l))
      , (λ l → SVR-← n x (proj₂ (SVR-fam-member (value (SVR-map n x))) l)) }

-- 推论（框架拼装）：head 语言因此也在 NP 中——不用另建验证器，
-- 直接由「SAT 族 ∈ NP（SATFam §6）+ 本归约」经 red-preserves-NP 落出。
SVR-head-in-NP : InNP L-Head₁
SVR-head-in-NP = red-preserves-NP (sat-in-NP 3) SVR-head-SAT

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层（refl 枚举）
-- ────────────────────────────────────────────────────────────────────

-- 映射分支：首位 T₁ → 真串；首位 T₀ → 假串（各 1 步账目）
SVR-check-map-T₁ : value (SVR-map 1 (T₁ ∷ [])) ≡ SVR-true24
SVR-check-map-T₁ = refl

SVR-check-map-T₀ : value (SVR-map 1 (T₀ ∷ [])) ≡ SVR-false24
SVR-check-map-T₀ = refl

SVR-check-map-steps : ∀ (n : ℕ) (x : Vec Trit n) → steps (SVR-map n x) ≡ 1
SVR-check-map-steps n x = refl

-- 复合的界/输出长：red-trans 的输出长 = 第二段的输出长 ∘ 第一段
SVR-check-comp-out : Reduces.r-out (red-trans SVR-head-SAT (red-refl (L-SAT 3))) 100
  ≡ 24
SVR-check-comp-out = refl

-- 框架落出的 NP 见证宽度：suc (池 3) = 4；代价界 24 + p(24) = 24 + (3·24+1) = 97
SVR-check-NP-wit : InNP.np-witLen SVR-head-in-NP 5 ≡ 4
SVR-check-NP-wit = refl

SVR-check-NP-p : InNP.np-p SVR-head-in-NP 1 ≡ 97
SVR-check-NP-p = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   **NP-难（∀ L ∈ NP，L ≤ₚ SAT 族）未证** ⟹ 本库不声称 SAT 族 NP-完备。
--       缺口精确为：InNP 的 np-verifier 是任意 Agda 总函数（无转移表），
--       函数 → CNF 需要「计算迹编码」（tableau）。可行路径有两条，均属 W2：
--       (a) 先给 InNP 加机器可实现前提（TM 转移表 + 步数界），再做
--           Cook–Levin tableau（变量 = (时刻, 位置, 符号/状态)，子句 = 局部
--           一致性）——库内 TM 无通用机（TuringMachine §5(iii) 立界），
--           故需先建编码/解释器；
--       (b) Fagin 路线（ESO 描述 ⟹ 多项式层级台面）——同样依赖机器编码。
-- (ii)  归约输出长取 n-only（r-out : ℕ → ℕ）：length-respecting。输出长随
--       内容变的归约需要见证集 cast（Vec 截断/重填），NPClass §5(ii) 同立。
-- (iii) 归约映射的代价只看「记账」r-cost（steps ≤ r-bound n）；机器可执行性
--       维持 SATMBridge 的边界（控制结构可实现，寻址需 multi-tape/自含头）。
-- (iv)  本件的真归约实例是**单点**（输出长恒 24，落进族成员 n = 24），不是
--       「族整体」的归约族：族形归约（对每个 n 给出族成员）需要归约参数化于
--       池，属 Cook–Levin 同族工作。
-- (v)   推论 SVR-head-in-NP 是框架自洽核对（由「SAT_m ∈ NP」+ 归约落出
--       head 语言 ∈ NP，与 PClass 独立构造的 head-P/inP⇒inNP 是同一事实的
--       两条路径），非新复杂度类结果。

-- 0 postulate / 0 hole。
