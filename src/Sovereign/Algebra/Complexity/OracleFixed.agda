{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.OracleFixed
-- 固定-oracle 语义——PvsNP 程序批三 OF（BGS 非平凡化前置）
--
-- 定理意义：OracleClasses 的 oracle 设计是「oracle 无关正确性」（其头注 (b)），
-- OracleCollapse 据此证明 BGS₁ 类前提退化为 P=NP 同义反复
-- （OCX-bgs₁-degenerate）——保守设计下非平凡相对化不可表达。本件换语义：
-- 正确性量化域从「一切 oracle 实例」收敛为「逐点吻合固定 oracle A 的实例」，
-- 得 OF-InP / OF-InNP；退化链由此断裂——BGS₁ 前提在固定语义下获得真实
-- 表达力（不再是 P=NP 同义反复）。
--
-- funext 绕行机制（本件核心，回应 OracleClasses 立界 (ii)）：「固定 A 正确性」
-- 的朴素形要求把「模拟 oracle 上的求值」换回「A 上的求值」，需函数外延相等
-- （funext，不在库公理集）。本件把「A′ 逐点吻合 A」作为 Π 型前提
-- (agree : ∀ y → A′ y ≡ A (mn n) y) 显式携带在 complete/sound/cost/qcount 的量化
-- 域里：Π 型前提的引入只需逐点给证据（λ y → …），消去只需对具体 y 实例化
-- ——全程在命题相等层操作，不触碰函数相等，0 funext。OF-eliminate 中
-- value/complete/sound 保持字段直接应用（定义性，零 congruence）：oc0-decider
-- 的值字段定义性就是 of-decider 在模拟 oracle 上的值，of-complete 以
-- (A′ := 模拟 oracle，agree := OF-sim-agree) 直接给出结论。对照旧设计：该
-- 替换需 cong 值字段 + funext 换 oracle——合法性缺口由 agree 前提内化。
--
-- 三存活定理：OF-p⊆np（P^A ⊆ NP^A，§4）、OF-eliminate（A ∈ P ⟹ oracle 可
-- 消除，§5）、OF-np-lift（普通 NP 免费提升，§6）。strip 断裂见 §7：旧
-- OCX-inp-strip 的「取 λ _ → false 剥槽」在固定语义下失去普遍合法性，其精确
-- 合法域 = 槽 oracle 逐点吻合 A（类型层定理 OF-inp-strip-at）——退化链断。
--
-- 分级标注：〔结构定义〕〔结构证明〕〔refl 枚举〕〔立界注记〕（同库惯例）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.OracleFixed where

open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤m+n)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁)
open import Sovereign.Algebra.Complexity.TimeBound
  using (value; steps; Mono; Pos; polySuc; polySuc-mono; polySuc-pos;
         mono-+ʳ)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass using (TritLang; InP)
open import Sovereign.Algebra.Complexity.NPClass using (InNP)
open import Sovereign.Algebra.Complexity.OracleClasses
  using (OC-CountedQ; oc-cntq; oc-value; oc-steps; oc-queries;
         oc-cqConst; oc-cqQuery;
         OC-Oracle; OC-OracleFam; OC-LangOf;
         OC-NoQuery; oc-collapse-p-mono)

-- ────────────────────────────────────────────────────────────────────
-- §1 Bool 吻合引理〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 接受域单点否证（策略 C：否定证明，空模式）。
-- 两案（true/false 与 false/true）中把前提 h 应用于 refl 得到的都是
-- false ≡ true，故只需这一个否证引理。
OF-false≢true : false ≡ true → ⊥
OF-false≢true ()

-- b 与 c 接受域相同则值相等——Bool 四案枚举。这是 OF-eliminate 中
-- 「模拟 oracle 逐点吻合 A」的唯一步（比 oc-collapse 多出的关键件）。
OF-boolAgree : ∀ (b c : Bool)
             → (b ≡ true → c ≡ true)
             → (c ≡ true → b ≡ true)
             → b ≡ c
OF-boolAgree true  true  _  _  = refl
OF-boolAgree true  false h₁ _  = ⊥-elim (OF-false≢true (h₁ refl))
OF-boolAgree false true  _  h₂ = ⊥-elim (OF-false≢true (h₂ refl))
OF-boolAgree false false _  _  = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 固定-oracle P 类 OF-InP〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 与 OC-InP 的唯一差别（设计核心）：complete/sound/cost/qcount 的量化域从
-- 「一切 oracle 实例 A′」收敛为「逐点吻合 A 的实例 A′」——前提
-- (agree : ∀ y → A′ y ≡ A (mn n) y) 是 Π 型，携带它不需要 funext（头注）。
record OF-InP (mn : ℕ → ℕ) (A : OC-OracleFam) (L : TritLang) : Set₁ where
  field
    of-p        : ℕ → ℕ                -- 代价界（步数）
    of-p-mono   : Mono of-p            -- 〔结构证明〕
    of-p-pos    : Pos of-p             -- 〔结构证明〕
    of-q        : ℕ → ℕ                -- 查询次数界
    of-q-mono   : Mono of-q            -- 〔结构证明〕
    of-q-pos    : Pos of-q             -- 〔结构证明〕
    of-decider  : (n : ℕ) → Vec Trit n → OC-Oracle (mn n) → OC-CountedQ
    of-complete : ∀ n x (A′ : OC-Oracle (mn n))
                    (agree : ∀ y → A′ y ≡ A (mn n) y) → L n x →
                  oc-value (of-decider n x A′) ≡ true          -- 〔结构证明〕
    of-sound    : ∀ n x (A′ : OC-Oracle (mn n))
                    (agree : ∀ y → A′ y ≡ A (mn n) y) →
                  oc-value (of-decider n x A′) ≡ true → L n x  -- 〔结构证明〕
    of-cost     : ∀ n x (A′ : OC-Oracle (mn n))
                    (agree : ∀ y → A′ y ≡ A (mn n) y) →
                  oc-steps (of-decider n x A′) ≤ of-p n
    of-qcount   : ∀ n x (A′ : OC-Oracle (mn n))
                    (agree : ∀ y → A′ y ≡ A (mn n) y) →
                  oc-queries (of-decider n x A′) ≤ of-q n

-- ────────────────────────────────────────────────────────────────────
-- §3 固定-oracle NP 类 OF-InNP〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 验证器范式，量化域同 §2（逐点吻合 A）。
record OF-InNP (mn : ℕ → ℕ) (A : OC-OracleFam) (L : TritLang) : Set₁ where
  field
    ofnp-p        : ℕ → ℕ
    ofnp-p-mono   : Mono ofnp-p
    ofnp-p-pos    : Pos ofnp-p
    ofnp-q        : ℕ → ℕ
    ofnp-q-mono   : Mono ofnp-q
    ofnp-q-pos    : Pos ofnp-q
    ofnp-witLen   : ℕ → ℕ              -- 见证长度界
    ofnp-w-mono   : Mono ofnp-witLen
    ofnp-verifier : (n : ℕ) → Vec Trit n → Vec Trit (ofnp-witLen n) →
                    OC-Oracle (mn n) → OC-CountedQ
    ofnp-complete : ∀ n x (w : Vec Trit (ofnp-witLen n)) (A′ : OC-Oracle (mn n))
                      (agree : ∀ y → A′ y ≡ A (mn n) y) → L n x →
                    Σ (Vec Trit (ofnp-witLen n))
                      (λ w′ → oc-value (ofnp-verifier n x w′ A′) ≡ true)
    ofnp-sound    : ∀ n x (w : Vec Trit (ofnp-witLen n)) (A′ : OC-Oracle (mn n))
                      (agree : ∀ y → A′ y ≡ A (mn n) y) →
                    oc-value (ofnp-verifier n x w A′) ≡ true → L n x
    ofnp-cost     : ∀ n x (w : Vec Trit (ofnp-witLen n)) (A′ : OC-Oracle (mn n))
                      (agree : ∀ y → A′ y ≡ A (mn n) y) →
                    oc-steps (ofnp-verifier n x w A′) ≤ ofnp-p n
    ofnp-qcount   : ∀ n x (w : Vec Trit (ofnp-witLen n)) (A′ : OC-Oracle (mn n))
                      (agree : ∀ y → A′ y ≡ A (mn n) y) →
                    oc-queries (ofnp-verifier n x w A′) ≤ ofnp-q n

-- ────────────────────────────────────────────────────────────────────
-- §4 存活定理一：OF-p⊆np〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 固定语义下 P^A ⊆ NP^A 仍闭合（镜像 oc-P⊆NP）：空见证（Vec Trit 0 仅 []）、
-- 验证器 = 判定器（oracle 实参透传）、界逐字继承；agree 前提透传——
-- 同一次量化，语义不变。
OF-p⊆np : ∀ {mn A L} (dp : OF-InP mn A L) → OF-InNP mn A L
OF-p⊆np dp = record
  { ofnp-p        = OF-InP.of-p dp
  ; ofnp-p-mono   = OF-InP.of-p-mono dp
  ; ofnp-p-pos    = OF-InP.of-p-pos dp
  ; ofnp-q        = OF-InP.of-q dp
  ; ofnp-q-mono   = OF-InP.of-q-mono dp
  ; ofnp-q-pos    = OF-InP.of-q-pos dp
  ; ofnp-witLen   = λ _ → 0
  ; ofnp-w-mono   = λ _ → z≤n
  ; ofnp-verifier = λ n x _ A′ → OF-InP.of-decider dp n x A′
  ; ofnp-complete = λ n x _ A′ agree l →
      [] , OF-InP.of-complete dp n x A′ agree l
  ; ofnp-sound    = λ n x _ A′ agree v → OF-InP.of-sound dp n x A′ agree v
  ; ofnp-cost     = λ n x _ A′ agree → OF-InP.of-cost dp n x A′ agree
  ; ofnp-qcount   = λ n x _ A′ agree → OF-InP.of-qcount dp n x A′ agree }

-- ────────────────────────────────────────────────────────────────────
-- §5 存活定理二：OF-eliminate（A ∈ P ⟹ oracle 可消除）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 模拟 oracle 的逐点吻合（比 oc-collapse 多 ~8 行的关键步）：dA 判定
-- OC-LangOf A（查询串 y 的成员性 = A m y ≡ true），故其值与 A m y 接受域
-- 相同——sound 给 (值 ≡ true → A m y ≡ true)，complete 的前提恰是
-- (A m y ≡ true → 值 ≡ true)，OF-boolAgree 拼合。全程命题相等层，0 funext。
OF-sim-agree : ∀ {A : OC-OracleFam} (dA : InP (OC-LangOf A))
                 (m : ℕ) (y : Vec Trit m)
               → value (InP.decider dA m y) ≡ A m y
OF-sim-agree {A} dA m y =
  OF-boolAgree (value (InP.decider dA m y)) (A m y)
    (InP.p-sound dA m y)        -- 值≡true → sound → OC-LangOf A m y ≡ A m y≡true
    (InP.p-complete dA m y)     -- A m y≡true（= complete 前提 OC-LangOf）→ 值≡true

-- 消除定理（镜像 oc-collapse，产出同形 OC-NoQuery L），两处更新——
--   (a) oracle 槽填模拟 oracle sim n = λ y → value (InP.decider dA (mn n) y)，
--       逐点吻合证据 sim-agree n = OF-sim-agree dA (mn n)（上件）；
--   (b) value/complete/sound 保持字段直接应用（定义性，零 congruence）：
--       oc0-decider 的值字段定义性就是 of-decider 在 sim n 上的值，
--       of-complete 以 (A′ := sim n, agree := sim-agree n) 直接给出 oc0 的
--       结论——对照旧设计：该替换需 cong 值字段 + funext 换 oracle，合法性
--       缺口由 agree 前提内化（头注）。
-- 账目同 oc-collapse 保守上界形（dec 自账 + 查询次数 × dA 界），界引理
-- oc-collapse-p-mono 直接复用；精确形 trace-passing 立界（§9 (ii)）。
OF-eliminate : ∀ {mn A L} (mn-mono : Mono mn)
               (dA : InP (OC-LangOf A)) (dp : OF-InP mn A L) → OC-NoQuery L
OF-eliminate {mn} {A} mn-mono dA dp = record
  { oc0-p      = λ n → OF-InP.of-p dp n + OF-InP.of-q dp n * InP.p dA (mn n)
  ; oc0-p-mono = oc-collapse-p-mono (OF-InP.of-p dp) (OF-InP.of-q dp)
                                    (InP.p dA) mn
                                    (OF-InP.of-p-mono dp) (OF-InP.of-q-mono dp)
                                    (InP.p-mono dA) mn-mono
  ; oc0-p-pos  = λ n → ≤-trans (OF-InP.of-p-pos dp n)
                               (m≤m+n (OF-InP.of-p dp n)
                                      (OF-InP.of-q dp n * InP.p dA (mn n)))
  ; oc0-decider = λ n x →
      let c = OF-InP.of-decider dp n x (sim n)
      in  oc-cntq (oc-value c)
                  (oc-steps c + OF-InP.of-q dp n * InP.p dA (mn n)) 0
  ; oc0-noq      = λ n x → refl
  ; oc0-complete = λ n x l → OF-InP.of-complete dp n x (sim n) (sim-agree n) l
  ; oc0-sound    = λ n x v → OF-InP.of-sound dp n x (sim n) (sim-agree n) v
  ; oc0-cost     = λ n x →
      mono-+ʳ (OF-InP.of-q dp n * InP.p dA (mn n))
              (OF-InP.of-cost dp n x (sim n) (sim-agree n)) }
  where
  sim : (n : ℕ) → OC-Oracle (mn n)
  sim n = λ y → value (InP.decider dA (mn n) y)

  sim-agree : (n : ℕ) → ∀ y → sim n y ≡ A (mn n) y
  sim-agree n = OF-sim-agree dA (mn n)

-- ────────────────────────────────────────────────────────────────────
-- §6 存活定理三：OF-np-lift〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 镜像 OCX-np-lift：验证器忽略 oracle 槽（查询账记 0），InNP 字段直接搬入；
-- 固定语义下各字段带 agree 前提但与 A′ 无关地成立（前提吸收：证据不消费
-- agree）。查询界取常数 1（Pos 排除零界；真实账目恒 0 ≤ 1）。
OF-np-lift : ∀ {mn A L} (np : InNP L) → OF-InNP mn A L
OF-np-lift np = record
  { ofnp-p        = InNP.np-p np
  ; ofnp-p-mono   = InNP.np-p-mono np
  ; ofnp-p-pos    = InNP.np-p-pos np
  ; ofnp-q        = λ _ → 1
  ; ofnp-q-mono   = λ _ → ≤-refl
  ; ofnp-q-pos    = λ _ → s≤s z≤n
  ; ofnp-witLen   = InNP.np-witLen np
  ; ofnp-w-mono   = InNP.np-w-mono np
  ; ofnp-verifier = λ n x w A′ →
      oc-cntq (value (InNP.np-verifier np n x w))
              (steps (InNP.np-verifier np n x w)) 0
  ; ofnp-complete = λ n x w A′ agree l → InNP.np-complete np n x l
  ; ofnp-sound    = λ n x w A′ agree v → InNP.np-sound np n x w v
  ; ofnp-cost     = λ n x w A′ agree → InNP.np-cost np n x w
  ; ofnp-qcount   = λ n x w A′ agree → z≤n }

-- ────────────────────────────────────────────────────────────────────
-- §7 strip 合法域与断裂机制坐标〔结构证明 + 立界注记〕
-- ────────────────────────────────────────────────────────────────────

-- 旧 OCX-inp-strip 取 λ _ → false 剥槽在 oracle 无关语义下免费；固定语义下
-- complete/sound 只对吻合 A 的实例承诺，其合法性精确收敛为「A 恒 false」
-- （下件）——strip 断 ⟹ 退化链断 ⟹ BGS₁ 前提获得真实表达力（头注）。
--
-- （¬ 泛型 strip 的全称形态不可构造性证明——需具体「不可判定 A」的元层
-- 论证，立界见 §9 (iii)；本节的可证形态已把断裂点钉在 agree 前提上。）

OF-inp-strip-at : ∀ {mn A L} (dp : OF-InP mn A L)
                  → (A₀ : (n : ℕ) → OC-Oracle (mn n))
                  → (∀ n (y : Vec Trit (mn n)) → A₀ n y ≡ A (mn n) y)
                  → InP L
OF-inp-strip-at dp A₀ agree = record
  { p          = OF-InP.of-p dp
  ; p-mono     = OF-InP.of-p-mono dp
  ; p-pos      = OF-InP.of-p-pos dp
  ; decider    = λ n x →
      mkCnt (oc-value (OF-InP.of-decider dp n x (A₀ n)))
            (oc-steps (OF-InP.of-decider dp n x (A₀ n)))
  ; p-complete = λ n x l → OF-InP.of-complete dp n x (A₀ n) (agree n) l
  ; p-sound    = λ n x v → OF-InP.of-sound dp n x (A₀ n) (agree n) v
  ; p-cost     = λ n x → OF-InP.of-cost dp n x (A₀ n) (agree n) }

-- λ _ → false 槽的精确合法条件：A 恒 false（退化 oracle 才可裸剥）——
-- 机制坐标：strip 断裂点 = agree 前提在 A 非恒 false 时无证据。
OF-inp-strip-false-ok : ∀ {mn A L} (dp : OF-InP mn A L)
                        → (∀ n (y : Vec Trit (mn n)) → A (mn n) y ≡ false)
                        → InP L
OF-inp-strip-false-ok dp A-false =
  OF-inp-strip-at dp (λ n _ → false) (λ n y → sym (A-false n y))

-- ────────────────────────────────────────────────────────────────────
-- §8 核对层〔refl 枚举 + 非空洞实例〕
-- ────────────────────────────────────────────────────────────────────

-- 具体固定 oracle（恒接受表）与其 P 判定器（恒接受，1 步）——
-- OF-sim-agree / OF-eliminate 的非空洞实例化基座。
OF-A-true : OC-OracleFam
OF-A-true _ _ = true

OF-dA-true : InP (OC-LangOf OF-A-true)
OF-dA-true = record
  { p          = polySuc
  ; p-mono     = polySuc-mono
  ; p-pos      = polySuc-pos
  ; decider    = λ _ _ → mkCnt true 1
  ; p-complete = λ _ _ _ → refl
  ; p-sound    = λ _ _ _ → refl
  ; p-cost     = λ _ _ → s≤s z≤n }

-- 模拟吻合在具体点成立（OF-sim-agree 实例的定义性归约）
check-OF-sim : value (InP.decider OF-dA-true 2 (T₁ ∷ T₀ ∷ [])) ≡ true
check-OF-sim = refl

check-OF-sim-point : value (InP.decider OF-dA-true 0 []) ≡ OF-A-true 0 []
check-OF-sim-point = refl

-- 查询长 = 输入长的调度；查询形固定-oracle 判定器（查输入本身，1 次查询）
OF-mn-id : ℕ → ℕ
OF-mn-id n = n

OF-dp-query : OF-InP OF-mn-id OF-A-true (OC-LangOf OF-A-true)
OF-dp-query = record
  { of-p        = λ n → suc (suc n)
  ; of-p-mono   = λ h → s≤s (s≤s h)
  ; of-p-pos    = λ _ → s≤s z≤n
  ; of-q        = polySuc
  ; of-q-mono   = polySuc-mono
  ; of-q-pos    = polySuc-pos
  ; of-decider  = λ n x A′ → oc-cqQuery (A′ x) (oc-cqConst false)
  ; of-complete = λ n x A′ agree l → trans (agree x) l
  ; of-sound    = λ _ _ _ _ _ → refl
  ; of-cost     = λ _ _ _ _ → s≤s (s≤s z≤n)
  ; of-qcount   = λ _ _ _ _ → s≤s z≤n }

-- 消除定理实例：OF-eliminate 作用于上述真实例（mn-mono = 恒等单调）
OF-elim-inst : OC-NoQuery (OC-LangOf OF-A-true)
OF-elim-inst = OF-eliminate (λ h → h) OF-dA-true OF-dp-query

-- 消除后：零查询（oc0-noq 的具体点）且值保持
check-OF-elim-noq :
  oc-queries (OC-NoQuery.oc0-decider OF-elim-inst 2 (T₁ ∷ T₀ ∷ [])) ≡ 0
check-OF-elim-noq = refl

check-OF-elim-accept :
  oc-value (OC-NoQuery.oc0-decider OF-elim-inst 2 (T₁ ∷ T₀ ∷ [])) ≡ true
check-OF-elim-accept = refl

-- ────────────────────────────────────────────────────────────────────
-- §9 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   变长查询仍立界：查询槽长 OC-Oracle (mn n) 在计算前固定；经典 OTM
--       的查询长度是计算内部量。本件沿用 OracleClasses 立界 (i)，未触碰。
-- (ii)  trace-congruence 完全版立界：OF-eliminate 的账目为保守上界形
--       （dec 自账 + 查询次数 × dA 界）；精确合成需判定器返回查询清单
--       （trace-passing），本件不引入（同 OracleClasses 立界 (iii)）。
-- (iii) strip 断裂的全称否定形态（¬ ∃ 泛型剥槽函数）不可构造性证明立界：
--       需具体化「InP (OC-LangOf A) 不可居住」的 A——元层论证（所有可写
--       函数皆可判定），类型层无可达矛盾；本件以 §7 的合法域刻画
--       （OF-inp-strip-at + OF-inp-strip-false-ok）钉住断裂机制坐标。
-- (iv)  BGS₁ / BGS₂ 世界件（PSPACE-complete / 对角化 oracle 构造）立界：
--       固定语义下前提不再自动退化（本件非平凡化通道已打开），但 ∃A 的
--       具体构造仍为世界级深件，status = 0，本件不设陈述 record（旧
--       OC-BGS₁/OC-BGS₂ 形态对其旧记录仍真，作设计边界文档保留）。
-- (v)   decider / verifier 的 OTM 实现桥——同 PClass §6(i)。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
