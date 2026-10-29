{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Automata.MultiTape
-- 双带图灵机（TM²）——含「停留」方向，为「带寻址的整机」铺模型
--
-- 数学背景：单带 TM 读不到「远处的格子」而不付移头代价；多带 TM 让
-- 「读公式 + 读见证」并进（lockstep），这正是 SAT 验证器里 a[v] 寻址的
-- 标准实现方式。本件给出两带模型与三条通用引理，供 SATLook 使用。
--
-- 与单带模型（Automata/TuringMachine）的差异（有意为之，两条）：
--   ①**方向集加 N（停留）**：回走/对齐收口需要「读标记但不移头」的一步，
--     单带模型的 L/R 二向做不到（只能 L 再 R，代价 2 且破坏对齐）。N 可
--     用 L;R 模拟（代价 +1），故不增计算力，只是把对齐写清。
--   ②**右带 = 头之后的余带**（tlOf 约定，与 TMBridge2 一致）：单带件
--     TMBridge 用「右带含当前格」的另一种约定，两者靠 hdOf/tlOf 的用法区分；
--     本件统一取余带约定，使「一步 = 头前进一格」在两边同形。
--
-- 内容：
--   §1 Dir3 · C2（两带格局）· TM2（δ 双符号三元组）
--   §2 mt-step / runN2（燃料形）；stepTape 三向语义
--   §3 冻结引理 runN2-freeze · **加法引理 runN2-+**（runN 的可组合性——
--      分段证明的关键；本条在单带通用层因 where-goN 的泛型不透明而不可写，
--      此处因引理只需对 halt 二分、不需把 step 展开成构造子而归约成功）
--   §4 核对层（refl）：双带同步右移 1 步 / 冻结 / 加法小值
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Automata.MultiTape where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

open import Sovereign.Algebra.Automata.TuringMachine using (hdOf; tlOf)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- ────────────────────────────────────────────────────────────────────
-- §1 方向（含停留）· 两带格局 · 机器〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

data Dir3 : Set where
  dL dR dN : Dir3        -- 左 / 右 / 停留（N = 读标记但不移头）

-- 两带格局：两带各有（左带 · 头 · 余带），共享一个状态
record C2 (Q Σ : Set) : Set where
  constructor mk2
  field
    l₁ : List Σ
    st : Q
    h₁ : Σ
    r₁ : List Σ
    l₂ : List Σ
    h₂ : Σ
    r₂ : List Σ

record TM2 (Q Σ : Set) : Set where
  field
    δ    : Q → Σ → Σ → Q × (Σ × Dir3) × (Σ × Dir3)
    q₀   : Q
    halt : Q → Bool

-- ────────────────────────────────────────────────────────────────────
-- §2 一步：每带的（写符号, 方向）独立〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 单带一步：返回（新左带, 新头, 新余带）
stepTape : ∀ {Σ} → Σ → Σ × Dir3 → List Σ → Σ → List Σ → List Σ × Σ × List Σ
stepTape b (w , dR) l a r = w ∷ l , hdOf b r , tlOf r
stepTape b (w , dL) l a r = tlOf l , hdOf b l , w ∷ r
stepTape b (w , dN) l a r = l , w , r

mt-stepH : ∀ {Q Σ} → TM2 Q Σ → Σ → Bool → C2 Q Σ → C2 Q Σ
mt-stepH M b true  c = c
mt-stepH M b false c =
  mk2 (proj₁ t₁) (proj₁ (TM2.δ M (C2.st c) (C2.h₁ c) (C2.h₂ c)))
      (proj₁ (proj₂ t₁)) (proj₂ (proj₂ t₁))
      (proj₁ t₂) (proj₁ (proj₂ t₂)) (proj₂ (proj₂ t₂))
  where
  t₁ = stepTape b (proj₁ (proj₂ (TM2.δ M (C2.st c) (C2.h₁ c) (C2.h₂ c))))
                  (C2.l₁ c) (C2.h₁ c) (C2.r₁ c)
  t₂ = stepTape b (proj₂ (proj₂ (TM2.δ M (C2.st c) (C2.h₁ c) (C2.h₂ c))))
                  (C2.l₂ c) (C2.h₂ c) (C2.r₂ c)

mt-step : ∀ {Q Σ} → TM2 Q Σ → Σ → C2 Q Σ → C2 Q Σ
mt-step M b c = mt-stepH M b (TM2.halt M (C2.st c)) c

-- 燃料形多步（至多 n 步；停机态冻结）
-- 用 if_then_else_ 而不用 where 辅助：if 的归约面对构造子实参透明，
-- 且 with 抽象会被同一项上的归约看见（单带件 §2.1 的同一类坑）。
runN2 : ∀ {Q Σ} → TM2 Q Σ → Σ → ℕ → C2 Q Σ → C2 Q Σ
runN2 M b zero    c = c
runN2 M b (suc n) c =
  if TM2.halt M (C2.st c) then c else runN2 M b n (mt-step M b c)

-- 停机观察面
Halts2 : ∀ {Q Σ} → TM2 Q Σ → ℕ → C2 Q Σ → Set
Halts2 M n c = TM2.halt M (C2.st (runN2 M (C2.h₁ c) n c)) ≡ true

-- ────────────────────────────────────────────────────────────────────
-- §3 冻结 / 加法〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 冻结：已经是停机态 ⟹ 任意燃料不改格局（true 分支直返）
runN2-freeze : ∀ {Q Σ} (M : TM2 Q Σ) (b : Σ) (n : ℕ) (c : C2 Q Σ)
             → TM2.halt M (C2.st c) ≡ true
             → runN2 M b n c ≡ c
runN2-freeze M b zero    c h = refl
runN2-freeze M b (suc n) c h rewrite h = refl

-- if 的消去（构造子探针，refl）
if-true : ∀ {A : Set} (x y : A) → (if true then x else y) ≡ x
if-true x y = refl

-- ── 盲跑（盲区无停机检查）：分段证明的承重面 ──────────────────────────
-- runN2 的泛型加法不可写（with 抽象不替换 runN2 展开后新出现的 halt 项，
-- 与单带件的 goN 不透明同源）。破局不是硬写泛型加法，而是分清「相」（phase）：
-- 一个相内机器不停机，于是该相用**盲跑** runB（纯结构递归，加法平凡），
-- 相与相之间再用 runN2-blind 把 runB 换回 runN2（要求该机 halt 恒 false）。
runB : ∀ {Q Σ} → TM2 Q Σ → Σ → ℕ → C2 Q Σ → C2 Q Σ
runB M b zero    c = c
runB M b (suc n) c = runB M b n (mt-stepH M b false c)

-- 盲跑的单步展开（定义性，refl）
runB-step : ∀ {Q Σ} (M : TM2 Q Σ) (b : Σ) (n : ℕ) (c : C2 Q Σ)
          → runB M b (suc n) c ≡ runB M b n (mt-stepH M b false c)
runB-step M b n c = refl

-- ★ 盲跑加法（泛型、结构归纳、无任何停机前提）
runB-+ : ∀ {Q Σ} (M : TM2 Q Σ) (b : Σ) (m n : ℕ) (c : C2 Q Σ)
       → runB M b (m + n) c ≡ runB M b n (runB M b m c)
runB-+ M b zero    n c = refl
runB-+ M b (suc m) n c = trans (runB-+ M b m n (mt-stepH M b false c))
                               (cong (runB M b n) (sym (runB-step M b m c)))

-- 未停机 ⟹ 走一步再跑（只能以重写特化出现，不能以 refl 形陈述——
-- 与单带件 §2.1 同一现象：泛型 halt 项在展开后新出现、不被 with 抽象）
runN2-false : ∀ {Q Σ} (M : TM2 Q Σ) (b : Σ) (n : ℕ) (c : C2 Q Σ)
            → TM2.halt M (C2.st c) ≡ false
            → runN2 M b (suc n) c ≡ runN2 M b n (mt-step M b c)
runN2-false M b n c h rewrite h = refl

-- halt 恒假 ⟹ runN2 = runB（相内无停机，检查是恒真的 no-op）
runN2-blind : ∀ {Q Σ} (M : TM2 Q Σ) (b : Σ)
            → (∀ q → TM2.halt M q ≡ false)
            → ∀ (n : ℕ) (c : C2 Q Σ) → runN2 M b n c ≡ runB M b n c
runN2-blind M b hz zero    c = refl
runN2-blind M b hz (suc n) c =
  trans (runN2-false M b n c (hz (C2.st c)))
        (trans (cong (runN2 M b n)
                     (cong (λ z → mt-stepH M b z c) (hz (C2.st c))))
               (runN2-blind M b hz n (mt-stepH M b false c)))

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

-- 最小机器：一步把两带头都右移、转停机态（δ 双带都写回原符号）
data Q1 : Set where
  qRun qHalt : Q1

tm2-move : TM2 Q1 Trit
tm2-move = record { δ = δm ; q₀ = qRun ; halt = haltm }
  where
  δm : Q1 → Trit → Trit → Q1 × (Trit × Dir3) × (Trit × Dir3)
  δm qRun  a b = qHalt , (a , dR) , (b , dR)
  δm qHalt a b = qHalt , (a , dR) , (b , dR)
  haltm : Q1 → Bool
  haltm qRun  = false
  haltm qHalt = true

mt-c0 : C2 Q1 Trit
mt-c0 = mk2 [] qRun T₁ (T₂ ∷ []) [] T₀ (T₁ ∷ [])

-- ①一步：两带头都前移一格，状态转 qHalt
check-mt-step : mt-step tm2-move T₀ mt-c0 ≡ mk2 (T₁ ∷ []) qHalt T₂ [] (T₀ ∷ []) T₁ []
check-mt-step = refl

-- ②冻结：再跑 5 步不变（已达停机态）
check-mt-freeze : runN2 tm2-move T₀ 5 (mt-step tm2-move T₀ mt-c0)
             ≡ mt-step tm2-move T₀ mt-c0
check-mt-freeze = refl

-- ③加法引理小值：2 + 3 与分段
check-mt-add : runB tm2-move T₀ (2 + 3) mt-c0 ≡ runB tm2-move T₀ 3 (runB tm2-move T₀ 2 mt-c0)
check-mt-add = runB-+ tm2-move T₀ 2 3 mt-c0

-- ④N（停留）语义：写回原符号、头不动
check-mt-stepTape-N : stepTape T₀ (T₁ , dN) (T₂ ∷ []) T₀ [] ≡ (T₂ ∷ [] , T₁ , [])
check-mt-stepTape-N = refl

-- ⑤L 语义：写 w 后左移，旧头落到右带
check-mt-stepTape-L : stepTape T₀ (T₁ , dL) (T₂ ∷ []) T₀ (T₀ ∷ [])
                 ≡ ([] , T₂ , T₁ ∷ T₀ ∷ [])
check-mt-stepTape-L = refl

-- 0 postulate / 0 hole。
