{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATLook
-- 含寻址：两带 lockstep 解变元号并取见证值（SATMBridge 立界 (i) 的机器侧）
--
-- 【本件闭合什么】SATMBridge 的验证器用「配对单元」编码：a[v] 的读取被编码层
-- 预先合成、不计机内步数。本件把这一步搬进机器：
--
--   带 1：逐文字放 [sign, o₀ … o_m]（onehot 变元号原样，§3 的 os），末格 sentinel
--   带 2：**一份**见证块 [⊢, a₀ … a_m, ⊣]（全公式共用，回走相每字把它完全复原）
--
-- 机器从 (sign, ⊢) 出发读符号，然后把带 1 的 onehot 与带 2 的见证**锁步**
-- 前移：见到首个 T₁ 就把该处见证值抄进状态，此后不再覆盖（= fromOneHot 的
-- 「首个 T₁」语义；LK-pick-cells 把两处钉死）。于是「解变元号 + 取 a[v]」
-- 由机器完成，不再是编码层的免费午餐。
--
-- 【计账（精确等式，非 O 记法）】
--   单文字引擎：1（符号步）+ (m+1)（锁步）+ 1（相迁移）+ (m+3)（回走）= **2m+6**
--               （LK-cycle / LK-cycleR / LK-cycleF / LK-cycleS）
--   整公式：    每文字再付 1 步收口 fold ⟹ **2m+7**/文字，L 个文字 = L·(2m+7)
--               （LK-runL，沿文字表结构归纳；线性计账推论 LK-runL-steps）
--   整机：      c 个子句 = 3c 个文字 = **3c·(2m+7)** 步
--               （LK-run-formula / LK-run-formula-steps；原始 trit 串入 = LK-run-stream）
--   对齐：      = 抽象验证器账目 steps(satFormulaC) × (2m+7)（LK-cost）
--               ⟹ 常数因子模拟；差额全在「每个文字独立付一次寻址」
--
-- 【OR/AND 累计在状态里（skill 附录 9 ①）】
--   相位 LK-Ph = (pos, ck, fk) 是状态的一部分：pos 为子句内位置（T₂ 收口），
--   ck 为本子句已满足，fk 为此前各子句全满足。收口只**一条** fold 子句
--   （LK-phStep，用 ∨/∧/if 表达）——不需要对 27 个 (pos, ck, fk) 组合分案，
--   也不需要另开一条 flag 带 + 相往返（本地先例：SATMBridge.tm-sat 的
--   qP0/qP1/qP2 : Bool → Bool → Q）。
--
-- 【诚实边界（尾注 §6）】
--   (i)  带 2 只有**一份**见证块（空间 O(m)，不是 O(m·L)）：回走相把带 2 完全
--        复原（头回 ⊢、左带回 l₂、⊣ 压回同位置）⟹ 每个文字只付自己那一块
--        (m+1) 格 ⟹ 整体**线性**。⚠ 此前写的「第 j 个字回走 j(m+1) ⟹ Θ(m·L²)」
--        是错的（只有不回填时才成立）。
--   (ii) **语义已闭合**（§4i）：`LK-look-sat` 给出
--        `C2.st (runB …) ≡ qLit (T₀ , false , satFormula a (map LK-clause→lib cs))`
--        ——机器终态的 fk 就是库内 SAT 真值。桥只用两件事：`evalLit` 与机器取值
--        只差一层 Sign 解码（2 案 refl），以及 ck 左折 vs satClause 右折的一步
--        `∨-assoc`＋跨子句的 `∧-assoc`（Bool 代数，不分案）。
--   (iii) **编码器也闭合**（§4j）：`LK-run-formula` 对任意库内 `Formula m c` 成立
--        （`LK-hot` 按索引结构递归 ⟹ 往返 3 案 refl/cong，不需要 ≟/toℕ）；
--        `LK-run-stream` 再把 SATMember.decFormula 接上 ⟹ **原始 trit 串入、SAT
--        判决出**。未做的是「直接吃 decLit 的 stride-3 重叠格、不重新编码」的
--        布局桥——那是可选的省步优化，不是接口缺口（Formula 才是接口）。
--   (iv) 引擎 halt 恒假（纯相），故只用 runB；判决从**第 L·(2m+7) 步的状态**读出
--        （fk），不从停机态读出。此后 sentinel 被当成下一个文字的 sign ⟹ 机器走
--        一个幽灵文字；实例（c=1/m=0）实测 22 步进幽灵、27 步停在 qDone、28 步
--        不动（§5d 三条 refl），一般性停驻定理未证、判决亦不依赖（停驻后 fk 仍在
--        状态里）。换 runN2 要证「相内恒不停机」的封闭性（δ 的状态×双符号 ~75 案，
--        或改布局加终止符），故未做。账目对齐用常数因子形式给出：LK-cost
--        （本机步数 = 抽象账目 × (2m+7)）。

-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATLook where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Bool.Properties using (∨-assoc; ∧-assoc; ∧-identityʳ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; *-suc)
open import Data.Nat.DivMod using (_/_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; lookup; map; replicate) renaming ([] to vNil; _∷_ to _v∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Automata.MultiTape
  using (Dir3; dL; dR; dN; C2; mk2; TM2; mt-stepH; runB; runB-step; runB-+)
open import Sovereign.Algebra.Automata.TuringMachine using (hdOf; tlOf)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; signOf; fromOneHot; isT₁
       ; Lit; Clause; Formula; Asg; evalLit; satClause; satFormula
       ; clauseW; decFormula; satFormulaC; steps-satFormulaC)
open import Sovereign.Algebra.Complexity.TimeBound using (steps)

-- ────────────────────────────────────────────────────────────────────
-- §1 字母表 / 状态 / δ 表〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

data LK-Σ : Set where
  LK-b : LK-Σ              -- 空白
  LK-m : LK-Σ              -- 见证块起点标记（锁步对齐用）
  LK-e : LK-Σ              -- 见证块**终止符**（布局 ⊢ block ⊣；使循环末端形与起点同形）
  LK-t : Trit → LK-Σ       -- trit 码

-- 符号的 trit 值（非 trit 码按空白读 T₀）
LK-v : LK-Σ → Trit
LK-v (LK-t t) = t
LK-v _        = T₀

-- 状态：相位 + 构造子。
--
-- 【相位在状态里（附录 9 ①）】OR/AND 累计不另开一条带、也不靠「8 步往返」，
-- 而是放进状态三格：
--   pos —— 子句内第几个文字（T₀,T₁,T₂ 循环；T₂ = 本子句最后一个 ⟹ 收口）
--   ck  —— 「本子句已满足」（跨文字累积，收口时清零）
--   fk  —— 「此前每一子句都已满足」（收口时与 ck 合取；初值 true）
-- 于是每个文字只多付**一条** fold 步（qDone → qLit），δ 里用 ∨/∧/if 表达，
-- 不需要对 27 个 (pos, ck, fk) 组合穷举（本地先例：SATMBridge.tm-sat 的
-- qP0/qP1/qP2 : Bool → Bool → Q）。
LK-Ph : Set
LK-Ph = Trit × Bool × Bool

-- 初相位：子句首、本子句未满足、此前子句全满足（空合取）
LK-ph₀ : LK-Ph
LK-ph₀ = T₀ , false , true

-- 本文字是否是本子句的最后一个（3 文字/子句 ⟹ pos = T₂ 收口）
LK-closing : Trit → Bool
LK-closing T₂ = true
LK-closing _  = false

-- 子句内位置推进（模 3）
LK-nextT : Trit → Trit
LK-nextT T₀ = T₁
LK-nextT T₁ = T₂
LK-nextT _  = T₀

-- 收口的两条更新（本子句满足 ⟹ ck 清零并进 fk；否则 ck 继续累积）
LK-foldCk : LK-Ph → Trit → Bool
LK-foldCk (pos , ck , _) v = if LK-closing pos then false else (ck ∨ isT₁ v)

LK-foldFk : LK-Ph → Trit → Bool
LK-foldFk (pos , ck , fk) v = if LK-closing pos then (fk ∧ (ck ∨ isT₁ v)) else fk

-- 文字取值：正文字取原值，负文字取 negate（与 SATMember.evalLit 同口径——
-- 相位 fold 的输入必须已是「本文字的真值载体」，否则 σ₋ 文字会判反）
LK-litVal : Sign → Trit → Trit
LK-litVal σ₊ v = v
LK-litVal σ₋ v = negate v

-- 一步 fold 后的相位（δ 的收口子句与整公式归纳共用**同一个**函数
-- ⟹ 归纳结论里不出现第二套「语义相位」，全部在定义层对齐，零枚举）
LK-phStep : LK-Ph → Trit → LK-Ph
LK-phStep ph@(pos , ck , fk) v = LK-nextT pos , LK-foldCk ph v , LK-foldFk ph v

data LK-Q : Set where
  qLit  : LK-Ph → LK-Q
  qScan : LK-Ph → Sign → Bool → Trit → LK-Q
  qBack : LK-Ph → Sign → Trit → LK-Q            -- 回走：把带 2 的头走回 ⊢ 标记
  qDone : LK-Ph → Sign → Trit → LK-Q            -- 一个文字收口（携带 (符号, a[v])）

-- δ：符号步读 (sign, ⊢) 双右移；锁步每格读 (oᵢ, aᵢ) 双右移；见到首个 T₁
--     即记下该处的见证值且此后不再覆盖（对见证格不作要求：耗尽时读空白 ⟹ T₀，
--     与 LK-pick 的耗尽口径一致）；回走相把带 2 扛回 ⊢；收口相做一次 fold。
lk-δ : LK-Q → LK-Σ → LK-Σ → LK-Q × (LK-Σ × Dir3) × (LK-Σ × Dir3)
lk-δ (qLit ph) (LK-t sg) LK-m =
  qScan ph (signOf sg) false T₀ , (LK-t sg , dR) , (LK-m , dR)
lk-δ (qLit ph) x y = qDone ph (signOf T₀) T₀ , (x , dN) , (y , dN)   -- 形状外（不可达）
lk-δ (qScan ph s false v) (LK-t T₁) y =
  qScan ph s true (LK-v y) , (LK-t T₁ , dR) , (y , dR)
-- 见证块走完（带 2 读到空白）⟹ 相迁移：锁步相 → 回走相
-- （带 1 不动——头 1 已停在下一文字的 sign 上；带 2 停在空白上，交给回走首步）
lk-δ (qScan ph s false v) x LK-b = qBack ph s v , (x , dN) , (LK-b , dN)
lk-δ (qScan ph s true  v) x LK-b = qBack ph s v , (x , dN) , (LK-b , dN)
lk-δ (qScan ph s false v) x LK-e = qBack ph s v , (x , dN) , (LK-e , dN)
lk-δ (qScan ph s true  v) x LK-e = qBack ph s v , (x , dN) , (LK-e , dN)
lk-δ (qScan ph s false v) x y = qScan ph s false v , (x , dR) , (y , dR)
lk-δ (qScan ph s true  v) x y = qScan ph s true  v , (x , dR) , (y , dR)
-- 回走相：带 1 不动（头 1 已停在下一文字的 sign 上）；带 2 左移，
-- 见到 ⊢ 标记即收口（dN 停在该标记上——下一次文字的符号步要读的就是它）
lk-δ (qBack ph s v) x LK-m = qDone ph s v , (x , dN) , (LK-m , dN)
lk-δ (qBack ph s v) x y = qBack ph s v , (x , dN) , (y , dL)
-- ★ 收口 fold（每个文字恰好一步，零枚举）：把「本文字是否让本子句满足」并进相位，
--   若是子句末文字则清零 ck 并与 fk 合取；带 1 头是下一文字的 sign、带 2 头是 ⊢
--   ⟹ 直接回 qLit 续跑（末端形与起点同形，可无限串联）。
lk-δ (qDone ph s v) (LK-t sg) LK-m =
  qLit (LK-phStep ph (LK-litVal s v)) , (LK-t sg , dN) , (LK-m , dN)
lk-δ (qDone ph s v) x y = qDone ph s v , (x , dN) , (y , dN)
tm-look : TM2 LK-Q LK-Σ
tm-look = record { δ = lk-δ ; q₀ = qLit LK-ph₀ ; halt = λ _ → false }

-- ────────────────────────────────────────────────────────────────────
-- §2 选择器与带表示〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 选择器：带 1 的首个 T₁ 处取带 2 的对应见证值（见证耗尽读 T₀——与 LK-v 空白同）
LK-pick : List LK-Σ → List Trit → Trit
LK-pick [] _ = T₀
LK-pick _ [] = T₀
LK-pick (LK-t T₁ ∷ _) (b ∷ _) = b
LK-pick (_ ∷ os) (_ ∷ as) = LK-pick os as

-- 见证耗尽 ⟹ 选择器走到底仍 T₀
LK-pick-nil : ∀ (os : List LK-Σ) → LK-pick os [] ≡ T₀
LK-pick-nil [] = refl
LK-pick-nil (x ∷ os) = refl

-- 「os 里有没有 T₁」（scan0 的空表基准要它）
LK-anyT₁ : List LK-Σ → Bool
LK-anyT₁ [] = false
LK-anyT₁ (LK-t T₁ ∷ _) = true
LK-anyT₁ (_ ∷ os) = LK-anyT₁ os

-- 带 1 的 onehot 单元格（Vec Trit → List LK-Σ）
LK-cells : ∀ {k} → Vec Trit k → List LK-Σ
LK-cells vNil = []
LK-cells (t v∷ ts) = LK-t t ∷ LK-cells ts

-- 带 2 的见证区（trit 列表 → List LK-Σ）
LK-wl : List Trit → List LK-Σ
LK-wl [] = []
LK-wl (t ∷ ts) = LK-t t ∷ LK-wl ts

-- Vec → List（trit 视图）
LK-vl : ∀ {k} → Vec Trit k → List Trit
LK-vl vNil = []
LK-vl (t v∷ ts) = t ∷ LK-vl ts

-- 选择器 ↔ 库内 fromOneHot：「首个 T₁」两处一致（需 ∃T₁ 前提——真实独热位保证）
LK-pick-cells : ∀ (m : ℕ) (o a : Vec Trit (suc m))
              → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
              → LK-pick (LK-cells o) (LK-vl a) ≡ lookup a (fromOneHot m o)
LK-pick-cells zero (T₁ v∷ vNil) (b v∷ vNil) _ = refl
LK-pick-cells zero (T₀ v∷ vNil) _ (fzero , ())
LK-pick-cells zero (T₂ v∷ vNil) _ (fzero , ())
LK-pick-cells (suc m) (T₁ v∷ os) (b v∷ as) _ = refl
LK-pick-cells (suc m) (T₀ v∷ os) (c v∷ as) (fsuc i , p) =
  LK-pick-cells m os as (i , p)
LK-pick-cells (suc m) (T₂ v∷ os) (c v∷ as) (fsuc i , p) =
  LK-pick-cells m os as (i , p)

-- ∃T₁ ⟹ anyT₁ = true
LK-anyT₁-cells : ∀ (m : ℕ) (o : Vec Trit (suc m))
               → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
               → LK-anyT₁ (LK-cells o) ≡ true
LK-anyT₁-cells zero (T₁ v∷ vNil) _ = refl
LK-anyT₁-cells zero (T₀ v∷ vNil) (fzero , ())
LK-anyT₁-cells zero (T₂ v∷ vNil) (fzero , ())
LK-anyT₁-cells (suc m) (T₁ v∷ os) _ = refl
LK-anyT₁-cells (suc m) (T₀ v∷ os) (fsuc i , p) = LK-anyT₁-cells m os (i , p)
LK-anyT₁-cells (suc m) (T₂ v∷ os) (fsuc i , p) = LK-anyT₁-cells m os (i , p)

-- ────────────────────────────────────────────────────────────────────
-- （原 §3/§4 的 list 级锁步引理已删除：加相迁移子句后「见证耗尽」分支不再
--   保持 qScan，而 Vec 级 LK-lock 用等长前提天然规避该分支；引擎定理改由
--   LK-lock 重推，见 §4e。）

-- §4b 回走相（无复制时的对齐回收）〔结构归纳于左带〕
-- ────────────────────────────────────────────────────────────────────
-- 锁步扫完，带 2 的头停在见证块之后；要回到 ⊢ 才能开始下一文字。
-- 左带 = cs（已消费见证格的逆序）++ (⊢ ∷ l₂)：移动左时消费左带的头，
-- 故 cs 用 trit 列表给出 ⟹ 归纳是结构的（无需 list-reverse 引理）。
-- 计账：LK-walk = |cs| + 2 步；LK-back = |cs| + 2 步（首步从空白跨到首格）。

LK-walk : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (h : Trit) (cs : List Trit) (l₂ : List LK-Σ)
            (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
        → C2.st (runB tm-look LK-b (suc (suc (length cs)))
            (mk2 l₁ (qBack ph sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) (LK-t h) r₂))
          ≡ qDone ph sg v
LK-walk ph sg v h [] l₂ l₁ h₁ r₁ r₂ = refl
LK-walk ph sg v h (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walk ph sg v b cs l₂ l₁ h₁ r₁ (LK-t h ∷ r₂)

LK-back : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (cs : List Trit) (l₂ : List LK-Σ)
            (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
        → C2.st (runB tm-look LK-b (suc (suc (length cs)))
            (mk2 l₁ (qBack ph sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) LK-b r₂))
          ≡ qDone ph sg v
LK-back ph sg v [] l₂ l₁ h₁ r₁ r₂ = refl
LK-back ph sg v (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walk ph sg v b cs l₂ l₁ h₁ r₁ (LK-b ∷ r₂)

-- ────────────────────────────────────────────────────────────────────
-- §4c 无复制整机：带形不变式 + 一次文字的完整循环〔结构归纳〕
-- ────────────────────────────────────────────────────────────────────
-- 未来态（先把目标形钉死）：一次文字 = 1（符号步）+ (m+1)（锁步）+ (m+3)（回走）
-- = 2m+6 步（含 1 步相迁移）；结束时带 2 **完全复原**（头回 ⊢、左带回 l₂），
-- 所以每个文字只付自己那一块（m+1 格）——整体 **线性** L·(2m+6)，不是 Θ(m·L²)。

-- 反向累积（带 2 左带的实际增长顺序：每消费一格就 prepend）
LK-rw : List Trit → List LK-Σ → List LK-Σ
LK-rw []       acc = acc
LK-rw (b ∷ bs) acc = LK-rw bs (LK-t b ∷ acc)

-- trit 列表反转（累加器版）
LK-revA : List Trit → List Trit → List Trit
LK-revA []       acc = acc
LK-revA (b ∷ bs) acc = LK-revA bs (b ∷ acc)

LK-revT : List Trit → List Trit
LK-revT ws = LK-revA ws []

LK-len-revA : ∀ (ws acc : List Trit) → length (LK-revA ws acc) ≡ length ws + length acc
LK-len-revA []       acc = refl
LK-len-revA (b ∷ bs) acc =
  trans (LK-len-revA bs (b ∷ acc)) (+-suc (length bs) (length acc))

LK-len-revT : ∀ (ws : List Trit) → length (LK-revT ws) ≡ length ws
LK-len-revT ws = trans (LK-len-revA ws []) (+-identityʳ (length ws))

LK-len-cells : ∀ {k} (v : Vec Trit k) → length (LK-vl v) ≡ k
LK-len-cells vNil = refl
LK-len-cells (x v∷ xs) = cong suc (LK-len-cells xs)

-- LK-wl 与 ++ 的分配
LK-wl-++ : ∀ (xs ys : List Trit) → LK-wl (xs ++ ys) ≡ LK-wl xs ++ LK-wl ys
LK-wl-++ []       ys = refl
LK-wl-++ (x ∷ xs) ys = cong (LK-t x ∷_) (LK-wl-++ xs ys)

-- 累加器版的分配律：LK-revA ws acc ≡ LK-revT ws ++ acc
LK-revA-wl : ∀ (ws acc : List Trit) → LK-revA ws acc ≡ LK-revT ws ++ acc
LK-revA-wl []       acc = refl
LK-revA-wl (b ∷ bs) acc =
  trans (LK-revA-wl bs (b ∷ acc))
        (sym (trans (cong (λ z → z ++ acc) (LK-revA-wl bs (b ∷ [])))
                    (++-assoc (LK-revT bs) (b ∷ []) acc)))

-- 反转的 snoc 形
LK-revT-snoc : ∀ (bs : List Trit) (b : Trit) → LK-revT (b ∷ bs) ≡ LK-revT bs ++ (b ∷ [])
LK-revT-snoc bs b = LK-revA-wl bs (b ∷ [])

-- ★ 接缝：反向累积 = 反序映射再拼上底带（回走相正是消费这个形态）
LK-rw-wl : ∀ (ws : List Trit) (acc : List LK-Σ)
         → LK-rw ws acc ≡ LK-wl (LK-revT ws) ++ acc
LK-rw-wl []       acc = refl
LK-rw-wl (b ∷ bs) acc =
  trans (LK-rw-wl bs (LK-t b ∷ acc))
        (sym (trans (cong (λ z → LK-wl z ++ acc) (LK-revT-snoc bs b))
                    (trans (cong (λ z → z ++ acc) (LK-wl-++ (LK-revT bs) (b ∷ [])))
                           (++-assoc (LK-wl (LK-revT bs)) (LK-t b ∷ []) acc))))

-- 锁步相（已找到变体）的带形：走完 todo 后左带 = 反向累积
-- §4d full-config 锁步引理：目标形（未来态锚点）+ 已备规范件
-- ────────────────────────────────────────────────────────────────────
-- 目标态：从 (qScan sg b v)、两带同时在格首出发，走 |o| = m+1 步后
--   带 1：左带 = 反向累积的 onehot 格，头/余带回空白与 []
--   带 2：左带 = 反向累积的见证格，头/余带回空白与 []
--   状态：LK-scanned sg b v（本节的规范函数）
-- 于是「符号步 + 锁步 + 回走」三段都能以**整幅格局**为接口用 runB-+ 拼接。
--
-- ⚠ 本轮未闭合（诊断见尾注 §6(v)）：两个**必须先解决的形状问题**已定位——
--   ① `b`、`v` 作为变量时 δ 不可归约（`lk-δ (qScan s false v) …` 的 false 是
--      子句里的构造子），故 b 必须逐真值分案；false→true 的迁移只在 T₁ 分支；
--   ② 分案后「已找到」变体必须对 v **全泛型**，否则 T₁ 之后的值会被重写成
--      剩余见证的首格（我把 v 写成 `LK-v (hdOf …)` 时就是这里失配）。
--   这两点已改对；剩下的是结论里「带 1 左带」的实例对齐（`LK-rc (LK-cells o) l₁`
--   与一步之后 `LK-rc (LK-cells (tl …)) (… ∷ l₁)` 的可转换性），未清。

-- 格级反向累积（带 1 左带的增长序）
LK-rc : List LK-Σ → List LK-Σ → List LK-Σ
LK-rc []       acc = acc
LK-rc (x ∷ xs) acc = LK-rc xs (x ∷ acc)

-- 见证侧的一格消费
LK-drop1 : List Trit → List Trit
LK-drop1 []       = []
LK-drop1 (b ∷ bs) = bs

-- LK-rc 的累加器律（三条）：
--   ① LK-revS = 反向映射（LK-rc 的零底形）；
--   ② LK-rc-wl：LK-rc os acc ≡ LK-revS os ++ acc（分配律，接缝用）；
--   ③ LK-rc-++：LK-rc (xs ++ ys) acc ≡ LK-rc ys (LK-rc xs acc)（分段拼接用）。
LK-revS : List LK-Σ → List LK-Σ
LK-revS os = LK-rc os []

LK-rc-wl : ∀ (os : List LK-Σ) (acc : List LK-Σ) → LK-rc os acc ≡ LK-revS os ++ acc
LK-rc-wl []       acc = refl
LK-rc-wl (x ∷ xs) acc =
  trans (LK-rc-wl xs (x ∷ acc))
        (sym (trans (cong (λ z → z ++ acc) (LK-rc-wl xs (x ∷ [])))
                    (++-assoc (LK-revS xs) (x ∷ []) acc)))

LK-rc-++ : ∀ (xs ys : List LK-Σ) (acc : List LK-Σ)
         → LK-rc (xs ++ ys) acc ≡ LK-rc ys (LK-rc xs acc)
LK-rc-++ []       ys acc = refl
LK-rc-++ (x ∷ xs) ys acc = LK-rc-++ xs ys (x ∷ acc)

-- 锁步扫描的规范终态（(已找到, 值) 全泛型 ⟹ 一条函数覆盖两变体）。
-- 关键语义：T₁ 在「未找到」时把值置为该格见证；在「已找到」时**不覆盖**。
LK-scanned : (ph : LK-Ph) (sg : Sign) (b : Bool) (v : Trit)
             (os : List LK-Σ) (ws : List Trit) → LK-Q
LK-scanned ph sg b v [] ws = qScan ph sg b v
LK-scanned ph sg false v (LK-t T₁ ∷ os) (w ∷ ws) = LK-scanned ph sg true w os ws
LK-scanned ph sg false v (LK-t T₁ ∷ os) [] = LK-scanned ph sg true (LK-v LK-b) os []
LK-scanned ph sg true  v (LK-t T₁ ∷ os) ws = LK-scanned ph sg true v os (LK-drop1 ws)
LK-scanned ph sg b v (LK-t T₀ ∷ os) ws = LK-scanned ph sg b v os (LK-drop1 ws)
LK-scanned ph sg b v (LK-t T₂ ∷ os) ws = LK-scanned ph sg b v os (LK-drop1 ws)
LK-scanned ph sg b v (LK-b ∷ os) ws = LK-scanned ph sg b v os (LK-drop1 ws)
LK-scanned ph sg b v (LK-m ∷ os) ws = LK-scanned ph sg b v os (LK-drop1 ws)
LK-scanned ph sg b v (LK-e ∷ os) ws = LK-scanned ph sg b v os (LK-drop1 ws)

-- §4d′ 配对标件（附录 8 的开工形）：两条带由**一个** List (LK-Σ × Trit) 驱动，
-- 长度相等由类型保证，于是「一条带耗尽」的分支根本不存在（也避开 tlOf 落在
-- 变量参数上不归约的坑）。
LK-cellsP : List (LK-Σ × Trit) → List LK-Σ
LK-cellsP [] = []
LK-cellsP ((q , w) ∷ ps) = q ∷ LK-cellsP ps

LK-cellsQ : List (LK-Σ × Trit) → List LK-Σ
LK-cellsQ [] = []
LK-cellsQ ((q , w) ∷ ps) = LK-t w ∷ LK-cellsQ ps

-- 配对版的「锁步扫描规范终态」：语义与 LK-scanned 相同，只是驱动列表成对
LK-scannedQ : (ph : LK-Ph) (sg : Sign) (b : Bool) (v : Trit) → List (LK-Σ × Trit) → LK-Q
LK-scannedQ ph sg b v [] = qScan ph sg b v
LK-scannedQ ph sg false v ((LK-t T₁ , w) ∷ ps) = LK-scannedQ ph sg true w ps
LK-scannedQ ph sg false v ((q , w) ∷ ps) = LK-scannedQ ph sg false v ps
LK-scannedQ ph sg true v ((q , w) ∷ ps) = LK-scannedQ ph sg true v ps

-- ══ A1 配对标构造（Vec 级 zip：等长由类型保证 ⟹ 三个投影引理全无「不可能分支」）
LK-zipV : ∀ {k} (o a : Vec Trit k) → List (LK-Σ × Trit)
LK-zipV vNil vNil = []
LK-zipV (x v∷ xs) (y v∷ ys) = (LK-t x , y) ∷ LK-zipV xs ys

LK-zipP : ∀ {k} (o a : Vec Trit k) → LK-cellsP (LK-zipV o a) ≡ LK-cells o
LK-zipP vNil vNil = refl
LK-zipP (x v∷ xs) (y v∷ ys) = cong (LK-t x ∷_) (LK-zipP xs ys)

LK-zipQ : ∀ {k} (o a : Vec Trit k) → LK-cellsQ (LK-zipV o a) ≡ LK-wl (LK-vl a)
LK-zipQ vNil vNil = refl
LK-zipQ (x v∷ xs) (y v∷ ys) = cong (LK-t y ∷_) (LK-zipQ xs ys)

LK-zip-len : ∀ {k} (o a : Vec Trit k) → length (LK-zipV o a) ≡ k
LK-zip-len vNil vNil = refl
LK-zip-len (x v∷ xs) (y v∷ ys) = cong suc (LK-zip-len xs ys)

-- ══ A2.1 配对标 ↔ 两列表版：LK-scannedQ 与 LK-scanned 同形（供 §4e 规范律复用）
LK-wq : List (LK-Σ × Trit) → List Trit
LK-wq [] = []
LK-wq ((q , w) ∷ ps) = w ∷ LK-wq ps

LK-wq-zip : ∀ {k} (o a : Vec Trit k) → LK-wq (LK-zipV o a) ≡ LK-vl a
LK-wq-zip vNil vNil = refl
LK-wq-zip (x v∷ xs) (y v∷ ys) = cong (y ∷_) (LK-wq-zip xs ys)

LK-scannedQ-scan : ∀ (ph : LK-Ph) (sg : Sign) (b : Bool) (v : Trit) (ps : List (LK-Σ × Trit))
                 → LK-scannedQ ph sg b v ps ≡ LK-scanned ph sg b v (LK-cellsP ps) (LK-wq ps)
LK-scannedQ-scan ph sg b v [] = refl
LK-scannedQ-scan ph sg false v ((LK-t T₁ , w) ∷ ps) =
  LK-scannedQ-scan ph sg true w ps
LK-scannedQ-scan ph sg false v ((LK-t T₀ , w) ∷ ps) =
  LK-scannedQ-scan ph sg false v ps
LK-scannedQ-scan ph sg false v ((LK-t T₂ , w) ∷ ps) =
  LK-scannedQ-scan ph sg false v ps
LK-scannedQ-scan ph sg false v ((LK-b , w) ∷ ps) =
  LK-scannedQ-scan ph sg false v ps
LK-scannedQ-scan ph sg false v ((LK-m , w) ∷ ps) =
  LK-scannedQ-scan ph sg false v ps
LK-scannedQ-scan ph sg true v ((LK-t T₁ , w) ∷ ps) =
  LK-scannedQ-scan ph sg true v ps
LK-scannedQ-scan ph sg true v ((LK-t T₀ , w) ∷ ps) =
  LK-scannedQ-scan ph sg true v ps
LK-scannedQ-scan ph sg true v ((LK-t T₂ , w) ∷ ps) =
  LK-scannedQ-scan ph sg true v ps
LK-scannedQ-scan ph sg true v ((LK-b , w) ∷ ps) =
  LK-scannedQ-scan ph sg true v ps
LK-scannedQ-scan ph sg true v ((LK-m , w) ∷ ps) =
  LK-scannedQ-scan ph sg true v ps
LK-scannedQ-scan ph sg false v ((LK-e , w) ∷ ps) =
  LK-scannedQ-scan ph sg false v ps
LK-scannedQ-scan ph sg true v ((LK-e , w) ∷ ps) =
  LK-scannedQ-scan ph sg true v ps

-- LK-revT 的两条基本律（终止符布局要用：rk∘rev 与「先反转再累积」）
LK-revT-++ : ∀ (xs ys : List Trit) → LK-revT (xs ++ ys) ≡ LK-revT ys ++ LK-revT xs
LK-revT-++ [] ys = sym (++-identityʳ (LK-revT ys))
LK-revT-++ (x ∷ xs) ys =
  trans (LK-revA-wl (xs ++ ys) (x ∷ []))
        (trans (cong (λ z → z ++ (x ∷ [])) (LK-revT-++ xs ys))
               (trans (++-assoc (LK-revT ys) (LK-revT xs) (x ∷ []))
                      (cong (LK-revT ys ++_) (sym (LK-revA-wl xs (x ∷ []))))))

LK-revT-revT : ∀ (ws : List Trit) → LK-revT (LK-revT ws) ≡ ws
LK-revT-revT [] = refl
LK-revT-revT (b ∷ bs) =
  trans (cong LK-revT (LK-revA-wl bs (b ∷ [])))
        (trans (LK-revT-++ (LK-revT bs) (b ∷ []))
               (cong ((b ∷ []) ++_) (LK-revT-revT bs)))

-- 先反转再累积 = 直接累积原列表
LK-rw-rev : ∀ (ws : List Trit) (acc : List LK-Σ)
          → LK-rw (LK-revT ws) acc ≡ LK-wl ws ++ acc
LK-rw-rev ws acc =
  trans (LK-rw-wl (LK-revT ws) acc)
        (cong (λ z → LK-wl z ++ acc) (LK-revT-revT ws))

-- 配对版见证反序累积
LK-rwQ : List (LK-Σ × Trit) → List LK-Σ → List LK-Σ
LK-rwQ [] acc = acc
LK-rwQ ((q , w) ∷ ps) acc = LK-rwQ ps (LK-t w ∷ acc)

-- ★ 配对版锁步引理（自相似陈述：两端一律写 hdOf/tlOf of (LK-cellsP ps ++ r₁)
--   与 (LK-cellsQ ps)，于是 ps 在子句里是构造子 ⟹ δ 每次可归约；ps = [] 由 0 步
--   base 覆盖，不需要「见证耗尽」的特殊分支）
LK-lockP-true : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (ps : List (LK-Σ × Trit))
                  (acc l₁ : List LK-Σ) (r₁ : List LK-Σ)
              → runB tm-look LK-b (length ps)
                  (mk2 l₁ (qScan ph sg true v)
                       (hdOf LK-b (LK-cellsP ps ++ r₁)) (tlOf (LK-cellsP ps ++ r₁))
                       acc (hdOf LK-b (LK-cellsQ ps)) (tlOf (LK-cellsQ ps)))
                ≡ mk2 (LK-rc (LK-cellsP ps) l₁) (LK-scannedQ ph sg true v ps)
                      (hdOf LK-b r₁) (tlOf r₁) (LK-rwQ ps acc) LK-b []
LK-lockP-true ph sg v [] acc l₁ r₁ = refl
LK-lockP-true ph sg v ((q , w) ∷ ps) acc l₁ r₁ =
  LK-lockP-true ph sg v ps (LK-t w ∷ acc) (q ∷ l₁) r₁

LK-lockP : ∀ (ph : LK-Ph) (sg : Sign) (ps : List (LK-Σ × Trit))
             (acc l₁ : List LK-Σ) (r₁ : List LK-Σ)
         → runB tm-look LK-b (length ps)
             (mk2 l₁ (qScan ph sg false T₀)
                  (hdOf LK-b (LK-cellsP ps ++ r₁)) (tlOf (LK-cellsP ps ++ r₁))
                  acc (hdOf LK-b (LK-cellsQ ps)) (tlOf (LK-cellsQ ps)))
           ≡ mk2 (LK-rc (LK-cellsP ps) l₁) (LK-scannedQ ph sg false T₀ ps)
                 (hdOf LK-b r₁) (tlOf r₁) (LK-rwQ ps acc) LK-b []
LK-lockP ph sg [] acc l₁ r₁ = refl
LK-lockP ph sg ((LK-t T₁ , w) ∷ ps) acc l₁ r₁ =
  LK-lockP-true ph sg w ps (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) r₁
LK-lockP ph sg ((LK-t T₀ , w) ∷ ps) acc l₁ r₁ =
  LK-lockP ph sg ps (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) r₁
LK-lockP ph sg ((LK-t T₂ , w) ∷ ps) acc l₁ r₁ =
  LK-lockP ph sg ps (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) r₁
LK-lockP ph sg ((LK-b , w) ∷ ps) acc l₁ r₁ =
  LK-lockP ph sg ps (LK-t w ∷ acc) (LK-b ∷ l₁) r₁
LK-lockP ph sg ((LK-m , w) ∷ ps) acc l₁ r₁ =
  LK-lockP ph sg ps (LK-t w ∷ acc) (LK-m ∷ l₁) r₁
LK-lockP ph sg ((LK-e , w) ∷ ps) acc l₁ r₁ =
  LK-lockP ph sg ps (LK-t w ∷ acc) (LK-e ∷ l₁) r₁

-- 规范的投影律（§4e）：LK-scanned 与「有没有 T₁ / 首个 T₁ 处的值」对齐
--   LK-scanned-true：已找到后不再变（对 v 全泛型）
--   LK-scanned-spec：未找到起步 ⟹ (anyT₁, pick)
LK-scanned-true : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (os : List LK-Σ) (ws : List Trit)
                → LK-scanned ph sg true v os ws ≡ qScan ph sg true v
LK-scanned-true ph sg v [] ws = refl
LK-scanned-true ph sg v (LK-t T₁ ∷ os) ws = LK-scanned-true ph sg v os (LK-drop1 ws)
LK-scanned-true ph sg v (LK-t T₀ ∷ os) ws = LK-scanned-true ph sg v os (LK-drop1 ws)
LK-scanned-true ph sg v (LK-t T₂ ∷ os) ws = LK-scanned-true ph sg v os (LK-drop1 ws)
LK-scanned-true ph sg v (LK-b ∷ os) ws = LK-scanned-true ph sg v os (LK-drop1 ws)
LK-scanned-true ph sg v (LK-m ∷ os) ws = LK-scanned-true ph sg v os (LK-drop1 ws)
LK-scanned-true ph sg v (LK-e ∷ os) ws = LK-scanned-true ph sg v os (LK-drop1 ws)

LK-scanned-spec : ∀ (ph : LK-Ph) (sg : Sign) (os : List LK-Σ) (ws : List Trit)
                → LK-scanned ph sg false T₀ os ws
                  ≡ qScan ph sg (LK-anyT₁ os) (LK-pick os ws)
LK-scanned-spec ph sg [] ws = refl
LK-scanned-spec ph sg (LK-t T₁ ∷ os) (w ∷ ws) = LK-scanned-true ph sg w os ws
LK-scanned-spec ph sg (LK-t T₁ ∷ os) [] =
  trans (LK-scanned-true ph sg (LK-v LK-b) os []) refl
LK-scanned-spec ph sg (LK-t T₀ ∷ os) [] =
  trans (LK-scanned-spec ph sg os [])
        (cong (λ t → qScan ph sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec ph sg (LK-t T₀ ∷ os) (w ∷ ws) = LK-scanned-spec ph sg os ws
LK-scanned-spec ph sg (LK-t T₂ ∷ os) [] =
  trans (LK-scanned-spec ph sg os [])
        (cong (λ t → qScan ph sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec ph sg (LK-t T₂ ∷ os) (w ∷ ws) = LK-scanned-spec ph sg os ws
LK-scanned-spec ph sg (LK-b ∷ os) [] =
  trans (LK-scanned-spec ph sg os [])
        (cong (λ t → qScan ph sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec ph sg (LK-b ∷ os) (w ∷ ws) = LK-scanned-spec ph sg os ws
LK-scanned-spec ph sg (LK-m ∷ os) [] =
  trans (LK-scanned-spec ph sg os [])
        (cong (λ t → qScan ph sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec ph sg (LK-m ∷ os) (w ∷ ws) = LK-scanned-spec ph sg os ws
LK-scanned-spec ph sg (LK-e ∷ os) [] =
  trans (LK-scanned-spec ph sg os [])
        (cong (λ t → qScan ph sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec ph sg (LK-e ∷ os) (w ∷ ws) = LK-scanned-spec ph sg os ws

-- ★ full-config 锁步引理（结论形 = 未来态：state 与两带同时给出）
-- 形状要点（上一轮的诊断）：b、v 为变量时 δ 不可归约 ⟹ b 逐真值分案；
-- 分案后「已找到」变体必须对 v 全泛型（否则 T₁ 之后的值会被重写）。

-- 已找到变体：值不再覆盖
LK-lock-true : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (o a : Vec Trit (suc m))
                 (acc l₁ : List LK-Σ) (h₁ : LK-Σ)
             → runB tm-look LK-b (suc m)
                 (mk2 l₁ (qScan ph sg true v)
                      (hdOf LK-b (LK-cells o)) (tlOf (LK-cells o))
                      acc (hdOf LK-b (LK-wl (LK-vl a))) (tlOf (LK-wl (LK-vl a))))
               ≡ mk2 (LK-rc (LK-cells o) l₁)
                     (LK-scanned ph sg true v (LK-cells o) (LK-vl a)) LK-b []
                     (LK-rw (LK-vl a) acc) LK-b []
LK-lock-true ph sg v zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock-true ph sg v zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock-true ph sg v zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock-true ph sg v (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock-true ph sg v (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock-true ph sg v (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) (hdOf LK-b (LK-cells os))

-- 未找到变体（b = false 固定）
LK-lock : ∀ (ph : LK-Ph) (sg : Sign) (m : ℕ) (o a : Vec Trit (suc m))
            (acc l₁ : List LK-Σ) (h₁ : LK-Σ)
        → runB tm-look LK-b (suc m)
            (mk2 l₁ (qScan ph sg false T₀)
                 (hdOf LK-b (LK-cells o)) (tlOf (LK-cells o))
                 acc (hdOf LK-b (LK-wl (LK-vl a))) (tlOf (LK-wl (LK-vl a))))
          ≡ mk2 (LK-rc (LK-cells o) l₁)
                (LK-scanned ph sg false T₀ (LK-cells o) (LK-vl a)) LK-b []
                (LK-rw (LK-vl a) acc) LK-b []
LK-lock ph sg zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock ph sg zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock ph sg zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock ph sg (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true ph sg w m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock ph sg (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock ph sg m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock ph sg (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock ph sg m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) (hdOf LK-b (LK-cells os))

-- ────────────────────────────────────────────────────────────────────
-- §4e 引擎定理（由 LK-lock 重推：锁步相 = m+2 步，终态携带 (符号, a[v])）
-- ────────────────────────────────────────────────────────────────────

LK-look-sem : ∀ (ph : LK-Ph) (m : ℕ) (sg : Trit) (o a : Vec Trit (suc m))
            → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
            → C2.st (runB tm-look LK-b (suc (suc m))
                (mk2 [] (qLit ph) (LK-t sg) (LK-cells o) [] LK-m (LK-wl (LK-vl a))))
              ≡ qScan ph (signOf sg) true (lookup a (fromOneHot m o))
LK-look-sem ph m sg o a h =
  trans (cong C2.st
           (LK-lock ph (signOf sg) m o a (LK-m ∷ []) (LK-t sg ∷ []) LK-b))
        (trans (LK-scanned-spec ph (signOf sg) (LK-cells o) (LK-vl a))
               (trans (cong (λ z → qScan ph (signOf sg) z
                                       (LK-pick (LK-cells o) (LK-vl a)))
                            (LK-anyT₁-cells m o h))
                      (cong (qScan ph (signOf sg) true) (LK-pick-cells m o a h))))

-- ────────────────────────────────────────────────────────────────────
-- §4f ★ 单文字循环（无复制）：符号步 + 锁步 + 相迁移 + 回走 = 2m+6 步
-- ────────────────────────────────────────────────────────────────────

-- 回走燃料对齐：cs = LK-revT (LK-vl a) 的长度恰为 suc m
LK-rewind-fuel : ∀ (m : ℕ) (a : Vec Trit (suc m))
               → length (LK-revT (LK-vl a)) ≡ suc m
LK-rewind-fuel m a = trans (LK-len-revT (LK-vl a)) (LK-len-cells a)

-- 接缝：锁步终态 ⟹ 回走起点（整幅格局等式）
LK-seam : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
        → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
        → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
              (LK-scanned ph (signOf sg) false T₀ (LK-cells o) (LK-vl a)) LK-b []
              (LK-rw (LK-vl a) (LK-m ∷ [])) LK-b []
          ≡ mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                (qScan ph (signOf sg) true (lookup a (fromOneHot m o))) LK-b []
                (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []
LK-seam ph sg m o a l₁ h =
  trans (cong (λ st → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) st LK-b []
                             (LK-rw (LK-vl a) (LK-m ∷ [])) LK-b [])
              (trans (LK-scanned-spec ph (signOf sg) (LK-cells o) (LK-vl a))
                     (trans (cong (λ z → qScan ph (signOf sg) z
                                      (LK-pick (LK-cells o) (LK-vl a)))
                                  (LK-anyT₁-cells m o h))
                            (cong (qScan ph (signOf sg) true) (LK-pick-cells m o a h)))))
        (cong (λ l → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                          (qScan ph (signOf sg) true (lookup a (fromOneHot m o))) LK-b []
                          l LK-b [])
              (LK-rw-wl (LK-vl a) (LK-m ∷ [])))

-- 回走的 m 索引版（燃料写成 suc³ m，避免 length 中性项与「展开后三步」
-- 两种范式在拼接处打架；subst 只在**本条**里做一次）
LK-back-m : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (a : Vec Trit (suc m)) (l₁ : List LK-Σ)
          → C2.st (runB tm-look LK-b (suc (suc (suc m)))
              (mk2 l₁ (qBack ph sg v) LK-b []
                   (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []))
            ≡ qDone ph sg v
LK-back-m ph sg v m a l₁ =
  subst (λ k → C2.st (runB tm-look LK-b k
                 (mk2 l₁ (qBack ph sg v) LK-b []
                      (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []))
               ≡ qDone ph sg v)
        (cong suc (cong suc (LK-rewind-fuel m a)))
        (LK-back ph sg v (LK-revT (LK-vl a)) [] l₁ LK-b [] [])

-- ══ A3 回走的**整幅格局**版（多文字循环的前置：循环边界必须知道两带的完整形）
LK-walkF : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (h : Trit) (cs : List Trit) (l₂ : List LK-Σ)
             (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
         → runB tm-look LK-b (suc (suc (length cs)))
             (mk2 l₁ (qBack ph sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) (LK-t h) r₂)
           ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ l₂ LK-m (LK-rw cs (LK-t h ∷ r₂))
LK-walkF ph sg v h [] l₂ l₁ h₁ r₁ r₂ = refl
LK-walkF ph sg v h (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walkF ph sg v b cs l₂ l₁ h₁ r₁ (LK-t h ∷ r₂)

LK-backF : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (cs : List Trit) (l₂ : List LK-Σ)
             (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
         → runB tm-look LK-b (suc (suc (length cs)))
             (mk2 l₁ (qBack ph sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) LK-b r₂)
           ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ l₂ LK-m (LK-rw cs (LK-b ∷ r₂))
LK-backF ph sg v [] l₂ l₁ h₁ r₁ r₂ = refl
LK-backF ph sg v (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walkF ph sg v b cs l₂ l₁ h₁ r₁ (LK-b ∷ r₂)

-- ★ 主定理：一次文字 = 1（符号）+ (m+1)（锁步）+ 1（相迁移）+ (m+3)（回走）
-- = 2m+6 步；终态携带 (符号, a[v])，带 2 由回走相复原。
LK-cycle : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
         → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
         → C2.st (runB tm-look LK-b (suc (suc m + suc (suc (suc (suc m)))))
             (mk2 l₁ (qLit ph) (LK-t sg) (LK-cells o) [] LK-m (LK-wl (LK-vl a))))
           ≡ qDone ph (signOf sg) (lookup a (fromOneHot m o))
LK-cycle ph sg m o a l₁ h =
  trans (cong C2.st
           (trans (runB-+ tm-look LK-b (suc m) (suc (suc (suc (suc m))))
                          (mk2 (LK-t sg ∷ l₁) (qScan ph (signOf sg) false T₀)
                               (hdOf LK-b (LK-cells o)) (tlOf (LK-cells o))
                               (LK-m ∷ []) (hdOf LK-b (LK-wl (LK-vl a)))
                               (tlOf (LK-wl (LK-vl a)))))
                  (trans (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                               (LK-lock ph (signOf sg) m o a (LK-m ∷ [])
                                        (LK-t sg ∷ l₁) LK-b))
                         (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                               (LK-seam ph sg m o a l₁ h)))))
        (LK-back-m ph (signOf sg) (lookup a (fromOneHot m o)) m a
                   (LK-rc (LK-cells o) (LK-t sg ∷ l₁)))

-- ────────────────────────────────────────────────────────────────────
-- §4g r₁ 版（可嵌入：带 1 后缀 r₁ 贯穿）——多文字循环的前置
-- ────────────────────────────────────────────────────────────────────
-- 关键形（此前失败点）：余带写 hdOf/tlOf (LK-cells o ++ r₁)，**不是**
-- tlOf (LK-cells o) ++ r₁ —— 后者在 o 为变量时不归约（附录 8）。

LK-lockR-true : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (o a : Vec Trit (suc m))
                  (acc l₁ : List LK-Σ) (r₁ : List LK-Σ)
              → runB tm-look LK-b (suc m)
                  (mk2 l₁ (qScan ph sg true v)
                       (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁))
                       acc (hdOf LK-b (LK-wl (LK-vl a))) (tlOf (LK-wl (LK-vl a))))
                ≡ mk2 (LK-rc (LK-cells o) l₁) (LK-scanned ph sg true v (LK-cells o) (LK-vl a))
                      (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) acc) LK-b []
LK-lockR-true ph sg v zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockR-true ph sg v zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockR-true ph sg v zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockR-true ph sg v (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockR-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) r₁
LK-lockR-true ph sg v (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockR-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) r₁
LK-lockR-true ph sg v (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockR-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) r₁

LK-lockR : ∀ (ph : LK-Ph) (sg : Sign) (m : ℕ) (o a : Vec Trit (suc m))
             (acc l₁ : List LK-Σ) (r₁ : List LK-Σ)
         → runB tm-look LK-b (suc m)
             (mk2 l₁ (qScan ph sg false T₀)
                  (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁))
                  acc (hdOf LK-b (LK-wl (LK-vl a))) (tlOf (LK-wl (LK-vl a))))
           ≡ mk2 (LK-rc (LK-cells o) l₁) (LK-scanned ph sg false T₀ (LK-cells o) (LK-vl a))
                 (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) acc) LK-b []
LK-lockR ph sg zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockR ph sg zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockR ph sg zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockR ph sg (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockR-true ph sg w m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) r₁
LK-lockR ph sg (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockR ph sg m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) r₁
LK-lockR ph sg (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockR ph sg m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) r₁

-- 接缝（r₁ 版）：锁步终态 ⟹ 回走起点
LK-seamR : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
             (r₁ : List LK-Σ)
         → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
         → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
               (LK-scanned ph (signOf sg) false T₀ (LK-cells o) (LK-vl a))
               (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) (LK-m ∷ [])) LK-b []
           ≡ mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                 (qScan ph (signOf sg) true (lookup a (fromOneHot m o))) (hdOf LK-b r₁) (tlOf r₁)
                 (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []
LK-seamR ph sg m o a l₁ r₁ h =
  trans (cong (λ st → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) st
                             (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) (LK-m ∷ [])) LK-b [])
              (trans (LK-scanned-spec ph (signOf sg) (LK-cells o) (LK-vl a))
                     (trans (cong (λ z → qScan ph (signOf sg) z
                                      (LK-pick (LK-cells o) (LK-vl a)))
                                  (LK-anyT₁-cells m o h))
                            (cong (qScan ph (signOf sg) true) (LK-pick-cells m o a h)))))
        (cong (λ l → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                          (qScan ph (signOf sg) true (lookup a (fromOneHot m o)))
                          (hdOf LK-b r₁) (tlOf r₁) l LK-b [])
              (LK-rw-wl (LK-vl a) (LK-m ∷ [])))

-- 回走（r₁ 版）
LK-back-mR : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (a : Vec Trit (suc m)) (l₁ : List LK-Σ)
               (h₁ : LK-Σ) (r₁ : List LK-Σ)
           → C2.st (runB tm-look LK-b (suc (suc (suc m)))
               (mk2 l₁ (qBack ph sg v) h₁ r₁
                    (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []))
             ≡ qDone ph sg v
LK-back-mR ph sg v m a l₁ h₁ r₁ =
  subst (λ k → C2.st (runB tm-look LK-b k
                 (mk2 l₁ (qBack ph sg v) h₁ r₁
                      (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []))
               ≡ qDone ph sg v)
        (cong suc (cong suc (LK-rewind-fuel m a)))
        (LK-back ph sg v (LK-revT (LK-vl a)) [] l₁ h₁ r₁ [])

-- ★ 可嵌入的单文字循环（r₁ 版，2m+6 步）
LK-cycleR : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
              (r₁ : List LK-Σ)
          → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
          → C2.st (runB tm-look LK-b (suc (suc m + suc (suc (suc (suc m)))))
              (mk2 l₁ (qLit ph) (LK-t sg) (LK-cells o ++ r₁) [] LK-m (LK-wl (LK-vl a))))
            ≡ qDone ph (signOf sg) (lookup a (fromOneHot m o))
LK-cycleR ph sg m o a l₁ r₁ h =
  trans (cong C2.st
           (trans (runB-+ tm-look LK-b (suc m) (suc (suc (suc (suc m))))
                          (mk2 (LK-t sg ∷ l₁) (qScan ph (signOf sg) false T₀)
                               (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁))
                               (LK-m ∷ []) (hdOf LK-b (LK-wl (LK-vl a)))
                               (tlOf (LK-wl (LK-vl a)))))
                  (trans (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                               (LK-lockR ph (signOf sg) m o a (LK-m ∷ [])
                                         (LK-t sg ∷ l₁) r₁))
                         (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                               (LK-seamR ph sg m o a l₁ r₁ h)))))
        (LK-back-mR ph (signOf sg) (lookup a (fromOneHot m o)) m a
                    (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) (hdOf LK-b r₁) (tlOf r₁))

-- ══ A3′ 终止符布局（tape2 = ⊢ block ⊣）：锁步末停在 ⊣ 上，回走把它压回**同位置**
-- ⟹ 循环末的带 2 形与循环起点**同形**、不随轮次增长（这是多文字循环能串起来的关键）。

LK-lockS-true : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (o a : Vec Trit (suc m))
                  (acc l₁ : List LK-Σ) (r₁ : List LK-Σ)
              → runB tm-look LK-b (suc m)
                  (mk2 l₁ (qScan ph sg true v)
                       (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁)) acc
                       (hdOf LK-b (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
                       (tlOf (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                ≡ mk2 (LK-rc (LK-cells o) l₁) (LK-scanned ph sg true v (LK-cells o) (LK-vl a))
                      (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) acc) LK-e []
LK-lockS-true ph sg v zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockS-true ph sg v zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockS-true ph sg v zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockS-true ph sg v (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockS-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) r₁
LK-lockS-true ph sg v (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockS-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) r₁
LK-lockS-true ph sg v (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockS-true ph sg v m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) r₁

LK-lockS : ∀ (ph : LK-Ph) (sg : Sign) (m : ℕ) (o a : Vec Trit (suc m))
             (acc l₁ : List LK-Σ) (r₁ : List LK-Σ)
         → runB tm-look LK-b (suc m)
             (mk2 l₁ (qScan ph sg false T₀)
                  (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁)) acc
                  (hdOf LK-b (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
                  (tlOf (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
           ≡ mk2 (LK-rc (LK-cells o) l₁) (LK-scanned ph sg false T₀ (LK-cells o) (LK-vl a))
                 (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) acc) LK-e []
LK-lockS ph sg zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockS ph sg zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockS ph sg zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ r₁ = refl
LK-lockS ph sg (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockS-true ph sg w m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) r₁
LK-lockS ph sg (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockS ph sg m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) r₁
LK-lockS ph sg (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ r₁ =
  LK-lockS ph sg m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) r₁

-- 回走（终止符版）：头在 ⊣ 上，走完 cs 后读 ⊢ 收口；⊣ 被压回右带同位置
LK-backFS : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (cs : List Trit) (l₂ : List LK-Σ)
              (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
          → runB tm-look LK-b (suc (suc (length cs)))
              (mk2 l₁ (qBack ph sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) LK-e r₂)
            ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ l₂ LK-m (LK-rw cs (LK-e ∷ r₂))
LK-backFS ph sg v [] l₂ l₁ h₁ r₁ r₂ = refl
LK-backFS ph sg v (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walkF ph sg v b cs l₂ l₁ h₁ r₁ (LK-e ∷ r₂)

-- 回走的 m 索引整幅格局版（燃料与 length 中性项对齐，subst 只做一次）
LK-backFR : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (a : Vec Trit (suc m))
              (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ : List LK-Σ)
          → runB tm-look LK-b (suc (suc (suc m)))
              (mk2 l₁ (qBack ph sg v) h₁ r₁
                   (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b [])
            ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ [] LK-m (LK-rw (LK-revT (LK-vl a)) (LK-b ∷ []))
LK-backFR ph sg v m a l₁ h₁ r₁ =
  subst (λ k → runB tm-look LK-b k
                 (mk2 l₁ (qBack ph sg v) h₁ r₁
                      (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b [])
               ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ [] LK-m (LK-rw (LK-revT (LK-vl a)) (LK-b ∷ [])))
        (cong suc (cong suc (LK-rewind-fuel m a)))
        (LK-backF ph sg v (LK-revT (LK-vl a)) [] l₁ h₁ r₁ [])

-- ★ 整幅格局的单文字循环（循环边界可续：带 1 头/余带与带 2 全形都给出）
LK-cycleF : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
              (r₁ : List LK-Σ)
          → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
          → runB tm-look LK-b (suc (suc m + suc (suc (suc (suc m)))))
              (mk2 l₁ (qLit ph) (LK-t sg) (LK-cells o ++ r₁) [] LK-m (LK-wl (LK-vl a)))
            ≡ mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                  (qDone ph (signOf sg) (lookup a (fromOneHot m o)))
                  (hdOf LK-b r₁) (tlOf r₁) [] LK-m
                  (LK-rw (LK-revT (LK-vl a)) (LK-b ∷ []))
LK-cycleF ph sg m o a l₁ r₁ h =
  trans (trans (runB-+ tm-look LK-b (suc m) (suc (suc (suc (suc m))))
                          (mk2 (LK-t sg ∷ l₁) (qScan ph (signOf sg) false T₀)
                               (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁))
                               (LK-m ∷ []) (hdOf LK-b (LK-wl (LK-vl a)))
                               (tlOf (LK-wl (LK-vl a)))))
               (trans (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                            (LK-lockR ph (signOf sg) m o a (LK-m ∷ [])
                                      (LK-t sg ∷ l₁) r₁))
                      (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                            (LK-seamR ph sg m o a l₁ r₁ h))))
        (LK-backFR ph (signOf sg) (lookup a (fromOneHot m o)) m a
                   (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) (hdOf LK-b r₁) (tlOf r₁))

-- 接缝（终止符版）
LK-seamS : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
             (r₁ l₂ : List LK-Σ)
         → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
         → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
               (LK-scanned ph (signOf sg) false T₀ (LK-cells o) (LK-vl a))
               (hdOf LK-b r₁) (tlOf r₁) (LK-rw (LK-vl a) (LK-m ∷ l₂)) LK-e []
           ≡ mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                 (qScan ph (signOf sg) true (lookup a (fromOneHot m o)))
                 (hdOf LK-b r₁) (tlOf r₁)
                 (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ l₂)) LK-e []
LK-seamS ph sg m o a l₁ r₁ l₂ h =
  trans (cong (λ st → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) st
                             (hdOf LK-b r₁) (tlOf r₁)
                             (LK-rw (LK-vl a) (LK-m ∷ l₂)) LK-e [])
              (trans (LK-scanned-spec ph (signOf sg) (LK-cells o) (LK-vl a))
                     (trans (cong (λ z → qScan ph (signOf sg) z
                                      (LK-pick (LK-cells o) (LK-vl a)))
                                  (LK-anyT₁-cells m o h))
                            (cong (qScan ph (signOf sg) true) (LK-pick-cells m o a h)))))
        (cong (λ l → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                          (qScan ph (signOf sg) true (lookup a (fromOneHot m o)))
                          (hdOf LK-b r₁) (tlOf r₁) l LK-e [])
              (LK-rw-wl (LK-vl a) (LK-m ∷ l₂)))

-- 回走（终止符版，m 索引）
LK-backFSR : ∀ (ph : LK-Ph) (sg : Sign) (v : Trit) (m : ℕ) (a : Vec Trit (suc m))
               (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ l₂ : List LK-Σ)
           → runB tm-look LK-b (suc (suc (suc m)))
               (mk2 l₁ (qBack ph sg v) h₁ r₁
                    (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ l₂)) LK-e [])
             ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ l₂ LK-m (LK-rw (LK-revT (LK-vl a)) (LK-e ∷ []))
LK-backFSR ph sg v m a l₁ h₁ r₁ l₂ =
  subst (λ k → runB tm-look LK-b k
                 (mk2 l₁ (qBack ph sg v) h₁ r₁
                      (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ l₂)) LK-e [])
               ≡ mk2 l₁ (qDone ph sg v) h₁ r₁ l₂ LK-m
                       (LK-rw (LK-revT (LK-vl a)) (LK-e ∷ [])))
        (cong suc (cong suc (LK-rewind-fuel m a)))
        (LK-backFS ph sg v (LK-revT (LK-vl a)) l₂ l₁ h₁ r₁ [])

-- ★★ 终止符布局的整幅格局单文字循环：**末端形与起点形同形**（可无限续跑）
LK-cycleS : ∀ (ph : LK-Ph) (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
              (r₁ l₂ : List LK-Σ)
          → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
          → runB tm-look LK-b (suc (suc m + suc (suc (suc (suc m)))))
              (mk2 l₁ (qLit ph) (LK-t sg) (LK-cells o ++ r₁) l₂
                   LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
            ≡ mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                  (qDone ph (signOf sg) (lookup a (fromOneHot m o)))
                  (hdOf LK-b r₁) (tlOf r₁) l₂ LK-m
                  (LK-wl (LK-vl a) ++ (LK-e ∷ []))
LK-cycleS ph sg m o a l₁ r₁ l₂ h =
  trans (trans (runB-+ tm-look LK-b (suc m) (suc (suc (suc (suc m))))
                          (mk2 (LK-t sg ∷ l₁) (qScan ph (signOf sg) false T₀)
                               (hdOf LK-b (LK-cells o ++ r₁)) (tlOf (LK-cells o ++ r₁))
                               (LK-m ∷ l₂)
                               (hdOf LK-b (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
                               (tlOf (LK-wl (LK-vl a) ++ (LK-e ∷ [])))))
               (trans (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                            (LK-lockS ph (signOf sg) m o a (LK-m ∷ l₂)
                                      (LK-t sg ∷ l₁) r₁))
                      (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                            (LK-seamS ph sg m o a l₁ r₁ l₂ h))))
        (trans (LK-backFSR ph (signOf sg) (lookup a (fromOneHot m o)) m a
                           (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) (hdOf LK-b r₁) (tlOf r₁) l₂)
               (cong (λ z → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                                  (qDone ph (signOf sg) (lookup a (fromOneHot m o)))
                                  (hdOf LK-b r₁) (tlOf r₁) l₂ LK-m z)
                     (LK-rw-rev (LK-vl a) (LK-e ∷ []))))

-- ────────────────────────────────────────────────────────────────────
-- §4h 整公式：沿文字表归纳（每字 2m+7 = 锁步循环 2m+6 + 收口 fold 1）
-- ────────────────────────────────────────────────────────────────────
-- 带 1：每字一格 sign + (m+1) 格 onehot，末尾留**一个** sentinel 格 LK-t sg₀
--       —— 收口 fold 的触发条件就是「带 1 头仍是 LK-t」（= 还有下一个文字）。
--       有 sentinel ⟹ 最后一个文字的 fold 也触发（相位因此是**整公式**的终值）；
--       没有 sentinel ⟹ 最后一个 fold 不触发（相位少折一次，still qDone）。
--       ⚠ 判决读第 L·(2m+7) 步的那个状态：此后 sentinel 会被当作「下一个文字」的
--       sign，机器再走一个**幽灵文字**。实测（§5d 三条 refl 钉住，c=1/m=0）：
--       第 22 步进入幽灵文字（qScan σ₋ false T₀）、第 27 步停在 qDone、第 28 步
--       不动。停驻后 fk 仍在状态里 ⟹ 判决事后照样可读。一般性停驻定理**未证**
--       （要对带 1 尾部全空白 + 固定距离回走作归纳），判决不依赖它。
-- 带 2：**只放一份**见证块（⊢ a₀…a_m ⊣）。LK-cycleS 的结论里带 2 与起点同形
--       ⟹ 每个文字复用同一块（空间 O(m)，不是 O(m·L)）——「无复制」的机器侧。
-- 相位：fold 用 δ 的**同一个** LK-phStep ⟹ 归纳结论与机器状态在定义层重合。
-- 计账：逐字拼接的 LK-fuelL（= 3 个字时 3·7 = 21，§5b 有 refl 自证），
--       乘法形由 LK-fuelL-len / LK-runL-steps 给出：L·(2m+7)。
-- 零枚举：不分 pos/ck/fk 的 27 案，也不对文字数做任何分案。

LK-Lit : ℕ → Set
LK-Lit m = Trit × Vec Trit (suc m)

-- 带 1 的逐文字格串（尾累积形：LK-cellsL (l ∷ ls) r = sign ∷ (onehot ++ LK-cellsL ls r)）
LK-cellsL : ∀ {m} → List (LK-Lit m) → List LK-Σ → List LK-Σ
LK-cellsL []              r = r
LK-cellsL ((sg , o) ∷ ls) r = LK-t sg ∷ (LK-cells o ++ LK-cellsL ls r)

-- 带 1 左带的逐文字累积（LK-rc 串起来）
LK-rcL : ∀ {m} → List (LK-Lit m) → List LK-Σ → List LK-Σ
LK-rcL []              acc = acc
LK-rcL ((sg , o) ∷ ls) acc = LK-rcL ls (LK-rc (LK-cells o) (LK-t sg ∷ acc))

-- 整公式的相位 fold：与 δ 的收口子句同一函数
LK-foldL : ∀ (m : ℕ) → LK-Ph → List (LK-Lit m) → Vec Trit (suc m) → LK-Ph
LK-foldL m ph []             a = ph
LK-foldL m ph ((sg , o) ∷ ls) a =
  LK-foldL m (LK-phStep ph (LK-litVal (signOf sg) (lookup a (fromOneHot m o)))) ls a

-- 每个文字都要有独热位（真实输入保证；全 T₀ 的 onehot 是伪输入）
LK-AllT₁ : ∀ (m : ℕ) → List (LK-Lit m) → Set
LK-AllT₁ m []              = ⊤
LK-AllT₁ m ((_ , o) ∷ ls)  = Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁) × LK-AllT₁ m ls

-- 一段文字的锁步循环 = 2m+6（LK-cycleS 的燃料）；加收口 fold 一条 = 2m+7。
-- 写成 (LK-cycleSteps m) + 1 而**不是** suc (LK-cycleSteps m)：`_+_` 与 `_*_`
-- 都递归在首参上，两种写法只在具体数下相等、在变量 m 处不可转换。
LK-cycleSteps : ℕ → ℕ
LK-cycleSteps m = suc (suc m + suc (suc (suc (suc m))))

LK-litSteps : ℕ → ℕ
LK-litSteps m = LK-cycleSteps m + 1

-- 燃料沿文字表逐字拼接（**不**写成 length ls * LK-litSteps m：`suc n * K` 展开为
-- `K + n * K`，末格会留下 `K + 0`，在变量 m 处不可转换 ⟹ 拼接处必须用本形；
-- 线性计账由 LK-fuelL-len 另行给出）
LK-fuelL : ∀ {m} → List (LK-Lit m) → ℕ
LK-fuelL {m} []       = 0
LK-fuelL {m} (_ ∷ ls) = LK-litSteps m + LK-fuelL ls

-- 计账：逐字拼接 = L·(2m+7)（+ 子句末 fold 一步已含在 LK-litSteps 里）
LK-fuelL-len : ∀ {m} (ls : List (LK-Lit m)) → LK-fuelL ls ≡ length ls * LK-litSteps m
LK-fuelL-len []           = refl
LK-fuelL-len {m} (_ ∷ ls) = cong (LK-litSteps m +_) (LK-fuelL-len ls)

-- 收口一步（fold）：两带不动，只有相位推进（δ 的收口子句 + dN ⟹ refl）
LK-fold-step : ∀ (ph : LK-Ph) (s : Sign) (v : Trit) (sg : Trit)
                 (l₁ r₁ l₂ r₂ : List LK-Σ)
             → runB tm-look LK-b 1 (mk2 l₁ (qDone ph s v) (LK-t sg) r₁ l₂ LK-m r₂)
               ≡ mk2 l₁ (qLit (LK-phStep ph (LK-litVal s v))) (LK-t sg) r₁ l₂ LK-m r₂
LK-fold-step ph s v sg l₁ r₁ l₂ r₂ = refl

-- ★ 整公式定理：逐文字消费带 1、复用带 2 的同一块见证，
--   终态 qLit 携带整公式的相位（fk = 所有子句皆满足），步数 L·(2m+7)。
LK-runL : ∀ (ph : LK-Ph) (m : ℕ) (ls : List (LK-Lit m))
            (l₁ : List LK-Σ) (sg₀ : Trit) (r₁ l₂ : List LK-Σ) (a : Vec Trit (suc m))
        → LK-AllT₁ m ls
        → runB tm-look LK-b (LK-fuelL ls)
            (mk2 l₁ (qLit ph)
                 (hdOf LK-b (LK-cellsL ls (LK-t sg₀ ∷ r₁)))
                 (tlOf (LK-cellsL ls (LK-t sg₀ ∷ r₁)))
                 l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
          ≡ mk2 (LK-rcL ls l₁) (qLit (LK-foldL m ph ls a)) (LK-t sg₀) r₁
                l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))
LK-runL ph m [] l₁ sg₀ r₁ l₂ a tt = refl
LK-runL ph m ((sg , o) ∷ []) l₁ sg₀ r₁ l₂ a (h , tt) =
  trans (runB-+ tm-look LK-b (LK-litSteps m) (LK-fuelL {m} [])
                (mk2 l₁ (qLit ph)
                     (hdOf LK-b (LK-t sg ∷ (LK-cells o ++ (LK-t sg₀ ∷ r₁))))
                     (tlOf (LK-t sg ∷ (LK-cells o ++ (LK-t sg₀ ∷ r₁))))
                     l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
        (cong (runB tm-look LK-b (LK-fuelL {m} []))
              (trans (runB-+ tm-look LK-b (LK-cycleSteps m) 1
                             (mk2 l₁ (qLit ph)
                                  (hdOf LK-b (LK-t sg ∷ (LK-cells o ++ (LK-t sg₀ ∷ r₁))))
                                  (tlOf (LK-t sg ∷ (LK-cells o ++ (LK-t sg₀ ∷ r₁))))
                                  l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                     (trans (cong (runB tm-look LK-b 1)
                                  (LK-cycleS ph sg m o a l₁ (LK-t sg₀ ∷ r₁) l₂ h))
                            (LK-fold-step ph (signOf sg) (lookup a (fromOneHot m o)) sg₀
                                            (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) r₁ l₂
                                            (LK-wl (LK-vl a) ++ (LK-e ∷ []))))))
LK-runL ph m ((sg , o) ∷ ((sg₁ , o₁) ∷ rest)) l₁ sg₀ r₁ l₂ a (h , hrest) =
  trans (runB-+ tm-look LK-b (LK-litSteps m) (LK-fuelL ((sg₁ , o₁) ∷ rest))
                (mk2 l₁ (qLit ph)
                     (hdOf LK-b (LK-t sg
                                    ∷ (LK-cells o ++ (LK-t sg₁
                                        ∷ (LK-cells o₁ ++ LK-cellsL rest (LK-t sg₀ ∷ r₁))))))
                     (tlOf (LK-t sg
                                    ∷ (LK-cells o ++ (LK-t sg₁
                                        ∷ (LK-cells o₁ ++ LK-cellsL rest (LK-t sg₀ ∷ r₁))))))
                     l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
        (trans (cong (runB tm-look LK-b (LK-fuelL ((sg₁ , o₁) ∷ rest)))
                     (trans (runB-+ tm-look LK-b (LK-cycleSteps m) 1
                                    (mk2 l₁ (qLit ph)
                                         (hdOf LK-b (LK-t sg
                                            ∷ (LK-cells o ++ (LK-t sg₁
                                                ∷ (LK-cells o₁ ++ LK-cellsL rest (LK-t sg₀ ∷ r₁))))))
                                         (tlOf (LK-t sg
                                            ∷ (LK-cells o ++ (LK-t sg₁
                                                ∷ (LK-cells o₁ ++ LK-cellsL rest (LK-t sg₀ ∷ r₁))))))
                                         l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                            (trans (cong (runB tm-look LK-b 1)
                                         (LK-cycleS ph sg m o a l₁
                                                     (LK-t sg₁ ∷ (LK-cells o₁
                                                         ++ LK-cellsL rest (LK-t sg₀ ∷ r₁)))
                                                     l₂ h))
                                   (LK-fold-step ph (signOf sg)
                                                  (lookup a (fromOneHot m o)) sg₁
                                                  (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                                                  (LK-cells o₁ ++ LK-cellsL rest (LK-t sg₀ ∷ r₁))
                                                  l₂ (LK-wl (LK-vl a) ++ (LK-e ∷ []))))))
               (LK-runL (LK-phStep ph (LK-litVal (signOf sg) (lookup a (fromOneHot m o)))) m
                        ((sg₁ , o₁) ∷ rest)
                        (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) sg₀ r₁ l₂ a hrest))

-- ★ 线性计账推论：L 个文字 = L·(2m+7) 步（LK-runL 用逐字拼接燃料，本条件换回乘法形）
LK-runL-steps : ∀ (ph : LK-Ph) (m : ℕ) (ls : List (LK-Lit m))
                  (l₁ : List LK-Σ) (sg₀ : Trit) (r₁ l₂ : List LK-Σ)
                  (a : Vec Trit (suc m))
              → LK-AllT₁ m ls
              → runB tm-look LK-b (length ls * LK-litSteps m)
                  (mk2 l₁ (qLit ph)
                       (hdOf LK-b (LK-cellsL ls (LK-t sg₀ ∷ r₁)))
                       (tlOf (LK-cellsL ls (LK-t sg₀ ∷ r₁)))
                       l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
                ≡ mk2 (LK-rcL ls l₁) (qLit (LK-foldL m ph ls a)) (LK-t sg₀) r₁
                      l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))
LK-runL-steps ph m ls l₁ sg₀ r₁ l₂ a h =
  subst (λ k → runB tm-look LK-b k
                 (mk2 l₁ (qLit ph)
                      (hdOf LK-b (LK-cellsL ls (LK-t sg₀ ∷ r₁)))
                      (tlOf (LK-cellsL ls (LK-t sg₀ ∷ r₁)))
                      l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
               ≡ mk2 (LK-rcL ls l₁) (qLit (LK-foldL m ph ls a)) (LK-t sg₀) r₁
                     l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ [])))
        (LK-fuelL-len ls)
        (LK-runL ph m ls l₁ sg₀ r₁ l₂ a h)

-- ────────────────────────────────────────────────────────────────────
-- §4i 语义桥：终态相位里的 fk 就是库内 satFormula 的值
-- ────────────────────────────────────────────────────────────────────
-- 机器读到的「本文字真值载体」与库内 evalLit 是同一个函数，只差一层 Sign 解码
-- （signOf）——这条一致性 2 案均 refl；此后的 OR/AND 折叠全靠 Bool 代数
-- （∨-assoc / ∧-assoc / ∧-identityʳ），不对文字数、子句数、相位值分任何案。
--
-- 机器侧公式 = Vec 的机器子句（每子句三个机器文字，顺序 = satClause 的 l₁l₂l₃）；
-- 库内公式 = 同一 Vec 经 LK-clause→lib 解码。于是「带格式 ↔ 库内编码」只剩
-- **独热编码的生成**（库内 Fin 号 ⟹ one-hot 向量）未做（尾注 (iii)），语义面在此闭合。
--
-- 唯一的结构性差异：机器 ck 是**左折** ((b₁∨b₂)∨b₃)，库内 satClause 是**右折**
-- b₁∨(b₂∨b₃) ⟹ 恰好一步 ∨-assoc（LK-or3-cong），不是分案。

-- 机器文字 → 库内文字（one-hot 解码 = fromOneHot）
LK-libLit : ∀ {m} → LK-Lit m → Lit m
LK-libLit {m} (sg , o) = signOf sg , fromOneHot m o

-- 机器读到的真值载体（δ 的收口子句用的就是它：LK-litVal 已施加符号）
LK-litOf : ∀ {m} → Asg m → LK-Lit m → Trit
LK-litOf {m} a (sg , o) = LK-litVal (signOf sg) (lookup a (fromOneHot m o))

-- 库内 evalLit = 机器取值（只差 Sign 一层：σ₊ 取原值 / σ₋ 取 negate）
LK-evalLit : ∀ {m} (a : Asg m) (l : Lit m)
           → evalLit a l ≡ LK-litVal (proj₁ l) (lookup a (proj₂ l))
LK-evalLit a (σ₊ , i) = refl
LK-evalLit a (σ₋ , i) = refl

-- 一致到真值位（fold 累积的就是这一位）
LK-litOf-eval : ∀ {m} (a : Asg m) (l : LK-Lit m)
              → isT₁ (LK-litOf a l) ≡ isT₁ (evalLit a (LK-libLit l))
LK-litOf-eval {m} a (sg , o) =
  cong isT₁ (sym (LK-evalLit a (signOf sg , fromOneHot m o)))

-- 机器子句（三个机器文字，顺序 = satClause 的 l₁ l₂ l₃）
LK-Clause : ℕ → Set
LK-Clause m = LK-Lit m × LK-Lit m × LK-Lit m

-- 机器子句 → 库内子句
LK-clause→lib : ∀ {m} → LK-Clause m → Clause m
LK-clause→lib (l₁ , l₂ , l₃) = LK-libLit l₁ , LK-libLit l₂ , LK-libLit l₃

-- 带 1 的格串（按子句顺序展平；每个子句三格文字）
LK-flatV : ∀ {m c} → Vec (LK-Clause m) c → List (LK-Lit m)
LK-flatV vNil                   = []
LK-flatV ((l₁ , l₂ , l₃) v∷ cs) = l₁ ∷ l₂ ∷ l₃ ∷ LK-flatV cs

-- 一个子句的三步 fold（纯定义性：pos 三格回卷、ck 左折、末格并进 fk）
LK-fold3 : ∀ (fk : Bool) (v₁ v₂ v₃ : Trit)
         → LK-phStep (LK-phStep (LK-phStep (T₀ , false , fk) v₁) v₂) v₃
           ≡ (T₀ , false , (fk ∧ ((isT₁ v₁ ∨ isT₁ v₂) ∨ isT₁ v₃)))
LK-fold3 fk v₁ v₂ v₃ = refl

-- 三步重写 + 一次 ∨-assoc：机器左折 ⟹ 库内右折
LK-or3-cong : ∀ (c₁ c₂ c₃ d₁ d₂ d₃ : Bool)
            → c₁ ≡ d₁ → c₂ ≡ d₂ → c₃ ≡ d₃
            → ((c₁ ∨ c₂) ∨ c₃) ≡ (d₁ ∨ (d₂ ∨ d₃))
LK-or3-cong c₁ c₂ c₃ d₁ d₂ d₃ e₁ e₂ e₃ =
  trans (cong (λ z → (z ∨ c₂) ∨ c₃) e₁)
        (trans (cong (λ z → (d₁ ∨ z) ∨ c₃) e₂)
               (trans (cong (λ z → (d₁ ∨ d₂) ∨ z) e₃)
                      (∨-assoc d₁ d₂ d₃)))

-- 把「机器左折的 fk ∧ rest」整块归到「库内右折 ∧ rest」
LK-and3 : ∀ (fk rest b₁ b₂ b₃ d₁ d₂ d₃ : Bool)
        → b₁ ≡ d₁ → b₂ ≡ d₂ → b₃ ≡ d₃
        → ((fk ∧ ((b₁ ∨ b₂) ∨ b₃)) ∧ rest) ≡ (fk ∧ ((d₁ ∨ (d₂ ∨ d₃)) ∧ rest))
LK-and3 fk rest b₁ b₂ b₃ d₁ d₂ d₃ e₁ e₂ e₃ =
  trans (cong (λ z → z ∧ rest)
              (cong (λ z → fk ∧ z) (LK-or3-cong b₁ b₂ b₃ d₁ d₂ d₃ e₁ e₂ e₃)))
        (∧-assoc fk (d₁ ∨ (d₂ ∨ d₃)) rest)

-- ★ 公式级：沿子句表归纳（fk 起始任意；每子句 3 步折进一个 satClause）
LK-foldV : ∀ {m c} (a : Asg m) (cs : Vec (LK-Clause m) c) (fk : Bool)
         → LK-foldL m (T₀ , false , fk) (LK-flatV cs) a
           ≡ (T₀ , false , (fk ∧ satFormula a (map LK-clause→lib cs)))
LK-foldV a vNil fk = cong (λ z → T₀ , false , z) (sym (∧-identityʳ fk))
LK-foldV {m} a (((sg₁ , o₁) , (sg₂ , o₂) , (sg₃ , o₃)) v∷ cs) fk =
  trans (cong (λ ph → LK-foldL m ph (LK-flatV cs) a)
              (LK-fold3 fk (LK-litOf a (sg₁ , o₁)) (LK-litOf a (sg₂ , o₂))
                          (LK-litOf a (sg₃ , o₃))))
        (trans (LK-foldV a cs (fk ∧ ((isT₁ (LK-litOf a (sg₁ , o₁))
                                      ∨ isT₁ (LK-litOf a (sg₂ , o₂)))
                                     ∨ isT₁ (LK-litOf a (sg₃ , o₃)))))
               (cong (λ z → T₀ , false , z)
                     (LK-and3 fk (satFormula a (map LK-clause→lib cs))
                              (isT₁ (LK-litOf a (sg₁ , o₁)))
                              (isT₁ (LK-litOf a (sg₂ , o₂)))
                              (isT₁ (LK-litOf a (sg₃ , o₃)))
                              (isT₁ (evalLit a (LK-libLit (sg₁ , o₁))))
                              (isT₁ (evalLit a (LK-libLit (sg₂ , o₂))))
                              (isT₁ (evalLit a (LK-libLit (sg₃ , o₃))))
                              (LK-litOf-eval a (sg₁ , o₁))
                              (LK-litOf-eval a (sg₂ , o₂))
                              (LK-litOf-eval a (sg₃ , o₃)))))

-- ★★ 主定理（语义桥）：整公式跑完，状态里 fk = satFormula a 解码后的公式
--   （pos 归位 T₀、ck 归位 false —— 即「机器读出的就是公式的真值」）
LK-look-sat : ∀ (m : ℕ) {c : ℕ} (cs : Vec (LK-Clause m) c) (a : Asg m)
                (l₁ : List LK-Σ) (sg₀ : Trit) (r₁ l₂ : List LK-Σ)
            → LK-AllT₁ m (LK-flatV cs)
            → C2.st (runB tm-look LK-b (LK-fuelL (LK-flatV cs))
                       (mk2 l₁ (qLit LK-ph₀)
                            (hdOf LK-b (LK-cellsL (LK-flatV cs) (LK-t sg₀ ∷ r₁)))
                            (tlOf (LK-cellsL (LK-flatV cs) (LK-t sg₀ ∷ r₁)))
                            l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
              ≡ qLit (T₀ , false , satFormula a (map LK-clause→lib cs))
LK-look-sat m cs a l₁ sg₀ r₁ l₂ h =
  trans (cong C2.st (LK-runL LK-ph₀ m (LK-flatV cs) l₁ sg₀ r₁ l₂ a h))
        (cong qLit (LK-foldV a cs true))

-- ────────────────────────────────────────────────────────────────────
-- §4j 编码器：库内公式 ⟹ 带 1 的格串（§4i 的反方向）
-- ────────────────────────────────────────────────────────────────────
-- 只有一件新东西：库内的变元号 Fin (suc m) → one-hot 向量。定义**按索引结构
-- 递归**（不用 tabulate + 可判定相等）：于是「读回来是原索引」3 案全 refl/cong，
-- 既不需要 ≟、也不需要 toℕ 或 Vec 的成员引理——这是「有限域事实先别穷举」
-- 的同一条口径：先找结构，找不到结构才分案。

-- Sign 的 trit 签位（signOf 是它的左逆）
LK-encSign : Sign → Trit
LK-encSign σ₊ = T₁
LK-encSign σ₋ = T₀

LK-signOf-encSign : ∀ (s : Sign) → signOf (LK-encSign s) ≡ s
LK-signOf-encSign σ₊ = refl
LK-signOf-encSign σ₋ = refl

-- one-hot：长度 suc m 的向量，第 i 位 T₁、其余 T₀
LK-hot : ∀ (m : ℕ) → Fin (suc m) → Vec Trit (suc m)
LK-hot zero    fzero    = T₁ v∷ vNil
LK-hot (suc m) fzero    = T₁ v∷ replicate (suc m) T₀
LK-hot (suc m) (fsuc i) = T₀ v∷ LK-hot m i

-- 独热位读出来恰是 T₁（= 良构前提的见证）
LK-hot-lookup : ∀ (m : ℕ) (i : Fin (suc m)) → lookup (LK-hot m i) i ≡ T₁
LK-hot-lookup zero    fzero    = refl
LK-hot-lookup (suc m) fzero    = refl
LK-hot-lookup (suc m) (fsuc i) = LK-hot-lookup m i

-- 往返：fromOneHot 解回来还是原索引
LK-fromOneHot-hot : ∀ (m : ℕ) (i : Fin (suc m)) → fromOneHot m (LK-hot m i) ≡ i
LK-fromOneHot-hot zero    fzero    = refl
LK-fromOneHot-hot (suc m) fzero    = refl
LK-fromOneHot-hot (suc m) (fsuc i) = cong fsuc (LK-fromOneHot-hot m i)

-- 文字 → 机器文字（签位 + 独热）
LK-encLit : ∀ {m} → Lit m → LK-Lit m
LK-encLit {m} (s , i) = LK-encSign s , LK-hot m i

-- 解码 ∘ 编码 = id
LK-dec-enc : ∀ {m} (l : Lit m) → LK-libLit (LK-encLit l) ≡ l
LK-dec-enc {m} (s , i) = cong₂ _,_ (LK-signOf-encSign s) (LK-fromOneHot-hot m i)

-- 子句 / 子句表 → 机器侧
LK-encClause : ∀ {m} → Clause m → LK-Clause m
LK-encClause (l₁ , l₂ , l₃) = LK-encLit l₁ , LK-encLit l₂ , LK-encLit l₃

LK-clause-dec-enc : ∀ {m} (cl : Clause m) → LK-clause→lib (LK-encClause cl) ≡ cl
LK-clause-dec-enc (l₁ , l₂ , l₃) =
  trans (cong (λ z → z , LK-libLit (LK-encLit l₂) , LK-libLit (LK-encLit l₃))
              (LK-dec-enc l₁))
        (trans (cong (λ z → l₁ , z , LK-libLit (LK-encLit l₃)) (LK-dec-enc l₂))
               (cong (λ z → l₁ , l₂ , z) (LK-dec-enc l₃)))

-- 编码后的输入**自动**满足良构前提（第 i 个文字的独热位就在 i 上）
LK-AllT₁-enc : ∀ {m c} (φ : Formula m c) → LK-AllT₁ m (LK-flatV (map LK-encClause φ))
LK-AllT₁-enc vNil = tt
LK-AllT₁-enc {m} (((s₁ , i₁) , (s₂ , i₂) , (s₃ , i₃)) v∷ φ) =
  (i₁ , LK-hot-lookup m i₁) , (i₂ , LK-hot-lookup m i₂) , (i₃ , LK-hot-lookup m i₃)
    , LK-AllT₁-enc φ

-- 解码回来的公式与原公式同真值
LK-satF-enc : ∀ {m c} (a : Asg m) (φ : Formula m c)
            → satFormula a (map LK-clause→lib (map LK-encClause φ)) ≡ satFormula a φ
LK-satF-enc a vNil = refl
LK-satF-enc a (cl v∷ φ) =
  trans (cong (λ z → satClause a z
                     ∧ satFormula a (map LK-clause→lib (map LK-encClause φ)))
              (LK-clause-dec-enc cl))
        (cong (satClause a cl ∧_) (LK-satF-enc a φ))

-- 带 1 的长度：c 个子句 = 3c 个文字（结构归纳 + 一次 *-suc）
LK-length-flatV : ∀ {m c} (φ : Formula m c)
                → length (LK-flatV (map LK-encClause φ)) ≡ 3 * c
LK-length-flatV vNil = refl
LK-length-flatV (cl v∷ φ) =
  trans (cong suc (cong suc (cong suc (LK-length-flatV φ)))) (sym (*-suc 3 _))

-- ★★ 端到端（编码路径）：库内公式 φ 编成带格式 ⟹ 机器跑完 ⟹ qLit (T₀,false, satFormula a φ)
LK-run-formula : ∀ (m : ℕ) {c : ℕ} (φ : Formula m c) (a : Asg m)
                   (l₁ : List LK-Σ) (sg₀ : Trit) (r₁ l₂ : List LK-Σ)
               → C2.st (runB tm-look LK-b (LK-fuelL (LK-flatV (map LK-encClause φ)))
                          (mk2 l₁ (qLit LK-ph₀)
                               (hdOf LK-b (LK-cellsL (LK-flatV (map LK-encClause φ))
                                                     (LK-t sg₀ ∷ r₁)))
                               (tlOf (LK-cellsL (LK-flatV (map LK-encClause φ))
                                                (LK-t sg₀ ∷ r₁)))
                               l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                 ≡ qLit (T₀ , false , satFormula a φ)
LK-run-formula m φ a l₁ sg₀ r₁ l₂ =
  trans (LK-look-sat m (map LK-encClause φ) a l₁ sg₀ r₁ l₂ (LK-AllT₁-enc φ))
        (cong qLit (cong (λ z → T₀ , false , z) (LK-satF-enc a φ)))

-- 计账形：c 个子句 = 3c 个文字 = 3c·(2m+7) 步
LK-run-formula-steps : ∀ (m : ℕ) {c : ℕ} (φ : Formula m c) (a : Asg m)
                         (l₁ : List LK-Σ) (sg₀ : Trit) (r₁ l₂ : List LK-Σ)
                     → C2.st (runB tm-look LK-b ((3 * c) * LK-litSteps m)
                                (mk2 l₁ (qLit LK-ph₀)
                                     (hdOf LK-b (LK-cellsL (LK-flatV (map LK-encClause φ))
                                                           (LK-t sg₀ ∷ r₁)))
                                     (tlOf (LK-cellsL (LK-flatV (map LK-encClause φ))
                                                      (LK-t sg₀ ∷ r₁)))
                                     l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                       ≡ qLit (T₀ , false , satFormula a φ)
LK-run-formula-steps m φ a l₁ sg₀ r₁ l₂ =
  subst (λ k → C2.st (runB tm-look LK-b k
                        (mk2 l₁ (qLit LK-ph₀)
                             (hdOf LK-b (LK-cellsL (LK-flatV (map LK-encClause φ))
                                                   (LK-t sg₀ ∷ r₁)))
                             (tlOf (LK-cellsL (LK-flatV (map LK-encClause φ))
                                              (LK-t sg₀ ∷ r₁)))
                             l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                 ≡ qLit (T₀ , false , satFormula a φ))
        (trans (LK-fuelL-len (LK-flatV (map LK-encClause φ)))
               (cong (_* LK-litSteps m) (LK-length-flatV φ)))
        (LK-run-formula m φ a l₁ sg₀ r₁ l₂)

-- 账目对齐（与 SATMember 的抽象验证器 satFormulaC）：本机步数 = 抽象账目 × (2m+7)
--   ⟹ 这是**常数因子**模拟（不是「多项式的多项式」），差距全在这个常数：
--   抽象账目把 a[v] 的读取当免费（配对单元编码），本机每个文字独立付一次寻址
--   （1 符号 + (m+1) 锁步 + 1 相迁移 + (m+3) 回走 + 1 收口）。
--   证明只用一次 cong：steps-satFormulaC 的逆向代入，**零算术**。
LK-cost : ∀ (m : ℕ) {c : ℕ} (φ : Formula m c) (a : Asg m)
        → (3 * c) * LK-litSteps m ≡ steps (satFormulaC a φ) * LK-litSteps m
LK-cost m φ a = cong (_* LK-litSteps m) (sym (steps-satFormulaC a φ))

-- ★★★ 整机接口：原始 trit 串 → 解码（SATMember.decFormula）→ §4j 编码 → 跑 3c·(2m+7) 步
--   → qLit (T₀ , false , satFormula a (decFormula m n x))
-- （本件不再有新证明：LK-run-formula-steps 在 φ := decFormula m n x 上的实例）
LK-run-stream : ∀ (m n : ℕ) (x : Vec Trit n) (a : Asg m)
                  (l₁ : List LK-Σ) (sg₀ : Trit) (r₁ l₂ : List LK-Σ)
              → C2.st (runB tm-look LK-b ((3 * (n / clauseW m)) * LK-litSteps m)
                         (mk2 l₁ (qLit LK-ph₀)
                              (hdOf LK-b
                                  (LK-cellsL (LK-flatV (map LK-encClause (decFormula m n x)))
                                             (LK-t sg₀ ∷ r₁)))
                              (tlOf (LK-cellsL (LK-flatV (map LK-encClause (decFormula m n x)))
                                               (LK-t sg₀ ∷ r₁)))
                              l₂ LK-m (LK-wl (LK-vl a) ++ (LK-e ∷ []))))
                ≡ qLit (T₀ , false , satFormula a (decFormula m n x))
LK-run-stream m n x a l₁ sg₀ r₁ l₂ =
  LK-run-formula-steps m (decFormula m n x) a l₁ sg₀ r₁ l₂

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层（refl 枚举）
-- ────────────────────────────────────────────────────────────────────

check-pick-hit : LK-pick (LK-t T₁ ∷ LK-t T₂ ∷ []) (T₂ ∷ T₁ ∷ []) ≡ T₂
check-pick-hit = refl

check-pick-miss : LK-pick (LK-t T₀ ∷ LK-t T₂ ∷ []) (T₁ ∷ T₂ ∷ []) ≡ T₀
check-pick-miss = refl

check-any : LK-anyT₁ (LK-t T₀ ∷ LK-t T₁ ∷ []) ≡ true
check-any = refl

-- 端到端（m = 0）：带 1 = [sign T₁, o₀ = T₁]，带 2 = [⊢, a₀ = T₂] ⟹ 携带 T₂
check-look-0 :
  C2.st (runB tm-look LK-b 2
    (mk2 [] (qLit LK-ph₀) (LK-t T₁) (LK-t T₁ ∷ []) [] LK-m (LK-t T₂ ∷ [])))
  ≡ qScan LK-ph₀ σ₊ true T₂
check-look-0 = refl

-- 端到端（符号 T₀ = σ₋）：值仍取 a₀
check-look-0-neg :
  C2.st (runB tm-look LK-b 2
    (mk2 [] (qLit LK-ph₀) (LK-t T₀) (LK-t T₁ ∷ []) [] LK-m (LK-t T₁ ∷ [])))
  ≡ qScan LK-ph₀ σ₋ true T₁
check-look-0-neg = refl

-- 端到端（m = 1）：onehot = [T₀, T₁] ⟹ 首个 T₁ 在第 2 格 ⟹ 取 a₁ = T₀
check-look-1 :
  C2.st (runB tm-look LK-b 3
    (mk2 [] (qLit LK-ph₀) (LK-t T₁) (LK-t T₀ ∷ LK-t T₁ ∷ []) [] LK-m
         (LK-t T₁ ∷ LK-t T₀ ∷ [])))
  ≡ qScan LK-ph₀ σ₊ true T₀
check-look-1 = refl

-- r₁ 版整链端到端（m=0，带 1 有后缀 [T₀]）：1 符号 + 1 锁步 + 1 相迁移 + 3 回走 = 6 步
check-cycleR-0 :
  C2.st (runB tm-look LK-b 6
    (mk2 [] (qLit LK-ph₀) (LK-t T₁) (LK-t T₁ ∷ LK-t T₀ ∷ []) [] LK-m (LK-t T₂ ∷ [])))
  ≡ qDone LK-ph₀ σ₊ T₂
check-cycleR-0 = refl

-- 回走端到端：左带只有 ⊢ ⟹ 2 步收口
check-back-0 :
  C2.st (runB tm-look LK-b 2 (mk2 [] (qBack LK-ph₀ σ₊ T₂) LK-b [] (LK-m ∷ []) LK-b []))
  ≡ qDone LK-ph₀ σ₊ T₂
check-back-0 = refl

-- 回走端到端：左带 = [a₀, ⊢] ⟹ 3 步收口
check-back-1 :
  C2.st (runB tm-look LK-b 3
    (mk2 [] (qBack LK-ph₀ σ₋ T₁) LK-b [] (LK-t T₀ ∷ LK-m ∷ []) LK-b []))
  ≡ qDone LK-ph₀ σ₋ T₁
check-back-1 = refl


-- ────────────────────────────────────────────────────────────────────
-- §5b 核对层：整公式（m = 0，每字 2·0+7 = 7 步；3 字 = 21 步）
-- ────────────────────────────────────────────────────────────────────

check-lit : LK-Lit 0
check-lit = T₁ , (T₁ v∷ vNil)

check-ls3 : List (LK-Lit 0)
check-ls3 = check-lit ∷ check-lit ∷ check-lit ∷ []

check-all3 : LK-AllT₁ 0 check-ls3
check-all3 = (fzero , refl) , (fzero , refl) , (fzero , refl) , tt

-- 计账自证：3 字 × 7 步 = 21（与下面写死的 21 对照）
check-fuel3 : LK-fuelL check-ls3 ≡ 21
check-fuel3 = refl

check-cfg3 : Trit → C2 LK-Q LK-Σ
check-cfg3 v = mk2 [] (qLit LK-ph₀)
                   (hdOf LK-b (LK-cellsL check-ls3 (LK-t T₂ ∷ [])))
                   (tlOf (LK-cellsL check-ls3 (LK-t T₂ ∷ [])))
                   [] LK-m (LK-wl (LK-vl (v v∷ vNil)) ++ (LK-e ∷ []))

-- 一个子句三个文字、见证值全 T₀ ⟹ 子句不满足 ⟹ fk = false（pos 回卷到 T₀、ck 清零）
check-run3-allfalse :
  C2.st (runB tm-look LK-b 21 (check-cfg3 T₀)) ≡ qLit (T₀ , false , false)
check-run3-allfalse = refl

-- 见证值 = T₁（三个文字都真）⟹ 子句满足 ⟹ fk 保持 true、ck 清零
check-run3-hit :
  C2.st (runB tm-look LK-b 21 (check-cfg3 T₁)) ≡ qLit (T₀ , false , true)
check-run3-hit = refl

-- 负文字（sign T₀ = σ₋）⟹ 取 negate：a[v] = T₁ 但 negate T₁ = T₂ ⟹ 三个文字全假
check-litNeg : LK-Lit 0
check-litNeg = T₀ , (T₁ v∷ vNil)

check-lsNeg : List (LK-Lit 0)
check-lsNeg = check-litNeg ∷ check-litNeg ∷ check-litNeg ∷ []

check-allNeg : LK-AllT₁ 0 check-lsNeg
check-allNeg = (fzero , refl) , (fzero , refl) , (fzero , refl) , tt

check-run3-neg :
  C2.st (runB tm-look LK-b 21
    (mk2 [] (qLit LK-ph₀)
         (hdOf LK-b (LK-cellsL check-lsNeg (LK-t T₂ ∷ [])))
         (tlOf (LK-cellsL check-lsNeg (LK-t T₂ ∷ [])))
         [] LK-m (LK-wl (LK-vl (T₁ v∷ vNil)) ++ (LK-e ∷ []))))
  ≡ qLit (T₀ , false , false)
check-run3-neg = refl

-- 两个不同变元的文字共用**同一份**见证块：a = (T₀, T₁) ⟹ x₀ 文字假、x₁ 文字真
check-litA : LK-Lit 1
check-litA = T₁ , (T₁ v∷ T₀ v∷ vNil)

check-litB : LK-Lit 1
check-litB = T₁ , (T₀ v∷ T₁ v∷ vNil)

check-lsAB : List (LK-Lit 1)
check-lsAB = check-litA ∷ check-litB ∷ []

check-allAB : LK-AllT₁ 1 check-lsAB
check-allAB = (fzero , refl) , (fsuc fzero , refl) , tt

check-fuelAB : LK-fuelL check-lsAB ≡ 18
check-fuelAB = refl

check-runAB :
  C2.st (runB tm-look LK-b 18
    (mk2 [] (qLit LK-ph₀)
         (hdOf LK-b (LK-cellsL check-lsAB (LK-t T₂ ∷ [])))
         (tlOf (LK-cellsL check-lsAB (LK-t T₂ ∷ [])))
         [] LK-m (LK-wl (LK-vl (T₀ v∷ T₁ v∷ vNil)) ++ (LK-e ∷ []))))
  ≡ qLit (T₂ , true , true)
check-runAB = refl


-- ────────────────────────────────────────────────────────────────────
-- §5c 语义桥核对：机器侧与库内侧各自 refl，定理把两侧缝在一起
-- ────────────────────────────────────────────────────────────────────
check-lmc : LK-Clause 0
check-lmc = check-lit , check-lit , check-lit

-- 解码口径：三个正文字、独热 fzero ⟹ 库内文字 (σ₊ , fzero)
check-lib-clause :
  LK-clause→lib check-lmc ≡ ((σ₊ , fzero) , (σ₊ , fzero) , (σ₊ , fzero))
check-lib-clause = refl

-- 库内一侧：子句真 ⟹ 公式真
check-satF-1 :
  satFormula (T₁ v∷ vNil) (map LK-clause→lib (check-lmc v∷ vNil)) ≡ true
check-satF-1 = refl

-- 机器一侧 21 步到同一个 true —— 走**定理实例**，不是手写 refl
check-bridge-1 :
  C2.st (runB tm-look LK-b 21 (check-cfg3 T₁)) ≡ qLit (T₀ , false , true)
check-bridge-1 = LK-look-sat 0 (check-lmc v∷ vNil) (T₁ v∷ vNil) [] T₂ [] [] check-all3

-- 库内一侧：见证全 T₀ ⟹ 子句假
check-satF-0 :
  satFormula (T₀ v∷ vNil) (map LK-clause→lib (check-lmc v∷ vNil)) ≡ false
check-satF-0 = refl

-- 两个子句（第二个是三个**负**文字）⟹ AND 跨子句：一真一假 ⟹ 公式假
check-lmc2 : LK-Clause 0
check-lmc2 = check-litNeg , check-litNeg , check-litNeg

check-all-2 : LK-AllT₁ 0 (LK-flatV (check-lmc v∷ check-lmc2 v∷ vNil))
check-all-2 = (fzero , refl) , (fzero , refl) , (fzero , refl)
            , (fzero , refl) , (fzero , refl) , (fzero , refl) , tt

-- 6 个文字 × 7 步 = 42（逐字拼接燃料与写死的 42 对照）
check-fuel-2 : LK-fuelL (LK-flatV (check-lmc v∷ check-lmc2 v∷ vNil)) ≡ 42
check-fuel-2 = refl

check-satF-2 :
  satFormula (T₁ v∷ vNil) (map LK-clause→lib (check-lmc v∷ check-lmc2 v∷ vNil)) ≡ false
check-satF-2 = refl

-- 同一格局先用 refl 暴力跑一遍（与下面的定理实例互证：一条走定义、一条走证明）
check-run2-refl :
  C2.st (runB tm-look LK-b 42
    (mk2 [] (qLit LK-ph₀)
         (hdOf LK-b (LK-cellsL (LK-flatV (check-lmc v∷ check-lmc2 v∷ vNil))
                               (LK-t T₂ ∷ [])))
         (tlOf (LK-cellsL (LK-flatV (check-lmc v∷ check-lmc2 v∷ vNil))
                          (LK-t T₂ ∷ [])))
         [] LK-m (LK-wl (LK-vl (T₁ v∷ vNil)) ++ (LK-e ∷ []))))
  ≡ qLit (T₀ , false , false)
check-run2-refl = refl

check-bridge-2 :
  C2.st (runB tm-look LK-b 42
    (mk2 [] (qLit LK-ph₀)
         (hdOf LK-b (LK-cellsL (LK-flatV (check-lmc v∷ check-lmc2 v∷ vNil))
                               (LK-t T₂ ∷ [])))
         (tlOf (LK-cellsL (LK-flatV (check-lmc v∷ check-lmc2 v∷ vNil))
                          (LK-t T₂ ∷ [])))
         [] LK-m (LK-wl (LK-vl (T₁ v∷ vNil)) ++ (LK-e ∷ []))))
  ≡ qLit (T₀ , false , false)
check-bridge-2 = LK-look-sat 0 (check-lmc v∷ check-lmc2 v∷ vNil) (T₁ v∷ vNil)
                              [] T₂ [] [] check-all-2

-- ────────────────────────────────────────────────────────────────────
-- §5d 编码器核对：编码口径、独热往返、计账、端到端（编码路径）
-- ────────────────────────────────────────────────────────────────────
check-lc : Clause 0
check-lc = (σ₊ , fzero) , (σ₊ , fzero) , (σ₊ , fzero)

-- 正文字 (σ₊ , fzero) 编成 (T₁ , [T₁]) —— 正是 §5b 的 check-lit
check-enc-lit : LK-encLit (σ₊ , fzero) ≡ check-lit
check-enc-lit = refl

-- 负文字：签位换 T₀、独热不变 —— 正是 check-litNeg
check-enc-lit-neg : LK-encLit (σ₋ , fzero) ≡ check-litNeg
check-enc-lit-neg = refl

-- 整子句编码 = §5b/§5c 手搓的 check-lmc
check-enc-clause : LK-encClause check-lc ≡ check-lmc
check-enc-clause = refl

-- 独热（m = 1，两个变元各查一遍）
check-hot-0 : LK-hot 1 fzero ≡ T₁ v∷ (T₀ v∷ vNil)
check-hot-0 = refl

check-hot-1 : LK-hot 1 (fsuc fzero) ≡ T₀ v∷ (T₁ v∷ vNil)
check-hot-1 = refl

check-fromOneHot-1 : fromOneHot 1 (LK-hot 1 (fsuc fzero)) ≡ fsuc fzero
check-fromOneHot-1 = refl

-- 编码路径的燃料：1 子句 = 3 字 = 21 步（与 §5b 写死的 21 对照）
check-fuel-enc-1 : LK-fuelL (LK-flatV (map LK-encClause (check-lc v∷ vNil))) ≡ 21
check-fuel-enc-1 = refl

-- 计账形自证：3c·(2m+7)，c=1、m=0 ⟹ 21
check-steps-enc-1 : (3 * 1) * LK-litSteps 0 ≡ 21
check-steps-enc-1 = refl

-- 端到端（编码路径）：两个子句都真 ⟹ 42 步 ⟹ 真（这个判决此前没有）
check-φ2 : Formula 0 2
check-φ2 = check-lc v∷ check-lc v∷ vNil

check-run-formula-2 :
  C2.st (runB tm-look LK-b ((3 * 2) * LK-litSteps 0)
    (mk2 [] (qLit LK-ph₀)
         (hdOf LK-b (LK-cellsL (LK-flatV (map LK-encClause check-φ2)) (LK-t T₂ ∷ [])))
         (tlOf (LK-cellsL (LK-flatV (map LK-encClause check-φ2)) (LK-t T₂ ∷ [])))
         [] LK-m (LK-wl (LK-vl (T₁ v∷ vNil)) ++ (LK-e ∷ []))))
  ≡ qLit (T₀ , false , true)
check-run-formula-2 = LK-run-formula-steps 0 check-φ2 (T₁ v∷ vNil) [] T₂ [] []

-- 独立复核：同一局面用 refl 暴力跑 42 步（与上式互证：一条走证明、一条走定义）
check-run-formula-2-refl :
  C2.st (runB tm-look LK-b 42
    (mk2 [] (qLit LK-ph₀)
         (hdOf LK-b (LK-cellsL (LK-flatV (map LK-encClause check-φ2)) (LK-t T₂ ∷ [])))
         (tlOf (LK-cellsL (LK-flatV (map LK-encClause check-φ2)) (LK-t T₂ ∷ [])))
         [] LK-m (LK-wl (LK-vl (T₁ v∷ vNil)) ++ (LK-e ∷ []))))
  ≡ qLit (T₀ , false , true)
check-run-formula-2-refl = refl

-- 账目对齐：3c·(2m+7) = 抽象账目 steps(satFormulaC) × (2m+7)（c=1、m=0 ⟹ 21）
check-cost-1 :
  (3 * 1) * LK-litSteps 0
    ≡ steps (satFormulaC (T₁ v∷ vNil) (check-lc v∷ vNil)) * LK-litSteps 0
check-cost-1 = LK-cost 0 (check-lc v∷ vNil) (T₁ v∷ vNil)

-- 判决之后机器并不停：第 22 步把 sentinel 当成「下一个文字」的 sign（幽灵文字）
-- ⟹ 判决必须从第 21 步的状态读（§4h 的 ⚠）
check-after-verdict :
  C2.st (runB tm-look LK-b 22 (check-cfg3 T₁)) ≡ qScan (T₀ , false , true) σ₋ false T₀
check-after-verdict = refl

-- 幽灵文字的代价：+1（扫到 ⊣）+1（相迁移）+3（回走）⟹ 第 27 步停在 qDone
check-settles :
  C2.st (runB tm-look LK-b 27 (check-cfg3 T₁)) ≡ qDone (T₀ , false , true) σ₋ T₀
check-settles = refl

-- 停驻：再走一步不动（带 1 头已是空白 ⟹ 收口 fold 不触发，落在兜底子句）
check-settles-2 :
  C2.st (runB tm-look LK-b 28 (check-cfg3 T₁)) ≡ qDone (T₀ , false , true) σ₋ T₀
check-settles-2 = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   带 2 只有一份见证块（空间 O(m)）：LK-cycleS 的结论与起点同形 ⟹ 每个
--       文字复用同一块，不复制、不增长。带 1 是每文字 m+2 格无重叠 + 末格
--       sentinel；整体代价 **3c·(2m+7)**（LK-run-formula-steps），线性。
-- (ii)  语义闭合：§4i LK-look-sat（fk ≡ satFormula，2 案 Sign 解码 + 一步 assoc）。
-- (iii) 编码闭合：§4j LK-hot/LK-fromOneHot-hot/LK-AllT₁-enc ⟹ LK-run-formula；
--       LK-run-stream 接 SATMember.decFormula ⟹ 原始串入、判决出。
--       **未做**：直接消费 decLit 的 stride-3 重叠格（不重编码）的布局桥；
--       这是省步优化，接口层面已由 Formula 覆盖。
-- (iv)  判决从状态读出（halt 恒假，纯相）：要「停机即判决」需把 qLit 的 fk 出口
--       改成 qAcc/qRej 两态（那会破坏「末端形 = 起点形」的可续跑性，故不做）；
--       与 SATMBridge 的账目对齐（3c·(2m+7) vs tm-sat 的 3/子句）未做。

-- 0 postulate / 0 hole。
