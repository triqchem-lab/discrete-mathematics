{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.TMBridge
-- Counted↔TM 实例级桥——PvsNP 程序 W1 桥接件批二（单旗舰方法示范）
--
-- 【边界声明（头注，必须先读）】本件是**实例级方法示范**：以单旗舰语言
-- L-Head₁（首位检测）闭合「函数层计账判定器 dec-Head₁ ⇌ 图灵机 tm-head」
-- 的双向兼容（§4 TMH-head-bridge，恰 1 步接受口径）。
-- 「任意 Counted 函数可实现为 TM」的**通用**编码桥 = Church-Turing 型深件，
-- 维持 PClass §6(i) / TimeBound §8(i) 的立界，本件**不冒充其闭合**；
-- 「实例自动提升为 TM 多项式语言」只对本件旗舰对成立，不外推。
--
-- 内容五节：
--   §1 Vec→List 小桥 TMH-tapeOf（输入词的带表示）；
--   §2 AcceptsIn 计账谓词 + runN 步进显式诱导引理 + 燃料单调引理 TMH-halt-mono；
--   §3 旗舰实例 tm-head（3 态 qScan/qAcc/qRej，接受语义由状态编码——库内
--      TM record 无接受/拒绝双态字段）；
--   §4 兼容定理 TMH-head-bridge（value (dec-Head₁ n x) ≡ true ⇔ tm-head
--      于 TMH-tapeOf x 恰 1 步接受；双向各一条）；
--   §5 尾注立界清单。
--
-- 分级标注约定（与 TimeBound/PClass 一致）：
--   〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕。
--
-- 工程注记：TuringMachine.runN 内部 where-子句 goN 对**泛型** halt 值不透明
-- 归约（中性 goN 卡住）；本件所有泛型步骤分解显式经 step 诱导（§2
-- TMH-runN-halt / TMH-runN-suc + TMH-halt-mono 的 halt 二分），不假设透明。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.TMBridge where

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Automata.TuringMachine
  using (TM; TConfig; mkTC; step; runN; HaltsAt; Dir; R)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; StepsLE)
open import Sovereign.Algebra.Complexity.PClass
  using (dec-Head₁; headT; isT₁)

-- ────────────────────────────────────────────────────────────────────
-- §1 Vec→List 小桥〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 输入词（n 位 trit 向量）的带表示：右带原序（首位为带首——与 tm-head
-- 「读首符号」的 hdOf/tlOf 语义对齐；位数 n 为规模账目，随桥接定理携带）。
TMH-tapeOf : ∀ (n : ℕ) → Vec Trit n → List Trit
TMH-tapeOf zero    []       = []
TMH-tapeOf (suc n) (t ∷ ts) = t ∷ TMH-tapeOf n ts

-- 核对层〔refl 枚举〕
TMH-check-tapeOf : TMH-tapeOf 3 (T₁ ∷ T₂ ∷ T₀ ∷ []) ≡ (T₁ ∷ T₂ ∷ T₀ ∷ [])
TMH-check-tapeOf = refl

TMH-check-tapeOf-empty : TMH-tapeOf 0 [] ≡ []
TMH-check-tapeOf-empty = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 计账谓词与燃料单调〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- §2.1 runN 步进显式诱导（goN where-子句的泛型归约不透明，由此引理
-- 把「停机冻结」从 goN 内部提到引理面——结构证明）。
-- 冻结：当前态已是停机态 ⟹ 任意燃料 runN 不改格局（goN true = c 直返，
-- 无 step 卷入——此分支可 defeq 闭合，对比下条立界）。
TMH-runN-halt : ∀ {Q Σ} (M : TM Q Σ) (b : Σ) (n : ℕ) (c : TConfig Q Σ)
              → TM.halt M (TConfig.st c) ≡ true
              → runN M b n c ≡ c
TMH-runN-halt M b zero    c ht = refl
TMH-runN-halt M b (suc n) c ht rewrite ht = refl

-- 推进一步：当前态未停 ⟹ runN (suc n) = 先 step 一步再跑 n 步。
-- ⚠〔立界注记——此形状在泛型层不可 defeq 闭合，不设签名〕：
--   「halt M (st c) ≡ false ⟹ runN M b (suc n) c ≡ runN M b n (step M b c)」
--   的任何证明都必须让 goN 归约（参数需为构造子）；而 goN 体冻结**原版**
--   `step M b c`（其内 halt M (st c) 中性），rewrite/with 对目标树出现的
--   替换不穿透 unfold 新生项，陷「step 原版 vs stepH false 版」不等。
--   破局需把 runN/goN 重构为顶层定义（改既有件，本批禁区）或 Church 编码
--   桥（深件）。本件以 §2.3 的 with 二分平行归约绕行（见该节注记），
--   runN 步进语义在**具体实例**（§3 δ 表全 refl）与**泛型单调**（§2.3）
--   两个可用面上闭合。

-- §2.2 计账谓词：恰停于「halt-state=True 的接受态」〔结构定义〕。
-- 接受语义由状态编码（库内 TM record 无接受/拒绝双态字段）：n 燃料后
-- 状态 = qAcc（停于接受态）且 halt qAcc = true（接受态确为停机态）。
-- 空白符固定 T₀（Σ = Trit 的空白裁定）。
-- 初始头位约定：头在**首符号**上（空带头在空白格 T₀）——「恰 1 步读首
-- 分派」要求头已对准首符号。〔对比 Automata §4 cfg0「头在输入左侧空白格、
-- 首步右移读入」约定；两者差一步预移位，属输入编码规范自由度，尾注立界。〕
TMH-hdOf : List Trit → Trit
TMH-hdOf []      = T₀
TMH-hdOf (t ∷ _) = t

TMH-AcceptsIn : ∀ {Q : Set} (M : TM Q Trit) (qAcc : Q) (n : ℕ) (w : List Trit) → Set
TMH-AcceptsIn M qAcc n w =
  (TConfig.st (runN M T₀ n (mkTC [] (TM.q₀ M) (TMH-hdOf w) w)) ≡ qAcc)
  × TM.halt M qAcc ≡ true

-- §2.3 燃料单调引理〔结构证明〕：停机态在 step 下自持（δ(halt 态) 停在
-- 自己——self 前提）⟹ HaltsAt 对燃料单调。对 n 归纳；suc 步按 halt(q₀态)
-- with 二分。⚠ 工程注记：泛型 goN 不透明归约，但本引理两侧等式归约为
-- **平行的中性形**（false 分支两侧同卡于 goN(halt M (st X))，X 为同一
-- step 深展项），不要求 goN unfold 成构造子——with 二分即可闭合；
-- 对比 §2.1 立界（refl 形引理要求 unfold，故死结）。
TMH-halt-mono : ∀ {Q Σ} (M : TM Q Σ) (b : Σ)
              → (∀ (q : Q) (a : Σ) (l r : List Σ)
                 → TM.halt M q ≡ true → step M b (mkTC l q a r) ≡ mkTC l q a r)
              → ∀ (n : ℕ) (c : TConfig Q Σ)
              → HaltsAt M b n c → HaltsAt M b (suc n) c
TMH-halt-mono M b self zero c h rewrite h = h
TMH-halt-mono M b self (suc n) c h with TM.halt M (TConfig.st c)
... | true  = h
... | false = TMH-halt-mono M b self n (step M b c) h

-- ────────────────────────────────────────────────────────────────────
-- §3 旗舰实例 tm-head——读首符号 1 步分派〔refl 实例 + 核对层〕
-- ────────────────────────────────────────────────────────────────────

-- 3 态：扫描态（不停机）·接受态·拒绝态。接受语义由状态编码（库内 TM
-- record 无接受/拒绝双态字段）：qAcc/qRej 均 halt=true，qScan 不停。
data TMH-QH : Set where
  qScan qAcc qRej : TMH-QH

-- δ 表：qScan 三符号显式分派（T₁→接受 / T₀·T₂→拒绝；写出原符号并右移，
-- 对 (T₁∷…) 类输入即「读首符号」）；停机态自持（δ(halt 态) 停在自己，
-- §2.3 self 前提的实例基座）。等式 5 条（qScan×3 显式 + 停机态自持通配
-- ×2）；「逐项可 refl 验证」由下方核对层 6 项承载（4 项停机逐项核对 +
-- 2 项停机判据核对）。
TMH-δh : TMH-QH → Trit → TMH-QH × Trit × Dir
TMH-δh qScan T₁ = (qAcc , T₁ , R)
TMH-δh qScan T₀ = (qRej , T₀ , R)
TMH-δh qScan T₂ = (qRej , T₂ , R)
TMH-δh qAcc  t  = (qAcc , t , R)
TMH-δh qRej  t  = (qRej , t , R)

TMH-haltH : TMH-QH → Bool
TMH-haltH qScan = false
TMH-haltH qAcc  = true
TMH-haltH qRej  = true

tm-head : TM TMH-QH Trit
tm-head = record { δ = TMH-δh ; q₀ = qScan ; halt = TMH-haltH }

-- 自持前提实例〔refl 枚举〕：停机态 step 冻结（defeq）；qScan 分支无居民。
tm-head-self : ∀ (q : TMH-QH) (a : Trit) (l r : List Trit)
             → TM.halt tm-head q ≡ true
             → step tm-head T₀ (mkTC l q a r) ≡ mkTC l q a r
tm-head-self qScan a l r ()
tm-head-self qAcc  a l r h = refl
tm-head-self qRej  a l r h = refl

-- 燃料单调实例化：TMH-halt-mono 对 tm-head 特化。
tm-head-mono : ∀ (n : ℕ) (c : TConfig TMH-QH Trit)
             → HaltsAt tm-head T₀ n c → HaltsAt tm-head T₀ (suc n) c
tm-head-mono = TMH-halt-mono tm-head T₀ tm-head-self

-- 核对层〔refl 枚举〕——逐项核对（初始头在首符号，§2.2 约定）：
-- ①(T₁) 1 步停 qAcc ②(T₀) 1 步停 qRej ③(T₂) 1 步停 qRej ④空带 1 步停
-- qRej（scan 位空白补 T₀）；⑤⑥ qAcc/qRej 确为停机态。
TMH-check-h1 : TConfig.st (runN tm-head T₀ 1 (mkTC [] qScan T₁ [])) ≡ qAcc
TMH-check-h1 = refl

TMH-check-h2 : TConfig.st (runN tm-head T₀ 1 (mkTC [] qScan T₀ [])) ≡ qRej
TMH-check-h2 = refl

TMH-check-h3 : TConfig.st (runN tm-head T₀ 1 (mkTC [] qScan T₂ [])) ≡ qRej
TMH-check-h3 = refl

TMH-check-h4 : TConfig.st (runN tm-head T₀ 1 (mkTC [] qScan T₀ [])) ≡ qRej
TMH-check-h4 = refl

TMH-check-haltAcc : TM.halt tm-head qAcc ≡ true
TMH-check-haltAcc = refl

TMH-check-haltRej : TM.halt tm-head qRej ≡ true
TMH-check-haltRej = refl

-- 冻结核对（衔接 §2.3）：1 步停机后加燃料不改局（具体实例 defeq）。
TMH-check-freeze : runN tm-head T₀ 5 (mkTC [] qScan T₁ [])
                 ≡ runN tm-head T₀ 1 (mkTC [] qScan T₁ [])
TMH-check-freeze = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 兼容定理 TMH-head-bridge——实例级 Counted↔TM 闭合
-- ────────────────────────────────────────────────────────────────────

-- → 方向：函数层接受 ⟹ tm-head 恰 1 步接受〔refl 枚举 + absurd〕。
-- T₁ 分支：1 步分派 qAcc（带改写/移头全 definitional）；
-- T₀/T₂/[] 分支：dec-Head₁ 判 false，前提 false ≡ true 无居民。
TMH-head-bridge→ : ∀ (n : ℕ) (x : Vec Trit n)
                 → value (dec-Head₁ n x) ≡ true
                 → TMH-AcceptsIn tm-head qAcc 1 (TMH-tapeOf n x)
TMH-head-bridge→ n (T₁ ∷ xs) h = refl , refl
TMH-head-bridge→ n (T₀ ∷ xs) ()
TMH-head-bridge→ n (T₂ ∷ xs) ()
TMH-head-bridge→ n []        ()

-- ← 方向：tm-head 恰 1 步接受 ⟹ 函数层接受〔refl 枚举 + absurd〕。
-- T₁ 分支：dec-Head₁ 值 true 由定义性归约自足（前提冗余不引用）；
-- T₀/T₂/[] 分支：1 步必停 qRej，接受前提 st ≡ qAcc 给出 qRej ≡ qAcc
-- 无居民。
TMH-head-bridge← : ∀ (n : ℕ) (x : Vec Trit n)
                 → TMH-AcceptsIn tm-head qAcc 1 (TMH-tapeOf n x)
                 → value (dec-Head₁ n x) ≡ true
TMH-head-bridge← n (T₁ ∷ xs) acc = refl
TMH-head-bridge← n (T₀ ∷ xs) ((), _)
TMH-head-bridge← n (T₂ ∷ xs) ((), _)
TMH-head-bridge← n []        ((), _)

-- 兼容定理（双向合取）：value (dec-Head₁ n x) ≡ true ⇔ tm-head 于带
-- TMH-tapeOf n x 恰 1 步接受——「实例级 Counted↔TM」的闭合点。
TMH-head-bridge : ∀ (n : ℕ) (x : Vec Trit n)
  → (value (dec-Head₁ n x) ≡ true → TMH-AcceptsIn tm-head qAcc 1 (TMH-tapeOf n x))
  × (TMH-AcceptsIn tm-head qAcc 1 (TMH-tapeOf n x) → value (dec-Head₁ n x) ≡ true)
TMH-head-bridge n x = TMH-head-bridge→ n x , TMH-head-bridge← n x

-- 计账对齐〔refl 枚举〕：dec-Head₁ 账目恰为 1（StepsLE 口径）——桥两侧
-- 时间口径同阶（函数层 steps = TM 层燃料 1）。
TMH-head-steps : ∀ (n : ℕ) (x : Vec Trit n) → steps (dec-Head₁ n x) ≡ 1
TMH-head-steps n x = refl

TMH-head-StepsLE : ∀ (n : ℕ) (x : Vec Trit n) → StepsLE (dec-Head₁ n x) 1
TMH-head-StepsLE n x = s≤s z≤n

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   实例级示范边界：本件只闭合旗舰对 dec-Head₁ ⇌ tm-head（恰 1 步
--       口径）。「任意 Counted 函数可实现为 TM」的通用编码桥 = Church-Turing
--       型深件，维持 PClass §6(i) / TimeBound §8(i) 立界，本件不冒充闭合；
--       head-P 的 TM 多项式语言提升只在旗舰对成立，不外推。
-- (ii)  runN 泛型步进立界：「halt=false ⟹ runN (suc n) c = runN n (step c)」
--       的 refl 形引理在泛型层不可 defeq 闭合（goN where-体冻结原版 step，
--       §2.1）；本件以 §2.3 with 二分平行归约闭合燃料单调，步进语义的
--       全泛型面属深件（需重构 runN 为顶层定义——改既有件禁区——或 Church
--       编码桥）。
-- (iii) 输入编码约定：初始头在首符号（空带头在空白格 T₀），与 Automata §4
--       cfg0「头在输入左侧空白格、首步右移读入」约定差一步预移位——规范
--       自由度；空带判 qRej（无首符号即拒绝）。
-- (iv)  接受/拒绝编码：库内 TM record 无接受/拒绝双态字段，接受语义由
--       状态编码（qAcc/qRej，均 halt=true）；「接受 = 恰停于 qAcc」是本件
--       定义（TMH-AcceptsIn），Computes 的输出带语义（Automata §3 注）不涉及。
-- (v)   桥的双向是**等式级**（value ≡ true ⇔ 恰 1 步接受），非渐近；
--       大 O 渐近层维持 TimeBound §8(ii) 立界。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
