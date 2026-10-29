{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATLook
-- 含寻址：两带 lockstep 解变元号并取见证值（SATMBridge 立界 (i) 的机器侧）
--
-- 【本件闭合什么】SATMBridge 的验证器用「配对单元」编码：a[v] 的读取被编码层
-- 预先合成、不计机内步数。本件把这一步搬进机器：
--
--   带 1：逐文字放 [sign, o₀ … o_m]（onehot 变元号原样，§3 的 os）
--   带 2：逐文字放 [⊢, a₀ … a_m]（见证的逐文字副本，§3 的 ws）
--
-- 机器从 (sign, ⊢) 出发读符号，然后把带 1 的 onehot 与带 2 的见证**锁步**
-- 前移：见到首个 T₁ 就把该处见证值抄进状态，此后不再覆盖（= fromOneHot 的
-- 「首个 T₁」语义；LK-pick-cells 把两处钉死）。于是「解变元号 + 取 a[v]」
-- 由机器完成，不再是编码层的免费午餐。
--
-- 计账：每文字 1（符号步）+ (m+1)（锁步）= m+2 步（LK-look，精确等式）。
--
-- 【诚实边界（尾注 §6）】
--   (i)  带 2 的**逐文字副本**仍是编码（空间 O(m·#literals)）。不复制就得
--        每文字后回走 O(m) 格重新对齐；回走相可用 MultiTape.runB-+ 与锁步相
--        拼接，本件未做（下一步）。
--   (ii) 本引擎是**相**（halt 恒假）：公式层 OR/AND 控制器与终止符收口已在
--        SATMBridge（tm-sat）闭合；两件拼成整机（引擎 × 控制器）未做。
--   (iii) 带 1 的「每文字 m+2 格无重叠」是本机输入格式；库内 decLit 的 stride
--        3（m > 1 时重叠）到本格式的转换属编码层，未做。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATLook where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup) renaming ([] to vNil; _∷_ to _v∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Automata.MultiTape
  using (Dir3; dL; dR; dN; C2; mk2; TM2; mt-stepH; runB; runB-step; runB-+)
open import Sovereign.Algebra.Automata.TuringMachine using (hdOf; tlOf)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; signOf; fromOneHot)

-- ────────────────────────────────────────────────────────────────────
-- §1 字母表 / 状态 / δ 表〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

data LK-Σ : Set where
  LK-b : LK-Σ              -- 空白
  LK-m : LK-Σ              -- 见证块起点标记（每文字一个，锁步对齐用）
  LK-t : Trit → LK-Σ       -- trit 码

-- 符号的 trit 值（非 trit 码按空白读 T₀）
LK-v : LK-Σ → Trit
LK-v (LK-t t) = t
LK-v _        = T₀

-- 三态：待读符号 / 锁步扫 onehot（符号, 已找到, 值）/ 收口
data LK-Q : Set where
  qLit  : LK-Q
  qScan : Sign → Bool → Trit → LK-Q
  qNext : Sign → Trit → LK-Q

-- δ：符号步读 (sign, ⊢) 双右移；锁步每格读 (oᵢ, aᵢ) 双右移；见到首个 T₁
--     即记下该处的见证值且此后不再覆盖（对见证格不作要求：耗尽时读空白 ⟹ T₀，
--     与 LK-pick 的耗尽口径一致）；收口相不动带。
lk-δ : LK-Q → LK-Σ → LK-Σ → LK-Q × (LK-Σ × Dir3) × (LK-Σ × Dir3)
lk-δ qLit (LK-t sg) LK-m =
  qScan (signOf sg) false T₀ , (LK-t sg , dR) , (LK-m , dR)
lk-δ qLit x y = qNext (signOf T₀) T₀ , (x , dN) , (y , dN)      -- 形状外（不可达）
lk-δ (qScan s false v) (LK-t T₁) y =
  qScan s true (LK-v y) , (LK-t T₁ , dR) , (y , dR)
lk-δ (qScan s false v) x y = qScan s false v , (x , dR) , (y , dR)
lk-δ (qScan s true  v) x y = qScan s true  v , (x , dR) , (y , dR)
lk-δ (qNext s v) x y = qNext s v , (x , dN) , (y , dN)

tm-look : TM2 LK-Q LK-Σ
tm-look = record { δ = lk-δ ; q₀ = qLit ; halt = λ _ → false }

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
-- §3 锁步扫描（scan1 在前：scan0 调用它）〔结构归纳于 onehot 余表〕
-- ────────────────────────────────────────────────────────────────────
-- 陈述自相似：余表 os 的头/尾一律写 hdOf/tlOf os，一步之后恰落在 tlOf os 的
-- 同一命题上（无需 list-eta 引理）。

-- 已找到：值不再改写，扫完保持
LK-scan1 : ∀ (sg : Sign) (v : Trit) (os : List LK-Σ) (ws : List Trit)
             (l₁ l₂ : List LK-Σ)
         → C2.st (runB tm-look LK-b (length os)
             (mk2 l₁ (qScan sg true v) (hdOf LK-b os) (tlOf os)
                  l₂ (hdOf LK-b (LK-wl ws)) (tlOf (LK-wl ws))))
           ≡ qScan sg true v
LK-scan1 sg v [] ws l₁ l₂ = refl
LK-scan1 sg v (x ∷ os) [] l₁ l₂ =
  LK-scan1 sg v os [] (x ∷ l₁) (LK-b ∷ l₂)
LK-scan1 sg v (x ∷ os) (b ∷ ws) l₁ l₂ =
  LK-scan1 sg v os ws (x ∷ l₁) (LK-t b ∷ l₂)

-- 未找到：扫完 os 后，状态 = (有没有 T₁, 首个 T₁ 处的见证值)
LK-scan0 : ∀ (sg : Sign) (os : List LK-Σ) (ws : List Trit) (l₁ l₂ : List LK-Σ)
         → C2.st (runB tm-look LK-b (length os)
             (mk2 l₁ (qScan sg false T₀) (hdOf LK-b os) (tlOf os)
                  l₂ (hdOf LK-b (LK-wl ws)) (tlOf (LK-wl ws))))
           ≡ qScan sg (LK-anyT₁ os) (LK-pick os ws)
LK-scan0 sg [] ws l₁ l₂ = refl
LK-scan0 sg (LK-t T₁ ∷ os) [] l₁ l₂ =
  LK-scan1 sg T₀ os [] (LK-t T₁ ∷ l₁) (LK-b ∷ l₂)
LK-scan0 sg (LK-t T₁ ∷ os) (b ∷ ws) l₁ l₂ =
  LK-scan1 sg b os ws (LK-t T₁ ∷ l₁) (LK-t b ∷ l₂)
LK-scan0 sg (LK-t T₀ ∷ os) [] l₁ l₂ =
  trans (LK-scan0 sg os [] (LK-t T₀ ∷ l₁) (LK-b ∷ l₂))
               (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scan0 sg (LK-t T₀ ∷ os) (b ∷ ws) l₁ l₂ =
  LK-scan0 sg os ws (LK-t T₀ ∷ l₁) (LK-t b ∷ l₂)
LK-scan0 sg (LK-t T₂ ∷ os) [] l₁ l₂ =
  trans (LK-scan0 sg os [] (LK-t T₂ ∷ l₁) (LK-b ∷ l₂))
               (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scan0 sg (LK-t T₂ ∷ os) (b ∷ ws) l₁ l₂ =
  LK-scan0 sg os ws (LK-t T₂ ∷ l₁) (LK-t b ∷ l₂)
LK-scan0 sg (LK-b ∷ os) [] l₁ l₂ =
  trans (LK-scan0 sg os [] (LK-b ∷ l₁) (LK-b ∷ l₂))
               (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scan0 sg (LK-b ∷ os) (b ∷ ws) l₁ l₂ =
  LK-scan0 sg os ws (LK-b ∷ l₁) (LK-t b ∷ l₂)
LK-scan0 sg (LK-m ∷ os) [] l₁ l₂ =
  trans (LK-scan0 sg os [] (LK-m ∷ l₁) (LK-b ∷ l₂))
               (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scan0 sg (LK-m ∷ os) (b ∷ ws) l₁ l₂ =
  LK-scan0 sg os ws (LK-m ∷ l₁) (LK-t b ∷ l₂)

-- ────────────────────────────────────────────────────────────────────
-- §4 ★ 寻址主定理：一次文字 = 符号步 + 锁步扫，终态携带 (符号, a[v])
-- ────────────────────────────────────────────────────────────────────

-- 符号步的显式结果（refl：状态/两格皆构造子 ⟹ δ 可算）
LK-step1 : ∀ (sg : Trit) (os : List LK-Σ) (ws : List Trit) (l₁ l₂ : List LK-Σ)
         → mt-stepH tm-look LK-b false (mk2 l₁ qLit (LK-t sg) os l₂ LK-m (LK-wl ws))
           ≡ mk2 (LK-t sg ∷ l₁) (qScan (signOf sg) false T₀) (hdOf LK-b os) (tlOf os)
                 (LK-m ∷ l₂) (hdOf LK-b (LK-wl ws)) (tlOf (LK-wl ws))
LK-step1 sg os ws l₁ l₂ = refl

LK-look : ∀ (sg : Trit) (os : List LK-Σ) (ws : List Trit) (l₁ l₂ : List LK-Σ)
        → C2.st (runB tm-look LK-b (suc (length os))
            (mk2 l₁ qLit (LK-t sg) os l₂ LK-m (LK-wl ws)))
          ≡ qScan (signOf sg) (LK-anyT₁ os) (LK-pick os ws)
LK-look sg os ws l₁ l₂ =
  LK-scan0 (signOf sg) os ws (LK-t sg ∷ l₁) (LK-m ∷ l₂)

-- 与库内语义对齐：终态值 = lookup a (fromOneHot m o)（需 ∃T₁）
LK-look-sem : ∀ (m : ℕ) (sg : Trit) (o a : Vec Trit (suc m))
            → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
            → C2.st (runB tm-look LK-b (suc (length (LK-cells o)))
                (mk2 [] qLit (LK-t sg) (LK-cells o) [] LK-m (LK-wl (LK-vl a))))
              ≡ qScan (signOf sg) true (lookup a (fromOneHot m o))
LK-look-sem m sg o a h =
  trans (trans (LK-look sg (LK-cells o) (LK-vl a) [] [])
               (cong (λ z → qScan (signOf sg) z (LK-pick (LK-cells o) (LK-vl a)))
                     (LK-anyT₁-cells m o h)))
        (cong (qScan (signOf sg) true) (LK-pick-cells m o a h))

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
    (mk2 [] qLit (LK-t T₁) (LK-t T₁ ∷ []) [] LK-m (LK-t T₂ ∷ [])))
  ≡ qScan σ₊ true T₂
check-look-0 = refl

-- 端到端（符号 T₀ = σ₋）：值仍取 a₀
check-look-0-neg :
  C2.st (runB tm-look LK-b 2
    (mk2 [] qLit (LK-t T₀) (LK-t T₁ ∷ []) [] LK-m (LK-t T₁ ∷ [])))
  ≡ qScan σ₋ true T₁
check-look-0-neg = refl

-- 端到端（m = 1）：onehot = [T₀, T₁] ⟹ 首个 T₁ 在第 2 格 ⟹ 取 a₁ = T₀
check-look-1 :
  C2.st (runB tm-look LK-b 3
    (mk2 [] qLit (LK-t T₁) (LK-t T₀ ∷ LK-t T₁ ∷ []) [] LK-m
         (LK-t T₁ ∷ LK-t T₀ ∷ [])))
  ≡ qScan σ₊ true T₀
check-look-1 = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   带 2 逐文字副本是编码（空间 O(m·#literals)）；不复制需回走相，
--       回走相 + 锁步相的拼接靠 MultiTape.runB-+（下一步）。
-- (ii)  公式层 OR/AND 控制器 + 终止符收口已在 SATMBridge(tm-sat)；引擎 ×
--       控制器的**整机拼装**未做。
-- (iii) 本机带 1 格式（每文字 m+2 格、无重叠）与库内 decLit 的 stride-3
--       重叠格式之间的转换属编码层，未做。
-- (iv)  引擎 halt 恒假（纯相），故只用 runB；换 runN2 需 runN2-blind
--       （MultiTape 已备），拼装时再用。

-- 0 postulate / 0 hole。
