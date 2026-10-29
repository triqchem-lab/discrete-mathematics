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
--   (i)  带 2 的**逐文字副本**是编码（空间 O(m·#L)）。无复制的回走相已落地
--        （§4b LK-walk/LK-back + §4c 带形不变式 LK-lw/LK-rw-wl）：回走**把带 2
--        完全复原**（头回 ⊢、左带回 l₂），故每个文字只付自己那一块 (m+1) 格，
--        单文字总代价 **2m+6**（1 符号 + (m+1) 锁步 + 1 相迁移 + (m+3) 回走）
--        = **线性**，整体 L·(2m+6)。⚠ 此前写 2m+5 漏算了相迁移一步（见 §4f）。
--        ⚠ 更正：此前写的「第 j 个文字回走 j(m+1) ⟹ Θ(m·L²)」是**错的**——
--        那只有在不回填（见证被单调消费）时才成立；回走相回填后不累积。
--        仍缺的是把「符号步 + 锁步 + 回走」拼成单个 runB 的整机引理
--        （需一条 full-config 锁步引理；三段燃料已各自钉死）。
--   (ii) 本引擎是**相**（halt 恒假）：公式层 OR/AND 控制器与终止符收口已在
--        SATMBridge（tm-sat）闭合；两件拼成整机（引擎 × 控制器）未做。
--   (iii) 带 1 的「每文字 m+2 格无重叠」是本机输入格式；库内 decLit 的 stride
--        3（m > 1 时重叠）到本格式的转换属编码层，未做。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATLook where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup) renaming ([] to vNil; _∷_ to _v∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

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

-- 状态：待读符号 / 锁步扫 onehot（符号, 已找到, 值）/ 回走 / 收口（携带结果）
data LK-Q : Set where
  qLit  : LK-Q
  qScan : Sign → Bool → Trit → LK-Q
  qBack : Sign → Trit → LK-Q            -- 回走：把带 2 的头走回 ⊢ 标记
  qDone : Sign → Trit → LK-Q            -- 一个文字收口（携带 (符号, a[v])）

-- δ：符号步读 (sign, ⊢) 双右移；锁步每格读 (oᵢ, aᵢ) 双右移；见到首个 T₁
--     即记下该处的见证值且此后不再覆盖（对见证格不作要求：耗尽时读空白 ⟹ T₀，
--     与 LK-pick 的耗尽口径一致）；收口相不动带。
lk-δ : LK-Q → LK-Σ → LK-Σ → LK-Q × (LK-Σ × Dir3) × (LK-Σ × Dir3)
lk-δ qLit (LK-t sg) LK-m =
  qScan (signOf sg) false T₀ , (LK-t sg , dR) , (LK-m , dR)
lk-δ qLit x y = qDone (signOf T₀) T₀ , (x , dN) , (y , dN)      -- 形状外（不可达）
lk-δ (qScan s false v) (LK-t T₁) y =
  qScan s true (LK-v y) , (LK-t T₁ , dR) , (y , dR)
-- 见证块走完（带 2 读到空白）⟹ 相迁移：锁步相 → 回走相
-- （带 1 不动——头 1 已停在下一文字的 sign 上；带 2 停在空白上，交给回走首步）
lk-δ (qScan s false v) x LK-b = qBack s v , (x , dN) , (LK-b , dN)
lk-δ (qScan s true  v) x LK-b = qBack s v , (x , dN) , (LK-b , dN)
lk-δ (qScan s false v) x y = qScan s false v , (x , dR) , (y , dR)
lk-δ (qScan s true  v) x y = qScan s true  v , (x , dR) , (y , dR)
-- 回走相：带 1 不动（头 1 已停在下一文字的 sign 上）；带 2 左移，
-- 见到 ⊢ 标记即收口（dN 停在该标记上——下一次文字的符号步要读的就是它）
lk-δ (qBack s v) x LK-m = qDone s v , (x , dN) , (LK-m , dN)
lk-δ (qBack s v) x y = qBack s v , (x , dN) , (y , dL)
lk-δ (qDone s v) x y = qDone s v , (x , dN) , (y , dN)

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
-- （原 §3/§4 的 list 级锁步引理已删除：加相迁移子句后「见证耗尽」分支不再
--   保持 qScan，而 Vec 级 LK-lock 用等长前提天然规避该分支；引擎定理改由
--   LK-lock 重推，见 §4e。）

-- §4b 回走相（无复制时的对齐回收）〔结构归纳于左带〕
-- ────────────────────────────────────────────────────────────────────
-- 锁步扫完，带 2 的头停在见证块之后；要回到 ⊢ 才能开始下一文字。
-- 左带 = cs（已消费见证格的逆序）++ (⊢ ∷ l₂)：移动左时消费左带的头，
-- 故 cs 用 trit 列表给出 ⟹ 归纳是结构的（无需 list-reverse 引理）。
-- 计账：LK-walk = |cs| + 2 步；LK-back = |cs| + 2 步（首步从空白跨到首格）。

LK-walk : ∀ (sg : Sign) (v : Trit) (h : Trit) (cs : List Trit) (l₂ : List LK-Σ)
            (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
        → C2.st (runB tm-look LK-b (suc (suc (length cs)))
            (mk2 l₁ (qBack sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) (LK-t h) r₂))
          ≡ qDone sg v
LK-walk sg v h [] l₂ l₁ h₁ r₁ r₂ = refl
LK-walk sg v h (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walk sg v b cs l₂ l₁ h₁ r₁ (LK-t h ∷ r₂)

LK-back : ∀ (sg : Sign) (v : Trit) (cs : List Trit) (l₂ : List LK-Σ)
            (l₁ : List LK-Σ) (h₁ : LK-Σ) (r₁ r₂ : List LK-Σ)
        → C2.st (runB tm-look LK-b (suc (suc (length cs)))
            (mk2 l₁ (qBack sg v) h₁ r₁ (LK-wl cs ++ (LK-m ∷ l₂)) LK-b r₂))
          ≡ qDone sg v
LK-back sg v [] l₂ l₁ h₁ r₁ r₂ = refl
LK-back sg v (b ∷ cs) l₂ l₁ h₁ r₁ r₂ =
  LK-walk sg v b cs l₂ l₁ h₁ r₁ (LK-b ∷ r₂)

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
LK-scanned : (sg : Sign) (b : Bool) (v : Trit)
             (os : List LK-Σ) (ws : List Trit) → LK-Q
LK-scanned sg b v [] ws = qScan sg b v
LK-scanned sg false v (LK-t T₁ ∷ os) (w ∷ ws) = LK-scanned sg true w os ws
LK-scanned sg false v (LK-t T₁ ∷ os) [] = LK-scanned sg true (LK-v LK-b) os []
LK-scanned sg true  v (LK-t T₁ ∷ os) ws = LK-scanned sg true v os (LK-drop1 ws)
LK-scanned sg b v (LK-t T₀ ∷ os) ws = LK-scanned sg b v os (LK-drop1 ws)
LK-scanned sg b v (LK-t T₂ ∷ os) ws = LK-scanned sg b v os (LK-drop1 ws)
LK-scanned sg b v (LK-b ∷ os) ws = LK-scanned sg b v os (LK-drop1 ws)
LK-scanned sg b v (LK-m ∷ os) ws = LK-scanned sg b v os (LK-drop1 ws)

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
LK-scannedQ : (sg : Sign) (b : Bool) (v : Trit) → List (LK-Σ × Trit) → LK-Q
LK-scannedQ sg b v [] = qScan sg b v
LK-scannedQ sg false v ((LK-t T₁ , w) ∷ ps) = LK-scannedQ sg true w ps
LK-scannedQ sg false v ((q , w) ∷ ps) = LK-scannedQ sg false v ps
LK-scannedQ sg true v ((q , w) ∷ ps) = LK-scannedQ sg true v ps

-- 规范的投影律（§4e）：LK-scanned 与「有没有 T₁ / 首个 T₁ 处的值」对齐
--   LK-scanned-true：已找到后不再变（对 v 全泛型）
--   LK-scanned-spec：未找到起步 ⟹ (anyT₁, pick)
LK-scanned-true : ∀ (sg : Sign) (v : Trit) (os : List LK-Σ) (ws : List Trit)
                → LK-scanned sg true v os ws ≡ qScan sg true v
LK-scanned-true sg v [] ws = refl
LK-scanned-true sg v (LK-t T₁ ∷ os) ws = LK-scanned-true sg v os (LK-drop1 ws)
LK-scanned-true sg v (LK-t T₀ ∷ os) ws = LK-scanned-true sg v os (LK-drop1 ws)
LK-scanned-true sg v (LK-t T₂ ∷ os) ws = LK-scanned-true sg v os (LK-drop1 ws)
LK-scanned-true sg v (LK-b ∷ os) ws = LK-scanned-true sg v os (LK-drop1 ws)
LK-scanned-true sg v (LK-m ∷ os) ws = LK-scanned-true sg v os (LK-drop1 ws)

LK-scanned-spec : ∀ (sg : Sign) (os : List LK-Σ) (ws : List Trit)
                → LK-scanned sg false T₀ os ws
                  ≡ qScan sg (LK-anyT₁ os) (LK-pick os ws)
LK-scanned-spec sg [] ws = refl
LK-scanned-spec sg (LK-t T₁ ∷ os) (w ∷ ws) = LK-scanned-true sg w os ws
LK-scanned-spec sg (LK-t T₁ ∷ os) [] =
  trans (LK-scanned-true sg (LK-v LK-b) os []) refl
LK-scanned-spec sg (LK-t T₀ ∷ os) [] =
  trans (LK-scanned-spec sg os [])
        (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec sg (LK-t T₀ ∷ os) (w ∷ ws) = LK-scanned-spec sg os ws
LK-scanned-spec sg (LK-t T₂ ∷ os) [] =
  trans (LK-scanned-spec sg os [])
        (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec sg (LK-t T₂ ∷ os) (w ∷ ws) = LK-scanned-spec sg os ws
LK-scanned-spec sg (LK-b ∷ os) [] =
  trans (LK-scanned-spec sg os [])
        (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec sg (LK-b ∷ os) (w ∷ ws) = LK-scanned-spec sg os ws
LK-scanned-spec sg (LK-m ∷ os) [] =
  trans (LK-scanned-spec sg os [])
        (cong (λ t → qScan sg (LK-anyT₁ os) t) (LK-pick-nil os))
LK-scanned-spec sg (LK-m ∷ os) (w ∷ ws) = LK-scanned-spec sg os ws

-- ★ full-config 锁步引理（结论形 = 未来态：state 与两带同时给出）
-- 形状要点（上一轮的诊断）：b、v 为变量时 δ 不可归约 ⟹ b 逐真值分案；
-- 分案后「已找到」变体必须对 v 全泛型（否则 T₁ 之后的值会被重写）。

-- 已找到变体：值不再覆盖
LK-lock-true : ∀ (sg : Sign) (v : Trit) (m : ℕ) (o a : Vec Trit (suc m))
                 (acc l₁ : List LK-Σ) (h₁ : LK-Σ)
             → runB tm-look LK-b (suc m)
                 (mk2 l₁ (qScan sg true v)
                      (hdOf LK-b (LK-cells o)) (tlOf (LK-cells o))
                      acc (hdOf LK-b (LK-wl (LK-vl a))) (tlOf (LK-wl (LK-vl a))))
               ≡ mk2 (LK-rc (LK-cells o) l₁)
                     (LK-scanned sg true v (LK-cells o) (LK-vl a)) LK-b []
                     (LK-rw (LK-vl a) acc) LK-b []
LK-lock-true sg v zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock-true sg v zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock-true sg v zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock-true sg v (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true sg v m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock-true sg v (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true sg v m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock-true sg v (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true sg v m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) (hdOf LK-b (LK-cells os))

-- 未找到变体（b = false 固定）
LK-lock : ∀ (sg : Sign) (m : ℕ) (o a : Vec Trit (suc m))
            (acc l₁ : List LK-Σ) (h₁ : LK-Σ)
        → runB tm-look LK-b (suc m)
            (mk2 l₁ (qScan sg false T₀)
                 (hdOf LK-b (LK-cells o)) (tlOf (LK-cells o))
                 acc (hdOf LK-b (LK-wl (LK-vl a))) (tlOf (LK-wl (LK-vl a))))
          ≡ mk2 (LK-rc (LK-cells o) l₁)
                (LK-scanned sg false T₀ (LK-cells o) (LK-vl a)) LK-b []
                (LK-rw (LK-vl a) acc) LK-b []
LK-lock sg zero (T₁ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock sg zero (T₀ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock sg zero (T₂ v∷ vNil) (w v∷ vNil) acc l₁ h₁ = refl
LK-lock sg (suc m) (T₁ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock-true sg w m os as (LK-t w ∷ acc) (LK-t T₁ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock sg (suc m) (T₀ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock sg m os as (LK-t w ∷ acc) (LK-t T₀ ∷ l₁) (hdOf LK-b (LK-cells os))
LK-lock sg (suc m) (T₂ v∷ os) (w v∷ as) acc l₁ h₁ =
  LK-lock sg m os as (LK-t w ∷ acc) (LK-t T₂ ∷ l₁) (hdOf LK-b (LK-cells os))

-- ────────────────────────────────────────────────────────────────────
-- §4e 引擎定理（由 LK-lock 重推：锁步相 = m+2 步，终态携带 (符号, a[v])）
-- ────────────────────────────────────────────────────────────────────

LK-look-sem : ∀ (m : ℕ) (sg : Trit) (o a : Vec Trit (suc m))
            → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
            → C2.st (runB tm-look LK-b (suc (suc m))
                (mk2 [] qLit (LK-t sg) (LK-cells o) [] LK-m (LK-wl (LK-vl a))))
              ≡ qScan (signOf sg) true (lookup a (fromOneHot m o))
LK-look-sem m sg o a h =
  trans (cong C2.st
           (LK-lock (signOf sg) m o a (LK-m ∷ []) (LK-t sg ∷ []) LK-b))
        (trans (LK-scanned-spec (signOf sg) (LK-cells o) (LK-vl a))
               (trans (cong (λ z → qScan (signOf sg) z
                                       (LK-pick (LK-cells o) (LK-vl a)))
                            (LK-anyT₁-cells m o h))
                      (cong (qScan (signOf sg) true) (LK-pick-cells m o a h))))

-- ────────────────────────────────────────────────────────────────────
-- §4f ★ 单文字循环（无复制）：符号步 + 锁步 + 相迁移 + 回走 = 2m+6 步
-- ────────────────────────────────────────────────────────────────────

-- 回走燃料对齐：cs = LK-revT (LK-vl a) 的长度恰为 suc m
LK-rewind-fuel : ∀ (m : ℕ) (a : Vec Trit (suc m))
               → length (LK-revT (LK-vl a)) ≡ suc m
LK-rewind-fuel m a = trans (LK-len-revT (LK-vl a)) (LK-len-cells a)

-- 接缝：锁步终态 ⟹ 回走起点（整幅格局等式）
LK-seam : ∀ (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
        → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
        → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
              (LK-scanned (signOf sg) false T₀ (LK-cells o) (LK-vl a)) LK-b []
              (LK-rw (LK-vl a) (LK-m ∷ [])) LK-b []
          ≡ mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                (qScan (signOf sg) true (lookup a (fromOneHot m o))) LK-b []
                (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []
LK-seam sg m o a l₁ h =
  trans (cong (λ st → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁)) st LK-b []
                             (LK-rw (LK-vl a) (LK-m ∷ [])) LK-b [])
              (trans (LK-scanned-spec (signOf sg) (LK-cells o) (LK-vl a))
                     (trans (cong (λ z → qScan (signOf sg) z
                                      (LK-pick (LK-cells o) (LK-vl a)))
                                  (LK-anyT₁-cells m o h))
                            (cong (qScan (signOf sg) true) (LK-pick-cells m o a h)))))
        (cong (λ l → mk2 (LK-rc (LK-cells o) (LK-t sg ∷ l₁))
                          (qScan (signOf sg) true (lookup a (fromOneHot m o))) LK-b []
                          l LK-b [])
              (LK-rw-wl (LK-vl a) (LK-m ∷ [])))

-- 回走的 m 索引版（燃料写成 suc³ m，避免 length 中性项与「展开后三步」
-- 两种范式在拼接处打架；subst 只在**本条**里做一次）
LK-back-m : ∀ (sg : Sign) (v : Trit) (m : ℕ) (a : Vec Trit (suc m)) (l₁ : List LK-Σ)
          → C2.st (runB tm-look LK-b (suc (suc (suc m)))
              (mk2 l₁ (qBack sg v) LK-b []
                   (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []))
            ≡ qDone sg v
LK-back-m sg v m a l₁ =
  subst (λ k → C2.st (runB tm-look LK-b k
                 (mk2 l₁ (qBack sg v) LK-b []
                      (LK-wl (LK-revT (LK-vl a)) ++ (LK-m ∷ [])) LK-b []))
               ≡ qDone sg v)
        (cong suc (cong suc (LK-rewind-fuel m a)))
        (LK-back sg v (LK-revT (LK-vl a)) [] l₁ LK-b [] [])

-- ★ 主定理：一次文字 = 1（符号）+ (m+1)（锁步）+ 1（相迁移）+ (m+3)（回走）
-- = 2m+6 步；终态携带 (符号, a[v])，带 2 由回走相复原。
LK-cycle : ∀ (sg : Trit) (m : ℕ) (o a : Vec Trit (suc m)) (l₁ : List LK-Σ)
         → Σ (Fin (suc m)) (λ i → lookup o i ≡ T₁)
         → C2.st (runB tm-look LK-b (suc (suc m + suc (suc (suc (suc m)))))
             (mk2 l₁ qLit (LK-t sg) (LK-cells o) [] LK-m (LK-wl (LK-vl a))))
           ≡ qDone (signOf sg) (lookup a (fromOneHot m o))
LK-cycle sg m o a l₁ h =
  trans (cong C2.st
           (trans (runB-+ tm-look LK-b (suc m) (suc (suc (suc (suc m))))
                          (mk2 (LK-t sg ∷ l₁) (qScan (signOf sg) false T₀)
                               (hdOf LK-b (LK-cells o)) (tlOf (LK-cells o))
                               (LK-m ∷ []) (hdOf LK-b (LK-wl (LK-vl a)))
                               (tlOf (LK-wl (LK-vl a)))))
                  (trans (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                               (LK-lock (signOf sg) m o a (LK-m ∷ [])
                                        (LK-t sg ∷ l₁) LK-b))
                         (cong (runB tm-look LK-b (suc (suc (suc (suc m)))))
                               (LK-seam sg m o a l₁ h)))))
        (LK-back-m (signOf sg) (lookup a (fromOneHot m o)) m a
                   (LK-rc (LK-cells o) (LK-t sg ∷ l₁)))

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

-- 回走端到端：左带只有 ⊢ ⟹ 2 步收口
check-back-0 :
  C2.st (runB tm-look LK-b 2 (mk2 [] (qBack σ₊ T₂) LK-b [] (LK-m ∷ []) LK-b []))
  ≡ qDone σ₊ T₂
check-back-0 = refl

-- 回走端到端：左带 = [a₀, ⊢] ⟹ 3 步收口
check-back-1 :
  C2.st (runB tm-look LK-b 3
    (mk2 [] (qBack σ₋ T₁) LK-b [] (LK-t T₀ ∷ LK-m ∷ []) LK-b []))
  ≡ qDone σ₋ T₁
check-back-1 = refl

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
