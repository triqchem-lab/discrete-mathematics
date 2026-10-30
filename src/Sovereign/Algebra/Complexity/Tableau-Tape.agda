{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.Tableau-Tape
-- 带索引层：**相对头偏移**的局部视图 + 一步演化的窗口事实 —— 里程碑 M3b
--
-- 【为什么用相对偏移而不是绝对格号】tableau 的转移子句说的是「头及其左右邻」，
-- 即**相对头**的窗口；绝对格号（`i−1`、`i+1`）会引入 `∸`、边界比较与一串
-- 算术引理。本件把视图定义成 `tH`（头格）/ `tL k`（头左第 k 格）/ `tR k`（头右第 k 格），
-- 于是「新头读旧右侧第 0 格」「写符号落在旧头格」这类事实都是**定义性相等**。
-- 绝对格号的对齐留给 M3c（tableau 的行要对齐同一格，那时才需要编号）。
--
-- 【库内带约定（实测 TuringMachine §2）】`left` = 头**左侧逆序**，`scan` = 头格符号，
-- `right` = 头**右侧**（不含头格）：
--   · 右移：`left′ = w′ ∷ left`、`scan′ = hdOf blk right`、`right′ = tlOf right`；
--   · 左移（左非空）：`left′ = tl left`、`scan′ = hd left`、`right′ = w′ ∷ scan ∷ right`；
--   · 左移（左空）：`left′ = []`、`scan′ = w′`、`right′ = scan ∷ right`。
-- 三条都直接读成 §2 的窗口事实。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.Tableau-Tape where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _+_; s<s⁻¹)
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; m≤n⇒m≤1+n; +-mono-≤)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Automata.TuringMachine
  using (Dir; L; R; TM; TConfig; mkTC; step; stepH; moveH; hdOf; tlOf)
open import Sovereign.Algebra.Complexity.NPClass-TM using (NPT-initCfg)

-- ────────────────────────────────────────────────────────────────────
-- §1 相对偏移视图〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

data TOff : Set where
  tH : TOff            -- 头格
  tL : ℕ → TOff        -- 头左侧第 k 格（k = 0 紧邻头）
  tR : ℕ → TOff        -- 头右侧第 k 格（k = 0 紧邻头）

-- 列表第 i 项（越界给默认值 = 空白）
nth : ∀ {A : Set} → A → List A → ℕ → A
nth d []       i       = d
nth d (x ∷ xs) zero    = x
nth d (x ∷ xs) (suc i) = nth d xs i

-- 局部视图：头格取 `scan`，左/右按偏移取 `left`/`right`
tSym : ∀ {Q A : Set} → A → TConfig Q A → TOff → A
tSym blk c tH      = TConfig.scan c
tSym blk c (tL k)  = nth blk (TConfig.left c) k
tSym blk c (tR k)  = nth blk (TConfig.right c) k

-- `hdOf` 与 `nth … 0` 同值（两者都在列表上分案，故需一条 2 案引理）
hdOf-nth : ∀ {A : Set} (d : A) (xs : List A) → hdOf d xs ≡ nth d xs zero
hdOf-nth d []       = refl
hdOf-nth d (x ∷ xs) = refl

-- 右带「去掉一格」= 偏移前移一位（对 `r` 分案，两案均定义性）
nth-tlOf : ∀ {A : Set} (d : A) (r : List A) (k : ℕ)
         → nth d (tlOf r) k ≡ nth d r (suc k)
nth-tlOf d []       k = refl
nth-tlOf d (x ∷ xs) k = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 一步演化的窗口事实〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 三条（右移 / 左移·左非空 / 左移·左空）：把「新格局的局部视图」逐格对齐到
-- 「旧格局的局部视图」，每个分量都是定义性相等；只有「新头读旧右第 0 格」
-- 需要 `hdOf-nth` 这一步换形。

-- 右移
tstep-R : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
            (l : List A) (s : Q) (a : A) (r : List A)
        → TM.δ M s a ≡ (q′ , w′ , R)
        → TM.halt M s ≡ false
        →   (tSym blk (step M blk (mkTC l s a r)) tH ≡ tSym blk (mkTC l s a r) (tR zero))
          × (tSym blk (step M blk (mkTC l s a r)) (tL zero) ≡ w′)
          × (∀ k → tSym blk (step M blk (mkTC l s a r)) (tL (suc k))
                     ≡ tSym blk (mkTC l s a r) (tL k))
          × (∀ k → tSym blk (step M blk (mkTC l s a r)) (tR k)
                     ≡ tSym blk (mkTC l s a r) (tR (suc k)))
tstep-R blk M q′ w′ l s a r hδ hhalt = P1 , P2 , P3 , P4
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)

  P1 : tSym blk (step M blk (mkTC l s a r)) tH ≡ tSym blk (mkTC l s a r) (tR zero)
  P1 = trans (cong (λ c → tSym blk c tH) stp) (hdOf-nth blk r)

  P2 : tSym blk (step M blk (mkTC l s a r)) (tL zero) ≡ w′
  P2 = cong (λ c → tSym blk c (tL zero)) stp

  P3 : ∀ k → tSym blk (step M blk (mkTC l s a r)) (tL (suc k))
             ≡ tSym blk (mkTC l s a r) (tL k)
  P3 k = cong (λ c → tSym blk c (tL (suc k))) stp

  P4 : ∀ k → tSym blk (step M blk (mkTC l s a r)) (tR k)
             ≡ tSym blk (mkTC l s a r) (tR (suc k))
  P4 k = trans (cong (λ c → tSym blk c (tR k)) stp) (nth-tlOf blk r k)

-- 左移·左空（头已在最左）：新头是写符号，左邻全空白
tstep-L-nil : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                (s : Q) (a : A) (r : List A)
            → TM.δ M s a ≡ (q′ , w′ , L)
            → TM.halt M s ≡ false
            →   (tSym blk (step M blk (mkTC [] s a r)) tH ≡ w′)
              × (∀ k → tSym blk (step M blk (mkTC [] s a r)) (tL k) ≡ blk)
              × (tSym blk (step M blk (mkTC [] s a r)) (tR zero) ≡ tSym blk (mkTC [] s a r) tH)
              × (∀ k → tSym blk (step M blk (mkTC [] s a r)) (tR (suc k))
                         ≡ tSym blk (mkTC [] s a r) (tR k))
tstep-L-nil blk M q′ w′ s a r hδ hhalt = P1 , P2 , P3 , P4
  where
  stp : step M blk (mkTC [] s a r) ≡ mkTC [] q′ w′ (a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC [] s a r)) hhalt)
              (trans (cong (λ d → moveH blk d [] a r) hδ) refl)

  P1 : tSym blk (step M blk (mkTC [] s a r)) tH ≡ w′
  P1 = cong (λ c → tSym blk c tH) stp

  P2 : ∀ k → tSym blk (step M blk (mkTC [] s a r)) (tL k) ≡ blk
  P2 k = cong (λ c → tSym blk c (tL k)) stp

  P3 : tSym blk (step M blk (mkTC [] s a r)) (tR zero)
     ≡ tSym blk (mkTC [] s a r) tH
  P3 = cong (λ c → tSym blk c (tR zero)) stp

  P4 : ∀ k → tSym blk (step M blk (mkTC [] s a r)) (tR (suc k))
             ≡ tSym blk (mkTC [] s a r) (tR k)
  P4 k = cong (λ c → tSym blk c (tR (suc k))) stp

-- 左移·左非空：新头是旧左邻，写符号落在旧头格
tstep-L-cons : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                 (x : A) (xs : List A) (s : Q) (a : A) (r : List A)
             → TM.δ M s a ≡ (q′ , w′ , L)
             → TM.halt M s ≡ false
             →   (tSym blk (step M blk (mkTC (x ∷ xs) s a r)) tH
                    ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL zero))
               × (∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tL k)
                          ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL (suc k)))
               × (tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR zero) ≡ w′)
               × (tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc zero))
                    ≡ tSym blk (mkTC (x ∷ xs) s a r) tH)
               × (∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc (suc k)))
                          ≡ tSym blk (mkTC (x ∷ xs) s a r) (tR k))
tstep-L-cons blk M q′ w′ x xs s a r hδ hhalt = P1 , P2 , P3 , P4 , P5
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)

  P1 : tSym blk (step M blk (mkTC (x ∷ xs) s a r)) tH
     ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL zero)
  P1 = cong (λ c → tSym blk c tH) stp

  P2 : ∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tL k)
             ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL (suc k))
  P2 k = cong (λ c → tSym blk c (tL k)) stp

  P3 : tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR zero) ≡ w′
  P3 = cong (λ c → tSym blk c (tR zero)) stp

  P4 : tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc zero))
     ≡ tSym blk (mkTC (x ∷ xs) s a r) tH
  P4 = cong (λ c → tSym blk c (tR (suc zero))) stp

  P5 : ∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc (suc k)))
             ≡ tSym blk (mkTC (x ∷ xs) s a r) (tR k)
  P5 k = cong (λ c → tSym blk c (tR (suc (suc k)))) stp

-- ────────────────────────────────────────────────────────────────────
-- §3 初值视图〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────
-- `NPT-initCfg M blk inp = mkTC [] (q₀ M) (hdOf blk inp) inp`：
-- 头在第 0 格，右侧就是输入串，左侧全空白。

tinit-tH : ∀ {Q A : Set} (M : TM Q A) (blk : A) (inp : List A)
         → tSym blk (NPT-initCfg M blk inp) tH ≡ hdOf blk inp
tinit-tH M blk inp = refl

tinit-tL : ∀ {Q A : Set} (M : TM Q A) (blk : A) (inp : List A) (k : ℕ)
         → tSym blk (NPT-initCfg M blk inp) (tL k) ≡ blk
tinit-tL M blk inp k = refl

tinit-tR : ∀ {Q A : Set} (M : TM Q A) (blk : A) (inp : List A) (k : ℕ)
         → tSym blk (NPT-initCfg M blk inp) (tR k) ≡ nth blk inp k
tinit-tR M blk inp k = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

Tp-check-nth-0 : nth T₀ (T₁ ∷ (T₂ ∷ [])) zero ≡ T₁
Tp-check-nth-0 = refl

Tp-check-nth-1 : nth T₀ (T₁ ∷ (T₂ ∷ [])) (suc zero) ≡ T₂
Tp-check-nth-1 = refl

-- 越界取空白
Tp-check-nth-out : nth T₀ (T₁ ∷ []) (suc (suc zero)) ≡ T₀
Tp-check-nth-out = refl

Tp-check-tlOf : nth T₀ (tlOf (T₁ ∷ (T₂ ∷ []))) zero ≡ nth T₀ (T₁ ∷ (T₂ ∷ [])) (suc zero)
Tp-check-tlOf = refl

Tp-check-hdOf : hdOf T₀ (T₁ ∷ (T₂ ∷ [])) ≡ nth T₀ (T₁ ∷ (T₂ ∷ [])) zero
Tp-check-hdOf = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   本件只给**相对头**的局部视图与三条一步事实。tableau 的子句要对齐
--       **绝对格号**（时刻 t 与 t+1 的同一格）⟹ 还需要「绝对 = 头位置 + 偏移」
--       的对齐层（含 `left` 逆序的下标换算），属 M3c 的编号工作。
-- (ii)  §2 三条已覆盖「头邻之外的格不动」这一事实（以相对形式：`tL (suc k)` /
--       `tR (suc k)` 精确表达移位），**不另立**绝对形态的「非相邻不变」。
-- (iii) 「赋值 ⟹ 运行存在」的提取（M3c 的硬核）不在本件；本件只提供它要用的
--       一步事实。
-- (iv)  `tstep-*` 以 `halt ≡ false` 为前提：停机态自持由 `stepH` 的 `true` 分支
--       保证（`stepH M b true c = c`），故不在本件重复陈述。

-- 0 postulate / 0 hole。

-- ────────────────────────────────────────────────────────────────────
-- §2b 行对齐原语：偏移平移〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 相对行方案（路线 B）把 tableau 的行按**相对头的偏移**索引，于是「时刻 t 与 t+1 的
-- 同一格」正是**偏移平移**：
--   · 头右移一格 ⟹ 旧 `tR k` 变新 `tR (k−1)`、旧 `tH` 变新 `tL 0`、旧 `tL k` 变新 `tL (k+1)`；
--   · 头左移一格（左非空）⟹ 镜像；
--   · 头左移而左带为空 ⟹ 头**没真动**（`leftLof` 的 `[]` 支原地写入）⟹ 平移是**恒等**。
-- 平移在 `TOff` 上是**全函数、零算术**（只有 `suc` 与「零/后继」两支）。
--
-- 逐点形式把 §2 的四/五个分量收成**一条等式**：除「被写入的旧头格」(`o = tH`) 之外，
-- 每个格子的符号都等于它在新一行对应偏移上的符号。转移子句族（M3c）用的正是这条。

tShiftR : TOff → TOff
tShiftR tH            = tL zero
tShiftR (tL k)        = tL (suc k)
tShiftR (tR zero)     = tH
tShiftR (tR (suc k))  = tR k

tShiftL : TOff → TOff
tShiftL tH            = tR (suc zero)
tShiftL (tL zero)     = tH
tShiftL (tL (suc k))  = tL k
tShiftL (tR k)        = tR (suc (suc k))

-- 右移：`o ≠ tH` 的格子逐点对齐
tstep-R-pt : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
               (l : List A) (s : Q) (a : A) (r : List A)
           → TM.δ M s a ≡ (q′ , w′ , R) → TM.halt M s ≡ false
           → ∀ (o : TOff) → (o ≡ tH → ⊥)
           → tSym blk (step M blk (mkTC l s a r)) (tShiftR o)
             ≡ tSym blk (mkTC l s a r) o
tstep-R-pt blk M q′ w′ l s a r hδ hhalt (tL k) h =
  cong (λ c → tSym blk c (tL (suc k))) stp
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)
tstep-R-pt blk M q′ w′ l s a r hδ hhalt (tR zero) h =
  trans (cong (λ c → tSym blk c tH) stp) (hdOf-nth blk r)
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)
tstep-R-pt blk M q′ w′ l s a r hδ hhalt (tR (suc k)) h =
  trans (cong (λ c → tSym blk c (tR k)) stp) (nth-tlOf blk r k)
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)
tstep-R-pt blk M q′ w′ l s a r hδ hhalt tH h = ⊥-elim (h refl)

-- 左移（左非空）：同一形式，平移换成 `tShiftL`
tstep-L-cons-pt : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                    (x : A) (xs : List A) (s : Q) (a : A) (r : List A)
                → TM.δ M s a ≡ (q′ , w′ , L) → TM.halt M s ≡ false
                → ∀ (o : TOff) → (o ≡ tH → ⊥)
                → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tShiftL o)
                  ≡ tSym blk (mkTC (x ∷ xs) s a r) o
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt (tL zero) h =
  cong (λ c → tSym blk c tH) stp
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt (tL (suc j)) h =
  cong (λ c → tSym blk c (tL j)) stp
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt (tR k) h =
  cong (λ c → tSym blk c (tR (suc (suc k)))) stp
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt tH h = ⊥-elim (h refl)

-- 左移·左空：头进入空白区（真左移一格），旧头格落到新 `tR 0`；被写入的 `w′` 落在
-- **新出现**的格（它没有旧偏移）⟹ 本支**没有例外点**：逐点对齐是**全**的。
tShiftLN : TOff → TOff
tShiftLN tH         = tR zero
tShiftLN (tL k)     = tL k
tShiftLN (tR k)     = tR (suc k)

-- 一步方程（本支专用；右移/左非空两支的方程已内联在 §2 与 §2b）
tstep-L-nil-eq : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                   (s : Q) (a : A) (r : List A)
               → TM.δ M s a ≡ (q′ , w′ , L) → TM.halt M s ≡ false
               → step M blk (mkTC [] s a r) ≡ mkTC [] q′ w′ (a ∷ r)
tstep-L-nil-eq blk M q′ w′ s a r hδ hhalt =
  trans (cong (λ h → stepH M blk h (mkTC [] s a r)) hhalt)
        (trans (cong (λ d → moveH blk d [] a r) hδ) refl)

-- 逐点对齐（全，无 `o ≡ tH` 例外）
tstep-L-nil-pt : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                   (s : Q) (a : A) (r : List A)
               → TM.δ M s a ≡ (q′ , w′ , L) → TM.halt M s ≡ false
               → ∀ (o : TOff)
               → tSym blk (step M blk (mkTC [] s a r)) (tShiftLN o)
                 ≡ tSym blk (mkTC [] s a r) o
tstep-L-nil-pt blk M q′ w′ s a r hδ hhalt tH =
  cong (λ c → tSym blk c (tR zero)) (tstep-L-nil-eq blk M q′ w′ s a r hδ hhalt)
tstep-L-nil-pt blk M q′ w′ s a r hδ hhalt (tL k) =
  cong (λ c → tSym blk c (tL k)) (tstep-L-nil-eq blk M q′ w′ s a r hδ hhalt)
tstep-L-nil-pt blk M q′ w′ s a r hδ hhalt (tR k) =
  cong (λ c → tSym blk c (tR (suc k))) (tstep-L-nil-eq blk M q′ w′ s a r hδ hhalt)

-- ────────────────────────────────────────────────────────────────────
-- §2c 单射性：给逆函数（提取方向本就要它）
-- ────────────────────────────────────────────────────────────────────
-- 提取方向要问「新一行的这个偏移，来自旧一行的哪个偏移」——即 `tShift*` 的**原像**。
-- 与其对 16 格分类证单射，不如把原像写成**全函数**再证往返（4 案全定义性）：
-- 单射性随即是一行推论（`cong` + 两次往返）。

tUnshiftR : TOff → TOff
tUnshiftR (tL zero)     = tH
tUnshiftR (tL (suc k))  = tL k
tUnshiftR tH            = tR zero
tUnshiftR (tR k)        = tR (suc k)

tUnshiftL : TOff → TOff
tUnshiftL (tR (suc zero))     = tH
tUnshiftL (tR (suc (suc k)))  = tR k
tUnshiftL tH                  = tL zero
tUnshiftL (tL k)              = tL (suc k)
tUnshiftL (tR zero)           = tR zero          -- 不在像里（占位，保持全函数）

tUnshiftLN : TOff → TOff
tUnshiftLN (tR zero)     = tH
tUnshiftLN (tR (suc k))  = tR k
tUnshiftLN (tL k)        = tL k
tUnshiftLN tH            = tH                    -- 不在像里（占位）

tUnshiftR-tShiftR : ∀ (o : TOff) → tUnshiftR (tShiftR o) ≡ o
tUnshiftR-tShiftR tH           = refl
tUnshiftR-tShiftR (tL k)       = refl
tUnshiftR-tShiftR (tR zero)    = refl
tUnshiftR-tShiftR (tR (suc k)) = refl

tUnshiftL-tShiftL : ∀ (o : TOff) → tUnshiftL (tShiftL o) ≡ o
tUnshiftL-tShiftL tH           = refl
tUnshiftL-tShiftL (tL zero)    = refl
tUnshiftL-tShiftL (tL (suc k)) = refl
tUnshiftL-tShiftL (tR k)       = refl

tUnshiftLN-tShiftLN : ∀ (o : TOff) → tUnshiftLN (tShiftLN o) ≡ o
tUnshiftLN-tShiftLN tH         = refl
tUnshiftLN-tShiftLN (tL k)     = refl
tUnshiftLN-tShiftLN (tR k)     = refl

-- 单射性（提取方向：新偏移唯一确定旧偏移）
tShiftR-inj : ∀ {o o′ : TOff} → tShiftR o ≡ tShiftR o′ → o ≡ o′
tShiftR-inj {o} {o′} p =
  trans (sym (tUnshiftR-tShiftR o))
        (trans (cong tUnshiftR p) (tUnshiftR-tShiftR o′))

tShiftL-inj : ∀ {o o′ : TOff} → tShiftL o ≡ tShiftL o′ → o ≡ o′
tShiftL-inj {o} {o′} p =
  trans (sym (tUnshiftL-tShiftL o))
        (trans (cong tUnshiftL p) (tUnshiftL-tShiftL o′))

tShiftLN-inj : ∀ {o o′ : TOff} → tShiftLN o ≡ tShiftLN o′ → o ≡ o′
tShiftLN-inj {o} {o′} p =
  trans (sym (tUnshiftLN-tShiftLN o))
        (trans (cong tUnshiftLN p) (tUnshiftLN-tShiftLN o′))

-- ────────────────────────────────────────────────────────────────────
-- §2d 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

Tp-check-shiftR : tShiftR (tH) ≡ tL zero
Tp-check-shiftR = refl

Tp-check-unshiftR : tUnshiftR (tL zero) ≡ tH
Tp-check-unshiftR = refl

Tp-check-shiftL-two : tShiftL (tR zero) ≡ tR (suc (suc zero))
Tp-check-shiftL-two = refl

Tp-check-shiftLN : tShiftLN (tR zero) ≡ tR (suc zero)
Tp-check-shiftLN = refl

Tp-check-roundtrip : tUnshiftL (tShiftL (tL (suc zero))) ≡ tL (suc zero)
Tp-check-roundtrip = refl

-- ────────────────────────────────────────────────────────────────────
-- §3 偏移编号层〔结构定义〕（闸门 G1；路线 B 的最后一处算术）
-- ────────────────────────────────────────────────────────────────────
-- 【A0 设计冻结（(b) 按时间参数化的双侧界）】
--   · 第 t 行覆盖的偏移区间是 **[−t, len−1+2t]**（左界 = 已右漂步数上限 t；
--     右界 = 输入 len−1 + **左漂贡献 2t**）——**不对称**，且右界系数是 **2**：
--     `leftLof` 的 `x ∷ xs` 支令 `right′ = w′ ∷ a ∷ right`（写符号 + 旧头符号
--     两格推入右带）⟹ 每左移一步右侧相对偏移 **+2**（M3b 的
--     `tShiftL (tR k) = tR (suc (suc k))`）。
--     帧宽参数取 `L = len + 2*T + 2`。⚠ 漏掉系数 2 会在 A8 的 `tShiftL` 支撞墙
--     （`suc (suc k) ≤ len + (t+1)` 不成立）——本行是查证后修正，不是初稿。
--     ⚠ 错的写法是对称居中 `2T+3`：它只在「输入很短、T 很大」时碰巧够用。
--   · 编码 = 三元 tag（`tH` / `tL` / `tR`）× 有界索引；tag 用 `Fin 3`、索引用 `Fin L`。
--   · `tShiftR (tL k) = tL (suc k)`、`tShiftL (tR k) = tR (suc (suc k))` 使索引**增长**
--     ⟹ 「平移保持界内」（A8）必须带显式不等式前提，固定界下对边界格不成立。

-- A1：偏移的三元 tag
offTag : TOff → Fin 3
offTag tH       = fzero
offTag (tL k)   = fsuc fzero
offTag (tR k)   = fsuc (fsuc fzero)

-- A2：偏移的有界索引（`tH` 用占位 0；`tL`/`tR` 取距头的格数）
offIdx : TOff → ℕ
offIdx tH       = zero
offIdx (tL k)   = k
offIdx (tR k)   = k

-- ────────────────────────────────────────────────────────────────────
-- §3b 编号层核对〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

Tp-check-offTag-tH : offTag tH ≡ fzero
Tp-check-offTag-tH = refl

Tp-check-offTag-tL : offTag (tL (suc zero)) ≡ fsuc fzero
Tp-check-offTag-tL = refl

Tp-check-offTag-tR : offTag (tR zero) ≡ fsuc (fsuc fzero)
Tp-check-offTag-tR = refl

Tp-check-offIdx-tL : offIdx (tL (suc (suc zero))) ≡ suc (suc zero)
Tp-check-offIdx-tL = refl

Tp-check-offIdx-tH : offIdx tH ≡ zero
Tp-check-offIdx-tH = refl

-- ────────────────────────────────────────────────────────────────────
-- §3c 界内谓词（A3）与它的算术备件（A4a）
-- ────────────────────────────────────────────────────────────────────
-- 第 t 行的偏移界（**双侧、不对称**，见 §3 头注）：
--   左侧 `tL k` —— 头左第 k 格，最多右漂 t 步 ⟹ `k ≤ t`；
--   右侧 `tR k` —— 头右第 k 格，输入 len−1 + 左漂贡献 2t ⟹ `k ≤ len + t + t`。
-- 帧宽 `L = suc (suc (len + T + T))`——**必须写成 `suc` 形**：`_+_` 递归在首参，
-- `len + T + T + 2` 的首参 stuck ⟹ 不归约成 `suc (suc …)`（`suc` 形才可转换）。
InOff : (len t : ℕ) → TOff → Set
InOff len t tH      = ⊤
InOff len t (tL k)  = k ≤ t
InOff len t (tR k)  = k ≤ len + t + t

-- A4a-1：`n < suc n`（即 `suc n ≤ suc n`，一个 `≤-refl`）
off-lt-suc : ∀ (n : ℕ) → n < suc n
off-lt-suc n = ≤-refl

-- A4a-2：上界可以加余量
off-le-add : ∀ {a b c : ℕ} → a ≤ b → a ≤ b + c
off-le-add {a} {b} {c} h = ≤-trans h (m≤m+n b c)

-- A4a-3：`a ≤ b ⟹ a ≤ suc b`（不引入 `_+_`，避开首参递归的 stuck）
off-le-suc : ∀ {a b : ℕ} → a ≤ b → a ≤ suc b
off-le-suc h = m≤n⇒m≤1+n h

-- A4a-4：时间上界落在帧宽内（`T < suc (suc (len + T + T))`）
--   链：T ≤ len+T（m≤n+m）→ ≤ (len+T)+T → ≤ suc((len+T)+T) → 再 suc 成严格
off-T-lt-L : ∀ (len T : ℕ) → T < suc (suc (len + T + T))
off-T-lt-L len T =
  s≤s (≤-trans (≤-trans (m≤n+m T len)
                        (off-le-add {a = len + T} {b = len + T} {c = T} ≤-refl))
               (off-le-suc ≤-refl))

-- ────────────────────────────────────────────────────────────────────
-- §3d A3/A4a 核对〔refl 枚举 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

Tp-check-InOff-tH : InOff 3 1 tH
Tp-check-InOff-tH = tt

Tp-check-InOff-tL : InOff 3 1 (tL (suc zero))
Tp-check-InOff-tL = s≤s z≤n

Tp-check-InOff-tR : InOff 3 1 (tR (suc (suc zero)))
Tp-check-InOff-tR = s≤s (s≤s z≤n)

Tp-check-off-lt-suc : 4 < suc 4
Tp-check-off-lt-suc = off-lt-suc 4

Tp-check-off-T-lt-L : 2 < suc (suc (3 + 2 + 2))
Tp-check-off-T-lt-L = off-T-lt-L 3 2

-- ────────────────────────────────────────────────────────────────────
-- §3e 编号（A4b）：`InOff` → `Fin 3 × Fin (off-L len T)`
-- ────────────────────────────────────────────────────────────────────
-- 设计点（已裁决）：`t ≤ T` **不进** `InOff`——前者是「该行在时域内」，后者是
-- 「该行的偏移界」，两件事分开，由调用方显式给出。

off-L : (len T : ℕ) → ℕ
off-L len T = suc (suc (len + T + T))

-- tL 支：k ≤ t ≤ T < L ⟹ k < L
off-tL-lt-L : ∀ (len T t k : ℕ) → k ≤ t → t ≤ T → k < off-L len T
off-tL-lt-L len T t k h hT = ≤-trans (s≤s (≤-trans h hT)) (off-T-lt-L len T)

-- tR 支：k ≤ len+t+t ≤ len+T+T < L ⟹ k < L
off-tR-lt-L : ∀ (len T t k : ℕ) → k ≤ len + t + t → t ≤ T → k < off-L len T
off-tR-lt-L len T t k h hT = s≤s (off-le-suc (≤-trans h mono))
  where
  mono : len + t + t ≤ len + T + T
  mono = +-mono-≤ (+-mono-≤ ≤-refl hT) hT

offEnc : ∀ (len T t : ℕ) (o : TOff) → InOff len t o → t ≤ T → Fin 3 × Fin (off-L len T)
offEnc len T t tH     h hT = fzero , fzero
offEnc len T t (tL k) h hT = fsuc fzero , fromℕ< (off-tL-lt-L len T t k h hT)
offEnc len T t (tR k) h hT = fsuc (fsuc fzero) , fromℕ< (off-tR-lt-L len T t k h hT)

Tp-check-offEnc-tH : offEnc 3 2 1 tH tt (s≤s z≤n) ≡ (fzero , fzero)
Tp-check-offEnc-tH = refl

-- ────────────────────────────────────────────────────────────────────
-- §3f 解码（A5）：`Fin 3 × Fin (off-L len T)` → `TOff`
-- ────────────────────────────────────────────────────────────────────
-- 与 `offEnc` 互为反：tag 0 ↦ `tH`（索引忽略）、tag 1 ↦ `tL (toℕ k)`、
-- tag 2 ↦ `tR (toℕ k)`。全函数（不检查界内——界内是 `InOff` 的事）。

offDec : ∀ (len T : ℕ) → Fin 3 × Fin (off-L len T) → TOff
offDec len T (fzero , _)           = tH
offDec len T (fsuc fzero , k)      = tL (toℕ k)
offDec len T (fsuc (fsuc _) , k)   = tR (toℕ k)

Tp-check-offDec-tH : offDec 3 2 (fzero , fzero) ≡ tH
Tp-check-offDec-tH = refl

Tp-check-offDec-roundtrip-tH : offDec 3 2 (offEnc 3 2 1 tH tt (s≤s z≤n)) ≡ tH
Tp-check-offDec-roundtrip-tH = refl

-- ────────────────────────────────────────────────────────────────────
-- §3g A6：`offDec ∘ offEnc = id`（在界内）
-- ────────────────────────────────────────────────────────────────────
-- 先探明 `fromℕ<` 的定义（Data/Fin/Base:81-83）：
--   fromℕ< : .(m < n) → Fin n                 -- 界证明 **irrelevant**（`.` 前缀）
--   fromℕ< {zero}  {suc _} _   = zero
--   fromℕ< {suc m} {suc _} m<n = suc (fromℕ< (s<s⁻¹ m<n))
-- ⟹ 对 `suc` 形参数**透明** ⟹ 直接对 k 归纳自证取值引理。
-- ⚠ 两处踩坑：(1) 模式变量不能叫 `L`——`L` 是 `Dir` 的构造子（TuringMachine 导入），
--   会报 "L is not a constructor of the datatype ℕ"；(2) 界内性证明必须显式给出
--   （`_` 推不出来），直接用 `off-tL-lt-L` / `off-tR-lt-L` 这两个已证的项。

off-toℕ-fromℕ< : ∀ (k : ℕ) {n : ℕ} (h : k < n) → toℕ (fromℕ< h) ≡ k
off-toℕ-fromℕ< zero    {zero}  ()
off-toℕ-fromℕ< zero    {suc n} h = refl
off-toℕ-fromℕ< (suc k) {zero}  ()
off-toℕ-fromℕ< (suc k) {suc n} h = cong suc (off-toℕ-fromℕ< k (s<s⁻¹ h))

-- ★ A6 主引理：编码-解码在界内互逆（tH 支 refl；tL/tR 支取值引理 + cong）
offDec-enc : ∀ (len T t : ℕ) (o : TOff) (h : InOff len t o) (hT : t ≤ T)
           → offDec len T (offEnc len T t o h hT) ≡ o
offDec-enc len T t tH     h hT = refl
offDec-enc len T t (tL k) h hT =
  cong tL (off-toℕ-fromℕ< k {n = off-L len T} (off-tL-lt-L len T t k h hT))
offDec-enc len T t (tR k) h hT =
  cong tR (off-toℕ-fromℕ< k {n = off-L len T} (off-tR-lt-L len T t k h hT))

-- ────────────────────────────────────────────────────────────────────
-- §3h A7：编码**单射**（同 `len`/`T`/`t`，界内性证明各带各的）
-- ────────────────────────────────────────────────────────────────────
-- 消费者：池层要把 `(时刻, 偏移, 符号)` 压成一个 `Fin`，若两个不同偏移编到同一格，
-- 池里就会撞变量。单射由 A6 一行导出：两边各自解回原偏移，中间用 `cong offDec` 过桥。
offEnc-inj : ∀ (len T t : ℕ) (o o′ : TOff)
               (h : InOff len t o) (h′ : InOff len t o′)
               (hT : t ≤ T)
           → offEnc len T t o h hT ≡ offEnc len T t o′ h′ hT → o ≡ o′
offEnc-inj len T t o o′ h h′ hT p =
  trans (sym (offDec-enc len T t o h hT))
        (trans (cong (offDec len T) p) (offDec-enc len T t o′ h′ hT))
