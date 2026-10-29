{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATMBridge
-- 验证器 → TM 实现桥（SATFam 立界 (iv) 闭合；TMBridge 家族第三件）
--
-- 【边界声明（头注，必须先读）】本件闭合**SAT 验证器的 TM 实现桥**（固定池 m
-- 与族池 m = w(n) 两形），不是「任意 Counted 验证器可实现为 TM」的通用桥
-- ——后者维持 PClass §6(i) / NPClass §5(iii) / TMBridge §5(i) 立界，本件不冒充。
--
-- 桥的三层（与 TMBridge/TMBridge2 同范式，但首次覆盖**折叠控制结构**）：
--   ① 编码层 SVM-cellOf：把（解码后的）文字与其见证值合成**一个带单元**
--      （配对单元；Σ = Sign × Trit 六符 + 终止符 = 七符）。
--   ② 机器层 tm-sat：单向扫描 + 相位（qP0/qP1/qP2 三格一轮 = 一子句）
--      + 两级累计标志（子句内 OR、子句间 AND）——satClause/satFormula 的
--      控制结构逐字落地。
--   ③ 记账层：每单元恰 1 步（= satLitC 的账目 1），一子句 3 步
--      （= satClauseC 的账目 3），终止符 1 步 ⟹
--      **燃料 = 函数层账目 + 1**（SVM-account，精确等式非上界）。
--
-- 主定理（SVM-bridge，双向）：
--   value (satFormulaC a φ) ≡ true ⇔ tm-sat 于带 SVM-cells a φ 上
--   恰 SVM-fuel c 步停于 qAcc。
-- 验证器/族实例：φ := decFormula m n x（SVM-verifier-bridge），
-- m := SF-wlog3 n（SVM-fam-bridge，池随 n 生成承 SATFam §6）。
--
-- 【诚实边界（尾注 §6）】
--   (i)   配对 SVM-cellOf 是**输入编码**，不计机内步数：它含一次数组读取
--         a[v]（onehot 解码 + 移头 O(m)）。故本件闭合的是**控制结构**的
--         逐字实现，不是「含寻址的整机 1 步/文字」。
--   (ii)  自含格式（m 内嵌串首）与见证读取的机内实现 = multi-tape / 自含头
--         新基建，未做（承 SATMember §7(i)）。
--   (iii) 泛型 runN 步进引理（TMBridge §2.1 立界）本件**不需要**：run 定理
--         的每一步都落在具体态上（相位/标志由构造子复合，halt 恒可算），
--         归约是转换级而非重写级。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATMBridge where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Bool.Properties using (∨-assoc; ∨-identityˡ; ∧-assoc; ∧-identityʳ)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (*-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup) renaming ([] to vNil; _∷_ to _v∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Automata.TuringMachine
  using (TM; TConfig; mkTC; runN; Dir; R; hdOf; tlOf)
open import Sovereign.Algebra.Complexity.TimeBound using (value; steps)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; Lit; Clause; Formula; Asg; isT₁; evalLit;
         satClause; satFormula; satFormulaC; value-satFormulaC;
         clauseW; decFormula; sat-verifier)
open import Sovereign.Algebra.Complexity.SATFam using (SF-wlog3)

-- ────────────────────────────────────────────────────────────────────
-- §1 编码层：配对单元（符号 × 见证值）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 配对单元：一个文字在带上占一格（符号 + 该变元的见证值）
SVM-Cell : Set
SVM-Cell = Sign × Trit

-- 带字母表：配对单元 + 终止符（终止符使单向扫描能判带尾——TMBridge2 同法）
data SVM-Σ : Set where
  SVM-c   : SVM-Cell → SVM-Σ
  SVM-end : SVM-Σ

-- 空白裁定：读作假文字（与 safeLook 越界取 T₀ 同规范）
SVM-blank : SVM-Σ
SVM-blank = SVM-c (σ₋ , T₀)

-- 文字判据：σ₊ 取原值、σ₋ 取反（与 evalLit 同语义）
SVM-litOk : SVM-Cell → Bool
SVM-litOk (σ₊ , v) = isT₁ v
SVM-litOk (σ₋ , v) = isT₁ (negate v)

-- 配对：解码后的文字 (sign, var) 与其见证值 lookup a var 合成一格
SVM-cellOf : ∀ {m} (a : Asg m) (l : Lit m) → SVM-Cell
SVM-cellOf a l = proj₁ l , lookup a (proj₂ l)

-- 判据一致：机器读配对单元 = 函数层读 (文字, 赋值)（两案 refl）
SVM-litOk-cellOf : ∀ {m} (a : Asg m) (l : Lit m)
  → SVM-litOk (SVM-cellOf a l) ≡ isT₁ (evalLit a l)
SVM-litOk-cellOf a (σ₊ , v) = refl
SVM-litOk-cellOf a (σ₋ , v) = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 机器层：相位 3 格一轮（= 一子句）+ 两级累计标志〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- qP0/qP1/qP2 = 待读第 1/2/3 文字；(子句内 OR 累计, 子句间 AND 累计)
data SVM-Q : Set where
  qP0 qP1 qP2 : Bool → Bool → SVM-Q
  qAcc qRej   : SVM-Q

SVM-halt : SVM-Q → Bool
SVM-halt (qP0 _ _) = false
SVM-halt (qP1 _ _) = false
SVM-halt (qP2 _ _) = false
SVM-halt qAcc = true
SVM-halt qRej = true

-- δ 表：单元一格 1 步（读判据 → OR 进子句）；第 3 格收子句（AND 进公式）；
-- 终止符收公式（真→qAcc / 假→qRej）。停机态自持，写出原符号右移。
SVM-δ : SVM-Q → SVM-Σ → SVM-Q × SVM-Σ × Dir
SVM-δ (qP0 ck fk) (SVM-c cell) = qP1 (ck ∨ SVM-litOk cell) fk , SVM-c cell , R
SVM-δ (qP1 ck fk) (SVM-c cell) = qP2 (ck ∨ SVM-litOk cell) fk , SVM-c cell , R
SVM-δ (qP2 ck fk) (SVM-c cell) =
  qP0 false (fk ∧ (ck ∨ SVM-litOk cell)) , SVM-c cell , R
SVM-δ (qP0 _ fk) SVM-end = (if fk then qAcc else qRej) , SVM-end , R
SVM-δ (qP1 _ _) SVM-end = qRej , SVM-end , R   -- 不可达：整块 tape 才进带尾
SVM-δ (qP2 _ _) SVM-end = qRej , SVM-end , R   -- 同上（§6(iv) 立界注记）
SVM-δ qAcc s = qAcc , s , R
SVM-δ qRej s = qRej , s , R

tm-sat : TM SVM-Q SVM-Σ
tm-sat = record { δ = SVM-δ ; q₀ = qP0 false true ; halt = SVM-halt }

-- ────────────────────────────────────────────────────────────────────
-- §3 带编码与燃料〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 反序累积（左带的规范形：每步 w' ∷ l）
SVM-rev : List SVM-Σ → List SVM-Σ → List SVM-Σ
SVM-rev []       acc = acc
SVM-rev (x ∷ xs) acc = SVM-rev xs (x ∷ acc)

-- 公式 → 带：每子句 3 格（一文字一格），带尾终止符
SVM-cells : ∀ {m c} (a : Asg m) → Formula m c → List SVM-Σ
SVM-cells a vNil = SVM-end ∷ []
SVM-cells a ((l₁ , l₂ , l₃) v∷ φ) =
  SVM-c (SVM-cellOf a l₁) ∷ SVM-c (SVM-cellOf a l₂) ∷
  SVM-c (SVM-cellOf a l₃) ∷ SVM-cells a φ

-- 空公式的带 = 仅终止符；带首即终止符
SVM-cells-nil : ∀ {m} (a : Asg m) → SVM-cells {c = zero} a vNil ≡ SVM-end ∷ []
SVM-cells-nil a = refl

SVM-head-nil : ∀ {m} (a : Asg m)
  → hdOf SVM-blank (SVM-cells {c = zero} a vNil) ≡ SVM-end
SVM-head-nil a = refl

-- 燃料：每子句 3 步 + 终止符 1 步
SVM-fuel : ℕ → ℕ
SVM-fuel zero    = 1
SVM-fuel (suc c) = suc (suc (suc (SVM-fuel c)))

-- 闭式：fuel c = 3c + 1（3 * suc c ≡ 3 + 3c 由 *-suc 反向给出）
SVM-fuel-eq : ∀ c → SVM-fuel c ≡ suc (3 * c)
SVM-fuel-eq zero = refl
SVM-fuel-eq (suc c) =
  trans (cong suc (cong suc (cong suc (SVM-fuel-eq c))))
        (cong suc (sym (*-suc 3 c)))

-- 机器态内的"噪声形"子句判据（左结合 OR 累计的规范形）
SVM-clauseOk : ∀ {m} (a : Asg m) (cl : Clause m) → Bool
SVM-clauseOk a (l₁ , l₂ , l₃) =
  ((false ∨ SVM-litOk (SVM-cellOf a l₁)) ∨ SVM-litOk (SVM-cellOf a l₂))
    ∨ SVM-litOk (SVM-cellOf a l₃)

-- 噪声形 ≡ satClause：false-∨ 消去 → OR 结合 → 三处 litOk 换 isT₁∘evalLit
SVM-clauseOk-eq : ∀ {m} (a : Asg m) (cl : Clause m)
  → SVM-clauseOk a cl ≡ satClause a cl
SVM-clauseOk-eq a (l₁ , l₂ , l₃) =
  trans (cong (λ x → (x ∨ SVM-litOk (SVM-cellOf a l₂))
                        ∨ SVM-litOk (SVM-cellOf a l₃))
              (∨-identityˡ (SVM-litOk (SVM-cellOf a l₁))))
        (trans (∨-assoc (SVM-litOk (SVM-cellOf a l₁))
                        (SVM-litOk (SVM-cellOf a l₂))
                        (SVM-litOk (SVM-cellOf a l₃)))
               (cong₂ _∨_
                 (SVM-litOk-cellOf a l₁)
                 (cong₂ _∨_ (SVM-litOk-cellOf a l₂) (SVM-litOk-cellOf a l₃))))

-- 累计标志收口：把"噪声形子句 ∧ 余公式"换回 satClause（+ AND 结合）
-- （对整幅格局成立——左/扫描/右带作参数，避免 cong 的函数位置推断歧义）
SVM-state-cong : ∀ {m} (a : Asg m) (cl : Clause m) (fk s : Bool)
  (l : List SVM-Σ) (sc : SVM-Σ) (r : List SVM-Σ)
  → mkTC l (if (fk ∧ SVM-clauseOk a cl) ∧ s then qAcc else qRej) sc r
  ≡ mkTC l (if fk ∧ (satClause a cl ∧ s) then qAcc else qRej) sc r
SVM-state-cong a cl fk s l sc r =
  cong (λ b → mkTC l (if b then qAcc else qRej) sc r)
       (trans (cong (λ x → (fk ∧ x) ∧ s) (SVM-clauseOk-eq a cl))
              (∧-assoc fk (satClause a cl) s))

-- ────────────────────────────────────────────────────────────────────
-- §4 ★ 主 run 定理：整条带的运行 = 子句 OR/公式 AND 的折叠〔结构归纳〕
-- ────────────────────────────────────────────────────────────────────
-- 运行面：每步都落在具体态上（相位/标志由构造子复合，halt 恒可算），
-- 故 runN 是转换级归约——不需要 TMBridge §2.1 所立界的泛型步进引理。
-- 带约定承 TMBridge2：初始 scan = 首格，右带 = **扫描格之后的余带**（tlOf）。

SVM-run : ∀ {m c} (a : Asg m) (φ : Formula m c) (fk : Bool)
          (ls : List SVM-Σ)
        → runN tm-sat SVM-blank (SVM-fuel c)
            (mkTC ls (qP0 false fk) (hdOf SVM-blank (SVM-cells a φ))
                    (tlOf (SVM-cells a φ)))
          ≡ mkTC (SVM-rev (SVM-cells a φ) ls)
                 (if fk ∧ satFormula a φ then qAcc else qRej) SVM-blank []
SVM-run a vNil fk ls =
  trans (SVM-base-step fk ls)
        (cong (λ b → mkTC (SVM-end ∷ ls) (if b then qAcc else qRej) SVM-blank [])
              (sym (∧-identityʳ fk)))
  where
  SVM-base-step : ∀ (fk′ : Bool) (ls′ : List SVM-Σ)
    → runN tm-sat SVM-blank 1 (mkTC ls′ (qP0 false fk′) SVM-end [])
      ≡ mkTC (SVM-end ∷ ls′) (if fk′ then qAcc else qRej) SVM-blank []
  SVM-base-step fk′ ls′ = refl
SVM-run a ((l₁ , l₂ , l₃) v∷ φ) fk ls =
  trans (SVM-run a φ (fk ∧ SVM-clauseOk a (l₁ , l₂ , l₃))
                 (SVM-c (SVM-cellOf a l₃) ∷ SVM-c (SVM-cellOf a l₂) ∷
                  SVM-c (SVM-cellOf a l₁) ∷ ls))
        (SVM-state-cong a (l₁ , l₂ , l₃) fk (satFormula a φ)
                        (SVM-rev (SVM-cells a ((l₁ , l₂ , l₃) v∷ φ)) ls)
                        SVM-blank [])

-- ────────────────────────────────────────────────────────────────────
-- §5 桥定理：验证器 / 族验证器 的 TM 实现〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 停机态 = "公式真则 qAcc 否则 qRej"（进入标志 fk = true）
SVM-halt-state : ∀ {m c} (a : Asg m) (φ : Formula m c) (ls : List SVM-Σ)
  → TConfig.st (runN tm-sat SVM-blank (SVM-fuel c)
      (mkTC ls (qP0 false true) (hdOf SVM-blank (SVM-cells a φ))
              (tlOf (SVM-cells a φ))))
    ≡ (if satFormula a φ then qAcc else qRej)
SVM-halt-state a φ ls = cong TConfig.st (SVM-run a φ true ls)

-- 停机态判别：qAcc ⟺ 标志为真
SVM-halt-acc : ∀ b → (if b then qAcc else qRej) ≡ qAcc → b ≡ true
SVM-halt-acc true  h = refl
SVM-halt-acc false ()

-- → 方向：计账求值接受 ⟹ 机器停于 qAcc
SVM-bridge→ : ∀ {m c} (a : Asg m) (φ : Formula m c)
  → value (satFormulaC a φ) ≡ true
  → TConfig.st (runN tm-sat SVM-blank (SVM-fuel c)
      (mkTC [] (qP0 false true) (hdOf SVM-blank (SVM-cells a φ))
              (tlOf (SVM-cells a φ)))) ≡ qAcc
SVM-bridge→ a φ h =
  trans (SVM-halt-state a φ [])
        (cong (λ b → if b then qAcc else qRej)
              (trans (sym (value-satFormulaC a φ)) h))

-- ← 方向：机器停于 qAcc ⟹ 计账求值接受
SVM-bridge← : ∀ {m c} (a : Asg m) (φ : Formula m c)
  → TConfig.st (runN tm-sat SVM-blank (SVM-fuel c)
      (mkTC [] (qP0 false true) (hdOf SVM-blank (SVM-cells a φ))
              (tlOf (SVM-cells a φ)))) ≡ qAcc
  → value (satFormulaC a φ) ≡ true
SVM-bridge← a φ h =
  trans (value-satFormulaC a φ)
        (SVM-halt-acc (satFormula a φ) (trans (sym (SVM-halt-state a φ [])) h))

-- 双向桥（公式层）
SVM-bridge : ∀ {m c} (a : Asg m) (φ : Formula m c)
  → (value (satFormulaC a φ) ≡ true
      → TConfig.st (runN tm-sat SVM-blank (SVM-fuel c)
          (mkTC [] (qP0 false true) (hdOf SVM-blank (SVM-cells a φ))
                  (tlOf (SVM-cells a φ)))) ≡ qAcc)
  × (TConfig.st (runN tm-sat SVM-blank (SVM-fuel c)
          (mkTC [] (qP0 false true) (hdOf SVM-blank (SVM-cells a φ))
                  (tlOf (SVM-cells a φ)))) ≡ qAcc
      → value (satFormulaC a φ) ≡ true)
SVM-bridge a φ = SVM-bridge→ a φ , SVM-bridge← a φ

-- 验证器层：φ := decFormula m n x（带 = 解码公式的三格展开）
SVM-verifier-bridge : ∀ (m n : ℕ) (x : Vec Trit n) (a : Asg m)
  → (value (sat-verifier m n x a) ≡ true
      → TConfig.st (runN tm-sat SVM-blank (SVM-fuel (n / clauseW m))
          (mkTC [] (qP0 false true)
                (hdOf SVM-blank (SVM-cells a (decFormula m n x)))
                (tlOf (SVM-cells a (decFormula m n x))))) ≡ qAcc)
  × (TConfig.st (runN tm-sat SVM-blank (SVM-fuel (n / clauseW m))
          (mkTC [] (qP0 false true)
                (hdOf SVM-blank (SVM-cells a (decFormula m n x)))
                (tlOf (SVM-cells a (decFormula m n x))))) ≡ qAcc
      → value (sat-verifier m n x a) ≡ true)
SVM-verifier-bridge m n x a = SVM-bridge a (decFormula m n x)

-- 族实例：池 = SF-wlog3 n（随 n 增长；族一致性见 SATFam §6）
SVM-fam-bridge : ∀ (n : ℕ) (x : Vec Trit n) (a : Asg (SF-wlog3 n))
  → (value (sat-verifier (SF-wlog3 n) n x a) ≡ true
      → TConfig.st (runN tm-sat SVM-blank
          (SVM-fuel (n / clauseW (SF-wlog3 n)))
          (mkTC [] (qP0 false true)
                (hdOf SVM-blank (SVM-cells a (decFormula (SF-wlog3 n) n x)))
                (tlOf (SVM-cells a (decFormula (SF-wlog3 n) n x))))) ≡ qAcc)
  × (TConfig.st (runN tm-sat SVM-blank
          (SVM-fuel (n / clauseW (SF-wlog3 n)))
          (mkTC [] (qP0 false true)
                (hdOf SVM-blank (SVM-cells a (decFormula (SF-wlog3 n) n x)))
                (tlOf (SVM-cells a (decFormula (SF-wlog3 n) n x))))) ≡ qAcc
      → value (sat-verifier (SF-wlog3 n) n x a) ≡ true)
SVM-fam-bridge n x a = SVM-verifier-bridge (SF-wlog3 n) n x a

-- 记账对齐：机器燃料 = 函数层账目 + 1（精确等式，1 = 终止符收口步）
SVM-account : ∀ (m n : ℕ) (x : Vec Trit n) (a : Asg m)
  → SVM-fuel (n / clauseW m) ≡ suc (steps (sat-verifier m n x a))
SVM-account m n x a = SVM-fuel-eq (n / clauseW m)

-- 逐文字步数：机器一格 = satLitC 的 1 步账目（值面按 §1 判据桥）
SVM-lit-steps : ∀ {m} (a : Asg m) (l : Lit m)
  → SVM-litOk (SVM-cellOf a l) ≡ isT₁ (evalLit a l)
SVM-lit-steps a l = SVM-litOk-cellOf a l

-- ────────────────────────────────────────────────────────────────────
-- §6 核对层（refl 枚举）与尾注立界
-- ────────────────────────────────────────────────────────────────────

-- 判据表：σ₊ 取原值、σ₋ 取反
SVM-check-ok1 : SVM-litOk (σ₊ , T₁) ≡ true
SVM-check-ok1 = refl

SVM-check-ok2 : SVM-litOk (σ₊ , T₀) ≡ false
SVM-check-ok2 = refl

SVM-check-ok3 : SVM-litOk (σ₋ , T₂) ≡ true
SVM-check-ok3 = refl

SVM-check-ok4 : SVM-litOk (σ₋ , T₁) ≡ false
SVM-check-ok4 = refl

-- 配对：a = (T₁ ∷ [])、文字 (σ₊, 0 号) → (σ₊ , T₁)
SVM-check-cell : SVM-cellOf (T₁ v∷ vNil) (σ₊ , fzero) ≡ (σ₊ , T₁)
SVM-check-cell = refl

-- 燃料闭式小值：fuel 0 = 1、fuel 2 = 7
SVM-check-fuel-0 : SVM-fuel 0 ≡ 1
SVM-check-fuel-0 = refl

SVM-check-fuel-2 : SVM-fuel 2 ≡ 7
SVM-check-fuel-2 = refl

-- 端到端接受：一子句 [(σ₊,1),(σ₋,0),(σ₊,0)] + 终止符，4 步停 qAcc
-- （步 1: OR 得 true；步 2: negate T₀ = T₂ 不真，仍 true；步 3: AND 收子句真；
--  步 4: 终止符 → qAcc）
SVM-check-run-acc :
  TConfig.st (runN tm-sat SVM-blank 4
    (mkTC [] (qP0 false true) (SVM-c (σ₊ , T₁))
      (SVM-c (σ₋ , T₀) ∷ SVM-c (σ₊ , T₀) ∷ SVM-end ∷ [])))
  ≡ qAcc
SVM-check-run-acc = refl

-- 端到端拒绝：三文字皆假 → 子句假 → 公式假 → qRej
SVM-check-run-rej :
  TConfig.st (runN tm-sat SVM-blank 4
    (mkTC [] (qP0 false true) (SVM-c (σ₊ , T₀))
      (SVM-c (σ₊ , T₀) ∷ SVM-c (σ₊ , T₀) ∷ SVM-end ∷ [])))
  ≡ qRej
SVM-check-run-rej = refl

-- 终止符提前到达（半截子句）：qP1/qP2 支给 qRej（保守拒绝，§6(iv) 立界）
SVM-check-run-half :
  TConfig.st (runN tm-sat SVM-blank 2
    (mkTC [] (qP0 false true) (SVM-c (σ₊ , T₁))
      (SVM-end ∷ [])))
  ≡ qRej
SVM-check-run-half = refl

-- 尾注立界（诚实边界——不设空壳签名）
-- (i)   配对 SVM-cellOf 是输入编码，不计机内步数：单带上一次 a[v] 读取需
--       onehot 解码 + 移头 O(m)——故「1 步/文字」是**控制结构**口径，整机
--       口径需 multi-tape 或自含头（承 SATMember §7(i)）。
-- (ii)  通用桥（任意 Counted 验证器 → TM）= Church-Turing 型深件，维持
--       PClass §6(i) / NPClass §5(iii) / TMBridge §5(i) 立界，本件不冒充。
-- (iii) 半截子句（终止符落在 qP1/qP2）不可达于整块 tape；δ 给保守 qRej，
--       不以「不可能是它」充当证明（该两行有具体 δ 语义与核对层）。
-- (iv)  本桥是等式级（值 + 精确燃料），非渐近；大 O 层维持 TimeBound §8(ii)。

-- 0 postulate / 0 hole。
