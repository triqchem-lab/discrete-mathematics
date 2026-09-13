{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.KernelSpec — 内核空类型判定（eb1251683f）的**补丁无关条款**
--
-- 定位（2026-09-13 更正）：**数学侧早已证完**，缺的是「Haskell 分支 ↔ 已证条款」的
-- **机械对接**（L2，工程件）。本模块把该对接的**规范侧**写成可编译的签名：
-- 每一条款都能指到库内已证的三层单射性，或指到一个可复跑的 exit 码判据。
--
-- ⚠ 本模块是 A/B 矩阵的**真负控制**（2026-09-13 拆分，依据用户反馈第 3 条）：
--   旧版本模块自己 import 了 `Sovereign.Trust.PatchedTypeChecker`，而后者在**无补丁内核**
--   上 import 阶段就炸（`PatchedTypeChecker.agda:84` `Is empty: R1 ≡ R2 (stuck)`）。
--   于是所谓「双版本差分」那一行的失败点落在被 import 的模块里，**本模块自己的条款
--   从未在两版下被对照检查过** —— 那一行与 `PatchedTypeChecker` 的行完全冗余。
--   拆分后：
--     · **本模块**：零补丁依赖 ⇒ 必须在 2.9.0 与官方 2.8.0.1 上**都通过**（负控制臂）。
--     · `Sovereign.Trust.KernelWitness`：自带 R1w/R2w，承载 K1 正控制 ⇒ 2.9.0 通过、
--       2.8.0.1 在**它自己的** `¬R1w≡R2w ()` 行失败。
--   四行矩阵（模块 × 内核）里「第二行通过、第四行失败」，才是「差分测的是补丁，
--   而不是环境噪声」的有效证据。只有正控制、没有负控制的差分是无信息的。
--
-- 补丁本体（git numstat 实测，非转述）：**2 个文件 / 净 +9 −1**
--   · Empty.hs +1/−0： checkEmptyType 中 `splitLast` 前加 `tel <- instantiateFull tel`
--   · Unify.hs +8/−1： failure 在「零消去(es=[])、相异 Def(d≠d')」时返回
--                      `NoUnify (UnifyConflict …)`，而非 `UnifyStuck []`
--   （同提交另有 10 个黄金期望文件、792 行误入库 .bak、.gitignore 一行 ⇒ 合计 15 文件 +822/−43）
--
-- 数学锚点（三层，均已证，本模块用**签名**钉住；锚点漂移 ⇒ 本模块编译失败 = 自动告警）：
--   算术层 Sovereign.Arithmetic.CRTLemmas:22/104  coprime-POW2-POW3 / crt-merge
--   双射层 Sovereign.Algebra.Duodecimal:438/445/454  crt12-roundtrip / -inv-π3 / -inv-π4
--   望远镜层 Sovereign.Structology.QuantumBridge:395 起「构造子注入性的 CRT 正交分解」
--            （:604 module TelescopeVerification；:640/:661/:668/:702/:712 为名字级对应）

module Sovereign.Trust.KernelSpec where

open import Data.Product using (_×_; _,_; proj₁)
open import Data.Nat.Base using (_%_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Arithmetic.CRTLemmas using (POW2; POW3; M; crt-merge)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; π3; π4; crt12; crt12-roundtrip; crt12-inv-π3; crt12-inv-π4)

--------------------------------------------------------------------------------
-- §1 锚点索具：把三层单射性钉进一个签名（锚点漂移 ⇒ 本模块编译失败）
--------------------------------------------------------------------------------

-- | K4 锚点：把两层单射性**钉成签名**
--     · 算术层：两个互质投影上一致 ⇒ mod M 一致（正交性）
--     · 双射层：12 元载体上 (π₃,π₄) 与 crt12 互逆
anchor-arithmetic : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
anchor-arithmetic = crt-merge

anchor-bijection : ∀ x → crt12 (π3 x) (π4 x) ≡ x
anchor-bijection = crt12-roundtrip

--------------------------------------------------------------------------------
-- §2 K4 推论：单射性 ⇒ 相异编码不可等（「相异刚性头 ⇒ ≡ 空」的模型侧）
--------------------------------------------------------------------------------

-- | (π₃,π₄) 单射：两个投影都相同 ⇒ 载体元素相同
pair-injective : ∀ {x y : Duodec} → π3 x ≡ π3 y → π4 x ≡ π4 y → x ≡ y
pair-injective {x} {y} p3 p4 =
  trans (sym (crt12-roundtrip x))
    (trans (cong₂ crt12 p3 p4) (crt12-roundtrip y))

-- | crt12 作为二元映射单射（由两条左逆律直接得出）
crt12-injective : ∀ {a a′ : Trit} {b b′ : Fin 4}
                → crt12 a b ≡ crt12 a′ b′ → (a ≡ a′) × (b ≡ b′)
crt12-injective {a} {a′} {b} {b′} p =
    trans (sym (crt12-inv-π3 a b)) (trans (cong π3 p) (crt12-inv-π3 a′ b′))
  , trans (sym (crt12-inv-π4 a b)) (trans (cong π4 p) (crt12-inv-π4 a′ b′))

-- | 单射 ⇒ 相异原像的像相异（这就是「冲突判定」的数学内容）
injective⇒≢ : ∀ {A B : Set} (f : A → B)
            → (∀ {x y} → f x ≡ f y → x ≡ y) → ∀ {x y} → x ≢ y → f x ≢ f y
injective⇒≢ f inj neq p = neq (inj p)

-- | 特例：固定第二分量，相异第一分量不可同码
crt12-distinct : ∀ {a a′ : Trit} {b : Fin 4} → a ≢ a′ → crt12 a b ≢ crt12 a′ b
crt12-distinct {a} {a′} {b} neq =
  injective⇒≢ (λ x → crt12 x b)
    (λ {x} {y} p → proj₁ (crt12-injective {x} {y} {b} {b} p)) neq

--------------------------------------------------------------------------------
-- §3 条款表（Haskell 侧对拍单测的规范；单测由使用者撰写）
--------------------------------------------------------------------------------
--
-- K1 相异刚性头冲突（Unify.hs `failure` 分支）——**正控制已移至 `KernelWitness`**
--   陈述: 两侧均为**零消去**的 `Def` 头且名字相异 ⇒ 必须 `NoUnify (UnifyConflict …)`
--   Agda: `KernelWitness.¬R1w≡R2w`（2.9.0 通过 / 2.8.0.1 失败）、
--         `KernelWitness.K2w-same-def-inhabited`（同头非空，两版都过）
--   单测: `(Def R1 [], Def R2 [])` → Conflict；`(Def R1 [], Def R1 [])` → Unifies
--
-- K2 不可判不得当判（三值纪律；对应 DecisionSoundness 的 C5）
--   陈述: 两侧**不是**零消去相异 Def 时（同 Def / 带消去子 / 含未解元变量）⇒ 必须
--         保持 `UnifyStuck []`（延迟），不得复用 K1 判冲突
--   单测: `(Def f [x], Def g [x])`（带消去子）→ Stuck；`(MetaV ?m [], Def R2 [])` → Stuck
--
-- K3 判空前的实例化只读已解元变量（Empty.hs）
--   陈述: `checkEmptyType` 必须先 `instantiateFull tel` 再 `splitLast`；结论只基于**已解**替换
--   判据: Issue292 形态本机 exit 0 / 2.8.0.1 exit 42（blocked on MetaV）
--   单测: telescope 末项类型头为**已解** MetaV ⇒ 判空成功；头为**未解** MetaV ⇒ 仍 DontKnow
--
-- K4 正当性锚点 = 编码单射（数学侧三层；§1 两条引理钉签名、§2 给推论）
--   算术层 `crt-merge` + 双射层 `crt12-roundtrip/-inv-π3/-inv-π4` + 望远镜层 QuantumBridge:395 起
--   单测: 无（数学侧）；但锚点签名漂移会让本模块编译失败 = 自动告警

--------------------------------------------------------------------------------
-- §4 边界（不许越界）
--------------------------------------------------------------------------------
-- · 本模块只规范两侧**观测面**：Agda 侧命题 + Haskell 侧 UnificationResult。
--   它**不**把 Haskell 实现形式化为 Agda 定理（那要把 tcm 状态机搬进 Agda，不划算）。
-- · **本模块不含任何补丁相关条款**（这是拆分的全部意义）：它在两版内核上都必须通过，
--   否则说明「差分」被环境噪声污染，A/B 矩阵失去判据价值。
-- · 数学侧没有悬案：单射性三层已证；缺口只是「名字级对应 → 可测对应」的工程件。

-- 0 postulate.
