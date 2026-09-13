{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.ClockIteration
--
-- 杜德克时钟的**走钟过程**：参数化迭代、过程律、分量分解、联合周期（块 7）。
--
-- 本体论定位（**本源侧**，见下）：
--   本模块只谈 DC 自己的生成结构 —— `DuodecPoint = Trit × AlphaPower` 上的
--   `mixedOp`（幅度 GF(3) 加法 ⊕ 相位 GF(9)⟨α⟩ 乘法，联合走一步）沿联合生成元
--   `g = (T₁,a1)` 的**迭代**。这是展示群八要素里的
--       · 时钟 = 迭代过程（走钟 n 步）
--       · 归零 = 周期闭合（12 步回来）
--   的**过程语言**形态，此前只有等式形态。
--
-- ⚠ **本体论红线（勿越）**：
--   本模块**不出现** `C₁₂` / `Fin 12` / `Action`，也**不做**任何「下降为 C₁₂ 作用」的表述。
--   理由（`docs/duodecimal/12-rigorous-type-theory.md:263-272`）：
--   `toDuodec` 是**有损投影 / 截断操作**，其丢弃清单**恰好包含「时钟过程」与「归零机制」**，
--   并明写「**投影方向 = 信息丢失方向**」。把走钟搬到 C₁₂ 上，
--   等于把它搬到已经丢掉走钟的地方 —— 自相矛盾。（该表述曾于 2026-09-10 被误写入 07 §9，已更正。）
--
-- 为什么用**分量分解**而不是「降到单群」：
--   `DayanCore.agda:108` 的 `iter-decompose` 已给出本源侧样板：
--       iterate (δ ∘ φ) n c ≡ iterate δ n (iterate φ n c)
--   —— 联合迭代**拆回两个生成元各自的迭代**，**保留两分量**。
--   本模块把同一形态落到 DC 的具体载体的两个分量上（幅度/相位），于是
--   `12 = lcm(3,4)` 是**推论**（幅度 3 步闭合 × 相位 4 步闭合，分量正交），不是定义。
--
-- 复用的既有件（**不重造**）：
--   · `mixedOp-power : DuodecPoint → ℕ → DuodecPoint`（`CyclicGroupStructure.agda:58-60`）
--     —— 参数化迭代**已存在**；`CyclicGroupStructure` 模块头承诺的 `mixedOp-power-add`
--     与 `dc-order-12` 在本模块补齐（它们此前**只出现在注释里**，代码中不存在）
--   · `iterate`（`DayanCore.agda:42-44`）—— 通用迭代器
--   · `⊕-assoc` / `⊕-identityʳ`（`Trit.agda`）、`mulAlpha-assoc` / `mulAlpha-identityʳ`
--     （`DuodecClock.agda`）、`mixedOp-12-cycle`（既有硬编码 12 重路径）
--
-- 核心原则：
--   1. `mixedOp` 是 let-free 直接模式匹配（`DuodecClock.agda:215`），故分量投影可归约
--   2. 全部证明是**结构归纳 + 分量代数链**，无 `%` / `/`，无 27 以上的穷举
--   3. 0 postulate / 0 hole；无 funExt；不引 Choice
--
-- 诚实边界：
--   · `generator-order-12` 检查的是 g 的**真因子** 1/2/3/4/6 步；「阶恰 12」的完整形式
--     还需「g^n = g ⟹ ord ∣ n」这类论证（本模块不证，只给真因子见证）
--   · 本模块不声称与任何「C₁₂ 作用」的关系（见上红线）
--
-- 包含：iterate-add / tritStep / phaStep
--       §2 mixedOp-power-add（过程律 = 头注释承诺的 mixedOp-power-add）
--       §3 mixedOp-power-decompose（分量分解，本源侧承重件）
--       §4 tritStep-3 / phaStep-4（分量周期）
--       §5 tritStep-12 / phaStep-12 / mixedOp-power-12（联合周期 = 12）
--       §6 mixedOp-power-agrees-^12（与既有硬编码路径一致）
--       §7 generator-order-12（真因子见证）

module Sovereign.Algebra.GroupTheory.ClockIteration where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; ⊕-assoc; ⊕-identityʳ)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; mixedOp; mulAlpha;
   mulAlpha-assoc; mulAlpha-identityʳ; mixedOp-12-cycle; mixedOp^12)
open import Sovereign.Algebra.GroupTheory.CyclicGroupStructure using (mixedOp-power)
open import Sovereign.Algebra.GroupTheory.DayanCore using (iterate)

-- ⚠ fixity 说明（实测结论，勿在本模块重复尝试）：
--   `Trit.agda` **未**声明 `_⊕_` / `_⊗_` 的 fixity（该文件无任何 infix 行），
--   故全库使用 `⊕` 的模块都吃**默认 fixity**（infixl 9）。
--   本模块**不能**在本地补 `infixl 6 _⊕_` —— Agda 报 [UnknownNamesInFixityDecl]：
--   fixity 只能针对同作用域内声明的名字，而 `_⊕_` 是 import 进来的。
--   正确修法是在 `Trit.agda` 里声明，但那会**改变全库所有未加括号的 ⊕ 表达式的解析**
--   （Trit 被 300+ 模块依赖）⇒ 属全库级操作，必须单独立项、单独评估，不得顺手做。
--   本模块的对策：所有复合 `⊕` 表达式**一律显式括号**（proof-engineer 附录 4 第二条），
--   故不依赖 fixity，解析无歧义。
open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 通用迭代加法律 + 两个分量步算子
--------------------------------------------------------------------------------

-- 通用件：iterate 对「步数相加」的分解（对 n 归纳）
--
-- ⚠ 归约陷阱（本库经验库 agda-one-mul-yields-n-plus-zero 的同根因）：
--   `_+_` 按**第一参数**递归，故 `m + zero` 与 `m + suc n` 对符号 m **都不归约**。
--   必须显式接 `+-identityʳ` / `+-suc` 把索引改写成能归约的形状，不能用 refl。
iterate-add : ∀ {A : Set} (f : A → A) (m n : ℕ) (c : A)
            → iterate f (m + n) c ≡ iterate f n (iterate f m c)
iterate-add f m zero    c = cong (λ k → iterate f k c) (+-identityʳ m)
iterate-add f m (suc n) c =
  trans (cong (λ k → iterate f k c) (+-suc m n))
        (cong f (iterate-add f m n c))

-- 幅度分量步：⊕ T₁（GF(3) 加法，特征 3）
tritStep : Trit → Trit
tritStep t = t ⊕ T₁

-- 相位分量步：· a1（⟨α⟩ 乘法，阶 4）
phaStep : AlphaPower → AlphaPower
phaStep a = mulAlpha a a1

--------------------------------------------------------------------------------
-- §2. 过程律（幂加法律）—— CyclicGroupStructure 头注释承诺但代码中不存在
--------------------------------------------------------------------------------

-- 同一归约陷阱：索引处的 `m + zero` / `m + suc n` 需先经 +-identityʳ / +-suc 改写
mixedOp-power-add : ∀ (p : DuodecPoint) (m n : ℕ)
                  → mixedOp-power p (m + n) ≡ mixedOp-power (mixedOp-power p m) n
mixedOp-power-add p m zero =
  cong (λ k → mixedOp-power p k) (+-identityʳ m)
mixedOp-power-add p m (suc n) =
  trans (cong (λ k → mixedOp-power p k) (+-suc m n))
        (cong (λ u → mixedOp u (T₁ , a1)) (mixedOp-power-add p m n))

--------------------------------------------------------------------------------
-- §3. 分量分解（本源侧承重件：拆回两分量，不压成单群）
--------------------------------------------------------------------------------

mixedOp-power-decompose : ∀ (t : Trit) (a : AlphaPower) (n : ℕ)
                        → mixedOp-power (t , a) n
                        ≡ (iterate tritStep n t , iterate phaStep n a)
mixedOp-power-decompose t a zero = refl
mixedOp-power-decompose t a (suc n) =
  trans (cong (λ u → mixedOp u (T₁ , a1)) (mixedOp-power-decompose t a n))
        refl

--------------------------------------------------------------------------------
-- §4. 分量周期：幅度 3 步闭合、相位 4 步闭合
--------------------------------------------------------------------------------

-- 幅度：T₁ ⊕ T₁ = T₂，T₂ ⊕ T₁ = T₀ ⇒ 三步步回原处
tritStep-3 : ∀ t → iterate tritStep 3 t ≡ t
tritStep-3 t = begin
  ((t ⊕ T₁) ⊕ T₁) ⊕ T₁       ≡⟨ ⊕-assoc (t ⊕ T₁) T₁ T₁ ⟩
  (t ⊕ T₁) ⊕ (T₁ ⊕ T₁)       ≡⟨ ⊕-assoc t T₁ (T₁ ⊕ T₁) ⟩
  t ⊕ (T₁ ⊕ (T₁ ⊕ T₁))       ≡⟨ ⊕-identityʳ t ⟩
  t                          ∎

-- 相位：α⁴ = 1 ⇒ 四步回原处（把 a₁ 的四次连乘经结合律并成 (a1⁴) = a0）
phaStep-4 : ∀ a → iterate phaStep 4 a ≡ a
phaStep-4 a = begin
  mulAlpha (mulAlpha (mulAlpha (mulAlpha a a1) a1) a1) a1
    ≡⟨ mulAlpha-assoc (mulAlpha (mulAlpha a a1) a1) a1 a1 ⟩
  mulAlpha (mulAlpha (mulAlpha a a1) a1) (mulAlpha a1 a1)
    ≡⟨ mulAlpha-assoc (mulAlpha a a1) a1 (mulAlpha a1 a1) ⟩
  mulAlpha (mulAlpha a a1) (mulAlpha a1 (mulAlpha a1 a1))
    ≡⟨ mulAlpha-assoc a a1 (mulAlpha a1 (mulAlpha a1 a1)) ⟩
  mulAlpha a (mulAlpha a1 (mulAlpha a1 (mulAlpha a1 a1)))
    ≡⟨ mulAlpha-identityʳ a ⟩
  a                          ∎

--------------------------------------------------------------------------------
-- §5. 联合周期 12 = lcm(3,4)：分量正交（12 = 3 × 4，且 3 与 4 互质）
--------------------------------------------------------------------------------

-- 12 = 3 + 3 + 3 + 3：四层幅度 3-周期塌缩
tritStep-12 : ∀ t → iterate tritStep 12 t ≡ t
tritStep-12 t = begin
  iterate tritStep 12 t
    ≡⟨ iterate-add tritStep 9 3 t ⟩
  iterate tritStep 3 (iterate tritStep 9 t)
    ≡⟨ cong (iterate tritStep 3) (iterate-add tritStep 6 3 t) ⟩
  iterate tritStep 3 (iterate tritStep 3 (iterate tritStep 6 t))
    ≡⟨ cong (iterate tritStep 3)
           (cong (iterate tritStep 3) (iterate-add tritStep 3 3 t)) ⟩
  iterate tritStep 3 (iterate tritStep 3
    (iterate tritStep 3 (iterate tritStep 3 t)))
    ≡⟨ tritStep-3 (iterate tritStep 3 (iterate tritStep 3 (iterate tritStep 3 t))) ⟩
  iterate tritStep 3 (iterate tritStep 3 (iterate tritStep 3 t))
    ≡⟨ tritStep-3 (iterate tritStep 3 (iterate tritStep 3 t)) ⟩
  iterate tritStep 3 (iterate tritStep 3 t)
    ≡⟨ tritStep-3 (iterate tritStep 3 t) ⟩
  iterate tritStep 3 t
    ≡⟨ tritStep-3 t ⟩
  t                          ∎

-- 12 = 4 + 4 + 4：三层相位 4-周期塌缩
phaStep-12 : ∀ a → iterate phaStep 12 a ≡ a
phaStep-12 a = begin
  iterate phaStep 12 a
    ≡⟨ iterate-add phaStep 8 4 a ⟩
  iterate phaStep 4 (iterate phaStep 8 a)
    ≡⟨ cong (iterate phaStep 4) (iterate-add phaStep 4 4 a) ⟩
  iterate phaStep 4 (iterate phaStep 4 (iterate phaStep 4 a))
    ≡⟨ phaStep-4 (iterate phaStep 4 (iterate phaStep 4 a)) ⟩
  iterate phaStep 4 (iterate phaStep 4 a)
    ≡⟨ phaStep-4 (iterate phaStep 4 a) ⟩
  iterate phaStep 4 a
    ≡⟨ phaStep-4 a ⟩
  a                          ∎

-- 联合周期：走钟 12 步回到原处（经分量分解 + 两个分量周期）
mixedOp-power-12 : ∀ p → mixedOp-power p 12 ≡ p
mixedOp-power-12 (t , a) = begin
  mixedOp-power (t , a) 12                ≡⟨ mixedOp-power-decompose t a 12 ⟩
  (iterate tritStep 12 t , iterate phaStep 12 a)
                                          ≡⟨ cong₂ _,_ (tritStep-12 t) (phaStep-12 a) ⟩
  (t , a)                                 ∎

--------------------------------------------------------------------------------
-- §6. 与既有硬编码路径交叉一致（两条独立路径证同一事实）
--------------------------------------------------------------------------------

mixedOp-power-agrees-^12 : ∀ p → mixedOp-power p 12 ≡ mixedOp^12 p
mixedOp-power-agrees-^12 p =
  trans (mixedOp-power-12 p) (sym (mixedOp-12-cycle p))

--------------------------------------------------------------------------------
-- §7. 生成元阶恰 12（真因子见证）—— 头注释承诺的 dc-order-12 的实质部分
--------------------------------------------------------------------------------

g : DuodecPoint
g = (T₁ , a1)

T₂≢T₁ : T₂ ≢ T₁
T₂≢T₁ ()

T₀≢T₁ : T₀ ≢ T₁
T₀≢T₁ ()

a0≢a1 : a0 ≢ a1
a0≢a1 ()

a3≢a1 : a3 ≢ a1
a3≢a1 ()

-- 1 步：g² = (T₂, a2)，不比 g 小
g1≢g : mixedOp-power g 1 ≢ g
g1≢g eq = T₂≢T₁ (cong proj₁ eq)

-- 2 步：g³ = (T₀, a3)
g2≢g : mixedOp-power g 2 ≢ g
g2≢g eq = T₀≢T₁ (cong proj₁ eq)

-- 3 步：g⁴ = (T₁, a0)
g3≢g : mixedOp-power g 3 ≢ g
g3≢g eq = a0≢a1 (cong proj₂ eq)

-- 4 步：g⁵ = (T₂, a1)
g4≢g : mixedOp-power g 4 ≢ g
g4≢g eq = T₂≢T₁ (cong proj₁ eq)

-- 6 步：g⁷ = (T₁, a3)
g6≢g : mixedOp-power g 6 ≢ g
g6≢g eq = a3≢a1 (cong proj₂ eq)

-- 真因子见证打包：DC 走钟的周期不是 1/2/3/4/6
generator-order-12 :
    (mixedOp-power g 1 ≢ g)
  × (mixedOp-power g 2 ≢ g)
  × (mixedOp-power g 3 ≢ g)
  × (mixedOp-power g 4 ≢ g)
  × (mixedOp-power g 6 ≢ g)
generator-order-12 = g1≢g , g2≢g , g3≢g , g4≢g , g6≢g
