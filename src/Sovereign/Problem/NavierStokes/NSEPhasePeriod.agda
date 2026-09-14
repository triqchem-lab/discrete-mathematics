{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEPhasePeriod
-- 相位路径累积的周期律 (闭合 NSEPhaseField 的 O3 可证部分)
--
-- 背景 (来自 NSEPhaseField.agda 的开放义务清单 :541-549):
--   O3「相位刚性 ⇒ 无爆聚」被拆成三项:
--     ✓ 已证: 固定旋转迭代四步回归  (phase-accumulation-period-4, :529)
--     ✗ 未证: 任意相位路径的累积回归 —— 反例 (a1,a1,a1,a2) 的累积 = a1 ≠ a0 (:526/:544)
--     ✗ 未证: 「因此无爆聚」(需先定义爆聚)
--
-- 本模块把中间那一项**精确化并闭合其可证部分**:
--   反例击穿的是「**任意路径在 4 步内**回归」—— 该命题确实是**假**的, 不应去证。
--   但相位层是 C₄: **一条固定路径走一遍**的累积只是一个确定的 P ∈ C₄;
--   而 P⁴ = 1 对 C₄ 的**每个**元素成立 (φ⁴ = id 的直接后果)。
--   故「路径重复 4 次 ⇒ 回归」是**真命题且不依赖路径细节** —— 这正是
--   反例注记所说的「周期 = lcm(各旋转阶)」的可用形式 (每个阶整除 4 ⇒ lcm 整除 4)。
--
-- 结构 (全部构造性, 无 postulate / 无 hole):
--   §1 路径类型 Path 与累积 accumPath
--   §2 拼接同态 accumPath-++  (归纳 + mulAlpha-assoc)
--   §3 主定理 accumPath-repeat-4 : 重复 4 次 ⇒ a0
--   §4 推论 accumPath-order-divides-4 : 单周期累积的四次幂 = a0
--   §5 对抗验证: 反例路径 (a1,a1,a1,a2) 的**单周期**累积确为 a1 ≠ a0 (refl),
--      但按 §3 重复 4 次后回归 —— 两个断言同时为真, 不冲突。
--
-- ⚠ 依赖纪律 (2026-09-14): 本模块**只** import 已在缓存中的 stdlib 模块
--   (Relation.Binary.PropositionalEquality / DuodecClock / NSEPhaseField)。
--   **不** import `Data.List`: 它的接口在本机缓存中陈旧, 会迫使 Agda
--   重新检查并**回写 agda-stdlib/_build/**, 而该目录在工作区外
--   (沙箱只读 ⇒ exit 42 且错误数 0)。路径类型只有 3 个构造子, 本地定义即可,
--   这样编译**完全不触碰标准库目录**。
--
-- 依赖: Sovereign.Problem.NavierStokes.NSEPhaseField (取 rotate/rotate-4)
--       Sovereign.Algebra.GroupTheory.DuodecClock (AlphaPower/mulAlpha)
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEPhasePeriod where

open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; cong; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.DuodecClock using (
  AlphaPower; a0; a1; a2; mulAlpha; mulAlpha-assoc;
  mulAlpha-identityˡ; mulAlpha-identityʳ)
open import Sovereign.Problem.NavierStokes.NSEPhaseField using (rotate; rotate-4)

--------------------------------------------------------------------------------
-- §1. 路径类型与路径累积
--
-- 语义: 一条路径 ps = p₁ ∷ p₂ ∷ … ∷ [] 表示依次施加的相位转动;
--       其累积效应是首尾相接的乘积 p₁·p₂·…·pₙ ( ∈ C₄)。
--
-- (本地归纳类型, 不引入 Data.List —— 见模块头的依赖纪律)
--------------------------------------------------------------------------------

data Path : Set where
  ⟨⟩   : Path
  _∷_  : AlphaPower → Path → Path

infixr 5 _∷_

accumPath : Path → AlphaPower
accumPath ⟨⟩       = a0
accumPath (p ∷ ps) = mulAlpha p (accumPath ps)

--------------------------------------------------------------------------------
-- §2. 拼接: Path 的串联与其同态律
--
-- 这是把「路径」与「群乘法」接起来的关键引理 —— 有了它,
-- 重复路径的累积才能化为「同一元素的自乘幂」。
--------------------------------------------------------------------------------

_++P_ : Path → Path → Path
⟨⟩      ++P qs = qs
(p ∷ ps) ++P qs = p ∷ (ps ++P qs)

infixr 5 _++P_

accumPath-++ : ∀ (ps qs : Path) →
  accumPath (ps ++P qs) ≡ mulAlpha (accumPath ps) (accumPath qs)
accumPath-++ ⟨⟩      qs = sym (mulAlpha-identityˡ (accumPath qs))
accumPath-++ (p ∷ ps) qs = begin
    accumPath ((p ∷ ps) ++P qs)
  ≡⟨ refl ⟩
    mulAlpha p (accumPath (ps ++P qs))
  ≡⟨ cong (mulAlpha p) (accumPath-++ ps qs) ⟩
    mulAlpha p (mulAlpha (accumPath ps) (accumPath qs))
  ≡⟨ sym (mulAlpha-assoc p (accumPath ps) (accumPath qs)) ⟩
    mulAlpha (mulAlpha p (accumPath ps)) (accumPath qs)
  ≡⟨ refl ⟩
    mulAlpha (accumPath (p ∷ ps)) (accumPath qs)
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §3. 主定理: 任一相位路径重复 4 次, 累积回到 a0
--
-- 证明路线: 令 P = accumPath ps。由 §2 逐层剥离, 左端化为
--   P·(P·(P·(P·a0)))
-- 而 rotate-4 P a0 (库内已证, NSEPhaseField:510) 正是该式 ≡ a0
-- (最后一跳前用 mulAlpha-identityʳ P 把内层的 P 写成 P·a0)。
-- 注意: 结论**与路径细节无关** —— 所有路径信息都被吸收进 P ∈ C₄。
--------------------------------------------------------------------------------

accumPath-repeat-4 : ∀ (ps : Path) →
  accumPath (ps ++P ps ++P ps ++P ps) ≡ a0
accumPath-repeat-4 ps = begin
    accumPath (ps ++P (ps ++P (ps ++P ps)))
  ≡⟨ accumPath-++ ps (ps ++P (ps ++P ps)) ⟩
    mulAlpha P (accumPath (ps ++P (ps ++P ps)))
  ≡⟨ cong (mulAlpha P) (accumPath-++ ps (ps ++P ps)) ⟩
    mulAlpha P (mulAlpha P (accumPath (ps ++P ps)))
  ≡⟨ cong (λ z → mulAlpha P (mulAlpha P z)) (accumPath-++ ps ps) ⟩
    mulAlpha P (mulAlpha P (mulAlpha P (accumPath ps)))
  ≡⟨ cong (λ z → mulAlpha P (mulAlpha P (mulAlpha P z)))
          (sym (mulAlpha-identityʳ P)) ⟩
    mulAlpha P (mulAlpha P (mulAlpha P (mulAlpha P a0)))
  ≡⟨ rotate-4 P a0 ⟩
    a0
  ∎
  where
    open ≡-Reasoning
    P : AlphaPower
    P = accumPath ps

--------------------------------------------------------------------------------
-- §4. 推论 (幂形式): 单周期累积 P 的四次幂为 1
--
-- 与 §3 等价但更便于与「阶整除 4」的说法对接:
-- 每个 P ∈ C₄ 的阶 ∈ {1,2,4}, 均整除 4 ⇒ 路径的周期整除 4。
--------------------------------------------------------------------------------

accumPath-order-divides-4 : ∀ (ps : Path) →
  mulAlpha (accumPath ps) (mulAlpha (accumPath ps)
    (mulAlpha (accumPath ps) (accumPath ps))) ≡ a0
accumPath-order-divides-4 ps = begin
    mulAlpha P (mulAlpha P (mulAlpha P P))
  ≡⟨ cong (λ z → mulAlpha P (mulAlpha P (mulAlpha P z)))
          (sym (mulAlpha-identityʳ P)) ⟩
    mulAlpha P (mulAlpha P (mulAlpha P (mulAlpha P a0)))
  ≡⟨ rotate-4 P a0 ⟩
    a0
  ∎
  where
    open ≡-Reasoning
    P : AlphaPower
    P = accumPath ps

--------------------------------------------------------------------------------
-- §5. 对抗验证 (纪律 §6): 具体点上独立 refl 计算
--
-- ⚠ 关键: 下面 (1) 与 (2) **同时为真**, 不构成矛盾 ——
--   (1) 反例路径在**单周期内**的累积 ≠ a0 (这正是 O3 注记里的反例);
--   (2) 同一路径**重复 4 次**后累积 = a0 (§3 的实例)。
-- 二者的差别是「周期内」与「跨周期」, 不是「对」与「错」。
--------------------------------------------------------------------------------

-- (1) 单周期反例: [a1,a1,a1,a2] 的累积 = a1·a1·a1·a2 = a1 ≠ a0
counterexample-path : Path
counterexample-path = a1 ∷ a1 ∷ a1 ∷ a2 ∷ ⟨⟩

counterexample-accum : accumPath counterexample-path ≡ a1
counterexample-accum = refl

counterexample-nonzero : accumPath counterexample-path ≢ a0
counterexample-nonzero ()

-- (2) 同一路径重复 4 次 ⇒ 回归 (即 §3 的实例, 由定理直接给出)
counterexample-repeat-4 :
  accumPath (counterexample-path ++P counterexample-path
             ++P counterexample-path ++P counterexample-path) ≡ a0
counterexample-repeat-4 = accumPath-repeat-4 counterexample-path

-- (3) 退化路径: 空路径的累积 = a0, 且重复仍为 a0
empty-accum : accumPath ⟨⟩ ≡ a0
empty-accum = refl

empty-repeat : accumPath (⟨⟩ ++P ⟨⟩ ++P ⟨⟩ ++P ⟨⟩) ≡ a0
empty-repeat = refl

-- (4) 单元素路径 [a1]: 单周期累积 = a1 (阶 4), 四次幂回归
singleton-path : Path
singleton-path = a1 ∷ ⟨⟩

singleton-accum : accumPath singleton-path ≡ a1
singleton-accum = refl

singleton-order : mulAlpha a1 (mulAlpha a1 (mulAlpha a1 a1)) ≡ a0
singleton-order = accumPath-order-divides-4 singleton-path
