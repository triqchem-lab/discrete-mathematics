-- | Sovereign.Algebra.LinearAlgebra.ListBounds
-- 「独立表的三条界互不相容」—— 不用实数的 Agda 镜像
--
-- 数学背景（镜像对象: OpenAI `openai/math` 仓库
-- `OAI/LinearAlgebra/MatrixExponent/ListBounds.lean` 与 `Iteration.lean:76–77` 的
-- `incompatible`; 来龙去脉见 docs/techniques/OpenAI-omega-9-4-只读审计-2026-11-25.md 文末《读完记录》）:
--   设 P w t m 表示「宽度 w 的 t 重张量幂有一个规模为 m 的精确实现」。三条性质:
--     Seed        t = 1 时有一个多项式开销的平凡实现;
--     ManyList    每个实现都至少要 t·n·w^σ 这么大（硬度）;
--     Compression 足够小的实现可以放大 d 倍并节省规模。
--   三者互不相容。它是那个下界里唯一与域无关、不需要枚举的一环: 对一切 w 成立的软论证。
--
-- 与 Lean 的逐条对照（Lean 行号为 2026-11-26 读到的原文）:
--   Lean                                                    本文件
--   listBits w = 2 * w * 2 ^ w                        (:14) lb-listBits
--   Seed P                                            (:16) lb-Seed P lb-listBits
--   ManyList P                                        (:20) lb-Many P lb-listBits
--   Compression P                                     (:25) lb-Comp P lb-listBits (λ w → w * w)
--   Seed P → ManyList P → Compression P → False  (:76) lb-incompatible-lists
--
-- 本文件证了的（全部过 Agda 2.9.0-nightly 内核, 0 postulate, 0 REWRITE 规则, 只依赖标准库）:
--   ★ lb-incompatible       : lb-Grow N H → lb-Seed P N → lb-Many P N → lb-Comp P N H → ⊥
--   ★ lb-incompatible-lists : 上条取 N := lb-listBits、H := λ w → w * w
--   ★ lb-wk≤2w              : 2 ^ (k + 4) ≤ w → w ^ k ≤ 2 ^ w
--     （增长条件 lb-Grow 第一个分量的内容, 经 lb-listBits-grow 接入;
--       另两个分量对 H = w² 是 lb-w≤ww 与 ≤-refl）
--   证明是独立重构: 写成时只读过 Lean 证明的开头。事后（2026-11-26）通读 `Iteration.lean`（164 行）,
--   确认两边同构: 步引理 lb-step-Y ↔ `absorb`; 迭代不变式 lb-Inv ↔ `iterate`;
--   副本界 t ≤ n^(j·δ), δ = 1/(40·J) ↔ `copies`; 终局矛盾 ↔ 末段; 都在 η = σ/4 处调用压缩
--   （Lean: `compress (σ / 4)`; 本文件: `comp p (4 * q)`）。两处差别: 衰减率——Lean 取
--   b = min γ (σ/2)/2, 本文件 rn/(16·q·G) = min(γ/4, σ/16), 更保守; 取 w——Lean 用 Mathlib 的
--   渐近工具, 本文件取 w = W^N0 把一切化成 W 的整数次幂。
--
-- 不用实数的表述（宪法禁无理数; Lean 原文用实指数 w^σ）:
--   · 分数次幂只出现在不等式里。两边乘方成整数不等式: σ = p/q 时
--     「t·n·w^σ < 3m」写成「(t·n)^q · w^p < (3m)^q」;
--     「d ≤ n^(1/D)」写成「d^D ≤ n」;「m ≤ n^(21/20)」写成「m^20 ≤ n^21」。
--   · Compression 里 h 的分数次幂写成「对一切满足侧条件的自然数 u、v」的形式（§7 lb-Comp）。
--   · 证明把 w 取在子序列 w = W^N0 上（N0 = 16·q·G 是各指数的公分母）, w 的幂全是 W 的整数次幂。
--   · n 与 h 抽象成满足增长条件的函数 N、H（lb-Grow）; listBits 与 h := w² 在 §10 实例化。
--
-- 证明骨架（每步的定理名）:
--   lb-rn-pkg   选衰减率 rn: 2·rn·G ≤ 16·q·G·g 且 rn + 1 ≤ 8·G·p
--   lb-step-Y   一步: 硬度 t·n·W^(2·half) < 3m ⟹ m + t·n·W^half·W^(2·rn) ≤ m·W^rn
--   lb-step     上条 + 压缩给出的界 ⟹ m′·W^rn ≤ d·m
--   lb-copy     t^(40·J) ≤ n^j ⟹ t ≤ n（副本数不失控）
--   lb-size     + 规模界 ⟹ m^20 ≤ n^21（下一步的压缩前提）
--   lb-iter     迭代 J = 3·N0 + 16·G·p 步, 保持不变式 lb-Inv
--   lb-seed-at / lb-many-at / lb-comp-at   三条性质搬到 w = W^N0 上
--   lb-final    J 步后 3m ≤ t·n·W^(2·half), 与硬度矛盾
--   lb-wk≤2w    归纳于 k, 取半 a = lb-half w: 线性·常数 ≤ 指数（lb-lin-exp）
--
-- 诚实边界:
--   1. ⚠ 「Lean 的实数陈述 ⟹ 本文件的 ℕ 陈述」这座桥**没有形式化** [手工论证·未验证]:
--        Seed: 取有理数 c₁/c₂ ≥ C, 通分即得;
--        ManyList: 取有理数 p/q ≤ σ, 两边取 q 次幂;
--        Compression: 取有理数 g/G ≤ γ; u^G ≤ h^g 给出 u ≤ h^γ, 于是 m·h^(−γ)·u ≤ m;
--                      h^e ≤ v^E 给出 h^η ≤ v;
--        h: Lean 取 h = Nat.clog 2 (listBits w); w ≤ h ≤ w²（对 w ≥ 2）把 h 换成 H = w²。
--      缺什么才能证: 实数幂函数的单调性 + 用有理数从下方逼近实数 + clog 的界。
--      桥的左端（实指数 w^σ、h^γ, σ、γ 可为无理数）要 ℝ; 本库宪法禁无理数, 所以左端在本库写不出。
--      这座桥只能在 Lean 一侧补（一条「由 Lean 定义推出 ℕ 形式」的引理）, 本仓库不做。
--      所以本文件是「软核在 ℕ 上的一条**独立**定理**, **不是** Lean 那条定理的形式化推论。
--      旁证（是证据不是证明）: engineering/oracle_list_bounds.py 的 G1–G3、H（分数精确抽样）。
--   2. 本文件只镜像软核。硬度与压缩本身（对具体网络模型）不在这里。
--   3. 这**不**是任何域上任何矩阵乘法下界的证明; 也不改变 ω = 9/4 一事的审计状态。

module Sovereign.Algebra.LinearAlgebra.ListBounds where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _≤?_; _<?_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤n⇒m≤1+n; <⇒≤; <-≤-trans; ≤-<-trans; <-asym; ≰⇒>; ≮⇒≥
        ; *-monoʳ-≤; *-monoˡ-≤; *-mono-≤; *-assoc; *-comm; *-identityˡ; *-identityʳ
        ; *-distribʳ-+; +-suc; +-comm; +-assoc; +-identityʳ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; m≤m+n; m≤n+m
        ; ^-distribˡ-+-*; ^-distribʳ-*; ^-*-assoc; ^-monoʳ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

--------------------------------------------------------------------------------
-- §0. 基础: ℕ 上幂与序的引理
--------------------------------------------------------------------------------

-- m + 1 ≡ suc m
lb-add1 : ∀ m → m + 1 ≡ suc m
lb-add1 m = trans (+-suc m zero) (cong suc (+-identityʳ m))

-- 幂的单调性（底）
lb-pow≤ : ∀ k {a b} → a ≤ b → a ^ k ≤ b ^ k
lb-pow≤ zero _ = ≤-refl
lb-pow≤ (suc k) h = *-mono-≤ h (lb-pow≤ k h)

-- 底 ≥ 1 则幂 ≥ 1
lb-pow1 : ∀ k {a} → 1 ≤ a → 1 ≤ a ^ k
lb-pow1 zero _ = ≤-refl
lb-pow1 (suc k) {a} h =
  ≤-trans h (subst (λ z → z ≤ a ^ suc k) (*-identityʳ a) (*-monoʳ-≤ a (lb-pow1 k h)))

-- 指数 ≥ 1 时 a ≤ a ^ k
lb-pow-ge : ∀ k {a} → 1 ≤ a → 1 ≤ k → a ≤ a ^ k
lb-pow-ge zero _ ()
lb-pow-ge (suc k) {a} h _ =
  subst (λ z → z ≤ a ^ suc k) (*-identityʳ a) (*-monoʳ-≤ a (lb-pow1 k h))

-- 幂的单调性（指数）; 底须非零
lb-pow-mono : ∀ {a} k l → 1 ≤ a → k ≤ l → a ^ k ≤ a ^ l
lb-pow-mono {suc a} k l (s≤s _) h = ^-monoʳ-≤ (suc a) h
lb-pow-mono {zero} k l () h

-- 1 的幂
lb-pow-one : ∀ k → 1 ^ k ≡ 1
lb-pow-one zero = refl
lb-pow-one (suc k) = trans (*-identityˡ (1 ^ k)) (lb-pow-one k)

-- 2k 次幂拆成两个 k 次幂
lb-pow2 : ∀ a k → a ^ (2 * k) ≡ a ^ k * a ^ k
lb-pow2 a k = trans (cong (a ^_) (cong (k +_) (+-identityʳ k))) (^-distribˡ-+-* a k k)

-- 1 ≤ suc k（右端显式, 避免元变量）
lb-1≤ : ∀ k → 1 ≤ suc k
lb-1≤ _ = s≤s z≤n

-- m ≤ k·m
lb-m≤k·m : ∀ m k → 1 ≤ k → m ≤ k * m
lb-m≤k·m m (suc k) (s≤s _) = m≤m+n m (k * m)

-- m ≤ m·k（右乘版本）
lb-m≤m·k : ∀ m k → 1 ≤ k → m ≤ m * k
lb-m≤m·k m k hk = subst (λ z → m ≤ z) (*-comm k m) (lb-m≤k·m m k hk)

-- 乘积的正性（a、b 是变量时 1 * b 是卡死项, 不能直接当 1 用）
lb-1≤· : ∀ a b → 1 ≤ a → 1 ≤ b → 1 ≤ a * b
lb-1≤· a b ha hb = ≤-trans ha (lb-m≤m·k a b hb)

-- 严格单调: a < b、1 ≤ x ⟹ a·x < b·x
lb-*< : ∀ x a b → a < b → 1 ≤ x → a * x < b * x
lb-*< x a b h hx =
  ≤-trans (≤-reflexive (sym (lb-add1 (a * x))))
  (≤-trans (+-monoʳ-≤ (a * x) hx)
  (≤-trans (≤-reflexive (+-comm (a * x) x)) (*-monoˡ-≤ x h)))

-- 严格单调（左乘）: a < b、1 ≤ x ⟹ x·a < x·b
lb-<· : ∀ x a b → a < b → 1 ≤ x → x * a < x * b
lb-<· x a b h hx =
  subst (λ z → z < x * b) (sym (*-comm x a))
  (subst (λ z → a * x < z) (*-comm b x) (lb-*< x a b h hx))

-- 幂的严格单调: a·a^k ≤ a·b^k < b·b^k
lb-pow< : ∀ k {a b} → a < b → a ^ suc k < b ^ suc k
lb-pow< k {a} {b} h =
  ≤-<-trans (*-monoʳ-≤ a (lb-pow≤ k (<⇒≤ h)))
  (lb-*< (b ^ k) a b h (lb-pow1 k (≤-trans (s≤s z≤n) h)))

lb-<abs : ∀ {x} → x < x → ⊥
lb-<abs h = <-asym h h

-- 消去律
lb-cancelʳ-< : ∀ k a b → a * k < b * k → a < b
lb-cancelʳ-< k a b h with a <? b
... | yes p = p
... | no np = ⊥-elim (lb-<abs (<-≤-trans h (*-monoˡ-≤ k (≮⇒≥ np))))

lb-cancelʳ-≤ : ∀ k a b → 1 ≤ k → a * k ≤ b * k → a ≤ b
lb-cancelʳ-≤ k a b hk h with a ≤? b
... | yes p = p
... | no np = ⊥-elim (lb-<abs (<-≤-trans (lb-*< k b a (≰⇒> np) hk) h))

lb-pow-cancelʳ-≤ : ∀ k a b → a ^ suc k ≤ b ^ suc k → a ≤ b
lb-pow-cancelʳ-≤ k a b h with a ≤? b
... | yes p = p
... | no np = ⊥-elim (lb-<abs (≤-<-trans h (lb-pow< k (≰⇒> np))))

lb-pow-cancelʳ-< : ∀ k a b → a ^ suc k < b ^ suc k → a < b
lb-pow-cancelʳ-< k a b h with a <? b
... | yes p = p
... | no np = ⊥-elim (lb-<abs (<-≤-trans h (lb-pow≤ (suc k) (≮⇒≥ np))))

lb-pow-cancel≤ : ∀ e a b → 1 ≤ e → a ^ e ≤ b ^ e → a ≤ b
lb-pow-cancel≤ (suc e) a b (s≤s _) h = lb-pow-cancelʳ-≤ e a b h
lb-pow-cancel≤ zero a b () h

lb-pow-cancel< : ∀ e a b → 1 ≤ e → a ^ e < b ^ e → a < b
lb-pow-cancel< (suc e) a b (s≤s _) h = lb-pow-cancelʳ-< e a b h
lb-pow-cancel< zero a b () h

--------------------------------------------------------------------------------
-- §1. 乘法的换位（stdlib 环求解器）与幂的拆分
--------------------------------------------------------------------------------

-- 末两个因子换位
lb-swap12 : ∀ x b c → (x * b) * c ≡ (x * c) * b
lb-swap12 x b c = solve 3 (λ x′ b′ c′ → (x′ :* b′) :* c′ := (x′ :* c′) :* b′) refl x b c

-- t·n·v·u·v ≡ t·n·(v·v)·u
lb-Yv : ∀ t n v u → t * n * v * u * v ≡ t * n * (v * v) * u
lb-Yv t n v u =
  solve 4 (λ t′ n′ v′ u′ → t′ :* n′ :* v′ :* u′ :* v′ := t′ :* n′ :* (v′ :* v′) :* u′)
  refl t n v u

-- 3·m·(x·x)·2 ≡ (m·x)·(6·x)
lb-budget≡ : ∀ m x → 3 * m * (x * x) * 2 ≡ m * x * (6 * x)
lb-budget≡ m x =
  solve 2 (λ m′ x′ → con 3 :* m′ :* (x′ :* x′) :* con 2 := m′ :* x′ :* (con 6 :* x′))
  refl m x

-- a < b ⟹ b = (a+1) + o
lb-<-add : ∀ a b → a < b → Σ ℕ (λ o → b ≡ suc a + o)
lb-<-add zero (suc b) _ = b , refl
lb-<-add (suc a) (suc b) (s≤s h) = o , cong suc e
  where
  o : ℕ
  o = proj₁ (lb-<-add a b h)
  e : b ≡ suc a + o
  e = proj₂ (lb-<-add a b h)

-- 幂的移位: a < b、k < W ⟹ k·W^a ≤ W^b
lb-pow-split : ∀ W a b k → suc k ≤ W → a < b → k * W ^ a ≤ W ^ b
lb-pow-split (suc W) a b k (s≤s hW) hab =
  subst (λ z → k * suc W ^ a ≤ z) (sym e1)
  (≤-trans (*-monoˡ-≤ (suc W ^ a) (m≤n⇒m≤1+n hW))
  (lb-m≤m·k (suc W * suc W ^ a) (suc W ^ o) (lb-pow1 o (s≤s z≤n))))
  where
  o : ℕ
  o = proj₁ (lb-<-add a b hab)
  e : b ≡ suc a + o
  e = proj₂ (lb-<-add a b hab)
  e1 : suc W ^ b ≡ suc W * suc W ^ a * suc W ^ o
  e1 = trans (cong (suc W ^_) e) (^-distribˡ-+-* (suc W) (suc a) o)

-- 6·W^rn ≤ W^half（rn + 1 ≤ half）
lb-h6 : ∀ W half rn → 6 ≤ W → rn + 1 ≤ half → 6 * W ^ rn ≤ W ^ half
lb-h6 W half rn hW h =
  ≤-trans (*-monoˡ-≤ (W ^ rn) hW)
  (≤-trans (≤-reflexive lem) (lb-pow-mono (rn + 1) half (≤-trans (s≤s z≤n) hW) h))
  where
  lem : W * W ^ rn ≡ W ^ (rn + 1)
  lem = sym (trans (^-distribˡ-+-* W rn 1)
             (trans (cong ((W ^ rn) *_) (*-identityʳ W)) (*-comm (W ^ rn) W)))

--------------------------------------------------------------------------------
-- §2. 迭代一步: 规模每步多衰减一个 W^rn
--------------------------------------------------------------------------------

-- 一步的括号界: 由硬度「t·n·W^(2·half) < 3m」得 m + t·n·W^half·W^(2·rn) ≤ m·W^rn
--   （m 占一半额度: 2m ≤ m·W^rn; 第二项占另一半: 2Y ≤ m·W^rn, 靠 6·W^rn ≤ W^half）
lb-step-Y : ∀ W half rn n t m → 6 ≤ W → 1 ≤ rn → rn + 1 ≤ half →
  t * n * (W ^ (2 * half)) < 3 * m →
  m + t * n * (W ^ half) * (W ^ (2 * rn)) ≤ m * (W ^ rn)
lb-step-Y W half rn n t m hW hrn hh hL1 =
  lb-cancelʳ-≤ 2 (m + Y) R (lb-1≤ 1)
    (≤-trans (≤-reflexive (*-distribʳ-+ 2 m Y))
    (≤-trans (+-mono-≤ m2 (<⇒≤ Y2<))
             (≤-reflexive R2)))
  where
  Y : ℕ
  Y = t * n * (W ^ half) * (W ^ (2 * rn))
  R : ℕ
  R = m * (W ^ rn)
  h1W : 1 ≤ W
  h1W = ≤-trans (s≤s z≤n) hW
  hu : 1 ≤ W ^ (2 * rn)
  hu = lb-pow1 (2 * rn) h1W
  Yv : Y * (W ^ half) ≡ t * n * (W ^ (2 * half)) * (W ^ (2 * rn))
  Yv = trans (lb-Yv t n (W ^ half) (W ^ (2 * rn)))
       (cong (λ z → t * n * z * W ^ (2 * rn)) (sym (lb-pow2 W half)))
  s1 : Y * (W ^ half) < 3 * m * (W ^ (2 * rn))
  s1 = subst (λ z → z < 3 * m * (W ^ (2 * rn))) (sym Yv)
       (lb-*< (W ^ (2 * rn)) (t * n * (W ^ (2 * half))) (3 * m) hL1 hu)
  s1′ : Y * (W ^ half) * 2 < 3 * m * (W ^ (2 * rn)) * 2
  s1′ = lb-*< 2 (Y * (W ^ half)) (3 * m * (W ^ (2 * rn))) s1 (lb-1≤ 1)
  s2 : 3 * m * (W ^ (2 * rn)) * 2 ≤ m * (W ^ rn) * (W ^ half)
  s2 = ≤-trans (≤-reflexive (cong (λ z → 3 * m * z * 2) (lb-pow2 W rn)))
       (≤-trans (≤-reflexive (lb-budget≡ m (W ^ rn)))
       (*-monoʳ-≤ (m * (W ^ rn)) (lb-h6 W half rn hW hh)))
  s3 : Y * (W ^ half) * 2 < m * (W ^ rn) * (W ^ half)
  s3 = <-≤-trans s1′ s2
  s4 : Y * 2 * (W ^ half) < m * (W ^ rn) * (W ^ half)
  s4 = subst (λ z → z < m * (W ^ rn) * (W ^ half)) (lb-swap12 Y (W ^ half) 2) s3
  Y2< : Y * 2 < m * (W ^ rn)
  Y2< = lb-cancelʳ-< (W ^ half) (Y * 2) (m * (W ^ rn)) s4
  m2 : m * 2 ≤ m * (W ^ rn)
  m2 = *-monoʳ-≤ m (≤-trans (≤-trans (s≤s (s≤s z≤n)) hW) (lb-pow-ge rn h1W hrn))
  R2 : m * (W ^ rn) + m * (W ^ rn) ≡ m * (W ^ rn) * 2
  R2 = solve 1 (λ r′ → r′ :+ r′ := r′ :* con 2) refl R

-- 迭代一步: 压缩给出的界 + 第二项的界 ⟹ m′·W^rn ≤ d·m
lb-step : ∀ W half rn n t m d m′ → 6 ≤ W → 1 ≤ rn → rn + 1 ≤ half →
  t * n * (W ^ (2 * half)) < 3 * m →
  m′ * (W ^ (2 * rn)) ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn))) →
  m′ * (W ^ rn) ≤ d * m
lb-step W half rn n t m d m′ hW hrn hh hL1 hC =
  lb-cancelʳ-≤ (W ^ rn) (m′ * (W ^ rn)) (d * m) (lb-pow1 rn h1W) chain
  where
  h1W : 1 ≤ W
  h1W = ≤-trans (s≤s z≤n) hW
  lhs≡ : m′ * (W ^ rn) * (W ^ rn) ≡ m′ * (W ^ (2 * rn))
  lhs≡ = trans (*-assoc m′ (W ^ rn) (W ^ rn))
          (cong (m′ *_) (sym (lb-pow2 W rn)))
  hC′ : m′ * (W ^ (2 * rn)) ≤ d * (m * (W ^ rn))
  hC′ = ≤-trans hC (*-monoʳ-≤ d (lb-step-Y W half rn n t m hW hrn hh hL1))
  rhs≡ : d * (m * (W ^ rn)) ≡ d * m * (W ^ rn)
  rhs≡ = sym (*-assoc d m (W ^ rn))
  chain : m′ * (W ^ rn) * (W ^ rn) ≤ d * m * (W ^ rn)
  chain = ≤-trans (≤-reflexive lhs≡) (≤-trans hC′ (≤-reflexive rhs≡))

--------------------------------------------------------------------------------
-- §3. 两条推论: 副本数与规模
--------------------------------------------------------------------------------

-- 副本数: t^(40J) ≤ n^j（j ≤ J）⟹ t ≤ n 且 t^20 ≤ n
lb-copy : ∀ J j n t → 1 ≤ J → j ≤ J → 1 ≤ n → t ^ (40 * J) ≤ n ^ j →
  (t ≤ n) × (t ^ 20 ≤ n)
lb-copy J j n zero hJ hj hn h = z≤n , z≤n
lb-copy J j n (suc t) hJ hj hn h = tn , t20
  where
  nm : ∀ a b → a ≤ b → n ^ a ≤ n ^ b
  nm a b hab = lb-pow-mono a b hn hab
  jJ : 1 ≤ 40 * J
  jJ = *-mono-≤ (lb-1≤ 39) hJ
  tn : suc t ≤ n
  tn = lb-pow-cancel≤ (40 * J) (suc t) n jJ
       (≤-trans h (≤-trans (nm j J hj)
       (nm J (40 * J) (lb-m≤k·m J 40 (lb-1≤ 39)))))
  B : (suc t ^ 20) ^ J ≤ n ^ J
  B = ≤-trans (≤-reflexive (^-*-assoc (suc t) 20 J))
      (≤-trans (lb-pow-mono (20 * J) (40 * J) (s≤s z≤n)
               (≤-trans (lb-m≤k·m (20 * J) 2 (lb-1≤ 1))
               (≤-reflexive (solve 1 (λ j′ → con 2 :* (con 20 :* j′) := con 40 :* j′)
                                refl J))))
      (≤-trans h (nm j J hj)))
  t20 : suc t ^ 20 ≤ n
  t20 = lb-pow-cancel≤ J (suc t ^ 20) n hJ B

-- 规模: t^(40J) ≤ n^J、W^(120·N0) ≤ n、m ≤ t·n·W^(3·N0) ⟹ m^20 ≤ n^21
--   （t^20 与 W^(60·N0) 各占 n 的一半额度: 合起来取 (2J) 次幂后 ≤ n^(2J)）
lb-size : ∀ t n W m N0 J → 1 ≤ J → 1 ≤ n → W ^ (120 * N0) ≤ n →
  t ^ (40 * J) ≤ n ^ J → m ≤ t * n * W ^ (3 * N0) → m ^ 20 ≤ n ^ 21
lb-size t n W m N0 J hJ hn hWn h hm =
  ≤-trans (lb-pow≤ 20 hm)
  (≤-trans (≤-reflexive e2)
  (*-monoˡ-≤ (n ^ 20) Xn))
  where
  X : ℕ
  X = t ^ 20 * W ^ (60 * N0)
  eX : X ^ (2 * J) ≡ t ^ (40 * J) * ((W ^ (120 * N0)) ^ J)
  eX = trans (^-distribʳ-* (2 * J) (t ^ 20) (W ^ (60 * N0)))
       (trans (cong₂ _*_ (^-*-assoc t 20 (2 * J)) (^-*-assoc W (60 * N0) (2 * J)))
       (trans (cong₂ _*_ (cong (t ^_) (solve 1 (λ j′ → con 20 :* (con 2 :* j′) := con 40 :* j′)
                                          refl J))
                         (cong (W ^_) (solve 2 (λ n′ j′ → con 60 :* n′ :* (con 2 :* j′)
                                                    := con 120 :* n′ :* j′) refl N0 J)))
       (cong (λ z → t ^ (40 * J) * z) (sym (^-*-assoc W (120 * N0) J)))))
  eN : n ^ J * n ^ J ≡ n ^ (2 * J)
  eN = trans (sym (^-distribˡ-+-* n J J))
       (cong (n ^_) (solve 1 (λ j′ → j′ :+ j′ := con 2 :* j′) refl J))
  h2J : 1 ≤ 2 * J
  h2J = *-mono-≤ (lb-1≤ 1) hJ
  Xn : X ≤ n
  Xn = lb-pow-cancel≤ (2 * J) X n h2J
       (≤-trans (≤-reflexive eX)
       (≤-trans (*-mono-≤ h (lb-pow≤ J hWn)) (≤-reflexive eN)))
  e2 : (t * n * W ^ (3 * N0)) ^ 20 ≡ X * n ^ 20
  e2 = trans (^-distribʳ-* 20 (t * n) (W ^ (3 * N0)))
       (trans (cong₂ _*_ (^-distribʳ-* 20 t n) (^-*-assoc W (3 * N0) 20))
       (trans (cong (λ z → t ^ 20 * n ^ 20 * z)
                    (cong (W ^_) (solve 1 (λ n′ → con 3 :* n′ :* con 20 := con 60 :* n′)
                                     refl N0)))
       (solve 3 (λ t′ n′ w′ → (t′ :* n′) :* w′ := (t′ :* w′) :* n′)
       refl (t ^ 20) (n ^ 20) (W ^ (60 * N0)))))

--------------------------------------------------------------------------------
-- §4. 迭代: 压缩 J 步, 每步规模多衰减一个 W^rn
--------------------------------------------------------------------------------

-- 第 j 步的状态: 副本数 t、规模 m; t^(40J) ≤ n^j; m·W^(j·rn) ≤ t·n·W^(3·N0)
lb-Inv : (Q : ℕ → ℕ → Set) (W rn N0 J n j : ℕ) → Set
lb-Inv Q W rn N0 J n j =
  Σ ℕ (λ t → Σ ℕ (λ m → (1 ≤ t) × (Q t m) × (t ^ (40 * J) ≤ n ^ j)
                          × (m * W ^ (j * rn) ≤ t * n * W ^ (3 * N0))))

-- 压缩在该宽度上的形态（u、v 已取成 W 的幂, D 已取成 40J）
lb-CompAt : (Q : ℕ → ℕ → Set) (W half rn J n : ℕ) → Set
lb-CompAt Q W half rn J n =
  ∀ t m → 1 ≤ t → Q t m → m ^ 20 ≤ n ^ 21 →
  Σ ℕ (λ d → Σ ℕ (λ m′ → (1 ≤ d) × (d ^ (40 * J) ≤ n) × Q (t * d) m′
                          × (m′ * (W ^ (2 * rn))
                             ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn))))))

lb-iter : ∀ (Q : ℕ → ℕ → Set) W half rn N0 J n →
  6 ≤ W → 1 ≤ rn → rn + 1 ≤ half → 1 ≤ J → 1 ≤ n → W ^ (120 * N0) ≤ n →
  (∀ t m → 1 ≤ t → t ≤ n → Q t m → t * n * (W ^ (2 * half)) < 3 * m) →
  lb-CompAt Q W half rn J n →
  Σ ℕ (λ m₀ → Q 1 m₀ × m₀ ≤ 1 * n * W ^ (3 * N0)) →
  ∀ j → j ≤ J → lb-Inv Q W rn N0 J n j
lb-iter Q W half rn N0 J n hW hrn hh hJ hn hgrow hmany hcomp hseed zero _ =
  1 , (m₀ , (s≤s z≤n) , qm0 , copy0 , base)
  where
  m₀ : ℕ
  m₀ = proj₁ hseed
  qm0 : Q 1 m₀
  qm0 = proj₁ (proj₂ hseed)
  sz0 : m₀ ≤ 1 * n * W ^ (3 * N0)
  sz0 = proj₂ (proj₂ hseed)
  copy0 : 1 ^ (40 * J) ≤ n ^ zero
  copy0 = ≤-reflexive (lb-pow-one (40 * J))
  base : m₀ * 1 ≤ 1 * n * W ^ (3 * N0)
  base = ≤-trans (≤-reflexive (*-identityʳ m₀)) sz0
lb-iter Q W half rn N0 J n hW hrn hh hJ hn hgrow hmany hcomp hseed (suc j) hj =
  (t * d) , (m′ , (td1 , qtdm′ , copy′ , size′))
  where
  ij : j ≤ J
  ij = ≤-trans (m≤n⇒m≤1+n (≤-refl {j})) hj
  ih : lb-Inv Q W rn N0 J n j
  ih = lb-iter Q W half rn N0 J n hW hrn hh hJ hn hgrow hmany hcomp hseed j ij
  t : ℕ
  t = proj₁ ih
  m : ℕ
  m = proj₁ (proj₂ ih)
  t1 : 1 ≤ t
  t1 = proj₁ (proj₂ (proj₂ ih))
  qtm : Q t m
  qtm = proj₁ (proj₂ (proj₂ (proj₂ ih)))
  copyj : t ^ (40 * J) ≤ n ^ j
  copyj = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ih))))
  sizej : m * W ^ (j * rn) ≤ t * n * W ^ (3 * N0)
  sizej = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ih))))
  tn : t ≤ n
  tn = proj₁ (lb-copy J j n t hJ ij hn copyj)
  h1W : 1 ≤ W
  h1W = ≤-trans (s≤s z≤n) hW
  mbare : m ≤ t * n * W ^ (3 * N0)
  mbare = ≤-trans (lb-m≤m·k m (W ^ (j * rn)) (lb-pow1 (j * rn) h1W)) sizej
  sz : m ^ 20 ≤ n ^ 21
  sz = lb-size t n W m N0 J hJ hn hgrow
       (≤-trans copyj (lb-pow-mono j J hn ij)) mbare
  c : Σ ℕ (λ d → Σ ℕ (λ m′ → (1 ≤ d) × (d ^ (40 * J) ≤ n) × Q (t * d) m′
                               × (m′ * (W ^ (2 * rn)) ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn))))))
  c = hcomp t m t1 qtm sz
  d : ℕ
  d = proj₁ c
  m′ : ℕ
  m′ = proj₁ (proj₂ c)
  X2 : (1 ≤ d) × ((d ^ (40 * J) ≤ n) × (Q (t * d) m′ × (m′ * (W ^ (2 * rn)) ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn))))))
  X2 = proj₂ (proj₂ c)
  X3 : (d ^ (40 * J) ≤ n) × (Q (t * d) m′ × (m′ * (W ^ (2 * rn)) ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn)))))
  X3 = proj₂ X2
  X4 : Q (t * d) m′ × (m′ * (W ^ (2 * rn)) ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn))))
  X4 = proj₂ X3
  d1 : 1 ≤ d
  d1 = proj₁ X2
  dcopy : d ^ (40 * J) ≤ n
  dcopy = proj₁ X3
  qtdm′ : Q (t * d) m′
  qtdm′ = proj₁ X4
  cb : (m′ * (W ^ (2 * rn)) ≤ d * (m + t * n * (W ^ half) * (W ^ (2 * rn))))
  cb = proj₂ X4
  td1 : 1 ≤ t * d
  td1 = ≤-trans t1 (lb-m≤m·k t d d1)
  copy′ : (t * d) ^ (40 * J) ≤ n ^ suc j
  copy′ = ≤-trans (≤-reflexive (^-distribʳ-* (40 * J) t d))
           (≤-trans (*-mono-≤ copyj dcopy)
           (≤-reflexive (trans (cong (λ z → n ^ j * z) (sym (*-identityʳ n)))
           (trans (sym (^-distribˡ-+-* n j 1))
                  (cong (n ^_) (lb-add1 j))))))
  step : m′ * (W ^ rn) ≤ d * m
  step = lb-step W half rn n t m d m′ hW hrn hh (hmany t m t1 tn qtm) cb
  eA : m′ * W ^ (suc j * rn) ≡ m′ * (W ^ rn) * W ^ (j * rn)
  eA = trans (cong (λ z → m′ * z) (^-distribˡ-+-* W rn (j * rn)))
           (sym (*-assoc m′ (W ^ rn) (W ^ (j * rn))))
  size′ : m′ * W ^ (suc j * rn) ≤ t * d * n * W ^ (3 * N0)
  size′ = ≤-trans (≤-reflexive eA)
           (≤-trans (*-monoˡ-≤ (W ^ (j * rn)) step)
           (≤-trans (≤-reflexive (*-assoc d m (W ^ (j * rn))))
           (≤-trans (*-monoʳ-≤ d sizej)
           (≤-reflexive (solve 4 (λ d′ t′ n′ w′ → d′ :* (t′ :* n′ :* w′)
                                             := t′ :* d′ :* n′ :* w′)
                                refl d t n (W ^ (3 * N0)))))))

--------------------------------------------------------------------------------
-- §5. 「在子序列 w = W^N0 上」的转换引理
--------------------------------------------------------------------------------

-- 六个阈值都在同一个 W 之内
lb-S6 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
lb-S6 a b c d e f = a + (b + (c + (d + (e + f))))

lb-sum6 : ∀ a b c d e f →
  (a ≤ lb-S6 a b c d e f) × (b ≤ lb-S6 a b c d e f) × (c ≤ lb-S6 a b c d e f) ×
  (d ≤ lb-S6 a b c d e f) × (e ≤ lb-S6 a b c d e f) × (f ≤ lb-S6 a b c d e f)
lb-sum6 a b c d e f =
  (m≤m+n a (b + (c + (d + (e + f))))) ,
  (≤-trans (m≤m+n b (c + (d + (e + f))))
           (m≤n+m (b + (c + (d + (e + f)))) a)) ,
  (≤-trans (m≤m+n c (d + (e + f)))
           (≤-trans (m≤n+m (c + (d + (e + f))) b)
                    (m≤n+m (b + (c + (d + (e + f)))) a))) ,
  (≤-trans (m≤m+n d (e + f))
           (≤-trans (m≤n+m (d + (e + f)) c)
           (≤-trans (m≤n+m (c + (d + (e + f))) b)
                    (m≤n+m (b + (c + (d + (e + f)))) a)))) ,
  (≤-trans (m≤m+n e f)
           (≤-trans (m≤n+m (e + f) d)
           (≤-trans (m≤n+m (d + (e + f)) c)
           (≤-trans (m≤n+m (c + (d + (e + f))) b)
                    (m≤n+m (b + (c + (d + (e + f)))) a))))) ,
  (≤-trans (m≤n+m f e)
           (≤-trans (m≤n+m (e + f) d)
           (≤-trans (m≤n+m (d + (e + f)) c)
           (≤-trans (m≤n+m (c + (d + (e + f))) b)
                    (m≤n+m (b + (c + (d + (e + f)))) a)))))

-- 种子在该宽度上: m₀·c₂ ≤ c₁·(n·w²)、c₁ ≤ W、w = W^N0（N0 ≥ 1）
--   ⟹ m₀ ≤ n·W^(3·N0)   （c₁ ≤ w; w·w·w = W^(3·N0)）
lb-seed-at : ∀ c₁ c₂ W N0 n m₀ w → 1 ≤ c₂ → 1 ≤ W → 1 ≤ N0 → c₁ ≤ W →
  w ≡ W ^ N0 → m₀ * c₂ ≤ c₁ * (n * (w * w)) → m₀ ≤ 1 * n * W ^ (3 * N0)
lb-seed-at c₁ c₂ W N0 n m₀ w h1c₂ h1W h1N0 hc₁ ew h =
  ≤-trans (lb-m≤m·k m₀ c₂ h1c₂)
  (≤-trans h
  (≤-trans (*-monoˡ-≤ (n * (w * w)) hc₁w)
  (≤-reflexive (subst (λ z → z * (n * (z * z)) ≡ 1 * n * W ^ (3 * N0))
                  (sym ew) eS′))))
  where
  hc₁w : c₁ ≤ w
  hc₁w = ≤-trans hc₁ (≤-trans (lb-pow-ge N0 h1W h1N0) (≤-reflexive (sym ew)))
  eS′ : W ^ N0 * (n * (W ^ N0 * W ^ N0)) ≡ 1 * n * W ^ (3 * N0)
  eS′ = trans (cong (λ z → W ^ N0 * (n * z)) (sym (lb-pow2 W N0)))
         (trans (solve 3 (λ w′ n′ x′ → w′ :* (n′ :* x′) := con 1 :* n′ :* (w′ :* x′))
                       refl (W ^ N0) n (W ^ (2 * N0)))
         (trans (cong (λ z → 1 * n * z) (sym (^-distribˡ-+-* W N0 (2 * N0))))
                (cong (λ z → 1 * n * W ^ z)
                      (solve 1 (λ n′ → n′ :+ con 2 :* n′ := con 3 :* n′) refl N0))))

-- 硬度在该宽度上: (t·n)^q·w^p < (3m)^q、w = W^N0、S·q ≡ N0·p ⟹ t·n·W^S < 3m
--   （分数次幂的整数形式 ↔ 子序列上的整数次幂）
lb-many-at : ∀ W N0 S p q n t m w → 1 ≤ q →
  w ≡ W ^ N0 → S * q ≡ N0 * p →
  (t * n) ^ q * w ^ p < (3 * m) ^ q → t * n * W ^ S < 3 * m
lb-many-at W N0 S p q n t m w h1q ew eS h =
  lb-pow-cancel< q (t * n * W ^ S) (3 * m) h1q
  (subst (λ z → z < (3 * m) ^ q) (sym eX)
  (subst (λ z → (t * n) ^ q * z ^ p < (3 * m) ^ q) ew h))
  where
  eX : (t * n * W ^ S) ^ q ≡ (t * n) ^ q * (W ^ N0) ^ p
  eX = trans (^-distribʳ-* q (t * n) (W ^ S))
         (trans (cong ((t * n) ^ q *_) (^-*-assoc W S q))
         (trans (cong ((t * n) ^ q *_) (cong (W ^_) eS))
                (cong ((t * n) ^ q *_) (sym (^-*-assoc W N0 p)))))

-- 最后一步: J 步之后 m·W^(J·rn) ≤ t·n·W^(3·N0), 而 3·N0 + 2·half ≤ J
--   ⟹ 3m ≤ t·n·W^(2·half), 与硬度矛盾
lb-final : ∀ W half rn N0 J n t m → 6 ≤ W → 1 ≤ rn → 1 ≤ half → 1 ≤ J →
  3 * N0 + 2 * half ≤ J →
  (t * n * W ^ (2 * half) < 3 * m) →
  (m * W ^ (J * rn) ≤ t * n * W ^ (3 * N0)) → ⊥
lb-final W half rn N0 J n t m h6W h1rn h1hh h1J hJle L1 sizeJ =
  lb-<abs (<-≤-trans L1 fin)
  where
  h1W : 1 ≤ W
  h1W = ≤-trans (s≤s z≤n) h6W
  h4W : suc 3 ≤ W
  h4W = ≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) h6W
  h2hh : 1 ≤ 2 * half
  h2hh = ≤-trans h1hh (lb-m≤k·m half 2 (s≤s z≤n))
  h1Jrn : 1 ≤ J * rn
  h1Jrn = ≤-trans h1J (lb-m≤m·k J rn h1rn)
  -- suc (3·N0) ≤ 3·N0 + 2·half ≤ J ≤ J·rn ≤ 2·half + J·rn
  hlt : 3 * N0 < 2 * half + J * rn
  hlt = ≤-trans (≤-reflexive (sym (lb-add1 (3 * N0))))
         (≤-trans (+-monoʳ-≤ (3 * N0) h2hh)
         (≤-trans hJle
         (≤-trans (lb-m≤m·k J rn h1rn)
                  (m≤n+m (J * rn) (2 * half)))))
  ps : 3 * W ^ (3 * N0) ≤ W ^ (2 * half) * W ^ (J * rn)
  ps = ≤-trans (lb-pow-split W (3 * N0) (2 * half + J * rn) 3 h4W hlt)
         (≤-reflexive (^-distribˡ-+-* W (2 * half) (J * rn)))
  eA : 3 * m * W ^ (J * rn) ≡ 3 * (m * W ^ (J * rn))
  eA = solve 2 (λ m′ x′ → con 3 :* m′ :* x′ := con 3 :* (m′ :* x′)) refl m (W ^ (J * rn))
  A : 3 * m * W ^ (J * rn) ≤ 3 * (t * n * W ^ (3 * N0))
  A = ≤-trans (≤-reflexive eA) (*-monoʳ-≤ 3 sizeJ)
  eB1 : 3 * (t * n * W ^ (3 * N0)) ≡ t * n * (3 * W ^ (3 * N0))
  eB1 = solve 2 (λ a c → con 3 :* (a :* c) := a :* (con 3 :* c)) refl (t * n) (W ^ (3 * N0))
  eB2 : t * n * (W ^ (2 * half) * W ^ (J * rn)) ≡ t * n * W ^ (2 * half) * W ^ (J * rn)
  eB2 = solve 3 (λ a b c → a :* (b :* c) := a :* b :* c)
        refl (t * n) (W ^ (2 * half)) (W ^ (J * rn))
  B : 3 * (t * n * W ^ (3 * N0)) ≤ (t * n * W ^ (2 * half)) * W ^ (J * rn)
  B = ≤-trans (≤-reflexive eB1) (≤-trans (*-monoʳ-≤ (t * n) ps) (≤-reflexive eB2))
  fin : 3 * m ≤ t * n * W ^ (2 * half)
  fin = lb-cancelʳ-≤ (W ^ (J * rn)) (3 * m) (t * n * W ^ (2 * half))
        (lb-pow1 (J * rn) h1W) (≤-trans A B)

--------------------------------------------------------------------------------
-- §6. 衰减率的选取: 每步多省一个 W^rn
--   需要 1 ≤ rn、2·rn·G ≤ N0·g（u 的侧条件）、rn + 1 ≤ half（6·W^rn ≤ W^half）
--   这里 N0 = 16·q·G、half = 8·G·p; rn 取 4·g·q 与 p·G 中较小的一个
--------------------------------------------------------------------------------

lb-8≤16 : 8 ≤ 16
lb-8≤16 = lb-m≤k·m 8 2 (s≤s z≤n)

lb-2≤8 : 2 ≤ 8
lb-2≤8 = lb-m≤k·m 2 4 (s≤s z≤n)

lb-rn-e16 : ∀ g q G → 16 * q * G * g ≡ 16 * (g * q * G)
lb-rn-e16 g q G =
  solve 3 (λ g′ q′ G′ → con 16 :* q′ :* G′ :* g′ := con 16 :* (g′ :* q′ :* G′)) refl g q G

-- 2·(4·g·q)·G ≤ 16·q·G·g
lb-rn-A1 : ∀ g q G → 2 * (4 * g * q) * G ≤ 16 * q * G * g
lb-rn-A1 g q G =
  ≤-trans (≤-reflexive e1)
  (≤-trans (*-monoˡ-≤ (g * q * G) lb-8≤16) (≤-reflexive (sym (lb-rn-e16 g q G))))
  where
  e1 : 2 * (4 * g * q) * G ≡ 8 * (g * q * G)
  e1 = solve 3 (λ g′ q′ G′ → con 2 :* (con 4 :* g′ :* q′) :* G′
                        := con 8 :* (g′ :* q′ :* G′)) refl g q G

-- p·G ≤ 4·g·q ⟹ 2·(p·G)·G ≤ 8·(g·q·G)
lb-rn-A2 : ∀ g q p G → p * G ≤ 4 * g * q → 2 * (p * G) * G ≤ 8 * (g * q * G)
lb-rn-A2 g q p G hle =
  ≤-trans (≤-reflexive e1) (≤-trans (*-monoʳ-≤ (2 * G) hle) (≤-reflexive e2))
  where
  e1 : 2 * (p * G) * G ≡ 2 * G * (p * G)
  e1 = solve 2 (λ p′ G′ → con 2 :* (p′ :* G′) :* G′ := con 2 :* G′ :* (p′ :* G′)) refl p G
  e2 : 2 * G * (4 * g * q) ≡ 8 * (g * q * G)
  e2 = solve 3 (λ g′ q′ G′ → con 2 :* G′ :* (con 4 :* g′ :* q′)
                       := con 8 :* (g′ :* q′ :* G′)) refl g q G

-- 8·(g·q·G) ≤ 16·q·G·g
lb-rn-A3 : ∀ g q G → 8 * (g * q * G) ≤ 16 * q * G * g
lb-rn-A3 g q G =
  ≤-trans (*-monoˡ-≤ (g * q * G) lb-8≤16) (≤-reflexive (sym (lb-rn-e16 g q G)))

-- p·G + 1 ≤ 8·G·p
lb-rn-B : ∀ G p → 1 ≤ p → 1 ≤ G → p * G + 1 ≤ 8 * G * p
lb-rn-B G p hp hG =
  ≤-trans (+-monoʳ-≤ (p * G) (*-mono-≤ hG hp))
  (≤-trans (≤-reflexive eB)
  (≤-trans (*-monoˡ-≤ (G * p) lb-2≤8) (≤-reflexive eB′)))
  where
  eB : p * G + G * p ≡ 2 * (G * p)
  eB = solve 2 (λ p′ G′ → p′ :* G′ :+ G′ :* p′ := con 2 :* (G′ :* p′)) refl p G
  eB′ : 8 * (G * p) ≡ 8 * G * p
  eB′ = solve 2 (λ G′ p′ → con 8 :* (G′ :* p′) := con 8 :* G′ :* p′) refl G p

lb-rn-pkg : ∀ q g p G → 1 ≤ q → 1 ≤ g → 1 ≤ p → 1 ≤ G →
  Σ ℕ (λ rn → (1 ≤ rn) × (2 * rn * G ≤ 16 * q * G * g) × (rn + 1 ≤ 8 * G * p))
lb-rn-pkg q g p G hq hg hp hG with 4 * g * q ≤? p * G
... | yes le =
  (4 * g * q) ,
  (h1 ,
   lb-rn-A1 g q G ,
   ≤-trans (+-monoˡ-≤ 1 le) (lb-rn-B G p hp hG))
  where
  h1 : 1 ≤ 4 * g * q
  h1 = *-mono-≤ (*-mono-≤ (lb-1≤ 3) hg) hq
... | no nle =
  (p * G) ,
  (*-mono-≤ hp hG ,
   ≤-trans (lb-rn-A2 g q p G (<⇒≤ (≰⇒> nle))) (lb-rn-A3 g q G) ,
   lb-rn-B G p hp hG)

-- 压缩在该宽度上: u、v 取成 W 的幂, D 取成 40J
--   u = W^(2·rn):  u^G = W^(2·rn·G) ≤ W^(N0·g) = w^g ≤ h^g
--   v = W^(8·G·p): h^p ≤ (w·w)^p = (W^(2·N0))^p = W^(8·G·p·4q) = v^(4q)
lb-comp-at : ∀ (P : ℕ → ℕ → ℕ → Set) W N0 rn J n h g G p q w →
  1 ≤ W → 1 ≤ rn → 2 * rn * G ≤ N0 * g → 2 * N0 * p ≡ 8 * G * p * (4 * q) →
  w ≡ W ^ N0 → w ≤ h → h ≤ w * w →
  (∀ t m → 1 ≤ t → P w t m → m ^ 20 ≤ n ^ 21 →
   Σ ℕ (λ d → Σ ℕ (λ m′ → (1 ≤ d) × (d ^ (40 * J) ≤ n) × P w (t * d) m′
     × (∀ u v → 1 ≤ u → 1 ≤ v → u ^ G ≤ h ^ g → h ^ p ≤ v ^ (4 * q)
            → m′ * u ≤ d * (m + t * n * v * u))))) →
  lb-CompAt (λ t m → P w t m) W (8 * G * p) rn J n
lb-comp-at P W N0 rn J n h g G p q w h1W h1rn hrnG eS ew hlo hhi hc t m h1t qtm sz =
  (d , m′ , (d1 , dJ , qtdm′ , cb′))
  where
  c = hc t m h1t qtm sz
  d : ℕ
  d = proj₁ c
  m′ : ℕ
  m′ = proj₁ (proj₂ c)
  X2 = proj₂ (proj₂ c)
  X3 = proj₂ X2
  X4 = proj₂ X3
  d1 : 1 ≤ d
  d1 = proj₁ X2
  dJ : d ^ (40 * J) ≤ n
  dJ = proj₁ X3
  qtdm′ : P w (t * d) m′
  qtdm′ = proj₁ X4
  alluv : ∀ u v → 1 ≤ u → 1 ≤ v → u ^ G ≤ h ^ g → h ^ p ≤ v ^ (4 * q) →
          m′ * u ≤ d * (m + t * n * v * u)
  alluv = proj₂ X4
  Sc1 : (W ^ (2 * rn)) ^ G ≤ h ^ g
  Sc1 = ≤-trans (≤-reflexive (^-*-assoc W (2 * rn) G))
         (≤-trans (lb-pow-mono (2 * rn * G) (N0 * g) h1W hrnG)
         (≤-trans (≤-reflexive (sym (^-*-assoc W N0 g)))
         (≤-trans (≤-reflexive (cong (λ z → z ^ g) (sym ew))) (lb-pow≤ g hlo))))
  ew1 : w * w ≡ W ^ (2 * N0)
  ew1 = trans (cong (λ z → z * z) ew) (sym (lb-pow2 W N0))
  ew2 : (w * w) ^ p ≡ (W ^ (2 * N0)) ^ p
  ew2 = cong (λ z → z ^ p) ew1
  Sc2 : h ^ p ≤ (W ^ (8 * G * p)) ^ (4 * q)
  Sc2 = ≤-trans (lb-pow≤ p hhi)
         (≤-trans (≤-reflexive ew2)
         (≤-trans (≤-reflexive (^-*-assoc W (2 * N0) p))
         (≤-trans (≤-reflexive (cong (W ^_) eS))
                  (≤-reflexive (sym (^-*-assoc W (8 * G * p) (4 * q)))))))
  cb′ : m′ * W ^ (2 * rn) ≤ d * (m + t * n * W ^ (8 * G * p) * W ^ (2 * rn))
  cb′ = alluv (W ^ (2 * rn)) (W ^ (8 * G * p))
         (lb-pow1 (2 * rn) h1W) (lb-pow1 (8 * G * p) h1W) Sc1 Sc2

--------------------------------------------------------------------------------
-- §7. 四条性质的 ℕ 表述
--------------------------------------------------------------------------------

-- 「对一切足够大的 w」
lb-Ev : (ℕ → Set) → Set
lb-Ev A = Σ ℕ (λ W₀ → ∀ w → W₀ ≤ w → A w)

-- Seed: t = 1 时有多项式开销的实现（常数 C = c₁/c₂）
--   Lean: ∃ C : ℝ, ∀ᶠ w, ∃ m, P w 1 m ∧ m ≤ C * listBits w * w²
--   Lean 陈述蕴涵本陈述（取有理数 C′ ≥ C）
lb-Seed : (P : ℕ → ℕ → ℕ → Set) (N : ℕ → ℕ) → Set
lb-Seed P N =
  Σ (ℕ × ℕ) (λ c → 1 ≤ proj₂ c ×
    lb-Ev (λ w → Σ ℕ (λ m₀ → P w 1 m₀ × (m₀ * proj₂ c ≤ proj₁ c * (N w * (w * w))))))

-- ManyList: 硬度（σ = p/q）
--   Lean: ∃ σ > 0, ∀ᶠ w, ∀ t m, 1 ≤ t → t ≤ listBits w → P w t m → t * listBits w * w ^ σ < 3 * m
--   两边取 q 次幂; Lean 陈述蕴涵本陈述（取有理数 0 < p/q ≤ σ）
lb-Many : (P : ℕ → ℕ → ℕ → Set) (N : ℕ → ℕ) → Set
lb-Many P N =
  Σ (ℕ × ℕ) (λ s → 1 ≤ proj₁ s × 1 ≤ proj₂ s ×
    lb-Ev (λ w → ∀ t m → 1 ≤ t → t ≤ N w → P w t m →
      (t * N w) ^ proj₂ s * w ^ proj₁ s < (3 * m) ^ proj₂ s))

-- 增长条件: n 快过 w 的任意幂; w ≤ h ≤ w²
lb-Grow : (N H : ℕ → ℕ) → Set
lb-Grow N H = (∀ k → lb-Ev (λ w → w ^ k ≤ N w))
            × lb-Ev (λ w → w ≤ H w) × lb-Ev (λ w → H w ≤ w * w)

-- Compression（η = e/E, γ = g/G, δ = 1/D）
--   Lean: … d ≤ listBits w ^ δ ∧ P w (t*d) m' ∧ m' ≤ d * (m * h ^ (-γ) + t * listBits w * h ^ η)
--   这里 h 的分数次幂写成「对一切满足侧条件的自然数 u、v」的形式:
--   取 u ≤ h^γ、v ≥ h^η, 两边乘 u 即 m′·u ≤ d·(m + t·n·v·u)。
--   Lean 陈述蕴涵本陈述（取有理数 g/G ≤ γ）
lb-Comp : (P : ℕ → ℕ → ℕ → Set) (N H : ℕ → ℕ) → Set
lb-Comp P N H =
  ∀ e E → 1 ≤ e → 1 ≤ E →
  Σ (ℕ × ℕ) (λ c → 1 ≤ proj₁ c × 1 ≤ proj₂ c ×
    ∀ D → 1 ≤ D →
    lb-Ev (λ w → ∀ t m → 1 ≤ t → P w t m → m ^ 20 ≤ N w ^ 21 →
      Σ ℕ (λ d → Σ ℕ (λ m′ → (1 ≤ d) × (d ^ D ≤ N w) × P w (t * d) m′
        × (∀ u v → 1 ≤ u → 1 ≤ v → u ^ proj₂ c ≤ H w ^ proj₁ c
             → H w ^ e ≤ v ^ E → m′ * u ≤ d * (m + t * N w * v * u))))))

--------------------------------------------------------------------------------
-- §8. ★ 主定理
--------------------------------------------------------------------------------

-- Seed ∧ ManyList ∧ Grow ∧ Compression ⟹ ⊥
--   证明: 取 w = W^N0（N0 = 16·q·G）, 从种子出发迭代压缩 J = 3·N0 + 16·G·p 步;
--   每步规模多衰减一个 W^rn; J 步后 3m ≤ t·n·W^(16·G·p), 与硬度矛盾。
lb-incompatible : ∀ (P : ℕ → ℕ → ℕ → Set) (N H : ℕ → ℕ) →
  lb-Grow N H → lb-Seed P N → lb-Many P N → lb-Comp P N H → ⊥
lb-incompatible P N H grow seed many comp =
  lb-final W (8 * G * p) rn (16 * q * G) (3 * (16 * q * G) + 16 * G * p) n t m
    h6W h1rn h1hh h1J hJle L1J sizeJ
  where
  -- Seed
  c : ℕ × ℕ
  c = proj₁ seed
  c₁ : ℕ
  c₁ = proj₁ c
  c₂ : ℕ
  c₂ = proj₂ c
  h1c₂ : 1 ≤ c₂
  h1c₂ = proj₁ (proj₂ seed)
  seedEv : lb-Ev (λ w → Σ ℕ (λ m₀ → P w 1 m₀ × (m₀ * c₂ ≤ c₁ * (N w * (w * w)))))
  seedEv = proj₂ (proj₂ seed)
  seedW₀ : ℕ
  seedW₀ = proj₁ seedEv
  seedPr : ∀ w → seedW₀ ≤ w → Σ ℕ (λ m₀ → P w 1 m₀ × (m₀ * c₂ ≤ c₁ * (N w * (w * w))))
  seedPr = proj₂ seedEv
  -- ManyList
  s : ℕ × ℕ
  s = proj₁ many
  p : ℕ
  p = proj₁ s
  q : ℕ
  q = proj₂ s
  hp : 1 ≤ p
  hp = proj₁ (proj₂ many)
  hq : 1 ≤ q
  hq = proj₁ (proj₂ (proj₂ many))
  manyEv : lb-Ev (λ w → ∀ t m → 1 ≤ t → t ≤ N w → P w t m →
                      (t * N w) ^ q * w ^ p < (3 * m) ^ q)
  manyEv = proj₂ (proj₂ (proj₂ many))
  manyW₀ : ℕ
  manyW₀ = proj₁ manyEv
  manyPr : ∀ w → manyW₀ ≤ w → ∀ t m → 1 ≤ t → t ≤ N w → P w t m →
           (t * N w) ^ q * w ^ p < (3 * m) ^ q
  manyPr = proj₂ manyEv
  -- Compression, 取 η = σ/4 = p/(4q)
  h4q : 1 ≤ 4 * q
  h4q = *-mono-≤ (lb-1≤ 3) hq
  cc = comp p (4 * q) hp h4q
  g : ℕ
  g = proj₁ (proj₁ cc)
  G : ℕ
  G = proj₂ (proj₁ cc)
  hg : 1 ≤ g
  hg = proj₁ (proj₂ cc)
  hG : 1 ≤ G
  hG = proj₁ (proj₂ (proj₂ cc))
  compD = proj₂ (proj₂ (proj₂ cc))
  h1N0 : 1 ≤ 16 * q * G
  h1N0 = lb-1≤· (16 * q) G (lb-1≤· 16 q (lb-1≤ 15) hq) hG
  h1J : 1 ≤ 3 * (16 * q * G) + 16 * G * p
  h1J = ≤-trans h1N0 (≤-trans (lb-m≤k·m (16 * q * G) 3 (lb-1≤ 2))
         (m≤m+n (3 * (16 * q * G)) (16 * G * p)))
  hDJ : 1 ≤ 40 * (3 * (16 * q * G) + 16 * G * p)
  hDJ = ≤-trans h1J
         (lb-m≤k·m (3 * (16 * q * G) + 16 * G * p) 40 (lb-1≤ 39))
  compEv = compD (40 * (3 * (16 * q * G) + 16 * G * p)) hDJ
  compW₀ : ℕ
  compW₀ = proj₁ compEv
  compPr = proj₂ compEv
  -- 增长条件
  growEv : lb-Ev (λ w → w ^ (120 * (16 * q * G)) ≤ N w)
  growEv = proj₁ grow (120 * (16 * q * G))
  growW₀ : ℕ
  growW₀ = proj₁ growEv
  growPr : ∀ w → growW₀ ≤ w → w ^ (120 * (16 * q * G)) ≤ N w
  growPr = proj₂ growEv
  loEv : lb-Ev (λ w → w ≤ H w)
  loEv = proj₁ (proj₂ grow)
  loW₀ : ℕ
  loW₀ = proj₁ loEv
  loPr : ∀ w → loW₀ ≤ w → w ≤ H w
  loPr = proj₂ loEv
  hiEv : lb-Ev (λ w → H w ≤ w * w)
  hiEv = proj₂ (proj₂ grow)
  hiW₀ : ℕ
  hiW₀ = proj₁ hiEv
  hiPr : ∀ w → hiW₀ ≤ w → H w ≤ w * w
  hiPr = proj₂ hiEv
  -- 衰减率
  pkg = lb-rn-pkg q g p G hq hg hp hG
  rn : ℕ
  rn = proj₁ pkg
  h1rn : 1 ≤ rn
  h1rn = proj₁ (proj₂ pkg)
  hrnG : 2 * rn * G ≤ 16 * q * G * g
  hrnG = proj₁ (proj₂ (proj₂ pkg))
  hhh : rn + 1 ≤ 8 * G * p
  hhh = proj₂ (proj₂ (proj₂ pkg))
  h1hh : 1 ≤ 8 * G * p
  h1hh = lb-1≤· (8 * G) p (lb-1≤· 8 G (lb-1≤ 7) hG) hp
  eJ : 3 * (16 * q * G) + 2 * (8 * G * p) ≡ 3 * (16 * q * G) + 16 * G * p
  eJ0 : 2 * (8 * G * p) ≡ 16 * G * p
  eJ0 = solve 2 (λ G′ p′ → con 2 :* ((con 8 :* G′) :* p′) := (con 16 :* G′) :* p′)
        refl G p
  eJ = cong (λ z → 3 * (16 * q * G) + z) eJ0
  hJle : 3 * (16 * q * G) + 2 * (8 * G * p) ≤ 3 * (16 * q * G) + 16 * G * p
  hJle = ≤-reflexive eJ
  -- 取足够大的 W, 并令 w = W^(16·q·G)
  rest : ℕ
  rest = lb-S6 seedW₀ manyW₀ compW₀ growW₀ loW₀ hiW₀
  six = lb-sum6 seedW₀ manyW₀ compW₀ growW₀ loW₀ hiW₀
  W : ℕ
  W = rest + c₁ + 6
  h6W : 6 ≤ W
  h6W = m≤n+m 6 (rest + c₁)
  h1W : 1 ≤ W
  h1W = ≤-trans (s≤s z≤n) h6W
  hc₁ : c₁ ≤ W
  hc₁ = ≤-trans (m≤n+m c₁ rest) (m≤m+n (rest + c₁) 6)
  inW : ∀ W₀ → W₀ ≤ rest → W₀ ≤ W
  inW W₀ hX = ≤-trans (≤-trans hX (m≤m+n rest c₁)) (m≤m+n (rest + c₁) 6)
  w : ℕ
  w = W ^ (16 * q * G)
  -- nightly 坑: 类型里裸 λ 立即应用会留下未解元变量, 故具名
  Qw : ℕ → ℕ → Set
  Qw t m = P w t m
  atW : ∀ W₀ → W₀ ≤ W → W₀ ≤ w
  atW W₀ hX = ≤-trans hX (lb-pow-ge (16 * q * G) h1W h1N0)
  n : ℕ
  n = N w
  h : ℕ
  h = H w
  -- 各条性质在 w 处
  seedw = seedPr w (atW seedW₀ (inW seedW₀ (proj₁ six)))
  m₀ : ℕ
  m₀ = proj₁ seedw
  seed′ : Σ ℕ (λ m′ → Qw 1 m′ × m′ ≤ 1 * n * W ^ (3 * (16 * q * G)))
  seed′ = m₀ , (proj₁ (proj₂ seedw) ,
          lb-seed-at c₁ c₂ W (16 * q * G) n m₀ w h1c₂ h1W h1N0 hc₁ refl
          (proj₂ (proj₂ seedw)))
  manyw : ∀ t m → 1 ≤ t → t ≤ n → P w t m → (t * n) ^ q * w ^ p < (3 * m) ^ q
  manyw = manyPr w (atW manyW₀ (inW manyW₀ (proj₁ (proj₂ six))))
  eS : 16 * G * p * q ≡ 16 * q * G * p
  eS = solve 3 (λ G′ p′ q′ → con 16 :* G′ :* p′ :* q′ := con 16 :* q′ :* G′ :* p′)
       refl G p q
  L1 : ∀ t m → 1 ≤ t → t ≤ n → Qw t m →
       t * n * W ^ (16 * G * p) < 3 * m
  L1 t m h1t tn qtm =
    lb-many-at W (16 * q * G) (16 * G * p) p q n t m w hq refl eS
    (manyw t m h1t tn qtm)
  -- 指数 16·G·p 与 2·(8·G·p) 只经 eJ0 相等, 显式搬运
  L1′ : ∀ t m → 1 ≤ t → t ≤ n → Qw t m →
        t * n * W ^ (2 * (8 * G * p)) < 3 * m
  L1′ t m h1t tn qtm =
    subst (λ z → t * n * W ^ z < 3 * m) (sym eJ0) (L1 t m h1t tn qtm)
  eS2 : 2 * (16 * q * G) * p ≡ 8 * G * p * (4 * q)
  eS2 = solve 3 (λ q′ G′ p′ → con 2 :* (con 16 :* q′ :* G′) :* p′
                        := con 8 :* G′ :* p′ :* (con 4 :* q′)) refl q G p
  hlo : w ≤ h
  hlo = loPr w (atW loW₀ (inW loW₀ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ six)))))))
  hhi : h ≤ w * w
  hhi = hiPr w (atW hiW₀ (inW hiW₀ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ six)))))))
  compw : ∀ t m → 1 ≤ t → P w t m → m ^ 20 ≤ n ^ 21 →
          Σ ℕ (λ d → Σ ℕ (λ m′ → (1 ≤ d) × (d ^ (40 * (3 * (16 * q * G) + 16 * G * p)) ≤ n)
            × P w (t * d) m′
            × (∀ u v → 1 ≤ u → 1 ≤ v → u ^ G ≤ h ^ g → h ^ p ≤ v ^ (4 * q)
                   → m′ * u ≤ d * (m + t * n * v * u))))
  compw = compPr w (atW compW₀ (inW compW₀ (proj₁ (proj₂ (proj₂ six)))))
  compAt : lb-CompAt Qw W (8 * G * p) rn
             (3 * (16 * q * G) + 16 * G * p) n
  compAt = lb-comp-at P W (16 * q * G) rn (3 * (16 * q * G) + 16 * G * p) n
             h g G p q w h1W h1rn hrnG eS2 refl hlo hhi compw
  h1w : 1 ≤ w
  h1w = lb-pow1 (16 * q * G) h1W
  Wat : W ≤ w
  Wat = lb-pow-ge (16 * q * G) h1W h1N0
  groww : w ^ (120 * (16 * q * G)) ≤ n
  groww = growPr w (atW growW₀ (inW growW₀ (proj₁ (proj₂ (proj₂ (proj₂ six))))))
  -- 迭代引理要的是 W 的幂: W^(120·N0) ≤ w^(120·N0) ≤ n
  growW : W ^ (120 * (16 * q * G)) ≤ n
  growW = ≤-trans (lb-pow≤ (120 * (16 * q * G)) Wat) groww
  h1n : 1 ≤ n
  h1n = ≤-trans (lb-pow1 (120 * (16 * q * G)) h1W) growW
  -- 迭代 J 步
  iter : lb-Inv Qw W rn (16 * q * G)
           (3 * (16 * q * G) + 16 * G * p) n
           (3 * (16 * q * G) + 16 * G * p)
  iter = lb-iter Qw W (8 * G * p) rn (16 * q * G)
           (3 * (16 * q * G) + 16 * G * p) n
           h6W h1rn hhh h1J h1n growW L1′ compAt seed′
           (3 * (16 * q * G) + 16 * G * p) (≤-refl)
  t : ℕ
  t = proj₁ iter
  m : ℕ
  m = proj₁ (proj₂ iter)
  qtm : Qw t m
  qtm = proj₁ (proj₂ (proj₂ (proj₂ iter)))
  copyJ : t ^ (40 * (3 * (16 * q * G) + 16 * G * p))
          ≤ n ^ (3 * (16 * q * G) + 16 * G * p)
  copyJ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ iter))))
  sizeJ : m * W ^ ((3 * (16 * q * G) + 16 * G * p) * rn)
          ≤ t * n * W ^ (3 * (16 * q * G))
  sizeJ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ iter))))
  tn : t ≤ n
  tn = proj₁ (lb-copy (3 * (16 * q * G) + 16 * G * p)
             (3 * (16 * q * G) + 16 * G * p) n t h1J (≤-refl) h1n copyJ)
  L1J : t * n * W ^ (2 * (8 * G * p)) < 3 * m
  L1J = L1′ t m (proj₁ (proj₂ (proj₂ iter))) tn qtm

--------------------------------------------------------------------------------
-- §9. 增长引理: 2^(k+4) ≤ w ⟹ w ^ k ≤ 2 ^ w
--------------------------------------------------------------------------------

-- n ≤ 2 ^ n
lb-n≤2ⁿ : ∀ n → n ≤ 2 ^ n
lb-n≤2ⁿ zero = z≤n
lb-n≤2ⁿ (suc n) = ≤-trans (≤-trans (s≤s (lb-n≤2ⁿ n))
                     (≤-trans (≤-reflexive (sym (lb-add1 (2 ^ n))))
                       (+-monoʳ-≤ (2 ^ n) (lb-pow1 n (lb-1≤ 1)))))
                   (≤-reflexive e)
  where
  e : 2 ^ n + 2 ^ n ≡ 2 ^ suc n
  e = cong (λ z → 2 ^ n + z) (sym (+-identityʳ (2 ^ n)))

-- a ≥ 1 ⟹ a + 1 ≥ 1 之类的小件
lb-1≤n+ : ∀ a n → 1 ≤ a → 1 ≤ n + a
lb-1≤n+ a n h = ≤-trans h (m≤n+m a n)

-- 2·(k+3) ≤ 2^(k+3)
lb-2k₊6 : ∀ k → 2 * (k + 3) ≤ 2 ^ (k + 3)
lb-2k₊6 zero = m≤n+m 6 2
lb-2k₊6 (suc k) = ≤-trans (≤-reflexive eS)
                   (≤-trans (+-mono-≤ (lb-2k₊6 k) h2) (≤-reflexive e3))
  where
  eS : 2 * (suc k + 3) ≡ 2 * (k + 3) + 2
  eS = solve 1 (λ k′ → con 2 :* ((con 1 :+ k′) :+ con 3)
                        := (con 2 :* (k′ :+ con 3)) :+ con 2) refl k
  h2 : 2 ≤ 2 ^ (k + 3)
  h2 = lb-pow-mono 1 (k + 3) (lb-1≤ 1) (lb-1≤n+ 3 k (m≤n+m 1 2))
  e3 : 2 ^ (k + 3) + 2 ^ (k + 3) ≡ 2 ^ (suc k + 3)
  e3 = cong (λ z → 2 ^ (k + 3) + z) (sym (+-identityʳ (2 ^ (k + 3))))

-- x + x ≡ 2·x
lb-double : ∀ x → x + x ≡ 2 * x
lb-double x = cong (λ z → x + z) (sym (+-identityʳ x))

-- 线性·常数 ≤ 指数: c² ≤ 2^c、c ≤ 2^c ⟹ (c + d)·c ≤ 2^(c + d)
lb-lin-exp : ∀ c d → c * c ≤ 2 ^ c → c ≤ 2 ^ c → (c + d) * c ≤ 2 ^ (c + d)
lb-lin-exp c zero h1 h2 =
  ≤-trans (≤-reflexive (cong (λ z → z * c) (+-identityʳ c)))
    (≤-trans h1 (≤-reflexive (sym e)))
  where
  e : 2 ^ (c + zero) ≡ 2 ^ c
  e = trans (^-distribˡ-+-* 2 c zero) (*-identityʳ (2 ^ c))
lb-lin-exp c (suc d) h1 h2 =
  ≤-trans (≤-reflexive e1) (≤-trans (+-mono-≤ hc (lb-lin-exp c d h1 h2))
    (≤-reflexive e2))
  where
  e1 : (c + suc d) * c ≡ c + (c + d) * c
  e1 = cong (λ z → z * c) (+-suc c d)
  hc : c ≤ 2 ^ (c + d)
  hc = ≤-trans h2 (lb-pow-mono c (c + d) (lb-1≤ 1) (m≤m+n c d))
  e : 2 * 2 ^ (c + d) ≡ 2 ^ (c + suc d)
  e = trans refl (cong (λ z → 2 ^ z) (sym (+-suc c d)))
  e2 : 2 ^ (c + d) + 2 ^ (c + d) ≡ 2 ^ (c + suc d)
  e2 = trans (lb-double (2 ^ (c + d))) e

-- 取半: 2·half w ≤ w ≤ 2·half w + 1
lb-half : ℕ → ℕ
lb-half zero = zero
lb-half (suc zero) = zero
lb-half (suc (suc w)) = suc (lb-half w)

-- 2·(a+1) ≡ (a+1) + (a+1) ≡ 2·a + 2
lb-2suc : ∀ a → 2 * suc a ≡ suc (suc (2 * a))
lb-2suc a = solve 1 (λ a′ → con 2 :* (con 1 :+ a′)
                              := con 1 :+ (con 1 :+ (con 2 :* a′))) refl a

lb-2suc′ : ∀ a → 2 * suc a ≡ 2 * a + 2
lb-2suc′ a = solve 1 (λ a′ → con 2 :* (con 1 :+ a′) := (con 2 :* a′) :+ con 2) refl a

lb-half-lo : ∀ w → 2 * lb-half w ≤ w
lb-half-lo zero = z≤n
lb-half-lo (suc zero) = z≤n
lb-half-lo (suc (suc w)) =
  ≤-trans (≤-reflexive (lb-2suc (lb-half w))) (s≤s (s≤s (lb-half-lo w)))

lb-half-hi : ∀ w → w ≤ 2 * lb-half w + 1
lb-half-hi zero = z≤n
lb-half-hi (suc zero) = ≤-refl
lb-half-hi (suc (suc w)) =
  ≤-trans (s≤s (s≤s (lb-half-hi w))) (≤-reflexive (sym e))
  where
  e : 2 * suc (lb-half w) + 1 ≡ suc (suc (2 * lb-half w + 1))
  e = cong (λ z → z + 1) (lb-2suc (lb-half w))

-- 左消去: k + a ≤ k + b ⟹ a ≤ b
lb-cancelˡ+-≤ : ∀ k a b → k + a ≤ k + b → a ≤ b
lb-cancelˡ+-≤ zero a b h = h
lb-cancelˡ+-≤ (suc k) a b (s≤s h) = lb-cancelˡ+-≤ k a b h

-- 2 ≤ 1 荒谬
lb-2≤1 : 2 ≤ 1 → ⊥
lb-2≤1 (s≤s ())

-- 2x ≤ 2a + 1 ⟹ x ≤ a（整数取半的单调性）
--   反证: 若 a + 1 ≤ x, 则 2a + 2 = 2(a+1) ≤ 2x ≤ 2a + 1
lb-2x≤2a+1 : ∀ a x → 2 * x ≤ 2 * a + 1 → x ≤ a
lb-2x≤2a+1 a x h = ≮⇒≥ nle
  where
  nle : ¬ (a < x)
  nle c = lb-2≤1 (lb-cancelˡ+-≤ (2 * a) 2 1 step)
    where
    stepC : 2 * suc a ≤ 2 * a + 1
    stepC = ≤-trans (*-monoʳ-≤ 2 c) h
    step : 2 * a + 2 ≤ 2 * a + 1
    step = subst (λ z → z ≤ 2 * a + 1) (lb-2suc′ a) stepC

-- a ≤ b ⟹ b ≡ a + o
lb-≤-diff : ∀ a b → a ≤ b → Σ ℕ (λ o → b ≡ a + o)
lb-≤-diff zero b z≤n = b , refl
lb-≤-diff (suc a) (suc b) (s≤s h) with lb-≤-diff a b h
... | o , e = o , cong suc e

-- ★ 增长引理
--   归纳于 k。a := half w; 由 2·2^(k+4) ≤ w ≤ 2a+1 得 2^(k+4) ≤ a。
--   w ≤ 2(a+1) ⟹ w^k ≤ 2^k·(a+1)^k ≤ 2^k·2^(a+1)  （归纳假设在 a+1 处）
--   w^(k+1) ≤ 2^(k+1)·2^a·(2a+1) ≤ 2^a·(a·2^(k+3)) ≤ 2^a·2^a ≤ 2^w
lb-wk≤2w : ∀ k w → 2 ^ (k + 4) ≤ w → w ^ k ≤ 2 ^ w
lb-wk≤2w zero w h = lb-pow1 w (lb-1≤ 1)
lb-wk≤2w (suc k) w hw = ≤-trans E2 (≤-trans E3 E4)
  where
  a = lb-half w
  hlo : 2 * a ≤ w
  hlo = lb-half-lo w
  hhi : w ≤ 2 * a + 1
  hhi = lb-half-hi w
  -- 2^(k+5) = 2·2^(k+4) ≤ w ≤ 2a + 1 ⟹ 2^(k+4) ≤ a
  hw′ : 2 * 2 ^ (k + 4) ≤ w
  hw′ = hw
  hX : 2 ^ (k + 4) ≤ a
  hX = lb-2x≤2a+1 a (2 ^ (k + 4)) (≤-trans hw′ hhi)
  hsa : 2 ^ (k + 4) ≤ suc a
  hsa = m≤n⇒m≤1+n hX
  IH : suc a ^ k ≤ 2 ^ suc a
  IH = lb-wk≤2w k (suc a) hsa
  hw2a : 2 * a + 1 ≤ 2 * a + 2
  hw2a = +-monoʳ-≤ (2 * a) (lb-1≤ 1)
  hw2b : 2 * a + 2 ≤ 2 * suc a
  hw2b = ≤-reflexive (sym (lb-2suc′ a))
  hw2 : w ≤ 2 * suc a
  hw2 = ≤-trans hhi (≤-trans hw2a hw2b)
  -- w^k ≤ (2(a+1))^k = 2^k·(a+1)^k ≤ 2^k·2^(a+1)
  Epow : w ^ k ≤ (2 * suc a) ^ k
  Epow = lb-pow≤ k hw2
  Edis : (2 * suc a) ^ k ≤ 2 ^ k * suc a ^ k
  Edis = ≤-reflexive (^-distribʳ-* k 2 (suc a))
  Em : 2 ^ k * suc a ^ k ≤ 2 ^ k * 2 ^ suc a
  Em = *-monoʳ-≤ (2 ^ k) IH
  E1 : w ^ k ≤ 2 ^ k * 2 ^ suc a
  E1 = ≤-trans Epow (≤-trans Edis Em)
  Ecomm : w ^ suc k ≡ w ^ k * w
  Ecomm = *-comm w (w ^ k)
  E2 : w ^ suc k ≤ 2 ^ k * 2 ^ suc a * (2 * a + 1)
  E2 = ≤-trans (≤-reflexive Ecomm) (*-mono-≤ E1 hhi)
  -- 2^(k+1)·(2a+1) ≤ 2^(k+1)·3a = a·(3·2^(k+1)) ≤ a·2^(k+3) ≤ 2^a
  h1a : 1 ≤ a
  h1a = ≤-trans (lb-pow1 (k + 4) (lb-1≤ 1)) hX
  e3a : 2 * a + a ≡ 3 * a
  e3a = solve 1 (λ a′ → (con 2 :* a′) :+ a′ := con 3 :* a′) refl a
  h3a : 2 * a + 1 ≤ 3 * a
  h3a = ≤-trans (+-monoʳ-≤ (2 * a) h1a) (≤-reflexive e3a)
  S1 : 2 ^ (k + 1) * (2 * a + 1) ≤ 2 ^ (k + 1) * (3 * a)
  S1 = *-monoʳ-≤ (2 ^ (k + 1)) h3a
  eAB : 2 ^ (k + 1) * (3 * a) ≡ a * (2 ^ (k + 1) * 3)
  eAB = trans (sym (*-assoc (2 ^ (k + 1)) 3 a)) (*-comm (2 ^ (k + 1) * 3) a)
  ePow : 2 ^ (k + 3) ≡ 2 ^ (k + 1) * 4
  ePow = trans (cong (λ z → 2 ^ z) (sym (+-assoc k 1 2)))
           (^-distribˡ-+-* 2 (k + 1) 2)
  mono′ : 2 ^ (k + 1) * 3 ≤ 2 ^ (k + 3)
  mono′ = ≤-trans (*-monoʳ-≤ (2 ^ (k + 1)) (m≤n+m 3 1)) (≤-reflexive (sym ePow))
  S2 : a * (2 ^ (k + 1) * 3) ≤ a * 2 ^ (k + 3)
  S2 = *-monoʳ-≤ a mono′
  -- a·2^(k+3) ≤ 2^a（线性·常数 ≤ 指数, 阈值 2^(k+3) ≤ a）
  hk4 : k + 3 ≤ k + 4
  hk4 = +-monoʳ-≤ k (m≤n+m 3 1)
  h3 : 2 ^ (k + 3) ≤ 2 ^ (k + 4)
  h3 = lb-pow-mono (k + 3) (k + 4) (lb-1≤ 1) hk4
  diff = lb-≤-diff (2 ^ (k + 3)) a (≤-trans h3 hX)
  e2k : (k + 3) + (k + 3) ≡ 2 * (k + 3)
  e2k = cong (λ z → (k + 3) + z) (sym (+-identityʳ (k + 3)))
  eH1 : 2 ^ (k + 3) * 2 ^ (k + 3) ≡ 2 ^ ((k + 3) + (k + 3))
  eH1 = sym (^-distribˡ-+-* 2 (k + 3) (k + 3))
  eH2 : 2 ^ ((k + 3) + (k + 3)) ≡ 2 ^ (2 * (k + 3))
  eH2 = cong (λ z → 2 ^ z) e2k
  eH3 : 2 ^ (2 * (k + 3)) ≤ 2 ^ (2 ^ (k + 3))
  eH3 = lb-pow-mono (2 * (k + 3)) (2 ^ (k + 3)) (lb-1≤ 1) (lb-2k₊6 k)
  hcc : 2 ^ (k + 3) * 2 ^ (k + 3) ≤ 2 ^ (2 ^ (k + 3))
  hcc = ≤-trans (≤-reflexive eH1) (≤-trans (≤-reflexive eH2) eH3)
  linExp : a * 2 ^ (k + 3) ≤ 2 ^ a
  linExp = subst (λ z → z * 2 ^ (k + 3) ≤ 2 ^ z) (sym (proj₂ diff))
             (lb-lin-exp (2 ^ (k + 3)) (proj₁ diff) hcc (lb-n≤2ⁿ (2 ^ (k + 3))))
  I2 : 2 ^ (k + 1) * (2 * a + 1) ≤ 2 ^ a
  I2 = ≤-trans S1 (≤-trans (≤-reflexive eAB) (≤-trans S2 linExp))
  -- 2^k·2^(a+1)·(2a+1) = 2^a·(2^(k+1)·(2a+1)) ≤ 2^a·2^a
  eS′ : 2 ^ k * 2 ^ suc a * (2 * a + 1) ≡ 2 ^ k * (2 * 2 ^ a) * (2 * a + 1)
  eS′ = refl
  I1 : 2 ^ k * (2 * 2 ^ a) * (2 * a + 1) ≡ 2 ^ a * (2 ^ k * 2 * (2 * a + 1))
  I1 = solve 3 (λ X′ Y′ a′ → (X′ :* (con 2 :* Y′)) :* ((con 2 :* a′) :+ con 1)
                       := Y′ :* ((X′ :* con 2) :* ((con 2 :* a′) :+ con 1)))
         refl (2 ^ k) (2 ^ a) a
  eZ : 2 ^ k * 2 ≡ 2 ^ (k + 1)
  eZ = sym (^-distribˡ-+-* 2 k 1)
  eI1 : 2 ^ a * (2 ^ k * 2 * (2 * a + 1)) ≡ 2 ^ a * (2 ^ (k + 1) * (2 * a + 1))
  eI1 = cong (λ z → 2 ^ a * (z * (2 * a + 1))) eZ
  E3 : 2 ^ k * 2 ^ suc a * (2 * a + 1) ≤ 2 ^ a * 2 ^ a
  E3 = ≤-trans (≤-reflexive eS′) (≤-trans (≤-reflexive I1)
         (≤-trans (≤-reflexive eI1) (*-monoʳ-≤ (2 ^ a) I2)))
  -- 2^a·2^a = 2^(2a) ≤ 2^w
  e4a : 2 ^ a * 2 ^ a ≡ 2 ^ (a + a)
  e4a = sym (^-distribˡ-+-* 2 a a)
  e4b : a + a ≡ 2 * a
  e4b = cong (λ z → a + z) (sym (+-identityʳ a))
  E4 : 2 ^ a * 2 ^ a ≤ 2 ^ w
  E4 = ≤-trans (≤-reflexive (trans e4a (cong (λ z → 2 ^ z) e4b)))
         (lb-pow-mono (2 * a) w (lb-1≤ 1) hlo)

--------------------------------------------------------------------------------
-- §10. listBits 实例化
--------------------------------------------------------------------------------

-- 一条表: 2^w 条记录, 每条 2w 比特（Lean: listBits w = 2 * w * 2 ^ w）
lb-listBits : ℕ → ℕ
lb-listBits w = 2 * w * 2 ^ w

-- listBits 增长快过 w 的任意幂
lb-listBits-grow : ∀ k → lb-Ev (λ w → w ^ k ≤ lb-listBits w)
lb-listBits-grow k = 2 ^ (k + 4) , lp
  where
  lp : ∀ w → 2 ^ (k + 4) ≤ w → w ^ k ≤ lb-listBits w
  lp w h = ≤-trans (lb-wk≤2w k w h) (lb-m≤k·m (2 ^ w) (2 * w) h2w)
    where
    h1w : 1 ≤ w
    h1w = ≤-trans (lb-pow1 (k + 4) (lb-1≤ 1)) h
    h2w : 1 ≤ 2 * w
    h2w = lb-1≤· 2 w (lb-1≤ 1) h1w

lb-w≤ww : ∀ w → w ≤ w * w
lb-w≤ww zero = z≤n
lb-w≤ww (suc w) = lb-m≤m·k (suc w) (suc w) (s≤s z≤n)

-- ★ 推论: Lean `Iteration.incompatible`（Seed → ManyList → Compression → False）的 ℕ 镜像。
--   n := listBits w; h := w²（Lean 取 h = clog 2 (listBits w), 对大 w 有 w ≤ h ≤ w²,
--   故 Lean 的压缩蕴涵以 H = λ w → w * w 写出的 lb-Comp——桥接理由见头注）。
lb-incompatible-lists : ∀ (P : ℕ → ℕ → ℕ → Set) →
  lb-Seed P lb-listBits → lb-Many P lb-listBits →
  lb-Comp P lb-listBits (λ w → w * w) → ⊥
lb-incompatible-lists P seed many comp =
  lb-incompatible P lb-listBits (λ w → w * w) grow seed many comp
  where
  grow : lb-Grow lb-listBits (λ w → w * w)
  grow = lb-listBits-grow , (zero , (λ w _ → lb-w≤ww w)) ,
         (zero , (λ w _ → ≤-refl))
