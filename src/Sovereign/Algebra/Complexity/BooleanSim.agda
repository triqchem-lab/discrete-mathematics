{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.BooleanSim
-- Boolean ↔ GF(3) 门电路互模拟——「三进制不绕过 P/NP」的立界定理（W1c）
--
-- 定理意义（头注）：布尔电路（{false,true}^n 上的 Var/NOT/AND/OR/XOR 电路）
-- 在三进制门模型下**原生可求值**。同一电路 BS-Circuit 同时携带布尔求值
-- BS-evalB 与 GF(3) 求值 BS-evalT，经嵌入 BS-emb（false↦T₀, true↦T₁）后
-- 二者逐点一致（§4 主定理 BS-sim，结构归纳闭合，门引理为基例）；且 GF(3)
-- 侧带计账求值 BS-evalTC 的账目**恒等于**电路规模 BS-size（§5，每门 1 步、
-- 变量读 1 步——常数因子 c = 1）。由此得本件主推论：任何布尔电路族的
-- 多项式性（规模 ≤ 多项式 p）在三进制门模型下**逐字保持、界不放大**
-- （§5 BS-fam-steps-poly）。即：换三进制计算底座不会把布尔难题「免费」
-- 多项式化——这是立界定理的第一半（正向：布尔 ⟹ 三进制，零开销）。
-- 语言层（§6）闭合双向迁移：trit 侧 InP 判定器沿嵌入拉回布尔侧，界不变
-- （BS-migrate）；布尔电路族经叶解码 BS-evalBD 迁移为 trit 侧 InP 判定器，
-- 界同样不变（BS-migrate-family）。类级规范等式（P_ternary = P_Boolean 的
-- 全称形式）需要字母表编码理论 + 反向门模拟（⊕/⊗ 的 9 例布尔模拟器），
-- 按诚实纪律立界（§8），本件不冒充。
--
-- 分级标注约定（全库诚实分级纪律，同 TimeBound/PClass）：
--   〔结构定义〕= 数据/record 定义；〔结构证明〕= 对输入结构归纳；
--   〔refl 枚举〕= 有限情形逐点 refl；〔立界注记〕= 深件边界，不设空壳签名。
--
-- 跨层引用边界：
--   Sovereign.Base.Trit —— GF(3) 载体与 ⊕/⊗：主定理逐点消耗其**定义性
--   归约**（布尔片段 = 9 例中的嵌入像 4 例），不用任何环公理——复杂度层
--   与代数层正交（Fable 裁定「代数污染禁止」的接口件形态）。
--   Sovereign.Algebra.Complexity.{TimeBound,PClass} —— 同层（W1 计算模型层）。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.BooleanSim where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_; map; lookup)
open import Data.Vec.Properties using (lookup-map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym)

-- 引用边界（跨域引用注记，格式同 A4Representations L19）：
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; Mono; Pos; le-mul)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass
  using (TritLang; Decider; InP)

-- ────────────────────────────────────────────────────────────────────
-- §1 嵌入、解码与像〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 布尔 → GF(3)：false↦T₀（吸收态），true↦T₁（平衡态）
BS-emb : Bool → Trit
BS-emb false = T₀
BS-emb true  = T₁

-- GF(3) → 布尔：T₀↦false，T₁/T₂↦true（T₂ 是诚实折变，见 §6）
BS-dec : Trit → Bool
BS-dec T₀ = false
BS-dec T₁ = true
BS-dec T₂ = true

-- 像谓词：t 落在嵌入像 {T₀,T₁} 内
BS-inImage : Trit → Set
BS-inImage t = (t ≡ T₀) ⊎ (t ≡ T₁)

BS-inImage-emb : ∀ b → BS-inImage (BS-emb b)          -- 〔refl 枚举〕
BS-inImage-emb false = inj₁ refl
BS-inImage-emb true  = inj₂ refl

BS-dec-emb : ∀ b → BS-dec (BS-emb b) ≡ b              -- dec ∘ emb = id
BS-dec-emb false = refl
BS-dec-emb true  = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 GF(3) 门模拟器〔结构定义 + 逐门一致性（refl 枚举）+ 闭合性〕
--
-- 在嵌入像 {T₀,T₁} 上与布尔门逐点一致；{T₂} 上行为由 GF(3) 环结构
-- 自由延伸（2⊗t = −t），不承担布尔语义。
-- ────────────────────────────────────────────────────────────────────

-- 手征读法：T₂ ⊗ t = negate t（GF(3)：2 ≡ −1 mod 3）
BS-⊗2-negate : ∀ t → (T₂ ⊗ t) ≡ negate t              -- 〔refl 枚举 3 例〕
BS-⊗2-negate T₀ = refl
BS-⊗2-negate T₁ = refl
BS-⊗2-negate T₂ = refl

-- NOT x = T₁ ⊕ (T₂⊗x) = 1 + (−x) = 1 − x（mod 3）
BS-gNOT : Trit → Trit
BS-gNOT x = T₁ ⊕ (T₂ ⊗ x)

BS-gNOT-negate : ∀ x → BS-gNOT x ≡ (T₁ ⊕ negate x)     -- 门公式的手征形
BS-gNOT-negate x = cong (λ u → T₁ ⊕ u) (BS-⊗2-negate x)

-- AND x y = x⊗y
BS-gAND : Trit → Trit → Trit
BS-gAND x y = x ⊗ y

-- OR x y = (x⊕y) ⊕ (T₂⊗x⊗y)
BS-gOR : Trit → Trit → Trit
BS-gOR x y = (x ⊕ y) ⊕ ((T₂ ⊗ x) ⊗ y)

-- XOR x y = (x⊕y) ⊕ (x⊗y)
BS-gXOR : Trit → Trit → Trit
BS-gXOR x y = (x ⊕ y) ⊕ (x ⊗ y)

-- §2b 逐门一致性：嵌入点上 GF(3) 门 ≡ 布尔门〔refl 枚举，14 例〕
-- （NOT 2 例 + AND/OR/XOR 各 4 例 = 嵌入像 4/9 格逐点核对）

BS-sim-NOT : ∀ b → BS-gNOT (BS-emb b) ≡ BS-emb (not b)
BS-sim-NOT false = refl                                -- 1 − 0 = 1
BS-sim-NOT true  = refl                                -- 1 − 1 = 0

BS-sim-AND : ∀ b₁ b₂ → BS-gAND (BS-emb b₁) (BS-emb b₂) ≡ BS-emb (b₁ ∧ b₂)
BS-sim-AND false false = refl                          -- 0·0 = 0
BS-sim-AND false true  = refl                          -- 0·1 = 0
BS-sim-AND true  false = refl                          -- 1·0 = 0
BS-sim-AND true  true  = refl                          -- 1·1 = 1

BS-sim-OR : ∀ b₁ b₂ → BS-gOR (BS-emb b₁) (BS-emb b₂) ≡ BS-emb (b₁ ∨ b₂)
BS-sim-OR false false = refl                           -- 0⊕0 ⊕ 0·0 = 0
BS-sim-OR false true  = refl                           -- 0⊕1 ⊕ 0·1 = 1
BS-sim-OR true  false = refl                           -- 1⊕0 ⊕ 0    = 1
BS-sim-OR true  true  = refl                           -- 1⊕1 ⊕ 2·1 = 2⊕2 = 1

-- 布尔异或（自定义，避开 stdlib API 面）
BS-bxor : Bool → Bool → Bool
BS-bxor false y = y
BS-bxor true  y = not y

BS-sim-XOR : ∀ b₁ b₂ → BS-gXOR (BS-emb b₁) (BS-emb b₂) ≡ BS-emb (BS-bxor b₁ b₂)
BS-sim-XOR false false = refl                          -- 0⊕0 ⊕ 0·0 = 0
BS-sim-XOR false true  = refl                          -- 0⊕1 ⊕ 0    = 1
BS-sim-XOR true  false = refl                          -- 1⊕0 ⊕ 0    = 1
BS-sim-XOR true  true  = refl                          -- 1⊕1 ⊕ 1·1 = 2⊕1 = 0

-- §2c 闭合性：输入限制 {T₀,T₁} 时输出也在 {T₀,T₁}〔结构证明〕

BS-closed-NOT : ∀ x → BS-inImage x → BS-inImage (BS-gNOT x)
BS-closed-NOT x (inj₁ h) = inj₂ (cong BS-gNOT h)       -- gNOT T₀ = 1⊕(2·0) = 1
BS-closed-NOT x (inj₂ h) = inj₁ (cong BS-gNOT h)       -- gNOT T₁ = 1⊕(2·1) = 0

-- 归约注记：⊗ 的子句序（`_ ⊗ T₀` 先于首变元判位）使单边 cong 对自由
-- 变元卡死——闭合性证明一律双边 cong₂ 全实例化到构造子后整体归约。
BS-closed-AND : ∀ x y → BS-inImage x → BS-inImage y → BS-inImage (BS-gAND x y)
BS-closed-AND x y (inj₁ hx) (inj₁ hy) = inj₁ (cong₂ BS-gAND hx hy)
  -- 0⊗0 = 0
BS-closed-AND x y (inj₁ hx) (inj₂ hy) = inj₁ (cong₂ BS-gAND hx hy)
  -- 0⊗1 = 0
BS-closed-AND x y (inj₂ hx) (inj₁ hy) = inj₁ (cong₂ BS-gAND hx hy)
  -- 1⊗0 = 0
BS-closed-AND x y (inj₂ hx) (inj₂ hy) = inj₂ (cong₂ BS-gAND hx hy)
  -- 1⊗1 = 1

BS-closed-OR : ∀ x y → BS-inImage x → BS-inImage y → BS-inImage (BS-gOR x y)
BS-closed-OR x y (inj₁ hx) (inj₁ hy) = inj₁ (cong₂ BS-gOR hx hy)
  -- (0⊕0) ⊕ (2·0·0) = 0
BS-closed-OR x y (inj₁ hx) (inj₂ hy) = inj₂ (cong₂ BS-gOR hx hy)
  -- (0⊕1) ⊕ (2·0·1) = 1
BS-closed-OR x y (inj₂ hx) (inj₁ hy) = inj₂ (cong₂ BS-gOR hx hy)
  -- (1⊕0) ⊕ (2·1·0) = 1
BS-closed-OR x y (inj₂ hx) (inj₂ hy) = inj₂ (cong₂ BS-gOR hx hy)
  -- (1⊕1) ⊕ (2·1·1) = 2⊕2 = 1

BS-closed-XOR : ∀ x y → BS-inImage x → BS-inImage y → BS-inImage (BS-gXOR x y)
BS-closed-XOR x y (inj₁ hx) (inj₁ hy) = inj₁ (cong₂ BS-gXOR hx hy)
  -- (0⊕0) ⊕ (0·0) = 0
BS-closed-XOR x y (inj₁ hx) (inj₂ hy) = inj₂ (cong₂ BS-gXOR hx hy)
  -- (0⊕1) ⊕ (0·1) = 1
BS-closed-XOR x y (inj₂ hx) (inj₁ hy) = inj₂ (cong₂ BS-gXOR hx hy)
  -- (1⊕0) ⊕ (1·0) = 1
BS-closed-XOR x y (inj₂ hx) (inj₂ hy) = inj₁ (cong₂ BS-gXOR hx hy)
  -- (1⊕1) ⊕ (1·1) = 2⊕1 = 0

-- ────────────────────────────────────────────────────────────────────
-- §3 电路数据型与双求值〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

data BS-Circuit (n : ℕ) : Set where
  BS-var : Fin n → BS-Circuit n
  BS-not : BS-Circuit n → BS-Circuit n
  BS-and : BS-Circuit n → BS-Circuit n → BS-Circuit n
  BS-or  : BS-Circuit n → BS-Circuit n → BS-Circuit n
  BS-xor : BS-Circuit n → BS-Circuit n → BS-Circuit n

-- 布尔求值
BS-evalB : ∀ {n} → BS-Circuit n → Vec Bool n → Bool
BS-evalB (BS-var i)   xs = lookup xs i
BS-evalB (BS-not c)   xs = not (BS-evalB c xs)
BS-evalB (BS-and a b) xs = BS-evalB a xs ∧ BS-evalB b xs
BS-evalB (BS-or  a b) xs = BS-evalB a xs ∨ BS-evalB b xs
BS-evalB (BS-xor a b) xs = BS-bxor (BS-evalB a xs) (BS-evalB b xs)

-- GF(3) 求值（§2 门模拟器的逐节点复制——同一电路，双载体）
BS-evalT : ∀ {n} → BS-Circuit n → Vec Trit n → Trit
BS-evalT (BS-var i)   xs = lookup xs i
BS-evalT (BS-not c)   xs = BS-gNOT (BS-evalT c xs)
BS-evalT (BS-and a b) xs = BS-gAND (BS-evalT a xs) (BS-evalT b xs)
BS-evalT (BS-or  a b) xs = BS-gOR (BS-evalT a xs) (BS-evalT b xs)
BS-evalT (BS-xor a b) xs = BS-gXOR (BS-evalT a xs) (BS-evalT b xs)

-- 电路规模：变量读 1，每门 1（计账常数因子 c 的口径基准）
BS-size : ∀ {n} → BS-Circuit n → ℕ
BS-size (BS-var _)    = 1
BS-size (BS-not c)    = suc (BS-size c)
BS-size (BS-and a b)  = suc (BS-size a + BS-size b)
BS-size (BS-or  a b)  = suc (BS-size a + BS-size b)
BS-size (BS-xor a b)  = suc (BS-size a + BS-size b)

-- ────────────────────────────────────────────────────────────────────
-- §4 主定理：结构归纳互模拟〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- ★ 主定理：同一电路在嵌入输入上，GF(3) 求值 ≡ 嵌入(布尔求值)。
--   基例 var = lookup-map；门步 = §2 门引理 + cong/cong₂。
BS-sim : ∀ {n} (c : BS-Circuit n) (xs : Vec Bool n)
       → BS-evalT c (map BS-emb xs) ≡ BS-emb (BS-evalB c xs)
BS-sim (BS-var i)   xs = lookup-map i BS-emb xs
BS-sim (BS-not c)   xs = trans (cong BS-gNOT (BS-sim c xs))
                               (BS-sim-NOT (BS-evalB c xs))
BS-sim (BS-and a b) xs = trans (cong₂ BS-gAND (BS-sim a xs) (BS-sim b xs))
                               (BS-sim-AND (BS-evalB a xs) (BS-evalB b xs))
BS-sim (BS-or  a b) xs = trans (cong₂ BS-gOR (BS-sim a xs) (BS-sim b xs))
                               (BS-sim-OR (BS-evalB a xs) (BS-evalB b xs))
BS-sim (BS-xor a b) xs = trans (cong₂ BS-gXOR (BS-sim a xs) (BS-sim b xs))
                               (BS-sim-XOR (BS-evalB a xs) (BS-evalB b xs))

-- 解码推论：嵌入点上的 GF(3) 求值经 BS-dec 直接落回布尔值
BS-sim-dec : ∀ {n} (c : BS-Circuit n) (xs : Vec Bool n)
           → BS-dec (BS-evalT c (map BS-emb xs)) ≡ BS-evalB c xs
BS-sim-dec c xs = trans (cong BS-dec (BS-sim c xs)) (BS-dec-emb (BS-evalB c xs))

-- ────────────────────────────────────────────────────────────────────
-- §5 计账层〔结构定义 + 结构证明〕
--
-- 三种 Counted 形：布尔计账 evalBC、GF(3) 计账 evalTC、叶解码计账
-- evalBD（迁移机，§6 用）。三者的 steps 均恒等于 BS-size（每门常数账 1）。
-- ────────────────────────────────────────────────────────────────────

BS-evalBC : ∀ {n} → BS-Circuit n → Vec Bool n → Counted Bool
BS-evalBC (BS-var i)   xs = mkCnt (lookup xs i) 1
BS-evalBC (BS-not c)   xs =
  mkCnt (not (value (BS-evalBC c xs))) (suc (steps (BS-evalBC c xs)))
BS-evalBC (BS-and a b) xs =
  mkCnt (value (BS-evalBC a xs) ∧ value (BS-evalBC b xs))
        (suc (steps (BS-evalBC a xs) + steps (BS-evalBC b xs)))
BS-evalBC (BS-or  a b) xs =
  mkCnt (value (BS-evalBC a xs) ∨ value (BS-evalBC b xs))
        (suc (steps (BS-evalBC a xs) + steps (BS-evalBC b xs)))
BS-evalBC (BS-xor a b) xs =
  mkCnt (BS-bxor (value (BS-evalBC a xs)) (value (BS-evalBC b xs)))
        (suc (steps (BS-evalBC a xs) + steps (BS-evalBC b xs)))

BS-evalTC : ∀ {n} → BS-Circuit n → Vec Trit n → Counted Trit
BS-evalTC (BS-var i)   xs = mkCnt (lookup xs i) 1
BS-evalTC (BS-not c)   xs =
  mkCnt (BS-gNOT (value (BS-evalTC c xs))) (suc (steps (BS-evalTC c xs)))
BS-evalTC (BS-and a b) xs =
  mkCnt (BS-gAND (value (BS-evalTC a xs)) (value (BS-evalTC b xs)))
        (suc (steps (BS-evalTC a xs) + steps (BS-evalTC b xs)))
BS-evalTC (BS-or  a b) xs =
  mkCnt (BS-gOR (value (BS-evalTC a xs)) (value (BS-evalTC b xs)))
        (suc (steps (BS-evalTC a xs) + steps (BS-evalTC b xs)))
BS-evalTC (BS-xor a b) xs =
  mkCnt (BS-gXOR (value (BS-evalTC a xs)) (value (BS-evalTC b xs)))
        (suc (steps (BS-evalTC a xs) + steps (BS-evalTC b xs)))

-- 叶解码形：变量读线经 BS-dec 折到布尔，门体全布尔——同一电路吃任意
-- trit 输入、产出布尔语义的**单遍**计账判定器（解码在账内，无隐藏遍）。
BS-evalBD : ∀ {n} → BS-Circuit n → Vec Trit n → Counted Bool
BS-evalBD (BS-var i)   xs = mkCnt (BS-dec (lookup xs i)) 1
BS-evalBD (BS-not c)   xs =
  mkCnt (not (value (BS-evalBD c xs))) (suc (steps (BS-evalBD c xs)))
BS-evalBD (BS-and a b) xs =
  mkCnt (value (BS-evalBD a xs) ∧ value (BS-evalBD b xs))
        (suc (steps (BS-evalBD a xs) + steps (BS-evalBD b xs)))
BS-evalBD (BS-or  a b) xs =
  mkCnt (value (BS-evalBD a xs) ∨ value (BS-evalBD b xs))
        (suc (steps (BS-evalBD a xs) + steps (BS-evalBD b xs)))
BS-evalBD (BS-xor a b) xs =
  mkCnt (BS-bxor (value (BS-evalBD a xs)) (value (BS-evalBD b xs)))
        (suc (steps (BS-evalBD a xs) + steps (BS-evalBD b xs)))

-- §5b 账目恒等：三形 steps ≡ BS-size〔结构证明〕
-- （精确等式而非不等式——每门常数账 1，无隐藏系数）

BS-steps-BC : ∀ {n} (c : BS-Circuit n) (xs : Vec Bool n)
            → steps (BS-evalBC c xs) ≡ BS-size c
BS-steps-BC (BS-var i)   xs = refl
BS-steps-BC (BS-not c)   xs = cong suc (BS-steps-BC c xs)
BS-steps-BC (BS-and a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-BC a xs) (BS-steps-BC b xs)
BS-steps-BC (BS-or  a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-BC a xs) (BS-steps-BC b xs)
BS-steps-BC (BS-xor a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-BC a xs) (BS-steps-BC b xs)

BS-steps-TC : ∀ {n} (c : BS-Circuit n) (xs : Vec Trit n)
            → steps (BS-evalTC c xs) ≡ BS-size c
BS-steps-TC (BS-var i)   xs = refl
BS-steps-TC (BS-not c)   xs = cong suc (BS-steps-TC c xs)
BS-steps-TC (BS-and a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-TC a xs) (BS-steps-TC b xs)
BS-steps-TC (BS-or  a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-TC a xs) (BS-steps-TC b xs)
BS-steps-TC (BS-xor a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-TC a xs) (BS-steps-TC b xs)

BS-steps-BD : ∀ {n} (c : BS-Circuit n) (xs : Vec Trit n)
            → steps (BS-evalBD c xs) ≡ BS-size c
BS-steps-BD (BS-var i)   xs = refl
BS-steps-BD (BS-not c)   xs = cong suc (BS-steps-BD c xs)
BS-steps-BD (BS-and a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-BD a xs) (BS-steps-BD b xs)
BS-steps-BD (BS-or  a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-BD a xs) (BS-steps-BD b xs)
BS-steps-BD (BS-xor a b) xs =
  cong₂ (λ u v → suc (u + v)) (BS-steps-BD a xs) (BS-steps-BD b xs)

-- 布尔计账与 GF(3) 计账逐电路同账（与输入值无关）
BS-steps-BC≡TC : ∀ {n} (c : BS-Circuit n) (xs : Vec Bool n) (ys : Vec Trit n)
               → steps (BS-evalBC c xs) ≡ steps (BS-evalTC c ys)
BS-steps-BC≡TC c xs ys = trans (BS-steps-BC c xs) (sym (BS-steps-TC c ys))

-- §5c 值一致：Counted 形 ≡ 纯形〔结构证明〕

BS-value-BC : ∀ {n} (c : BS-Circuit n) (xs : Vec Bool n)
            → value (BS-evalBC c xs) ≡ BS-evalB c xs
BS-value-BC (BS-var i)   xs = refl
BS-value-BC (BS-not c)   xs = cong not (BS-value-BC c xs)
BS-value-BC (BS-and a b) xs = cong₂ _∧_ (BS-value-BC a xs) (BS-value-BC b xs)
BS-value-BC (BS-or  a b) xs = cong₂ _∨_ (BS-value-BC a xs) (BS-value-BC b xs)
BS-value-BC (BS-xor a b) xs = cong₂ BS-bxor (BS-value-BC a xs) (BS-value-BC b xs)

BS-value-TC : ∀ {n} (c : BS-Circuit n) (xs : Vec Trit n)
            → value (BS-evalTC c xs) ≡ BS-evalT c xs
BS-value-TC (BS-var i)   xs = refl
BS-value-TC (BS-not c)   xs = cong BS-gNOT (BS-value-TC c xs)
BS-value-TC (BS-and a b) xs = cong₂ BS-gAND (BS-value-TC a xs) (BS-value-TC b xs)
BS-value-TC (BS-or  a b) xs = cong₂ BS-gOR (BS-value-TC a xs) (BS-value-TC b xs)
BS-value-TC (BS-xor a b) xs = cong₂ BS-gXOR (BS-value-TC a xs) (BS-value-TC b xs)

BS-value-BD : ∀ {n} (c : BS-Circuit n) (xs : Vec Trit n)
            → value (BS-evalBD c xs) ≡ BS-evalB c (map BS-dec xs)
BS-value-BD (BS-var i)   xs = sym (lookup-map i BS-dec xs)
BS-value-BD (BS-not c)   xs = cong not (BS-value-BD c xs)
BS-value-BD (BS-and a b) xs = cong₂ _∧_ (BS-value-BD a xs) (BS-value-BD b xs)
BS-value-BD (BS-or  a b) xs = cong₂ _∨_ (BS-value-BD a xs) (BS-value-BD b xs)
BS-value-BD (BS-xor a b) xs = cong₂ BS-bxor (BS-value-BD a xs) (BS-value-BD b xs)

-- §5d 界定理（TimeBound ≤-算术引理库）

-- 精确账 ≤ 规模（等式包装；常数因子 c = 1）
BS-steps≤size : ∀ {n} (c : BS-Circuit n) (xs : Vec Trit n)
              → steps (BS-evalTC c xs) ≤ BS-size c
BS-steps≤size c xs = ≤-reflexive (BS-steps-TC c xs)

-- 放大形：steps ≤ 规模 × 2（le-mul 练习件——j ≤ j*k 对 k ≥ 1）
BS-steps≤2size : ∀ {n} (c : BS-Circuit n) (xs : Vec Trit n)
               → steps (BS-evalTC c xs) ≤ BS-size c * 2
BS-steps≤2size c xs =
  ≤-trans (≤-reflexive (BS-steps-TC c xs)) (le-mul (BS-size c) 2 (s≤s z≤n))

-- ★ 主推论（立界定理的正面陈述）：布尔电路族的多项式性在三进制门模型
--   下逐字保持——同一电路、同一多项式界 p，无任何放大。
BS-fam-steps-poly : (fam : (n : ℕ) → BS-Circuit n) (p : ℕ → ℕ)
                  → (∀ n → BS-size (fam n) ≤ p n)
                  → ∀ n xs → steps (BS-evalTC (fam n) xs) ≤ p n
BS-fam-steps-poly fam p bnd n xs = ≤-trans (BS-steps≤size (fam n) xs) (bnd n)

-- ────────────────────────────────────────────────────────────────────
-- §6 解码方向与类迁移
-- ────────────────────────────────────────────────────────────────────

-- emb ∘ dec 仅在像上恒等（诚实注记：T₂ 经 dec 折到 true，无布尔原像）
BS-emb-dec-image : ∀ t → BS-inImage t → BS-emb (BS-dec t) ≡ t
BS-emb-dec-image t (inj₁ h) = trans (cong (λ z → BS-emb (BS-dec z)) h) (sym h)
BS-emb-dec-image t (inj₂ h) = trans (cong (λ z → BS-emb (BS-dec z)) h) (sym h)

-- 串级：dec∘emb 恒等 ⟹ 串级恒等〔结构证明〕
BS-decVec : ∀ {n} → Vec Trit n → Vec Bool n
BS-decVec = map BS-dec

BS-embVec : ∀ {n} → Vec Bool n → Vec Trit n
BS-embVec = map BS-emb

BS-decVec-embVec : ∀ {n} (xs : Vec Bool n) → BS-decVec (BS-embVec xs) ≡ xs
BS-decVec-embVec []         = refl
BS-decVec-embVec (x ∷ xs) = cong₂ _∷_ (BS-dec-emb x) (BS-decVec-embVec xs)

-- §6b 迁移引理一（拉回形）：trit 侧 InP 判定器 ⟹ 布尔侧判定器。
--   布尔语言 := 原语言的嵌入拉回；判定器直接吃嵌入输入，界不变
--   （嵌入点求值做的正是同一份 trit 工作，无成本缩放）。
--   规范形注记：库内 InP 仅索引 TritLang（PClass 裁定：母语为 trit 串），
--   故布尔侧以同字段集镜像 record BS-InPBool 承接——拉回成员资格在
--   镜像类上闭合；「镜像类 = 布尔串上的规范 P」的类级同一性立界（§8(i)）。
BS-pull-lang : TritLang → (n : ℕ) → Vec Bool n → Set
BS-pull-lang L n xs = L n (map BS-emb xs)

BS-DeciderB : Set
BS-DeciderB = (n : ℕ) → Vec Bool n → Counted Bool

BS-BoolLang : Set₁
BS-BoolLang = (n : ℕ) → Vec Bool n → Set

record BS-InPBool (L : BS-BoolLang) : Set₁ where
  field
    p          : ℕ → ℕ                 -- 多项式界（以位数 n 为规模）
    p-mono     : Mono p
    p-pos      : Pos p
    decider    : BS-DeciderB
    p-complete : ∀ n xs → L n xs → value (decider n xs) ≡ true
    p-sound    : ∀ n xs → value (decider n xs) ≡ true → L n xs
    p-cost     : ∀ n xs → steps (decider n xs) ≤ p n

BS-migrate : ∀ {L} (dp : InP L) → BS-InPBool (BS-pull-lang L)
BS-migrate dp = record
  { p          = InP.p dp
  ; p-mono     = InP.p-mono dp
  ; p-pos      = InP.p-pos dp
  ; decider    = λ n xs → InP.decider dp n (map BS-emb xs)
  ; p-complete = λ n xs → InP.p-complete dp n (map BS-emb xs)
  ; p-sound    = λ n xs → InP.p-sound dp n (map BS-emb xs)
  ; p-cost     = λ n xs → InP.p-cost dp n (map BS-emb xs) }

-- §6c 迁移引理二（推前形）：布尔电路族 ⟹ trit 侧 InP 判定器。
--   trit 语言 := 布尔语言的叶解码推前；判定器 = evalBD（§5 叶解码形，
--   解码在账内），界不变（steps ≡ size ≤ p）。两方向合流：语言层迁移
--   **双向闭合且零成本因子**。
record BS-BoolFamily (L : BS-BoolLang) : Set₁ where
  field
    fam      : (n : ℕ) → BS-Circuit n
    fam-p    : ℕ → ℕ
    fam-mono : Mono fam-p
    fam-pos  : Pos fam-p
    fam-size : ∀ n → BS-size (fam n) ≤ fam-p n
    fam-corr : ∀ n xs → BS-evalB (fam n) xs ≡ true → L n xs
    fam-comp : ∀ n xs → L n xs → BS-evalB (fam n) xs ≡ true

BS-push-lang : BS-BoolLang → TritLang
BS-push-lang L n xs = L n (map BS-dec xs)

BS-migrate-family : ∀ {L} (bf : BS-BoolFamily L) → InP (BS-push-lang L)
BS-migrate-family bf = record
  { p          = fam-p
  ; p-mono     = fam-mono
  ; p-pos      = fam-pos
  ; decider    = λ n xs → BS-evalBD (fam n) xs
  ; p-complete = λ n xs h →
      trans (BS-value-BD (fam n) xs) (fam-comp n (map BS-dec xs) h)
  ; p-sound    = λ n xs h →
      fam-corr n (map BS-dec xs) (trans (sym (BS-value-BD (fam n) xs)) h)
  ; p-cost     = λ n xs →
      ≤-trans (≤-reflexive (BS-steps-BD (fam n) xs)) (fam-size n) }
  where open BS-BoolFamily bf

-- ────────────────────────────────────────────────────────────────────
-- §7 核对层〔refl 枚举〕——半加器实例（1 + 1 = carry 1, sum 0）
-- ────────────────────────────────────────────────────────────────────

BS-c-ha-sum : BS-Circuit 2
BS-c-ha-sum = BS-xor (BS-var fzero) (BS-var (fsuc fzero))

BS-c-ha-carry : BS-Circuit 2
BS-c-ha-carry = BS-and (BS-var fzero) (BS-var (fsuc fzero))

-- 互模拟实例化（嵌入点上 GF(3) 求值 = 嵌入(布尔求值)）
check-ha-sum : BS-evalT BS-c-ha-sum (map BS-emb (true ∷ true ∷ []))
             ≡ BS-emb (BS-evalB BS-c-ha-sum (true ∷ true ∷ []))
check-ha-sum = refl

check-ha-sum-val : BS-evalB BS-c-ha-sum (true ∷ true ∷ []) ≡ false
check-ha-sum-val = refl

check-ha-carry-val : BS-evalB BS-c-ha-carry (true ∷ true ∷ []) ≡ true
check-ha-carry-val = refl

-- 账目实例：steps ≡ size ≡ 3（2 变量读 + 1 门，逐字算术）
check-ha-steps : steps (BS-evalTC BS-c-ha-sum (map BS-emb (true ∷ true ∷ [])))
               ≡ BS-size BS-c-ha-sum
check-ha-steps = refl

check-ha-steps-num : BS-size BS-c-ha-sum ≡ 3
check-ha-steps-num = refl

-- 放大界实例（BS-steps≤2size 的应用核对）
check-ha-2size : steps (BS-evalTC BS-c-ha-sum (map BS-emb (true ∷ true ∷ [])))
               ≤ BS-size BS-c-ha-sum * 2
check-ha-2size = BS-steps≤2size BS-c-ha-sum (map BS-emb (true ∷ true ∷ []))

-- 迁移机实例：evalBD 在原始 trit 输入上复现布尔语义
check-ha-BD : value (BS-evalBD BS-c-ha-carry (T₁ ∷ T₁ ∷ [])) ≡ true
check-ha-BD = refl

-- 诚实边界样本：T₂ 叶解码折到 true（emb-dec-image 的反例显形）
check-ha-BD-T₂ : value (BS-evalBD BS-c-ha-carry (T₂ ∷ T₁ ∷ [])) ≡ true
check-ha-BD-T₂ = refl

-- ────────────────────────────────────────────────────────────────────
-- §8 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   类级规范等式（P_ternary = P_Boolean 全称形式）需两件缺件：
--       (a) 字母表编码理论——Vec Trit n ↔ Vec Bool m 的规范双射与长度
--           折算（本件的 BS-pull-lang/BS-push-lang 是以 emb/dec 为核的
--           **定向迁移**，非两种载体上的语言规范恒等）；
--       (b) 反向门模拟——⊕/⊗ 在 2-bit/2-trit 编码上的 9 例常规模拟器及
--           编码一致性证明（本件只覆盖嵌入像 {T₀,T₁} 的 4 例）。
--       两者齐备后方能陈述类级等式，独立批，未排期。
-- (ii)  BS-emb∘BS-dec 仅在像上恒等（BS-emb-dec-image 的假设形）：T₂ 上的
--       三值计算能力（三值逻辑谓词、平衡三进制算术）不被布尔片段吸收，
--       本互模拟对其无断言——「三进制不绕过 P/NP」论断仅覆盖**布尔问题
--       的嵌入编码**：其多项式性在三进制门模型下保持（§4/§5 已闭合）。
-- (iii) 「判定器可由 TM 实现」——函数层 → 图灵机层编码桥，同 PClass §6(i)
--       立界（Church-Turing 型深件，独立批）。
-- (iv)  计账口径：steps 为函数内部精确账（TimeBound §8(ii) 同口径）；
--       渐近 Big-O 层未设，本件的「多项式性保持」是等式级陈述
--       （steps ≡ size ≤ p n），强于渐近陈述。
-- (v)   XOR 由 AND/OR/NOT 的标准表达（xor(a,b) = or(and(a,¬b),and(¬a,b))）
--       与规模常数比较——工程扩展件，未排期。

-- 0 postulate / 0 hole / 0 Terminate-check 溢出。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
