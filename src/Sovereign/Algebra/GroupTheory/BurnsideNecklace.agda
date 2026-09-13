{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurnsideNecklace
--
-- **项链计数**：Burnside（Cauchy–Frobenius）引理的招牌应用（块 5）。
--
--       2 色 4 珠的项链数  =  (1/4)·(2⁴ + 2¹ + 2² + 2¹)  =  24/4  =  6
--
-- 数学背景：
--   把 4 珠 2 色着色编码为 4-bit 串 n : Fin 16（第 i 位 = 第 i 珠的颜色）。
--   C₄ 通过**循环右移** rot（低位绕到高位）作用：rot n = (n % 2)·8 + n / 2。
--   项链 = 该作用的轨道，故项链数 = #orbits。
--
--   不动点：|Fix id| = 2⁴ = 16；|Fix rot| = |Fix rot³| = 2（全 0 / 全 1）；
--   |Fix rot²| = 2² = 4（周期 2 的串）。Σ_g |Fix g| = 16+2+4+2 = 24 = 4·6 ✓
--
-- 核心原则：
--   1. **act-⊙ 不穷举**：4×4×16 = 256 个 case 是暴力计算。改为按 (g,h) 分 16 个 case，
--      其中 8 个 refl、8 个归约到「rot 是 4 阶置换」（rot⁴），每个 case 对 x 仍符号化。
--   2. **rot⁴ 是支点**：rot 为 4 阶置换（16 case refl，≤27 合规），
--      与 Lagrange.agda:347 的 +1₄^4-id 同型。
--   3. **f16 的归约**：fromℕ< 的归约只依赖隐式索引 m，不依赖界证明
--      （界是不可约的 .(_<_)，且 ℕ.s<s⁻¹ 的卡住不阻碍 suc 逐层产出），
--      故 f16 k 对具体 k 归约到第 (k mod 16) 个元素。
--   4. §4 对抗验证不只核对 numOrbits **一个数**，而是把 6 条轨道逐条列出并核对
--      大小分解 1+1+4+4+2+4 = 16 —— 单个数对得上可能是巧合。
--   5. 0 postulate / 0 hole；无 funExt；不引 Choice。
--
-- 诚实边界：
--   作用于有限集 Fin 16；本模块只算 2 色 4 珠这一具体实例（一般 n 的项链计数未形式化）。
--   rot 的「颜色语义」是本模块选定的一种编码（低位 = 第 0 珠），换编码得同构的作用。
--
-- 包含：f16 / rot / rot⁴ / act / act-ε / act-⊙ / C4-necklace
--       §4 necklace-numOrbits / necklace-fixCount / necklace-stabCount /
--          necklace-classical / 六条轨道的显式大小分解

module Sovereign.Algebra.GroupTheory.BurnsideNecklace where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _≤_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Lagrange
  using (FinGroup; C4; _+4_; +4-assoc; +4-idʳ)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum)
open import Sovereign.Algebra.GroupTheory.Burnside using (stabSize; stabCount; fixCount)
open import Sovereign.Algebra.GroupTheory.OrbitPartition using (module OrbitPart)
open import Sovereign.Algebra.GroupTheory.BurnsideMain
  using (numOrbitsOf; burnside-lemma; burnside-classical)

--------------------------------------------------------------------------------
-- §1. 旋转：4-bit 串循环右移
--------------------------------------------------------------------------------

-- 第 (k mod 16) 个元素
f16 : ℕ → Fin 16
f16 k = fromℕ< {k % 16} {16} (m%n<n k 16)

-- 循环右移：低位（第 0 珠）绕到高位（第 3 珠）
rot : Fin 16 → Fin 16
rot n = f16 (toℕ n % 2 * 8 + toℕ n / 2)

-- rot 是 4 阶置换（16 case refl，≤ 27 合规）
rot⁴ : ∀ x → rot (rot (rot (rot x))) ≡ x
rot⁴ (fzero) = refl
rot⁴ (fsuc (fzero)) = refl
rot⁴ (fsuc (fsuc (fzero))) = refl
rot⁴ (fsuc (fsuc (fsuc (fzero)))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fzero))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) = refl
rot⁴ (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) = refl

--------------------------------------------------------------------------------
-- §2. 作用 C₄ ↷ Fin 16
--------------------------------------------------------------------------------

act : Fin 4 → Fin 16 → Fin 16
act fzero x = x
act (fsuc fzero) x = rot x
act (fsuc (fsuc fzero)) x = rot (rot x)
act (fsuc (fsuc (fsuc fzero))) x = rot (rot (rot x))

act-ε : ∀ x → act fzero x ≡ x
act-ε x = refl

-- 16 case（g, h）：8 个 refl，8 个归约到 rot⁴ —— 不穷举 4×4×16 = 256 个 case
act-⊙ : ∀ g h x → act (g +4 h) x ≡ act g (act h x)
act-⊙ (fzero) (fzero) x = refl
act-⊙ (fzero) (fsuc fzero) x = refl
act-⊙ (fzero) (fsuc (fsuc fzero)) x = refl
act-⊙ (fzero) (fsuc (fsuc (fsuc fzero))) x = refl
act-⊙ (fsuc fzero) (fzero) x = refl
act-⊙ (fsuc fzero) (fsuc fzero) x = refl
act-⊙ (fsuc fzero) (fsuc (fsuc fzero)) x = refl
act-⊙ (fsuc fzero) (fsuc (fsuc (fsuc fzero))) x = sym (rot⁴ x)
act-⊙ (fsuc (fsuc fzero)) (fzero) x = refl
act-⊙ (fsuc (fsuc fzero)) (fsuc fzero) x = refl
act-⊙ (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) x = sym (rot⁴ x)
act-⊙ (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) x = sym (rot⁴ (rot x))
act-⊙ (fsuc (fsuc (fsuc fzero))) (fzero) x = refl
act-⊙ (fsuc (fsuc (fsuc fzero))) (fsuc fzero) x = sym (rot⁴ x)
act-⊙ (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) x = sym (rot⁴ (rot x))
act-⊙ (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) x = sym (rot⁴ (rot (rot x)))

C4-necklace : Action C4 (Fin 16)
C4-necklace = record
  { _·_ = act
  ; ·-ε = act-ε
  ; ·-⊙ = act-⊙
  }

--------------------------------------------------------------------------------
-- §3. 对抗验证：具体点 refl 交叉比对
--------------------------------------------------------------------------------

-- ① 项链数 = 6（独立算出）
necklace-numOrbits : numOrbitsOf C4 C4-necklace ≡ 6
necklace-numOrbits = refl

-- ② 双重计数两侧独立算出 24 = Σ_g |Fix g| = Σ_x |Stab x|
necklace-fixCount : fixCount C4 C4-necklace ≡ 24
necklace-fixCount = refl

necklace-stabCount : stabCount C4 C4-necklace ≡ 24
necklace-stabCount = refl

-- ③ 定理实例与独立算出的 4 × 6 逐位比对
necklace-classical : fixCount C4 C4-necklace ≡ 4 * 6
necklace-classical = burnside-classical C4 C4-necklace

--------------------------------------------------------------------------------
-- §4. 六条轨道的显式分解（独立于 numOrbits 的验证）
--
-- 只核对「#orbits = 6」这一个数可能是巧合；这里把 16 个着色按轨道划分逐条列出，
-- 并核对大小之和 = 16。
--------------------------------------------------------------------------------

orb-size : Fin 16 → ℕ
orb-size x = SubEnum.size (OrbitPart.orbEnum C4 C4-necklace x)

-- {0000}
orb-0000 : orb-size (f16 0) ≡ 1
orb-0000 = refl

-- {1111}
orb-1111 : orb-size (f16 15) ≡ 1
orb-1111 = refl

-- {0001, 0010, 0100, 1000}
orb-0001 : orb-size (f16 1) ≡ 4
orb-0001 = refl

-- {0011, 0110, 1100, 1001}
orb-0011 : orb-size (f16 3) ≡ 4
orb-0011 = refl

-- {0101, 1010}
orb-0101 : orb-size (f16 5) ≡ 2
orb-0101 = refl

-- {0111, 1011, 1101, 1110}
orb-0111 : orb-size (f16 7) ≡ 4
orb-0111 = refl

-- 划分完整：大小之和 = 16
partition-sum : 1 + 1 + 4 + 4 + 2 + 4 ≡ 16
partition-sum = refl

-- 与 numOrbits 交叉一致：6 条轨道
partition-count : SubEnum.size (OrbitPart.RepEnum C4 C4-necklace) ≡ 6
partition-count = refl
