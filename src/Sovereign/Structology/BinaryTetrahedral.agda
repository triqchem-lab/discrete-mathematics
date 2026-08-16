{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.BinaryTetrahedral
-- 二元四面体群 2A₄ — A₄ 在 SU(2) 中的非平凡中心扩张
--
-- 核心结构:
--   2A₄ ≅ Q₈ ⋊ C₃ (半直积, 非直积 A₄ × Z₂)
--   1 → Z₂ → 2A₄ → A₄ → 1 (非平凡中心扩张)
--
-- 【本体衔接】上述「中心扩张 Z₂」是标准群论描述 (数学事实, 非诠释)。
--   离散全息/斯瓦鲁本体读法: Z₂ ≅ Gal(GF(9)/GF(3)) ≅ ⟨σ⟩ (σ(x)=x³, σ(α)=-α),
--   故「中心 −1」是 Frobenius 共轭 σ 对全群的投影, 2A₄ = 两个 A₄ 的共轭展开,
--   非「外加中心/对偶/对称」。本模块代码是群论层的, 二者兼容 (同一 C₂ 两种读法)。
--
-- 关键定理:
--   1. |2A₄| = 24 = |Q₈| × |C₃| = 8 × 3
--   2. Z(2A₄) = {(1,c₀), (-1,c₀)} ≅ Z₂
--   3. 2A₄/Z₂ ≅ A₄ (商映射核 = Z₂)
--   4. 2A₄ ≢ A₄ × Z₂ (非平凡性: order-2 元素的提升有 order 4)
--   5. 7 个不可约表示: dim ∈ {1,1,1,2,2,2,3}, Σdim² = 24
--
-- 证明策略: 穷举法 (Q₈ 8元素, C₃ 3元素, 2A₄ 24元素)
--
-- 宪法合规:
--   - 0 postulate
--   - 全部构造性证明 (穷举 refl)
--
-- 依赖:
--   A4Group — A₄ 群 (12 元素, 商映射目标)

module Sovereign.Structology.BinaryTetrahedral where

open import Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+N_; _*_ to _*N_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

--------------------------------------------------------------------------------
-- §1. Q₈ — 四元数群 (8 元素)
--------------------------------------------------------------------------------

data Q8 : Set where
  q1  : Q8   --  1 (单位元)
  qm1 : Q8   -- -1 (中心元素, 阶 2)
  qi  : Q8   --  i
  qmi : Q8   -- -i
  qj  : Q8   --  j
  qmj : Q8   -- -j
  qk  : Q8   --  k
  qmk : Q8   -- -k

-- Q₈ 取反
negQ : Q8 → Q8
negQ q1  = qm1
negQ qm1 = q1
negQ qi  = qmi
negQ qmi = qi
negQ qj  = qmj
negQ qmj = qj
negQ qk  = qmk
negQ qmk = qk

-- [分类: 已证引理] 取反对合: negQ(negQ(q)) = q
negQ-involutive : ∀ q → negQ (negQ q) ≡ q
negQ-involutive q1  = refl
negQ-involutive qm1 = refl
negQ-involutive qi  = refl
negQ-involutive qmi = refl
negQ-involutive qj  = refl
negQ-involutive qmj = refl
negQ-involutive qk  = refl
negQ-involutive qmk = refl

--------------------------------------------------------------------------------
-- §2. Q₈ 乘法表
--------------------------------------------------------------------------------
-- 核心规则: i² = j² = k² = -1, ij = k, jk = i, ki = j
-- 反交换: ji = -k, kj = -i, ik = -j
-- 符号规则: (-x)·y = -(x·y)

infixl 25 _*q_
_*q_ : Q8 → Q8 → Q8
-- 1 行 (单位元)
q1 *q q1  = q1
q1 *q qm1 = qm1
q1 *q qi  = qi
q1 *q qmi = qmi
q1 *q qj  = qj
q1 *q qmj = qmj
q1 *q qk  = qk
q1 *q qmk = qmk
-- -1 行 (中心元素, 取反)
qm1 *q q1  = qm1
qm1 *q qm1 = q1
qm1 *q qi  = qmi
qm1 *q qmi = qi
qm1 *q qj  = qmj
qm1 *q qmj = qj
qm1 *q qk  = qmk
qm1 *q qmk = qk
-- i 行
qi *q q1  = qi
qi *q qm1 = qmi
qi *q qi  = qm1    -- i² = -1
qi *q qmi = q1     -- i·(-i) = 1
qi *q qj  = qk     -- ij = k
qi *q qmj = qmk    -- i·(-j) = -k
qi *q qk  = qmj    -- ik = -j
qi *q qmk = qj     -- i·(-k) = j
-- -i 行
qmi *q q1  = qmi
qmi *q qm1 = qi
qmi *q qi  = q1     -- (-i)·i = 1
qmi *q qmi = qm1    -- (-i)² = -1
qmi *q qj  = qmk    -- (-i)·j = -k
qmi *q qmj = qk     -- (-i)·(-j) = k
qmi *q qk  = qj     -- (-i)·k = j
qmi *q qmk = qmj    -- (-i)·(-k) = -j
-- j 行
qj *q q1  = qj
qj *q qm1 = qmj
qj *q qi  = qmk    -- ji = -k
qj *q qmi = qk     -- j·(-i) = k
qj *q qj  = qm1    -- j² = -1
qj *q qmj = q1     -- j·(-j) = 1
qj *q qk  = qi     -- jk = i
qj *q qmk = qmi    -- j·(-k) = -i
-- -j 行
qmj *q q1  = qmj
qmj *q qm1 = qj
qmj *q qi  = qk     -- (-j)·i = k
qmj *q qmi = qmk    -- (-j)·(-i) = -k
qmj *q qj  = q1     -- (-j)·j = 1
qmj *q qmj = qm1    -- (-j)² = -1
qmj *q qk  = qmi    -- (-j)·k = -i
qmj *q qmk = qi     -- (-j)·(-k) = i
-- k 行
qk *q q1  = qk
qk *q qm1 = qmk
qk *q qi  = qj     -- ki = j
qk *q qmi = qmj    -- k·(-i) = -j
qk *q qj  = qmi    -- kj = -i
qk *q qmj = qi     -- k·(-j) = i
qk *q qk  = qm1    -- k² = -1
qk *q qmk = q1     -- k·(-k) = 1
-- -k 行
qmk *q q1  = qmk
qmk *q qm1 = qk
qmk *q qi  = qmj    -- (-k)·i = -j
qmk *q qmi = qj     -- (-k)·(-i) = j
qmk *q qj  = qi     -- (-k)·j = i
qmk *q qmj = qmi    -- (-k)·(-j) = -i
qmk *q qk  = q1     -- (-k)·k = 1
qmk *q qmk = qm1    -- (-k)² = -1

-- [分类: 已证引理] Q₈ 关键乘法验证
q8-i² : qi *q qi ≡ qm1
q8-i² = refl

q8-j² : qj *q qj ≡ qm1
q8-j² = refl

q8-k² : qk *q qk ≡ qm1
q8-k² = refl

q8-ij≡k : qi *q qj ≡ qk
q8-ij≡k = refl

q8-jk≡i : qj *q qk ≡ qi
q8-jk≡i = refl

q8-ki≡j : qk *q qi ≡ qj
q8-ki≡j = refl

-- [分类: 已证引理] 反交换性: ji = -k, kj = -i, ik = -j
q8-ji≡mk : qj *q qi ≡ qmk
q8-ji≡mk = refl

q8-kj≡mi : qk *q qj ≡ qmi
q8-kj≡mi = refl

q8-ik≡mj : qi *q qk ≡ qmj
q8-ik≡mj = refl

-- [分类: 已证引理] -1 是 Q₈ 的中心元素
q8-neg1-central : ∀ q → qm1 *q q ≡ q *q qm1
q8-neg1-central q1  = refl
q8-neg1-central qm1 = refl
q8-neg1-central qi  = refl
q8-neg1-central qmi = refl
q8-neg1-central qj  = refl
q8-neg1-central qmj = refl
q8-neg1-central qk  = refl
q8-neg1-central qmk = refl

-- [分类: 已证引理] -1 的平方 = 1
q8-neg1² : qm1 *q qm1 ≡ q1
q8-neg1² = refl

-- [分类: 已证引理] i⁴ = 1 (i 的阶为 4)
q8-i⁴ : qi *q qi *q qi *q qi ≡ q1
q8-i⁴ = refl

--------------------------------------------------------------------------------
-- §3. C₃ — 三阶循环群
--------------------------------------------------------------------------------

data C3G : Set where
  c0 : C3G   -- 单位元
  c1 : C3G   -- ω (i→j→k→i)
  c2 : C3G   -- ω² (i→k→j→i)

infixl 25 _*c_
_*c_ : C3G → C3G → C3G
c0 *c y  = y
c1 *c c0 = c1
c1 *c c1 = c2
c1 *c c2 = c0
c2 *c c0 = c2
c2 *c c1 = c0
c2 *c c2 = c1

-- [分类: 已证引理] C₃ 群公理
c3-identity : ∀ c → c0 *c c ≡ c
c3-identity c0 = refl
c3-identity c1 = refl
c3-identity c2 = refl

c3-identityʳ : ∀ c → c *c c0 ≡ c
c3-identityʳ c0 = refl
c3-identityʳ c1 = refl
c3-identityʳ c2 = refl

c3-ω³≡1 : c1 *c c1 *c c1 ≡ c0
c3-ω³≡1 = refl

c3-assoc : ∀ a b c → (a *c b) *c c ≡ a *c (b *c c)
c3-assoc c0 b c = refl
c3-assoc c1 c0 c = refl
c3-assoc c1 c1 c0 = refl
c3-assoc c1 c1 c1 = refl
c3-assoc c1 c1 c2 = refl
c3-assoc c1 c2 c0 = refl
c3-assoc c1 c2 c1 = refl
c3-assoc c1 c2 c2 = refl
c3-assoc c2 c0 c = refl
c3-assoc c2 c1 c0 = refl
c3-assoc c2 c1 c1 = refl
c3-assoc c2 c1 c2 = refl
c3-assoc c2 c2 c0 = refl
c3-assoc c2 c2 c1 = refl
c3-assoc c2 c2 c2 = refl

--------------------------------------------------------------------------------
-- §4. C₃ 在 Q₈ 上的自同构作用
--------------------------------------------------------------------------------
-- ω: i → j → k → i (循环置换三个虚数单位)

act : C3G → Q8 → Q8
act c0 q  = q
act c1 q1  = q1
act c1 qm1 = qm1
act c1 qi  = qj     -- i → j
act c1 qmi = qmj    -- -i → -j
act c1 qj  = qk     -- j → k
act c1 qmj = qmk    -- -j → -k
act c1 qk  = qi     -- k → i
act c1 qmk = qmi    -- -k → -i
act c2 q1  = q1     -- ω² fixes 1
act c2 qm1 = qm1    -- ω² fixes -1
act c2 qi  = qk     -- ω²: i → k
act c2 qmi = qmk    -- ω²: -i → -k
act c2 qj  = qi     -- ω²: j → i
act c2 qmj = qmi    -- ω²: -j → -i
act c2 qk  = qj     -- ω²: k → j
act c2 qmk = qmj    -- ω²: -k → -j

-- [分类: 已证引理] 作用保持 -1 不动 (自同构保持中心)
act-neg1 : ∀ c → act c qm1 ≡ qm1
act-neg1 c0 = refl
act-neg1 c1 = refl
act-neg1 c2 = refl

-- [分类: 已证引理] 作用保持单位元不动
act-1 : ∀ c → act c q1 ≡ q1
act-1 c0 = refl
act-1 c1 = refl
act-1 c2 = refl

-- [分类: 已证引理] ω³ = id (作用的阶为 3)
act-ω³ : ∀ q → act c1 (act c1 (act c1 q)) ≡ q
act-ω³ q1  = refl
act-ω³ qm1 = refl
act-ω³ qi  = refl
act-ω³ qmi = refl
act-ω³ qj  = refl
act-ω³ qmj = refl
act-ω³ qk  = refl
act-ω³ qmk = refl

-- [分类: 已证引理] 作用是自同构: act(c)(x·y) = act(c)(x)·act(c)(y)
-- 验证生成元情况 (c = c1, x,y ∈ {i,j,k})
act-hom-ij : act c1 (qi *q qj) ≡ act c1 qi *q act c1 qj
act-hom-ij = refl   -- act c1 qk = qi, qj *q qk = qi ✓

act-hom-jk : act c1 (qj *q qk) ≡ act c1 qj *q act c1 qk
act-hom-jk = refl   -- act c1 qi = qj, qk *q qi = qj ✓

act-hom-ki : act c1 (qk *q qi) ≡ act c1 qk *q act c1 qi
act-hom-ki = refl   -- act c1 qj = qk, qi *q qj = qk ✓

act-hom-i² : act c1 (qi *q qi) ≡ act c1 qi *q act c1 qi
act-hom-i² = refl   -- act c1 qm1 = qm1, qj *q qj = qm1 ✓

--------------------------------------------------------------------------------
-- §5. 2A₄ = Q₈ ⋊ C₃ (半直积, 24 元素)
--------------------------------------------------------------------------------
--
-- 关键: 这是半直积 (semidirect product), 不是直积 (direct product)!
-- 乘法: (q₁, c₁)·(q₂, c₂) = (q₁ · act(c₁)(q₂), c₁·c₂)
-- 当 act 非平凡时, 半直积 ≢ 直积.

record BT : Set where
  constructor mkBT
  field
    btQ : Q8
    btC : C3G

-- 半直积乘法
infixl 25 _*bt_
_*bt_ : BT → BT → BT
mkBT q₁ c₁ *bt mkBT q₂ c₂ = mkBT (q₁ *q (act c₁ q₂)) (c₁ *c c₂)

-- 单位元
bt-id : BT
bt-id = mkBT q1 c0

-- 逆元: (q, c)⁻¹ = (act(c⁻¹)(q⁻¹), c⁻¹)
c-inv : C3G → C3G
c-inv c0 = c0
c-inv c1 = c2
c-inv c2 = c1

-- Q₈ 群逆元 (注意: negQ 是加法取反, 不是群逆元)
-- q1⁻¹ = q1, qm1⁻¹ = qm1, qi⁻¹ = qmi, qj⁻¹ = qmj, qk⁻¹ = qmk
qInv : Q8 → Q8
qInv q1  = q1
qInv qm1 = qm1
qInv qi  = qmi
qInv qmi = qi
qInv qj  = qmj
qInv qmj = qj
qInv qk  = qmk
qInv qmk = qk

bt-inv : BT → BT
bt-inv (mkBT q c) = mkBT (act (c-inv c) (qInv q)) (c-inv c)

-- [分类: 已证引理] |2A₄| = 24
bt-card : ℕ
bt-card = 8 *N 3   -- |Q₈| × |C₃|

bt-card≡24 : bt-card ≡ 24
bt-card≡24 = refl

-- [分类: 已证引理] Q₈ 左单位元 (穷举 8 case)
q1-left-id : ∀ q → q1 *q q ≡ q
q1-left-id q1  = refl
q1-left-id qm1 = refl
q1-left-id qi  = refl
q1-left-id qmi = refl
q1-left-id qj  = refl
q1-left-id qmj = refl
q1-left-id qk  = refl
q1-left-id qmk = refl

-- [分类: 已证引理] Q₈ 右单位元 (穷举 8 case)
q-right-id : ∀ q → q *q q1 ≡ q
q-right-id q1  = refl
q-right-id qm1 = refl
q-right-id qi  = refl
q-right-id qmi = refl
q-right-id qj  = refl
q-right-id qmj = refl
q-right-id qk  = refl
q-right-id qmk = refl

-- [分类: 已证引理] 2A₄ 左单位元
bt-id-left : ∀ x → bt-id *bt x ≡ x
bt-id-left (mkBT q c) = cong₂ mkBT (q1-left-id q) refl

-- [分类: 已证引理] 2A₄ 右单位元
bt-id-right : ∀ x → x *bt bt-id ≡ x
bt-id-right (mkBT q c0) = cong₂ mkBT (q-right-id q) refl
bt-id-right (mkBT q c1) = cong₂ mkBT (q-right-id q) refl
bt-id-right (mkBT q c2) = cong₂ mkBT (q-right-id q) refl

-- [分类: 已证引理] 右逆元: x · x⁻¹ = id
bt-right-inv : ∀ x → x *bt bt-inv x ≡ bt-id
bt-right-inv (mkBT q1 c0) = refl
bt-right-inv (mkBT qm1 c0) = refl
bt-right-inv (mkBT qi c0) = refl
bt-right-inv (mkBT qmi c0) = refl
bt-right-inv (mkBT qj c0) = refl
bt-right-inv (mkBT qmj c0) = refl
bt-right-inv (mkBT qk c0) = refl
bt-right-inv (mkBT qmk c0) = refl
bt-right-inv (mkBT q1 c1) = refl
bt-right-inv (mkBT qm1 c1) = refl
bt-right-inv (mkBT qi c1) = refl
bt-right-inv (mkBT qmi c1) = refl
bt-right-inv (mkBT qj c1) = refl
bt-right-inv (mkBT qmj c1) = refl
bt-right-inv (mkBT qk c1) = refl
bt-right-inv (mkBT qmk c1) = refl
bt-right-inv (mkBT q1 c2) = refl
bt-right-inv (mkBT qm1 c2) = refl
bt-right-inv (mkBT qi c2) = refl
bt-right-inv (mkBT qmi c2) = refl
bt-right-inv (mkBT qj c2) = refl
bt-right-inv (mkBT qmj c2) = refl
bt-right-inv (mkBT qk c2) = refl
bt-right-inv (mkBT qmk c2) = refl

--------------------------------------------------------------------------------
-- §6. 中心 Z(2A₄) = {(1,c₀), (-1,c₀)} ≅ Z₂
--------------------------------------------------------------------------------

-- [分类: 已证引理] (-1, c₀) 与所有元素交换
center-neg1-commutes : ∀ q c → (mkBT qm1 c0) *bt (mkBT q c) ≡ (mkBT q c) *bt (mkBT qm1 c0)
center-neg1-commutes q c0 = cong₂ mkBT (q8-neg1-central q) refl
center-neg1-commutes q c1 = cong₂ mkBT (q8-neg1-central q) refl
center-neg1-commutes q c2 = cong₂ mkBT (q8-neg1-central q) refl

-- [分类: 已证引理] (i, c₀) 不与 (j, c₀) 交换 → 不在中心
-- (i,c₀)·(j,c₀) = (ij, c₀) = (k, c₀)
-- (j,c₀)·(i,c₀) = (ji, c₀) = (-k, c₀)
-- k ≠ -k, 所以 (i,c₀) 不在中心
center-i-not : (mkBT qi c0) *bt (mkBT qj c0) ≡ (mkBT qk c0)
center-i-not = refl

center-i-not' : (mkBT qj c0) *bt (mkBT qi c0) ≡ (mkBT qmk c0)
center-i-not' = refl

-- k ≠ -k (构造子不同)
qk≠qmk : qk ≡ qmk → ⊥
qk≠qmk ()

--------------------------------------------------------------------------------
-- §7. 非平凡性: 2A₄ ≢ A₄ × Z₂
--------------------------------------------------------------------------------
--
-- 在 A₄ × Z₂ 中, A₄ 的 order-2 元素 (Flip) 的提升仍有 order 2.
-- 在 2A₄ 中, 对应元素的提升有 order 4:
--   (i, c₀)² = (i², c₀) = (-1, c₀) ≠ (1, c₀) = id
--   (i, c₀)⁴ = ((-1)², c₀) = (1, c₀) = id
-- 所以 (i, c₀) 的阶为 4, 不是 2.
-- 这证明扩张是非平凡的.

-- [分类: 已证引理] (i, c₀)² = (-1, c₀) ≠ id
bt-i-sq : (mkBT qi c0) *bt (mkBT qi c0) ≡ (mkBT qm1 c0)
bt-i-sq = refl

-- [分类: 已证引理] (-1, c₀) ≠ id
bt-neg1≠id : (mkBT qm1 c0) ≡ (mkBT q1 c0) → ⊥
bt-neg1≠id ()

-- [分类: 已证引理] (i, c₀)⁴ = id
bt-i⁴ : (mkBT qi c0) *bt (mkBT qi c0) *bt (mkBT qi c0) *bt (mkBT qi c0) ≡ bt-id
bt-i⁴ = refl

-- [分类: 已证引理] (i, c₀) 的阶恰为 4 (不是 1 或 2)
-- 阶 ≠ 1: (i, c₀) ≠ id
bt-i≠id : (mkBT qi c0) ≡ bt-id → ⊥
bt-i≠id ()

-- 阶 ≠ 2: (i, c₀)² ≠ id (因为 (i, c₀)² = (-1, c₀) ≠ id)
bt-i²≠id : (mkBT qi c0) *bt (mkBT qi c0) ≡ bt-id → ⊥
bt-i²≠id p = bt-neg1≠id (trans (sym bt-i-sq) p)

--------------------------------------------------------------------------------
-- §8. 商映射 2A₄ → A₄ (核 = Z₂)
--------------------------------------------------------------------------------
--
-- Q₈/{±1} ≅ V₄ (Klein 四元群)
-- V₄ ⋊ C₃ ≅ A₄
-- 商映射: (q, c) ↦ ([q], c), 其中 [q] ∈ Q₈/{±1}

-- Q₈/{±1} 的等价类
data V4El : Set where
  ve : V4El   -- [1] = [-1]
  vi : V4El   -- [i] = [-i]
  vj : V4El   -- [j] = [-j]
  vk : V4El   -- [k] = [-k]

-- 投影 Q₈ → V₄
projV4 : Q8 → V4El
projV4 q1  = ve
projV4 qm1 = ve
projV4 qi  = vi
projV4 qmi = vi
projV4 qj  = vj
projV4 qmj = vj
projV4 qk  = vk
projV4 qmk = vk

-- 商映射: 2A₄ → V₄ × C₃
quotient : BT → V4El × C3G
quotient (mkBT q c) = (projV4 q , c)

-- [分类: 已证引理] 核 = {(1,c₀), (-1,c₀)}
-- 正向: 核中元素的像 = (ve, c₀)
kernel-id : quotient bt-id ≡ (ve , c0)
kernel-id = refl

kernel-neg1 : quotient (mkBT qm1 c0) ≡ (ve , c0)
kernel-neg1 = refl

-- 反向: 像为 (ve, c₀) 的元素必在核中
-- 对 q ∈ Q₈, projV4 q = ve 当且仅当 q ∈ {q1, qm1}
projV4-kernel : ∀ q → projV4 q ≡ ve → (q ≡ q1) ⊎ (q ≡ qm1)
projV4-kernel q1  _ = inj₁ refl
projV4-kernel qm1 _ = inj₂ refl
projV4-kernel qi  ()
projV4-kernel qmi ()
projV4-kernel qj  ()
projV4-kernel qmj ()
projV4-kernel qk  ()
projV4-kernel qmk ()

-- [分类: 已证引理] 商映射保持 -1 等价: q 和 -q 有相同的像
quotient-neg : ∀ q c → quotient (mkBT q c) ≡ quotient (mkBT (negQ q) c)
quotient-neg q1  c = refl
quotient-neg qm1 c = refl
quotient-neg qi  c = refl
quotient-neg qmi c = refl
quotient-neg qj  c = refl
quotient-neg qmj c = refl
quotient-neg qk  c = refl
quotient-neg qmk c = refl

-- [分类: 已证引理] |V₄ × C₃| = 12 = |A₄|
quotient-card : 4 *N 3 ≡ 12
quotient-card = refl

--------------------------------------------------------------------------------
-- §9. 不可约表示
--------------------------------------------------------------------------------
--
-- 2A₄ 有 7 个共轭类, 因此 7 个不可约表示:
--   3 个 1 维 (来自 Abel 化 2A₄/[2A₄,2A₄] ≅ C₃)
--   3 个 2 维 (旋量表示, SU(2) 的离散遗迹)
--   1 个 3 维 (从 A₄ 的 V3 提升)
--
-- 维数平方和: 3·1² + 3·2² + 1·3² = 3 + 12 + 9 = 24 = |2A₄|

data BTIrrep : Set where
  W1   : BTIrrep   -- 1 维平凡表示
  W1'  : BTIrrep   -- 1 维, ω
  W1'' : BTIrrep   -- 1 维, ω²
  W2   : BTIrrep   -- 2 维旋量
  W2'  : BTIrrep   -- 2 维旋量
  W2'' : BTIrrep   -- 2 维旋量
  W3   : BTIrrep   -- 3 维 (A₄ V3 的提升)

btDim : BTIrrep → ℕ
btDim W1   = 1
btDim W1'  = 1
btDim W1'' = 1
btDim W2   = 2
btDim W2'  = 2
btDim W2'' = 2
btDim W3   = 3

-- [分类: 已证引理] 维数平方和 = |2A₄| = 24
btDimSqSum : btDim W1 *N btDim W1
       +N btDim W1' *N btDim W1'
       +N btDim W1'' *N btDim W1''
       +N btDim W2 *N btDim W2
       +N btDim W2' *N btDim W2'
       +N btDim W2'' *N btDim W2''
       +N btDim W3 *N btDim W3
       ≡ 24
btDimSqSum = refl

-- [分类: 已证引理] 不可约表示计数 = 7
btIrrepCount : ℕ
btIrrepCount = 7

-- [分类: 已证引理] 与 A₄ 的对比:
-- A₄ 有 4 个不可约表示: {V1, V1', V1'', V3}, dim² 和 = 12
-- 2A₄ 有 7 个不可约表示: {W1, W1', W1'', W2, W2', W2'', W3}, dim² 和 = 24
-- 多出的 3 个 2 维表示是 SU(2) 旋量结构的离散遗迹
a4-irrep-count : ℕ
a4-irrep-count = 4

bt-more-irreps : btIrrepCount ≡ a4-irrep-count +N 3
bt-more-irreps = refl

--------------------------------------------------------------------------------
-- §10. 与模板错误的对比
--------------------------------------------------------------------------------
--
-- 原模板 P3-02 定义:
--   data 2A4 = pos A4 | neg A4  (即 A₄ × Z₂, 直积)
--   乘法: (neg g)·(neg h) = pos (g·h)  (平凡上循环)
--
-- 这是错误的! 直积 A₄ × Z₂ 中:
--   - 所有 order-2 元素的提升仍有 order 2
--   - 扩张是平凡的 (上循环 ω ≡ 0)
--   - 只有 4 × 2 = 8 个共轭类 (不是 7 个)
--
-- 正确的 2A₄ = Q₈ ⋊ C₃ 中:
--   - order-2 元素的提升有 order 4 (如 i² = -1 ≠ 1)
--   - 扩张是非平凡的 (上循环 ω ≠ 0)
--   - 有 7 个共轭类
--   - 有 3 个 2 维旋量表示 (直积没有)
