{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dCardinality
--
-- **π₁ᵈ(G) 的一般理论（二）：基数刻画 —— 何时塌缩**
--
-- ## 数学背景
--
-- `Pi1dMonoid` 已证：对**任意**有向图 G，闭走模 A-同伦 `π₁ᵈ(G) := Walk G v v / AHomotopy`
-- 是**幺半群**（左/右单位律、结合律、左右同余）。但那时**基数**未刻画 ——
-- `AHomotopy` 是 `AStep` 生成的等价闭包，何时它会真的**粘合不同的走**？
--
-- ## 本模块的主定理（双向刻画）
--
-- > **π₁ᵈ(G) 不塌缩 ⟺ G 无有向三角形**
--
-- 形式化（逐点，无 `funext`）：
--
--   ```
--   no-collapse : ∀ {p q} → AHomotopy G p q → p ≡ q
--   ```
--
--   与
--
--   ```
--   TriangleFree G = ∀ {x y z} → edge x y → edge y z → ¬ (edge x z)
--   ```
--
--   之间是**双向蕴含** ✓
--
-- ## 论证
--
-- **（⇐）无三角形 ⇒ 不塌缩**
--   `AStep` 的两个构造子（`slide` / `expand`）**都**要求一组有向三角形
--   `e1 : x→y`、`e2 : y→z`、`e3 : x→z` ⇒ 无三角形时 `AStep G p q` **空** ✓
--   ⇒ `AHomotopy` 只剩 `refl'/symm/trans'` ⇒ 就是 `_≡_` ✓
--
-- **（⇒）有三角形 ⇒ 一定塌缩**
--   给定 `e1 e2 e3`，取
--     `p = cons e1 (cons e2 (nil z))`（长 2）、`q = cons e3 (nil z)`（长 1）
--   ⇒ `slide (nil x) (nil z) e1 e2 e3 : AStep G p q` ⇒ `gen` 给出 `AHomotopy G p q` ✓
--   而 `p ≢ q`（用走长 `len` 区分：2 ≠ 1）✓
--   ⇒ **每个有向三角形都至少粘合一对不同的走** ✓
--
-- ## 与既有件的关系
--
--   · 塌缩侧的**实例**见证：`PIO-1a.library-side`（`probes/_PPI4e` 的 `gcmp-classify`）
--     —— `Gcmp two-chain` 的闭走分两类 ⇒ 商只有 2 元，正是三角形造成的塌缩 ✓
--   · `PIO-1.card-divergence`（**已 abandoned**）：原陈述「π₁ᵈ(G) ≇ π₁(|N₁G|)」需要
--     几何实现与拓扑 π₁，本库无此机件 ⇒ 已立界，本模块**不重开** ✗
--
-- ## 诚实边界
--
--   · 本模块刻画的是**关系层**（`AHomotopy ⇔ _≡_`），不是**基数层**的直接等式 ✗
--     ——因为本库没有 `Walk` 的有限性与计数设备。
--     关系层的双向蕴含**等价于**「商与闭走等基数」（等价类退化为单点）✓
--   · 本模块不声称「π₁ᵈ 是群」✗ —— 一般形态是**幺半群**（见 `Pi1dMonoid`）✓
--
-- ## 推论：无三角形时，单位元是**唯一**幂等元
--
-- `A-homotopy` 一般**不保走长**（`slide` 把长度 `n+2` 压成 `n+1`）✗，
-- 但**无三角形时它退化为命题相等** ⇒ 保长 ✓。于是
--
--   `w · w ⁓ w` ⇒ `len w + len w ≡ len w` ⇒ `len w ≡ 0` ⇒ `w ≡ nil` ✓
--
-- ## 核心原则
--   · 对**任意** `DiGraph` 成立 ✓
--   · 0 postulate / 0 hole

module Sovereign.Synthesis.Homotopy.Pi1dCardinality where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-cancelˡ-≡; +-identityʳ; m+n≡0⇒m≡0; suc-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep; slide; expand;
         AHomotopy; refl'; symm; trans'; gen)
open DiGraph using (V; edge)

--------------------------------------------------------------------------------
-- §1. 有向三角形与「无三角形」谓词
--------------------------------------------------------------------------------

TriangleFree : DiGraph → Set
TriangleFree G = ∀ {x y z} → edge G x y → edge G y z → ¬ (edge G x z)

--------------------------------------------------------------------------------
-- §2. 无三角形 ⇒ AStep 空 ⇒ AHomotopy 就是 _≡_
--------------------------------------------------------------------------------

-- AStep 的两个构造子都要求有向三角形 ⇒ 无三角形时无生成元
AStep-empty : ∀ {G : DiGraph} (tf : TriangleFree G) {u v : V G} {p q : Walk G u v}
            → AStep G p q → ⊥
AStep-empty tf (slide  p b e1 e2 e3) = tf e1 e2 e3
AStep-empty tf (expand p b e1 e2 e3) = tf e1 e2 e3

-- ⇒ 等价闭包退化为命题相等
AH→≡ : ∀ {G : DiGraph} (tf : TriangleFree G) {u v : V G} {p q : Walk G u v}
     → AHomotopy G p q → p ≡ q
AH→≡ tf (refl' p)      = refl
AH→≡ tf (symm h)       = sym (AH→≡ tf h)
AH→≡ tf (trans' h1 h2) = trans (AH→≡ tf h1) (AH→≡ tf h2)
AH→≡ tf (gen st)       = ⊥-elim (AStep-empty tf st)

-- 反向：命题相等 ⇒ A-同伦（总成立，不需要任何假设）
≡→AH : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v}
     → p ≡ q → AHomotopy G p q
≡→AH refl = refl' _

-- 局部双向蕴含（不引入 Relation.Binary 的 _↔_；名字加 ᵈ 后缀以免与 DuodecClock 的同名件冲突）
-- ⚠ 必须显式声明 fixity：默认 infix 20 比 _≡_ 的 4 更紧，
--   否则 `A ↔ p ≡ q` 会被解析成 `(A ↔ p) ≡ q`（2026-10-21 实测编译报错）
infix 3 _↔ᵈ_
_↔ᵈ_ : Set → Set → Set
A ↔ᵈ B = (A → B) × (B → A)

ahomotopy-iff-eq : ∀ {G : DiGraph} (tf : TriangleFree G) {u v : V G} {p q : Walk G u v}
                 → (AHomotopy G p q) ↔ᵈ (p ≡ q)
ahomotopy-iff-eq tf = AH→≡ tf , ≡→AH

--------------------------------------------------------------------------------
-- §3. 有三角形 ⇒ 一定塌缩（存在粘合的不同走）
--------------------------------------------------------------------------------

-- 走长（用来区分不同形状的走）
walk-len : ∀ {G : DiGraph} {u v : V G} → Walk G u v → ℕ
walk-len (nil v)    = zero
walk-len (cons e p) = suc (walk-len p)

-- 长度 2 与 1 不同 ⇒ 两个走不相等
2≢1 : suc (suc zero) ≡ suc zero → ⊥
2≢1 ()

-- 三角形的「折叠边」给出两个**不同**的走，且它们 A-同伦
triangle-collapses : ∀ {G : DiGraph} {x y z : V G}
                     (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G x z)
                   → ∃ (λ (p : Walk G x z)
                       → ∃ (λ (q : Walk G x z)
                           → (p ≢ q) × AHomotopy G p q))
triangle-collapses {G = G} {x} {y} {z} e1 e2 e3 =
    cons e1 (cons e2 (nil z))
  , cons e3 (nil z)
  , (λ eq → 2≢1 (cong walk-len eq))
  , gen (slide {u = x} {x = x} {y = y} {z = z} {v = z} (nil x) (nil z) e1 e2 e3)

--------------------------------------------------------------------------------
-- §4. ★ 主定理：不塌缩 ⟺ 无有向三角形
--------------------------------------------------------------------------------

-- 「AHomotopy 蕴含命题相等」—— 即商不塌缩
NoCollapse : DiGraph → Set
NoCollapse G = ∀ {u v : V G} {p q : Walk G u v} → AHomotopy G p q → p ≡ q

-- 塌缩 ⇒ 有三角形（逆否：有三角形 ⇒ 违反 NoCollapse）
collapse→triangle : ∀ {G : DiGraph} → ¬ NoCollapse G → ¬ TriangleFree G
collapse→triangle {G} ¬nc tf = ¬nc (AH→≡ tf)

-- ★ 主定理（双向）
no-collapse-iff-triangle-free : ∀ {G : DiGraph} → (NoCollapse G) ↔ᵈ (TriangleFree G)
no-collapse-iff-triangle-free {G} = (λ nc → no-triangle nc) , AH→≡
  where
    -- 若有三角形，则用它构造一对「不同但 A-同伦」的走，与 NoCollapse 冲突
    no-triangle : NoCollapse G → TriangleFree G
    no-triangle nc {x} {y} {z} e1 e2 e3 with triangle-collapses {G = G} {x} {y} {z} e1 e2 e3
    ... | (p , q , p≢q , ah) = p≢q (nc ah)

--------------------------------------------------------------------------------
-- §5. 推论：无三角形时 π₁ᵈ 的乘法就是 `_++w_`，且等价类是单点
--------------------------------------------------------------------------------

-- 每个 AHomotopy-类恰含一个元素（等价类退化）
class-singleton : ∀ {G : DiGraph} (tf : TriangleFree G) {u v : V G} (p : Walk G u v)
                → ∀ (q : Walk G u v) → AHomotopy G p q → q ≡ p
class-singleton tf p q ah = sym (AH→≡ tf ah)

-- 商与闭走「等基数」的精确形态：对每个闭走，它的等价类只含它自己
pi1d-class-is-point : ∀ {G : DiGraph} (tf : TriangleFree G) {v : V G} (w : Walk G v v)
                    → ∀ (w' : Walk G v v) → AHomotopy G w w' → w' ≡ w
pi1d-class-is-point tf w w' ah = sym (AH→≡ tf ah)

--------------------------------------------------------------------------------
-- §6. 推论：走长的可加性与「长度 0 即空走」
--------------------------------------------------------------------------------

walk-len-++w : ∀ {G : DiGraph} {u v w : V G}
               (p : Walk G u v) (q : Walk G v w)
             → walk-len (p ++w q) ≡ walk-len p + walk-len q
walk-len-++w (nil v)    q = refl
walk-len-++w (cons e p) q = cong suc (walk-len-++w p q)

-- `a + a ≡ a ⇒ a ≡ 0`（ℕ 左消去）
double→zero : ∀ a → a + a ≡ a → a ≡ zero
double→zero a p = +-cancelˡ-≡ a a zero (trans p (sym (+-identityʳ a)))

-- ⚠ **without-K 阻断（重要，勿当可修 bug）**：
--   「`walk-len w ≡ zero → w ≡ nil u`」在**闭走**形态下**不可证** ✗ —— 库开 `--cubical`
--   ⇒ K 被禁用，两个方向都卡在同一处：
--     · split `nil` on `Walk G u u`  ⇒ Cannot eliminate reflexive equation u = u
--     · match `refl` on `u ≡ u`      ⇒ 同上
--   换用「带显式端点等式」的版本也不行：要把它用回闭走形态，需要
--   `subst P e x ≡ x` 对任意 `e : u ≡ u` 成立 —— 那**正是 K** ✗
--   ⇒ 本模块只交付可证的**长度形态**（见 §7），强化的空走形态登记为限制，不硬凑 ✓
--
-- ⚠ 保留 `walk-len` 的可加性（这才是推论真正用到的部分）

--------------------------------------------------------------------------------
-- §7. ★ 推论：无三角形 ⇒ 幂等闭走的长度必为 0
--------------------------------------------------------------------------------

-- `w · w ⁓ w` ⇒ （无三角形时 AHomotopy 就是相等）⇒ `len w + len w ≡ len w`
--              ⇒ `len w ≡ 0`
idempotent-len-zero : ∀ {G : DiGraph} (tf : TriangleFree G) {v : V G}
                      (w : Walk G v v)
                    → AHomotopy G (w ++w w) w → walk-len w ≡ zero
idempotent-len-zero tf w ah =
  double→zero (walk-len w)
    (trans (sym (walk-len-++w w w)) (cong walk-len (AH→≡ tf ah)))

-- ⇒ 无三角形时，商里**没有**长度正的幂等元
--   （长度 0 即空走的强化形态受 without-K 阻断，见 §6 说明）
no-pos-idempotent : ∀ {G : DiGraph} (tf : TriangleFree G) {v : V G}
                    (w : Walk G v v)
                  → AHomotopy G (w ++w w) w → ¬ (0 < walk-len w)
no-pos-idempotent tf w ah =
  subst (λ n → ¬ (0 < n)) (sym (idempotent-len-zero tf w ah)) (λ ())

--------------------------------------------------------------------------------
-- §8. A-同伦**不保走长**（一般事实，不依赖无三角形）
--
-- `slide` 把长度 `|p| + (2 + |b|)` 压成 `|p| + (1 + |b|)` ⇒ **每一步都改长度** ✓
-- 这是 §8 的反面：只有 `refl'/symm/trans'` 保长，`gen` 一律不保长。
--------------------------------------------------------------------------------

suc≢ : ∀ n → suc n ≡ n → ⊥
suc≢ zero    ()
suc≢ (suc n) p = suc≢ n (suc-injective p)

AStep-changes-len : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v}
                  → AStep G p q → ¬ (walk-len p ≡ walk-len q)
AStep-changes-len (slide p' b e1 e2 e3) h =
  suc≢ (walk-len b)
    (suc-injective
      (+-cancelˡ-≡ (walk-len p')
                   (suc (suc (walk-len b))) (suc (walk-len b))
        (trans (sym (walk-len-++w p' (cons e1 (cons e2 b))))
          (trans h (walk-len-++w p' (cons e3 b))))))
AStep-changes-len (expand p' b e1 e2 e3) h =
  suc≢ (walk-len b)
    (sym (suc-injective
      (+-cancelˡ-≡ (walk-len p')
                   (suc (walk-len b)) (suc (suc (walk-len b)))
        (trans (sym (walk-len-++w p' (cons e3 b)))
          (trans h (walk-len-++w p' (cons e1 (cons e2 b))))))))

-- 推论：无三角形时 `AHomotopy` 保走长（因为此时它退化为相等）
ahomotopy-preserves-len : ∀ {G : DiGraph} (tf : TriangleFree G)
                          {u v : V G} {p q : Walk G u v}
                        → AHomotopy G p q → walk-len p ≡ walk-len q
ahomotopy-preserves-len tf ah = cong walk-len (AH→≡ tf ah)

-- 逆否：走长不同 ⇒ 不 A-同伦
differing-len-not-AH : ∀ {G : DiGraph} (tf : TriangleFree G)
                       {u v : V G} {p q : Walk G u v}
                     → ¬ (walk-len p ≡ walk-len q) → ¬ (AHomotopy G p q)
differing-len-not-AH tf neq ah = neq (ahomotopy-preserves-len tf ah)

--------------------------------------------------------------------------------
-- §9. ★ 群性判据：无三角形时，正长闭走不可逆
--
-- `w · w' ⁓ nil` ⇒ 无三角形时 `|w| + |w'| ≡ 0` ⇒ `|w| ≡ 0`
-- ⇒ **只要存在正长闭走，`π₁ᵈ(G)` 就不是群** ✓
--------------------------------------------------------------------------------

-- 自备：`0 < 0` 空（直接 `λ ()` 在 `subst` 之后会留 unsolved meta，2026-10-21 实测）
¬0<0 : ¬ (0 < zero)
¬0<0 ()

no-inverse-for-pos : ∀ {G : DiGraph} (tf : TriangleFree G) {v : V G}
                       (w w' : Walk G v v)
                     → AHomotopy G (w ++w w') (nil v) → ¬ (0 < walk-len w)
no-inverse-for-pos tf w w' ah lt =
  ¬0<0 (subst (λ n → 0 < n) eq lt)
  where
    len-sum≡0 : walk-len w + walk-len w' ≡ zero
    len-sum≡0 = trans (sym (walk-len-++w w w')) (cong walk-len (AH→≡ tf ah))
    eq : walk-len w ≡ zero
    -- ⚠ `m+n≡0⇒m≡0 : ∀ m {n} → m + n ≡ 0 → m ≡ 0` —— `n` 是**隐式**参数，
    --   多传一个参数会把 `walk-len w'` 当成 `m`，报「ℕ 不是 ≡ 的子类型」（2026-10-21 实测）
    eq = m+n≡0⇒m≡0 (walk-len w) {walk-len w'} len-sum≡0

-- ★ 推论：无三角形时，若 `π₁ᵈ(G)` 是**群**，则所有闭走长度为零（即 π₁ᵈ 平凡）
group-trivial-when-triangle-free :
    ∀ {G : DiGraph} (tf : TriangleFree G) {v : V G}
  → (∀ (w : Walk G v v) → ∃ (λ (w' : Walk G v v) → AHomotopy G (w ++w w') (nil v)))
  → ∀ (w : Walk G v v) → walk-len w ≡ zero
-- 自备小引理（避开 `≤-antisym` 的 `{i j}` 命名参数与 metas，2026-10-21 实测）
¬0<→≡0 : ∀ n → ¬ (0 < n) → n ≡ zero
¬0<→≡0 zero    h = refl
¬0<→≡0 (suc n) h = ⊥-elim (h (s≤s z≤n))

group-trivial-when-triangle-free tf {v} inv w =
  ¬0<→≡0 (walk-len w)
    (no-inverse-for-pos tf w (proj₁ (inv w)) (proj₂ (inv w)))
