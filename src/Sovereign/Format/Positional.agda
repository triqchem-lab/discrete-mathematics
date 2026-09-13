{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Format.Positional
-- 泛型位值制（base-b positional system）—— **归一保值 + 加法/乘法同态**
--
-- 为什么需要这个模块（两个已知缺口的共同根）：
--   · **Doz（十二进制位值制）**：`docs/duodecimal/01-ontology.md` 明确写着「记数法层（尚未系统形式化）」。
--     十二律相位、`phase_bias` 的高 4 位、TQ10 的相位字段都建立在「以 12 为底记数」上，
--     但这层一直没有形式化定义。
--   · **Z/3¹¹ 环（内核 `lib/sov/sov_z3r_*`）**：内核/C++ 用 11 位基 3 的环元素，
--     而库里只有 `SovereignSection = Vec Trit 30`，两者对不上（见 `lib/sov/README` 缺口清单）。
--
-- 二者是**同一套机制**的两个实例：把「超范围的位表」按 base 逐位进位归一，
-- 位表的值在归一前后（模 base^n 意义下）不变；加法是逐位相加再归一，
-- 乘法是逐位卷积再归一。本模块对任意 `base ≥ 2` 一次性给出这套机制。
--
-- ── 设计（为什么归一写成 expand 而不是手写进位循环）────────────────────────
-- 手写进位循环要处理「尾进位自身还要展开成多位」，那一步只有良基递归可终止，
-- 而 Agda 的 `wfRec` 在**递归调用处不按定义化简**（可及性证明不同 ⇒ 项不同），
-- 于是「展开引理」无法用 `≡⟨⟩` 走通。本模块改用**外延指定**：
--
--   expand n v  =  v 的 base 进制 n 位表示（低位在前）**外加**一个剩余高位值
--   norm n v    =  proj₂ (expand n v)      —— 机器上的「归一后位表」
--
-- 于是「逐位相加再归一」= `norm n (value (addRaw xs ys))`，而它的正确性
-- 只需两条引理：`expand-spec`（展开保值，唯一的实质引理）与 `value-addRaw`
-- （逐位相加保值）。不需要为进位循环单独做终止性论证。
--
-- ── 诚实边界（不许含糊）────────────────────────────────────────────────
-- 本模块证明的是**位运算的规范语义**：`addNorm` / `mulNorm` 的值满足
--   value (addNorm n xs ys) + base^n · 进位 = value xs + value ys
-- 即「结果的低 n 位就是真和的低 n 位」（机器丢弃的进位被显式留在等式里）。
--
-- **本模块不证明**：C 里那个 `for` 进位循环（`sov_z3r_mul` / tritvm 的 `doz_mul`）
-- **精化**（refine）成这里的 `expand`。那需要程序验证工具链（Frama-C/ACSL、VST 之类），
-- 不在 Agda 的能力范围内。两者之间的落差由差分 oracle（抽样对照）覆盖，
-- 而不是由本模块覆盖——这是两条不同的证据线，不能互相冒充。
--
-- 位序：**低位在前**（表头是最低位），与 `Data.Vec` 的 `unpack5` 一致。

-- 参数的类型必须先于模块声明进入作用域（stdlib 的 Effect.Monad.Writer.Indexed 同款写法）
open import Data.Nat.Base using (ℕ; _<_; NonZero; >-nonZero)

module Sovereign.Format.Positional (base : ℕ) (base>1 : 1 < base) where

open import Data.Nat using (zero; suc; _+_; _*_; _^_; s≤s; z≤n)
open import Data.Nat.DivMod using (_%_; _/_; m%n<n; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityˡ; +-identityʳ
  ; *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+; *-zeroʳ
  ; <-trans
  )
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- 0. base ≥ 2 的两个推论
--------------------------------------------------------------------------------

instance
  baseNonZero : NonZero base
  baseNonZero = >-nonZero (<-trans (s≤s z≤n) base>1)

-- 局部引理：加法交换重排（stdlib 2.4 的 Data.Nat.Properties 不导出 +-interchange）
+-shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-shuffle a b c d = begin
  (a + b) + (c + d)
    ≡⟨ +-assoc a b (c + d) ⟩
  a + (b + (c + d))
    ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
  a + ((b + c) + d)
    ≡⟨ cong (a +_) (cong (_+ d) (+-comm b c)) ⟩
  a + ((c + b) + d)
    ≡⟨ cong (a +_) (+-assoc c b d) ⟩
  a + (c + (b + d))
    ≡⟨ sym (+-assoc a c (b + d)) ⟩
  (a + c) + (b + d) ∎

--------------------------------------------------------------------------------
-- 1. 原始位表与值函数
--------------------------------------------------------------------------------

-- 「原始位」不是数字：允许暂时超出 [0, base)。这正是逐位相加/卷积的中间状态。
Raw : Set
Raw = List ℕ

-- 值：低位在前，第 k 位权重 base^k
value : Raw → ℕ
value []       = 0
value (x ∷ xs) = x + base * value xs

--------------------------------------------------------------------------------
-- 2. 展开：v 的 n 位 base 进制表示 + 剩余高位值
--------------------------------------------------------------------------------

-- 注意定义里直接写 proj₁/proj₂ 而不是 let-模式：`let (a , b) = e in …` 在 e 卡住时
-- 不化简，会让下面的计算引理无法用 refl 证明。
expand : ℕ → ℕ → ℕ × Raw
expand zero    v = v , []
expand (suc k) v =
  proj₁ (expand k (v / base)) , v % base ∷ proj₂ (expand k (v / base))

-- 计算引理（逐条 refl）：证明时只跟这些等式打交道，不依赖 let/投影的偶然化简
expand-zero-rest : ∀ v → proj₁ (expand zero v) ≡ v
expand-zero-rest v = refl

expand-zero-digits : ∀ v → proj₂ (expand zero v) ≡ []
expand-zero-digits v = refl

expand-suc-rest : ∀ k v → proj₁ (expand (suc k) v) ≡ proj₁ (expand k (v / base))
expand-suc-rest k v = refl

expand-suc-digits : ∀ k v → proj₂ (expand (suc k) v) ≡ v % base ∷ proj₂ (expand k (v / base))
expand-suc-digits k v = refl

-- 展开保值（本模块唯一的实质引理）：
--   value (低 n 位) + base^n × (剩余高位值) ≡ v
-- 直观：v = (v mod base) + base ⋅ (v / base)，逐层剥 n 次。
expand-spec : ∀ n v → value (proj₂ (expand n v)) + base ^ n * proj₁ (expand n v) ≡ v
expand-spec zero v =
  -- value [] + base^0 * v = 0 + 1 * v = v + 0 ≡ v
  +-identityʳ v
expand-spec (suc k) v = begin
  value (proj₂ (expand (suc k) v)) + base ^ suc k * proj₁ (expand (suc k) v)
    ≡⟨⟩
  (v % base + base * value (proj₂ (expand k (v / base))))
    + (base * base ^ k) * proj₁ (expand k (v / base))
    ≡⟨ cong (λ z → (v % base + base * value (proj₂ (expand k (v / base)))) + z)
            (*-assoc base (base ^ k) (proj₁ (expand k (v / base)))) ⟩
  (v % base + base * value (proj₂ (expand k (v / base))))
    + base * (base ^ k * proj₁ (expand k (v / base)))
    ≡⟨ +-assoc (v % base) (base * value (proj₂ (expand k (v / base))))
                (base * (base ^ k * proj₁ (expand k (v / base)))) ⟩
  v % base + (base * value (proj₂ (expand k (v / base)))
              + base * (base ^ k * proj₁ (expand k (v / base))))
    ≡⟨ cong ((v % base) +_)
            (sym (*-distribˡ-+ base (value (proj₂ (expand k (v / base))))
                                 (base ^ k * proj₁ (expand k (v / base))))) ⟩
  v % base + base * (value (proj₂ (expand k (v / base)))
                      + base ^ k * proj₁ (expand k (v / base)))
    ≡⟨ cong (λ z → v % base + base * z) (expand-spec k (v / base)) ⟩
  v % base + base * (v / base)
    ≡⟨ cong ((v % base) +_) (*-comm base (v / base)) ⟩
  v % base + (v / base) * base
    ≡⟨ sym (m≡m%n+[m/n]*n v base) ⟩
  v ∎

-- 展开出来的每一位都 < base（规范位）
expand-bound : ∀ n v → All.All (_< base) (proj₂ (expand n v))
expand-bound zero    v = All.[]
expand-bound (suc k) v = m%n<n v base All.∷ expand-bound k (v / base)

--------------------------------------------------------------------------------
-- 3. 归一（机器上的「进位处理完」位表）
--------------------------------------------------------------------------------

-- norm n v = v 的 n 位规范表示（低位在前），更高位被丢弃
norm : ℕ → ℕ → Raw
norm n v = proj₂ (expand n v)

-- 归一语义：结果的低 n 位就是 v 的低 n 位，被丢弃的部分显式写成 base^n × 剩余值。
-- 这就是「模 base^n 保值」的展开写法——机器位宽语义即此。
norm-spec : ∀ n v → value (norm n v) + base ^ n * proj₁ (expand n v) ≡ v
norm-spec n v = expand-spec n v

norm-bound : ∀ n v → All.All (_< base) (norm n v)
norm-bound n v = expand-bound n v

--------------------------------------------------------------------------------
-- 4. 逐位相加 → 归一
--------------------------------------------------------------------------------

addRaw : Raw → Raw → Raw
addRaw []       ys       = ys
addRaw (x ∷ xs) []       = x ∷ xs
addRaw (x ∷ xs) (y ∷ ys) = (x + y) ∷ addRaw xs ys

value-addRaw : ∀ xs ys → value (addRaw xs ys) ≡ value xs + value ys
value-addRaw []       ys       = refl
value-addRaw (x ∷ xs) []       = sym (+-identityʳ (value (x ∷ xs)))
value-addRaw (x ∷ xs) (y ∷ ys) = begin
  value (addRaw (x ∷ xs) (y ∷ ys))
    ≡⟨⟩
  (x + y) + base * value (addRaw xs ys)
    ≡⟨ cong (λ z → (x + y) + base * z) (value-addRaw xs ys) ⟩
  (x + y) + base * (value xs + value ys)
    ≡⟨ cong (λ z → (x + y) + z) (*-distribˡ-+ base (value xs) (value ys)) ⟩
  (x + y) + (base * value xs + base * value ys)
    ≡⟨ +-shuffle x y (base * value xs) (base * value ys) ⟩
  (x + base * value xs) + (y + base * value ys) ∎

-- 位值制加法：逐位相加 → 进位归一（模 base^n）
addNorm : ℕ → Raw → Raw → Raw
addNorm n xs ys = norm n (value (addRaw xs ys))

add-spec : ∀ n xs ys →
  value (addNorm n xs ys) + base ^ n * proj₁ (expand n (value (addRaw xs ys)))
    ≡ value xs + value ys
add-spec n xs ys =
  trans (norm-spec n (value (addRaw xs ys))) (value-addRaw xs ys)

--------------------------------------------------------------------------------
-- 5. 逐位卷积 → 归一（乘法）
--------------------------------------------------------------------------------

scale : ℕ → Raw → Raw
scale k xs = map (k *_) xs

value-scale : ∀ k xs → value (scale k xs) ≡ k * value xs
value-scale k []       = sym (*-zeroʳ k)
value-scale k (y ∷ ys) = begin
  value (scale k (y ∷ ys))
    ≡⟨⟩
  k * y + base * value (scale k ys)
    ≡⟨ cong (λ z → k * y + base * z) (value-scale k ys) ⟩
  k * y + base * (k * value ys)
    ≡⟨ cong (λ z → k * y + z) (sym (*-assoc base k (value ys))) ⟩
  k * y + (base * k) * value ys
    ≡⟨ cong (λ z → k * y + z * value ys) (*-comm base k) ⟩
  k * y + (k * base) * value ys
    ≡⟨ cong (λ z → k * y + z) (*-assoc k base (value ys)) ⟩
  k * y + k * (base * value ys)
    ≡⟨ sym (*-distribˡ-+ k y (base * value ys)) ⟩
  k * (y + base * value ys) ∎

-- 卷积：第 k 位 = Σ_{i+j=k} x_i · y_j（不处理进位）
conv : Raw → Raw → Raw
conv []       ys = []
conv (x ∷ xs) ys = addRaw (scale x ys) (0 ∷ conv xs ys)

value-conv : ∀ xs ys → value (conv xs ys) ≡ value xs * value ys
value-conv []       ys = refl
value-conv (x ∷ xs) ys = begin
  value (addRaw (scale x ys) (0 ∷ conv xs ys))
    ≡⟨ value-addRaw (scale x ys) (0 ∷ conv xs ys) ⟩
  value (scale x ys) + value (0 ∷ conv xs ys)
    ≡⟨ cong₂ _+_ (value-scale x ys) refl ⟩
  x * value ys + base * value (conv xs ys)
    ≡⟨ cong (λ z → x * value ys + base * z) (value-conv xs ys) ⟩
  x * value ys + base * (value xs * value ys)
    ≡⟨ cong (λ z → x * value ys + z) (sym (*-assoc base (value xs) (value ys))) ⟩
  x * value ys + (base * value xs) * value ys
    ≡⟨ sym (*-distribʳ-+ (value ys) x (base * value xs)) ⟩
  (x + base * value xs) * value ys ∎

-- 位值制乘法：逐位卷积 → 进位归一（模 base^n）
mulNorm : ℕ → Raw → Raw → Raw
mulNorm n xs ys = norm n (value (conv xs ys))

mul-spec : ∀ n xs ys →
  value (mulNorm n xs ys) + base ^ n * proj₁ (expand n (value (conv xs ys)))
    ≡ value xs * value ys
mul-spec n xs ys =
  trans (norm-spec n (value (conv xs ys))) (value-conv xs ys)

--------------------------------------------------------------------------------
-- 6. 截断与位合法性
--------------------------------------------------------------------------------

trim : ℕ → Raw → Raw
trim zero    xs       = []
trim (suc n) []       = []
trim (suc n) (x ∷ xs) = x ∷ trim n xs

trim-bound : ∀ n xs → All.All (_< base) xs → All.All (_< base) (trim n xs)
trim-bound zero    xs       ok              = All.[]
trim-bound (suc n) []       ok              = All.[]
trim-bound (suc n) (x ∷ xs) (px All.∷ pxs)  = px All.∷ trim-bound n xs pxs
