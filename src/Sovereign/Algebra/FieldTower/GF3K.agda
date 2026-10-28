{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.GF3K
-- 参数化 GF(3^k) 泛型域构造 —— PvsNP 路线图 W3 工作流
--
-- 定位：域塔 GF(9)/GF(27)/GF(36) 至今逐级硬编码；本模块给出以
-- 「次数 k + monic 多项式 P（数据给定）」为参数的泛型 GF(3^k) 载体，
-- 作为 {GF(3^k)}_k 渐近族的尺寸参数载体（后续复杂度陈述的挂靠点）。
--
-- == 系数表示约定
--   · carrier GF3K k = Vec Trit k，升幂：head = 常数项，第 i 位 = x^i 系数。
--   · P 以 Vec Trit (suc k) 降幂给定（head = x^k 系数，monic 时为 T₁）。
--   · 约简表 redTable P：x^k ≡ negate(c_{k-1})·x^{k-1} ⊕ … ⊕ negate(c₀)（升幂输出）。
--   · modPoly 以 x^k ≡ red 反复代换归约（最高次先消，slack 逐位递减）。
--
-- == 分级交付（诚实分级）
--   §1 泛型定义层………………【纯定义】总能闭合（W3-①）
--   §2 k=2 对拍 GF9……………【refl 枚举 81 项】乘法逐点相等（W3-②）
--   §3 k=2 定律…………………【对拍借用】经由 §2 传输，借用 GF9 已证定律
--   §4 k=3 对拍 GF27…………【结构证明】⊕-重排链 + 【refl】加法逐位
--   §5 k=3 定律…………………【对拍借用】经由 §4 传输，借用 GF27 已证定律
--   §6 立界清单…………………【立界注记】只声明不证明
--
-- == 立界清单（本模块不做的事）
--   B1 任意 k 不可约多项式存在性：不证明。真实数学路径：
--      x^{3^k} − x 无重根（形式导数 3x^{3^k-1} − 1 ≡ −1 ≠ 0，可分）
--      + 次数整除计数 / Möbius 反演 Σ_{d∣k} d·N_d = 3^k ⇒ N_k ≥ 1。
--      本模块的 P 一律以数据给定；x²+1（k=2）、x³+2x+1（k=3）的
--      不可约性分别在 GF9/GF27 本体以无根枚举在案，此处不重述。
--   B2 monic 性不类型强制：redTable 丢弃 P 的首系数；首系数 ≠ T₁ 时
--      redTable 仍可计算，但约简不再对应 GF(3^k)。调用方约束。
--   B3 域性不泛化：不证「P 不可约 ⇒ GF3K k 为域」的一般定理；
--      逐实例域性经由对拍借用 GF9/GF27 本体已证定律获得。
--   B4 k=6 / GF36 对拍未做（预算边界）；k=0/k=1 退化载体不承载定律。
--   B5 泛型层语义定理（mulPoly 等于抽象多项式乘法）不设——只有逐实例对拍。
--   B6 泛型循环 mulMod 3 red3 的符号传输未闭合（其归一形含 ⊕T₀ 残渣，
--      符号重排不可行）；k=3 实例改以 red3-数据驱动内联公式交付
--      （GF36 同款形态，模数数据仍从 redTable P3 流入），其与泛型循环
--      的逐点相等留待后续；k=2 层面泛型循环已全量对拍闭合。
--
-- 命名：与 GF9/GF27/GF36 本体无撞名（2026-10-28 全 src grep 在案；
-- GenericInst.agda 属数论泛型线，与本模块无关）。
-- 0 postulate；0 hole；无 REWRITE 规则；不修改既有文件。
module Sovereign.Algebra.FieldTower.GF3K where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; head; tail)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
         ⊕-comm; ⊕-assoc; ⊕-identityʳ;
         ⊗-comm; ⊗-identityʳ; ⊗-zeroʳ)
open import Sovereign.Algebra.FieldTower.GF9
  using (GF9; _+gf9_; _*gf9_; gf9-one; gf9-zero;
         +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-inverse;
         *gf9-comm; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ;
         *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9)
open import Sovereign.Algebra.FieldTower.GF27
  using (GF27; _+gf27_; _*gf27_; gf27-one; gf27-zero;
         +gf27-comm; +gf27-assoc; +gf27-identityˡ; +gf27-inverse;
         *gf27-comm; *gf27-assoc; *gf27-identityˡ; *gf27-identityʳ;
         *gf27-distribˡ; *gf27-distribʳ; two-mul-neg; cong-triple)

--------------------------------------------------------------------------------
-- §1. 泛型定义层（纯定义；W3-①：本节仅要求类型检查闭合，无定律主张）
--------------------------------------------------------------------------------

-- carrier：k 个 trit，升幂系数（head = 常数项）
GF3K : ℕ → Set
GF3K k = Vec Trit k

-- 1.1 向量工具 ----------------------------------------------------------------

-- 尾部接元
snocV : ∀ {n} → Vec Trit n → Trit → Vec Trit (suc n)
snocV [] t = t ∷ []
snocV (x ∷ xs) t = x ∷ snocV xs t

-- 全零向量（零多项式）
zeros : ∀ (n : ℕ) → Vec Trit n
zeros zero = []
zeros (suc n) = T₀ ∷ zeros n

-- 取最高位系数（x^{n} 的系数，输入长 suc n）
topCoef : ∀ {n} → Vec Trit (suc n) → Trit
topCoef (x ∷ []) = x
topCoef (x ∷ y ∷ ys) = topCoef (y ∷ ys)

-- 去掉最高位
initVec : ∀ {n} → Vec Trit (suc n) → Vec Trit n
initVec (x ∷ []) = []
initVec (x ∷ y ∷ ys) = x ∷ initVec (y ∷ ys)

-- 逐位取负
negVec : ∀ {n} → Vec Trit n → Vec Trit n
negVec = map negate

-- 逐位加法（GF(3^k) 加法：(Z/3)^k 逐位 ⊕）
addVec : ∀ {n} → Vec Trit n → Vec Trit n → Vec Trit n
addVec = zipWith _⊕_

-- 1.2 monic 多项式 → 约简表 ----------------------------------------------------
-- P 降幂 (c_k ∷ c_{k-1} ∷ … ∷ c₀)；monic 首系数 c_k = T₁ 由调用方保证，
-- 本函数不读它（立界 B2）。输出升幂 (negate c₀ ∷ … ∷ negate c_{k-1})：
--   x^k ≡ −(c_{k-1}x^{k-1} + … + c₀)
redTable : ∀ {k} → Vec Trit (suc k) → Vec Trit k
redTable {zero} (_ ∷ []) = []
redTable {suc k} (_ ∷ p ∷ ps) = snocV (redTable (p ∷ ps)) (negate p)

-- 1.3 卷积乘法（未约简）---------------------------------------------------------
-- 尾部补零到长 (e + n)（升幂：高位补零）
extendEnd : ∀ (e : ℕ) {n} → Vec Trit n → Vec Trit (e + n)
extendEnd zero xs = xs
extendEnd (suc e) xs = snocV (extendEnd e xs) T₀

-- 把短向量 xs（长 n）加进长向量 ys（长 e + n）的第 e..e+n-1 位（前 e 位原样）。
-- 零档以 ys 侧为 ⊕ 左参量（使 reduceTop 输出的归一形为「原位 ⊕ 行」）
addFront : ∀ (e : ℕ) {n} → Vec Trit n → Vec Trit (e + n) → Vec Trit (e + n)
addFront zero xs ys = zipWith _⊕_ ys xs
addFront (suc e) xs (y ∷ ys) = y ∷ addFront e xs ys

-- 多项式乘法（卷积）：升幂，输出长 m + n（高位为补零 padding）
mulPoly : ∀ {m n} → Vec Trit m → Vec Trit n → Vec Trit (m + n)
mulPoly {zero} {n} [] bs = zeros n
mulPoly {suc m} {n} (a ∷ as) bs =
  zipWith _⊕_ (extendEnd (suc m) (map (a ⊗_) bs)) (T₀ ∷ mulPoly as bs)

-- 1.4 modP 归约（x^k ≡ red 反复代换）--------------------------------------------
-- 一次最高次代换：xs 长 (suc (e+k))，顶系数 c = topCoef xs 携带 x^{e+k}；
--   x^{e+k} = x^e · x^k ≡ x^e · red，把 c·red 加进余部第 e..e+k-1 位
reduceTop : ∀ (e : ℕ) {k} → Vec Trit k → Vec Trit (suc (e + k)) → Vec Trit (e + k)
reduceTop e red xs = addFront e (map (topCoef xs ⊗_) red) (initVec xs)

-- 归约主循环：slack s 逐位递减至 0
modPoly : ∀ (s k : ℕ) → Vec Trit k → Vec Trit (s + k) → Vec Trit k
modPoly zero k red xs = xs
modPoly (suc s) k red xs = modPoly s k red (reduceTop s red xs)

-- 泛型乘法（模 P）：mulMod k red as bs，red 为约简表
mulMod : ∀ (k : ℕ) → Vec Trit k → Vec Trit k → Vec Trit k → Vec Trit k
mulMod k red as bs = modPoly k k red (mulPoly as bs)

-- P-接口：直接以 monic 降幂多项式给定（等价于先取 redTable）
mulModMono : ∀ (k : ℕ) → Vec Trit (suc k) → Vec Trit k → Vec Trit k → Vec Trit k
mulModMono k P as bs = mulMod k (redTable P) as bs

-- 1.5 单位元 -------------------------------------------------------------------
zero3K : ∀ (k : ℕ) → Vec Trit k
zero3K k = zeros k

one3K : ∀ (k : ℕ) → Vec Trit (suc k)
one3K k = T₁ ∷ zeros k

--------------------------------------------------------------------------------
-- §2. k=2 实例——与 GF9 全量对拍（81 项 refl 枚举；W3-②）
--------------------------------------------------------------------------------

-- P = x² + 1（降幂 (1, 0, 1)），即 GF9 的扩张多项式
P2K : Vec Trit 3
P2K = T₁ ∷ T₀ ∷ T₁ ∷ []

red2 : Vec Trit 2
red2 = redTable P2K                 -- x² ≡ 2 + 0·x

red2-check : red2 ≡ T₂ ∷ T₀ ∷ []
red2-check = refl

mulMod2 : Vec Trit 2 → Vec Trit 2 → Vec Trit 2
mulMod2 = mulMod 2 red2

add2 : Vec Trit 2 → Vec Trit 2 → Vec Trit 2
add2 = addVec

one2 zero2 : Vec Trit 2
one2 = T₁ ∷ T₀ ∷ []               -- 与 gf9-one = (T₁, T₀) 定义相等
zero2 = T₀ ∷ T₀ ∷ []              -- 与 gf9-zero = (T₀, T₀) 定义相等

-- 与 GF9 本体 (a, b) = a + bα 的往返转换 ---------------------------------------

toG9 : Vec Trit 2 → GF9
toG9 (a ∷ b ∷ []) = a , b

fromG9 : GF9 → Vec Trit 2
fromG9 (a , b) = a ∷ b ∷ []

to-from9 : ∀ (x : GF9) → toG9 (fromG9 x) ≡ x
to-from9 (a , b) = refl

from-to9 : ∀ (v : Vec Trit 2) → fromG9 (toG9 v) ≡ v
from-to9 (a ∷ b ∷ []) = refl

toG9-inj : ∀ (u v : Vec Trit 2) → toG9 u ≡ toG9 v → u ≡ v
toG9-inj u v e = trans (sym (from-to9 u)) (trans (cong fromG9 e) (from-to9 v))

-- 加法逐位对拍（结构归约，1 条通式）【refl】
add2-≡ : ∀ (u v : Vec Trit 2) → toG9 (add2 u v) ≡ toG9 u +gf9 toG9 v
add2-≡ (a ∷ b ∷ []) (c ∷ d ∷ []) = refl

-- 乘法对拍：泛型 mulMod2 与 GF9 硬编码 *gf9 逐元素相等【refl 枚举 81 项】
mul2-≡ : ∀ (u v : Vec Trit 2) → toG9 (mulMod2 u v) ≡ toG9 u *gf9 toG9 v
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₀ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₁ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₀ ∷ T₂ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₀ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₁ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₁ ∷ T₂ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₀ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₁ ∷ []) (T₂ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₀ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₀ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₀ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₁ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₁ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₁ ∷ T₂ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₂ ∷ T₀ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₂ ∷ T₁ ∷ []) = refl
mul2-≡ (T₂ ∷ T₂ ∷ []) (T₂ ∷ T₂ ∷ []) = refl

--------------------------------------------------------------------------------
-- §3. k=2 定律——「对拍借用」GF9 已证定律（W3-② 合规路线）
-- 边界注记：本节定律不在泛型层直接证明；经由 mul2-≡（81 项对拍）把
-- GF9 本体已证定律传输到泛型载体上。定律真值以 GF9 模块为准，
-- 本模块只承担「泛型 mulMod2 与本体 *gf9 逐点相等」的传输责任。
--------------------------------------------------------------------------------

-- GF9 本体缺零律，本地补两条（9 case refl，供借用；K2- 前缀避免与库内既有
-- *gf9-zeroˡ/ʳ 本地副本撞名——见 FiniteInnerProduct/LinearFunctionalDiscrete/BCHGF9）
K2-gf9-zeroˡ : ∀ (x : GF9) → gf9-zero *gf9 x ≡ gf9-zero
K2-gf9-zeroˡ x = refl

K2-gf9-zeroʳ : ∀ (x : GF9) → x *gf9 gf9-zero ≡ gf9-zero
K2-gf9-zeroʳ (T₀ , T₀) = refl
K2-gf9-zeroʳ (T₁ , T₀) = refl
K2-gf9-zeroʳ (T₂ , T₀) = refl
K2-gf9-zeroʳ (T₀ , T₁) = refl
K2-gf9-zeroʳ (T₁ , T₁) = refl
K2-gf9-zeroʳ (T₂ , T₁) = refl
K2-gf9-zeroʳ (T₀ , T₂) = refl
K2-gf9-zeroʳ (T₁ , T₂) = refl
K2-gf9-zeroʳ (T₂ , T₂) = refl

*2-comm : ∀ (u v : Vec Trit 2) → mulMod2 u v ≡ mulMod2 v u
*2-comm u v = toG9-inj (mulMod2 u v) (mulMod2 v u) (
  begin
    toG9 (mulMod2 u v)      ≡⟨ mul2-≡ u v ⟩
    toG9 u *gf9 toG9 v      ≡⟨ *gf9-comm (toG9 u) (toG9 v) ⟩
    toG9 v *gf9 toG9 u      ≡⟨ sym (mul2-≡ v u) ⟩
    toG9 (mulMod2 v u)
  ∎)

*2-assoc : ∀ (u v w : Vec Trit 2) →
  mulMod2 (mulMod2 u v) w ≡ mulMod2 u (mulMod2 v w)
*2-assoc u v w = toG9-inj (mulMod2 (mulMod2 u v) w) (mulMod2 u (mulMod2 v w)) (
  begin
    toG9 (mulMod2 (mulMod2 u v) w)    ≡⟨ mul2-≡ (mulMod2 u v) w ⟩
    toG9 (mulMod2 u v) *gf9 toG9 w    ≡⟨ cong (_*gf9 toG9 w) (mul2-≡ u v) ⟩
    (toG9 u *gf9 toG9 v) *gf9 toG9 w  ≡⟨ *gf9-assoc (toG9 u) (toG9 v) (toG9 w) ⟩
    toG9 u *gf9 (toG9 v *gf9 toG9 w)  ≡⟨ sym (cong (toG9 u *gf9_) (mul2-≡ v w)) ⟩
    toG9 u *gf9 toG9 (mulMod2 v w)    ≡⟨ sym (mul2-≡ u (mulMod2 v w)) ⟩
    toG9 (mulMod2 u (mulMod2 v w))
  ∎)

*2-identityˡ : ∀ (v : Vec Trit 2) → mulMod2 one2 v ≡ v
*2-identityˡ v = toG9-inj (mulMod2 one2 v) v (
  begin
    toG9 (mulMod2 one2 v)  ≡⟨ mul2-≡ one2 v ⟩
  gf9-one *gf9 toG9 v      ≡⟨ *gf9-identityˡ (toG9 v) ⟩
    toG9 v
  ∎)

*2-identityʳ : ∀ (v : Vec Trit 2) → mulMod2 v one2 ≡ v
*2-identityʳ v = toG9-inj (mulMod2 v one2) v (
  begin
    toG9 (mulMod2 v one2)  ≡⟨ mul2-≡ v one2 ⟩
  toG9 v *gf9 gf9-one      ≡⟨ *gf9-identityʳ (toG9 v) ⟩
    toG9 v
  ∎)

*2-zeroˡ : ∀ (v : Vec Trit 2) → mulMod2 zero2 v ≡ zero2
*2-zeroˡ v = toG9-inj (mulMod2 zero2 v) zero2 (
  begin
    toG9 (mulMod2 zero2 v)  ≡⟨ mul2-≡ zero2 v ⟩
  gf9-zero *gf9 toG9 v      ≡⟨ K2-gf9-zeroˡ (toG9 v) ⟩
    gf9-zero
  ∎)

*2-zeroʳ : ∀ (v : Vec Trit 2) → mulMod2 v zero2 ≡ zero2
*2-zeroʳ v = toG9-inj (mulMod2 v zero2) zero2 (
  begin
    toG9 (mulMod2 v zero2)  ≡⟨ mul2-≡ v zero2 ⟩
  toG9 v *gf9 gf9-zero      ≡⟨ K2-gf9-zeroʳ (toG9 v) ⟩
    gf9-zero
  ∎)

*2-distribˡ : ∀ (u v w : Vec Trit 2) →
  mulMod2 u (add2 v w) ≡ add2 (mulMod2 u v) (mulMod2 u w)
*2-distribˡ u v w = toG9-inj (mulMod2 u (add2 v w)) (add2 (mulMod2 u v) (mulMod2 u w)) (
  begin
    toG9 (mulMod2 u (add2 v w))                       ≡⟨ mul2-≡ u (add2 v w) ⟩
    toG9 u *gf9 toG9 (add2 v w)                       ≡⟨ cong (toG9 u *gf9_) (add2-≡ v w) ⟩
    toG9 u *gf9 (toG9 v +gf9 toG9 w)                  ≡⟨ *gf9-distribˡ-+gf9 (toG9 u) (toG9 v) (toG9 w) ⟩
    (toG9 u *gf9 toG9 v) +gf9 (toG9 u *gf9 toG9 w)    ≡⟨ cong₂ _+gf9_ (sym (mul2-≡ u v)) (sym (mul2-≡ u w)) ⟩
    toG9 (mulMod2 u v) +gf9 toG9 (mulMod2 u w)        ≡⟨ sym (add2-≡ (mulMod2 u v) (mulMod2 u w)) ⟩
    toG9 (add2 (mulMod2 u v) (mulMod2 u w))
  ∎)

*2-distribʳ : ∀ (u v w : Vec Trit 2) →
  mulMod2 (add2 u v) w ≡ add2 (mulMod2 u w) (mulMod2 v w)
*2-distribʳ u v w = toG9-inj (mulMod2 (add2 u v) w) (add2 (mulMod2 u w) (mulMod2 v w)) (
  begin
    toG9 (mulMod2 (add2 u v) w)                       ≡⟨ mul2-≡ (add2 u v) w ⟩
    toG9 (add2 u v) *gf9 toG9 w                       ≡⟨ cong (_*gf9 toG9 w) (add2-≡ u v) ⟩
    (toG9 u +gf9 toG9 v) *gf9 toG9 w                  ≡⟨ *gf9-distribʳ-+gf9 (toG9 u) (toG9 v) (toG9 w) ⟩
    (toG9 u *gf9 toG9 w) +gf9 (toG9 v *gf9 toG9 w)    ≡⟨ cong₂ _+gf9_ (sym (mul2-≡ u w)) (sym (mul2-≡ v w)) ⟩
    toG9 (mulMod2 u w) +gf9 toG9 (mulMod2 v w)        ≡⟨ sym (add2-≡ (mulMod2 u w) (mulMod2 v w)) ⟩
    toG9 (add2 (mulMod2 u w) (mulMod2 v w))
  ∎)

+2-comm : ∀ (u v : Vec Trit 2) → add2 u v ≡ add2 v u
+2-comm u v = toG9-inj (add2 u v) (add2 v u) (
  begin
    toG9 (add2 u v)      ≡⟨ add2-≡ u v ⟩
    toG9 u +gf9 toG9 v   ≡⟨ +gf9-comm (toG9 u) (toG9 v) ⟩
    toG9 v +gf9 toG9 u   ≡⟨ sym (add2-≡ v u) ⟩
    toG9 (add2 v u)
  ∎)

+2-assoc : ∀ (u v w : Vec Trit 2) → add2 (add2 u v) w ≡ add2 u (add2 v w)
+2-assoc u v w = toG9-inj (add2 (add2 u v) w) (add2 u (add2 v w)) (
  begin
    toG9 (add2 (add2 u v) w)   ≡⟨ add2-≡ (add2 u v) w ⟩
    toG9 (add2 u v) +gf9 toG9 w ≡⟨ cong (_+gf9 toG9 w) (add2-≡ u v) ⟩
    (toG9 u +gf9 toG9 v) +gf9 toG9 w ≡⟨ +gf9-assoc (toG9 u) (toG9 v) (toG9 w) ⟩
    toG9 u +gf9 (toG9 v +gf9 toG9 w) ≡⟨ sym (cong (toG9 u +gf9_) (add2-≡ v w)) ⟩
    toG9 u +gf9 toG9 (add2 v w) ≡⟨ sym (add2-≡ u (add2 v w)) ⟩
    toG9 (add2 u (add2 v w))
  ∎)

+2-identityˡ : ∀ (v : Vec Trit 2) → add2 zero2 v ≡ v
+2-identityˡ v = toG9-inj (add2 zero2 v) v (
  begin
    toG9 (add2 zero2 v)  ≡⟨ add2-≡ zero2 v ⟩
  gf9-zero +gf9 toG9 v   ≡⟨ +gf9-identityˡ (toG9 v) ⟩
    toG9 v
  ∎)

+2-inverse : ∀ (v : Vec Trit 2) → add2 v (negVec v) ≡ zero2
+2-inverse (a ∷ b ∷ []) = toG9-inj (add2 (a ∷ b ∷ []) (negVec (a ∷ b ∷ []))) zero2 (
  begin
    toG9 (add2 (a ∷ b ∷ []) (negVec (a ∷ b ∷ [])))  ≡⟨ add2-≡ (a ∷ b ∷ []) (negVec (a ∷ b ∷ [])) ⟩
  (a , b) +gf9 (negate a , negate b)                 ≡⟨ +gf9-inverse (a , b) ⟩
    gf9-zero
  ∎)

--------------------------------------------------------------------------------
-- §4. k=3 实例——与 GF27 对拍（乘法为结构证明 ⊕-重排链；W3-③）
--------------------------------------------------------------------------------

-- P = x³ + 2x + 1（降幂 (1, 0, 2, 1)），即 GF27 的扩张多项式
P3 : Vec Trit 4
P3 = T₁ ∷ T₀ ∷ T₂ ∷ T₁ ∷ []

red3 : Vec Trit 3
red3 = redTable P3                 -- x³ ≡ 2 + x

red3-check : red3 ≡ T₂ ∷ T₁ ∷ T₀ ∷ []
red3-check = refl

-- k=3 实例乘法——red3 数据驱动的内联公式（GF36 同款形态）：
--   q₀..q₄ 为卷积系数；x⁴ ≡ r₀x + r₁x² + r₂x³，x³ ≡ r₀ + r₁x + r₂x²；
--   本 P3 数据下 r₂ = T₀（red3-check 数据闭合），x³ 项消零、q₄ 只摊入 x/x²。
--【结构注记】泛型循环 mulMod 3 red3 的符号传输未闭合（其归一形含 ⊕T₀
--   残渣，立界 B6）；本实例改走 red3-数据流入的内联形态，对拍 GF27 闭合。
mulMod3 : Vec Trit 3 → Vec Trit 3 → Vec Trit 3
mulMod3 (a ∷ b ∷ c ∷ []) (d ∷ e ∷ f ∷ []) =
  (q₀ ⊕ (q₃' ⊗ r₀)) ∷ ((q₁ ⊕ (q₄ ⊗ r₀)) ⊕ (q₃' ⊗ r₁)) ∷ (q₂ ⊕ (q₄ ⊗ r₁)) ∷ []
  where
    q₀ = a ⊗ d
    q₁ = (a ⊗ e) ⊕ (b ⊗ d)
    q₂ = (a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))
    r₀ = head red3
    r₁ = head (tail red3)
    r₂ = head (tail (tail red3))
    q₄ = c ⊗ f
    q₃' = ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ (q₄ ⊗ r₂)

addT3 : Vec Trit 3 → Vec Trit 3 → Vec Trit 3
addT3 = addVec

one3 zero3 : Vec Trit 3
one3 = T₁ ∷ T₀ ∷ T₀ ∷ []          -- 与 gf27-one 定义相等
zero3 = T₀ ∷ T₀ ∷ T₀ ∷ []         -- 与 gf27-zero 定义相等

toG27 : Vec Trit 3 → GF27
toG27 (a ∷ b ∷ c ∷ []) = a , b , c

fromG27 : GF27 → Vec Trit 3
fromG27 (a , b , c) = a ∷ b ∷ c ∷ []

to-from27 : ∀ (x : GF27) → toG27 (fromG27 x) ≡ x
to-from27 (a , b , c) = refl

from-to27 : ∀ (v : Vec Trit 3) → fromG27 (toG27 v) ≡ v
from-to27 (a ∷ b ∷ c ∷ []) = refl

toG27-inj : ∀ (u v : Vec Trit 3) → toG27 u ≡ toG27 v → u ≡ v
toG27-inj u v e = trans (sym (from-to27 u)) (trans (cong fromG27 e) (from-to27 v))

-- 加法逐位对拍（结构归约，1 条通式）【refl】
addT3-≡ : ∀ (u v : Vec Trit 3) → toG27 (addT3 u v) ≡ toG27 u +gf27 toG27 v
addT3-≡ (a ∷ b ∷ c ∷ []) (d ∷ e ∷ f ∷ []) = refl

-- 右乘 T₂：t·2 = negate t（GF3 中 −1 ≡ 2；GF27 本体的 two-mul-neg 是左乘）
mul-two-r : ∀ t → t ⊗ T₂ ≡ negate t
mul-two-r t = trans (⊗-comm t T₂) (two-mul-neg t)

-- red3 分量投影的数据闭合（head-投影取回 r₀/r₁/r₂ 的字面值）
r₀-def : head red3 ≡ T₂
r₀-def = cong head red3-check

r₁-def : head (tail red3) ≡ T₁
r₁-def = cong (λ v → head (tail v)) red3-check

r₂-def : head (tail (tail red3)) ≡ T₀
r₂-def = cong (λ v → head (tail (tail v))) red3-check

-- x³ 顶系数摊入后的规范形 q₃' = (b·f ⊕ c·e) ⊕ (c·f·r₂)，r₂ = T₀ 消零
q₃'-simp : ∀ b c e f →
  ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))
  ≡ (b ⊗ f) ⊕ (c ⊗ e)
q₃'-simp b c e f =
  trans (cong (λ w → ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ w)) r₂-def)
  (trans (cong (λ w → ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ w) (⊗-zeroʳ (c ⊗ f)))
         (⊕-identityʳ ((b ⊗ f) ⊕ (c ⊗ e))))

-- 泛型 k=3 分量与 *gf27 三分量逐项相等【结构证明】（两侧皆干净公式）
--   内联 mulMod3 (a,b,c)(d,e,f) =
--     m₀ = q₀ ⊕ (q₃' ⊗ r₀)
--     m₁ = (q₁ ⊕ (q₄ ⊗ r₀)) ⊕ (q₃' ⊗ r₁)
--     m₂ = q₂ ⊕ (q₄ ⊗ r₁)

mul3-≡₀ : ∀ a b c d e f →
  (a ⊗ d) ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ head red3)
  ≡ (a ⊗ d) ⊕ negate ((b ⊗ f) ⊕ (c ⊗ e))
mul3-≡₀ a b c d e f =
  trans (cong (λ w → (a ⊗ d) ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ w)) r₀-def)
  (trans (cong (λ w → (a ⊗ d) ⊕ (w ⊗ T₂)) (q₃'-simp b c e f))
         (cong (λ w → (a ⊗ d) ⊕ w) (mul-two-r ((b ⊗ f) ⊕ (c ⊗ e)))))

mul3-≡₁ : ∀ a b c d e f →
  (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((c ⊗ f) ⊗ head red3))
  ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ head (tail red3))
  ≡ ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f)))
mul3-≡₁ a b c d e f =
  begin
    (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((c ⊗ f) ⊗ head red3))
    ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ head (tail red3))
      ≡⟨ cong (λ w → (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((c ⊗ f) ⊗ w))
                      ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ head (tail red3)))
              r₀-def ⟩
    (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((c ⊗ f) ⊗ T₂))
    ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ head (tail red3))
      ≡⟨ cong (λ w → (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((c ⊗ f) ⊗ T₂))
                      ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ w))
              r₁-def ⟩
    (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((c ⊗ f) ⊗ T₂))
    ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ T₁)
      ≡⟨ cong (λ w → (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ w)
                      ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ T₁))
              (mul-two-r (c ⊗ f)) ⟩
    (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate (c ⊗ f))
    ⊕ ((((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((c ⊗ f) ⊗ head (tail (tail red3)))) ⊗ T₁)
      ≡⟨ cong (λ w → (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate (c ⊗ f)) ⊕ (w ⊗ T₁))
              (q₃'-simp b c e f) ⟩
    (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate (c ⊗ f)) ⊕ (((b ⊗ f) ⊕ (c ⊗ e)) ⊗ T₁)
      ≡⟨ cong (λ w → (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate (c ⊗ f)) ⊕ w)
              (⊗-identityʳ ((b ⊗ f) ⊕ (c ⊗ e))) ⟩
    (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate (c ⊗ f)) ⊕ ((b ⊗ f) ⊕ (c ⊗ e))
      ≡⟨ ⊕-assoc ((a ⊗ e) ⊕ (b ⊗ d)) (negate (c ⊗ f)) ((b ⊗ f) ⊕ (c ⊗ e)) ⟩
    ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ (negate (c ⊗ f) ⊕ ((b ⊗ f) ⊕ (c ⊗ e)))
      ≡⟨ cong (λ w → ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ w)
              (sym (⊕-assoc (negate (c ⊗ f)) (b ⊗ f) (c ⊗ e))) ⟩
    ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((negate (c ⊗ f) ⊕ (b ⊗ f)) ⊕ (c ⊗ e))
      ≡⟨ cong (λ w → ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ (w ⊕ (c ⊗ e)))
              (⊕-comm (negate (c ⊗ f)) (b ⊗ f)) ⟩
    ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ (((b ⊗ f) ⊕ negate (c ⊗ f)) ⊕ (c ⊗ e))
      ≡⟨ cong (λ w → ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ w)
              (⊕-assoc (b ⊗ f) (negate (c ⊗ f)) (c ⊗ e)) ⟩
    ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ (negate (c ⊗ f) ⊕ (c ⊗ e)))
      ≡⟨ cong (λ u → ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ u))
              (⊕-comm (negate (c ⊗ f)) (c ⊗ e)) ⟩
    ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f)))
  ∎

mul3-≡₂ : ∀ a b c d e f →
  ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))) ⊕ ((c ⊗ f) ⊗ head (tail red3))
  ≡ ((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((c ⊗ d) ⊕ (c ⊗ f))
mul3-≡₂ a b c d e f =
  begin
    ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))) ⊕ ((c ⊗ f) ⊗ head (tail red3))
      ≡⟨ cong (λ w → ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))) ⊕ ((c ⊗ f) ⊗ w)) r₁-def ⟩
    ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))) ⊕ ((c ⊗ f) ⊗ T₁)
      ≡⟨ cong (λ w → ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))) ⊕ w) (⊗-identityʳ (c ⊗ f)) ⟩
    ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d))) ⊕ (c ⊗ f)
      ≡⟨ ⊕-assoc (a ⊗ f) ((b ⊗ e) ⊕ (c ⊗ d)) (c ⊗ f) ⟩
    (a ⊗ f) ⊕ (((b ⊗ e) ⊕ (c ⊗ d)) ⊕ (c ⊗ f))
      ≡⟨ cong (λ w → (a ⊗ f) ⊕ w) (⊕-assoc (b ⊗ e) (c ⊗ d) (c ⊗ f)) ⟩
    (a ⊗ f) ⊕ ((b ⊗ e) ⊕ ((c ⊗ d) ⊕ (c ⊗ f)))
      ≡⟨ sym (⊕-assoc (a ⊗ f) (b ⊗ e) ((c ⊗ d) ⊕ (c ⊗ f))) ⟩
    ((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((c ⊗ d) ⊕ (c ⊗ f))
  ∎

-- 乘法对拍（分量拼接）【结构证明】
mul3-≡ : ∀ (u v : Vec Trit 3) → toG27 (mulMod3 u v) ≡ toG27 u *gf27 toG27 v
mul3-≡ (a ∷ b ∷ c ∷ []) (d ∷ e ∷ f ∷ []) =
  cong-triple (mul3-≡₀ a b c d e f) (mul3-≡₁ a b c d e f) (mul3-≡₂ a b c d e f)

--------------------------------------------------------------------------------
-- §5. k=3 定律——「对拍借用」GF27 已证定律
--------------------------------------------------------------------------------

-- GF27 本体缺零律，本地补两条（ˡ 定义归约；ʳ 结构证明）
*gf27-zeroˡ : ∀ (x : GF27) → gf27-zero *gf27 x ≡ gf27-zero
*gf27-zeroˡ x = refl

*gf27-zeroʳ : ∀ (x : GF27) → x *gf27 gf27-zero ≡ gf27-zero
*gf27-zeroʳ (a , b , c) = cong-triple e₀ e₁ e₂
  where
    e₀ : (a ⊗ T₀) ⊕ negate ((b ⊗ T₀) ⊕ (c ⊗ T₀)) ≡ T₀
    e₀ = cong₂ (λ u v → u ⊕ negate v)
               (⊗-zeroʳ a) (cong₂ _⊕_ (⊗-zeroʳ b) (⊗-zeroʳ c))
    e₁ : ((a ⊗ T₀) ⊕ (b ⊗ T₀)) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ negate (c ⊗ T₀))) ≡ T₀
    e₁ = trans (cong (λ u → (u ⊕ (b ⊗ T₀)) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ negate (c ⊗ T₀))))
                      (⊗-zeroʳ a))
         (trans (cong (λ v → ((T₀ ⊕ v) ⊕ (v ⊕ ((c ⊗ T₀) ⊕ negate (c ⊗ T₀)))))
                      (⊗-zeroʳ b))
                (cong (λ w → ((T₀ ⊕ T₀) ⊕ (T₀ ⊕ (w ⊕ negate w))))
                      (⊗-zeroʳ c)))
    e₂ : ((a ⊗ T₀) ⊕ (b ⊗ T₀)) ⊕ ((c ⊗ T₀) ⊕ (c ⊗ T₀)) ≡ T₀
    e₂ = trans (cong (λ u → (u ⊕ (b ⊗ T₀)) ⊕ ((c ⊗ T₀) ⊕ (c ⊗ T₀)))
                      (⊗-zeroʳ a))
         (trans (cong (λ v → ((T₀ ⊕ v) ⊕ ((c ⊗ T₀) ⊕ (c ⊗ T₀))))
                      (⊗-zeroʳ b))
                (cong (λ w → ((T₀ ⊕ T₀) ⊕ (w ⊕ w)))
                      (⊗-zeroʳ c)))

*3-comm : ∀ (u v : Vec Trit 3) → mulMod3 u v ≡ mulMod3 v u
*3-comm u v = toG27-inj (mulMod3 u v) (mulMod3 v u) (
  begin
    toG27 (mulMod3 u v)     ≡⟨ mul3-≡ u v ⟩
    toG27 u *gf27 toG27 v   ≡⟨ *gf27-comm (toG27 u) (toG27 v) ⟩
    toG27 v *gf27 toG27 u   ≡⟨ sym (mul3-≡ v u) ⟩
    toG27 (mulMod3 v u)
  ∎)

*3-assoc : ∀ (u v w : Vec Trit 3) →
  mulMod3 (mulMod3 u v) w ≡ mulMod3 u (mulMod3 v w)
*3-assoc u v w = toG27-inj (mulMod3 (mulMod3 u v) w) (mulMod3 u (mulMod3 v w)) (
  begin
    toG27 (mulMod3 (mulMod3 u v) w)    ≡⟨ mul3-≡ (mulMod3 u v) w ⟩
    toG27 (mulMod3 u v) *gf27 toG27 w  ≡⟨ cong (_*gf27 toG27 w) (mul3-≡ u v) ⟩
    (toG27 u *gf27 toG27 v) *gf27 toG27 w ≡⟨ *gf27-assoc (toG27 u) (toG27 v) (toG27 w) ⟩
    toG27 u *gf27 (toG27 v *gf27 toG27 w) ≡⟨ sym (cong (toG27 u *gf27_) (mul3-≡ v w)) ⟩
    toG27 u *gf27 toG27 (mulMod3 v w)  ≡⟨ sym (mul3-≡ u (mulMod3 v w)) ⟩
    toG27 (mulMod3 u (mulMod3 v w))
  ∎)

*3-identityˡ : ∀ (v : Vec Trit 3) → mulMod3 one3 v ≡ v
*3-identityˡ v = toG27-inj (mulMod3 one3 v) v (
  begin
    toG27 (mulMod3 one3 v)  ≡⟨ mul3-≡ one3 v ⟩
  gf27-one *gf27 toG27 v    ≡⟨ *gf27-identityˡ (toG27 v) ⟩
    toG27 v
  ∎)

*3-identityʳ : ∀ (v : Vec Trit 3) → mulMod3 v one3 ≡ v
*3-identityʳ v = toG27-inj (mulMod3 v one3) v (
  begin
    toG27 (mulMod3 v one3)  ≡⟨ mul3-≡ v one3 ⟩
  toG27 v *gf27 gf27-one    ≡⟨ *gf27-identityʳ (toG27 v) ⟩
    toG27 v
  ∎)

*3-zeroˡ : ∀ (v : Vec Trit 3) → mulMod3 zero3 v ≡ zero3
*3-zeroˡ v = toG27-inj (mulMod3 zero3 v) zero3 (
  begin
    toG27 (mulMod3 zero3 v)  ≡⟨ mul3-≡ zero3 v ⟩
  gf27-zero *gf27 toG27 v    ≡⟨ *gf27-zeroˡ (toG27 v) ⟩
    gf27-zero
  ∎)

*3-zeroʳ : ∀ (v : Vec Trit 3) → mulMod3 v zero3 ≡ zero3
*3-zeroʳ v = toG27-inj (mulMod3 v zero3) zero3 (
  begin
    toG27 (mulMod3 v zero3)  ≡⟨ mul3-≡ v zero3 ⟩
  toG27 v *gf27 gf27-zero    ≡⟨ *gf27-zeroʳ (toG27 v) ⟩
    gf27-zero
  ∎)

*3-distribˡ : ∀ (u v w : Vec Trit 3) →
  mulMod3 u (addT3 v w) ≡ addT3 (mulMod3 u v) (mulMod3 u w)
*3-distribˡ u v w = toG27-inj (mulMod3 u (addT3 v w)) (addT3 (mulMod3 u v) (mulMod3 u w)) (
  begin
    toG27 (mulMod3 u (addT3 v w))                        ≡⟨ mul3-≡ u (addT3 v w) ⟩
    toG27 u *gf27 toG27 (addT3 v w)                      ≡⟨ cong (toG27 u *gf27_) (addT3-≡ v w) ⟩
    toG27 u *gf27 (toG27 v +gf27 toG27 w)               ≡⟨ *gf27-distribˡ (toG27 u) (toG27 v) (toG27 w) ⟩
    (toG27 u *gf27 toG27 v) +gf27 (toG27 u *gf27 toG27 w) ≡⟨ cong₂ _+gf27_ (sym (mul3-≡ u v)) (sym (mul3-≡ u w)) ⟩
    toG27 (mulMod3 u v) +gf27 toG27 (mulMod3 u w)       ≡⟨ sym (addT3-≡ (mulMod3 u v) (mulMod3 u w)) ⟩
    toG27 (addT3 (mulMod3 u v) (mulMod3 u w))
  ∎)

*3-distribʳ : ∀ (u v w : Vec Trit 3) →
  mulMod3 (addT3 u v) w ≡ addT3 (mulMod3 u w) (mulMod3 v w)
*3-distribʳ u v w = toG27-inj (mulMod3 (addT3 u v) w) (addT3 (mulMod3 u w) (mulMod3 v w)) (
  begin
    toG27 (mulMod3 (addT3 u v) w)                        ≡⟨ mul3-≡ (addT3 u v) w ⟩
    toG27 (addT3 u v) *gf27 toG27 w                      ≡⟨ cong (_*gf27 toG27 w) (addT3-≡ u v) ⟩
    (toG27 u +gf27 toG27 v) *gf27 toG27 w               ≡⟨ *gf27-distribʳ (toG27 u) (toG27 v) (toG27 w) ⟩
    (toG27 u *gf27 toG27 w) +gf27 (toG27 v *gf27 toG27 w) ≡⟨ cong₂ _+gf27_ (sym (mul3-≡ u w)) (sym (mul3-≡ v w)) ⟩
    toG27 (mulMod3 u w) +gf27 toG27 (mulMod3 v w)       ≡⟨ sym (addT3-≡ (mulMod3 u w) (mulMod3 v w)) ⟩
    toG27 (addT3 (mulMod3 u w) (mulMod3 v w))
  ∎)

+3-comm : ∀ (u v : Vec Trit 3) → addT3 u v ≡ addT3 v u
+3-comm u v = toG27-inj (addT3 u v) (addT3 v u) (
  begin
    toG27 (addT3 u v)      ≡⟨ addT3-≡ u v ⟩
    toG27 u +gf27 toG27 v ≡⟨ +gf27-comm (toG27 u) (toG27 v) ⟩
    toG27 v +gf27 toG27 u ≡⟨ sym (addT3-≡ v u) ⟩
    toG27 (addT3 v u)
  ∎)

+3-assoc : ∀ (u v w : Vec Trit 3) → addT3 (addT3 u v) w ≡ addT3 u (addT3 v w)
+3-assoc u v w = toG27-inj (addT3 (addT3 u v) w) (addT3 u (addT3 v w)) (
  begin
    toG27 (addT3 (addT3 u v) w)    ≡⟨ addT3-≡ (addT3 u v) w ⟩
    toG27 (addT3 u v) +gf27 toG27 w ≡⟨ cong (_+gf27 toG27 w) (addT3-≡ u v) ⟩
    (toG27 u +gf27 toG27 v) +gf27 toG27 w ≡⟨ +gf27-assoc (toG27 u) (toG27 v) (toG27 w) ⟩
    toG27 u +gf27 (toG27 v +gf27 toG27 w) ≡⟨ sym (cong (toG27 u +gf27_) (addT3-≡ v w)) ⟩
    toG27 u +gf27 toG27 (addT3 v w) ≡⟨ sym (addT3-≡ u (addT3 v w)) ⟩
    toG27 (addT3 u (addT3 v w))
  ∎)

+3-identityˡ : ∀ (v : Vec Trit 3) → addT3 zero3 v ≡ v
+3-identityˡ v = toG27-inj (addT3 zero3 v) v (
  begin
    toG27 (addT3 zero3 v)  ≡⟨ addT3-≡ zero3 v ⟩
  gf27-zero +gf27 toG27 v ≡⟨ +gf27-identityˡ (toG27 v) ⟩
    toG27 v
  ∎)

+3-inverse : ∀ (v : Vec Trit 3) → addT3 v (negVec v) ≡ zero3
+3-inverse (a ∷ b ∷ c ∷ []) = toG27-inj (addT3 (a ∷ b ∷ c ∷ []) (negVec (a ∷ b ∷ c ∷ []))) zero3 (
  begin
    toG27 (addT3 (a ∷ b ∷ c ∷ []) (negVec (a ∷ b ∷ c ∷ []))) ≡⟨ addT3-≡ (a ∷ b ∷ c ∷ []) (negVec (a ∷ b ∷ c ∷ [])) ⟩
  (a , b , c) +gf27 (negate a , negate b , negate c)         ≡⟨ +gf27-inverse (a , b , c) ⟩
    gf27-zero
  ∎)

--------------------------------------------------------------------------------
-- §6. 立界清单（复述头注，作为模块内可见边界）
--------------------------------------------------------------------------------
-- B1 任意 k 不可约多项式存在性：立界不证（x^{3^k}−x 无重根 + Möbius 反演
--    Σ_{d∣k} d·N_d = 3^k ⇒ N_k ≥ 1）。本模块 P 一律以数据给定。
-- B2 monic 性不类型强制（redTable 丢弃首系数，调用方约束）。
-- B3 「P 不可约 ⇒ GF3K k 为域」的一般定理不设；域性逐实例对拍借用。
-- B4 k=6 / GF36 对拍未做；k=0/k=1 退化载体不承载定律。
-- B5 泛型层 mulPoly 的抽象语义定理不设；只有 §2/§4 逐实例对拍。
-- B6 泛型循环 mulMod 3 red3 的符号传输未闭合（归一形 ⊕T₀ 残渣）；
--    k=3 实例以 red3-数据驱动内联公式交付并闭合对拍 GF27，
--    内联公式与泛型循环在 k=3 的逐点相等留待后续。
--
-- 0 postulate.
