{-# OPTIONS --rewriting --guardedness #-}

-- | _PDH4
-- DH-4a：ab-计数桥 + red₃ 系数约化 + CT-2/CT-3 two-chain 实例
--
-- 数学背景（对照定理族——`docs/plan/discrete-hurewicz-dh4-design.md` C 案首件）：
--   Gao-Yang Thm 5.4 的 ℤ 版核 = 交换子（阿贝尔化动机）；本地 GF(3) 版核 = 3·子幺半群类。
--   两版的**真桥**是 CT-2 系数约化方块：h₁₃ ≡ red₃ ∘ (ab 计数数据)——
--   「阿贝尔化后系数 mod 3 约化」正是本地 GF(3) 版的语义定位。
-- 核心原则：
--   1. ab-计数桥 = (npos, nneg) 计数对（_PPI4i walk4-classify 全证的 dim-1 边链数据）；
--   2. red₃ = trit3（ℕ→GF(3) 模 3 形）——同态桥 red₃-+ 是 CT-2 的核心引理；
--   3. CT-3 定名「模 3 纤维定理」（Ker h₁₃ = 3·类）——**不冒充 commutator 形**（诚实边界）；
--   4. 代码为本文档为镜——机件锚：_PDH1（h₁/h₁₃/trit3/div3）、_PPI4g（npos/nneg/loopK/loop-diagonal）、
--      _PPI4i（unloop0）、_PDH1（npos-++/3m/trit3-3m）。
-- 包含：§0 基础件（⊕ 小律/trit3-suc）｜§1 ab-计数桥｜§2 red₃ 约化｜§3 CT-2 实例｜§4 CT-3 纤维定理

module _PDH4 where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Cubical.Foundations.Prelude
  using (_≡_; refl; sym; cong; cong₂; _∙_; subst)
open import Cubical.HITs.SetQuotients using (_/_; [_])

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Synthesis.BarceloAHomotopy using (Walk; nil; cons; _++w_)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_)
open import _PPI4 using (Gskel)
open import _PPI4g using (loopK; npos; nneg; npos-loopK; loop-diagonal)
open import _PPI4i using (unloop0)
open import _PDH1
  using (h₁; h₁₃; trit3; npos-++; 3m; trit3-3m; div3; h₁-hom)

--------------------------------------------------------------------------------
-- §0 基础件（⊕ 小律——3/27 case 全具体构造子，零世界跨界）
--------------------------------------------------------------------------------

-- T₀ 左单位（按 x 分 3 案——避免 ⊕ 定义取向风险）
⊕-zeroˡ : ∀ x → T₀ ⊕ x ≡ x
⊕-zeroˡ T₀ = refl
⊕-zeroˡ T₁ = refl
⊕-zeroˡ T₂ = refl

-- ⊕ 结合律（27-case 穷举——穷举边界 ≤27 内）
⊕-assocT : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assocT T₀ T₀ T₀ = refl
⊕-assocT T₀ T₀ T₁ = refl
⊕-assocT T₀ T₀ T₂ = refl
⊕-assocT T₀ T₁ T₀ = refl
⊕-assocT T₀ T₁ T₁ = refl
⊕-assocT T₀ T₁ T₂ = refl
⊕-assocT T₀ T₂ T₀ = refl
⊕-assocT T₀ T₂ T₁ = refl
⊕-assocT T₀ T₂ T₂ = refl
⊕-assocT T₁ T₀ T₀ = refl
⊕-assocT T₁ T₀ T₁ = refl
⊕-assocT T₁ T₀ T₂ = refl
⊕-assocT T₁ T₁ T₀ = refl
⊕-assocT T₁ T₁ T₁ = refl
⊕-assocT T₁ T₁ T₂ = refl
⊕-assocT T₁ T₂ T₀ = refl
⊕-assocT T₁ T₂ T₁ = refl
⊕-assocT T₁ T₂ T₂ = refl
⊕-assocT T₂ T₀ T₀ = refl
⊕-assocT T₂ T₀ T₁ = refl
⊕-assocT T₂ T₀ T₂ = refl
⊕-assocT T₂ T₁ T₀ = refl
⊕-assocT T₂ T₁ T₁ = refl
⊕-assocT T₂ T₁ T₂ = refl
⊕-assocT T₂ T₂ T₀ = refl
⊕-assocT T₂ T₂ T₁ = refl
⊕-assocT T₂ T₂ T₂ = refl

-- trit3 后继形：(k+1) mod 3 = 1 + (k mod 3)（T₁ ⊕——模 3 后继=加一）
trit3-suc : ∀ k → trit3 (suc k) ≡ T₁ ⊕ trit3 k
trit3-suc zero = refl
trit3-suc (suc zero) = refl
trit3-suc (suc (suc zero)) = refl
trit3-suc (suc (suc (suc k))) = trit3-suc k

--------------------------------------------------------------------------------
-- §1 ab-计数桥（npos/nneg 计数对 = π₁^ab 数据——dim-1 边链形）
--------------------------------------------------------------------------------

-- ab 计数数据（walk 级——_PPI4i walk4-classify 的四参不变量在闭走处的对角面）
abData : ∀ {u v} → Walk (Gskel two-chain) u v → ℕ × ℕ
abData w = npos w , nneg w

-- nneg 拼接同态（npos-++ 的镜像——_PDH1:48 同构形）
nneg-++ : ∀ {u v w} (p : Walk (Gskel two-chain) u v) (q : Walk (Gskel two-chain) v w)
  → nneg (p ++w q) ≡ nneg p +ℕ nneg q
nneg-++ (nil _) q = refl
nneg-++ (cons (inj₁ e) p) q = nneg-++ p q
nneg-++ (cons (inj₂ e) p) q = cong suc (nneg-++ p q)

-- ab 拼接同态（计数对的加法性——π₁^ab 同态面）
ab-++ : ∀ {u v w} (p : Walk (Gskel two-chain) u v) (q : Walk (Gskel two-chain) v w)
  → abData (p ++w q) ≡ (npos p +ℕ npos q , nneg p +ℕ nneg q)
ab-++ p q = cong₂ _,_ (npos-++ p q) (nneg-++ p q)

-- ab 对角定理（闭走计数对沿对角——loop-diagonal 直引，_PPI4g:200）
ab-diag : (w : Walk (Gskel two-chain) fzero fzero) → npos w ≡ nneg w
ab-diag = loop-diagonal

--------------------------------------------------------------------------------
-- §2 red₃ 系数约化（ℕ→GF(3) 模 3 形——h₁₃ ≡ red₃ ∘ h₁ 分解）
--------------------------------------------------------------------------------

-- 系数约化（文档名形——= trit3 的对照定理名）
red₃ : ℕ → Trit
red₃ = trit3

-- 同态桥（CT-2 核心引理）：red₃ (m+n) ≡ red₃ m ⊕ red₃ n
red₃-+ : ∀ m n → red₃ (m +ℕ n) ≡ red₃ m ⊕ red₃ n
red₃-+ zero n = sym (⊕-zeroˡ (red₃ n))
red₃-+ (suc m) n =
  trit3-suc (m +ℕ n)
    ∙ cong (λ x → T₁ ⊕ x) (red₃-+ m n)
    ∙ sym (⊕-assocT T₁ (red₃ m) (red₃ n))
    ∙ cong (λ x → x ⊕ red₃ n) (sym (trit3-suc m))

-- 消失律（3 的倍数约化为零——trit3-3m 对照名）
red₃-3m : ∀ m → red₃ (3m m) ≡ T₀
red₃-3m = trit3-3m

-- 分解引理：h₁₃ ≡ red₃ ∘ h₁（定义相等——组合投影免二次下降的 defeq 红利）
h₁₃-decomp : ∀ q → h₁₃ q ≡ red₃ (h₁ q)
h₁₃-decomp q = refl

--------------------------------------------------------------------------------
-- §3 CT-2 交换方块 two-chain 实例
--------------------------------------------------------------------------------

-- CT-2 同态面（quotient 级）：h₁₃ 是到 (Trit, ⊕) 的幺半群同态
--   = 「π₁^ab ⊗ mod3」语义的可构造形——h₁ 同态（_PDH1）经 red₃-+ 搬运
ct2-hom : ∀ q q' → h₁₃ (q ⊞ᵈ q') ≡ h₁₃ q ⊕ h₁₃ q'
ct2-hom q q' = cong red₃ (h₁-hom q q') ∙ red₃-+ (h₁ q) (h₁ q')

-- CT-2 方块 walk 形：投影经 ab 两分量一致（对角一致性）
ct2-square : (w : Walk (Gskel two-chain) fzero fzero)
  → red₃ (proj₁ (abData w)) ≡ red₃ (proj₂ (abData w))
ct2-square w = cong red₃ (ab-diag w)

--------------------------------------------------------------------------------
-- §4 CT-3 模 3 纤维定理（two-chain 形——Ker h₁₃ = 3·类）
--------------------------------------------------------------------------------

-- 纤维特征（walk 级）：trit3 (npos w) ≡ T₀ ⟹ w 是 3m 个 loopK 的幂
--   （unloop0 重构 + div3 分解合成——Gao-Yang Thm 5.4 的模 3 版**纤维形**，非 commutator 形）
ker-walk-3m : (w : Walk (Gskel two-chain) fzero fzero)
  → trit3 (npos w) ≡ T₀ → Σ ℕ (λ m → w ≡ loopK (3m m))
ker-walk-3m w h with div3 (npos w) h
... | m , eq = m , (unloop0 w ∙ cong loopK eq)

-- 反向（3m 幂必落核——npos-loopK 计数桥 + trit3-3m 通道）
ker-3m-walk : ∀ m → trit3 (npos (loopK (3m m))) ≡ T₀
ker-3m-walk m = cong trit3 (npos-loopK (3m m)) ∙ trit3-3m m

--------------------------------------------------------------------------------
-- §5 核对层（two-chain 实例——CT-2/CT-3 交叉）
--------------------------------------------------------------------------------

-- CT-2 同态实例（mod 3 加法表核对）
check-red3-+ : red₃ (2 +ℕ 2) ≡ red₃ 2 ⊕ red₃ 2
check-red3-+ = red₃-+ 2 2

-- CT-2 方块实例（loopK 2 对角）
check-ct2-sq-w2 : red₃ (proj₁ (abData (loopK 2))) ≡ red₃ (proj₂ (abData (loopK 2)))
check-ct2-sq-w2 = ct2-square (loopK 2)

-- CT-3 纤维实例（loopK 3：npos=3 → 落核）
check-ker-w3 : trit3 (npos (loopK 3)) ≡ T₀
check-ker-w3 = ker-3m-walk 1
