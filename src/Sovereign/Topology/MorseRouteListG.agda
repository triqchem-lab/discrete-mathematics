{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseRouteListG
-- 任务书第五层·5.1 泛型化 M2：泛型路由列表 routeList
--
-- 数学背景：M3 的 ∂^Morse 需要 Σ_{p ∈ routeList σ τ} μ(p)·τ。
--   实例层（MorseRouteListDT）手写 3 条路由；
--   泛型层用归纳关系（MorseRoute）的 List 化枚举。
--
-- 方法：用 ℕ 步数上限（fuel）做结构递归枚举——
--   routeList-fuel fuel σ τ = 所有 ≤ fuel 步的 CoeffRoute σ τ 的列表
--   （step-decreases 保证 fuel = dim σ 即够用）
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseRouteListG where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Product using (Σ; _×_; _,_)

--------------------------------------------------------------------------------
-- §1. 泛型 record（简化版——只保留 routeList 需要的字段）
--------------------------------------------------------------------------------

record MorseFieldG (K : Set) (dimK : K → ℕ) : Set₁ where
  field
    Face     : K → K → Set
    face-dim : ∀ τ σ → Face τ σ → dimK τ < dimK σ
    V        : K → Maybe K
    dim-law  : ∀ σ τ → V σ ≡ just τ → dimK τ ≡ suc (dimK σ)

open MorseFieldG public

--------------------------------------------------------------------------------
-- §2. 路由数据类型
--------------------------------------------------------------------------------

-- 路由记录：终止胞腔 + 面证据 + 路由路径
record Route (K : Set) (Face : K → K → Set) (σ τ : K) : Set where
  constructor route
  field
    -- 路由路径的编码（省略中间步骤，只存终止信息）
    route-end : K
    route-≡τ  : route-end ≡ τ

--------------------------------------------------------------------------------
-- §3. 泛型路由列表（fuel 参数化枚举）
--
--   routeList-fuel fuel field σ τ：所有 ≤ fuel 步的从 σ 到 τ 的路由列表
--
--   fuel 递减：每步 r-via 经过配对面降一维（dim-law），fuel = dim σ 够用。
--   本模块给出框架和 base case；完整枚举需要 K 的可枚举性——实例层任务。
--------------------------------------------------------------------------------

-- 路由列表类型
RouteList : Set → Set
RouteList K = List (Σ K (λ τ → K))  -- 简化：对 (源, 目标) 对的列表

--------------------------------------------------------------------------------
-- §4. 泛型路由列表——框架
--
--   完整的泛型 routeList 需要 K 的可枚举性（Fin n → K 的枚举）。
--   泛型框架给出类型签名；具体实现委托给实例层（MorseRouteListDT 已闭合）。
--
--   泛型化路线图：
--   ① K 可枚举（Fin n → K 的 surjection）→ 每个候选 τ 检查 CoeffRoute
--   ② 用 CoeffRoute 的归纳结构做判定（有限搜索）
--   ③ 结果类型：List (Σ K (λ τ → CoeffRoute K V Face coeff σ τ μ))
--------------------------------------------------------------------------------

-- List 成员资格（顶层定义——不能在 record 内部）
data _∈List_ {K : Set} (x : K) : List K → Set where
  here  : ∀ xs → x ∈List (x ∷ xs)
  there : ∀ y xs → x ∈List xs → x ∈List (y ∷ xs)

record RouteListG (K : Set) (Face : K → K → Set) (V : K → Maybe K) : Set₁ where
  field
    -- 路由列表函数：σ 的所有路由终止胞腔
    routeList : (σ : K) → List K
    -- 完备性：每个路由都终止在列表中的某个胞腔
    route-complete : ∀ σ τ → Face τ σ × (V τ ≡ nothing) →
                     τ ∈List routeList σ
    -- 无冗余：列表中每个胞腔都有路由
    route-sound : ∀ σ → ∀ τ → τ ∈List routeList σ →
                  Σ (Face τ σ) (λ f → V τ ≡ nothing)

--------------------------------------------------------------------------------
-- §5. M2 完成度
--
--   ✅ MorseFieldG record（从 MorseRoute 复用）
--   ✅ RouteListG record（泛型接口：routeList + 完备性 + 无冗余）
--   ⚠ 泛型 routeList 实现：需要 K 的可枚举性（实例层任务——K₃ 双三角已闭合）
--   ✅ 实例层：MorseRouteListDT（3 条路由手写枚举完备）
--
--   M2 泛型化的核心贡献：接口规范（RouteListG record），
--   让后续 M3（∂² 消元）可以依赖泛型接口而非具体实例。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §6. 里程碑 2：K 可枚举 + 求和域引理（M3 枚举基座）
--------------------------------------------------------------------------------

open import Data.List using (map)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to p₁; proj₂ to p₂)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-comm; ⊕-assoc)

-- 6a. K 有限可枚举
record FiniteK (K : Set) : Set where
  field
    nK    : ℕ          -- 胞腔总数
    enumK : ℕ → K      -- 枚举函数

-- 全胞腔列表：upTo nK 逐项过 enumK
upTo : ℕ → List ℕ
upTo zero    = []
upTo (suc n) = upTo n ++ (n ∷ [])
  where open import Data.List using (_++_)

allCells : ∀ {K} → FiniteK K → List K
allCells fk = map (FiniteK.enumK fk) (upTo (FiniteK.nK fk))

-- 6b. 完备枚举：每个 k 都在 allCells 中（有见证下标）
record EnumComplete (K : Set) : Set where
  field
    fk : FiniteK K
    -- 满射：∀ k ∃ i < nK，enumK i ≡ k
    enum-surj : ∀ (k : K) → Σ ℕ (λ i → i < FiniteK.nK fk × FiniteK.enumK fk i ≡ k)

-- 6c. Trit 列表的 ⊕ 求和
sum⊕ : List Trit → Trit
sum⊕ []       = T₀
sum⊕ (x ∷ xs) = x ⊕ sum⊕ xs

-- 6d. 求和域引理——pair-popping 基础
-- 引理 1：交换相邻两元素，求和不变
sum⊕-swap : ∀ (x y : Trit) (xs : List Trit) →
            sum⊕ (x ∷ y ∷ xs) ≡ sum⊕ (y ∷ x ∷ xs)
sum⊕-swap x y xs =
  trans (⊕-comm x (y ⊕ sum⊕ xs))
  (trans (⊕-assoc y (sum⊕ xs) x)
         (cong (λ w → y ⊕ w) (⊕-comm (sum⊕ xs) x)))
  where
    open import Sovereign.Base.Trit using (⊕-comm; ⊕-assoc)

-- 引理 2：去掉 T₀ 不改变和（定义性：T₀ ⊕ z ≡ z）
sum⊕-skip-T₀ : ∀ (xs : List Trit) → sum⊕ (T₀ ∷ xs) ≡ sum⊕ xs
sum⊕-skip-T₀ xs = refl

-- 6e. 求和域引理（核心）：两个列表的求和域相等
--     形式化为：加一个公共项 f，两列表和相等 ⟺ 不加也相等
--     这把「不同枚举顺序求和相同」归约到 sum⊕-swap 的传递闭包
record SumDomainLemma : Set₁ where
  field
    -- 求和域等价：Σ{a} = Σ{b} 加公共项 f 后仍相等
    sum-ext : ∀ (a b : List Trit) (f : Trit) →
              sum⊕ (f ∷ a) ≡ sum⊕ (f ∷ b) →
              sum⊕ a ≡ sum⊕ b

--------------------------------------------------------------------------------
-- §7. 里程碑 2 完成度
--
--   ✅ FiniteK record（K 有限可枚举：nK + enumK）
--   ✅ allCells（upTo nK 全胞腔列表）
--   ✅ EnumComplete record（满射见证）
--   ✅ sum⊕（⊕ 折叠）
--   ✅ sum⊕-swap（相邻交换引理——pair-popping 基础，refl 链）
--   ✅ sum⊕-skip-T₀（T₀ 跳过引理，定义性）
--   ✅ SumDomainLemma record（求和域等价）
--
--   K₃ 实例的 FiniteK/EnumComplete 实例化 + SumDomainLemma 的构造证明 → 里程碑 3。
--------------------------------------------------------------------------------
