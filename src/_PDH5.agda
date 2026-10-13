{-# OPTIONS --rewriting --guardedness #-}

-- | _PDH5 —— DH-4b：n=2 离散 Hurewicz（S²ᵈ 面）+ 对齐续
-- 数学背景：h₂ : π₂ᵈ → H₂ 的组合形。2-腔（Ω2Walk）的每个 AStep 携带三角
--   (x,y,z)（slide/expand 隐式三元）——h₂ = 步的带号面计数（slide +、expand −）。
--   H₂ 面 = S²ᵈ（∂Δ³ 四面边界）的 2-链/闭链（GF(3) 系数）；fund2 = 基本 2-闭链
--   （交错定向 f012−f013+f023−f123）——∂₂ fund2 ≡ 0 全边核对。
-- 核心原则：
-- 1. 组合形即终形（不碰 ℝⁿ）；面数据 = 四面四面片（Face2 四构造子）；
-- 2. h₂ 构造携带（步→面单项）+ 带号（negT 本地形——T₁↔T₂ 对换）；
-- 3. 诚实分层：h₂ 定义层+实例+骨架；一般良定义/满性立界注记。
-- 包含：Face2/Edge2/∂₂ 表｜fund2 基本闭链+全边核对｜h₂/h₂-step（带号面计数）
--       ｜omega2-wit/witb 归零实例｜n=2 Hurewicz 骨架+对齐续注记

module _PDH5 where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Synthesis.BarceloAHomotopy using (Walk; AStep; slide; expand)
open import _PPI5d using (Ω2Walk; nil2; cons2; s2-adj; s2v0; w3; w'; omega2-wit; face012-slide; face012-expand)

-- ─── §1 S²ᵈ 面/边/2-链（组合链面——GF(3) 系数）────────────────────

-- 四面片（∂Δ³ 的四个三角面——顶点集 Fin 4）
data Face2 : Set where
  f012 f013 f023 f123 : Face2

-- 六条有序边（i<j 规范形）
data Edge2 : Set where
  e01 e02 e03 e12 e13 e23 : Edge2

-- 取负（Trit 上 −：T₁↔T₂ 对换、T₀ 固定——3-case 自含）
negT : Trit → Trit
negT T₀ = T₀
negT T₁ = T₂
negT T₂ = T₁

-- 面边界表 ∂₂ : Face2 → Edge2 → Trit
--   定向约定（升序顶点形）：∂(i,j,k) = eᵢⱼ ⊕ eⱼₖ ⊖ eᵢₖ
∂₂ : Face2 → Edge2 → Trit
∂₂ f012 e01 = T₁
∂₂ f012 e12 = T₁
∂₂ f012 e02 = T₂
∂₂ f013 e01 = T₁
∂₂ f013 e13 = T₁
∂₂ f013 e03 = T₂
∂₂ f023 e02 = T₁
∂₂ f023 e23 = T₁
∂₂ f023 e03 = T₂
∂₂ f123 e12 = T₁
∂₂ f123 e23 = T₁
∂₂ f123 e13 = T₂
∂₂ _ _ = T₀

-- 2-链 = 面系数函数形
Chain2 : Set
Chain2 = Face2 → Trit

zeroC : Chain2
zeroC _ = T₀

addC : Chain2 → Chain2 → Chain2
addC c₁ c₂ f = c₁ f ⊕ c₂ f

-- 面单项（带号）
sing : Face2 → Chain2
sing f012 f012 = T₁
sing f013 f013 = T₁
sing f023 f023 = T₁
sing f123 f123 = T₁
sing _ _ = T₀

negC : Chain2 → Chain2
negC c f = negT (c f)

-- 标量乘（Trit 自含——免 ⊗ 算符歧义：T₀ 零化/T₁ 单位/T₂ 对换乘）
mulT : Trit → Trit → Trit
mulT T₀ _ = T₀
mulT T₁ x = x
mulT T₂ T₀ = T₀
mulT T₂ T₁ = T₂
mulT T₂ T₂ = T₁

-- 2-链的边界（∑ 系数·∂₂ 面——全括号单行）
∂₂sum : Chain2 → Edge2 → Trit
∂₂sum c e = (mulT (c f012) (∂₂ f012 e) ⊕ mulT (c f013) (∂₂ f013 e)) ⊕ (mulT (c f023) (∂₂ f023 e) ⊕ mulT (c f123) (∂₂ f123 e))

-- ─── §2 基本 2-闭链（fund2）——H₂ 非平凡性内容件 ─────────────────

-- 交错定向：∂(0123) 的面符号 = (−1)^i（省 i 号顶点）→ (+,−,+,−)
fund2 : Chain2
fund2 f012 = T₁
fund2 f013 = T₂
fund2 f023 = T₁
fund2 f123 = T₂

-- 主定理（全边核对——6 边各 refl 级，系数表精确算术）：
--   每条边恰现于两面、定向相消（e03：f013⊖ 与 f023⊖ 双负 → T₂⊕T₂ ... 交错后相消）
fund2-cycle : (e : Edge2) → ∂₂sum fund2 e ≡ T₀
fund2-cycle e01 = refl
fund2-cycle e02 = refl
fund2-cycle e03 = refl
fund2-cycle e12 = refl
fund2-cycle e13 = refl
fund2-cycle e23 = refl

-- ─── §3 h₂：2-腔 → 2-链（带号面计数——DHurewicz dim-2 组合形）──────

-- 步分类器（免匹配范式：变量绑定视图——不带字面隐式，避免索引合一卡复合（#56/附录10））
stepTri : ∀ {w1 w2 : Walk s2-adj s2v0 s2v0} → AStep s2-adj w1 w2 → Bool × (Fin 4 × Fin 4 × Fin 4)
stepTri (slide {_} {x} {y} {z} _ _ _ _ _) = true , (x , y , z)
stepTri (expand {_} {x} {y} {z} _ _ _ _ _) = false , (x , y , z)

-- 面单项（字面形——四规范升序三角面 + 兜底零；独立函数无索引族）
faceOf : Fin 4 → Fin 4 → Fin 4 → Chain2
faceOf fzero (fsuc fzero) (fsuc (fsuc fzero)) = sing f012
faceOf fzero (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = sing f013
faceOf fzero (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = sing f023
faceOf (fsuc fzero) (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = sing f123
faceOf _ _ _ = zeroC

-- 步→面单项（slide 正 +f / expand 反 −f——带号）
h₂-step : ∀ {w1 w2 : Walk s2-adj s2v0 s2v0} → AStep s2-adj w1 w2 → Chain2
h₂-step s with stepTri s
... | true , (x , y , z) = faceOf x y z
... | false , (x , y , z) = negC (faceOf x y z)

-- h₂：2-腔折算（Ω2Walk 的 cons2 链逐段累加）
h₂ : ∀ {w1 w2 : Walk s2-adj s2v0 s2v0} → Ω2Walk s2-adj s2v0 w1 w2 → Chain2
h₂ (nil2 _) = zeroC
h₂ (cons2 s rest) = addC (h₂-step s) (h₂ rest)

-- ─── §4 S²ᵈ 实例核对（归零族——与 _PPI5i/_PPT4 对齐）────────────────

-- omega2-wit = slide(012)∘expand(012) 的闭 2-腔 → h₂ 归零（带号相消）
h₂-wit-f012 : h₂ omega2-wit f012 ≡ T₀
h₂-wit-f012 = refl
h₂-wit-f013 : h₂ omega2-wit f013 ≡ T₀
h₂-wit-f013 = refl
h₂-wit-f023 : h₂ omega2-wit f023 ≡ T₀
h₂-wit-f023 = refl
h₂-wit-f123 : h₂ omega2-wit f123 ≡ T₀
h₂-wit-f123 = refl

-- 纯步实例（slide 单步 = 正面单项——计算律样例）
chk-face : faceOf fzero (fsuc fzero) (fsuc (fsuc fzero)) f012 ≡ T₁
chk-face = refl

triX : ∀ {w1 w2 : Walk s2-adj s2v0 s2v0} → AStep s2-adj w1 w2 → Fin 4
triX s with stepTri s
... | _ , (x , _ , _) = x
triY : ∀ {w1 w2 : Walk s2-adj s2v0 s2v0} → AStep s2-adj w1 w2 → Fin 4
triY s with stepTri s
... | _ , (_ , y , _) = y
triZ : ∀ {w1 w2 : Walk s2-adj s2v0 s2v0} → AStep s2-adj w1 w2 → Fin 4
triZ s with stepTri s
... | _ , (_ , _ , z) = z

chk-x12 : triX face012-slide ≡ fzero
chk-x12 = refl
chk-y12 : triY face012-slide ≡ fsuc fzero
chk-y12 = refl

h₂-step12-f012 : h₂-step face012-slide f012 ≡ T₁
h₂-step12-f012 = refl

h₂-slide12-f012 : h₂ (cons2 face012-slide (nil2 w')) f012 ≡ T₁
h₂-slide12-f012 = refl

-- ─── §5 n=2 Hurewicz 骨架 + 对齐续注记（立界显式）────────────────
-- 骨架①（核侧——two-chain 形）：loop 2-腔 ⟹ h₂ ∈ ker ∂₂sum
--   已实证：omega2-wit（=k₂ 平凡类）↦ 零链（§4）——与 _PPI5i
--   k2-zero→class-triv（k₂ 填充见证 ⟹ π₂ 类平凡）**同向对齐**：
--   h₂(平凡类) = 0 的实例证据与「k₂ 平凡 ⟺ π₂ 平凡」构造向互证同源。
-- 骨架②（满侧——H₂ 每类有 2-腔代表）：fund2 的 2-腔实现待造
--   （= S²ᵈ 整面扫掠 2-腔——需 Ω3Walk 完备形邻域，_PPI5h Dir2 同族立界）。
-- 立界清单（诚实）：
--   (i) h₂ 良定义（Ω3Walk 合同性：同伦步面计数不变——需 fill-tri 面符号律）；
--   (ii) h₂ 的核 = 平凡类（与 _PPI5i 逆向合一——构造性边界）；
--   (iii) 满性（fund2 代表元）；
--   (iv) 非规范三角序（x,y,z 非升序）步的符号规约（兜底案升级）。
-- 对齐续注记：本件 h₂ 与 _PPT4 k2-face-s2（omega2-wit 面粘合数据）、
--   _PPI5i 对齐主定理构成「k₂ ↔ π₂ ↔ h₂」三面——DH-4b 的 n=2 离散
--   Hurewicz 形以 S²ᵈ 实例落地，与设计文档 CT-2/CT-3 两版对照面衔接。
