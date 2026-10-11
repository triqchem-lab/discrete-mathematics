{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4i —— 非闭 walk 四参分型（(u,v,n₊,n₋)）
--
-- 数学背景：Gskel two-chain 上 walk 的完全分类从闭 walk（loopK/rounds）推广到
-- 非闭 walk（u ≠ v）。四参形 = (起点 u, 终点 v, 正向步数 n₊, 反向步数 n₋)。
-- 两顶点图无自环、每向边唯一（edge01-canon/edge10-canon 正范）⇒ walk 由计数完全决定。
--
-- 核心原则：
--   1. 复用优先：loopK/loop-classify/unloop/npos/nneg（_PPI4g）零重证；
--   2. 正范形互递（unloop01 ↔ unloop1）——边正范 + 计数搬运；
--   3. 分型主件 walk4-classify：同 (npos,nneg) ⟹ w ≡ w'（构造性形）。
--
-- 包含：loopK1/walk01/walk10（正范 walk）· unloop01/unloop1/unloop10/unloop0（互递重构）
--       · walk4-classify（四参分型主件）· 核对层
module _PPI4i where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil; cons)
open import Sovereign.Topology.McCordPi0 using (two-chain; ⊑₂-01)
open import _PPI4 using (Gskel)
open import _PPI4g
  using (npos; nneg; loopK; loop-classify; unloop; npos-≡-rounds;
         edge01-canon; edge10-canon; 0≢1)
open import _PPI4c using (edgeGskel-neq)
open import _PPI4d using (e01; e10)

private
  module DG = DiGraph
  G : DiGraph
  G = Gskel two-chain

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：正范 walk（计数索引构造）
-- ────────────────────────────────────────────────────────────────────

-- 顶点 1 的往返序列（k 次——与 loopK 对偶）
loopK1 : ℕ → Walk G (fsuc fzero) (fsuc fzero)
loopK1 zero    = nil (fsuc fzero)
loopK1 (suc k) = cons e10 (cons e01 (loopK1 k))

-- 非闭正范 walk：0→1 由 nneg 索引（npos = suc nneg）；1→0 由 npos 索引（nneg = suc npos）
walk01 : ℕ → Walk G fzero (fsuc fzero)
walk01 k = cons e01 (loopK1 k)

walk10 : ℕ → Walk G (fsuc fzero) fzero
walk10 k = cons e10 (loopK k)

-- ────────────────────────────────────────────────────────────────────
-- ④ 主件层：重构互递（unloop 系推广）
-- ────────────────────────────────────────────────────────────────────

-- 闭 walk 的 npos 形重构（由 _PPI4g unloop + 计数对齐一跳得）
unloop0 : (w : Walk G fzero fzero) → w ≡ loopK (npos w)
unloop0 w = unloop w ∙ cong loopK (sym (npos-≡-rounds w))

-- 互递重构：01 ↔ 1、10 ↔ 0（边正范 + 尾递归 + 计数搬运三段）
mutual
  unloop01 : (w : Walk G fzero (fsuc fzero)) → w ≡ walk01 (nneg w)
  unloop01 (cons {v = fzero} e _) = ⊥-elim (edgeGskel-neq fzero fzero e reflᴱ)
  unloop01 (cons {v = fsuc fzero} e t) =
    (cong (λ x → cons x t) (edge01-canon e))
    ∙ (cong (cons e01) (unloop1 t))
    ∙ (cong walk01 (sym (cong (λ x → nneg (cons x t)) (edge01-canon e))))

  unloop1 : (t : Walk G (fsuc fzero) (fsuc fzero)) → t ≡ loopK1 (nneg t)
  unloop1 (nil (fsuc fzero)) = refl
  unloop1 (cons {v = fzero} e b) =
    (cong (λ x → cons x b) (edge10-canon e))
    ∙ (cong (cons e10) (unloop01 b))
    ∙ (cong loopK1 (sym (cong (λ x → nneg (cons x b)) (edge10-canon e))))
  unloop1 (cons {v = fsuc fzero} e _) = ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e reflᴱ)

  unloop10 : (w : Walk G (fsuc fzero) fzero) → w ≡ walk10 (npos w)
  unloop10 (cons {v = fzero} e b) =
    (cong (λ x → cons x b) (edge10-canon e))
    ∙ (cong (cons e10) (unloop0 b))
    ∙ (cong walk10 (sym (cong (λ x → npos (cons x b)) (edge10-canon e))))
  unloop10 (cons {v = fsuc fzero} e _) = ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e reflᴱ)

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 组合层：四参分型主件
-- ────────────────────────────────────────────────────────────────────

-- 主件：非闭 walk 四参分型——(u,v,n₊,n₋) 完全不变量
--   u v 由 Walk 索引固定；同 (npos,nneg) ⟹ w ≡ w'（Gskel two-chain 上构造性形）
walk4-classify : ∀ {u v} (w w' : Walk G u v)
               → npos w ≡ npos w' → nneg w ≡ nneg w' → w ≡ w'
walk4-classify {fzero} {fzero} w w' p q = loop-classify w w' p
walk4-classify {fzero} {fsuc fzero} w w' p q =
  unloop01 w ∙ cong walk01 q ∙ sym (unloop01 w')
walk4-classify {fsuc fzero} {fzero} w w' p q =
  unloop10 w ∙ cong walk10 p ∙ sym (unloop10 w')
walk4-classify {fsuc fzero} {fsuc fzero} w w' p q =
  unloop1 w ∙ cong loopK1 q ∙ sym (unloop1 w')
walk4-classify {fsuc (fsuc ())} {_} _ _ _ _

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 核对层
-- ────────────────────────────────────────────────────────────────────

-- 非闭 walk 实例（0→1，计数 (2,1)）
w01a : Walk G fzero (fsuc fzero)
w01a = walk01 1

w01b : Walk G fzero (fsuc fzero)
w01b = cons e01 (cons e10 (cons e01 (nil (fsuc fzero))))

-- 语法相等核对（正范形与展开形同值）
check-01-syntax : w01a ≡ w01b
check-01-syntax = refl

-- 分型通道核对（走 walk4-classify 而非 refl）
check-01-class : w01a ≡ w01b
check-01-class = walk4-classify w01a w01b refl refl

-- 非语法对核对（边值不同构造——分类给出真实内容）
e01-alt : DG.edge G fzero (fsuc fzero)
e01-alt = inj₁ (⊑₂-01 , λ r → 0≢1 r)

w01c : Walk G fzero (fsuc fzero)
w01c = cons e01-alt (loopK1 1)

check-01-real : w01a ≡ w01c
check-01-real = walk4-classify w01a w01c refl refl

-- 1→0 侧核对
check-10 : walk10 1 ≡ cons e10 (cons e01 (cons e10 (nil fzero)))
check-10 = refl

-- 计数形核对（四参语义：walk01 k = (npos,nneg) = (suc k, k)）
check-count-01 : npos w01a ≡ 2
check-count-01 = refl

check-count-01b : nneg w01a ≡ 1
check-count-01b = refl
