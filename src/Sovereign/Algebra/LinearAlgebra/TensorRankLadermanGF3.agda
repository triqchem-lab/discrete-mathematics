{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankLadermanGF3
-- M17: 3×3 矩阵乘法张量 ⟨3,3,3⟩ 在 GF(3) 上的 23 项秩分解（Laderman 1976 的 23 门方案）
--
-- 数学背景
--   M16-A 的秩分解谓词 RankLE₃ 在 n = 2 处的见证是 Strassen 七门（M13 接桥）。
--   本件把它推到下一个尺寸 n = 3: 尺寸 3^3 = 27 的结构常数张量有一个 23 项分解
--   （Laderman 1976; 系数全 ∈ {-1,0,1}, 故 ℤ 恒等式 ⟹ 任意交换环, GF(3) 是实例）。
--   证书来源: GitHub `RakTikoo/matmul-333-tensor-rank` 的机器可读件（2026-11-26 经代理取回,
--   oracle 先在 ℤ 与 GF(3) 上逐点核验 729/729, 再由本件发射给 Agda 内核裁决）。
--
--   「指数 < p/q」的有限形态是 Saving₃ p q（TensorRankUpperGF3, 镜像 Lean
--   `FieldExtension.lean:72 exponent_lt_iff_rank` 取 (1,1,1) 形状）。于是:
--     ★ laderman-saving: p/q ≥ 20/7 时有严格节省（n = 3^(7q), r = 23^(7q)）;
--     ★ laderman-not-below: 6p < 17q 时 23^q < 3^p 不可能 —— (3,23) 这个见证
--       从不越过 (2,7) 见证已给的 17/6 那条线（数值内核: 3^17 ≤ 23^6）。
--
-- 内容
--   §1 表（oracle 发射）: raL / rbL / rcL —— 23 门 × 9 位置 = 621 条子句
--   §2 rank-eqL（oracle 发射）: 9×9×9 = 729 条 refl（sumFin{23} 按字面指数逐层归约）
--   §3 ★ rank-laderman : RankLE₃ 3 23; 配展平下界 rank-lower-laderman : 3 * 3 ≤ 23
--   §4 证书数值与 ★ laderman-saving / ★ laderman-not-below
--   §5 与 Strassen 的张量积: rank-mixed : RankLE₃ 6 161
--
-- 诚实边界
--   · 这是**上界见证**（秩 ≤ 23）, 不是「秩恰为 23」。n = 3 的库内下界只有展平 r ≥ 9;
--     「rank(⟨3,3,3⟩) ≤ 22 是否成立」是公开问题（[阅读层·未验证] 文献状态）,
--     本件 23 门经 oracle 核验为**删除封闭**: 23 个秩一贡献在 GF(3) 上线性无关,
--     丢任何一门都不再是分解（oracle 判据 6, 纯机器可核; 库内无对应定理）。
--   · (3,23) 的节省比值 20/7 ≈ 2.857 **不改进** (2,7) 的 17/6 ≈ 2.833。
--     尺寸 3 上要进入 9/4 与 17/6 之间的空档需 r ≤ 21（oracle 判据 7: 21^5 < 3^14
--     且 6·14 = 84 < 85 = 17·5; r=22 也可, 首个 (p,q) = (31,11), 31/11 ≈ 2.818）。
--   · 证书来自第三方仓库; 但数值真实性由两层独立核验: Python oracle（ℤ + GF(3) 逐点）
--     与 TriRV 三进制 VM（engineering/trirv/laderman23_gf3.c）, 内核裁决在本件 §2。
--
-- 先算后验: engineering/oracle_rank3_witness_gf3.py（判据 1–9, 含负控制 207/207 全转红）
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankLadermanGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; m≤m+n; <-irrefl; ≤-<-trans; <-≤-trans; <⇒≤
       ; *-comm; *-assoc; *-monoˡ-≤; ^-*-assoc; ^-monoˡ-≤)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3
  using (RankLE₃; mm; Pos; Out; rank-strassen)
open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3 using (rank-lower)
open import Sovereign.Algebra.LinearAlgebra.TensorRankPowGF3
  using (rank-mul; rank-pow)
open import Sovereign.Algebra.LinearAlgebra.TensorRankUpperGF3
  using (Saving₃; pow-base-<; pow-exp-mono)

--------------------------------------------------------------------------------
-- §1. 表（oracle 发射）
--------------------------------------------------------------------------------

-- ↓↓ 本段由 engineering/oracle_rank3_witness_gf3.py 发射（先算后验）, 请勿手改 ↓↓
raL : Fin 23 → Pos 3 → Trit
raL (fzero) (fzero , fzero) = T₀
raL (fzero) (fzero , fsuc fzero) = T₀
raL (fzero) (fzero , fsuc (fsuc fzero)) = T₀
raL (fzero) (fsuc fzero , fzero) = T₀
raL (fzero) (fsuc fzero , fsuc fzero) = T₁
raL (fzero) (fsuc fzero , fsuc (fsuc fzero)) = T₂
raL (fzero) (fsuc (fsuc fzero) , fzero) = T₀
raL (fzero) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fzero)) (fzero , fzero) = T₀
raL (fsuc (fzero)) (fzero , fsuc fzero) = T₀
raL (fsuc (fzero)) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fzero)) (fsuc fzero , fzero) = T₀
raL (fsuc (fzero)) (fsuc fzero , fsuc fzero) = T₁
raL (fsuc (fzero)) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fzero)) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fzero)) (fsuc (fsuc fzero) , fsuc fzero) = T₁
raL (fsuc (fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fzero))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fzero))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fzero))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fzero))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fzero))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fzero))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fzero)))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
raL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fsuc (fsuc fzero)) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fsuc fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₂
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fsuc fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fsuc fzero) = T₁
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
raL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL : Fin 23 → Pos 3 → Trit
rbL (fzero) (fzero , fzero) = T₀
rbL (fzero) (fzero , fsuc fzero) = T₀
rbL (fzero) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fzero) (fsuc fzero , fzero) = T₀
rbL (fzero) (fsuc fzero , fsuc fzero) = T₁
rbL (fzero) (fsuc fzero , fsuc (fsuc fzero)) = T₂
rbL (fzero) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fzero) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fzero)) (fzero , fzero) = T₀
rbL (fsuc (fzero)) (fzero , fsuc fzero) = T₀
rbL (fsuc (fzero)) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fzero)) (fsuc fzero , fzero) = T₀
rbL (fsuc (fzero)) (fsuc fzero , fsuc fzero) = T₁
rbL (fsuc (fzero)) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fzero)) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fzero)) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rbL (fsuc (fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fzero))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fzero))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fzero))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fzero))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fzero))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fzero))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
rbL (fsuc (fsuc (fsuc (fzero)))) (fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fzero)))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fzero)))) (fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fsuc fzero) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fzero) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fzero) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₁
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rbL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL : Fin 23 → Out 3 → Trit
rcL (fzero) (fzero , fzero) = T₀
rcL (fzero) (fzero , fsuc fzero) = T₀
rcL (fzero) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fzero) (fsuc fzero , fzero) = T₀
rcL (fzero) (fsuc fzero , fsuc fzero) = T₁
rcL (fzero) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fzero) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fzero) (fsuc (fsuc fzero) , fsuc fzero) = T₂
rcL (fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fzero)) (fzero , fzero) = T₀
rcL (fsuc (fzero)) (fzero , fsuc fzero) = T₀
rcL (fsuc (fzero)) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fzero)) (fsuc fzero , fzero) = T₀
rcL (fsuc (fzero)) (fsuc fzero , fsuc fzero) = T₁
rcL (fsuc (fzero)) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fzero)) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fzero)) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fzero))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fzero))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fzero))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fzero))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fzero))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fzero))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fzero))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fzero)))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fzero , fsuc (fsuc fzero)) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fsuc fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc fzero , fsuc (fsuc fzero)) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₂
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fsuc fzero) = T₁
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc fzero , fsuc (fsuc fzero)) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc fzero) = T₀
rcL (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))))))))))))))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = T₀

rank-eqL : ∀ (x y : Pos 3) (z : Out 3) →
  sumFin (λ i → (raL i x) ⊗ ((rbL i y) ⊗ (rcL i z))) ≡ mm 3 x y z
rank-eqL (fzero , fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
rank-eqL (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fzero , fsuc (fsuc fzero)) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl ; (fsuc fzero , fsuc (fsuc fzero)) → refl ; (fsuc (fsuc fzero) , fzero) → refl ; (fsuc (fsuc fzero) , fsuc fzero) → refl ; (fsuc (fsuc fzero) , fsuc (fsuc fzero)) → refl }
-- ↑↑ 发射段结束 ↑↑

--------------------------------------------------------------------------------
-- §3. 见证
--------------------------------------------------------------------------------

-- ★ 3×3 矩阵乘法张量在 GF(3) 上有一个 23 项秩分解
rank-laderman : RankLE₃ 3 23
rank-laderman = record
  { ra = raL
  ; rb = rbL
  ; rc = rcL
  ; rank-eq = rank-eqL
  }

-- 与展平下界配对: n = 3 处 9 ≤ r ≤ 23（库内两方向的全部内容）
rank-lower-laderman : 3 * 3 ≤ 23
rank-lower-laderman = rank-lower 3 23 rank-laderman

--------------------------------------------------------------------------------
-- §4. 证书数值 / 节省 / 阈值
--------------------------------------------------------------------------------

-- 数值由 oracle 发射（先算后验, 不手算）:
--   3^17 = 129140163, 23^6 = 148035889, 差 = 18895726
--   23^7 = 3404825447, 3^20 = 3486784401, 3^20 − 23^7 − 1 = 81958953
cert-laderman : 3 ^ 17 ≤ 23 ^ 6
cert-laderman = m≤m+n (3 ^ 17) 18895726

cert-laderman-strict : 23 ^ 7 < 3 ^ 20
cert-laderman-strict = m≤m+n (suc (23 ^ 7)) 81958953

1≤3 : 1 ≤ 3
1≤3 = s≤s z≤n

-- ★ 对一切 p/q ≥ 20/7, GF(3) 上有严格节省: 取 n = 3^(7q)、r = 23^(7q)
--   r ^ q = (23^7)^(q²) < (3^20)^(q²) ≤ 3^(7qp) = n ^ p
--   （结构与 TensorRankUpperGF3.strassen-saving 相同, 换一组证书）
laderman-saving : ∀ p q → 0 < q → 20 * q ≤ 7 * p → Saving₃ p q
laderman-saving p (suc q′) h sq =
  (3 ^ (7 * suc q′)) , (23 ^ (7 * suc q′)) , n≥2 , rank-pow rank-laderman (7 * suc q′) , saving
  where
  Q : ℕ
  Q = suc q′ * suc q′

  hQ : 0 < Q
  hQ = s≤s z≤n

  n≥2 : 2 ≤ 3 ^ (7 * suc q′)
  n≥2 = ≤-trans 2≤3 (pow-exp-mono 3 1 (7 * suc q′) 1≤3 one≤7q)
    where
    2≤3 : 2 ≤ 3
    2≤3 = s≤s (s≤s z≤n)
    -- 7 * suc q′ 按定义就是 suc (q′ + 6 * suc q′)
    one≤7q : 1 ≤ 7 * suc q′
    one≤7q = s≤s z≤n

  e1 : (23 ^ (7 * suc q′)) ^ suc q′ ≡ (23 ^ 7) ^ Q
  e1 = trans (^-*-assoc 23 (7 * suc q′) (suc q′))
         (trans (cong (λ t → 23 ^ t) (*-assoc 7 (suc q′) (suc q′)))
                (sym (^-*-assoc 23 7 Q)))

  st : (23 ^ 7) ^ Q < (3 ^ 20) ^ Q
  st = pow-base-< Q (23 ^ 7) (3 ^ 20) hQ cert-laderman-strict

  -- stdlib 的 _*_ 是左结合: a * b * c 读作 (a * b) * c
  e3 : 7 * p * suc q′ ≡ 7 * suc q′ * p
  e3 = trans (*-assoc 7 p (suc q′))
        (trans (cong (λ t → 7 * t) (*-comm p (suc q′)))
               (sym (*-assoc 7 (suc q′) p)))

  e2 : (3 ^ 20) ^ Q ≡ 3 ^ (20 * suc q′ * suc q′)
  e2 = trans (^-*-assoc 3 20 Q) (cong (λ t → 3 ^ t) (sym (*-assoc 20 (suc q′) (suc q′))))

  mo : 3 ^ (20 * suc q′ * suc q′) ≤ 3 ^ (7 * suc q′ * p)
  mo = pow-exp-mono 3 (20 * suc q′ * suc q′) (7 * suc q′ * p) 1≤3
         (≤-trans (*-monoˡ-≤ (suc q′) sq) (≤-reflexive e3))

  e4 : 3 ^ (7 * suc q′ * p) ≡ (3 ^ (7 * suc q′)) ^ p
  e4 = sym (^-*-assoc 3 (7 * suc q′) p)

  saving : (23 ^ (7 * suc q′)) ^ suc q′ < (3 ^ (7 * suc q′)) ^ p
  saving = ≤-<-trans (≤-reflexive e1)
             (<-≤-trans st (≤-trans (≤-reflexive e2) (≤-trans mo (≤-reflexive e4))))

-- 可读实例: ω₃ ≤ 20/7（由 (3,23) 见证）
saving-laderman-20-7 : Saving₃ 20 7
saving-laderman-20-7 = laderman-saving 20 7 (s≤s z≤n) (≤-reflexive (*-comm 20 7))

-- ★ (3,23) 这个见证从不越过 17/6: 若 6p < 17q, 则 23^q < 3^p 不可能
--   23^(6q) < 3^(6p) ≤ 3^(17q) ≤ (23^6)^q = 23^(6q), 矛盾（第一步用 h, 后两步用证书）
laderman-not-below : ∀ p q → 6 * p < 17 * q → (23 ^ q) < (3 ^ p) → ⊥
laderman-not-below p q h17 h = <-irrefl refl goal
  where
  s1 : (23 ^ q) ^ 6 < (3 ^ p) ^ 6
  s1 = pow-base-< 6 (23 ^ q) (3 ^ p) (s≤s z≤n) h

  e1 : (23 ^ q) ^ 6 ≡ (23 ^ 6) ^ q
  e1 = trans (^-*-assoc 23 q 6)
        (trans (cong (λ t → 23 ^ t) (*-comm q 6))
               (sym (^-*-assoc 23 6 q)))

  e2 : (3 ^ p) ^ 6 ≡ 3 ^ (6 * p)
  e2 = trans (^-*-assoc 3 p 6) (cong (λ t → 3 ^ t) (*-comm p 6))

  s4 : 3 ^ (6 * p) ≤ 3 ^ (17 * q)
  s4 = pow-exp-mono 3 (6 * p) (17 * q) 1≤3 (<⇒≤ h17)

  s5 : 3 ^ (17 * q) ≤ (23 ^ 6) ^ q
  s5 = ≤-trans (≤-reflexive (sym (^-*-assoc 3 17 q)))
        (^-monoˡ-≤ q cert-laderman)

  goal : (23 ^ q) ^ 6 < (23 ^ q) ^ 6
  goal = <-≤-trans s1 (≤-trans (≤-reflexive e2) (≤-trans s4 (≤-trans s5 (≤-reflexive (sym e1)))))

--------------------------------------------------------------------------------
-- §5. 与 Strassen 的张量积
--------------------------------------------------------------------------------

-- 秩相乘（M16-C）: (2,7) × (3,23) → (6,161)——混合尺寸的见证仍在谓词里
rank-mixed : RankLE₃ 6 161
rank-mixed = rank-mul rank-strassen rank-laderman
