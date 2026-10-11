{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.Applied.DeepAlgebraProofs
-- 深层代数证明索引 (B16–B22)
--
-- 本模块是证明索引：汇总并重导出已在各源模块中完成的深层证明。
-- 所有定理均为构造性证明，0 postulate。
--
-- 任务清单:
--   B16: GF(9) 乘法逆元完整验证        ← GF9.inv-correct
--   B17: Frobenius σ(xy)=σ(x)σ(y)     ← GF9.lemma-frobenius-multiplicative
--   B18: 范数乘性 N(xy)=N(x)N(y)       ← NormDiscrete.galoisNorm-multiplicative
--   B19: A₄ 群结合律                   ← A4Group.assoc
--   B20: A₄ 共轭类分类 (1+4+4+3=12)    ← A4Representations.classSizeSum
--   B21: 2A₄ 群公理                    ← BinaryTetrahedral.bt-id-left/right/inv
--   B22: 2A₄ 非平凡性                  ← BinaryTetrahedral.bt-i-sq/bt-neg1≠id

module Sovereign.Applied.DeepAlgebraProofs where

--------------------------------------------------------------------------------
-- B16: GF(9) 乘法逆元完整验证
-- 源: Sovereign.Algebra.GF9
-- 证明方法: 8 case 穷举 (GF9Star 的 8 个非零元素)
-- 定理: ∀ x → x *s inv x ≡ s1
--------------------------------------------------------------------------------

open import Sovereign.Algebra.GF9 public using (
  -- 类型与运算
  GF9; GF9Star; _*s_; _*gf9_; gf9-one;
  s1; s2; sα; s2α; s1α; s12α; s21α; s22α;
  toGF9; fromGF9;
  -- 逆元
  inv;
  -- B16 核心定理
  inv-correct;       -- ∀ x → x *s inv x ≡ s1 (8 case refl)
  inv-involutive;    -- ∀ x → inv (inv x) ≡ x
  -- 乘法表一致性
  *s-toGF9;          -- ∀ x y → toGF9 (x *s y) ≡ toGF9 x *gf9 toGF9 y
  *s-identityˡ;      -- ∀ x → s1 *s x ≡ x
  *s-identityʳ;      -- ∀ x → x *s s1 ≡ x
  *s-comm;           -- ∀ x y → x *s y ≡ y *s x
  fromGF9-toGF9;     -- ∀ x → fromGF9 (toGF9 x) ≡ x
  toGF9-inj          -- toGF9 单射
  )

--------------------------------------------------------------------------------
-- B17: Frobenius 自同构 σ(xy) = σ(x)σ(y)
-- 源: Sovereign.Algebra.GF9
-- 证明方法: 代数证明 (negate 分配律 + GF(3) 特征 3 性质)
-- 定理: ∀ x y → galoisConjugate (x *gf9 y) ≡ galoisConjugate x *gf9 galoisConjugate y
--------------------------------------------------------------------------------

open import Sovereign.Algebra.GF9 public using (
  galoisConjugate;
  galoisConjugate²;              -- σ² = id
  galoisNorm;
  galoisNorm-conjugate;          -- N(σ(x)) = N(x)
  -- B17 核心定理
  lemma-frobenius-multiplicative;  -- σ(xy) = σ(x)σ(y)
  lemma-eigen-conjugate;           -- σ(xα) = σ(x)σ(α) (推论)
  sigma-alpha                      -- σ(α) = -α
  )

--------------------------------------------------------------------------------
-- B18: 范数乘性 N(xy) = N(x)N(y)
-- 源: Sovereign.Analysis.NormDiscrete
-- 证明方法: 81 case 穷举 (GF9 的 9×9 个元素对)
-- 定理: ∀ x y → galoisNorm (x *gf9 y) ≡ galoisNorm x ⊗ galoisNorm y
--------------------------------------------------------------------------------

open import Sovereign.Analysis.NormDiscrete public using (
  -- B18 核心定理
  galoisNorm-multiplicative    -- N(xy) = N(x)N(y) (81 case refl)
  )

--------------------------------------------------------------------------------
-- B19: A₄ 群结合律
-- 源: Sovereign.Structology.A4Group
-- 证明方法: 代数证明 (perm-hom 半群同态 + 函数复合结合律)
-- 定理: ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
-- 注: 使用 Cubical _≡_ (Path), 因 A4Group 依赖 Cubical.Foundations.Prelude
--------------------------------------------------------------------------------

open import Sovereign.Structology.A4Group public using (
  A4; Id; Rot; Flip;
  _⊗_;
  -- B19 核心定理
  assoc;             -- (x⊗y)⊗z ≡ x⊗(y⊗z), 由 perm-hom 推导
  -- 群公理 (完整)
  identity;          -- Id⊗x ≡ x × x⊗Id ≡ x
  inverse;           -- ∀ x → Σ[ y ] (x⊗y ≡ Id × y⊗x ≡ Id)
  -- 置换表示
  perm;              -- A4 → Fin 4 → Fin 4
  fromPerm-perm;     -- fromPerm (perm x) ≡ x
  perm-hom           -- perm (x⊗y) ≡ perm x ∘ₚ perm y
  )

--------------------------------------------------------------------------------
-- B20: A₄ 共轭类分类 (1+4+4+3 = 12)
-- 源: Sovereign.Structology.A4Representations
-- 证明方法: refl (Agda 计算归约)
-- 共轭类:
--   C1 = {Id}           (size 1)
--   C2 = {3-cycles CW}  (size 4)
--   C3 = {3-cycles CCW} (size 4)
--   C4 = {flips}        (size 3)
-- 定理: classSize C1 + classSize C2 + classSize C3 + classSize C4 ≡ 12
--------------------------------------------------------------------------------

open import Sovereign.Structology.A4Representations public using (
  ConjugacyClass; C1; C2; C3; C4;
  classSize;
  classify;          -- A4 → ConjugacyClass
  -- B20 核心定理
  classSizeSum;      -- 1 + 4 + 4 + 3 ≡ 12 (refl)
  -- 不可约表示
  A4Irrep; V3; V1; V1'; V1'';
  dim;
  dimSqSum           -- 3² + 1² + 1² + 1² ≡ 12 (refl)
  )

--------------------------------------------------------------------------------
-- B21: 2A₄ 群公理
-- 源: Sovereign.Structology.BinaryTetrahedral
-- 证明方法: 穷举法 (Q₈ 8元素 × C₃ 3元素 = 24 元素)
-- 已证公理:
--   左单位元: bt-id *bt x ≡ x
--   右单位元: x *bt bt-id ≡ x
--   右逆元:   x *bt bt-inv x ≡ bt-id
--   基数:     |2A₄| = 24
--------------------------------------------------------------------------------

open import Sovereign.Structology.BinaryTetrahedral public using (
  BT; mkBT; _*bt_; bt-id; bt-inv;
  Q8; q1; qm1; qi; qmi; qj; qmj; qk; qmk;
  C3G; c0; c1; c2;
  -- B21 核心定理: 群公理
  bt-id-left;        -- ∀ x → bt-id *bt x ≡ x
  bt-id-right;       -- ∀ x → x *bt bt-id ≡ x
  bt-right-inv;      -- ∀ x → x *bt bt-inv x ≡ bt-id (24 case refl)
  bt-card≡24;        -- |2A₄| ≡ 24
  -- Q₈ 群公理
  q1-left-id;        -- ∀ q → q1 *q q ≡ q
  q-right-id;        -- ∀ q → q *q q1 ≡ q
  q8-neg1-central;   -- ∀ q → qm1 *q q ≡ q *q qm1
  q8-neg1²;          -- qm1 *q qm1 ≡ q1
  q8-i⁴;             -- qi⁴ ≡ q1
  -- C₃ 群公理
  c3-identity;       -- ∀ c → c0 *c c ≡ c
  c3-identityʳ;      -- ∀ c → c *c c0 ≡ c
  c3-assoc;          -- C₃ 结合律
  c3-ω³≡1            -- ω³ ≡ 1
  )

--------------------------------------------------------------------------------
-- B22: 2A₄ 非平凡性 (2A₄ ≢ A₄ × Z₂)
-- 源: Sovereign.Structology.BinaryTetrahedral
-- 证明方法: 构造性反证 (构造子不等 + 等式推导)
-- 核心论证:
--   在 A₄ × Z₂ 中, order-2 元素的提升仍有 order 2
--   在 2A₄ 中, (i,c₀)² = (-1,c₀) ≠ id, 但 (i,c₀)⁴ = id
--   所以 (i,c₀) 的阶为 4, 不是 2 → 扩张非平凡
--------------------------------------------------------------------------------

open import Sovereign.Structology.BinaryTetrahedral public using (
  -- B22 核心定理: 非平凡性
  bt-i-sq;           -- (i,c₀)² ≡ (-1,c₀) (refl)
  bt-neg1≠id;        -- (-1,c₀) ≢ id
  bt-i⁴;             -- (i,c₀)⁴ ≡ id (refl)
  bt-i≠id;           -- (i,c₀) ≢ id
  bt-i²≠id;          -- (i,c₀)² ≢ id
  -- 中心结构
  center-neg1-commutes;  -- (-1,c₀) 与所有元素交换
  qk≠qmk;               -- k ≢ -k
  -- 商映射
  quotient;              -- BT → V4El × C3G
  kernel-id;             -- quotient bt-id ≡ (ve, c₀)
  kernel-neg1;           -- quotient (mkBT qm1 c0) ≡ (ve, c₀)
  quotient-card;         -- |V₄ × C₃| ≡ 12
  -- 不可约表示
  BTIrrep; btDim;
  btDimSqSum;            -- Σdim² ≡ 24
  btIrrepCount;          -- 7 个不可约表示
  bt-more-irreps         -- 7 ≡ 4 + 3 (比 A₄ 多 3 个旋量表示)
  )
