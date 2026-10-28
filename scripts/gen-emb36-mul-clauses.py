#!/usr/bin/env python3
"""Embed36 乘法同态的构造子归约子句生成器（M3·emb 卷）。

单源：坐标级嵌入定义（FML `Embed36.agda` v2）
  · emb9 (a , b)       = a , b , (T₂ ⊗ b) , b , b , T₀
  · emb27 (a , b , c)  = a , c , b , ((T₂ ⊗ b) ⊕ (T₂ ⊗ c)) , (b ⊕ c) , c
以及 GF(9)/GF(27) 乘法公式（GF9.agda / GF27.agda）。

产物：`Embed36MulClauses.agda`——emb9-mul（3⁴ = 81 子句）与
emb27-mul（3⁶ = 729 子句）的构造子全 case 归约证明（全部 refl，
与 Trit.agda ⊕-assoc 27-case 同法）。Embed36.agda 引用该模块。

已由 Python 暴力预检（81/729 对全同）+ Agda 编译双验证。

用法：
  python3 scripts/gen-emb36-mul-clauses.py
"""
import pathlib

TR = ["T₀", "T₁", "T₂"]
OUT = (pathlib.Path(__file__).resolve().parent.parent
       / 'src/Sovereign/Algebra/FieldTower/Embed36MulClauses.agda')

L = []
L.append("{-# OPTIONS --rewriting #-}")
L.append("")
L.append("-- | Sovereign.Algebra.FieldTower.Embed36MulClauses —— 嵌入乘法同态的")
L.append("--   构造子全 case 归约证明（3⁴ = 81 / 3⁶ = 729 子句，全部 refl）。")
L.append("--")
L.append("-- ⚠ 生成文件——勿手改（FML scripts/gen-emb36-mul-clauses.py）。")
L.append("-- 与 Trit.agda ⊕-assoc 27-case 同法：有限型全称命题的标准构造子归约")
L.append("-- 证明，非数值表对拍。子句依赖 Embed36 的坐标级定义（v2）。")
L.append("")
L.append("module Sovereign.Algebra.FieldTower.Embed36MulClauses where")
L.append("")
L.append("open import Relation.Binary.PropositionalEquality using (_≡_; refl)")
L.append("open import Data.Product using (_×_; _,_)")
L.append("open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)")
L.append("open import Sovereign.Algebra.FieldTower.GF9")
L.append("  using (GF9; _*gf9_)")
L.append("open import Sovereign.Algebra.FieldTower.GF27")
L.append("  using (GF27; _*gf27_)")
L.append("open import Sovereign.Algebra.FieldTower.GF36 using (GF36; _*gf36_)")
L.append("open import Sovereign.Algebra.FieldTower.Embed36")
L.append("  using (emb9; emb27)")
L.append("")
L.append("emb9-mul : ∀ (x y : GF9) → emb9 (x *gf9 y) ≡ emb9 x *gf36 emb9 y")
for a in range(3):
    for b in range(3):
        for c in range(3):
            for d in range(3):
                L.append(f"emb9-mul ({TR[a]} , {TR[b]}) ({TR[c]} , {TR[d]}) = refl")
L.append("")
L.append("emb27-mul : ∀ (x y : GF27) → emb27 (x *gf27 y) ≡ emb27 x *gf36 emb27 y")
for a in range(3):
    for b in range(3):
        for c in range(3):
            for d in range(3):
                for e in range(3):
                    for f in range(3):
                        L.append(f"emb27-mul ({TR[a]} , {TR[b]} , {TR[c]}) "
                                 f"({TR[d]} , {TR[e]} , {TR[f]}) = refl")

OUT.write_text("\n".join(L) + "\n", encoding='utf-8')
print(f"written: {OUT} ({len(L)} lines)")
