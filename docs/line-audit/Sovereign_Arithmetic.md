# 目录 `src/Sovereign/Arithmetic/` 逐模块审计记录

共 3 个模块。


## `src/Sovereign/Arithmetic/CRTLemmas.agda`

- **module**: `Sovereign.Arithmetic.CRTLemmas`
- **行数**: 126（代码 102 / 注释 10）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (12)**: `Data.Nat`, `Data.Nat.GCD`, `Data.Nat.Base`, `Data.Nat.Coprimality`, `Data.Nat.Divisibility.Core`, `Data.Nat.Divisibility`, `Sovereign.AlgebraWrapper`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`, `Data.Empty`, `Relation.Nullary`
- **顶层签名 (6)**: `POW2`, `POW3`, `M`, `coprime-POW2-POW3`, `lemma-mod-sum`, `crt-merge`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Arithmetic/MobiusPhi.agda`

- **module**: `Sovereign.Arithmetic.MobiusPhi`
- **行数**: 39（代码 14 / 注释 16）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Arithmetic.MobiusPhi
  - 11M 解析数论补强 — Möbius 函数与 Euler φ (12 的除数格上, 0 postulate)
  - 乘性数论的离散载体: 12 = 2²·3 的除数格 {1,2,3,4,6,12}
  - μ(1)=1, μ(2)=−1, μ(3)=−1, μ(4)=0, μ(6)=1, μ(12)=0
  - Möbius 反演: Σ_{d|12} μ(d) = 0 (n>1)
  - φ(12) = Σ_{d|12} μ(d)·(12/d) = 4 (与单位群 (Z/12Z)* ≅ V₄ 一致)
  - ζ 的 Euler 乘积注释 (乘性数论与有限域塔的桥)
- **导入 (2)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (8)**: `mu-1`, `mu-2`, `mu-3`, `mu-4`, `mu-6`, `mu-12`, `mobius-sum`, `phi-12`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Arithmetic/Untrusted.agda`

- **module**: `Sovereign.Arithmetic.Untrusted`
- **行数**: 25（代码 4 / 注释 15）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Arithmetic.Untrusted
  - 隔离层：集中管理未信任的外部算术引理 (Data.Nat.*)
  - 宪法原则：
  - 1. 所有外部算术引理初始信任度为 0 (UNTRUSTED)。
  - 2. 禁止核心宪法模块直接引用外部标准库。
  - 3. 必须通过此隔离层访问，以便在阶段 2 替换为高维几何重新证明的版本。
- **导入 (2)**: `Data.Nat.Properties`, `Data.Nat.DivMod`
- **质量**: `refl`×0；无 postulate / 无 hole
