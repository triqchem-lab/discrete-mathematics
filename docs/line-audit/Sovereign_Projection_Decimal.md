# 目录 `src/Sovereign/Projection/Decimal/` 逐模块审计记录

共 2 个模块。


## `src/Sovereign/Projection/Decimal/Axioms.agda`

- **module**: `Sovereign.Projection.Decimal.Axioms`
- **行数**: 91（代码 51 / 注释 26）
- **OPTIONS**: `--rewriting --cubical --guardedness`, `--rewriting --termination-depth=2`
- **头部注释（数学背景）**:
  - | Sovereign.Projection.Decimal.Axioms
  - 十进制数字根计算与判定
  - ⚠️ 宪法声明：
  - 这是电性文明十进制算术的实现
  - 在十进制自然数体系内正确，但与律算 GF(3) 数字根不同范畴
  - 仅用于外部数据校验和投影自洽证明
- **导入 (4)**: `Data.Nat`, `Data.Bool`, `Data.Product`, `Cubical.Foundations.Prelude`
- **顶层签名 (7)**: `divMod10`, `sumDigits`, `digitalRoot`, `IsStable`, `POW3₁₁`, `POW2₁₆`, `zhonglvAlign`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Projection/Decimal/Proofs.agda`

- **module**: `Sovereign.Projection.Decimal.Proofs`
- **行数**: 177（代码 124 / 注释 31）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Projection.Decimal.Proofs
  - 十进制数字根正确性的构造性证明
  - ⚠️ 宪法声明：
  - 这些证明在十进制自然数体系内**严谨完备**
  - 但与律算 GF(3) 驻波叠加表属于**不同范畴**
  - 证明内容包括：
  - 1. divMod10Correct：十进制除法正确性
  - 2. sumDigitsTerminates：数字和递归终止性
  - 3. digitalRoot 稳定性证明
  - 2026-08 P0 收口 (路线 a): 全部 0 postulate —
  - Axioms.divMod10 已改为 stdlib 对齐的 with-free 定义 (n/10, n%10),
  - sumDigits 同改; 正确性由 m≡m%n+[m/n]*n + m%n<n + m/n<m 直证,
  - 终止性/稳定性由 <-wellFounded 良基归纳证明, 全程无 with。
- **导入 (12)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Data.Bool`, `Data.Unit`, `Data.Sum`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Data.Nat.Induction`, `Induction.WellFounded`, `Sovereign.Projection.Decimal.Axioms`
- **顶层签名 (11)**: `¬suc≤zero`, `true≢false`, `divMod10Correct`, `lemma_q_lt`, `lemma_sum_lt`, `sumDigitsBound`, `suc-eq`, `q≥1`, `sumDigitsTerminates`, `digitalRootConverges`, `digitalRootStable`
- **质量**: `refl`×6；无 postulate / 无 hole
