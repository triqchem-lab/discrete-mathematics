# 目录 `src/` 逐模块审计记录

共 3 个模块。


## `src/_rt.agda`

- **module**: `_rt`
- **行数**: 40（代码 24 / 注释 11）
- **导入 (6)**: `Data.Fin`, `Data.Vec`, `Data.Vec.Properties`, `Data.Nat`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (6)**: `Trit`, `p3`, `stc`, `cts`, `mod-toℕ`, `rt`
- **质量**: `refl`×5；⚠️ 1 hole

## `src/_test_irrelevant.agda`

- **module**: `_test_irrelevant`
- **行数**: 6（代码 4 / 注释 0）
- **OPTIONS**: `--safe`
- **导入 (2)**: `Data.Irrelevant`, `Relation.Nullary.Recomputable.Core`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/test_chiral.agda`

- **module**: `test_chiral`
- **行数**: 19（代码 12 / 注释 2）
- **OPTIONS**: `--guardedness`
- **导入 (2)**: `Data.Nat`, `Data.Product`
- **data 类型**: `ChiralSymmetry`, `WuXingAmplitude`
- **顶层签名 (2)**: `test1`, `test2`
- **质量**: `refl`×0；无 postulate / 无 hole
