# φ-respects 族归档（2026-10-11，人类裁决「归档」）

## 归档物
`φ` / `φ-respects`（postulate）/ `orbitStabilizer←` / `sec'` / `ret'` / `orbitIso` /
`orbitStabilizer-path` / `orbitStabilizer`（iso 全链）——原文见 `phi-respects-fragment.agda.txt`。

## 归档理由（分析定谳）
1. **截断层语义错配**：`Orbit x` 第二分量用 `∥_∥₂`（set 截断只压路径不压点——`|(g,·)|₂` 与 `|(h,·)|₂`
   在 g≠h 时是不同 0-胞腔，源码原注释自认），而 `φ-respects` 断言的商下降只在**命题截断**下成立
   ⇒ 如所述**为假**（非「难证」）；
2. **自辩不成立**：原注释「这是定理的核心公理级别断言，非缺失证明」违反 2026-10-11 豁免精化判据
   （「豁免留给内核对不上，不是定义没写好」）——此为定义没写好，正解是改定义不是 postulate；
3. **口径不合**：本框架「orbitStabilizer = 谱投影非等式」——iso 全链是旧路线残留。

## 保留物
`orbitStabilizer→`（STrec 构造性单向）留 T6 为谱投影 map；zero-fixed 系推论不依赖归档件，原样保留。

## 重开条件（若日后再战）
`Orbit` 第二分量改**命题截断** `∃ g → a4Action g x ≡ y`（或直接 SetQuotient）——
φ-respects 退化为命题内等式（可 refl 级闭合），约 30 行重述。**本框架口径下不建议重开**。

## 裁决链
2026-09-10 判 gap → 2026-10-04「保留代码不构成问题」→ **2026-10-11「归档」（最新，覆盖前者）**。
