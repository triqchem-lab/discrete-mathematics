# 线2 norm-unique 修正版计划（dropZ B 主 + NoZero A 辅）

> 状态：🔄 **批2 施工中**（fork 7c5158c4）｜台账映射：`Laurent.norm-unique`（diagnosis: statement_wrong）
> 背景：无条件版被孤零反例击穿（`norm-unique-false` 反证件入库）——dropZ 漏件三重显形第三案

## 目标与成功标准
双收口：`norm-unique-dropZ : xs ↭ ys → norm (dropZ xs) ≡ norm (dropZ ys)`（B 主，无条件）
+ `norm-unique-nz : NoZero xs → NoZero ys → xs ↭ ys → norm xs ≡ norm ys`（A 辅）
→ proof_compile EXIT=0 + 台账 statement 定稿回填

## 已绿地基（批1，288 行绿）
dropZ + dropZ-resp-↭（过滤保置换四案）｜ZeroFree 族（insW-free/normC-free/normD-free）
normD = norm ∘ dropZ｜check-dropZ-ex（Stage 2 反例 B 面退化 refl）+ check-dropZ-orphan

## 攻坚铁律（with-swamp 终解，5 轮失败实证）
一切新件**零 with**——aux 显式判定参数范式：谓词/函数 `f-aux … d`（Dec 参数普通子句）；
引理对 aux 形立式；调用点端段分支实参、中段中性检验子、链接处同源。
战术三条：构造子隐式全绑防 meta 塌陷｜eq3 嵌套 with 垫底｜lt3-cons-shape 桥接。

## 批2 交付序（矩阵地形图）
① normD-swap 零案（aux 双判定参数四分支，~40 行）
② insW2-swap 非零核心矩阵（one 基 9 格 → eq 四≟叶 → cons 格 8-10 叶 + 双合并叶 ≈8，~150-250 行）
③ normD-resp（↭ 归纳：refl/prep/swap/trans）
④ 双收口（B/A 各 ~30 行；A 面孤零叶 ⊥-elim 由 NoZero 消）

## 验证点（最终）
① _PNormU.agda EXIT=0（--no-fast-reduce）② 反例双核对（B 面退化 + tie/cancel/orphan 保持）③ 零洞零 postulate

## 修订记录
- 2026-10-11 ①：v3 卡点确诊（insF 返回 Σ(表值+证明) 致双侧证明分量不等）→ v4 表值级重构 + insW-irrel；
- 2026-10-11 ②：Stage 2 反例击穿无条件版 → 裁定 B 主 A 辅双证（dropZ = 原设计漏件补回）；
- 2026-10-11 ③：批1.5 with-沼泽实证 → aux 范式铁律化。
