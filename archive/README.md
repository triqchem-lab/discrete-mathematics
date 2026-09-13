# archive/ — 非库文件（归档区）

**本目录不是 Agda 库的一部分**：`sovereign.agda-lib` 的 `include: src` 不包含 `archive/`，
因此这里的 `.agda` 文件**永远不会被编译、也不会进门禁**。它们在此仅为历史留存，可随时用
`git mv archive/... src/...` 还原。

## civlayers-2026-07/ — 文明层旧稿（2026-07-27/29 建档，2026-09-13 归档）

来源：原先散落在 `src/01-electric-12d/`、`src/02-magnetic-24d/`、`src/03-neutral-144d/`。
这些文件**声明的是 `Sovereign.*` 模块名，而路径不是 `Sovereign/*`** ⇒ 在 `include: src` 下
模块名与路径永远不匹配 ⇒ 从未被编译过（`engineering/check_all_modules_parallel.sh:27`
只扫 `src/Sovereign`，这些目录全在扫描范围之外）。

归档理由（实测证据，2026-09-13）：

1. **10/11 个文件的模块名已被正式模块占用**——`src/Sovereign/Coupling/{ParityViolation,
   SpinTwistor,Entanglement,LossGain,TQ10,Zhonglv}.agda`、`src/Sovereign/RootMath/{Base,
   DigitalRoot}.agda`、`src/Sovereign/MetaStructure/WuXing.agda`、`src/Sovereign/Coupling/
   CartanTorsion.agda`；这些正式模块分别被 2/0/0/21/0/6/7/15/17/1 个模块 `import`，与本
   目录旧稿内容已漂移 100–528 行（`diff` 行数实测）。
   ⇒ **改名/改路径不可行**：会造出同名重复模块，破坏「唯一事实源」。
2. 旧稿本身是**从未编译过的草稿**：含 `where` 挂在 postulate 块/record/data/类型签名上
   （非法）、`ratio8_5`（`_` 后不得接字面量）、`H2O-C60-*`（`-` 是符号字符）、缩进不一致
   （SpinTwistor:128 用 3 空格）、`?` 洞（各文件 4–12 个）。2026-09-13 已修掉最初报告的 4 处
   ParseError（ParityViolation:199 / SpinTwistor:85 / Entanglement:142 / ZhonglvClosure:131），
   剩余同类尾巴未清（清完等于重写）。

## 已知例外（若日后要抢救，只看这两个）

- `civlayers-2026-07/03-neutral-144d/ZhonglvClosure.agda`：**孤儿**——`Sovereign.Coupling.
  ZhonglvClosure` 没有同名正式模块。若其内容未被 `src/Sovereign/Coupling/Zhonglv.agda`
  吸收，它是这批里唯一值得转正的。
- `civlayers-2026-07/03-neutral-144d/CartanTorsion.agda`：声明的是**裸模块名** `CartanTorsion`，
  且该目录自带 `.agda-lib`（`name: neutral144d / include: . / flags: --cubical --guardedness`），
  即原本就是当作独立 mini-library 用的。在原地编译得 `:140.44-59 [NotInScope]`。
