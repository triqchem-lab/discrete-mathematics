---
name: toolchain-agda-only-no-dype
description: 本数学库的裁决器口径——proof_compile 走 agda 通道（不请求 dype）；附 agdaBin 现状与两个已踩过的坑。dype 自身的状态见 dype 仓 docs/TOOLCHAIN-STATUS.md
type: project
---

# 裁决器口径：本库的形式化一律用 Agda（2026-09-13 人类指示）

> **适用域（必读）**
> 本条的定义域是：**本数学库（`discrete-mathematics`）的形式化该用哪个裁决器** ——
> `proof_compile` 走哪条通道、哪颗内核的结论可以写进台账 `proven`。
> **不适用于 dype 编译器项目（`/data/work/functional-programming/dype`）自身的架构问题**
> （包边界、内核归属、`Dayan.Kernel.Conversion` 接不接进内核、A/B 行为对拍怎么做）——
> 那些由 dype 仓自己的判据决定，**本条不作为其依据**；dype 侧的数据已迁至
> dype 仓 `docs/TOOLCHAIN-STATUS.md`（2026-09-14 按域拆分）。
> ⚠ 反例（真实发生过）：把本条套用到「是否把 Dayan 判定层接入内核」，是**定义域混淆**。

## 1. 决定

- `proof_compile` **一律用 agda**；今后显式传 `checker:"agda"`，不依赖默认回退。
- **不主动请求 `checker:"dype"`**。
- **唯一例外：交叉验证** —— 需要第二个独立内核对同一命题做行为对拍时才用 dype；
  此时结论必须标注「非权威，需 Agda 复核」，且**不得**以 dype 通过作为节点 `proven` 的证据。

## 2. agdaBin 现状（实测，会漂）

- `~/.local/bin/agda` → symlink → `/data/work/functional-programming/agda/.stack-work/dist/x86_64-linux/ghc-9.14.1/build/agda/agda`
  （项目补丁版 stack build，153 MB，mtime Sep 11 08:01）
- `--version` = `2.9.0-nightly`。⚠ **不是**历史流水里记的 `2.9.0-1705389`；它建在哪个 commit **未验证**。
- `/opt/agda/agda` **已不存在**（旧回退路径失效）。
- 唯一备选：`/usr/local/bin/agda`（`2.9.0-nightly`，**无项目补丁**，历史上曾因 prim 数据目录
  带 `--cubical` 而对本库全库报 `InfectiveImport` —— 现已能编过，原因未核）。

## 3. 两个已踩过的坑

1. **`proof_compile` 的 agda 通道依赖那个 symlink。** 目标一消失，工具直接报
   「无法编译：没有可用检查器」，退化成只有 dype 候选 —— 而 dype 也不可用，于是**完全无裁决器**。
   修法：`ln -sfn <patched-agda> ~/.local/bin/agda`。
2. **注释也会作废回执。** 回执绑源码哈希，改一个字符即失效。
   2026-09-13 实测：给 `NSEOnT6.agda` 加 42 行注释 → `NSE.T4`/`NSE.T5` 回执失效、
   台账掉到 90/100；重编重签（4.1 s）后回到 100/100。
   ⇒ **动任何 `.agda` 文件，改完顺手重编重签。**

## 4. 附带纪律

- 回执**不记录裁决器版本** ⇒ 引用旧回执时须另外标注当时的工具链版本串。
- 撞到 Agda 行为差异（尤其空类型判定）时，**先怀疑裁决器不是项目补丁版**。

## 5. 锚点

- 配置：`impl/local-paths.json`（键 `agdaBin`；`dypeRoot` 指向 dype 仓）
- 台账流水 2026-09-13：`decision`（本口径）+ `handoff`（agdaBin 修复与重签，回执 `c19ba03d…`）
- **dype 侧数据**（实验性内核定位、二进制 `/src/data` 阻塞、交叉验证纪律、包布局实测）：
  dype 仓 `docs/TOOLCHAIN-STATUS.md`
- 相关外部参照：`docs/NavierStokes/`、OpenAI Lean 仓库（`/data/work/leanprover/NavierStokesAndEuler`）
