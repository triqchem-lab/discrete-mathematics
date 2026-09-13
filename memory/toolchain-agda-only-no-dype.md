---
name: toolchain-agda-only-no-dype
description: 裁决器口径——只用 Agda，不用 dype（除非做交叉验证）；附 agdaBin 当前状态与两个已踩过的坑
type: project
---

# 裁决器口径：只用 Agda，不用 dype（2026-09-13 人类指示）

## 1. 决定

- `proof_compile` **一律用 agda**；今后显式传 `checker:"agda"`，不依赖默认回退。
- **不主动请求 `checker:"dype"`**。
- **唯一例外：交叉验证** —— 需要第二个独立内核对同一命题做行为对拍时才用 dype；
  此时结论必须标注「非权威，需 Agda 复核」，且**不得**以 dype 通过作为节点 `proven` 的证据。
- 依据：dype 是项目自研**实验性内核**，不作裁决权威；且当前两个 dype 二进制都因
  `data dir /src/data` 不存在而跑不起来（实测：`proof_compile` 把它列在「被跳过的检查器」）。

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

- 配置：`impl/local-paths.json`（键 `agdaBin` / `dypeRoot`）
- 台账流水 2026-09-13：`decision`（本口径）+ `handoff`（agdaBin 修复与重签，回执 `c19ba03d…`）
- 相关外部参照：`docs/NavierStokes/`、OpenAI Lean 仓库（`/data/work/leanprover/NavierStokesAndEuler`）
