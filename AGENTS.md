# 律算合一 (Sovereign Mathematics) — AGENTS.md

离散数学形式化验证: GF(3) 三进制 + T⁶ 离散环面 + CRT 谐波谱 + 主权 LCM 商空间。
Agda 形式化证明 + Python 工程验证双轨制。

## Project
- 技术栈: Agda 2.9.0 (自定义构建, `~/.local/bin/agda`), standard-library-2.4, cubical-0.9, agda-categories, agda-algebras
- 库注册: `sovereign.agda-lib` (flags: `--guardedness -WnoUnsupportedIndexedMatch`, include: `src`)
- 入口: ~~`src/Sovereign/All.agda`~~ 已取消 (2026-09-07 去聚合化, 模块独立编译); 全库 512 个 `.agda` 文件
- Python 轨道: `engineering/software/sovereign_core/` (零外部依赖)
- Git: 单分支 `master` → github.com/triqchem-lab/discrete-mathematics

## Commands（均已实测，注意当前状态）
- 全量编译: ~~`agda src/Sovereign/All.agda`~~ All.agda 已取消; 改为绿链/模块独立编译 (群论链/FLT链 gate, 见 engineering/check_*.sh)
  `Structology/HolographicSpace.agda:26` 等少数模块未开 `--rewriting`，却 import 带 `--rewriting` 的 `Base/Trit.agda`。
  **这是编译器传染性 flag 强制检查与项目代码的兼容性问题，不是代码缺陷**（全库 335/342 模块已统一 `--rewriting`）。
  项目既定处理（记忆 agda-stdlib-2-4-fixes §1）: 命令行不带 `--rewriting`，文件头保留 `{-# OPTIONS --rewriting --guardedness #-}`。
- 单模块检查: `agda src/Sovereign/Base/Trit.agda` ✅（仅 UnreachableClauses 警告）
- 测试集: **`make test` 是 no-op** — `test/` 目录遮蔽了 make target。必须用 `make -B test` ✅（17 模块，ALL_PASS）
- Python 测试: 在仓库根运行 `python3 -m pytest engineering/tests/` ✅ 29 passed
  （`cd engineering` 后运行会因 `engineering` 包不在 path 而 collection error）
- 编译产物: `_build/`、`*.agdai`（gitignored），不要删除

## Architecture
- `Base/` — GF(3) Trit 公理与不变量: POLAR=144, TORUS=46, CHERN=±2, SOVEREIGN_LCM=3¹¹·2¹⁶
- `Structology/` — T⁶ 环面、幻方 (M4/Arthur)、A₄ 群、格点、稳定态与 Burnside
- `Coupling/` — LCM 桥、仲吕相移、损益链、TQ10 格式
- `HoTT/` — CRT 谐波/纤维、T⁶ 同伦、陈类、万有覆盖
- `Format/` — CRT 基、谱投影; `Geometry/` — 射影(4320D G-轨道)、共形(1458)、环面几何
- `Algebra/` — GF(9)/GF(27)…、数字根、C₃ 轨道、Jacobian、Holographic; `Engine/` — 主权状态机; `MetaStructure/` — 五行、纳音
- 其余: Arithmetic/, Physics/, Quantum/, Topology/, Analysis/, PDE/, Density/, Coding/, Problem/, Trust/, Constitution/, AI/
- 顶层: `Integration.agda`、`Projection.agda`、`Examples.agda`（`All.agda` 已取消）
- 文档: `docs/`（架构/审计/路线图，中文）、`maps/` M1–M6、`memory/` 索引

## Conventions
- 注释一律中文；模块头部注释先说明数学背景（如 GF9 = GF(3)[x]/(x²+1)）
- Unicode 标识符: `T₀ T₁ T₂`、`⊕ ⊗`、`≡ ≅`、`⊎`
- 证明风格: 有限类型逐 case 的 refl 证明；目标零 postulate（README 的 85 文件/72 零 postulate 数字已过时）
- `--rewriting` 是全库标准 (335/342 模块)，承载自定义 REWRITE 规则——**语义完备性设计**，不是补丁:
  - `T6.agda`: `div3k`/`mod3k`/`gf3Toℕ-A4-inv` (4320D 归约, 替代 mod-helper 展开, 避免类型检查 OOM)
  - `XuanwuAbsorption.agda`: `mod46k`/`div46k`/`mod-a+598`; `jac_Pigeonhole.agda`: `decode9-encode9`
  - 合法性论述: `/data/work/docs/wiki/02-geometric-pole.md` C.3.1
- REWRITE 规则传染性: import 带重写规则模块的模块必须自带 `--rewriting`（Agda 保证 subject reduction 的强制检查）。
  少数模块刻意不开（如 `HolographicSpace.agda` 注释: 类型保持 ∀ n 参数化、避免 Fin 归一化展开）——
  由此触发的 InfectiveImport 报错是 **Agda 2.9.0 开发版固有限制/兼容性问题**，非代码缺陷，不要当 bug 修
- 宪法约束（详见 `memory/dual_track_constitution.md`）: 禁浮点数（无理数用定点整数比）、禁 postulate、范畴分离、144/46 全息 π 禁止约分、十二律长度表静态、标准库信任度=0
- 工作区现状: `src/Sovereign/Algebra/GF9.agda` 有未提交改动；`src/_test_irrelevant.agda` 是未跟踪草稿

## Notes
（待补充）
