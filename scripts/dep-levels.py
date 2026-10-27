#!/usr/bin/env python3
"""生成《模块依赖-import12层》报告。

口径声明（文档头会原样写入）：
  · 第三种口径（import 图），不替代 `docs/课题依赖DAG.{md,yaml,json}` 与 `proof_dag` 台账；
  · 12 层 = import 链深度，不是数学抽象层级；
  · 向上依赖是测量事实、不等于缺陷。

用法：
    python3 scripts/dep-levels.py            # 生成 docs/maps/模块依赖-import12层-2026-10-27.md
    python3 scripts/dep-levels.py --levels-only
                                             # 只写 _build/verify/levels.txt（供并行编译调度）

数据源：`git ls-files 'src/**.agda'`（受版本控制模块；pn-proofs/、probes/ 是 gitignore 草稿）。
"""
import argparse
import collections
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOC = ROOT / 'docs/maps/模块依赖-import12层-2026-10-27.md'
LEVELS = ROOT / '_build/verify/levels.txt'

AREA_ORDER = ['Foundation', 'Base', 'Infrastructure', 'Algebra', 'Synthesis', 'Application']
# Foundation 与 Base 同为 L0 原语层（互相 import 不算逆序）；Infrastructure 跨切带豁免。
RANK = {'Foundation': 0, 'Base': 0, 'Algebra': 2, 'Synthesis': 3, 'Application': 4}
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z][A-Za-z0-9_.']*)")


def tracked_files():
    out = subprocess.run(
        ['git', '-c', 'core.quotePath=false', 'ls-files', 'src/*.agda', 'src/**/*.agda'],
        cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return sorted(l.strip() for l in out.splitlines() if l.strip())


def area_of(f):
    return f.split('/')[2] if f.count('/') > 2 else 'other'


def analyse():
    files = tracked_files()
    mod_of = {f[len('src/'):-len('.agda')].replace('/', '.'): f for f in files}
    deps, dep_site = {}, {}
    for m, f in mod_of.items():
        sites = {}
        for ln, line in enumerate(open(ROOT / f, encoding='utf-8'), 1):
            h = IMPORT.match(line)
            if h and h.group(1) in mod_of:
                sites.setdefault(h.group(1), f'{f}:{ln}')
        deps[m], dep_site[m] = list(sites), sites

    level, chain = {}, {}

    def walk(m):
        if m not in level:
            lv = max((walk(d)[0] for d in deps[m]), default=0) + 1
            deep = max((walk(d)[1] for d in deps[m]), key=len, default=[])
            level[m], chain[m] = lv, [m] + deep
        return level[m], chain[m]

    for m in sorted(mod_of):
        walk(m)

    area_edges, area_ex = collections.Counter(), collections.defaultdict(list)
    lv_edges = collections.Counter()
    for m, f in mod_of.items():
        a = area_of(f)
        for d in deps[m]:
            b = area_of(mod_of[d])
            area_edges[(a, b)] += 1
            lv_edges[(level[m], level[d])] += 1
            if len(area_ex[(a, b)]) < 2:
                area_ex[(a, b)].append(dep_site[m][d])

    per_level = collections.defaultdict(list)
    by_area_level = collections.defaultdict(collections.Counter)
    intra, cross = collections.Counter(), collections.Counter()
    for m, lv in level.items():
        per_level[lv].append(m)
        by_area_level[lv][area_of(mod_of[m])] += 1
    for (a, b), n in area_edges.items():
        (intra if a == b else cross)[a] += n

    deepest = max(level, key=lambda m: level[m])
    return dict(files=files, mod_of=mod_of, deps=deps, level=level, chain=chain,
                area_edges=area_edges, area_ex=area_ex, lv_edges=lv_edges,
                per_level=per_level, by_area_level=by_area_level,
                intra=intra, cross=cross, deepest=deepest)


def write_levels(d):
    LEVELS.parent.mkdir(parents=True, exist_ok=True)
    rows = sorted((d['level'][m], d['mod_of'][m]) for m in d['mod_of'])
    LEVELS.write_text(''.join(f'{l}\t{p}\n' for l, p in rows))
    print(f'wrote {LEVELS.relative_to(ROOT)} ({len(rows)} modules)')


def write_doc(d):
    mod_of, level = d['mod_of'], d['level']
    area_edges, area_ex, lv_edges = d['area_edges'], d['area_ex'], d['lv_edges']
    per_level, by_area_level = d['per_level'], d['by_area_level']
    intra, cross = d['intra'], d['cross']
    maxlv = max(level.values())
    viol = sum(n for (a, b), n in area_edges.items()
               if a in RANK and b in RANK and RANK[b] > RANK[a])
    chain = d['chain'][d['deepest']]

    L = []
    w = L.append
    w('# 模块依赖-import12层')
    w('')
    w('> ⚠️ 本文档是**第三种口径**（import 图），不替代：')
    w('> - `docs/课题依赖DAG.{md,yaml,json}`（课题语义 DAG）')
    w('> - `proof_dag` 台账（回执）')
    w('>')
    w('> **用途**：并行调度——12 层是 import 链深度，**不是**数学抽象层级。')
    w(f'> **{viol} 条向上依赖**是测量事实，不等于缺陷；处置需逐条裁决，本文档只列事实。')
    w('')
    w('> 生成脚本：`scripts/dep-levels.py`（层级数据：`_build/verify/levels.txt`）')
    w('> 重新生成：`python3 scripts/dep-levels.py`')
    w('')
    w('> 抽象层级以 `AGENTS.md` 的声明为准：`Foundation` 与 `Base` 同为 L0 原语层'
      '（互相 import 不算逆序）→ `Algebra`(L2) → `Synthesis`(L3) → `Application`(L4)；'
      '`Infrastructure` 是跨切带，声明上豁免 import 单调性。')
    w('>')
    w(f'> 统计范围：`src/` 下**受版本控制**的 {len(mod_of)} 个模块；`pn-proofs/`、`probes/` 是 gitignore 草稿，不计。')
    w('')
    w('## 0. 三种「层级」不要混用')
    w('')
    w('| 口径 | 产物/位置 | 回答什么问题 |')
    w('|---|---|---|')
    w('| **课题依赖 DAG** | `docs/课题依赖DAG.{md,yaml,json}` | 研究课题之间谁先谁后（L0 基座 → A/B/C/D 类），语义口径 |')
    w('| **proof_dag 台账** | `proof_dag` 工具（search/check/journal） | 哪个符号已证、证据在哪（回执口径） |')
    w('| **import 深度层** | 本文档 | 编译调度：同层无依赖 ⇒ 可并行；**不是**数学抽象层级 |')
    w('')
    w('## 1. 结论先说：12 层 ≠ 12 级抽象')
    w('')
    w('- 声明抽象层只有 **4 级**（+ 1 个跨切带）；import 图实测最深 **%d 层**。' % maxlv)
    w('- 差异来自**同区文件拆分链**，不是跨区叠层：')
    for a in ['Foundation', 'Base', 'Algebra', 'Synthesis', 'Application']:
        t = intra[a] + cross[a]
        w(f'  - `{a}`：{t} 条内部 import，其中同区 {intra[a]} 条（{intra[a]*100//max(t,1)}%），跨区 {cross[a]} 条。')
    w('- 最长链（`%s`，%d 个模块）的区域序列：' % (d['deepest'], len(chain)))
    w('')
    w('```')
    w(' → '.join(area_of(mod_of[m]) for m in chain))
    w('```')
    w('')
    w('  整条链**只在 Algebra 内部绕**（Burnside 一族 6 文件、Coset 2 文件、Jacobian 2 文件），')
    w('  最后一跳才落到 `Base.Trit`。这就是「%d 层」的全部来源。' % maxlv)
    w('')
    w('## 2. 每层模块数 + 抽象层构成')
    w('')
    w('| import 层 | 模块数 | ' + ' | '.join(AREA_ORDER) + ' |')
    w('|---|---:|' + '---:|' * len(AREA_ORDER))
    for lv in range(1, maxlv + 1):
        c = by_area_level[lv]
        w(f'| L{lv} | {sum(c.values())} | ' + ' | '.join(str(c[a]) if c[a] else '' for a in AREA_ORDER) + ' |')
    w('')
    w('读法：L1 是「不依赖仓库内任何模块」的叶子（却已横跨 6 个区——说明**区域名不是深度**）；')
    w('越往上越窄，说明深层链集中在少数专题（群论、Jacobian、A4、拓扑）。')
    w('')
    w('## 3. 区域依赖矩阵（行 = 谁 import，列 = 被 import）')
    w('')
    w('| 从 \\ 到 | ' + ' | '.join(AREA_ORDER) + ' |')
    w('|---|' + '---:|' * len(AREA_ORDER))
    for a in AREA_ORDER:
        w(f'| **{a}** | ' + ' | '.join(str(area_edges[(a, b)]) if area_edges[(a, b)] else '' for b in AREA_ORDER) + ' |')
    w('')
    w('### 3.1 向上依赖（导入**更高**层；`Infrastructure` 按声明豁免）')
    w('')
    w('| 方向 | 边数 | 例 |')
    w('|---|---:|---|')
    for (a, b), n in sorted(area_edges.items(), key=lambda kv: -kv[1]):
        if a in RANK and b in RANK and RANK[b] > RANK[a]:
            w(f'| `{a}` → `{b}` | {n} | `{area_ex[(a,b)][0]}` |')
    w(f'| **合计** | **{viol}** | |')
    w('')
    w('> 这些是**按 `AGENTS.md` 声明判**的向上边，不等于错误：有些 `Application/` 子目录实际承担')
    w('> 库角色（如 `Application/Algebra/`），或专题跨区复用了证明件。要处置须逐条裁决，本文只列事实。')
    w('> 逐条裁决是**另一个任务**（可另建 `docs/maps/向上依赖-裁决清单.md`），不是本文件的前提。')
    w('')
    w('## 4. 依赖图（Mermaid）')
    w('')
    w('### 4.1 区域级（虚线 = 向上依赖）')
    w('')
    w('```mermaid')
    w('flowchart BT')
    for a in AREA_ORDER:
        w(f'    {a}["{a}"]')
    for (a, b), n in sorted(area_edges.items(), key=lambda kv: -kv[1]):
        if n == 0 or a == b:
            continue
        arrow = '-.->' if (a in RANK and b in RANK and RANK[b] > RANK[a]) else '-->'
        w(f'    {a} {arrow}|{n}| {b}')
    w('```')
    w('')
    w('### 4.2 import 层聚合（节点 = 层，边 = 跨层 import 条数，只画 ≥3 条的）')
    w('')
    w('```mermaid')
    w('flowchart BT')
    for lv in range(1, maxlv + 1):
        w(f'    L{lv}["L{lv} · {sum(by_area_level[lv].values())} 模块"]')
    for (a, b), n in sorted(lv_edges.items(), key=lambda kv: -kv[1]):
        if a == b or n < 3:
            continue
        w(f'    L{a} -->|{n}| L{b}')
    w('```')
    w('')
    w('### 4.3 最长链（%d 跳）' % (len(chain) - 1))
    w('')
    w('```mermaid')
    w('flowchart BT')
    for i, m in enumerate(chain):
        w(f'    C{i}["{m.split(".")[-1]} · {area_of(mod_of[m])}"]')
    for i in range(len(chain) - 1):
        w(f'    C{i} --> C{i+1}')
    w('```')
    w('')
    w('## 5. 逐层清单（全部 %d 个模块）' % len(mod_of))
    w('')
    for lv in range(1, maxlv + 1):
        ms = sorted(per_level[lv])
        c = by_area_level[lv]
        parts = '、'.join(f'{a} {c[a]}' for a in AREA_ORDER if c[a])
        w(f'### L{lv}（{len(ms)} 个：{parts}）')
        w('')
        for m in ms:
            w(f'- `{mod_of[m]}`')
        w('')
    w('## 6. 复现')
    w('')
    w('```bash')
    w('python3 scripts/dep-levels.py              # 重新生成本文档 + 层级数据')
    w('python3 scripts/dep-levels.py --levels-only  # 只刷 _build/verify/levels.txt')
    w('```')

    DOC.parent.mkdir(parents=True, exist_ok=True)
    DOC.write_text('\n'.join(L) + '\n')
    print(f'wrote {DOC.relative_to(ROOT)} ({len(L)} lines); levels={maxlv} modules={len(mod_of)} upward_edges={viol}')
    print('deepest:', d['deepest'])
    print('chain area sequence:', ' → '.join(area_of(mod_of[m]) for m in chain))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--levels-only', action='store_true', help='只写 _build/verify/levels.txt')
    args = ap.parse_args()
    d = analyse()
    write_levels(d)
    if not args.levels_only:
        write_doc(d)


if __name__ == '__main__':
    main()
