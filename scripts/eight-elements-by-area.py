#!/usr/bin/env python3
"""生成「八要素 × 六区」对照表。

权威件（不替代，只汇总）：
  · 八要素定义/映射/机检信号：`docs/maps/八要素统一形状-2026-10-14.md` §二/§五/§六
  · 类型论正源：`docs/duodecimal/11-type-theory-presentation.md` §二/§四

两层判据（分开列，不混算）：
  A 声明层：模块头部自带 `-- ① 载体 …` 索引（L1 注释索引）。文件自己说有哪些要素。
  B 候选层：按 §五 机检信号正则扫描全库。⚠ §五是「候选器不是判官」（M8 §5）。

用法：
    python3 scripts/eight-elements-by-area.py
    python3 scripts/eight-elements-by-area.py --selftest   # 只打印 §六 五件真值校验
"""
import argparse
import collections
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOC = ROOT / 'docs/maps/八要素×六区对照-2026-10-27.md'

ELEMS = ['①', '②', '③', '④', '⑤', '⑥', '⑦', '⑧']
ENAME = {'①': '载体', '②': '生成元', '③': '关系', '④': '相位',
         '⑤': '时钟', '⑥': '归零', '⑦': '刚性', '⑧': '核对'}
AREAS = ['Foundation', 'Base', 'Infrastructure', 'Algebra', 'Synthesis', 'Application']

# §六 真值（2026-10-14 版），用于校验/标注漂移；'—' 表示当时判为缺
GROUND_TRUTH = {
    'src/Sovereign/Algebra/GroupTheory/DCGroup.agda': '①②③④⑤⑥⑦⑧',
    'src/Sovereign/Algebra/GroupTheory/DuodecClock.agda': '①②③④⑤⑥—⑧',
    'src/Sovereign/Algebra/NumberTheory/ModularArithmetic.agda': '①—③——⑥—⑧',
    'src/Sovereign/Application/Problems/NavierStokes/NSEPresentation.agda': '①②③④⑤⑥—⑧',
    'src/Sovereign/Algebra/UniversalAlgebra/AlgebraicPoleUnified.agda': '①②③④⑤⑥⑦⑧',
}

DECL = re.compile(r'^\s*--\s*([①②③④⑤⑥⑦⑧])\s*(.{0,24})')
NEG = re.compile(r'^\s*(⚠|✗|❌|—|–|-|未|无|缺|不)')
FIELD = re.compile(r'^\s{2,}[A-Za-z_₀-₉][\w\-₀-₉\'′]*\s*:')


def tracked():
    out = subprocess.run(['git', '-c', 'core.quotePath=false', 'ls-files',
                          'src/*.agda', 'src/**/*.agda'],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return sorted(l.strip() for l in out.splitlines() if l.strip())


def area_of(f):
    return f.split('/')[2] if f.count('/') > 2 else 'other'


def declared(path):
    """头部八要素索引：编号必须与该编号的规范要素名配对，且不得带「未显式/✗」否定。"""
    els = set()
    for i, line in enumerate((ROOT / path).open(encoding='utf-8')):
        if i > 120:
            break
        m = DECL.match(line)
        if not m:
            continue
        num, rest = m.group(1), m.group(2)
        if not rest.startswith(ENAME[num]):
            continue          # 例：`-- ⑥ 核对层：…` 是文件自己的章节编号，不是 ⑧ 核对
        tail = rest[len(ENAME[num]):]
        if NEG.match(tail):
            continue          # 例：`④ 相位 ⚠ 未显式` = 显式声明为缺
        els.add(num)
    return els


def signals(path):
    """按 §五 的信号表给候选判定；返回命中集合。"""
    lines = (ROOT / path).read_text(encoding='utf-8').splitlines()
    text = '\n'.join(lines)
    hit = set()

    # ① 载体：record 字段 carrier:，或顶层 X : Set 后紧跟乘积别名
    if re.search(r'\bcarrier\s*:', text):
        hit.add('①')
    else:
        for i, ln in enumerate(lines):
            if re.match(r'^[A-Z][\w\'-]*\s*:\s*Set\s*$', ln) and '×' in '\n'.join(lines[i:i + 3]):
                hit.add('①')
                break
    # ② 生成元：顶层 data + 「来源」标记
    if re.search(r'^data\s+\w+', text, re.M) and '来源' in text:
        hit.add('②')
    # ③ 关系：record 字段名含 assoc/identity/inverse/comm/unit 类，至少 2 个
    keys = [ln for ln in lines if FIELD.match(ln)
            and re.search(r'assoc|identity|inverse|\bcomm\b|\bunit\b', ln)]
    if keys and re.search(r'^\s*record\s+\S+', text, re.M) and len(keys) >= 2:
        hit.add('③')
    # ④ 相位：字段名含 phase/rot，或 order-N 定理
    if any(FIELD.match(ln) and re.search(r'phase|rot', ln, re.I) for ln in lines) \
            or re.search(r'order-\d+|-order-\w*4\b', text):
        hit.add('④')
    # ⑤ 时钟：字段名含 clock/cycle，或 -cycle 定理
    if any(FIELD.match(ln) and re.search(r'clock|cycle', ln, re.I) for ln in lines) \
            or re.search(r'-\d*-?cycle\b|mixedOp-\d+-cycle', text):
        hit.add('⑤')
    # ⑥ 归零：字段名含 zero，或 `e :`，或零冥族定理
    if any(FIELD.match(ln) and re.search(r'zero', ln, re.I) for ln in lines) \
            or re.search(r'^\s+e\s*:', text, re.M) or re.search(r'tritCycle|ZeroOblivion', text):
        hit.add('⑥')
    # ⑦ 刚性：引用 galoisConjugate（§五 强信号）
    if 'galoisConjugate' in text:
        hit.add('⑦')
    # ⑧ 核对：roundtrip / check-* / reconstruct（弱信号；裸 refl 不作数）
    if re.search(r'roundtrip|-roundtrip|check-|\bcheck[A-Z]|reconstruct', text):
        hit.add('⑧')
    return hit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--selftest', action='store_true')
    args = ap.parse_args()

    files = tracked()
    decl = {f: declared(f) for f in files}
    decl = {f: e for f, e in decl.items() if e}
    sig = {f: signals(f) for f in files} if not args.selftest else {}

    if args.selftest:
        print('§六 五件真值校验（声明层 vs 2026-10-14 表）')
        for f, gt in GROUND_TRUTH.items():
            now = ''.join(sorted(decl.get(f, set()))) or '（无头部索引）'
            print(f'  {f}\n     2026-10-14: {gt}\n     当前头部声明: {now}')
        return

    area_n = collections.Counter(area_of(f) for f in files)
    decl_area = collections.Counter(area_of(f) for f in decl)
    A = collections.defaultdict(collections.Counter)
    for f, els in decl.items():
        for e in els:
            A[area_of(f)][e] += 1
    B = collections.defaultdict(collections.Counter)
    for f, els in sig.items():
        for e in els:
            B[area_of(f)][e] += 1

    L = []
    w = L.append
    w('# 八要素 × 六区对照（2026-10-27）')
    w('')
    w('> ⚠️ 本文档是**汇总视图**，不替代权威件：')
    w('> - 八要素定义 / 代码形状 / 机检信号：`docs/maps/八要素统一形状-2026-10-14.md`（§二/§五/§六）')
    w('> - 类型论正源：`docs/duodecimal/11-type-theory-presentation.md`（§二/§四）')
    w('>')
    w('> **两层判据分开列**：A = 模块头部自述索引（文件自己说）；B = §五 机检正则（候选器）。')
    w('> §五 原文即声明「机检是候选器不是判官」（M8 §5）——B 表**不是**判据，只作定位用。')
    w('>')
    w('> 生成脚本：`scripts/eight-elements-by-area.py`')
    w('> 重新生成：`python3 scripts/eight-elements-by-area.py`')
    w('>')
    w(f'> 统计范围：`src/` 下受版本控制 {len(files)} 个模块；`pn-proofs/`、`probes/` 是 gitignore 草稿。')
    w('')
    w('## 1. 判据（照录 §五，附本脚本实现的正则）')
    w('')
    w('| # | 要素 | §五 机检信号 | 强度 | 本脚本正则（`scripts/eight-elements-by-area.py`） |')
    w('|---|---|---|---|---|')
    w(r'| ① | 载体 | `field` 行含 `carrier\s*:` 或 顶层 `X : Set` + `X = … × …` | 强 | `\bcarrier\s*:` ；或 `^[A-Z]\w* : Set$` 后 3 行含 `×` |')
    w(r'| ② | 生成元 | 顶层 `^data\s+\w+` 且构造子旁有「来源」标记 | 中 | `^data ` 且全文含 `来源` |')
    w(r'| ③ | 关系 | record 内同时含 assoc/identity/inverse 类字段 | 中 | ≥2 个字段行含 `assoc\|identity\|inverse\|comm\|unit` 且存在 `record` |')
    w(r'| ④ | 相位 | 字段名含 `phase`/`rot`，或有 `-order-N` 定理 | 中 | 字段行含 `phase\|rot` 或 `order-\d+` |')
    w(r'| ⑤ | 时钟 | 字段名含 `clock`/`cycle`，或 `^n p ≡ p` 形式 | 中 | 字段行含 `clock\|cycle` 或 `mixedOp-\d+-cycle` |')
    w(r'| ⑥ | 归零 | 字段名含 `zero`/`e :`，或零冥族定理 | 中 | 字段行含 `zero`、`^\s+e\s*:`、`tritCycle\|ZeroOblivion` |')
    w(r'| ⑦ | 刚性 | **引用** `galoisConjugate`（或等价 Galois 作用） | 强 | `galoisConjugate`（等价形态如 `mu`/`phaseConjugate` **不计**，见 §5） |')
    w(r'| ⑧ | 核对 | `refl` 证明 / `*-roundtrip` / `check*` | 弱 | `roundtrip\|check-\|check[A-Z]\|reconstruct`（裸 `refl` 不计） |')
    w('')
    w('## 2. 表 A：声明层（模块头部自述索引）')
    w('')
    pct = len(decl) * 100 // len(files)
    full = sum(1 for e in decl.values() if len(e) == 8)
    w(f'带头部八要素索引的模块：**{len(decl)} 个**（占全库 {pct}%），'
      f'其中 **{full} 个声明八项齐备**。')
    w('')
    w('| 要素 | ' + ' | '.join(AREAS) + ' | 合计 |')
    w('|---|' + '---:|' * (len(AREAS) + 1))
    for e in ELEMS:
        row = [A[a][e] for a in AREAS]
        w(f'| {e} {ENAME[e]} | ' + ' | '.join(str(v) if v else '' for v in row) + f' | **{sum(row)}** |')
    w('| **该区声明件数** | ' + ' | '.join(str(decl_area[a]) for a in AREAS) + f' | **{len(decl)}** |')
    w('')
    w('> 读法：这是**文件自己声明**的分布，分母是该区的声明件数（不是全区模块数）。')
    w('')
    w('### 2.1 解析规则（含已排除的两类误判）')
    w('')
    w('声明层不是「见到 ①-⑧ 就算」，必须同时满足三条，否则会把普通章节编号读成八要素索引：')
    w('')
    w('| 规则 | 反例（已排除） |')
    w('|---|---|')
    w('| **编号与规范要素名配对**（①↔载体 … ⑧↔核对） | `Foundation/LogicDecidable.agda:71` 的 `-- ⑥ 核对层：…` 是该文件自己的章节编号（⑥ 的规范名是「归零」），不计 |')
    w('| **要素名后不得是否定标记**（`⚠`/`✗`/`—`/`未`/`无`/`缺`/`不`） | `Foundation/Axioms.agda` 的 `④ 相位 ⚠ 未显式`、`⑤ 时钟 ⚠ 未显式`、`⑧ 核对 ⚠ 未显式` 是**显式声明为缺**，不计 |')
    w('| 只在文件头 120 行内扫描 | 正文里的 ①②③ 多为内容条目编号 |')
    w('')
    w('两轮修正的实测影响：不加过滤时声明层被虚高为 36 件 / 29 件「八项齐备」；'
      f'加上后为 **{len(decl)} 件 / {full} 件齐备**。')
    w('')
    w('## 3. 表 B：机检候选层（全库 %d 个模块）' % len(files))
    w('')
    w('| 要素 | ' + ' | '.join(AREAS) + ' | 合计 |')
    w('|---|' + '---:|' * (len(AREAS) + 1))
    for e in ELEMS:
        row = [B[a][e] for a in AREAS]
        w(f'| {e} {ENAME[e]} | ' + ' | '.join(str(v) if v else '' for v in row) + f' | **{sum(row)}** |')
    w('| **该区模块数** | ' + ' | '.join(str(area_n[a]) for a in AREAS) + f' | **{len(files)}** |')
    w('')
    w('命中率（该要素命中数 / 该区模块数）：')
    w('')
    w('| 要素 | ' + ' | '.join(AREAS) + ' |')
    w('|---|' + '---:|' * len(AREAS))
    for e in ELEMS:
        w(f'| {e} {ENAME[e]} | ' + ' | '.join(
            f'{B[a][e]*100//max(area_n[a],1)}%' for a in AREAS) + ' |')
    w('')
    w('## 4. 每个要素主要落在哪个区（表 B 的 argmax）')
    w('')
    w('| 要素 | 命中最多的区 | 该区命中 | 占该要素命中 | 次多 |')
    w('|---|---|---:|---:|---|')
    for e in ELEMS:
        per = {a: B[a][e] for a in AREAS}
        tot = sum(per.values()) or 1
        top = sorted(per.items(), key=lambda kv: -kv[1])
        w(f'| {e} {ENAME[e]} | {top[0][0]} | {top[0][1]} | {top[0][1]*100//tot}% | {top[1][0]}（{top[1][1]}） |')
    w('')
    w('## 5. 与 §六（2026-10-14）的漂移')
    w('')
    w('§六 的「现有件对照」表现在有三处 ⑦ 已过时——文件头部后来补了刚性声明：')
    w('')
    w('| 件 | §六 的 ⑦ | 当前头部声明 | 依据（文件头原文） |')
    w('|---|---|---|---|')
    w('| `GroupTheory/DuodecClock.agda` | `—` | ⑦ 已声明 | `⑦ 刚性 **mu**（Frobenius 诱导的相位反射）`，并注明 2026-10-21 修正「原写 `rho` ✗」 |')
    w('| `Application/…/NSEPresentation.agda` | `—` | ⑦ 已声明 | `⑦ 刚性 Frobenius 共轭 phaseConjugate (C₄ 的 C₂ 自同构)` |')
    w('| `GroupTheory/DCGroup.agda` | `rho` | ⑦ 已声明 | `⑦ 刚性 galoisConjugate（Frobenius 从 GF9 诱导）`，并注明 `rho` 属投影层、**不参与刚性** |')
    w('')
    w('⇒ 表 A 用**当前文件头**为准；§六 那张 2026-10-14 的表若要保留，需同步这三格。')
    w('')
    w('## 6. 已知误报 / 漏报（按 §五 原文的自我声明）')
    w('')
    w('- **误报**：`Techniques/Pgm1-2` 这类工具件会被词面命中（§五 明示，须白名单排除；本表未排除）。')
    w('- **漏报**：`DCGroup` 的核对以 `alpha-order-4` 形式存在，纯正则易漏（§五 原文）。')
    w('- **⑦ 的等价形态**：`mu`（DuodecClock）、`phaseConjugate`（NSEPresentation）是 Galois 作用的等价物，')
    w('  但 §五 的强信号只认 `galoisConjugate` ⇒ 表 B 会**低估**这两个件的 ⑦；表 A 不受影响。')
    w('- **① 的乘积别名**：只认「`X : Set` 后 3 行内出现 `×`」，跨行别名会漏。')
    w('')
    w('## 7. 复现')
    w('')
    w('```bash')
    w('python3 scripts/eight-elements-by-area.py             # 重新生成本文档')
    w('python3 scripts/eight-elements-by-area.py --selftest  # 只打 §六 五件的真值校验')
    w('```')
    w('')
    w('## 8. 附：表 A 的 %d 个声明件清单' % len(decl))
    w('')
    for f in sorted(decl):
        w(f'- `{f}` — {"".join(sorted(decl[f]))}')
    w('')

    DOC.parent.mkdir(parents=True, exist_ok=True)
    DOC.write_text('\n'.join(L) + '\n')
    print(f'wrote {DOC.relative_to(ROOT)} ({len(L)} lines)')
    print(f'declared={len(decl)} files, signals over {len(files)} files')


if __name__ == '__main__':
    main()
