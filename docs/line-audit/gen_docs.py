#!/usr/bin/env python3
import os, re, collections
from pathlib import Path

SRC = 'src'
OUT = 'docs/line-audit'
os.makedirs(OUT, exist_ok=True)
OUT_REAL = os.path.realpath(OUT)

def safe_out(name):
    # 路径穿越防护: 只允许安全文件名字符, 且解析后必须落在 OUT 内
    if not re.fullmatch(r'[A-Za-z0-9_.\-]+', name):
        raise ValueError('非法输出文件名: %r' % name)
    base = Path(OUT).resolve()
    p = (base / name).resolve()
    if p.parent != base:
        raise ValueError('输出路径越界: %r' % name)
    return p

files = []
for root, dirs, fs in os.walk(SRC):
    if '_build' in root.split(os.sep):
        continue
    for f in fs:
        if f.endswith('.agda'):
            files.append(os.path.join(root, f))
files.sort()

def analyze(fp):
    with open(fp, 'r', errors='replace') as fh:
        content = fh.read()
    lines = content.split('\n')
    total = len(lines)
    nonempty = [l for l in lines if l.strip()]
    comment_lines = sum(1 for l in nonempty if l.strip().startswith('--'))
    code_lines = len(nonempty) - comment_lines
    text = content
    m = re.search(r'^\s*module\s+([\w.]+)\s', text, re.M)
    modname = m.group(1) if m else '(no module decl)'
    opts = [o.strip() for o in re.findall(r'\{-#\s*OPTIONS\s+([^#]*?)#-\}', text)]
    imports = re.findall(r'^\s*(?:open\s+)?import\s+([\w.]+)', text, re.M)
    postulates = re.findall(r'^\s*postulate\b', text, re.M)
    rewrites = re.findall(r'^\s*\{-#\s*REWRITE\s+([\w.]+)', text, re.M)
    holes = len(re.findall(r'\{\s*!\s*!\s*\}', text))
    refl_count = len(re.findall(r'\brefl\b', text))
    datas = re.findall(r'^\s*data\s+([\w]+)', text, re.M)
    records = re.findall(r'^\s*record\s+([\w]+)', text, re.M)
    funcs = re.findall(r'^([^\s{}(][\w\u2200-\u22ff\u0391-\u03c9\u4e00-\u9fff\u2080-\u209f\u00b0\u2032\-]*)\s*:\s*', text, re.M)
    todos = len(re.findall(r'--\s*(TODO|FIXME|XXX)\b', text))
    head = []
    for l in lines:
        s = l.strip()
        if s.startswith('module '):
            break
        if s.startswith('--'):
            head.append(s.lstrip('- ').strip())
    return {
        'path': fp, 'module': modname, 'total': total, 'code': code_lines,
        'comment': comment_lines, 'options': opts, 'imports': imports,
        'postulate': len(postulates), 'rewrites': rewrites, 'holes': holes,
        'refl': refl_count, 'data': datas, 'record': records, 'funcs': funcs,
        'todo': todos, 'head': head,
    }

results = [analyze(fp) for fp in files]

groups = collections.OrderedDict()
for r in results:
    d = os.path.dirname(r['path'])
    groups.setdefault(d, []).append(r)

index_lines = []
index_lines.append('# 全库逐模块逐行审计记录 (Line Audit)\n')
index_lines.append('> 自动遍历 `src/` 下全部 `.agda` 模块（排除 `_build/`），逐行读取并提取结构化信息。\n')
index_lines.append('- 模块总数: **%d**' % len(results))
total_all = sum(r['total'] for r in results)
code_all = sum(r['code'] for r in results)
comment_all = sum(r['comment'] for r in results)
refl_all = sum(r['refl'] for r in results)
post_all = sum(r['postulate'] for r in results)
hole_all = sum(r['holes'] for r in results)
npost_mods = sum(1 for r in results if r['postulate'])
nhole_mods = sum(1 for r in results if r['holes'])
index_lines.append('- 总行数: **%d**（代码 %d / 注释 %d）' % (total_all, code_all, comment_all))
index_lines.append('- 全库 `refl` 出现: **%d**' % refl_all)
index_lines.append('- 全库 `postulate`: **%d**（分布在 %d 个模块）' % (post_all, npost_mods))
index_lines.append('- 全库 hole `{!!}`: **%d**（分布在 %d 个模块）' % (hole_all, nhole_mods))
index_lines.append('')
index_lines.append('## 目录索引')
index_lines.append('')
for d in groups:
    fname = d.replace('/', '_').replace('src_', '') + '.md'
    cnt = len(groups[d])
    lines_sum = sum(r['total'] for r in groups[d])
    index_lines.append('- `%s/` (%d 模块, %d 行) → [%s](%s)' % (d, cnt, lines_sum, fname, fname))
index_lines.append('')
index_lines.append('## 含 postulate 的模块（与零 postulate 目标冲突，需关注）')
index_lines.append('')
for r in results:
    if r['postulate']:
        index_lines.append('- `%s` → %d postulate' % (r['path'], r['postulate']))
index_lines.append('')
index_lines.append('## 含 hole 的模块（未完成证明）')
index_lines.append('')
for r in results:
    if r['holes']:
        index_lines.append('- `%s` → %d hole' % (r['path'], r['holes']))
safe_out('INDEX.md').write_text('\n'.join(index_lines) + '\n')

for d, rs in groups.items():
    fname = d.replace('/', '_').replace('src_', '') + '.md'
    lines = []
    lines.append('# 目录 `%s/` 逐模块审计记录\n' % d)
    lines.append('共 %d 个模块。\n' % len(rs))
    for r in rs:
        lines.append('')
        lines.append('## `%s`' % r['path'])
        lines.append('')
        lines.append('- **module**: `%s`' % r['module'])
        lines.append('- **行数**: %d（代码 %d / 注释 %d）' % (r['total'], r['code'], r['comment']))
        if r['options']:
            lines.append('- **OPTIONS**: %s' % ', '.join('`%s`' % o for o in r['options']))
        if r['head']:
            lines.append('- **头部注释（数学背景）**:')
            for h in r['head'][:20]:
                if h:
                    lines.append('  - %s' % h)
        if r['imports']:
            lines.append('- **导入 (%d)**: %s' % (len(r['imports']), ', '.join('`%s`' % i for i in r['imports'])))
        if r['data']:
            lines.append('- **data 类型**: %s' % ', '.join('`%s`' % x for x in r['data']))
        if r['record']:
            lines.append('- **record 类型**: %s' % ', '.join('`%s`' % x for x in r['record']))
        if r['funcs']:
            fset = []
            seen = set()
            for f in r['funcs']:
                if f not in seen and f not in ('where','module','import','open'):
                    seen.add(f); fset.append(f)
            lines.append('- **顶层签名 (%d)**: %s' % (len(fset), ', '.join('`%s`' % x for x in fset[:60])))
            if len(fset) > 60:
                lines.append('  - … 其余 %d 项' % (len(fset) - 60))
        if r['rewrites']:
            lines.append('- **REWRITE 规则**: %s' % ', '.join('`%s`' % x for x in r['rewrites']))
        flag = []
        if r['postulate']: flag.append('%d postulate' % r['postulate'])
        if r['holes']: flag.append('%d hole' % r['holes'])
        if r['todo']: flag.append('%d TODO' % r['todo'])
        status = ' / '.join(flag) if flag else '干净'
        q = '- **质量**: `refl`×%d；%s' % (r['refl'], ('⚠️ ' + status) if flag else '无 postulate / 无 hole')
        lines.append(q)
    safe_out(fname).write_text('\n'.join(lines) + '\n')

print('已生成 %d 个目录记录文件 + INDEX.md 到 %s/' % (len(groups), OUT))
print('总模块 %d，总行数 %d' % (len(results), total_all))
