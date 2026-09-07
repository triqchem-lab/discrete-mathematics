#!/usr/bin/env python3
import os, re, json, sys
from pathlib import Path

SRC = 'src'
OUT = 'docs/line-audit'
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
        lines = fh.read().split('\n')
    total = len(lines)
    nonempty = [l for l in lines if l.strip() != '']
    comment_only = [l for l in nonempty if l.strip().startswith('--')]
    code_lines = [l for l in nonempty if not l.strip().startswith('--')]

    text = '\n'.join(lines)
    # module decl
    m = re.search(r'^\s*module\s+([\w.]+)\s', text, re.M)
    modname = m.group(1) if m else '(no module decl)'
    # OPTIONS
    opts = re.findall(r'\{-#\s*OPTIONS\s+([^#]*?)#-\}', text)
    opts = [o.strip() for o in opts]
    # imports
    imports = re.findall(r'^\s*(?:open\s+)?import\s+([\w.]+)', text, re.M)
    open_imports = re.findall(r'^\s*open\s+import\s+([\w.]+)', text, re.M)
    # postulates
    postulates = re.findall(r'^\s*postulate\b', text, re.M)
    # rewrite rules
    rewrites = re.findall(r'^\s*\{-#\s*REWRITE\s+', text, re.M)
    # holes
    holes = len(re.findall(r'\{\s*!\s*!\s*\}', text))
    qmarks = len(re.findall(r'(?<![\w?])\?(?![\w?])', text))
    # refl count
    refl_count = len(re.findall(r'\brefl\b', text))
    # data/record declarations
    datas = re.findall(r'^\s*data\s+([\w]+)', text, re.M)
    records = re.findall(r'^\s*record\s+([\w]+)', text, re.M)
    # top-level functions with type signature: name : type  at col 0
    funcs = re.findall(r'^([\w\u2200-\u22ff\u0391-\u03c9\u4e00-\u9fff][\w\-\u2032\u4e00-\u9fff\u2080-\u209f]*)\s*:\s*', text, re.M)
    # private/abstract keywords
    privates = len(re.findall(r'^\s*private\b', text, re.M))
    abstracts = len(re.findall(r'^\s*abstract\b', text, re.M))
    # TODO/FIXME
    todos = len(re.findall(r'--\s*(TODO|FIXME|XXX)', text))
    # head comment block: first contiguous comment lines after OPTIONS
    head_comments = []
    in_head = True
    for l in lines:
        s = l.strip()
        if s.startswith('{-#') or s.startswith('module ') or s.startswith('open import') or s.startswith('import '):
            in_head = False
            continue
        if in_head and s.startswith('--'):
            head_comments.append(s.lstrip('- ').strip())
            if len(head_comments) > 30:
                break
        elif s == '' :
            continue
        else:
            if in_head and not s.startswith('--'):
                in_head = False
    return {
        'path': fp,
        'module': modname,
        'total_lines': total,
        'code_lines': len(code_lines),
        'comment_lines': len(comment_only),
        'options': opts,
        'imports': imports,
        'open_imports': open_imports,
        'postulate_count': len(postulates),
        'rewrite_count': len(rewrites),
        'holes': holes,
        'refl_count': refl_count,
        'data': datas,
        'record': records,
        'top_level_sigs': funcs,
        'private': privates,
        'abstract': abstracts,
        'todo': todos,
        'head_comments': head_comments,
    }

results = []
for fp in files:
    try:
        results.append(analyze(fp))
    except Exception as e:
        results.append({'path': fp, 'error': str(e)})

safe_out('audit_full.json').write_text(json.dumps(results, ensure_ascii=False, indent=1))

# summary
total_lines = sum(r.get('total_lines',0) for r in results)
total_code = sum(r.get('code_lines',0) for r in results)
total_refl = sum(r.get('refl_count',0) for r in results)
total_post = sum(r.get('postulate_count',0) for r in results)
total_holes = sum(r.get('holes',0) for r in results)
print(f"模块数: {len(results)}")
print(f"总行数: {total_lines}, 代码行: {total_code}")
print(f"refl 总数: {total_refl}, postulate 总数: {total_post}, holes 总数: {total_holes}")
# modules with postulates
post_mods = [r for r in results if r.get('postulate_count',0) > 0]
print(f"\n含 postulate 的模块 ({len(post_mods)}):")
for r in post_mods:
    print(f"  [{r.get('postulate_count')}] {r['path']}")
# modules with holes
hole_mods = [r for r in results if r.get('holes',0) > 0]
print(f"\n含 hole 的模块 ({len(hole_mods)}):")
for r in hole_mods:
    print(f"  [holes={r.get('holes')}] {r['path']}")
