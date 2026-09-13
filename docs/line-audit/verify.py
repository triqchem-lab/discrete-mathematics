#!/usr/bin/env python3
"""完整性校验：比对 src/ 下全部 .agda（排除 _build）与 docs/line-audit 记录条目。"""
import os, re

files = set()
for root, dirs, fs in os.walk('src'):
    if '_build' in root.split(os.sep):
        continue
    for f in fs:
        if f.endswith('.agda'):
            files.add(os.path.join(root, f))

docs_paths = set()
for fn in os.listdir('docs/line-audit'):
    if fn.endswith('.md'):
        with open(os.path.join('docs/line-audit', fn), encoding='utf-8') as fh:
            for line in fh:
                m = re.match(r'^## `(src/.*\.agda)`', line)
                if m:
                    docs_paths.add(m.group(1))

missing = files - docs_paths
extra = docs_paths - files
print('源码模块: %d, 记录条目: %d' % (len(files), len(docs_paths)))
print('未记录: %d, 多余: %d' % (len(missing), len(extra)))
for m in sorted(missing):
    print('  MISSING:', m)
for m in sorted(extra):
    print('  EXTRA:', m)
print('RESULT:', 'PASS' if not missing and not extra else 'FAIL')
