#!/usr/bin/env python3
"""扫描 Agda 模块中所有 refl 穷举 (按子句数) 与 case-split 枚举。"""
import io, os, re, sys
from collections import defaultdict

root = "src"
results = []
for dirpath, _, files in os.walk(root):
    for fn in files:
        if not fn.endswith(".agda"):
            continue
        p = os.path.join(dirpath, fn)
        try:
            lines = io.open(p, encoding="utf-8").read().splitlines()
        except Exception:
            continue
        # 收集以 "name ... = refl" 结尾的连续子句块
        cur = None
        count = 0
        for i, ln in enumerate(lines):
            s = ln.strip()
            if not s or s.startswith("--") or s.startswith("{-"):
                continue
            m = re.match(r"^([a-zA-Z_][a-zA-Z0-9_'\-]*)\s+(.*?)\s*=\s*refl\s*$", s)
            if m:
                name = m.group(1)
                if cur == name:
                    count += 1
                else:
                    if cur is not None and count >= 9:
                        results.append((count, cur, p))
                    cur = name
                    count = 1
            else:
                if cur is not None and count >= 9:
                    results.append((count, cur, p))
                cur = None
                count = 0
        if cur is not None and count >= 9:
            results.append((count, cur, p))

results.sort(key=lambda x: (-x[0], x[2]))
for c, n, p in results:
    print("%5d  %-45s %s" % (c, n, p))
print("总计: %d 个枚举, %d 条子句" % (len(results), sum(c for c, _, _ in results)))
