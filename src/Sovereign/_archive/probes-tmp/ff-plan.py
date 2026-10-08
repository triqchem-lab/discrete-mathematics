#!/usr/bin/env python3
"""解析 run.sh 的 all 分派块 → 用例计划（JSON 行打到 stdout，不写文件）。
保序；共享 (prof, port) 的相邻用例聚为一组（同 origin 复现 Chrome 语义）。
输出行: {"name":..., "page":..., "query":..., "group":<int>, "port":<int|0>}
用法: python3 ff-plan.py /path/to/run.sh"""
import json, re, shlex, sys

src = open(sys.argv[1]).read()
# all 分派块：从 "  all)" 到下一个列首的 "  ;;"
m = re.search(r"^  all\)\n(.*?)^    exit \$rc ;;", src, re.S | re.M)
block = m.group(1)
# 反斜杠续行拼接
block = block.replace("\\\n", " ")

cases = []
group = 0
prev_key = None
for line in block.splitlines():
    line = line.strip()
    if not line.startswith("run_one "):
        continue
    toks = shlex.split(line)
    # run_one name src out page [extra] [query] [prof] [port] [|| rc=1 等 shell 尾巴]
    name, page = toks[1], toks[4]
    rest = [t for t in toks[5:] if t not in ("||", "rc=1", ";;", "|| rc=1")]
    # 位置参数语义：len(rest)>=1 extra；>=2 query；>=3 prof；>=4 port
    # extra/query 可为空串占位（run.sh 用 "" 跳过）
    query = rest[1] if len(rest) >= 2 and rest[1] else ""
    prof = rest[2] if len(rest) >= 3 and rest[2] else ""
    port = rest[3] if len(rest) >= 4 and rest[3] else ""
    key = (prof, port)
    if key == ("", ""):
        cases.append({"name": name, "page": page, "query": query, "group": 0, "port": 0})
    else:
        if key != prev_key:
            group += 1
            prev_key = key
        cases.append({"name": name, "page": page, "query": query,
                      "group": group, "port": port})

for c in cases:
    print(json.dumps(c, ensure_ascii=False))
print(f"# 共 {len(cases)} 用例，分组 {group}", file=sys.stderr)
