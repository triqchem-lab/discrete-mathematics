#!/usr/bin/env python3
"""cmpcert.py <a.pb.txt> <b.pb.txt> [max_dim]

逐轨道比较两份证书（用仓库里的解析器 engineering/wang_cert_check.py）：
维数 / 界 / 证明类型 / forced 的投影位 / degenerate 的额外约束。报告差异条数、逐维界的分布、
以及（可选）维数 ≤ max_dim 的轨道明细。只读，不改任何文件。

用法示例:
  cmpcert.py certs/matrix_q03_n333_v2.pb.txt run/out.pb.txt 3
"""
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))  # engineering/
import wang_cert_check as base  # noqa: E402


def load(path):
    cert = base.parse_certificate(path)
    out = {}
    for o in cert['orbits']:
        nrows = sum(len(r) for r in o['raw_rows']) // cert['na']
        out[o['index']] = (nrows, o['rank_lower_bound'] or 0, o['kind'],
                           o.get('projection_type'), o.get('extra_constraint'))
    return out


def main(argv):
    if len(argv) < 3:
        print(__doc__)
        return 2
    a, b = load(argv[1]), load(argv[2])
    print('entries', len(a), len(b))
    diff = [(k, a.get(k), b.get(k)) for k in sorted(set(a) | set(b)) if a.get(k) != b.get(k)]
    print('differing entries:', len(diff))
    for k, x, y in diff[:80]:
        print(f'  idx {k}: {x} -> {y}')
    better = sum(1 for _, x, y in diff if x and y and y[1] > x[1])
    worse = sum(1 for _, x, y in diff if x and y and y[1] < x[1])
    print('improved:', better, ' regressed:', worse)
    dims = {}
    for k, (d, lb, kind, proj, extra) in sorted(b.items()):
        dims.setdefault(d, []).append((lb, kind))
    for d in sorted(dims):
        print(f'dim {d}: n={len(dims[d])} bounds={sorted(set(x[0] for x in dims[d]))} '
              f'kinds={dict(Counter(x[1] for x in dims[d]))}')
    print('kinds:', dict(Counter(v[2] for v in b.values())))
    last = max(b) if b else None
    if last is not None:
        print(f'final orbit {last}: dim {b[last][0]} bound {b[last][1]} ({b[last][2]})')
    if len(argv) > 3:
        for k, v in sorted(b.items()):
            if v[0] <= int(argv[3]):
                print('  idx', k, v[:4])
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
