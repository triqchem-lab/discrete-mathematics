#!/usr/bin/env python3
"""cmp_btp.py <a.pb.txt> <b.pb.txt>

比较两份证书的回溯轨迹档案（同名 .btp）：逐轨道比较解压后的记录（字节数 + 内容），
报告带轨迹的轨道数与记录总数。只读。对 2 亿条记录量级的档案要跑一两分钟。
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))  # engineering/
import wang_cert_check as base  # noqa: E402


def records(blobs):
    return sum(len(base.decode_proof(b)['sizes']) for b in blobs if b)


def main(argv):
    if len(argv) != 3:
        print(__doc__)
        return 2
    pa, pb = argv[1], argv[2]
    A = base.load_btp(pa[:-7] + '.btp')
    B = base.load_btp(pb[:-7] + '.btp')
    assert len(A) == len(B), (len(A), len(B))
    diff = [i for i in range(len(A)) if A[i] != B[i]]
    print(f'orbits {len(A)}  with-trace a={sum(1 for x in A if x)} b={sum(1 for x in B if x)}  '
          f'records a={records(A)} b={records(B)}  differing blobs={len(diff)}')
    for i in diff[:20]:
        print('  orbit', i, 'compressed bytes', len(A[i]), len(B[i]))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
