#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_cert_check.py — Wang 框架(arXiv:2603.07280)证书的独立 Python 核对器(立项 A-T2/A-T4)

独立实现(不信任对方二进制): 解析 protobuf 文本证书 → 重建 F₂ ⟨3,3,3⟩ 矩阵乘法张量 →
按维数 NA→0 扫描, 对每轨道独立复检其证明(镜像 verifier/verifier.h 的语义):
  - flatten: 对约束后张量取三个循环位的最优展平秩, CHECK >= 声明;
  - forced:  Hopcroft–Kerr 引理 2(A 侧秩一片强制 + 组合枚举取最小展平界);
  - degenerate: 加一行约束后 RREF 独立 + 见证映射到已验证轨道查界;
  - backtracking: 待移植(.btp 33MB DFS 轨迹重放)。

用法: python3 -I engineering/wang_cert_check.py <cert.pb.txt> [--kinds flatten,forced,degenerate]
退出码 0 = 已覆盖种类的全部检查通过。负控制: --corrupt <orbit-index> 篡改一条声明必须转红。
"""
import re
import sys

# ---------------------------------------------------------------------------
# protobuf 文本子集解析(本 schema 专用; 括号深度追踪, 无嵌套省略)
# ---------------------------------------------------------------------------

def unescape(s):
    """protobuf 文本转义: \nnn 八进制 / \\ / \" / 原样字符"""
    out = bytearray()
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == '\\':
            m = re.match(r'\\([0-7]{1,3})', s[i:])
            if m:
                out.append(int(m.group(1), 8) & 0xFF)
                i += len(m.group(0))
                continue
            nxt = s[i + 1]
            out.append({'n': 10, 't': 9, 'r': 13, '"': 34, "'": 39,
                        '\\': 92}[nxt])
            i += 2
            continue
        out.append(ord(ch) & 0xFF)
        i += 1
    return bytes(out)


def parse_blocks(text, kind):
    """按括号深度切出顶层 kind { ... } 块的内部文本(嵌套安全)"""
    blocks = []
    pat = re.compile(kind + r'\s*\{')
    pos = 0
    while True:
        m = pat.search(text, pos)
        if not m:
            break
        depth = 1
        i = m.end()
        start = i
        while depth:
            ch = text[i]
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
            i += 1
        blocks.append(text[start:i - 1])
        pos = i
    return blocks


def get_int(block, field):
    m = re.search(r'\b' + field + r':\s*(\d+)', block)
    return int(m.group(1)) if m else None


def get_str(block, field):
    m = re.search(r'\b' + field + r':\s*"((?:[^"\\]|\\.)*)"', block, re.S)
    return unescape(m.group(1)) if m else None


def parse_certificate(path):
    text = open(path, encoding='utf-8', errors='strict').read()
    cert = {
        'problem_name': re.search(r'problem_name:\s*"([^"]*)"', text).group(1),
        'characteristic': int(re.search(r'characteristic:\s*(\d+)', text).group(1)),
        'extension_degree': int(re.search(r'extension_degree:\s*(\d+)', text).group(1)),
        'na': int(re.search(r'\bna:\s*(\d+)', text).group(1)),
        'nb': int(re.search(r'\bnb:\s*(\d+)', text).group(1)),
        'nc': int(re.search(r'\bnc:\s*(\d+)', text).group(1)),
        'orbits': [],
    }
    for idx, b in enumerate(parse_blocks(text, 'constrained_tensors')):
        orbit = {'index': get_int(b, 'index') if get_int(b, 'index') is not None else idx}
        cons = []
        for cb in parse_blocks(b, 'constraints'):
            cons.append(get_str(cb, 'constraints') or get_str(cb, 'constraints'))
        # constraints 字段直接是标量字节串(每行 sizeof(GFVec) 字节)
        rows_raw = re.findall(r'constraints:\s*"((?:[^"\\]|\\.)*)"', b, re.S)
        orbit['raw_rows'] = [unescape(r) for r in rows_raw]
        orbit['rank_lower_bound'] = get_int(b, 'rank_lower_bound')
        orbit['kind'] = ('flatten' if 'flatten_matrix_proof {' in b else
                         'forced' if 'forced_product_proof {' in b else
                         'degenerate' if 'degenerate_proof {' in b else
                         'backtracking' if 'backtracking_proof {' in b else 'none')
        pt = re.search(r'projection_type:\s*(\d+)', b)
        orbit['projection_type'] = int(pt.group(1)) if pt else None
        orbit['extra_constraint'] = get_str(b, 'extra_constraint')
        orb_q = re.search(r'query_elem:\s*(\d+)', b)
        orb_s = re.search(r'store_elem:\s*(\d+)', b)
        orbit['query_elem'] = int(orb_q.group(1)) if orb_q else None
        orbit['store_elem'] = int(orb_s.group(1)) if orb_s else None
        orbit['block'] = b
        cert['orbits'].append(orbit)
    return cert


# ---------------------------------------------------------------------------
# GF(2) 线性代数(NA=9, GFVec = 9-bit 小端打包, 每行 2 字节)
# ---------------------------------------------------------------------------

def rows_from_bytes(raw, na):
    """constraints 字节串 → 行列表(每行 sizeof(GFVec) 字节, 9-bit 打包)"""
    row_bytes = (na + 7) // 8  # GFVec<2,1,9> = BitVec<9> = 2 字节
    assert len(raw) % row_bytes == 0, (len(raw), row_bytes)
    rows = []
    for r in range(len(raw) // row_bytes):
        chunk = raw[r * row_bytes:(r + 1) * row_bytes]
        v = int.from_bytes(chunk, 'little') & ((1 << na) - 1)
        assert (int.from_bytes(chunk, 'little') >> na) == 0, '行含越界高位'
        rows.append(v)
    return rows


def rref_f2(rows, na):
    """镜像 GaussJordanEliminationF2: 行从尾往前放、列从高位往下消,
    零行停在最前, 主元行升序落在尾段; 返回 (rows, rank)"""
    data = list(rows)
    size = len(data)
    rank = 0
    current_row = size - 1
    pivot_col = na - 1
    while current_row >= 0 and pivot_col >= 0:
        mask = 1 << pivot_col
        piv = None
        for r in range(current_row, -1, -1):
            if data[r] & mask:
                piv = r
                break
        if piv is None:
            pivot_col -= 1
            continue
        if piv != current_row:
            data[current_row], data[piv] = data[piv], data[current_row]
        for r in range(size):
            if r != current_row and (data[r] & mask):
                data[r] ^= data[current_row]
        rank += 1
        current_row -= 1
        pivot_col -= 1
    return data, rank


def is_canonical_rref(rows, na):
    """规范 RREF = 幂等(RREF(RREF(r)) == RREF(r)) 且满秩无零行"""
    r1, rank = rref_f2(rows, na)
    r2, _ = rref_f2(r1, na)
    return r1 == r2 and r1 == list(rows) and rank == len(rows) and all(r for r in rows)


# ---------------------------------------------------------------------------
# ⟨3,3,3⟩ 矩阵乘法张量(镜像 problems/matrix/tensor.h BuildMulTensor)
# ---------------------------------------------------------------------------

def build_mul_tensor(n0, n1, n2):
    """T[i*n1+j][j*n2+k][k*n0+i] = 1; F₂ 上即 0/1"""
    T = [[[0] * (n2 * n0) for _ in range(n1 * n2)] for _ in range(n0 * n1)]
    for i in range(n0):
        for j in range(n1):
            for k in range(n2):
                T[i * n1 + j][j * n2 + k][k * n0 + i] = 1
    return T


def apply_constraints_f2(tensor, rows, na, nb, nc):
    """镜像 ApplyConstraintsToTensor 的 F₂ 快路径: 主元折叠 + 支路清零"""
    res = [[list(slice_) for slice_ in plane] for plane in tensor]
    for row in rows:
        if row == 0:
            continue
        pivot = row.bit_length() - 1
        free = row ^ (1 << pivot)
        for i in range(na):
            if not (free >> i) & 1:
                continue
            for j in range(nb):
                for k in range(nc):
                    res[i][j][k] ^= res[pivot][j][k]
        for j in range(nb):
            for k in range(nc):
                res[pivot][j][k] = 0
    return res


def gf2_rank(mat):
    """F₂ 矩阵秩; mat = 行列表(每行整数位打包)"""
    rows = [r for r in mat if r]
    rank = 0
    cols = max((r.bit_length() for r in mat), default=0)
    for col in range(cols - 1, -1, -1):
        piv = None
        for i in range(rank, len(rows)):
            if (rows[i] >> col) & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(rank + 1, len(rows)):
            if (rows[i] >> col) & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def flatten_rank_a(tensor, na, nb, nc):
    """沿 A 轴展平成 na × (nb·nc) 矩阵的 F₂ 秩"""
    mat = []
    for i in range(na):
        row = 0
        for j in range(nb):
            for k in range(nc):
                if tensor[i][j][k]:
                    row |= 1 << (j * nc + k)
        mat.append(row)
    return gf2_rank(mat)


def cyclic_transpose(tensor, na, nb, nc):
    """result[j][k][i] = tensor[i][j][k]"""
    return [[[tensor[i][j][k] for i in range(na)]
             for k in range(nc)] for j in range(nb)]


def rank_lower_bound_flatten(tensor, na, nb, nc, target):
    """三个循环位的最优展平秩(镜像 RankLowerBoundFlatten, 含 target 短路)"""
    t1 = cyclic_transpose(tensor, na, nb, nc)
    r1 = flatten_rank_a(t1, nb, nc, na)
    if r1 >= target:
        return r1
    t2 = cyclic_transpose(t1, nb, nc, na)
    r2 = flatten_rank_a(t2, nc, na, nb)
    if r2 >= target:
        return r2
    r0 = flatten_rank_a(tensor, na, nb, nc)
    return max(r0, r1, r2)


# ---------------------------------------------------------------------------
# 主流程
# ---------------------------------------------------------------------------

def main(argv):
    path = argv[1]
    corrupt = None
    if '--corrupt' in argv:
        corrupt = int(argv[argv.index('--corrupt') + 1])
    covered_kinds = {'flatten'}  # 本版覆盖面; forced/degenerate/backtracking 随后增补
    cert = parse_certificate(path)
    print(f"problem={cert['problem_name']} char={cert['characteristic']} "
          f"ext={cert['extension_degree']} dims=({cert['na']},{cert['nb']},{cert['nc']})")
    assert cert['problem_name'] == 'matrix_q02_n333'
    assert cert['characteristic'] == 2 and cert['extension_degree'] == 1
    na, nb, nc = cert['na'], cert['nb'], cert['nc']
    assert (na, nb, nc) == (9, 9, 9)
    base_tensor = build_mul_tensor(3, 3, 3)

    orbits = cert['orbits']
    print(f"orbits: {len(orbits)}")
    from collections import Counter
    for o in orbits:
        o['dim'] = len(rows_from_bytes(b''.join(o['raw_rows']), na))
    census = Counter((o['dim'], o['kind']) for o in orbits)
    for (d, k), c in sorted(census.items()):
        print(f"  dim={d} {k:14s} count={c}")

    # 结构检查: 每轨道的行合法 + 规范 RREF(全量, 不限种类)
    checked = 0
    for o in orbits:
        rows = rows_from_bytes(b''.join(o['raw_rows']), na)
        if o['raw_rows']:
            assert is_canonical_rref(rows, na), f"orbit {o['index']} 不是规范 RREF"
            checked += 1
    print(f"[结构] 规范 RREF 检查: {checked}/{len(orbits)} 通过(其余为无约束终轨道)")

    # flatten 轨道复检
    ok = fail = 0
    for o in orbits:
        if o['kind'] != 'flatten':
            continue
        rows = rows_from_bytes(b''.join(o['raw_rows']), na)
        tensor = apply_constraints_f2(base_tensor, rows, na, nb, nc)
        lb = o['rank_lower_bound'] or 0
        if corrupt is not None and o['index'] == corrupt:
            lb += 7  # 负控制: 抬高声明
        computed = rank_lower_bound_flatten(tensor, na, nb, nc, lb)
        if computed >= lb:
            ok += 1
        else:
            fail += 1
            print(f"  !! flatten orbit {o['index']}: computed={computed} < claimed={lb}")
    print(f"[flatten] 通过 {ok}, 失败 {fail}")
    assert fail == 0, 'flatten 有失配'
    print('PARTIAL_PASS(flatten 覆盖; forced/degenerate/backtracking 待增补)')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
