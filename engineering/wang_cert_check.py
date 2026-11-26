#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_cert_check.py — Wang 框架(arXiv:2603.07280)证书的独立 Python 核对器(立项 A-T2/A-T4)

独立实现(不信任对方二进制, 零外部依赖): 解析 protobuf 文本证书 → 重建 F₂ ⟨3,3,3⟩ 矩阵乘法
张量 → 按行数 9→0 扫描, 对每轨道独立复检其证明(逐行镜像 verifier/verifier.h +
backtracking_verifier.h + core/{gf,gf_vec,constraints,tensor,rank_lower_bound_*,backtracking_proof}):

  - flatten:      约束后张量三个循环位的最优展平秩, CHECK >= 声明;
  - forced:       Hopcroft–Kerr 引理 2(A 侧秩一片强制 + q^(r2p·r1) 组合枚举取最小展平界 + r1);
  - degenerate:   extra_constraint + RREF 独立 + 见证映射(query/store 群作用)查已验证轨道;
  - backtracking: .btp 档案(BTPARCH\\0 v2, 每轨道 gzip blob: n u64 + sizes u8×n +
                  masks/queries/stores u32×n 小端)的 DFS 前序轨迹重放。

用法: python3 -I engineering/wang_cert_check.py <cert.pb.txt> [--corrupt <orbit-index>]
退出码 0 = 全部 496 轨道核对通过。负控制: --corrupt 篡改该轨道声明, 必须转红。
"""
import gzip
import re
import sys

# ---------------------------------------------------------------------------
# protobuf 文本子集解析(本 schema 专用; 括号深度追踪, 无嵌套省略)
# ---------------------------------------------------------------------------

def unescape(s):
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
            out.append({'n': 10, 't': 9, 'r': 13, '"': 34, "'": 39, '\\': 92}[s[i + 1]])
            i += 2
            continue
        out.append(ord(ch) & 0xFF)
        i += 1
    return bytes(out)


def parse_blocks(text, kind):
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


def parse_certificate(path):
    text = open(path, encoding='utf-8').read()
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
        orbit = {'index': idx, 'raw_rows': []}
        rows_raw = re.findall(r'constraints:\s*"((?:[^"\\]|\\.)*)"', b, re.S)
        orbit['raw_rows'] = [unescape(r) for r in rows_raw]
        m = re.search(r'rank_lower_bound:\s*(-?\d+)', b)
        orbit['rank_lower_bound'] = int(m.group(1)) if m else None
        orbit['kind'] = ('flatten' if 'flatten_matrix_proof {' in b else
                         'forced' if 'forced_product_proof {' in b else
                         'degenerate' if 'degenerate_proof {' in b else
                         'backtracking' if 'backtracking_proof {' in b else 'none')
        pt = re.search(r'projection_type:\s*(\d+)', b)
        orbit['projection_type'] = int(pt.group(1)) if pt else None
        ec = re.search(r'extra_constraint:\s*(\d+)', b)
        orbit['extra_constraint'] = int(ec.group(1)) if ec else None
        qe = re.search(r'query_elem:\s*(\d+)', b)
        se = re.search(r'store_elem:\s*(\d+)', b)
        orbit['query_elem'] = int(qe.group(1)) if qe else None
        orbit['store_elem'] = int(se.group(1)) if se else None
        cert['orbits'].append(orbit)
    return cert


# ---------------------------------------------------------------------------
# GF(2) 线性代数(NA=9, GFVec = 9-bit 小端打包, 每行 2 字节)
# ---------------------------------------------------------------------------

def rows_from_bytes(raw, na):
    row_bytes = (na + 7) // 8
    assert len(raw) % row_bytes == 0
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
    r1, rank = rref_f2(rows, na)
    r2, _ = rref_f2(r1, na)
    return r1 == r2 and r1 == list(rows) and rank == len(rows) and all(r for r in rows)


def gf2_rank(mat):
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


# ---------------------------------------------------------------------------
# ⟨3,3,3⟩ 矩阵乘法张量(镜像 problems/matrix/tensor.h BuildMulTensor)
# ---------------------------------------------------------------------------

def build_mul_tensor(n0, n1, n2):
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


# 位打包工具: 切片 = (nb*nc)-bit 整数, 位 (j*nc+k) = T[i][j][k]

def slice_matrix_rank(s, nb, nc):
    rows = [(s >> (j * nc)) & ((1 << nc) - 1) for j in range(nb)]
    return gf2_rank(rows)


def transpose_slices(slices, na, nb, nc):
    """t1[j][k][i] = slices[i][j][k] → t1_j 的位 (k*na+i)"""
    out = []
    for j in range(nb):
        v = 0
        for i in range(na):
            row_j = (slices[i] >> (j * nc)) & ((1 << nc) - 1)
            v |= row_j << (i * na)
        out.append(v)
    return out


def rank_lower_bound_flatten(slices, na, nb, nc, target):
    """镜像 RankLowerBoundFlatten: B 位 → C 位 → A 位, 逐位 target 短路"""
    t1 = transpose_slices(slices, na, nb, nc)
    r1 = gf2_rank(t1)
    if r1 >= target:
        return r1
    t2 = transpose_slices(t1, nb, nc, na)
    r2 = gf2_rank(t2)
    if r2 >= target:
        return r2
    r0 = gf2_rank(slices)
    return max(r0, r1, r2)


# ---------------------------------------------------------------------------
# ★ forced: Hopcroft–Kerr 引理 2(镜像 RankLowerBoundForcedProductA)
# ---------------------------------------------------------------------------

def nested_slice_rank(slice_):
    """9×9 嵌套矩阵的 F₂ 秩"""
    rows = [sum(cell << k for k, cell in enumerate(row)) for row in slice_]
    return gf2_rank(rows)


def nested_flatten_max(tensor):
    """三个方向的展平秩的最大值(嵌套列表; 已与 C++ verifier 对拍: 轨道 5 受限张量 = 6)"""
    rows_a = []
    for a in range(9):
        rows_a.append(sum(tensor[a][j][k] << (j * 9 + k)
                          for j in range(9) for k in range(9)))
    rows_b = []
    for j in range(9):
        rows_b.append(sum(tensor[i][j][k] << (i * 9 + k)
                          for i in range(9) for k in range(9)))
    rows_c = []
    for k in range(9):
        rows_c.append(sum(tensor[i][j][k] << (j * 9 + i)
                          for i in range(9) for j in range(9)))
    return max(gf2_rank(rows_a), gf2_rank(rows_b), gf2_rank(rows_c))


def forced_product_a_nested(tensor, claim):
    """镜像 RankLowerBoundForcedProductA(嵌套列表版; tensor = [9][9][9] 嵌套)"""
    def flatten81(sl):
        return sum(sl[j][k] << (j * 9 + k) for j in range(9) for k in range(9))

    ranks = [nested_slice_rank(tensor[i]) for i in range(9)]
    r1_count = sum(1 for r in ranks if r == 1)
    if r1_count == 0:
        return 0
    r1_nested, r2p, r1_flat = [], [], []
    for i in range(9):
        if ranks[i] == 0:
            continue
        if ranks[i] == 1:
            cand = flatten81(tensor[i])
            r1_flat.append(cand)
            if gf2_rank(r1_flat) == len(r1_flat):
                r1_nested.append(tensor[i])
                continue
            r1_flat.pop()
            r2p.append(tensor[i])
        else:
            r2p.append(tensor[i])
    r1_bc_rows = len(r1_nested)
    bit_width = len(r2p) * r1_bc_rows
    if bit_width > 64:
        return 0  # uint64 溢出取消(镜像)
    num_iterations = 1 << bit_width
    k_prime = 73074167
    local_min = 1 << 30
    zero_slice = [[[0] * 9 for _ in range(9)]]
    for t in range(num_iterations):
        scrambled = (t * k_prime) % num_iterations
        tensor_t = [list(map(list, sl)) for sl in r2p] + \
                   [[[0] * 9 for _ in range(9)] for _ in range(9 - len(r2p))]
        for bit_idx in range(bit_width):
            if (scrambled >> bit_idx) & 1:
                r1_idx = bit_idx % r1_bc_rows
                i = bit_idx // r1_bc_rows
                for j in range(9):
                    for k in range(9):
                        tensor_t[i][j][k] ^= r1_nested[r1_idx][j][k]
        remaining = nested_flatten_max(tensor_t)
        local_min = min(local_min, r1_bc_rows + remaining)
    return local_min


def verify_forced_nested(tensor, claim):
    """镜像 VerifyForcedProductProof: 三个循环位取最大"""
    computed = forced_product_a_nested(tensor, claim)
    t1 = [[[tensor[i][j][k] for i in range(9)] for k in range(9)] for j in range(9)]
    c1 = forced_product_a_nested(t1, claim)
    t2 = [[[t1[j][k][i] for j in range(9)] for i in range(9)] for k in range(9)]
    c2 = forced_product_a_nested(t2, claim)
    return max(computed, c1, c2)


# ---------------------------------------------------------------------------
# ★ 对称群与 CanonicalFromWitness(镜像 problems/matrix/symmetry.h + backtracking_verifier.h)
# ---------------------------------------------------------------------------

def mat_mul(a, b, n0, n1, n2):
    out = 0
    for i in range(n0):
        for j in range(n2):
            acc = 0
            for k in range(n1):
                acc ^= (((a >> (i * n1 + k)) & 1) & ((b >> (k * n2 + j)) & 1))
            if acc:
                out |= 1 << (i * n2 + j)
    return out


def mat_transpose(a, n):
    out = 0
    for i in range(n):
        for j in range(n):
            if (a >> (i * n + j)) & 1:
                out |= 1 << (j * n + i)
    return out


def mat_inv(a, n):
    """F₂ 上 n×n 求逆(增广 Gauss; 假定可逆)"""
    rows = [(a >> (i * n)) & ((1 << n) - 1) for i in range(n)]
    inv_rows = [1 << i for i in range(n)]
    for col in range(n - 1, -1, -1):
        piv = None
        for i in range(col, -1, -1):
            if (rows[i] >> col) & 1:
                piv = i
                break
        assert piv is not None, '矩阵不可逆'
        rows[col], rows[piv] = rows[piv], rows[col]
        inv_rows[col], inv_rows[piv] = inv_rows[piv], inv_rows[col]
        for i in range(n):
            if i != col and ((rows[i] >> col) & 1):
                rows[i] ^= rows[col]
                inv_rows[i] ^= inv_rows[col]
    out = 0
    for i in range(n):
        out |= inv_rows[i] << (i * n)
    return out


def enumerate_gl(n):
    """镜像 EnumerateGL: 单位阵在前, 其余按 data 升序"""
    ident = sum(1 << (i * n + i) for i in range(n))
    out = [ident]
    for d in range(1 << (n * n)):
        if d == ident:
            continue
        rows = [(d >> (i * n)) & ((1 << n) - 1) for i in range(n)]
        if gf2_rank(rows) == n:
            out.append(d)
    return out


GL3 = enumerate_gl(3)
GL3_SET = set(GL3)
IDENT3 = GL3[0]


def query_apply(v, q_l, q_t):
    m = mat_transpose(v, 3) if q_t else v
    return mat_mul(q_l, m, 3, 3, 3)


def query_apply_inverse(v, q_l, q_t):
    w = mat_mul(mat_inv(q_l, 3), v, 3, 3, 3)
    return mat_transpose(w, 3) if q_t else w


def store_apply_inverse(v, s_r):
    return mat_mul(v, mat_inv(s_r, 3), 3, 3, 3)


def canonical_from_witness(extended_rows, raw_query, raw_store):
    """镜像 backtracking_verifier.h CanonicalFromWitness:
    每行 v ↦ store.apply_inverse(store, query.apply(query, v)); RREF 后保留最后 rank 行"""
    q_l = raw_query & 0xFFFF
    q_t = (raw_query >> 16) & 0xFFFF
    s_r = raw_store & 0xFFFF
    assert q_l in GL3_SET and q_t in (0, 1) and s_r in GL3_SET, '见证元素不在对称群里'
    image = [store_apply_inverse(query_apply(v, q_l, q_t), s_r)
             for v in extended_rows]  # 镜像 C++: query.Apply(正向) + store.ApplyInverse
    r1, rank = rref_f2(image, 9)
    return tuple(r1[len(r1) - rank:])  # 去掉前导零行, 保留最后 rank 行


# ---------------------------------------------------------------------------
# ★ .btp 档案解码与回溯重放(镜像 backtracking_proof.cc + backtracking_verifier.h)
# ---------------------------------------------------------------------------

def load_btp(path):
    data = open(path, 'rb').read()
    assert data[:8] == b'BTPARCH\x00', 'bad archive magic'
    version = int.from_bytes(data[8:12], 'little')
    assert version == 2, version
    count = int.from_bytes(data[12:20], 'little')
    pos = 20
    blobs = []
    for _ in range(count):
        ln = int.from_bytes(data[pos:pos + 8], 'little')
        pos += 8
        blobs.append(data[pos:pos + ln])
        pos += ln
    assert pos == len(data)
    return blobs


def decode_proof(blob):
    if not blob:
        return {'sizes': [], 'masks': [], 'queries': [], 'stores': []}
    d = gzip.decompress(blob)
    n = int.from_bytes(d[0:8], 'little')
    off = 8
    sizes = list(d[off:off + n])
    off += n
    masks = [int.from_bytes(d[off + 4 * i:off + 4 * i + 4], 'little') for i in range(n)]
    off += 4 * n
    queries = [int.from_bytes(d[off + 4 * i:off + 4 * i + 4], 'little') for i in range(n)]
    off += 4 * n
    stores = [int.from_bytes(d[off + 4 * i:off + 4 * i + 4], 'little') for i in range(n)]
    off += 4 * n
    assert off == len(d)
    return {'sizes': sizes, 'masks': masks, 'queries': queries, 'stores': stores}


def build_minimal(base_rows, na):
    """镜像构造: F₂^na 中不带任何基主元位的非零行(升序)"""
    base_pivots = [r.bit_length() - 1 for r in base_rows if r]
    minimal = []
    for value in range(1, 1 << na):
        skip = False
        for p in base_pivots:
            if (value >> p) & 1:
                skip = True
                break
        if not skip:
            minimal.append(value)  # F₂: LeadingNonzero 恒为 1
    assert minimal, '极小约束集为空'
    return minimal


def make_backtracking_verifier(base_rows, claim, proof, group_map, orbit_index=None):
    """镜像 RankLowerBoundBacktrackingVerifier"""
    na = 9
    minimal = build_minimal(base_rows, na)

    def dfs_verify(max_constraint_idx, dfs_constraints, proof_index):
        pi = proof_index[0]
        assert pi < len(proof['sizes']), '轨迹超出证明长度'
        p_dfs_size = proof['sizes'][pi]
        max_depth = claim - 1
        assert len(dfs_constraints) <= p_dfs_size, 'dfs 深度超过记录'
        if len(dfs_constraints) == p_dfs_size:
            mask = proof['masks'][pi]
            assert p_dfs_size > 0
            valid = (1 << p_dfs_size) - 1
            assert mask & ~valid == 0, 'mask 选到路径之外'
            assert mask & (1 << (p_dfs_size - 1)), 'mask 必须选最新路径项'
            extended = list(base_rows)
            for i in range(len(dfs_constraints)):
                if mask & (1 << i):
                    extended.append(dfs_constraints[i])
            assert len(extended) > len(base_rows)
            canonical = canonical_from_witness(extended, proof['queries'][pi],
                                               proof['stores'][pi])
            b = group_map.get(canonical)
            if b is None:
                same_dim = [k for k in group_map if len(k) == len(canonical)]
                raise AssertionError(
                    f'orbit {orbit_index}: backtracking 叶子 canonical 不在 map: '
                    f'{[bin(r) for r in canonical]}: {claim}; '
                    f'同维 map 键数 {len(same_dim)}, 示例 '
                    f'{[[bin(r) for r in k] for k in same_dim[:2]]}; '
                    f'extended 行 {len(extended)}')
            proved = bin(mask).count('1') + b
            assert claim <= proved, f'backtracking: claim {claim} > proved {proved}'
            proof_index[0] += 1
            return
        assert len(dfs_constraints) < max_depth, '回溯分支未在 L-1 深度内闭合'
        for i in range(max_constraint_idx + 1):
            dfs_constraints.append(minimal[i])
            dfs_verify(i, dfs_constraints, proof_index)
            dfs_constraints.pop()

    def verify():
        assert 0 < claim <= 32, claim
        proof_index = [0]
        dfs_verify(len(minimal) - 1, [], proof_index)
        assert proof_index[0] == len(proof['sizes']), '轨迹长度不匹配'

    return verify


# ---------------------------------------------------------------------------
# 主流程: 维数扫描 NA→0(镜像 VerifyRankLowerBound)
# ---------------------------------------------------------------------------

def main(argv):
    path = argv[1]
    corrupt = None
    if '--corrupt' in argv:
        corrupt = int(argv[argv.index('--corrupt') + 1])
    cert = parse_certificate(path)
    print(f"problem={cert['problem_name']} char={cert['characteristic']} "
          f"ext={cert['extension_degree']} dims=({cert['na']},{cert['nb']},{cert['nc']})")
    assert cert['problem_name'] == 'matrix_q02_n333'
    assert cert['characteristic'] == 2 and cert['extension_degree'] == 1
    na, nb, nc = cert['na'], cert['nb'], cert['nc']
    assert (na, nb, nc) == (9, 9, 9)
    assert len(cert['orbits']) > 0
    base_tensor = build_mul_tensor(3, 3, 3)

    orbits = cert['orbits']
    for o in orbits:
        o['rows'] = rows_from_bytes(b''.join(o['raw_rows']), na)
        o['dim'] = len(o['rows'])
        if o['rank_lower_bound'] is None:
            o['rank_lower_bound'] = 0
        if corrupt is not None and o['index'] == corrupt:
            o['rank_lower_bound'] += 7  # 负控制: 抬高声明
    from collections import Counter
    census = Counter((o['dim'], o['kind']) for o in orbits)
    for (d, k), c in sorted(census.items()):
        print(f"  dim={d} {k:14s} count={c}")

    needs_archive = any(o['kind'] == 'backtracking' for o in orbits)
    archive = None
    if needs_archive:
        archive_path = path
        for suffix in ('.pb.txt.gz', '.pb.gz', '.pb.txt', '.pb'):
            if archive_path.endswith(suffix):
                archive_path = archive_path[: -len(suffix)] + '.btp'
                break
        archive = load_btp(archive_path)
        assert len(archive) == len(orbits)

    group_map = {}
    counts = Counter()
    for dim in range(na, -1, -1):
        bucket = [o for o in orbits if o['dim'] == dim]
        if not bucket:
            continue
        for o in bucket:
            kind = o['kind']
            rows = o['rows']
            claim = o['rank_lower_bound']
            if rows:
                assert is_canonical_rref(rows, na), f"orbit {o['index']} 不是规范 RREF"
            if kind == 'none':
                assert claim <= 0, f"orbit {o['index']} 无证明却声明 {claim}"
                counts[kind] += 1
                continue
            if kind == 'flatten':
                slices = [sum(row[j][k] << (j * nc + k) for j in range(nb) for k in range(nc))
                          for row in apply_constraints_f2(base_tensor, rows, na, nb, nc)]
                computed = rank_lower_bound_flatten(slices, na, nb, nc, claim)
                assert computed >= claim, f"orbit {o['index']}: flatten {computed} < {claim}"
            elif kind == 'forced':
                constrained = apply_constraints_f2(base_tensor, rows, na, nb, nc)
                computed = verify_forced_nested(constrained, claim)
                assert computed >= claim, f"orbit {o['index']}: forced {computed} < {claim}"
            elif kind == 'degenerate':
                raw_extra = o['extra_constraint']
                assert raw_extra is not None and 0 <= raw_extra < (1 << na), 'extra_constraint 越界'
                extended = rows + [raw_extra]
                r2, rank2 = rref_f2(extended, na)
                assert rank2 == len(extended), 'degenerate: 加行后线性相关'
                canonical = canonical_from_witness(extended, o['query_elem'], o['store_elem'])
                b = group_map.get(canonical)
                assert b is not None, f"orbit {o['index']}: degenerate 规范轨道不在 map"
                assert b >= claim, f"orbit {o['index']}: degenerate {b} < {claim}"
            elif kind == 'backtracking':
                proof = decode_proof(archive[o['index']])
                verifier = make_backtracking_verifier(rows, claim, proof, group_map,
                                                       orbit_index=o['index'])
                verifier()  # 内部自管首调用与轨迹长度检查
            else:
                raise AssertionError(kind)
            counts[kind] += 1
        for o in bucket:
            key = tuple(o['rows'])
            assert key not in group_map, f"orbit {o['index']} 重复轨道代表"
            group_map[key] = o['rank_lower_bound']
        print(f"  dim={dim}: 核对 {len(bucket)} 轨道, 累计 map={len(group_map)}")

    assert len(group_map) == len(orbits), 'map 大小与轨道数不符'
    last = orbits[-1]
    assert last['rows'] == [], '最后轨道必须是无约束张量'
    result = last['rank_lower_bound']
    print(f"UNCONSTRAINED TENSOR RANK LOWER BOUND: {result}")
    print(f"OK. 已核对 {len(orbits)} 轨道: {dict(counts)}")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
