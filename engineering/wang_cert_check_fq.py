#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_cert_check_fq.py — Wang 框架证书的独立核对器: 素域通用版(P = 3, 即 GF(3))

与 wang_cert_check.py(F₂ 位打包版, 已对 q02_n333 全量核对 496/496)并存的通用域实现。
复用其中与域无关的部分(protobuf 文本解析、.btp 档案解码、BuildMulTensor), 其余按
verifier/verifier.h + backtracking_verifier.h + core/{constraints,math_utils,
rank_lower_bound_*,symmetry}.h 的**通用域路径**(GaussJordanEliminationFq、
ApplyConstraintsToTensor 的 F_q 支路、RankLowerBoundForcedProductA 的 q 进制支路)镜像:

  - 结构: 每轨道的约束行是 F_q^NA 的元素(每行 NA 字节, 每字节一个域元素下标), 且在规范 RREF
    (GaussJordanEliminationFq: 行从尾往前放、列从高位往下消、零行在前、主元归一);
  - flatten:      约束后张量三个循环位的最优展平秩 ≥ 声明;
  - forced:       Hopcroft–Kerr 引理 2: q^(r2p·r1) 组合枚举(乱序访问 + target 短路)取最小 + r1;
                  大枚举交给独立 C 内核(forced_fq.c), 小枚举直接算;
  - degenerate:   extra_constraint + RREF 独立 + 见证映射(query.Apply 正向, store.ApplyInverse)
                  查已验证轨道;
  - backtracking: .btp DFS 前序轨迹重放。

用法: python3 -I engineering/wang_cert_check_fq.py <cert.pb.txt> [--corrupt <orbit-index>]
退出码 0 = 全部轨道核对通过。
"""
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wang_cert_check as base  # noqa: E402

INF = float('inf')
HERE = os.path.dirname(os.path.abspath(__file__))
C_HELPER = os.path.join(HERE, 'forced_fq_c', 'forced_fq')
BT_HELPER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "forced_fq_c", "bt_fq")
BT_HELPER_SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "forced_fq_c", "bt_fq.c")
# Python 直接枚举的上限(超过则必须用 C 内核)
PY_ITER_CAP = 3 ** 11

P = 3  # 由 main 按证书设置
NA = NB = NC = 9


# ---------------------------------------------------------------------------
# 域与行运算(行 = Σ_k digit_k · P^k 的整数)
# ---------------------------------------------------------------------------

def digit(v, k):
    return (v // P ** k) % P


def modinv(a):
    a %= P
    for x in range(1, P):
        if a * x % P == 1:
            return x
    raise ZeroDivisionError


def rows_from_bytes_fq(raw, na):
    """每行 na 字节, 每字节一个域元素下标(ConstraintsFromBytes 的通用域布局)"""
    assert len(raw) % na == 0
    rows = []
    for r in range(len(raw) // na):
        chunk = raw[r * na:(r + 1) * na]
        assert all(b < P for b in chunk), '行元素 ≥ q'
        v = 0
        for k in range(na):
            v += chunk[k] * P ** k
        rows.append(v)
    return rows


def row_scale(v, s, na):
    return sum(digit(v, k) * s % P * P ** k for k in range(na))


def row_axpy(a, c, b, na):
    """a − c·b"""
    return sum(((digit(a, k) - c * digit(b, k)) % P) * P ** k for k in range(na))


def leading_idx(v, na):
    for k in range(na - 1, -1, -1):
        if digit(v, k):
            return k
    return -1


def rref_fq(rows, na):
    """镜像 GaussJordanEliminationFq"""
    data = list(rows)
    size = len(data)
    rank = 0
    cur = size - 1
    pc = na - 1
    while cur >= 0 and pc >= 0:
        piv = None
        for r in range(cur, -1, -1):
            if digit(data[r], pc):
                piv = r
                break
        if piv is None:
            pc -= 1
            continue
        data[cur], data[piv] = data[piv], data[cur]
        p = digit(data[cur], pc)
        if p != 1:
            data[cur] = row_scale(data[cur], modinv(p), na)
        for r in range(size):
            if r != cur:
                c = digit(data[r], pc)
                if c:
                    data[r] = row_axpy(data[r], c, data[cur], na)
        rank += 1
        cur -= 1
        pc -= 1
    return data, rank


def is_canonical_rref_fq(rows, na):
    r1, rank = rref_fq(rows, na)
    r2, _ = rref_fq(r1, na)
    return r1 == r2 and r1 == list(rows) and rank == len(rows) and all(rows)


def gfq_rank(rows):
    """F_q 上矩阵的秩(rows = 行的列表, 每行是域元素列表); 可选 threshold: 秩一旦达到即返回"""
    mat = [list(r) for r in rows]
    ncols = len(mat[0]) if mat else 0
    rank = 0
    for col in range(ncols):
        piv = None
        for i in range(rank, len(mat)):
            if mat[i][col] % P:
                piv = i
                break
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        inv = modinv(mat[rank][col])
        mat[rank] = [x * inv % P for x in mat[rank]]
        for i in range(len(mat)):
            if i != rank and mat[i][col]:
                f = mat[i][col]
                mat[i] = [(a - f * b) % P for a, b in zip(mat[i], mat[rank])]
        rank += 1
        if rank == len(mat):
            break
    return rank


# ---------------------------------------------------------------------------
# 张量
# ---------------------------------------------------------------------------

def apply_constraints_fq(tensor, rows, na, nb, nc):
    """镜像 ApplyConstraintsToTensor 的 F_q 支路"""
    res = [[list(sl) for sl in plane] for plane in tensor]
    for row in rows:
        if row == 0:
            continue
        pivot = leading_idx(row, na)
        assert digit(row, pivot) == 1, '主元未归一, 输入不是规范 RREF'
        for i in range(na):
            if i == pivot:
                continue
            c = digit(row, i)
            if c == 0:
                continue
            for j in range(nb):
                for k in range(nc):
                    res[i][j][k] = (res[i][j][k] - c * res[pivot][j][k]) % P
        for j in range(nb):
            for k in range(nc):
                res[pivot][j][k] = 0
    return res


def cyclic(t, na, nb, nc):
    """镜像 CyclicTranspose: result[j][k][i] = t[i][j][k]"""
    return [[[t[i][j][k] for i in range(na)] for k in range(nc)] for j in range(nb)]


def flatten_a_rank(t, na, nb, nc, target=INF):
    return gfq_rank_threshold([[t[a][j][k] for j in range(nb) for k in range(nc)]
                               for a in range(na)], target)


def gfq_rank_threshold(rows, target=INF):
    mat = [list(r) for r in rows]
    ncols = len(mat[0]) if mat else 0
    rank = 0
    for col in range(ncols):
        piv = None
        for i in range(rank, len(mat)):
            if mat[i][col] % P:
                piv = i
                break
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        inv = modinv(mat[rank][col])
        mat[rank] = [x * inv % P for x in mat[rank]]
        for i in range(rank + 1, len(mat)):  # 仅向下消 enough for rank
            if mat[i][col]:
                f = mat[i][col]
                mat[i] = [(a - f * b) % P for a, b in zip(mat[i], mat[rank])]
        rank += 1
        if rank == len(mat) or rank >= target:
            break
    return rank


def rank_lower_bound_flatten_fq(t, na, nb, nc, target):
    """镜像 RankLowerBoundFlatten: B 位 → C 位 → A 位, target 短路"""
    t1 = cyclic(t, na, nb, nc)
    r1 = flatten_a_rank(t1, nb, nc, na, target)
    if r1 >= target:
        return r1
    t2 = cyclic(t1, nb, nc, na)
    r2 = flatten_a_rank(t2, nc, na, nb, target)
    if r2 >= target:
        return r2
    r0 = flatten_a_rank(t, na, nb, nc, target)
    return max(r0, r1, r2)


# ---------------------------------------------------------------------------
# ★ forced(Hopcroft–Kerr 引理 2)
# ---------------------------------------------------------------------------

def forced_classify(tensor, na, nb, nc):
    """返回 (r1_flat, r1_slices, r2p): r1_flat = 展平的强制行(用于独立性), r2p = 其余非零切片"""
    r1_flat, r1_slices, r2p = [], [], []
    r1_count = 0
    for i in range(na):
        rk = gfq_rank(tensor[i])
        if rk == 0:
            continue
        if rk == 1:
            r1_count += 1
            cand = [tensor[i][j][k] for j in range(nb) for k in range(nc)]
            if gfq_rank(r1_flat + [cand]) == len(r1_flat) + 1:
                r1_flat.append(cand)
                r1_slices.append(tensor[i])
            else:
                r2p.append(tensor[i])
        else:
            r2p.append(tensor[i])
    return r1_flat, r1_slices, r2p, r1_count


def forced_product_a_fq(tensor, na, nb, nc):
    """镜像 RankLowerBoundForcedProductA 的 q 进制支路(known = 0, 预算 = 64)。
    返回 (bound, bit_width, num_iterations); bound = None 表示枚举过大需 C 内核。"""
    r1_flat, r1_slices, r2p, r1_count = forced_classify(tensor, na, nb, nc)
    if r1_count == 0:
        return 0, 0, 0
    r1_bc_rows = len(r1_flat)
    bit_width = len(r2p) * r1_bc_rows
    if P ** bit_width > 2 ** 64:
        return 0, bit_width, 0  # uint64 溢出取消
    num_iterations = P ** bit_width
    if num_iterations > PY_ITER_CAP:
        return None, bit_width, num_iterations
    local_min = INF
    zero = [[0] * nc for _ in range(nb)]
    for t in range(num_iterations):
        scrambled = (t * 73074167) % num_iterations
        tensor_t = [[list(r) for r in s] for s in r2p] + \
                   [[list(r) for r in zero] for _ in range(na - len(r2p))]
        v = scrambled
        for bit_idx in range(bit_width):
            d = v % P
            v //= P
            if d == 0:
                continue
            r1_idx = bit_idx % r1_bc_rows
            i = bit_idx // r1_bc_rows
            for j in range(nb):
                for k in range(nc):
                    tensor_t[i][j][k] = (tensor_t[i][j][k] + d * r1_flat[r1_idx][j * nc + k]) % P
        remaining = rank_lower_bound_flatten_fq(tensor_t, na, nb, nc, local_min - r1_bc_rows)
        local_min = min(local_min, r1_bc_rows + remaining)
    return local_min, bit_width, num_iterations


def bt_via_c(base_rows, claim, proof, group_map, orbit_index=None, helper=BT_HELPER, src=BT_HELPER_SRC):
    """回溯证明的独立重放内核(镜像 make_backtracking_verifier_fq 的逐条断言, 用 C 写以免 Python 逐节点重放过慢)。
    轨道表 = 到此为止已核对的所有轨道规范形 → 界。返回 (ok, nodes, leaves, reason)。"""
    if os.path.exists(src) and (not os.path.exists(helper) or os.path.getmtime(helper) < os.path.getmtime(src)):
        subprocess.run(["cc", "-O2", "-o", helper, src], check=True)
    lines = [f"{P} {NA}", f"{len(base_rows)} {' '.join(map(str, base_rows))}".rstrip(), str(claim), str(len(proof['sizes']))]
    for s, m, q, st in zip(proof['sizes'], proof['masks'], proof['queries'], proof['stores']):
        lines.append(f"{s} {m} {q} {st}")
    lines.append(str(len(group_map)))
    for key, b in group_map.items():
        lines.append(f"{len(key)} {' '.join(map(str, key))} {b}".replace('  ', ' '))
    inp = "\n".join(lines) + "\n"
    out = subprocess.run([helper], input=inp, capture_output=True, text=True, check=True)
    # 输出 "bt ok <0|1> nodes <n> leaves <k> reason <可含空格的文本>": 按字段名取, 不数 token
    toks = out.stdout.split()
    assert len(toks) >= 8 and toks[0] == 'bt' and toks[1] == 'ok' and toks[3] == 'nodes' \
        and toks[5] == 'leaves' and toks[7] == 'reason', out.stdout
    return int(toks[2]) == 1, int(toks[4]), int(toks[6]), out.stdout[out.stdout.index('reason ') + 7:].strip()


def forced_via_c(rows, projection, claim, helper=C_HELPER):
    """大枚举: 调独立 C 内核。输入 P, 投影位, 约束行数与各行(基 P 整数), 声明。
    内核输出 "computed <界> bit_width <bw> iterations <n> claim_ok <0|1>"——按字段名取 computed,
    不能取末尾 token(那是 claim_ok 标志; 2026-11-27 曾因此把 F₃ 的 9 读成 1)。"""
    inp = f"{P} {projection} {len(rows)} {' '.join(map(str, rows))} {claim}\n"
    out = subprocess.run([helper], input=inp, capture_output=True, text=True, check=True)
    toks = out.stdout.split()
    assert len(toks) == 8 and toks[0] == 'computed' and toks[2] == 'bit_width', out.stdout
    computed = int(toks[1])
    assert computed >= claim or toks[7] == '0', f"内核 claim_ok 与 computed={computed} 不一致"
    return computed


# ---------------------------------------------------------------------------
# ★ 对称群(GL(N0,P) × GL(N1,P) ⋊ C₂): 矩阵 = 基 P 打包的 9 位整数, 位 (i*3+j) = (i,j)
# ---------------------------------------------------------------------------

def mdigit(m, i, j):
    return (m // P ** (i * 3 + j)) % P


def mat_mul_fq(a, b):
    out = 0
    for i in range(3):
        for j in range(3):
            acc = 0
            for k in range(3):
                acc = (acc + mdigit(a, i, k) * mdigit(b, k, j)) % P
            out += acc * P ** (i * 3 + j)
    return out


def mat_t_fq(a):
    out = 0
    for i in range(3):
        for j in range(3):
            out += mdigit(a, i, j) * P ** (j * 3 + i)
    return out


def mat_inv_fq(a):
    rows = [[mdigit(a, i, j) for j in range(3)] for i in range(3)]
    inv = [[1 if i == j else 0 for j in range(3)] for i in range(3)]
    for col in range(3):
        piv = next((r for r in range(col, 3) if rows[r][col]), None)
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        inv[col], inv[piv] = inv[piv], inv[col]
        s = modinv(rows[col][col])
        rows[col] = [x * s % P for x in rows[col]]
        inv[col] = [x * s % P for x in inv[col]]
        for r in range(3):
            if r != col and rows[r][col]:
                f = rows[r][col]
                rows[r] = [(x - f * y) % P for x, y in zip(rows[r], rows[col])]
                inv[r] = [(x - f * y) % P for x, y in zip(inv[r], inv[col])]
    out = 0
    for i in range(3):
        for j in range(3):
            out += inv[i][j] * P ** (i * 3 + j)
    return out


_GL_CACHE = {}


def gl_set():
    if P not in _GL_CACHE:
        _GL_CACHE[P] = frozenset(m for m in range(P ** 9) if mat_inv_fq(m) is not None)
    return _GL_CACHE[P]


def row_to_mat(v):
    """约束行(Σ_k d_k P^k) ↔ 矩阵(位 (i*3+j) = d_{i*3+j}): 两种打包的下标顺序相同"""
    return v


def query_apply_fq(v, q_l, q_t):
    m = mat_t_fq(v) if q_t else v
    return mat_mul_fq(q_l, m)


def store_apply_inverse_fq(v, s_r):
    return mat_mul_fq(v, mat_inv_fq(s_r))


def canonical_from_witness_fq(extended_rows, raw_query, raw_store):
    q_l = raw_query & 0xFFFF
    q_t = (raw_query >> 16) & 0xFFFF
    s_r = raw_store  # StoreElem 是完整 uint32(矩阵数据)
    gl = gl_set()
    assert q_l in gl and q_t in (0, 1) and s_r in gl, '见证元素不在对称群里'
    image = [store_apply_inverse_fq(query_apply_fq(v, q_l, q_t), s_r) for v in extended_rows]
    r1, rank = rref_fq(image, NA)
    return tuple(r1[len(r1) - rank:])


# ---------------------------------------------------------------------------
# ★ backtracking 重放
# ---------------------------------------------------------------------------

def build_minimal_fq(base_rows):
    base_pivots = [leading_idx(r, NA) for r in base_rows if r]
    minimal = []
    for v in range(1, P ** NA):
        ld = leading_idx(v, NA)
        if digit(v, ld) != 1:
            continue  # LeadingNonzero ≠ One
        if any(digit(v, p) for p in base_pivots):
            continue
        minimal.append(v)
    assert minimal, '极小约束集为空'
    return minimal


def make_backtracking_verifier_fq(base_rows, claim, proof, group_map, orbit_index=None):
    minimal = build_minimal_fq(base_rows)

    def dfs_verify(max_constraint_idx, dfs_constraints, proof_index):
        pi = proof_index[0]
        assert pi < len(proof['sizes']), '轨迹超出证明长度'
        p_dfs_size = proof['sizes'][pi]
        max_depth = claim - 1
        assert len(dfs_constraints) <= p_dfs_size, 'dfs 深度超过记录'
        if len(dfs_constraints) == p_dfs_size:
            mask = proof['masks'][pi]
            assert p_dfs_size > 0
            assert mask & ~((1 << p_dfs_size) - 1) == 0, 'mask 选到路径之外'
            assert mask & (1 << (p_dfs_size - 1)), 'mask 必须选最新路径项'
            extended = list(base_rows) + [dfs_constraints[i] for i in range(len(dfs_constraints))
                                          if (mask >> i) & 1]
            assert len(extended) > len(base_rows)
            canonical = canonical_from_witness_fq(extended, proof['queries'][pi], proof['stores'][pi])
            b = group_map.get(canonical)
            if b is None:
                raise AssertionError(f'orbit {orbit_index}: backtracking 叶子 canonical 不在 map')
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
# 主流程(镜像 VerifyRankLowerBound 的维数扫描)
# ---------------------------------------------------------------------------

def main(argv):
    global P
    path = argv[1]
    corrupt = None
    if '--corrupt' in argv:
        corrupt = int(argv[argv.index('--corrupt') + 1])
    cert = base.parse_certificate(path)
    P = cert['characteristic']
    assert cert['extension_degree'] == 1
    na, nb, nc = cert['na'], cert['nb'], cert['nc']
    print(f"problem={cert['problem_name']} char={P} dims=({na},{nb},{nc})")
    assert (na, nb, nc) == (9, 9, 9)
    base_tensor = base.build_mul_tensor(3, 3, 3)

    orbits = cert['orbits']
    for o in orbits:
        o['rows'] = rows_from_bytes_fq(b''.join(o['raw_rows']), na)
        o['dim'] = len(o['rows'])
        if o['rank_lower_bound'] is None:
            o['rank_lower_bound'] = 0
        if corrupt is not None and o['index'] == corrupt:
            o['rank_lower_bound'] += 7
    from collections import Counter
    for (d, k), c in sorted(Counter((o['dim'], o['kind']) for o in orbits).items()):
        print(f"  dim={d} {k:14s} count={c}")

    archive = None
    if any(o['kind'] == 'backtracking' for o in orbits):
        archive_path = path
        for suffix in ('.pb.txt.gz', '.pb.gz', '.pb.txt', '.pb'):
            if archive_path.endswith(suffix):
                archive_path = archive_path[:-len(suffix)] + '.btp'
                break
        archive = base.load_btp(archive_path)
        assert len(archive) == len(orbits)

    group_map = {}
    counts = Counter()
    forced_stats = Counter()
    bt_stats = Counter()
    for dim in range(na, -1, -1):
        bucket = [o for o in orbits if o['dim'] == dim]
        if not bucket:
            continue
        for o in bucket:
            kind = o['kind']
            rows = o['rows']
            claim = o['rank_lower_bound']
            if rows:
                assert is_canonical_rref_fq(rows, na), f"orbit {o['index']} 不是规范 RREF"
            if kind == 'none':
                assert claim <= 0
                counts[kind] += 1
                continue
            if kind == 'flatten':
                tensor = apply_constraints_fq(base_tensor, rows, na, nb, nc)
                computed = rank_lower_bound_flatten_fq(tensor, na, nb, nc, claim)
                assert computed >= claim, f"orbit {o['index']}: flatten {computed} < {claim}"
            elif kind == 'forced':
                # 记录的投影位: 0 = A, 1 = B(一次循环转置), 2 = C(两次)
                proj = o['projection_type']
                assert proj in (0, 1, 2), proj
                if os.path.exists(C_HELPER):
                    computed = forced_via_c(rows, proj, claim)
                    forced_stats['c'] += 1
                else:
                    tensor = apply_constraints_fq(base_tensor, rows, na, nb, nc)
                    if proj == 1:
                        tensor = cyclic(tensor, na, nb, nc)
                    elif proj == 2:
                        tensor = cyclic(cyclic(tensor, na, nb, nc), nb, nc, na)
                    bound, bw, iters = forced_product_a_fq(tensor, 9, 9, 9)
                    assert bound is not None, \
                        f"orbit {o['index']}: forced 枚举 3^{bw} 过大, 需编译 C 内核 {C_HELPER}"
                    computed = bound
                    forced_stats['py'] += 1
                assert computed >= claim, f"orbit {o['index']}: forced {computed} < {claim}"
            elif kind == 'degenerate':
                raw_extra = o['extra_constraint']
                assert raw_extra is not None and 0 <= raw_extra < P ** na
                extended = rows + [raw_extra]
                r2, rank2 = rref_fq(extended, na)
                assert rank2 == len(extended), 'degenerate: 加行后线性相关'
                canonical = canonical_from_witness_fq(extended, o['query_elem'], o['store_elem'])
                b = group_map.get(canonical)
                assert b is not None, f"orbit {o['index']}: degenerate 规范轨道不在 map"
                assert b >= claim, f"orbit {o['index']}: degenerate {b} < {claim}"
            elif kind == 'backtracking':
                proof = base.decode_proof(archive[o['index']])
                if os.path.exists(BT_HELPER_SRC) and not os.environ.get('WANG_BT_PY'):
                    # 独立 C 内核重放(纯 Python 逐节点重放对 1e7 步的搜索太慢; WANG_BT_PY=1 强制走 Python)
                    ok, nodes, leaves, reason = bt_via_c(rows, claim, proof, group_map, orbit_index=o['index'])
                    assert ok, f"orbit {o['index']}: backtracking kernel rejected: {reason}"
                    bt_stats['nodes'] += nodes
                    bt_stats['c'] += 1
                else:
                    make_backtracking_verifier_fq(rows, claim, proof, group_map,
                                                  orbit_index=o['index'])()
                    bt_stats['py'] += 1
            counts[kind] += 1
        for o in bucket:
            key = tuple(o['rows'])
            assert key not in group_map, f"orbit {o['index']} 重复轨道代表"
            group_map[key] = o['rank_lower_bound']
        print(f"  dim={dim}: 核对 {len(bucket)} 轨道, 累计 map={len(group_map)}", flush=True)

    assert len(group_map) == len(orbits)
    last = orbits[-1]
    assert last['rows'] == [], '最后轨道必须是无约束张量'
    result = last['rank_lower_bound']
    print(f"UNCONSTRAINED TENSOR RANK LOWER BOUND: {result}")
    print(f"OK. 已核对 {len(orbits)} 轨道: {dict(counts)}; forced 路径 {dict(forced_stats)}; backtracking 路径 {dict(bt_stats)}")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
