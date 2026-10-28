#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""research-nse-divgrad.py — NSE 离散动力学数值预检（FML/Agda 形式化前置真值预检）。

四项检验（全部结论以本脚本实际输出为准，不许推断充数；反例完整打印）：
  T1  div∘grad 恒等式（题述形式）:
          div (grad f) x ≡ 2·Σ_{i=0,1,2} f(x+2eᵢ)   (mod 3)
      —— 50 个 LCG 随机场（seed 43..92，各 729 trit）× 全部 729 点。
      右端恰为三轴 x+2eᵢ 之三项和：不含 f(x)、不含 x+eᵢ 项、不是 6 项。
      附加（供 FML 参考、与题述形式分开报告）：修正候选
          div (grad f) x ≡ 2·Σ_{i=0,1,2} [f(x+2eᵢ) + f(x+eᵢ)]   (mod 3)
  T2  lap 两形式逐点相等（mod 3）:
          lap₃ f x = Σ_{i=0,1,2} [f(x+2eᵢ)+f(x+eᵢ)+f(x)]
          Δ   f x = Σ_{i=0,1,2} [f(x+eᵢ)+f(x+2eᵢ)]
      预期相差 3f(x) ≡ 0，应逐点全等。
  T3  旁观数字解耦（三个子检验，分别报告）:
      T3(题述)  S1−S0 逐 trit 差在 x ≡ x' (mod 27) 的点间恒相同（逐分量 k）；
      T3b(同子环面读法)  「digit 3,4,5 相同的点」= 仅 digit 0,1,2 不同的两点
                （同一 27 点低维子环面），S1−S0 在其上恒相同；
      T3c(平移等变·修正候选)  对 digit 3,4,5 的全部 27 个平移 τ：
                nsStep(τ S0) ≡ τ (nsStep S0)（即动力学按高数字纤维解耦）。
      状态链取 golden（seed=42）。
  T4  周期-9 大样本统计: 100 个 LCG seed（1000..1099，各 4374 trit 速度场），
      nsStep 迭代 9 步验证回到初态，并统计最小周期分布。

T0 门禁（定义读法校验）：本脚本独立实现 shiftAt/diffF/div/grad/nsStep/LCG，
并与现成 golden 文件 GOLDEN_SEED/GOLDEN_S1..S4 逐 trit 对拍；T0 不过则
后续一切结论无效（会显式标出）。

定义（与 FML NSEOnT6.agda / scripts/gen-nse-golden.py 逐条同构）：
  Torus6 = (Z/3)⁶ = 729 点，x = Σ aᵢ·3ⁱ，digit i = (x // 3ⁱ) % 3；
  shiftAt i x = digit i 加 1 mod 3；
  diffF i f x = f(shiftAt i x) − f(x) (mod 3)；
  grad f 第 k 分量 = diffF (k%3) f（轴序 0,1,2,0,1,2）；
  div v x = Σ_{k=0..5} diffF (k%3) v_k x (mod 3)；
  nsStep v = v + grad (div v)（逐点 mod 3）；
  LCG: s₀=seed；s ← (s·6364136223846793005 + 1442695040888963407) mod 2⁶⁴；
       值 = (s>>32)%3（先更新后取值）；k 主序铺 comp[k·729+x]。

用法：python3 research-nse-divgrad.py [--golden <l2_nse_golden.rs>]
"""

import argparse
import re
import time
from collections import Counter

# ---------------------------------------------------------------- 常量与 LCG

MASK64 = (1 << 64) - 1
LCG_A = 6364136223846793005
LCG_C = 1442695040888963407
N = 729            # Torus6 点数
NC = 6             # 速度场分量数
GOLDEN_DEFAULT = '/home/yanli/work/math/rust/sov-math/sov-core/src/l2_nse_golden.rs'


def lcg_trits(seed: int, n: int):
    """先更新后取值：s ← (s·A+C) mod 2⁶⁴，值=(s>>32)%3，共 n 个。"""
    s = seed & MASK64
    out = [0] * n
    for j in range(n):
        s = (s * LCG_A + LCG_C) & MASK64
        out[j] = (s >> 32) % 3
    return out


# ---------------------------------------------------------------- Torus6 算子

POW3 = [3 ** i for i in range(6)]


def shift_at(i: int, x: int) -> int:
    base = POW3[i]
    digit = (x // base) % 3
    return x + ((digit + 1) % 3) * base - digit * base


# SHIFT1[i][x] = x+eᵢ（digit i 加 1）；SHIFT2[i][x] = x+2eᵢ（digit i 加 2）
SHIFT1 = [[shift_at(i, x) for x in range(N)] for i in range(3)]
SHIFT2 = [[SHIFT1[i][SHIFT1[i][x]] for x in range(N)] for i in range(3)]


def digits6(x: int):
    return tuple((x // POW3[i]) % 3 for i in range(6))


def grad(f):
    """标量场 f → 6 分量场 g，g[k*N+x] = diffF (k%3) f x。"""
    g = [0] * (NC * N)
    for k in range(NC):
        si = SHIFT1[k % 3]
        base = k * N
        for x in range(N):
            g[base + x] = (f[si[x]] - f[x]) % 3
    return g


def div(v):
    """6 分量速度场 v → 标量场 d，d[x] = Σ_k diffF (k%3) v_k x (mod 3)。"""
    d = [0] * N
    for k in range(NC):
        si = SHIFT1[k % 3]
        base = k * N
        for x in range(N):
            d[x] += v[base + si[x]] - v[base + x]
    return [t % 3 for t in d]


def ns_step(v):
    """nsStep v = v + grad (div v)，逐点 mod 3。"""
    d = div(v)
    g = grad(d)
    return [(a + b) % 3 for a, b in zip(v, g)]


# ---------------------------------------------------------------- golden 解析

GOLDEN_RE = re.compile(
    r'pub const (GOLDEN_SEED|GOLDEN_S[1-4]):\s*\[u8;\s*4374\]\s*=\s*\[([0-9,\s]+?)\];',
    re.S)


def parse_golden(path):
    text = open(path, 'r', encoding='utf-8').read()
    out = {}
    for m in GOLDEN_RE.finditer(text):
        vals = [int(t) for t in m.group(2).split(',') if t.strip()]
        assert len(vals) == NC * N, f'{m.group(1)}: {len(vals)} != 4374'
        out[m.group(1)] = vals
    return out


# ---------------------------------------------------------------- T0 门禁

def check_T0(golden):
    """独立实现 vs golden 文件逐 trit 对拍（seed=42 链）。"""
    print('[T0] 定义读法门禁：独立实现 vs golden 文件（seed=42 链）')
    if not golden:
        print('     SKIP：golden 文件缺失/解析为空——门禁未建立，后续结论无效！')
        return False
    s0 = lcg_trits(42, NC * N)
    ok = True
    m = (s0 == golden.get('GOLDEN_SEED'))
    ok &= m
    print(f'     LCG 重算(seed=42) == GOLDEN_SEED : {"MATCH" if m else "MISMATCH"}'
          + ('' if m else '  ← LCG 读法有误'))
    st = s0
    for step in (1, 2, 3, 4):
        st = ns_step(st)
        m = (st == golden.get(f'GOLDEN_S{step}'))
        ok &= m
        print(f'     nsStep^{step} == GOLDEN_S{step}      : {"MATCH" if m else "MISMATCH"}'
              + ('' if m else '  ← 算子读法有误，以下结论无效'))
    print(f'[T0] 结论: {"PASS" if ok else "FAIL"}')
    return ok


# ---------------------------------------------------------------- T1

def check_T1():
    """div∘grad 恒等式：题述形式 + 修正候选，分别计数。"""
    print('[T1] div∘grad 恒等式（题述形式）: div(grad f) x ≡ 2·Σ_{i=0,1,2} f(x+2eᵢ) (mod 3)')
    print('     右端 = 三轴 x+2eᵢ 三项之和（不含 f(x)、不含 x+eᵢ）')
    total = 50 * N
    fails = 0
    fields_with_ce = 0
    first = None
    corr_fails = 0
    corr_first = None
    for seed in range(43, 93):
        f = lcg_trits(seed, N)
        lhs = div(grad(f))
        field_ce = 0
        for x in range(N):
            rhs_stated = (2 * (f[SHIFT2[0][x]] + f[SHIFT2[1][x]] + f[SHIFT2[2][x]])) % 3
            if lhs[x] != rhs_stated:
                fails += 1
                field_ce += 1
                if first is None:
                    first = (seed, x, lhs[x], rhs_stated)
            rhs_corr = (2 * (f[SHIFT2[0][x]] + f[SHIFT1[0][x]]
                             + f[SHIFT2[1][x]] + f[SHIFT1[1][x]]
                             + f[SHIFT2[2][x]] + f[SHIFT1[2][x]])) % 3
            if lhs[x] != rhs_corr:
                corr_fails += 1
                if corr_first is None:
                    corr_first = (seed, x, lhs[x], rhs_corr)
        if field_ce:
            fields_with_ce += 1
    verdict = 'PASS' if fails == 0 else 'FAIL'
    print(f'     检验点数 = 50 场 × {N} 点 = {total}；反例数 = {fails}；'
          f'含反例的场数 = {fields_with_ce}/50')
    if first:
        seed, x, lv, rv = first
        print(f'     首个反例: seed={seed}, x={x}, digits(a0..a5)={digits6(x)}, '
              f'LHS=div(grad f)[x]={lv}, RHS(题述)={rv}')
    print(f'[T1] 结论（题述形式）: {verdict}')
    print(f'     [T1+] 附加·修正候选 2·Σᵢ[f(x+2eᵢ)+f(x+eᵢ)]: '
          f'反例数 = {corr_fails} → {"PASS" if corr_fails == 0 else "FAIL"}')
    if corr_first:
        seed, x, lv, rv = corr_first
        print(f'     [T1+] 首个反例: seed={seed}, x={x}, digits={digits6(x)}, '
              f'LHS={lv}, RHS(修正)={rv}')
    # T1++：更干净的形式 div(grad f) ≡ 2·lap₃ f（lap₃ 含 f(x) 项，2·3f(x)≡0 抵消）
    lap_fails = 0
    lap_first = None
    for seed in range(43, 93):
        f = lcg_trits(seed, N)
        lhs = div(grad(f))
        for x in range(N):
            lap3 = (f[SHIFT2[0][x]] + f[SHIFT1[0][x]] + f[x]
                    + f[SHIFT2[1][x]] + f[SHIFT1[1][x]] + f[x]
                    + f[SHIFT2[2][x]] + f[SHIFT1[2][x]] + f[x]) % 3
            if lhs[x] != (2 * lap3) % 3:
                lap_fails += 1
                if lap_first is None:
                    lap_first = (seed, x, lhs[x], (2 * lap3) % 3)
    print(f'     [T1++] div(grad f) ≡ 2·lap₃ f: 反例数 = {lap_fails} → '
          f'{"PASS" if lap_fails == 0 else "FAIL"}')
    return fails == 0, corr_fails == 0, first


# ---------------------------------------------------------------- T2

def check_T2():
    """lap 三点式 vs 对式，逐点 mod 3 相等。"""
    print('[T2] lap 形式等价: lap₃ f x = Σᵢ[f(x+2eᵢ)+f(x+eᵢ)+f(x)] '
          'vs Δ f x = Σᵢ[f(x+eᵢ)+f(x+2eᵢ)] (mod 3)')
    total = 50 * N
    fails = 0
    first = None
    for seed in range(43, 93):
        f = lcg_trits(seed, N)
        for x in range(N):
            lap3 = (f[SHIFT2[0][x]] + f[SHIFT1[0][x]] + f[x]
                    + f[SHIFT2[1][x]] + f[SHIFT1[1][x]] + f[x]
                    + f[SHIFT2[2][x]] + f[SHIFT1[2][x]] + f[x]) % 3
            delta = (f[SHIFT1[0][x]] + f[SHIFT2[0][x]]
                     + f[SHIFT1[1][x]] + f[SHIFT2[1][x]]
                     + f[SHIFT1[2][x]] + f[SHIFT2[2][x]]) % 3
            if lap3 != delta:
                fails += 1
                if first is None:
                    first = (seed, x, lap3, delta)
    verdict = 'PASS' if fails == 0 else 'FAIL'
    print(f'     检验点数 = 50 场 × {N} 点 = {total}；反例数 = {fails}')
    if first:
        seed, x, lv, rv = first
        print(f'     首个反例: seed={seed}, x={x}, digits={digits6(x)}, lap₃={lv}, Δ={rv}')
    print(f'[T2] 结论: {verdict}' + ('（差 3f(x) ≡ 0 mod 3，与预期一致）' if fails == 0 else ''))
    return fails == 0, first


# ---------------------------------------------------------------- T3

def translate_high(v, t3, t4, t5):
    """高数字平移 τ：digit3,4,5 分别加 (t3,t4,t5) mod 3，digit0,1,2 不动。"""
    out = list(v)
    for x in range(N):
        a3 = (x // 27) % 3
        a4 = (x // 81) % 3
        a5 = (x // 243) % 3
        xp = x + ((a3 + t3) % 3 - a3) * 27 + ((a4 + t4) % 3 - a4) * 81 \
              + ((a5 + t5) % 3 - a5) * 243
        for k in range(NC):
            out[k * N + xp] = v[k * N + x]
    return out


def check_T3(golden):
    """旁观数字解耦：题述形式 / 同子环面读法 / 高数字平移等变，三者分开报告。"""
    print('[T3] 旁观数字解耦（golden 链 seed=42）')
    if not golden or 'GOLDEN_SEED' not in golden or 'GOLDEN_S1' not in golden:
        print('     SKIP：golden 缺失')
        return False
    s0 = golden['GOLDEN_SEED']
    s1 = golden['GOLDEN_S1']
    d = [[(s1[k * N + x] - s0[k * N + x]) % 3 for x in range(N)] for k in range(NC)]

    # T3（题述）：x ≡ x' (mod 27)（digit 0,1,2 相同）⇒ D[k][x] = D[k][x']
    classes = [[] for _ in range(27)]
    for x in range(N):
        classes[x % 27].append(x)
    mism = 0
    first = None
    for c, members in enumerate(classes):
        rep = members[0]
        for k in range(NC):
            dv = d[k][rep]
            for x in members:
                if d[k][x] != dv:
                    mism += 1
                    if first is None:
                        first = (k, c, rep, x, dv, d[k][x])
    print(f'     [T3 题述] x≡x′(mod 27)（digit0,1,2 相同，异子环面）: '
          f'检验 = 27类×6分量×27点 = {27 * NC * 27}；不一致数 = {mism}')
    if first:
        k, c, rep, x, dv, dx = first
        print(f'     [T3 题述] 首个反例: k={k}, class(mod27)={c}, '
              f'rep={rep}(digits={digits6(rep)}), x={x}(digits={digits6(x)}), '
              f'D[rep]={dv}, D[x]={dx}')
    print(f'     [T3 题述] 结论: {"PASS" if mism == 0 else "FAIL"}')

    # T3b（同子环面读法）：digit 3,4,5 相同（仅 digit0,1,2 不同）⇒ D[k][x] = D[k][x']
    mism_b = 0
    first_b = None
    for base in range(0, N, 27):          # base = a3·27 + a4·81 + a5·243（每子环面代表）
        for k in range(NC):
            dv = d[k][base]
            for t in range(27):           # t 仅触 digit0,1,2
                x = base + t
                if d[k][x] != dv:
                    mism_b += 1
                    if first_b is None:
                        first_b = (k, base, x, dv, d[k][x])
    print(f'     [T3b 同子环面] digit3,4,5 相同（27 纤维×6 分量×27 点）: '
          f'检验 = {27 * NC * 27}；不一致数 = {mism_b}')
    if first_b:
        k, base, x, dv, dx = first_b
        print(f'     [T3b] 首个反例: k={k}, base={base}(digits={digits6(base)}), '
              f'x={x}(digits={digits6(x)}), D[base]={dv}, D[x]={dx}')
    print(f'     [T3b] 结论: {"PASS" if mism_b == 0 else "FAIL"}')

    # T3c（高数字平移等变·修正候选）：nsStep(τ S0) ≡ τ(nsStep S0)，τ 遍历 digit3,4,5 平移
    step0 = ns_step(s0)
    mism_c = 0
    first_c = None
    n_checks_c = 0
    for t3 in range(3):
        for t4 in range(3):
            for t5 in range(3):
                lhs = ns_step(translate_high(s0, t3, t4, t5))
                rhs = translate_high(step0, t3, t4, t5)
                for idx in range(NC * N):
                    n_checks_c += 1
                    if lhs[idx] != rhs[idx]:
                        mism_c += 1
                        if first_c is None:
                            first_c = ((t3, t4, t5), idx % N, lhs[idx], rhs[idx])
    print(f'     [T3c 平移等变] nsStep(τS0)≡τ(nsStep S0), τ∈{27} 个高数字平移: '
          f'检验 = {n_checks_c}；不一致数 = {mism_c}')
    if first_c:
        tt, x, lv, rv = first_c
        print(f'     [T3c] 首个反例: τ(t3,t4,t5)={tt}, x={x}(digits={digits6(x)}), '
              f'LHS={lv}, RHS={rv}')
    print(f'     [T3c] 结论: {"PASS" if mism_c == 0 else "FAIL"}'
          f'（动力学按 digit3,4,5 纤维解耦的真命题）')
    return mism == 0, mism_b == 0, mism_c == 0


# ---------------------------------------------------------------- T4

def check_T4():
    """100 个 seed 的 9 步回归与最小周期分布。"""
    print('[T4] 周期-9 大样本统计: seeds 1000..1099，各 4374 trit 速度场')
    dist = Counter()
    no_return = []
    sub9 = []
    for seed in range(1000, 1100):
        v0 = lcg_trits(seed, NC * N)
        v = v0
        period = None
        for t in range(1, 10):
            v = ns_step(v)
            if v == v0:
                period = t
                break
        if period is None:
            no_return.append(seed)
            dist['>9'] += 1
        else:
            dist[period] += 1
            if period != 9:
                sub9.append((seed, period))
    n9 = dist.get(9, 0)
    verdict = 'PASS' if not no_return else 'FAIL'
    print(f'     场数 = 100；9 步回归初态 = {n9}/100；最小周期分布 = '
          f'{{{", ".join(f"{k}: {v}" for k, v in sorted(dist.items(), key=str))}}}')
    if sub9:
        print(f'     周期≠9 的场: {sub9}')
    if no_return:
        print(f'     9 步未回归的 seed: {no_return}  ← 破坏周期-9')
    print(f'[T4] 结论: {verdict}（{"全部在 9 步内首次回归" if not no_return else "存在未回归场"}）')
    return not no_return, dist, sub9


# ---------------------------------------------------------------- 主流程

def main():
    ap = argparse.ArgumentParser(description='NSE 离散动力学数值预检')
    ap.add_argument('--golden', default=GOLDEN_DEFAULT, help='l2_nse_golden.rs 路径')
    args = ap.parse_args()
    t0 = time.time()
    try:
        golden = parse_golden(args.golden)
    except (OSError, AssertionError, ValueError) as e:
        print(f'golden 解析失败: {e}')
        golden = {}
    gate = check_T0(golden)
    print()
    t1_ok, t1c_ok, t1_first = check_T1()
    print()
    t2_ok, t2_first = check_T2()
    print()
    t3_ok, t3b_ok, t3c_ok = check_T3(golden)
    print()
    t4_ok, t4_dist, t4_sub = check_T4()
    print()
    print('=' * 72)
    print('SUMMARY（供 FML 形式化选题参考；以各段详细输出为准）')
    print(f'  T0 门禁(定义读法 vs golden): {"PASS" if gate else "FAIL"}')
    print(f'  T1 div∘grad 题述形式      : '
          f'{"PASS" if t1_ok else "FAIL"}'
          + (f'  首反例 seed/x/LHS/RHS = {t1_first}' if t1_first else ''))
    print(f'  T1+ 修正候选 2Σ[f(x+2eᵢ)+f(x+eᵢ)] : {"PASS" if t1c_ok else "FAIL"}'
          f'（等价于 2·lap₃，见 T1++）')
    print(f'  T2 lap 两形式等价         : {"PASS" if t2_ok else "FAIL"}')
    print(f'  T3 旁观数字解耦·题述(x≡x′ mod 27): {"PASS" if t3_ok else "FAIL"}')
    print(f'  T3b 同子环面读法          : {"PASS" if t3b_ok else "FAIL"}')
    print(f'  T3c 高数字平移等变(修正候选): {"PASS" if t3c_ok else "FAIL"}')
    print(f'  T4 周期-9（100 seeds）    : {"PASS" if t4_ok else "FAIL"}'
          f'  分布={dict(sorted(t4_dist.items(), key=str))}'
          + (f'  周期≠9: {t4_sub}' if t4_sub else ''))
    print(f'(总耗时 {time.time() - t0:.2f}s)')


if __name__ == '__main__':
    main()
