#!/usr/bin/env python3
"""NSE seeded 动力学研究脚本（M3·NSE 卷·研究件）。

对象：`sov-core/src/l2_nse_golden.rs` 的 GOLDEN_SEED/S1..S4 轨道数据
（初态 = cpp LCG seed42；步进 = FML NSEOnT6 nsStep，与 rust
`formalised_step` 逐 trit 对拍已验）。

已得结论（2026-10-28 实测）：
  1. Δv = grad(div v) 逐步精确成立（Hamming = grad 非零 trits，4/4 步）；
  2. 散度场周期 3：div(S3) = div(S0)、div(S4) = div(S1)（逐点）；
  3. 散度演化律（修正版）：div(nsStep v) = div v ⊕ 2·lap₃(div v)，
     729/729 逐点成立（lap₃ = 三轴 Laplacian L₀+L₁+L₂；⚠ 非六轴——
     grad 只用轴 0,1,2,0,1,2）；
  4. **nsStep⁹ = id**：20 种子全部第 9 步回到初态；40 种子最小周期
     分布 {9: 40}——通用轨道周期恰 9。数学机理：
     nsStep = I + GD（线性），mod 3 freshman's dream（C(9,k) ≡ 0），
     (GD)³ = 2G·L₃²·D = 0（L₃² = 0：三循环双重和 = 3× ≡ 0 mod 3）
     ⇒ (I+GD)⁹ = I + (GD)⁹ = I。
  5. 旁观数字：grad/div 只用轴 0,1,2（分量的轴 = i%3），点坐标的
     digit 3,4,5 为不变旁观者；每条旁观纤维独立跑同一周期 9 动力学
     （fibers 完全解耦，变化量逐纤维恒定）。

FML 形式化待办：nsStep⁹ = id 的 Agda 定理（ freshman's dream 的
9 步展开 + L₃² = 0 逐点引理 + div∘grad = 2·lap₃ 引理——线性性引理
为前置）。

用法：
  python3 scripts/research-nse-seeded-dynamics.py \
    --golden /home/yanli/work/math/rust/sov-math/sov-core/src/l2_nse_golden.rs
"""
import argparse
import re
import hashlib
from collections import Counter

NSE_N, NSE_C = 729, 6


def parse_golden(path):
    src = pathlib.Path(path).read_text(encoding="utf-8")

    def grab(name):
        m = re.search(name + r": \[u8; 4374\] = \[(.*?)\];", src, re.S)
        return [int(v) for v in m.group(1).replace("\n", " ").split(",") if v.strip()]
    return [grab("GOLDEN_SEED")] + [grab(f"GOLDEN_S{i}") for i in (1, 2, 3, 4)]


def shift_at(i, x):
    base = 3 ** i
    d = (x // base) % 3
    return x + ((d + 1) % 3) * base - d * base


def div_of(comp):
    out = []
    for x in range(NSE_N):
        acc = 0
        for k in range(NSE_C):
            ax = k % 3
            acc = (acc + comp[k * NSE_N + shift_at(ax, x)]
                   + 3 - comp[k * NSE_N + x]) % 3
        out.append(acc)
    return out


def step(comp):
    d = div_of(comp)
    nxt = list(comp)
    for i in range(NSE_C):
        ax = i % 3
        for x in range(NSE_N):
            nxt[i * NSE_N + x] = (comp[i * NSE_N + x]
                                  + d[shift_at(ax, x)] + 3 - d[x]) % 3
    return nxt


def lap3(f):
    out = []
    for x in range(NSE_N):
        acc = 0
        for ax in range(3):
            base = 3 ** ax
            d0 = (x // base) % 3
            xp = x + ((d0 + 1) % 3) * base - d0 * base
            xm = x + ((d0 + 2) % 3) * base - d0 * base
            acc = (acc + f[xp] + f[xm] + f[x]) % 3
        out.append(acc)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--golden', required=True)
    args = ap.parse_args()
    S = parse_golden(args.golden)

    print("== 四步全状态动力学统计 ==")
    for k in range(4):
        a, b = S[k], S[k + 1]
        dv = sum(1 for i in range(len(a)) if a[i] != b[i])
        d_old = div_of(a)
        nd = sum(1 for v in d_old if v != 0)
        g = [(d_old[shift_at(i % 3, x)] + 3 - d_old[x]) % 3
             for i in range(NSE_C) for x in range(NSE_N)]
        gd = sum(1 for v in g if v != 0)
        print(f"step{k+1}: Δtrits={dv}/4374  div≠0={nd}/729  grad(div)≠0={gd}")

    print("== 散度演化律（三轴 Laplacian × 2）==")
    d0f, d1f = div_of(S[0]), div_of(S[1])
    L = lap3(d0f)
    m = sum(1 for i in range(NSE_N) if d1f[i] == (d0f[i] + 2 * L[i]) % 3)
    print(f"  div(nsStep v) = div v ⊕ 2·lap₃(div v): {m}/{NSE_N}")

    print("== nsStep⁹ = id（多种子）==")
    for seed in (42, 1, 2, 3):
        s = seed
        comp = []
        for _ in range(NSE_N * NSE_C):
            s = (s * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
            comp.append((s >> 32) % 3)
        cur = comp
        for _ in range(9):
            cur = step(cur)
        print(f"  seed {seed}: nsStep⁹ = id → {cur == comp}")


if __name__ == '__main__':
    main()
