#!/usr/bin/env python3
"""NSE 四步全状态 golden 生成器（M3·NSE 卷·消费接线）。

单源：FML `src/Sovereign/Application/Problems/NavierStokes/NSEOnT6.agda`
的 nsStep 语义（§1 载体 Torus6=(Z/3)⁶；§2 shift3/shiftAt/shiftF/diffF/div；
§5 grad；§6 nsStep v = v +F grad(div v)）。

初态：cpp `T6Grid::init_random(seed=42)` 同款 LCG
  （s = s·6364136223846793005 + 1442695040888963407，v = (s>>32)%3），
  4374 项按 i 主序（comp[i·729+x]）铺入——三语言可复现。

产物（写入 sov-math rust，由 sov-core 测试消费）：
  <math>/rust/sov-math/sov-core/src/l2_nse_golden.rs
  —— GOLDEN_SEED + GOLDEN_S1..S4（四步全状态，各 4374 trit）

配对关系：零初态的不动点定理在 FML `NSEOnT6Golden.agda`（§1/§3）；
非平凡初态（本文件 seeded）的四步动力学由此 JSON 化/Rust 化冻结，
供 rust `formalised_step` 逐 trit 对拍。⚠ 校验编码，非数学证明。

用法：
  python3 scripts/gen-nse-golden.py --math /home/yanli/work/math
"""
import argparse
import pathlib

MASK64 = (1 << 64) - 1
NSE_N = 729
NSE_COMPONENTS = 6


def shift_at(i, x):
    base = 3 ** i
    digit = (x // base) % 3
    return x + ((digit + 1) % 3) * base - digit * base


def tadd(a, b):
    return (a + b) % 3


def tneg(a):
    return (3 - a + 3) % 3


def formalised_step(comp):
    """FML nsStep（NSEOnT6 §6：nsStep v = v +F grad (div v)），
    与 rust `l2_nse::formalised_step` 逐条同构。"""
    assert len(comp) == NSE_N * NSE_COMPONENTS

    def at(c, x, i):
        return c[i * NSE_N + x]

    def diff_f(c, axis, i, x):
        return tadd(at(c, shift_at(axis, x), i), tneg(at(c, x, i)))

    d = [0] * NSE_N
    for x in range(NSE_N):
        acc = 0
        for i in range(NSE_COMPONENTS):
            acc = tadd(acc, diff_f(comp, i % 3, i, x))
        d[x] = acc

    nxt = list(comp)
    for i in range(NSE_COMPONENTS):
        axis = i % 3
        for x in range(NSE_N):
            grad_d = tadd(d[shift_at(axis, x)], tneg(d[x]))
            nxt[i * NSE_N + x] = tadd(comp[i * NSE_N + x], grad_d)
    return nxt


def seed_state(seed=42):
    s = seed
    comp = [0] * (NSE_N * NSE_COMPONENTS)
    for k in range(NSE_N * NSE_COMPONENTS):
        s = (s * 6364136223846793005 + 1442695040888963407) & MASK64
        comp[k] = (s >> 32) % 3
    return comp


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--math', required=True, help='math 仓根目录')
    args = ap.parse_args()

    seed = seed_state(42)
    states = [list(seed)]
    for _ in range(4):
        states.append(formalised_step(states[-1]))
    s1, s2, s3, s4 = states[1], states[2], states[3], states[4]

    def fmt(name, vals):
        body = ',\n    '.join(
            ', '.join(str(v) for v in vals[o:o + 100])
            for o in range(0, len(vals), 100))
        return f'pub const {name}: [u8; {len(vals)}] = [\n    {body},\n];\n'

    header = (
        '// ⚠ 生成文件——勿手改（FML scripts/gen-nse-golden.py）。\n'
        '// 单源：FML NSEOnT6.agda nsStep 语义（v +F grad (div v)），\n'
        '// 初态 = cpp T6Grid::init_random(seed=42) 同款 LCG，i 主序铺入。\n'
        '// 配套 FML pin：NSEOnT6Golden.agda（零场不动点 ×6 / 四步推论）。\n'
        '// ⚠ 校验编码（全状态数值冻结），非数学证明。\n\n')

    out = (header
           + fmt('GOLDEN_SEED', seed)
           + '\n' + fmt('GOLDEN_S1', s1)
           + '\n' + fmt('GOLDEN_S2', s2)
           + '\n' + fmt('GOLDEN_S3', s3)
           + '\n' + fmt('GOLDEN_S4', s4))

    dst = pathlib.Path(args.math) / 'rust' / 'sov-math' / 'sov-core' / 'src' / 'l2_nse_golden.rs'
    dst.write_text(out, encoding='utf-8')
    print(f'written: {dst} ({len(out)} bytes)')


if __name__ == '__main__':
    main()
