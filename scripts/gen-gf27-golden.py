#!/usr/bin/env python3
"""GF(27) golden 表生成器（M1 试点）。

单源：`src/Sovereign/Algebra/FieldTower/GF27.agda` 的两张显式表
  · toGF27   pow0..pow25   → 26 组 (t0,t1,t2) 坐标
  · fromGF27 (t0,t1,t2)    → 27 子句（含零元折到 pow0 的约定）

产物（写入 trha，由 trha 测试消费）：
  <trha>/test/golden/gf27.json      —— 单源 golden（测试直接读）
配套（写入本仓，spec freeze）：
  <这里>/src/Sovereign/Algebra/FieldTower/GF27Golden.agda
  —— 校验编码（pin）：refl 钉住两张表与解析结果一致。⚠ 不是数学证明。

用法：
  python3 scripts/gen-gf27-golden.py --trha /home/yanli/work/trha
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
GF27 = ROOT / 'src/Sovereign/Algebra/FieldTower/GF27.agda'
PIN = ROOT / 'src/Sovereign/Algebra/FieldTower/GF27Golden.agda'
TRIT = {'₀': 0, '₁': 1, '₂': 2}
WEIGHTS = [1, 3, 9]

TO_RE = re.compile(r'^toGF27\s+(pow\d+)\s*=\s*T([₀₁₂])\s*,\s*T([₀₁₂])\s*,\s*T([₀₁₂])\s*$')
FROM_RE = re.compile(r'^fromGF27\s*\(T([₀₁₂])\s*,\s*T([₀₁₂])\s*,\s*T([₀₁₂])\)\s*=\s*(pow\d+)\s*(?:--\s*(.*))?$')


def parse():
    to_table, from_table = {}, []
    for ln in GF27.open(encoding='utf-8'):
        m = TO_RE.match(ln.strip())
        if m:
            k = int(m.group(1)[3:])
            to_table[k] = [TRIT[m.group(2)], TRIT[m.group(3)], TRIT[m.group(4)]]
            continue
        m = FROM_RE.match(ln.strip())
        if m:
            coords = [TRIT[m.group(1)], TRIT[m.group(2)], TRIT[m.group(3)]]
            from_table.append({'coords': coords,
                               'pow': int(m.group(4)[3:]),
                               'note': (m.group(5) or '').strip()})
    if len(to_table) != 26:
        raise SystemExit(f'toGF27 解析出 {len(to_table)} 条（应 26）')
    if len(from_table) != 27:
        raise SystemExit(f'fromGF27 解析出 {len(from_table)} 条（应 27）')
    return to_table, from_table


def build(to_table, from_table):
    star = []
    enc_of = {}
    for k in range(26):
        c = to_table[k]
        enc = c[0] * WEIGHTS[0] + c[1] * WEIGHTS[1] + c[2] * WEIGHTS[2]
        enc_of[k] = enc
        star.append({'pow': k, 'coords': c, 'enc': enc, 'alpha_exp': k})
    log27 = [-1] * 27                      # trha 约定：零元哨兵 -1
    for k in range(26):
        log27[enc_of[k]] = k
    return star, log27, enc_of


def agda_pin(star, from_table):
    stars = ' ∷ '.join(f'pow{k}' for k in range(26)) + ' ∷ []'
    gto = ' ∷ '.join('(' + ' , '.join(f'T{TRIT_INV[c]}' for c in row) + ')'
                     for row in (star[i]['coords'] for i in range(26))) + ' ∷ []'
    allc = ' ∷ '.join('(' + ' , '.join(f'T{TRIT_INV[c]}' for c in e['coords']) + ')'
                      for e in from_table) + ' ∷ []'
    gfrom = ' ∷ '.join(f"pow{e['pow']}" for e in from_table) + ' ∷ []'
    pow_imports = ';\n          '.join(
        '; '.join(f'pow{k}' for k in rng) for rng in
        [range(0, 7), range(7, 14), range(14, 21), range(21, 26)])
    header = '{-# OPTIONS --rewriting --guardedness #-}'
    return header + '''

-- | Sovereign.Algebra.FieldTower.GF27Golden —— GF(27) golden 表**校验编码**（pin）
--
-- ⚠ **校验编码，不是数学证明**：本文件由 `scripts/gen-gf27-golden.py` 生成
--   （不要手改），把 `GF27.agda` 的 toGF27 / fromGF27 两张表钉成字面量，
--   供跨仓对拍（trha: `test/golden/gf27.json` ← 同一脚本写出）。
--   `pin-to` / `pin-from` 的 refl 只证明「golden 没有抄错表」，
--   **不承载任何数学结论**（依 2026-10-26 裁定：数值等式不作证明，
--   除非给结构理由；此处显然没有，故只当 pin）。
--
--   若 `GF27.agda` 的表发生变化 ⇒ 本文件 refl 必红 ⇒ 重新跑生成器同步 golden。

module Sovereign.Algebra.FieldTower.GF27Golden where

open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; _∷_; []; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.FieldTower.GF27
  using ( GF27; GF27Star; toGF27; fromGF27
''' + ''.join(
        '        ; ' + '; '.join(f'pow{k}' for k in rng) + '\n'
        for rng in [range(0, 7), range(7, 14), range(14, 21), range(21, 26)]) + '''        )

Coord = GF27

-- toGF27 pow0..pow25 的 26 组坐标（与 golden/gf27.json 的 star[].coords 逐项同源）
goldenTo : Vec Coord 26
goldenTo = ''' + gto + '''

pin-to : map toGF27 (''' + stars + ''') ≡ goldenTo
pin-to = refl

-- fromGF27 的 27 个子句按原顺序（第 1 条是零元折到 pow0 的约定）
goldenFrom : Vec GF27Star 27
goldenFrom = ''' + gfrom + '''

allCoords : Vec Coord 27
allCoords = ''' + allc + '''

pin-from : map fromGF27 allCoords ≡ goldenFrom
pin-from = refl
'''


TRIT_INV = {0: '₀', 1: '₁', 2: '₂'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--trha', default='/home/yanli/work/trha')
    args = ap.parse_args()
    to_table, from_table = parse()
    star, log27, enc_of = build(to_table, from_table)

    # 交叉核对：解析出的 enc/log 必须与 trha 现表逐项一致（除哨兵外）
    trha = pathlib.Path(args.trha)
    enc_hs = re.search(r'gf27PowEnc :: V\.Vector Int\ngf27PowEnc = V\.fromList\s*\[([^\]]*)\]',
                       (trha / 'src/llm/Infrastructure/CPU/GF3Intrinsic.hs').read_text(encoding='utf-8'))
    if enc_hs:
        hs_enc = [int(x) for x in enc_hs.group(1).replace('\n', ' ').split(',')]
        expect = [enc_of[k] for k in range(26)]
        if hs_enc != expect:
            raise SystemExit(f'❌ trha gf27PowEnc 与权威表不一致：\n  hs ={hs_enc}\n  fml={expect}')
        print(f'✓ trha gf27PowEnc 与权威表逐项一致（26 项）')
    log_line = re.search(r'gf27LogTable :: V\.Vector Int\n(?:.*\n)*?  v <- MV\.replicate 27 \((-?\d+)\)',
                         (trha / 'src/llm/Infrastructure/CPU/GF3Intrinsic.hs').read_text(encoding='utf-8'))
    if log_line and log_line.group(1) != '-1':
        print(f'⚠ trha 零元哨兵是 {log_line.group(1)}（本脚本按 -1 记录）')

    doc = {
        'spec': 'gf27-golden v1',
        'authority': 'src/Sovereign/Algebra/FieldTower/GF27.agda',
        'authority_repo': '/data/work/discrete-mathematics',
        'irreducible': 'x^3 + 2*x + 1 (mod 3)',
        'mult_group': 'GF(27)* ≅ Z/26Z, 生成元 α（α^13 = 2 = -1）',
        'coords_weights': WEIGHTS,
        'coords_note': 'GF27 = (t0, t1, t2)，enc = t0 + 3*t1 + 9*t2',
        'star': star,
        'pow_enc': [enc_of[k] for k in range(26)],
        'log27': log27,
        'log27_zero': -1,
        'conventions': {
            'agda': 'fromGF27 (0,0,0) = pow0（零元折到单位元，Agda 约定）',
            'trha': 'log27[0] = -1（零元哨兵，trha 实现层约定）',
        },
        'from27': from_table,
    }
    raw = json.dumps(doc, ensure_ascii=False, indent=2)
    digest = hashlib.sha256(raw.encode()).hexdigest()
    doc['sha256'] = digest
    out = trha / 'test/golden/gf27.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'wrote {out}  sha256={digest[:16]}…')

    PIN.write_text(agda_pin(star, from_table), encoding='utf-8')
    print(f'wrote {PIN.relative_to(ROOT)}')

    _ = subprocess, hashlib, digest


if __name__ == '__main__':
    TRIT_INV = {0: '₀', 1: '₁', 2: '₂'}
    main()
