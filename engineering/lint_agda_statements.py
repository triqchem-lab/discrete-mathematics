#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""② 层陈述审计（Agda 通过 ≠ 数学通过——陈述层缺陷猎手）。

四指纹（签名层静态扫描）：
  taut_eq        同义反复等式（两侧字面相同）
  no_var_conjunct 无变元合取塞子（合取分量不含任何 ∀ 绑定变元——T6 同义反复塞子类）
  dup_conjunct   重复合取分量
  risk_word      越界声称词（最小/恰好/唯一/完备/当且仅当/⟺/精确阶）——散文层越界
退化假设（恒真假设/哑变元）需语义复核，由本扫描器标候选后走盲审 read-back。

用法: python3 engineering/lint_agda_statements.py [ROOT]
退出码: 0=干净 1=有命中（供门禁）
"""
import re, os, sys

RISK = ['最小','恰好','唯一','完备','当且仅当','⟺','精确阶','阶恰好']
SIG = re.compile(r'^([A-Za-z_πσφ∂][A-Za-z0-9_πσφ₀-₉′\']*)\s*:')

def scan(root):
    hits = {'taut_eq': [], 'no_var_conjunct': [], 'dup_conjunct': [], 'risk_word': []}
    for r, _, files in os.walk(root):
        for fn in files:
            if not fn.endswith('.agda'): continue
            p = os.path.join(r, fn)
            try: lines = open(p, encoding='utf-8').read().splitlines()
            except Exception: continue
            i = 0
            while i < len(lines):
                m = SIG.match(lines[i])
                if not m: i += 1; continue
                name = m.group(1)
                sig = [lines[i]]; j = i + 1
                while j < len(lines) and (lines[j][:1] in (' ', '\t')):
                    sig.append(lines[j]); j += 1
                text = ' '.join(sig)
                binders = set()
                for bm in re.finditer(r'∀\s*\(?([^):]*)\)?', text):
                    binders.update(re.findall(r"[A-Za-z_πσφ∂][A-Za-z0-9_πσφ₀-₉′']*", bm.group(1)))
                for eqm in re.finditer(r'([^()×≡]{1,40})\s*≡\s*([^()×≡]{1,40})', text):
                    L, R = eqm.group(1).strip(), eqm.group(2).strip()
                    if L and L == R: hits['taut_eq'].append((p, name, L[:40]))
                parts = re.split(r'\s(?:∧|×)\s', text)
                for pt in parts[1:]:
                    if len(pt) >= 8 and binders and not any(b in pt for b in binders):
                        hits['no_var_conjunct'].append((p, name, pt.strip()[:50]))
                seen = set()
                for pt in parts[1:]:
                    k = pt.strip()
                    if k in seen and len(k) > 6: hits['dup_conjunct'].append((p, name, k[:50]))
                    seen.add(k)
                for w in RISK:
                    if w in text: hits['risk_word'].append((p, name, w)); break
                i = j
    return hits

if __name__ == '__main__':
    root = sys.argv[1] if len(sys.argv) > 1 else 'src'
    hits = scan(root)
    total = 0
    for k, v in hits.items():
        print(f'== {k}: {len(v)} ==')
        for x in v[:10]:
            print('  ', x[0], '|', x[1], '|', x[2] if len(x) > 2 else '')
        total += len(v)
    print(f'--- 合计 {total} 命中（候选须语义复核：退化假设/哑变元判据见 proof-engineer 技能 ②层节）---')
    sys.exit(1 if total else 0)
