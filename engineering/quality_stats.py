#!/usr/bin/env python3
# quality_stats.py —— QUALITY.batch0-machine 全库机器统计底料（八批质量审计基件）
# 可复跑：python3 engineering/quality_stats.py [--root src] [--report docs/quality-batch0-stats.md]
# 口径：
#   ① postulate/hole 剥注释后计数（`--` 行注释去除；{-# ... #-} pragma 不计）
#   ② 规模：行/顶层签名/**定理形签名**——多行签名容错（`^name :` 与续行类型合并判定；第三案教训）
#   ③ lint 汇总（外部脚本 check_structure_lint.sh，本脚本只引用其输出摘要）
#   ④ 重复顶层名扫描（同名跨文件——dup-names 判例口径：同名≠重复，交表人工判）
#   ⑤ 活动/定理比（深度审核口径：trans/cong/∙/refl/sym/subst/⊥-elim 活动标记）
# 零源码改动；纯读取 + 报告生成。
import re, os, sys, argparse, collections, datetime

KEYWORDS = {'module','open','import','data','record','where','postulate','private','instance',
            'mutual','abstract','infix','infixl','infixr','syntax','pattern','quote',
            'forall','let','in','with','rewrite','field','constructor','inductive',
            'eta-equality','no-eta-equality','variable','macro','unquote','do','Set'}
ACT = re.compile(r'\btrans\b|\bcong₂?\b|\bsym\b|\bsubst₂?\b|_∙_|\brefl\b|⊥-elim|\bcase\b|\babsurd\b')
THM = re.compile(r'≡|≢|¬|≤|<|↔|≃|⊥|≉')

def strip_comments(t):
    # 去 {-# ... #-} pragma、{- ... -} 块注释、-- 行注释（启发式：字符串内 -- 少见，已注明）
    t = re.sub(r'\{-#.*?#-\}', '', t, flags=re.S)
    t = re.sub(r'\{-(?!#).*?-\}', '', t, flags=re.S)
    t = re.sub(r'--.*', '', t)
    return t

SIG = re.compile(r'^([^\s:(){}\[\]→≡·][^:\n]*?)\s*:(.*)$')

def top_level_sigs(stripped):
    """返回 [(name, type_text含续行, 行号)]——多行签名容错。"""
    lines = stripped.split('\n')
    out = []
    for i, ln in enumerate(lines):
        if not ln or ln[0].isspace():
            continue
        first = ln.split()[0] if ln.split() else ''
        if first in KEYWORDS:
            continue
        m = SIG.match(ln)
        if not m:
            continue
        name, rest = m.group(1).strip(), m.group(2)
        if any(c in name for c in ' →≡(){}[]'):
            continue
        # 续行收集（缩进行）
        j = i + 1
        while j < len(lines) and lines[j] and lines[j][0].isspace():
            rest += ' ' + lines[j]
            j += 1
        out.append((name, rest, i + 1))
    return out

def scan_file(path):
    t = open(path, errors='ignore').read()
    nc = strip_comments(t)
    lines = t.count('\n') + 1
    post = len(re.findall(r'\bpostulate\b', nc))
    holes = nc.count('{!')
    sigs = top_level_sigs(nc)
    thm = [(n, ty, ln) for (n, ty, ln) in sigs if THM.search(ty)]
    acts = len(ACT.findall(nc))
    return dict(path=path, lines=lines, post=post, holes=holes,
                sigs=len(sigs), thm=len(thm), acts=acts,
                names=[n for n, _, _ in sigs])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='src')
    ap.add_argument('--report', default=None)
    a = ap.parse_args()
    files = []
    for dp, _, fns in os.walk(a.root):
        for fn in fns:
            if fn.endswith('.agda'):
                files.append(os.path.join(dp, fn))
    files.sort()
    rows = [scan_file(p) for p in files]
    # 分组（src/Sovereign/<一级目录>）
    def grp(p):
        parts = p.split(os.sep)
        return parts[2] if len(parts) > 3 else '(root)'
    groups = collections.defaultdict(list)
    for r in rows:
        groups[grp(r['path'])].append(r)
    # 重复顶层名（跨文件）
    name_map = collections.defaultdict(set)
    for r in rows:
        for n in set(r['names']):
            name_map[n].add(r['path'])
    dups = {n: ps for n, ps in name_map.items() if len(ps) > 1}
    # 汇总
    T = lambda k: sum(r[k] for r in rows)
    out = []
    out.append('# QUALITY.batch0-machine —— 全库机器统计底料\n')
    out.append(f'> 生成：{datetime.date.today()}｜工具：`engineering/quality_stats.py`（可复跑）｜零源码改动')
    out.append(f'> 口径：剥注释计数｜多行签名容错（`^name :` + 续行合并）｜定理形 = 类型含 ≡/≢/¬/≤/</↔/≃/⊥\n')
    out.append('## 一、全库总量\n')
    out.append(f'| 指标 | 值 |\n|---|---|')
    out.append(f'| 模块数 | {len(rows)} |')
    out.append(f'| 总行数 | {T("lines")} |')
    out.append(f'| 顶层签名 | {T("sigs")} |')
    out.append(f'| 定理形签名 | {T("thm")} |')
    out.append(f'| 证明活动标记 | {T("acts")} |')
    out.append(f'| postulate 计数（模块内出现） | {T("post")} |')
    out.append(f'| hole（{{!）计数 | {T("holes")} |')
    out.append(f'| 跨文件重复顶层名组 | {len(dups)} |\n')
    out.append('## 二、按目录分组\n')
    out.append('| 目录 | 模块 | 行 | 签名 | 定理形 | 活动 | 活动/定理 | post | hole |')
    out.append('|---|---|---|---|---|---|---|---|---|')
    for g in sorted(groups):
        rs = groups[g]
        gm = lambda k: sum(r[k] for r in rs)
        ratio = gm('acts') / gm('thm') if gm('thm') else 0
        out.append(f'| {g} | {len(rs)} | {gm("lines")} | {gm("sigs")} | {gm("thm")} | {gm("acts")} | {ratio:.1f} | {gm("post")} | {gm("holes")} |')
    # 异常清单
    out.append('\n## 三、异常清单\n')
    p_pos = [r for r in rows if r['post'] > 0]
    h_pos = [r for r in rows if r['holes'] > 0]
    act0 = [r for r in rows if r['sigs'] > 0 and r['acts'] == 0]
    out.append(f'### 3.1 postulate>0（{len(p_pos)} 模块——kind 登记面）')
    for r in p_pos:
        out.append(f'- `{r["path"]}` post={r["post"]}')
    out.append(f'\n### 3.2 hole>0（{len(h_pos)} 模块）')
    for r in h_pos:
        out.append(f'- `{r["path"]}` hole={r["holes"]}')
    if not h_pos:
        out.append('- （无）')
    out.append(f'\n### 3.3 活动=0 且签名>0（{len(act0)} 模块——空壳嫌疑面，需人工四问）')
    for r in act0:
        out.append(f'- `{r["path"]}` sigs={r["sigs"]}（其中定理形 {r["thm"]}）')
    out.append('\n## 四、跨文件重复顶层名（同名≠重复——dup-names 判例口径，交人工判）\n')
    out.append(f'共 {len(dups)} 组；按涉及文件数降序前 30：\n')
    for n, ps in sorted(dups.items(), key=lambda kv: -len(kv[1]))[:30]:
        out.append(f'- `{n}` ×{len(ps)}')
    txt = '\n'.join(out) + '\n'
    if a.report:
        open(a.report, 'w').write(txt)
        print(f'报告写入 {a.report}')
    else:
        print(txt)

if __name__ == '__main__':
    main()
