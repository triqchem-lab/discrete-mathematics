#!/usr/bin/env python3
# A/B/C 分级初筛 v2 + D1-D6 风险（2026-10-11 核实后修正：D6 排除关键字；D4 真嵌套深度；C 加空壳比）
import sys, csv, re, pathlib
RISK_D3 = ("Hensel", "LaurentNorm", "LaurentSums", "LaurentRing", "Kakeya", "T6", "jac_")
KEYWORDS = {'data','record','module','where','open','import','instance','variable','postulate','field','mutual','abstract','private','_','let','in','with','rewrite','syntax','infix','infixl','infixr','∀','λ'}
print("module,path,lines,grade,D1_naming,D2_shell,D3_compile,D4_trans,D5_where,D6_dup")
for row in csv.DictReader(open(sys.argv[1])):
    p = row['path']; text = pathlib.Path(p).read_text(encoding='utf-8', errors='ignore')
    code = re.sub(r'--.*', '', text)
    lines, post, holes, six = int(row['lines']), int(row['postulates']), int(row['holes']), row['six_section']
    bodies = re.findall(r'(?m)^[^\s:(){}\[\]→≡·]+[^\n:]*=[^\n]+', code)
    ncode = len([l for l in code.splitlines() if l.strip()])
    thms = len(re.findall(r'(?m)^[^\s:(){}\[\]→≡·]+\s+[^:\n]*:', code))
    hollow = ncode < 30 and len(bodies) < 3
    grade = 'C' if (holes > 0 or hollow) else 'B'
    d1 = 'y' if re.search(r'\b(encode|dec)[A-Z]\w*|jac_[A-Z]', text) and six == 'n' else ''
    d2 = 'y' if hollow or (len(bodies) < 3 and '待补' in text) else ''
    d3 = 'y' if any(k in p for k in RISK_D3) else ''
    maxnest = 0
    for m in re.finditer(r'trans\b', code):
        d, i = 0, m.start()
        while code[i:i+6] == 'trans ' or code[i:i+5] == 'trans':
            d += 1; nxt = code.find('trans', i+5)
            seg = code[i:nxt if nxt>0 else i+200]
            if '(' not in seg[:seg.find('trans', 5) if seg.find('trans',5)>0 else len(seg)]: break
            i = nxt if nxt>0 else 10**9
        maxnest = max(maxnest, d)
    d4 = 'y' if maxnest >= 4 else ''
    d5 = 'y' if re.search(r'(?m)^\s{2,}\w+.*=.*\n\s*where', text) else ''
    tops = [n for n in re.findall(r'(?m)^([^\s:(){}\[\]→≡·]+)[^\n:]* :', code) if n not in KEYWORDS]
    d6 = 'y' if len(tops) != len(set(tops)) else ''
    print(f"{row['module']},{p},{lines},{grade},{d1},{d2},{d3},{d4},{d5},{d6}")
