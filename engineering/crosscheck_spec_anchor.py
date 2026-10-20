# crosscheck_spec_anchor — Agda 规范锚 (SpecAnchor) vs 三语言 dump（移植自 bridge-from-sov-math/crosscheck.py ✓）
import json, os, re, sys

anchor_p = "src/Sovereign/Algebra/SpecAnchor.agda"   # 移植：路径对齐本项目 ✓
default_dump = os.path.join(os.path.dirname(os.path.abspath(__file__)), "artifacts", "sovdump.csv")
dump_p = sys.argv[1] if len(sys.argv) > 1 else default_dump
TRI = {"T₀": 0, "T₁": 1, "T₂": 2}

add_exp, mul_exp, crt_exp, gm_exp, ds_exp, dm_exp = {}, {}, {}, {}, {}, {}
for ln in open(anchor_p):
    ln = ln.rstrip("\n")
    m = re.match(r"^(add|mul|crt|gm|ds)-(\d)(\d) :", ln)
    m2 = re.match(r"^dm-(\d)(\d)(\d)(\d) :", ln)
    if m2 and not m:
        t1,k1,t2,k2 = (int(x) for x in m2.groups())
        ts = re.findall(r"T([₀₁₂])", ln.split("≡")[-1])
        az = re.findall(r"a([0-3])", ln.split("≡")[-1])
        if len(ts) == 1 and len(az) == 1:
            dm_exp[(t1,k1,t2,k2)] = (TRI["T" + ts[0]], int(az[0]))
        continue
    if not m:
        continue
    kind, i, j = m.group(1), int(m.group(2)), int(m.group(3))
    rhs = ln.split("≡")[-1].strip()
    if kind == "ds":
        ts = re.findall(r"T([₀₁₂])", rhs)
        az = re.findall(r"a([0-3])", rhs)
        if len(ts) == 1 and len(az) == 1:
            ds_exp[(i, j)] = (TRI["T" + ts[0]], int(az[0]))
    elif kind == "gm":
        mm = re.findall(r"T([₀₁₂])", rhs)
        if len(mm) == 2:
            gm_exp[(i, j)] = TRI["T" + mm[0]] * 3 + TRI["T" + mm[1]]
    elif kind == "crt":
        crt_exp[(i, j)] = int(rhs)
    else:
        mm = re.search(r"≡\s*T([₀₁₂])", ln)
        if mm:
            (add_exp if kind == "add" else mul_exp)[(i, j)] = TRI["T" + mm.group(1)]

add_dump, mul_dump, crt_dump, gm_dump, ds_dump, dm_dump = {}, {}, {}, {}, {}, {}
for ln in open(dump_p):
    p = ln.strip().split(",")
    if p[0] == "GF3ADD": add_dump[(int(p[1]), int(p[2]))] = int(p[3])
    elif p[0] == "GF3MUL": mul_dump[(int(p[1]), int(p[2]))] = int(p[3])
    elif p[0] == "DCCRT": crt_dump[(int(p[1]), int(p[2]))] = int(p[3])
    elif p[0] == "GF9MUL": gm_dump[(int(p[1]), int(p[2]))] = int(p[3])
    elif p[0] == "DCSIGMA": ds_dump[(int(p[1]), int(p[2]))] = (int(p[3]), int(p[4]))
    elif p[0] == "DCMIX": dm_dump[(int(p[1]), int(p[2]), int(p[3]), int(p[4]))] = int(p[5])

def cmp(name, exp, got):
    bad = [(k, exp[k], got.get(k)) for k in exp if got.get(k) != exp[k]]
    print(f"{name}: {len(exp)} 项, 不一致 {len(bad)}" + ("" if not bad else f" → {bad[:4]}"))
    return not bad

# DCMIX：dump 的结果编码 r ≡ 4t − 3k (mod 12)，由 Agda 侧的 (t,k) 换算比对
def cmp_dm(exp, got):
    bad = [(k, (4 * exp[k][0] - 3 * exp[k][1]) % 12, got.get(k)) for k in exp
           if got.get(k) != (4 * exp[k][0] - 3 * exp[k][1]) % 12]
    print(f"Agda mixedOp ↔ dump DCMIX: {len(exp)} 项, 不一致 {len(bad)}" + ("" if not bad else f" → {bad[:4]}"))
    return not bad

ok = True
ok &= cmp("Agda add 表 ↔ dump GF3ADD", add_exp, add_dump)
ok &= cmp("Agda mul 表 ↔ dump GF3MUL", mul_exp, mul_dump)
ok &= cmp("Agda crt12 表 ↔ dump DCCRT", crt_exp, crt_dump)
ok &= cmp("Agda GF(9) 乘表 ↔ dump GF9MUL", gm_exp, gm_dump)
ok &= cmp("Agda sigmaDC ↔ dump DCSIGMA", ds_exp, ds_dump)
ok &= cmp_dm(dm_exp, dm_dump)
total = len(add_exp) + len(mul_exp) + len(crt_exp) + len(gm_exp) + len(ds_exp) + len(dm_exp)
print("ORACLE-MANIFEST", json.dumps({
    "basis": "Agda SpecAnchor.agda 内核判定值 vs 三语言 dump",
    "domain": total, "points": total,
    "claim": f"GF(3) 加乘 {len(add_exp)+len(mul_exp)} + CRT {len(crt_exp)} + GF(9) 乘表 {len(gm_exp)} + sigmaDC {len(ds_exp)} + DC 运算表 {len(dm_exp)} 项: Agda 内核判定 == dump 值"
}))
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
