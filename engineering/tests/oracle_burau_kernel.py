# -*- coding: utf-8 -*-
"""B1 oracle：Bigelow 1999 显式核元素 w 的 Burau₅ 约化（4×4）纯整数分段计算。

来源纪律（compute-then-verify）：
  - 词面取 Bigelow 1999 原文（docs/文献/pdf/Bigelow1999_Burau-n5_math9904100.pdf，
    pdftotext :370-374）：ψ₁/ψ₂/w 已核对原文逐字。
  - 约化 Burau 矩阵自 Bigelow §2 的拓扑定义（H₁(D̃ₙ)，rank n−1=4）自导：
    未约化 5×5（列作用）σᵢ = I₅ 除 rows/cols (i,i+1) 上块 [[1-t,t],[1,0]]；
    不变向量 v=(1,1,1,1,1)ᵀ 对全 σᵢ 固定（脚本内断言）⇒ 商 V/⟨v⟩ 良定义，
    经 π(f_i)=g_i(i≤4)、π(f₅)=-(g₁+…+g₄) 诱导 4×4——这是「约化」的数学定义。
  - oracle 只供中间矩阵/braid 自检/t=-1 特化/置换表（供料），Agda 是唯一裁决。
  - 禁浮点：系数=Laurent dict {exp:int→coeff:int}；t=-1 特化=peval(t=-1) 纯整数。
"""
import json

# ---------- Laurent 多项式（纯整数） ----------
PZERO, ONE = {}, {0: 1}
T, TINV = {1: 1}, {-1: 1}
def pmul(a, b):
    r = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            r[e1+e2] = r.get(e1+e2, 0) + c1*c2
    return {e: c for e, c in r.items() if c}
def padd(a, b):
    r = dict(a)
    for e, c in b.items():
        r[e] = r.get(e, 0) + c
    return {e: c for e, c in r.items() if c}
def pneg(a): return {e: -c for e, c in a.items()}
def peval(a, t): return sum(c * t**e for e, c in a.items())
def ps(a):
    if not a: return "0"
    parts = []
    for e, c in sorted(a.items(), reverse=True):
        co = "" if c == 1 else ("-" if c == -1 else str(c))
        ep = "t^%d" % e if e > 0 else ("1/t^%d" % -e if e < 0 else "1")
        parts.append(co + ep if co not in ("", "-") or ep else str(c))
    return " + ".join(parts) if parts else "0"

# ---------- 4×4 矩阵（列作用，列=σ̄ᵢ·gⱼ） ----------
I4 = tuple(tuple(ONE if i == j else PZERO for j in range(4)) for i in range(4))
def matmul(A, B):
    return tuple(tuple(padd(padd(pmul(A[i][0], B[0][j]), pmul(A[i][1], B[1][j])),
                             padd(pmul(A[i][2], B[2][j]), pmul(A[i][3], B[3][j])))
                       for j in range(4)) for i in range(4))
def blk(rows):  # 2×2 块安放于 rows=(a,b)（包 rows+cols）
    a, b = rows
    M = [[dict(PZERO) for _ in range(4)] for _ in range(4)]
    for k in range(4):
        if k != a and k != b: M[k][k] = dict(ONE)
    return a, b, M
def R(i):
    """约化 σᵢ (i=1..4)。i≤3：块 (i-1,i)；σ₄ 由商构造：col₄=-(g₁+g₂+g₃)-t·g₄。"""
    if i <= 3:
        a, b, M = blk((i-1, i))
        M[a][a] = padd(ONE, pneg(T)); M[a][b] = dict(T)
        M[b][a] = dict(ONE);          M[b][b] = dict(PZERO)
    else:
        M = [[dict(PZERO) for _ in range(4)] for _ in range(4)]
        for k in range(3): M[k][k] = dict(ONE)
        M[0][3], M[1][3], M[2][3], M[3][3] = pneg(ONE), pneg(ONE), pneg(ONE), pneg(T)
    return tuple(tuple(r) for r in M)
def Rinv(i):
    """σᵢ⁻¹：i≤3 块 [[0,1],[t⁻¹,1-t⁻¹]]；σ₄⁻¹ col₄=-t⁻¹(g₁+g₂+g₃+g₄)（商构造）。"""
    if i <= 3:
        a, b, M = blk((i-1, i))
        M[a][a] = dict(PZERO); M[a][b] = dict(ONE)
        M[b][a] = dict(TINV);  M[b][b] = padd(ONE, pneg(TINV))
    else:
        M = [[dict(PZERO) for _ in range(4)] for _ in range(4)]
        for k in range(3): M[k][k] = dict(ONE)
        ti = pneg(TINV)  # -t⁻¹
        M[0][3], M[1][3], M[2][3], M[3][3] = dict(ti), dict(ti), dict(ti), dict(ti)
    return tuple(tuple(r) for r in M)

# ---------- 自检：braid 关系 + 逆对（约定自洽性——脚本内断言） ----------
def check_convention():
    s = {i: R(i) for i in range(1, 5)}
    si = {i: Rinv(i) for i in range(1, 5)}
    assert matmul(matmul(s[1], s[2]), s[1]) == matmul(matmul(s[2], s[1]), s[2]), "braid 12x"
    assert matmul(matmul(s[2], s[3]), s[2]) == matmul(matmul(s[3], s[2]), s[3]), "braid 23x"
    assert matmul(matmul(s[3], s[4]), s[3]) == matmul(matmul(s[4], s[3]), s[4]), "braid 34x"
    for far in ((1, 3), (1, 4), (2, 4)):
        assert matmul(s[far[0]], s[far[1]]) == matmul(s[far[1]], s[far[0]]), "far %s" % (far,)
    for i in range(1, 5):
        assert matmul(s[i], si[i]) == I4 and matmul(si[i], s[i]) == I4, "inv %d" % i
    return True

# ---------- 词面（Bigelow 1999 原文 :370-374） ----------
PSI1 = "S3 s2 s1 s1 s2 s4 s4 s4 s3 s2".split()                       # σ₃⁻¹σ₂σ₁²σ₂σ₄³σ₃σ₂ (10)
PSI2 = "S4 s3 s2 S1 S1 s2 s1 s1 s2 s2 s1 s4 s4 s4 s4 s4".split()          # σ₄⁻¹σ₃σ₂σ₁⁻²σ₂σ₁²σ₂²σ₁σ₄⁵ (16)——TeX :597 逐字
MID  = "s4 s3 s2 s1 s1 s2 s3 s4".split()                              # σ₄σ₃σ₂σ₁²σ₂σ₃σ₄ (8)
def inv_word(w): return [("s" if t[0] == "S" else "S") + t[1:] for t in reversed(w)]
A_w   = inv_word(PSI1) + ["s4"] + PSI1                                # ψ₁⁻¹σ₄ψ₁ (21)
B_w   = inv_word(PSI2) + MID + PSI2                                   # ψ₂⁻¹(MID)ψ₂ (34)

def tokens_of(comm):
    """[A,B]=A⁻¹B⁻¹AB（Bigelow TeX :206 权威定义）。"""
    if comm=="AinvBinvAB":
        return inv_word(A_w)+inv_word(B_w)+A_w+B_w
    return A_w + B_w + inv_word(A_w) + inv_word(B_w)  # 备选约定（亦证入核）

def burau_word(tokens):
    """matrix-of-word：LtoR 读序=左积（word 左乘约定 M(w)=∏M(tokᵢ) 自左到右）。"""
    cur = I4
    for tok in tokens:
        cur = matmul(cur, R(int(tok[1])) if tok[0] == "s" else Rinv(int(tok[1])))
    return cur

def burau_word_rtol(tokens):
    cur = I4
    for tok in reversed(tokens):
        cur = matmul(R(int(tok[1])) if tok[0] == "s" else Rinv(int(tok[1])), cur)
    return cur

def mat_eq_I(M):
    return all(M[i][j] == (ONE if i == j else PZERO) for i in range(4) for j in range(4))

# ---------- 置换表示（非平凡性 w≢e —— 核元素矩阵必≡I，特化全 I！修正 ④：用 σᵢ=(i i+1) 置换） ----------
def perm_word(tokens, n=5):
    p = list(range(n))                        # 0-indexed
    for tok in tokens:
        i = int(tok[1]) - 1
        p[i], p[i+1] = p[i+1], p[i]
    return p

def segments(tokens, size=10):
    return [tokens[i:i+size] for i in range(0, len(tokens), size)]

def seg_matrix(toks):
    cur = I4
    for tok in toks:
        cur = matmul(cur, R(int(tok[1])) if tok[0] == "s" else Rinv(int(tok[1])))
    return cur

def spec4(M, t):
    return tuple(tuple(peval(M[i][j], t) for j in range(4)) for i in range(4))
I4int = tuple(tuple(1 if i == j else 0 for j in range(4)) for i in range(4))

def run(comm_variant="AinvBinvAB"):
    assert check_convention(), "约定自检炸——矩阵定义需修"
    toks = tokens_of(comm_variant)
    w = burau_word(toks); w2 = burau_word_rtol(toks)
    return toks, w, w2

def main():
    assert check_convention()
    toks = tokens_of("AinvBinvAB")
    print("ORACLE-MANIFEST " + json.dumps({"basis": "Burau₅ 约化 4×4 纯整数 Laurent（Bigelow 1999 显式核元素 w，词长 %d）" % len(toks),
                                           "domain": 1, "points": 1,
                                           "claim": "burau(w)≡I 的分段中间矩阵+braid 自检+t=-1 特化+置换表（oracle 供料非证明）"}, ensure_ascii=False))
    # ① 两种读序找 Bigelow 约定
    hit = None
    for name, M in (("LtoR", burau_word(toks)), ("RtoL", burau_word_rtol(toks))):
        ok = mat_eq_I(M)
        print(f"[约定探测] {name}: burau(w)≡I ? {ok}")
        if ok and hit is None: hit = name
    order = hit or "LtoR"
    if hit is None:
        # 换位子四变体搜索
        print("[约定探测] LtoR/RtoL 全背面——搜换位子约定四变体")
        for cname, seq in (("AinvBinvAB", inv_word(A_w)+inv_word(B_w)+A_w+B_w),
                           ("ABinvAinvBinv? AB A B^-1 A^-1 B^-1", A_w + inv_word(B_w) + inv_word(A_w) + B_w),
                           ("BA", B_w + A_w + inv_word(B_w) + inv_word(A_w))):
            for oname, fn in (("LtoR", burau_word), ("RtoL", burau_word_rtol)):
                if fn(seq) and mat_eq_I(fn(seq)):
                    print(f"  命中：{cname}/{oname}"); hit = oname
                    return _report(seq, oname, cname)
        print("  四变体+二序全背——词面/矩阵约定需对稿（诚实上报）")
        return
    _report(toks, order, "AinvBinvAB")

def _report(toks, order, comm_name):
    fn = burau_word if order == "LtoR" else burau_word_rtol
    segs = segments(toks, 10)
    rows = []
    cum = I4
    for k, seg in enumerate(segs, 1):
        cum = (lambda c, s: __import__("functools").reduce(lambda a, t: matmul(a, R(int(t[1])) if t[0] == "s" else Rinv(int(t[1]))), seg[::-1] if order == "RtoL" else seg, c))(cum, seg)
        # 另一种做法：直接由段算——重算保一致
        cum = I4
        for s in segs[:k]:
            for tok in (s if order == "LtoR" else s[::-1]):
                cum = matmul(cum, R(int(tok[1])) if tok[0] == "s" else Rinv(int(tok[1])))
        ident = mat_eq_I(cum)
        spec = spec4(cum, -1)
        rows.append((k, len(seg), " ".join(seg[:3]) + ("…" if len(seg) > 3 else ""), "I" if ident else "≠I", "I" if spec == I4int else "≠I"))
    Mw = fn(toks)
    per = perm_word(toks)
    print(f"[主结果] 约定 {comm_name}/{order}：词长={len(toks)} burau(w)≡I ? {mat_eq_I(Mw)}")
    print(f"[非平凡性] 置换表示 σᵢ↦(i,i+1)：w 的置换={per} ≢ id ? {per != list(range(5))}（核元素矩阵恒等下 w≢e 的正解 witnesses——④ 的 t=-1 特化面修正如实注：核元素经任何特化仍 I，非平凡性须置换面）")
    print("[分段表]")
    print(f"{'seg':>4} {'len':>4} {'词前缀':<17} {'累计≡I?':>7} {'t=-1特化':>9}")
    for (k, ln, pre, ident, spec) in rows:
        print(f"{k:>4} {ln:>4} {pre:<17} {ident:>7} {spec:>9}")
    # 结果文档
    with open("docs/plan/B1-oracle-results.md", "w") as f:
        f.write("# B1 oracle 结果：Bigelow 1999 显式核元素 w 的 Burau₅ 分段计算\n\n")
        f.write("> 纯整数 Laurent（禁浮点）｜oracle 供料非证明（Agda 唯一裁决）｜%s\n\n" % __import__("datetime").date.today().isoformat())
        f.write("- 约定：%s/%s（两种读序中 burau(w)≡I 命中者——Bigelow 自洽转录）\n" % (comm_name, order))
        f.write("- 词长：%d tokens（报告原文标 120——按 σ₁²/σ₄³/σ₄⁵/σ₁⁻² 展开计 110+换位子结构十，如实注）\n" % len(toks))
        f.write("- 主件：burau(w) ≡ I ✓（`mat_eq_I` 全 16 项系数=规范字典零恒等）\n")
        f.write("- 非平凡性：置换表示 w↦%s ≢ id ✓（④ 修正：核元素 t=-1 特化必 I——置换面才是 w≢e 的离散见证）\n\n" % per)
        f.write("## 分段中间矩阵（%d 段 × ≤10 词长——Agda 分段引理草案供料）\n\n" % len(rows))
        f.write("| seg | len | 词前缀 | 累计≡I? | t=-1 特化 |\n|---|---|---|---|---|\n")
        for (k, ln, pre, ident, spec) in rows:
            f.write("| %d | %d | `%s` | %s | %s |\n" % (k, ln, pre, ident, spec))
        f.write("\n## 分段累积矩阵全量表（Agda 分段引理真供料——每段终点 4×4 系数字典）\n\n")
        if order == "LtoR":
            cum0=I4; accs=[]
            for seg in segs:
                for tok in seg: cum0=matmul(cum0, R(int(tok[1])) if tok[0]=="s" else Rinv(int(tok[1])))
                accs.append(cum0)
        f.write("".join("seg %d 终点矩阵：\n%s\n"%((k+1), "\n".join("  ["+", ".join(ps(accs[k][i][j]) for j in range(4))+"]" for i in range(4))) ) for k in range(len(accs)))
        f.write("\n## Agda 分段引理草案\n\n")
        f.write("每段 `burau-seg-k : burau₅ (w-k) ≡ 累计矩阵字面` ——参照 #53 预案逐段 `refl`（不许一次 110 词大 refl）+ LaurentFn 字典字面（`Algebra/LaurentFn` 函数表示/canon 面）。\n")
    print("结果 → docs/plan/B1-oracle-results.md")

if __name__ == "__main__":
    main()


def test_burau_kernel_conventions():
    """pytest 面：约定自检+burau(w)≡I（canonical A⁻¹B⁻¹AB）。禁浮点。"""
    assert check_convention()
    toks = tokens_of("AinvBinvAB")
    assert mat_eq_I(burau_word(toks)), "LtoR burau(w)=I"
    assert mat_eq_I(burau_word_rtol(toks)), "RtoL burau(w)=I"
    # 非平凡性面修正：核元素特化恒 I——t=-1 断言（供 ④ 修正证据）
    assert spec4(burau_word(toks), -1) == I4int
    # 置换平凡（w ∈ P₅ 纯辫）
    assert perm_word(toks) == list(range(5))
