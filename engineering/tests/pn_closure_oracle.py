"""π₁bt 未闭合项的**先算后验** oracle（精确整数/符号穷举，禁用浮点）。

基座：2 顶点 4 有向边（= 2 条无向边）的图上的**全部走**（free groupoid 的模型）。
  a1,a2 : 0→1 ；b1,b2 : 1→0 ；flip(ai)=bi。
折叠 red = 自由群胚的消去正规形（相邻互逆对消去，栈实现）。
Red p   = p 无相邻互逆对。

待核两条**未闭合**命题：
  (a) rev-red ：Red p ⟹ Red (rev p)                       （本库 blocked 的 PN12.rev-red）
  (b) conj-mul：conj u (p ⊛ q) ≡ conj u p ⊛ conj u q      （本库 WIP 的 conj-mul，类层）
其中 conj u p = red (rev u ++ p ++ u)，⊛ = red(++).

穷举空间即 domain，实际检查数即 points；二者相等 ⇒ 完备（非抽样）。
"""
import itertools
import json

A = ('a1', 'a2')            # 0 → 1
B = ('b1', 'b2')            # 1 → 0
EDGES = A + B
FLIP = {'a1': 'b1', 'b1': 'a1', 'a2': 'b2', 'b2': 'a2'}


def src(e):
    return 0 if e in A else 1


def tgt(e):
    return 1 if e in A else 0


def walks(maxlen, start=None, end=None):
    """全部端点合法的走（长度 0..maxlen）；可选端点过滤。"""
    out = []
    for L in range(maxlen + 1):
        for w in itertools.product(EDGES, repeat=L):
            if L and any(tgt(w[i]) != src(w[i + 1]) for i in range(L - 1)):
                continue
            if not L:
                if start is not None and start != end:
                    continue
            if start is not None:
                s = start if L == 0 else src(w[0])
                t = start if L == 0 else tgt(w[-1])
                if s != start or t != end:
                    continue
            out.append(w)
    return out


def red(w):
    st = []
    for e in w:
        if st and st[-1] == FLIP[e]:
            st.pop()
        else:
            st.append(e)
    return tuple(st)


def isred(w):
    return all(w[i] != FLIP[w[i + 1]] for i in range(len(w) - 1))


def rev(w):
    return tuple(FLIP[e] for e in reversed(w))


L_REV = 8        # rev-red 枚举上限
L_CONJ = 4       # conj-mul 枚举上限

# ── (a) rev-red ──────────────────────────────────────────────────────────
ws = walks(L_REV)
rev_space = [w for w in ws if isred(w)]
rev_bad = [w for w in rev_space if not isred(rev(w))]

# ── (b) conj-mul ─────────────────────────────────────────────────────────
U = walks(L_CONJ, 0, 1)
LOOPS = walks(L_CONJ, 0, 0)
conj_space = 0
conj_bad = []
for u in U:
    ru = rev(u)
    for p in LOOPS:
        for q in LOOPS:
            conj_space += 1
            lhs = red(ru + red(p + q) + u)
            rhs = red(red(ru + p + u) + red(ru + q + u))
            if lhs != rhs:
                conj_bad.append((u, p, q))
                if len(conj_bad) > 5:
                    break

domain = len(rev_space) + conj_space
points = len(rev_space) + conj_space

print("rev-red   ：Red p ⟹ Red (rev p)  ｜枚举既约走 %d 条，反例 %d 条"
      % (len(rev_space), len(rev_bad)))
print("conj-mul  ：conj u (p ⊛ q) ≡ conj u p ⊛ conj u q  ｜枚举三元组 %d 个，反例 %d 个"
      % (conj_space, len(conj_bad)))
if rev_bad:
    print("  rev-red 反例（前 3）:", rev_bad[:3])
if conj_bad:
    print("  conj-mul 反例（前 3）:", conj_bad[:3])

claim = ("rev-red(H) 与 conj-mul(H) 在 2 顶点 2 无向边图的全部走上穷举成立"
         if not rev_bad and not conj_bad else "存在反例（见上）")
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "2 顶点 4 有向边（2 无向边）自由群胚模型；red=消去正规形",
    "domain": domain, "points": points, "claim": claim,
}, ensure_ascii=False))
