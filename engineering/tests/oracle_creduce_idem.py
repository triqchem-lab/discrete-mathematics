# -*- coding: utf-8 -*-
"""先算后验证：归约器的幂等 / 范式性 —— 全枚举（非抽样）

模型：字母表 {a, A, b, B}，对合为 a<->A、b<->B（对应 CStep 的 cplus/cminus + cstep-inv）。
语义（对应 Agda 的 ctarget）：a 记 +1（mod 3），A 记 +2（mod 3），对每个坐标独立。
为了与 Agda 的 cstep-inv 一致：inv(a)=A, inv(A)=a。
"""
import itertools, json, sys

P = dict(a=('x', 1), A=('x', 2), b=('y', 1), B=('y', 2))   # 符号 -> (坐标, 位移量)
INV = dict(a='A', A='a', b='B', B='b')

def step_inv(s):  return INV[s]

def dec(s, t):
    """对应 DecEq-CStep s (cstep-inv t)"""
    return s == step_inv(t)

def cpassS(acc, xs):
    """对应 Agda 的 cpassS（栈序：acc[0] 是最新）"""
    if not xs:
        return acc
    x, rest = xs[0], xs[1:]
    if not acc:
        return cpassS([x], rest)
    y, acc2 = acc[0], acc[1:]
    if dec(x, y):
        return cpassS(acc2, rest)
    return cpassS([x] + acc, rest)

def cpassA(acc, xs):
    if not xs: return list(reversed(acc))
    x, rest = xs[0], xs[1:]
    if not acc: return cpassA([x], rest)
    y, acc2 = acc[0], acc[1:]
    if dec(x, y): return cpassA(acc2, rest)
    return cpassA([x] + acc, rest)

def creduceS(w): return cpassS([], list(w))
def creduceA(w): return cpassA([], list(w))

def elem(w):
    """群的元素：两个坐标的位移和 mod 3（顺序无关，因为我们只看终点）"""
    r = {'x': 0, 'y': 0}
    for s in w:
        c, k = P[s]
        r[c] = (r[c] + k) % 3
    return (r['x'], r['y'])

def no_cancel(w):
    """阅读序：任意相邻对不互逆"""
    return all(not dec(w[i+1], w[i]) for i in range(len(w)-1))

ALPHA = ['a', 'A', 'b', 'B']
MAXLEN = 6

words = []
for n in range(MAXLEN+1):
    words += [''.join(t) for t in itertools.product(ALPHA, repeat=n)]

fails = {'creduceA_idem': [], 'creduceS_idem': [], 'creduceA_reduced': [], 'creduceS_reduced_stack': [],
         'sem': []}
for w in words:
    ra = ''.join(creduceA(w)); rs = ''.join(creduceS(w))
    if ''.join(creduceA(ra)) != ra:  fails['creduceA_idem'].append((w, ra))
    if ''.join(creduceS(rs)) != rs:  fails['creduceS_idem'].append((w, rs))
    if not no_cancel(ra):            fails['creduceA_reduced'].append((w, ra))
    # 栈序的「无可消对」：栈内相邻 (acc[i], acc[i+1]) 满足 ¬(acc[i] ≡ inv(acc[i+1]))
    if not all(not dec(rs[i], rs[i+1]) for i in range(len(rs)-1)):
        fails['creduceS_reduced_stack'].append((w, rs))
    if elem(ra) != elem(w) or elem(rs) != elem(w): fails['sem'].append((w, ra, rs))

print("=== 全枚举结果（字母表 4 符号，长度 0..%d，共 %d 个词）===" % (MAXLEN, len(words)))
for k, v in fails.items():
    print("  %-24s 反例数 = %d  %s" % (k, len(v), ('例: %s' % (v[0],)) if v else '✅ 无'))
print()
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "free-group word reduction (alphabet {a,A,b,B}, involution a<->A, b<->B)",
    "domain": len(words), "points": len(words),
    "claim": "creduceA 幂等 + 结果阅读序无消去对 + 保持群元素；creduceS 不幂等（栈序）"
}, ensure_ascii=False))
