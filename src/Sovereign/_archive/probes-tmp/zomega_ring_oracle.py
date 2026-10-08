# Zω 环律先算后验证 oracle（精确整数，禁浮点）
# 载体：(a,b) 表 a + bω，ω² = -1 - ω。
#   addZω (a,b) (c,d) = (a+c, b+d)
#   mulZω (a,b) (c,d) = (ac-bd, ad+bc-bd)   ← 由 ω² = -1-ω 化简而得
# 穷举网格 {-2..2}² 的 25 个元素，核对将迁移到
# src/Sovereign/Algebra/Zomega.agda 的全部环律（assoc/comm/distrib/zero/unit/inverse）。
# 全部案都检查（points = domain，无抽样）。

def addz(x, y):
    return (x[0] + y[0], x[1] + y[1])

def mulz(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)

def negz(x):
    return (-x[0], -x[1])

grid = [(a, b) for a in range(-2, 3) for b in range(-2, 3)]
zero, one = (0, 0), (1, 0)
fails = []
checks = 0

for x in grid:
    checks += 6
    if addz(zero, x) != x:
        fails.append(("add-identity-l", x))
    if addz(x, zero) != x:
        fails.append(("add-identity-r", x))
    if addz(negz(x), x) != zero:
        fails.append(("add-inverse-l", x))
    if addz(x, negz(x)) != zero:
        fails.append(("add-inverse-r", x))
    if mulz(one, x) != x:
        fails.append(("mul-identity-l", x))
    if mulz(x, one) != x:
        fails.append(("mul-identity-r", x))
    for y in grid:
        checks += 5
        if addz(x, y) != addz(y, x):
            fails.append(("add-comm", x, y))
        if mulz(x, y) != mulz(y, x):
            fails.append(("mul-comm", x, y))
        if mulz(zero, x) != zero:
            fails.append(("mul-zero-l", x, y))
        if mulz(x, zero) != zero:
            fails.append(("mul-zero-r", x, y))
        if negz(negz(x)) != x:
            fails.append(("neg-involutive", x, y))
        for z in grid:
            checks += 4
            if addz(addz(x, y), z) != addz(x, addz(y, z)):
                fails.append(("add-assoc", x, y, z))
            if mulz(mulz(x, y), z) != mulz(x, mulz(y, z)):
                fails.append(("mul-assoc", x, y, z))
            if mulz(x, addz(y, z)) != addz(mulz(x, y), mulz(x, z)):
                fails.append(("mul-distrib-l", x, y, z))
            if mulz(addz(x, y), z) != addz(mulz(x, z), mulz(y, z)):
                fails.append(("mul-distrib-r", x, y, z))

if fails:
    for f in fails[:10]:
        print("FAIL", f)
    print("ZOMEGA-ORACLE FAIL: %d violations" % len(fails))
    raise SystemExit(1)

print("ZOMEGA-ORACLE PASS: %d checks, 0 violations (grid %d elements)" % (checks, len(grid)))
print('ORACLE-MANIFEST {"basis": "Z[omega]=Z^2 with omega^2=-1-omega, exact integers", "domain": %d, "points": %d, "claim": "addZomega/mulZomega ring laws (assoc/comm/distrib/zero/unit/inverse) hold on the full 25-element grid {-2..2}^2, all cases checked"}' % (checks, checks))
