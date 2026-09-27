# ORACLE: Pi4.L4 —— π4 同态（CRT 第 4 腿）先算后验证
# 陈述: ∀ x y : Duodec → π4 (x +12 y) ≡ π4 x +4 π4 y
#   其中 +12 = mod-12 加法, π4 = mod-4 投影, _+4_ = Fin4 上按 suc4 迭代的加法
# 背景: 4 | 12 ⇒ ℤ/12 → ℤ/4 环同态（CRT 腿）; 穷举域 12×12 = 144
basis = "Duodec = Z/12, π4 = mod-4 投影, _+4_ = Fin4 suc4-迭代加法"

def suc4(i):
    return (i + 1) % 4

def add4(u, v):
    for _ in range(u):
        v = suc4(v)
    return v

domain = 12 * 12
points = 0
fail = 0
for x in range(12):
    for y in range(12):
        points += 1
        lhs = (x + y) % 12 % 4          # π4 (x +12 y)
        rhs = add4(x % 4, y % 4)        # π4 x +4 π4 y
        if lhs != rhs:
            fail += 1
            print("ADD FAIL", x, y, lhs, rhs)
# 附: *12 乘法腿同检 (π4 (x *12 y) ≡ π4 x *4 π4 y, *4 = mod-4 乘)
def mul4(u, v):
    return (u * v) % 4
fail2 = 0
for x in range(12):
    for y in range(12):
        lhs = (x * y) % 12 % 4
        rhs = mul4(x % 4, y % 4)
        if lhs != rhs:
            fail2 += 1
            print("MUL FAIL", x, y, lhs, rhs)
print("add-leg fails:", fail, " mul-leg fails:", fail2)
import json
print("ORACLE-MANIFEST " + json.dumps({
    "basis": basis,
    "domain": domain,
    "points": points,
    "claim": "π4 环同态: π4(x+12 y)=π4 x +4 π4 y 且 π4(x*12 y)=π4 x *4 π4 y (12x12 全域)"
}))
