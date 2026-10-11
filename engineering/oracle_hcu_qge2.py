# 线1 q≥2 分支先算后验证（精确整数，禁浮点）：
#   命题：x = 1 + q·M，M = 3¹¹·2¹⁵，N = SOVEREIGN_LCM = 3¹¹·2¹⁶
#   ① 2·M ≡ N（= 探针里 A+A≡N 的字面归约）② root₅ ≡ 1 + M（q=1 分支）
#   ③ q ≥ 2 → x ≥ 1 + 2·M = 1 + N > N（与 x < N 矛盾）④ q ∈ {0,1} → x < N
import json

M = 3**11 * 2**15
N = 3**11 * 2**16
SOVEREIGN_LCM = 177147 * 65536
root5 = 5804752897
root1 = 1

assert 2 * M == N, (2 * M, N)
assert SOVEREIGN_LCM == N, (SOVEREIGN_LCM, N)
assert 3**11 * 2**15 + 3**11 * 2**15 == SOVEREIGN_LCM          # A + A ≡ N（refl 级断言）
assert 1 + M == root5                                          # q=1 分支
assert 1 + 0 * M == root1                                      # q=0 分支
points = 0
for q in range(0, 12):
    x = 1 + q * M
    if q >= 2:
        assert x >= 1 + 2 * M == 1 + N > N, (q, x)             # q≥2 → x > N 矛盾
        assert not (x < N), (q, x)
    else:
        assert x < N, (q, x)
    points += 1

print("q>=2 branch verified: 2M=N, root5=1+M, q>=2 => x>N")
print("ORACLE-MANIFEST", json.dumps({
    "basis": "exact-int",
    "domain": 12,
    "points": points,
    "claim": "qge2-branch: M=3^11*2^15, 2M=N=SOVEREIGN_LCM, root5=1+M, q>=2 -> 1+q*M >= 1+N > N",
}))
