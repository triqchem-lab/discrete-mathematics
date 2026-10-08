# ORACLE: Burau B3 braid 关系精确整数核对（3x3 与 2x2 双验）
def matmul(A, B):
    n = len(A); m = len(B[0]); k = len(B)
    return [[sum(A[i][l]*B[l][j] for l in range(k)) for j in range(m)] for i in range(n)]

def check(t):
    # 标准 Burau: sigma_i = I_{i-1} ⊕ [[1-t, t],[1, 0]] ⊕ I_{n-i-1}
    s1 = [[1,0,0],[0,1-t,t],[0,1,0]]
    s2 = [[1-t,t,0],[1,0,0],[0,0,1]]
    L = matmul(matmul(s1,s2),s1); R = matmul(matmul(s2,s1),s2)
    ok3 = L == R
    # 2x2 变体（待排除）
    a = [[1-t,1],[1,0]]; b = [[1,0],[t,1-t]]
    L2 = matmul(matmul(a,b),a); R2 = matmul(matmul(b,a),b)
    ok2 = L2 == R2
    return ok3, ok2, L, R

all3 = all(check(t)[0] for t in range(-6, 7))
all2 = all(check(t)[1] for t in range(-6, 7))
print("ORACLE-MANIFEST {\"basis\":\"Burau B3 braid: sigma1*sigma2*sigma1 ?= sigma2*sigma1*sigma2, exact integer t in [-6,6]\",\"domain\":13,\"points\":13,\"claim\":\"3x3 standard Burau satisfies braid; 2x2 variant does not\"}")
print("3x3 braid holds for all t:", all3)
print("2x2 variant holds for all t:", all2, "(expected False)")
_, _, L, R = check(0)
print("t=0 3x3 L =", L); print("t=0 3x3 R =", R)
assert all3 and not all2
