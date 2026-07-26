#!/usr/bin/env python3
"""
Phase 4 验证: 全局矩阵 vs 逐点雅可比
用 GF(9)² 反例 F(x,y) = (x, y + α·y³) 验证:
1. 逐点雅可比 J(F) = I, det = 1 (盲区)
2. 全局函数表: 81 个输入 → 81 个输出, 非双射 (3-to-1)
3. 拉回矩阵 F*: 81×81, det(F*) = 0 (检测到非单射)
"""

# GF(9) 算术 (复用 Phase 2)
GF9_ELEMENTS = [(a, b) for a in range(3) for b in range(3)]
GF9_ZERO = (0, 0)
GF9_ONE = (1, 0)
GF9_ALPHA = (0, 1)

def gf9_add(x, y): return ((x[0]+y[0])%3, (x[1]+y[1])%3)
def gf9_neg(x): return ((-x[0])%3, (-x[1])%3)
def gf9_mul(x, y):
    a,b = x; c,d = y
    return ((a*c + 2*b*d)%3, (a*d + b*c)%3)
def gf9_pow(x, n):
    r = GF9_ONE
    for _ in range(n): r = gf9_mul(r, x)
    return r

GF9_2 = [((a1,b1),(a2,b2)) for a1 in range(3) for b1 in range(3)
         for a2 in range(3) for b2 in range(3)]

# 反例: F(x,y) = (x, y + α·y³)
def F(p):
    x, y = p
    y3 = gf9_pow(y, 3)  # Frobenius σ(y)
    return (x, gf9_add(y, gf9_mul(GF9_ALPHA, y3)))

# ============================================================
# 1. 逐点雅可比 (char 3 盲区)
# ============================================================
print("=" * 60)
print("1. 逐点雅可比: J(F) 在每个点上的值")
print("=" * 60)
print()
print("F(x,y) = (x, y + α·y³)")
print("∂F₁/∂x = 1,  ∂F₁/∂y = 0")
print("∂F₂/∂x = 0,  ∂F₂/∂y = 1 + α·3y² = 1 + 0 = 1  (char 3!)")
print()
print("J(F) = [[1,0],[0,1]] = I  在全部 81 个点上")
print("det J(F) = 1  ← 逐点雅可比条件完美满足")
print("但 F 不是双射!  ← Frobenius 盲区")

# ============================================================
# 2. 全局函数表
# ============================================================
print()
print("=" * 60)
print("2. 全局函数表: 81 个输入 → 输出")
print("=" * 60)

image_map = {}  # output -> [inputs]
for p in GF9_2:
    fp = F(p)
    if fp not in image_map:
        image_map[fp] = []
    image_map[fp].append(p)

image_size = len(image_map)
collisions = {k: v for k, v in image_map.items() if len(v) > 1}

print(f"输入点数:   81")
print(f"不同像点数: {image_size}")
print(f"碰撞像点:   {len(collisions)} 个 (每个有 3 个原像)")
print(f"双射?       {'是' if image_size == 81 else '否 ← 非双射!'}")
print()

# 展示碰撞结构
print("碰撞结构 (前 5 个):")
for target, sources in list(collisions.items())[:5]:
    print(f"  {target} ← {sources}")

# ============================================================
# 3. 拉回矩阵 F* (81×81 over GF(3))
# ============================================================
print()
print("=" * 60)
print("3. 拉回矩阵 F*: 81×81 over GF(3)")
print("=" * 60)
print()
print("F* 作用于函数空间: (F*g)(p) = g(F(p))")
print("F* 的矩阵: M[i][j] = 1 if F(point_j) = point_i, else 0")
print("(这是 F 作为集合映射的邻接矩阵)")
print()

# 构建 81×81 矩阵 (over GF(3), 但这里用整数表示)
point_to_idx = {p: i for i, p in enumerate(GF9_2)}
M = [[0]*81 for _ in range(81)]

for j, p in enumerate(GF9_2):
    fp = F(p)
    i = point_to_idx[fp]
    M[i][j] = 1  # F maps point_j to point_i

# 检查: 每列恰好一个 1 (函数性质)
col_sums = [sum(M[i][j] for i in range(81)) for j in range(81)]
assert all(s == 1 for s in col_sums), "每列应恰好一个 1"

# 检查: 每行的 1 的个数 = 原像大小
row_sums = [sum(M[i][j] for j in range(81)) for i in range(81)]
print(f"行和分布: min={min(row_sums)}, max={max(row_sums)}")
print(f"  行和=0 (不在像中): {row_sums.count(0)} 行")
print(f"  行和=1 (单原像):   {row_sums.count(1)} 行")
print(f"  行和=3 (三原像):   {row_sums.count(3)} 行")
print()

# 行列式 (over GF(3))
def det_gf3(mat, n):
    """计算 n×n 矩阵在 GF(3) 上的行列式"""
    # 复制矩阵
    A = [row[:] for row in mat]
    det = 1
    for col in range(n):
        # 找主元
        pivot = -1
        for row in range(col, n):
            if A[row][col] % 3 != 0:
                pivot = row
                break
        if pivot == -1:
            return 0  # 奇异
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            det = (-det) % 3
        # 消元
        inv_pivot = pow(A[col][col] % 3, -1, 3)
        det = (det * A[col][col]) % 3
        for row in range(col+1, n):
            if A[row][col] % 3 != 0:
                factor = (A[row][col] * inv_pivot) % 3
                for k in range(col, n):
                    A[row][k] = (A[row][k] - factor * A[col][k]) % 3
    return det % 3

det_M = det_gf3(M, 81)
print(f"det(F*) over GF(3) = {det_M}")
print(f"F* 可逆? {'是' if det_M != 0 else '否 ← 全局矩阵检测到非单射!'}")

# ============================================================
# 4. 对比: 双射映射的全局矩阵
# ============================================================
print()
print("=" * 60)
print("4. 对比: 恒等映射的全局矩阵")
print("=" * 60)

M_id = [[0]*81 for _ in range(81)]
for i in range(81):
    M_id[i][i] = 1

det_id = det_gf3(M_id, 81)
print(f"det(I₈₁) over GF(3) = {det_id}")
print(f"恒等映射可逆? {'是' if det_id != 0 else '否'}")

# ============================================================
# 5. 结论
# ============================================================
print()
print("=" * 60)
print("5. 结论: 逐点 vs 全局")
print("=" * 60)
print()
print("逐点雅可比:  det J(F)(p) = 1  在全部 81 个点上  ← 盲区!")
print(f"全局矩阵:    det(F*) = {det_M} over GF(3)          ← 检测到非单射!")
print()
print("逐点雅可比是连续统的妥协产物 (无穷维, 只能逐点近似)")
print("全局矩阵是离散环面的自然表述 (有限维, 精确判定)")
print()
print("Frobenius 盲区:")
print("  ∂(y³)/∂y = 3y² = 0 (char 3)  → 逐点看不见")
print("  但 F* 的行和 = 3 (三原像)     → 全局矩阵看得见")
