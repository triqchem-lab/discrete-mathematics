#!/usr/bin/env python3
"""
GF(9)^2 上的 BCW 三次齐次映射穷举搜索
雅可比猜想在离散有限域中的 Phase 2 实验

数学背景:
- GF(9) = GF(3)[α]/(α²+1), Frobenius σ(x) = x³ ≠ x
- BCW 规约: F = X + H, H 三次齐次, J(H) 幂零
- 特征 3: ∂(x³)/∂x = 3x² = 0, 纯三次项对雅可比不可见
- BCW 条件 det(I+J(H))=1 给出: b₂=0, c₁=0, c₂=-b₁
- 搜索空间: 9 × 9⁴ = 59,049 (从 9⁸=43M 坍缩)
"""

# ============================================================
# GF(9) 算术: GF(3)[α]/(α²+1), 元素 = (a, b) 表示 a + bα
# ============================================================

GF9_ELEMENTS = [(a, b) for a in range(3) for b in range(3)]

def gf9_add(x, y):
    return ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3)

def gf9_neg(x):
    return ((-x[0]) % 3, (-x[1]) % 3)

def gf9_mul(x, y):
    # (a+bα)(c+dα) = (ac + 2bd) + (ad+bc)α  (因为 α²=-1=2 in GF(3))
    a, b = x
    c, d = y
    return ((a*c + 2*b*d) % 3, (a*d + b*c) % 3)

def gf9_sub(x, y):
    return gf9_add(x, gf9_neg(y))

def gf9_eq(x, y):
    return x[0] == y[0] and x[1] == y[1]

GF9_ZERO = (0, 0)
GF9_ONE = (1, 0)
GF9_ALPHA = (0, 1)  # α

def gf9_pow(x, n):
    """x^n in GF(9)"""
    result = GF9_ONE
    base = x
    while n > 0:
        if n % 2 == 1:
            result = gf9_mul(result, base)
        base = gf9_mul(base, base)
        n //= 2
    return result

def gf9_frobenius(x):
    """σ(x) = x³ (Frobenius automorphism)"""
    return gf9_pow(x, 3)

# ============================================================
# GF(9)² 上的点
# ============================================================

GF9_2_POINTS = [((a1, b1), (a2, b2))
                for a1 in range(3) for b1 in range(3)
                for a2 in range(3) for b2 in range(3)]

assert len(GF9_2_POINTS) == 81

# ============================================================
# BCW 三次齐次映射
# H₁(x,y) = a₁x³ + b₁x²y + c₁xy² + d₁y³
# H₂(x,y) = a₂x³ + b₂x²y + c₂xy² + d₂y³
# F(x,y) = (x + H₁(x,y), y + H₂(x,y))
# ============================================================

def eval_cubic(coeffs, x, y):
    """计算三次齐次多项式 a·x³ + b·x²y + c·xy² + d·y³"""
    a, b, c, d = coeffs
    x2 = gf9_mul(x, x)
    x3 = gf9_mul(x2, x)
    y2 = gf9_mul(y, y)
    y3 = gf9_mul(y2, y)
    x2y = gf9_mul(x2, y)
    xy2 = gf9_mul(x, y2)

    result = GF9_ZERO
    result = gf9_add(result, gf9_mul(a, x3))
    result = gf9_add(result, gf9_mul(b, x2y))
    result = gf9_add(result, gf9_mul(c, xy2))
    result = gf9_add(result, gf9_mul(d, y3))
    return result

def eval_bcw_map(a1, b1, c1, d1, a2, b2, c2, d2, x, y):
    """F(x,y) = (x + H₁(x,y), y + H₂(x,y))"""
    h1 = eval_cubic((a1, b1, c1, d1), x, y)
    h2 = eval_cubic((a2, b2, c2, d2), x, y)
    return (gf9_add(x, h1), gf9_add(y, h2))

def check_bijective(a1, b1, c1, d1, a2, b2, c2, d2):
    """检查 F 在 GF(9)² 的 81 个点上是否为双射"""
    images = set()
    for x, y in GF9_2_POINTS:
        fx, fy = eval_bcw_map(a1, b1, c1, d1, a2, b2, c2, d2, x, y)
        images.add((fx, fy))
    return len(images) == 81

# ============================================================
# 主搜索
# ============================================================

def main():
    print("=" * 70)
    print("GF(9)² BCW 三次齐次映射穷举搜索")
    print("雅可比猜想 Phase 2: 离散有限域实验")
    print("=" * 70)

    # BCW 条件: b₂=0, c₁=0, c₂=-b₁
    # b₁ 自由 (9 choices), a₁,d₁,a₂,d₂ 自由 (9⁴ = 6561 choices)

    total_maps = 0
    bijective_maps = 0
    non_bijective_maps = 0
    non_bijective_examples = []

    ZERO = GF9_ZERO

    for b1 in GF9_ELEMENTS:
        c1 = ZERO           # BCW 条件
        b2 = ZERO           # BCW 条件
        c2 = gf9_neg(b1)    # BCW 条件: c₂ = -b₁

        for a1 in GF9_ELEMENTS:
            for d1 in GF9_ELEMENTS:
                for a2 in GF9_ELEMENTS:
                    for d2 in GF9_ELEMENTS:
                        total_maps += 1

                        if check_bijective(a1, b1, c1, d1, a2, b2, c2, d2):
                            bijective_maps += 1
                        else:
                            non_bijective_maps += 1
                            if len(non_bijective_examples) < 5:
                                non_bijective_examples.append(
                                    (a1, b1, c1, d1, a2, b2, c2, d2))

                        if total_maps % 10000 == 0:
                            print(f"  进度: {total_maps}/59049 "
                                  f"(双射={bijective_maps}, 非双射={non_bijective_maps})")

    print()
    print("=" * 70)
    print("搜索结果")
    print("=" * 70)
    print(f"总映射数:     {total_maps}")
    print(f"双射映射:     {bijective_maps} ({100*bijective_maps/total_maps:.1f}%)")
    print(f"非双射映射:   {non_bijective_maps} ({100*non_bijective_maps/total_maps:.1f}%)")
    print()

    if non_bijective_maps > 0:
        print("⚠️  发现非双射 BCW 映射！雅可比条件满足但 F 不是双射！")
        print("    这是 GF(9) 上的雅可比猜想反例！")
        print()
        for i, (a1, b1, c1, d1, a2, b2, c2, d2) in enumerate(non_bijective_examples):
            print(f"  反例 {i+1}:")
            print(f"    H₁ = {a1}·x³ + {b1}·x²y + {c1}·xy² + {d1}·y³")
            print(f"    H₂ = {a2}·x³ + {b2}·x²y + {c2}·xy² + {d2}·y³")

            # 找到碰撞的点
            images = {}
            for x, y in GF9_2_POINTS:
                fx, fy = eval_bcw_map(a1, b1, c1, d1, a2, b2, c2, d2, x, y)
                key = (fx, fy)
                if key not in images:
                    images[key] = []
                images[key].append((x, y))

            collisions = {k: v for k, v in images.items() if len(v) > 1}
            for target, sources in list(collisions.items())[:3]:
                print(f"    {len(sources)} 个点映射到 {target}: {sources[:4]}")
            print()
    else:
        print("✅ 所有 59,049 个 BCW 映射都是双射！")
        print("   GF(9)² 上的 BCW 三次齐次雅可比猜想成立。")
        print()
        print("   解读: 在 GF(9)² (81 点) 上，det J(F) = 1 (BCW 条件)")
        print("   蕴含 F 是双射。这与连续统 C² 的二维雅可比猜想")
        print("   (仍然开放) 形成对比。")

    # Frobenius 分析
    print()
    print("=" * 70)
    print("Frobenius 分析: σ(x) = x³ 在 GF(9) 上的行为")
    print("=" * 70)
    for x in GF9_ELEMENTS:
        sx = gf9_frobenius(x)
        fixed = "不动" if gf9_eq(x, sx) else ""
        print(f"  σ({x}) = {sx}  {fixed}")

    fixed_count = sum(1 for x in GF9_ELEMENTS if gf9_eq(x, gf9_frobenius(x)))
    print(f"\n  Frobenius 不动点: {fixed_count}/9 (即 GF(3) 嵌入)")
    print(f"  非平凡轨道: {(9 - fixed_count) // 2} 个 (大小 2)")

if __name__ == "__main__":
    main()
