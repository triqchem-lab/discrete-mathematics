/* duodec_verify.c
 * CompCert 3.17 验证「律算合一」12进制数学库核心算法
 * 对照 Agda 定理 (/data/work/discrete-mathematics/src/Sovereign)：
 *   Base/Trit.agda              — GF(3) char-3 加法表
 *   Algebra/GroupTheory/DuodecClock.agda — AlphaPower mulAlpha 16-case
 *   Algebra/GF9.agda            — GF(9) 域: α²=-1, α⁴=1, 范数 N(a+bα)=a²+b²
 *   Algebra/Duodecimal.agda     — Duodec Z/12, CRT roundtrip
 *   Algebra/DiscreteFibonacci.agda — φ=1+2α: φ²=α, φ⁸=1
 * 运行: 全部断言 PASS 且 CompCert/gcc 输出一致 = 编译正确 + 算法正确
 */

#include <stdio.h>

static int failures = 0;
#define CHECK(cond, msg) do { \
    if (cond) printf("PASS: %s\n", msg); \
    else { printf("FAIL: %s\n", msg); failures++; } \
} while (0)

/* ---------- §1 Trit: GF(3) ---------- */
typedef unsigned char Trit;              /* 0,1,2 */
static Trit trit_add(Trit a, Trit b) { return (Trit)((a + b) % 3); }
static Trit trit_mul(Trit a, Trit b) { return (Trit)((a * b) % 3); }
static Trit trit_neg(Trit a) { return (Trit)((3 - a) % 3); }

/* ---------- §3 GF(9) = GF(3)×GF(3), code = a*3+b, 元素 a+bα, α²=-1 ---------- */
static unsigned char gf9_mul(unsigned char x, unsigned char y) {
    Trit a = (Trit)(x / 3), b = (Trit)(x % 3);
    Trit c = (Trit)(y / 3), d = (Trit)(y % 3);
    /* (a+bα)(c+dα) = (ac-bd) + (ad+bc)α, 减法 = 加法取负 */
    Trit ac = trit_mul(a, c), bd = trit_mul(b, d);
    Trit ad = trit_mul(a, d), bc = trit_mul(b, c);
    return (unsigned char)(trit_add(ac, trit_neg(bd)) * 3 + trit_add(ad, bc));
}
static unsigned char gf9_norm(unsigned char x) { /* N(a+bα)=a²+b² */
    Trit a = (Trit)(x / 3), b = (Trit)(x % 3);
    return (unsigned char)(trit_add(trit_mul(a, a), trit_mul(b, b)));
}
#define GF9_ALPHA  1u   /* 0+1α */
#define GF9_ONE    3u   /* 1+0α */
#define GF9_NEGONE 6u   /* 2+0α = -1 */
#define GF9_NEGALPHA 2u /* 0+2α = -α */

/* ---------- §2 AlphaPower: ⟨α⟩ = {α⁰,α¹,α²,α³} ---------- */
static unsigned char mulAlpha(unsigned char i, unsigned char j) {
    return (unsigned char)((i + j) % 4);   /* α^i·α^j = α^{(i+j) mod 4} */
}
static unsigned char alphaInv(unsigned char i) {
    return (unsigned char)((4 - i) % 4);   /* (α^i)⁻¹ = α^{-i mod 4} */
}
static unsigned char alphaPowerToGF9(unsigned char i) { /* a_i ↦ α^i */
    unsigned char p = GF9_ONE;
    unsigned char k;
    for (k = 0; k < i; k++) p = gf9_mul(p, GF9_ALPHA);
    return p;
}

/* ---------- §4 Duodec: Z/12, CRT (π3: mod 3, π4: mod 4) ---------- */
static unsigned char crt12(unsigned char r3, unsigned char r4) {
    /* x ≡ r3 (mod 3), x ≡ r4 (mod 4), 0<=x<12
     * x = (4·r3·1 + 3·r4·3) mod 12,  4⁻¹≡1 (mod 3), 3⁻¹≡3 (mod 4) */
    return (unsigned char)((4 * r3 + 9 * r4) % 12);
}

/* ---------- §5 φ = 1+2α ∈ GF(9), 8 阶元 ---------- */
#define GF9_PHI 5u

/* ---------- §7 DuodecClock: 12 元素混合时钟 DuodecPoint = Trit × AlphaPower
 * 对照 Agda: mixedOp (x,a) (y,b) = (x⊕y, mulAlpha a b)
 *            duodec-e = (T₀,a0); duodec-inv (x,a) = (negate x, alphaInv a)
 *            toDuodec = crt12 (trit) (alpha), fromDuodec n = (π3 n, π4 n)
 * ---------- */
typedef unsigned char DuodecP;           /* code = trit*4 + alpha, 0..11 */
static Trit dp_trit(DuodecP p) { return (Trit)(p / 4); }
static unsigned char dp_alpha(DuodecP p) { return (unsigned char)(p % 4); }
static DuodecP dp_make(Trit t, unsigned char a) { return (DuodecP)(t * 4 + a); }
static DuodecP mixedOp(DuodecP p, DuodecP q) {
    return dp_make(trit_add(dp_trit(p), dp_trit(q)),
                   mulAlpha(dp_alpha(p), dp_alpha(q)));
}
static DuodecP duodec_inv(DuodecP p) {
    return dp_make(trit_neg(dp_trit(p)), alphaInv(dp_alpha(p)));
}
#define DUODEC_E 0u                      /* (T₀, a0) */
static unsigned char toDuodec(DuodecP p) {
    return crt12(dp_trit(p), dp_alpha(p));   /* (4·x + 9·a) mod 12 */
}
static DuodecP fromDuodec(unsigned char n) {
    return dp_make((Trit)(n % 3), (unsigned char)(n % 4));  /* (π3, π4) */
}

int main(void) {
    unsigned char i, j;

    printf("=== §1 Trit (GF(3)): char-3 加法表 ===\n");
    for (i = 0; i < 3; i++)
        for (j = 0; j < 3; j++) {
            char buf[64];
            snprintf(buf, sizeof buf, "trit_add(%u,%u)=%u", i, j, (i + j) % 3);
            CHECK(trit_add(i, j) == (i + j) % 3, buf);
        }
    CHECK(trit_add(1, 2) == 0, "T1⊕T2=T0 (char-3 归零)");
    CHECK(trit_add(2, 2) == 1, "T2⊕T2=T1 (char-3 归零)");
    CHECK(trit_neg(1) == 2 && trit_neg(2) == 1, "negate: -1=2, -2=1");

    printf("=== §2 AlphaPower: mulAlpha 16-case 表 ===\n");
    for (i = 0; i < 4; i++)
        for (j = 0; j < 4; j++) {
            char buf[64];
            snprintf(buf, sizeof buf, "α^%u·α^%u = α^%u", i, j, (i + j) % 4);
            CHECK(mulAlpha(i, j) == (i + j) % 4, buf);
        }
    CHECK(alphaInv(0) == 0 && alphaInv(1) == 3 && alphaInv(2) == 2 && alphaInv(3) == 1,
          "alphaInv: a0↔a0, a1↔a3, a2↔a2");

    printf("=== §3 GF(9): α²=-1, α³=-α, α⁴=1 ===\n");
    CHECK(gf9_mul(GF9_ALPHA, GF9_ALPHA) == GF9_NEGONE, "α² = -1");
    CHECK(gf9_mul(gf9_mul(GF9_ALPHA, GF9_ALPHA), GF9_ALPHA) == GF9_NEGALPHA, "α³ = -α");
    CHECK(alphaPowerToGF9(4) == GF9_ONE, "α⁴ = 1");
    CHECK(gf9_mul(GF9_NEGONE, GF9_NEGONE) == GF9_ONE, "(-1)² = 1");

    printf("=== §3b mulAlpha-hom: ⟨α⟩ 嵌入 GF(9) 保乘法 (16 case) ===\n");
    for (i = 0; i < 4; i++)
        for (j = 0; j < 4; j++) {
            char buf[64];
            snprintf(buf, sizeof buf, "hom(α^%u·α^%u) = hom(α^%u)·hom(α^%u)", i, j, i, j);
            CHECK(alphaPowerToGF9(mulAlpha(i, j)) ==
                  gf9_mul(alphaPowerToGF9(i), alphaPowerToGF9(j)), buf);
        }

    printf("=== §3c 范数 N(a+bα)=a²+b² (9 元素全查) ===\n");
    for (i = 0; i < 9; i++) {
        char buf[64];
        snprintf(buf, sizeof buf, "N(gf9[%u]) = a²+b²", i);
        CHECK(gf9_norm(i) ==
              trit_add(trit_mul(i / 3, i / 3), trit_mul(i % 3, i % 3)), buf);
    }

    printf("=== §4 Duodec: CRT roundtrip (12 项) ===\n");
    for (i = 0; i < 12; i++) {
        char buf[64];
        snprintf(buf, sizeof buf, "crt12(π3(%u),π4(%u)) = %u", i, i, i);
        CHECK(crt12(i % 3, i % 4) == i, buf);
    }
    CHECK((2 * 6) % 12 == 0, "R12 有零因子: 2·6≡0 (mod 12), 非域");
    CHECK(crt12(0, 1) == 9 && crt12(2, 2) == 2, "crt12 样例");

    printf("=== §5 φ=1+2α: φ²=α, φ⁴=-1, φ⁸=1 ===\n");
    CHECK(gf9_mul(GF9_PHI, GF9_PHI) == GF9_ALPHA, "φ² = α");
    CHECK(alphaPowerToGF9(2) == GF9_NEGONE, "α² = -1 (φ² 的平方 = -1 之半)");
    {
        unsigned char p4 = gf9_mul(gf9_mul(GF9_PHI, GF9_PHI), gf9_mul(GF9_PHI, GF9_PHI));
        unsigned char p8 = gf9_mul(p4, p4);
        CHECK(p4 == GF9_NEGONE, "φ⁴ = -1");
        CHECK(p8 == GF9_ONE, "φ⁸ = 1");
        CHECK(p4 != GF9_ONE && p8 == GF9_ONE, "φ 阶 = 8 (φ⁴≠1 且 φ⁸=1)");
    }

    printf("=== §6 宪法常量: 3¹¹, 2¹⁶, M = 3¹¹×2¹⁶ ===\n");
    {
        unsigned long long p3 = 1, p2 = 1;
        int k;
        for (k = 0; k < 11; k++) p3 *= 3;
        for (k = 0; k < 16; k++) p2 *= 2;
        CHECK(p3 == 177147ull, "3¹¹ = 177147");
        CHECK(p2 == 65536ull, "2¹⁶ = 65536");
        CHECK(p3 * p2 == 11609505792ull, "M = 3¹¹×2¹⁶ = 11609505792");
    }

    printf("=== §7 DuodecClock: 12 元素混合时钟 (加乘联合) ===\n");
    {
        unsigned char p, q, r, n, bad;
        /* 单位元: mixedOp(e,p)=p, mixedOp(p,e)=p */
        bad = 0;
        for (p = 0; p < 12; p++)
            if (mixedOp(DUODEC_E, p) != p || mixedOp(p, DUODEC_E) != p) bad++;
        CHECK(bad == 0, "单位元: mixedOp(e,p)=mixedOp(p,e)=p (12×2)");

        /* 逆元: mixedOp(p, inv(p)) = e */
        bad = 0;
        for (p = 0; p < 12; p++)
            if (mixedOp(p, duodec_inv(p)) != DUODEC_E) bad++;
        CHECK(bad == 0, "逆元: mixedOp(p,duodec-inv(p))=e (12)");

        /* 交换律: mixedOp(p,q)=mixedOp(q,p) */
        bad = 0;
        for (p = 0; p < 12; p++)
            for (q = 0; q < 12; q++)
                if (mixedOp(p, q) != mixedOp(q, p)) bad++;
        CHECK(bad == 0, "交换律 (144)");

        /* 结合律: mixedOp(mixedOp(p,q),r)=mixedOp(p,mixedOp(q,r)) 穷举 12³ */
        bad = 0;
        for (p = 0; p < 12; p++)
            for (q = 0; q < 12; q++)
                for (r = 0; r < 12; r++)
                    if (mixedOp(mixedOp(p, q), r) != mixedOp(p, mixedOp(q, r))) bad++;
        CHECK(bad == 0, "结合律穷举 12³=1728 (mixedOp-assoc)");

        /* CRT 同构 roundtrip: toDuodec(fromDuodec n)=n, fromDuodec(toDuodec p)=p */
        bad = 0;
        for (n = 0; n < 12; n++)
            if (toDuodec(fromDuodec(n)) != n) bad++;
        CHECK(bad == 0, "roundtrip: toDuodec∘fromDuodec = id (12)");
        bad = 0;
        for (p = 0; p < 12; p++)
            if (fromDuodec(toDuodec(p)) != p) bad++;
        CHECK(bad == 0, "roundtrip: fromDuodec∘toDuodec = id (12)");

        /* 群同态: toDuodec(mixedOp(p,q)) = (toDuodec p + toDuodec q) mod 12
         * = 混合时钟 ≅ Z/12 加法群同构 (crt12 正交分解) */
        bad = 0;
        for (p = 0; p < 12; p++)
            for (q = 0; q < 12; q++)
                if (toDuodec(mixedOp(p, q)) != (unsigned char)((toDuodec(p) + toDuodec(q)) % 12)) bad++;
        CHECK(bad == 0, "群同态: toDuodec(mixedOp(p,q)) = toDuodec(p)+12 toDuodec(q) (144)");

        /* 12 进制数字样例: 0..11 的加法表前几项直接检查 */
        CHECK(mixedOp(dp_make(1, 0), dp_make(2, 0)) == dp_make(0, 0), "T1⊕T2 归零 (trit 分量)");
        CHECK(mixedOp(dp_make(0, 1), dp_make(0, 2)) == dp_make(0, 3), "α¹·α²=α³ (旋转分量)");
        CHECK(mixedOp(dp_make(1, 3), dp_make(2, 1)) == dp_make(0, 0), "混合: (1,α³)⊕(2,α¹)=(0,a0)");
    }

    printf("\n========================================\n");
    if (failures == 0)
        printf("RESULT: ALL PASS\n");
    else
        printf("RESULT: %d FAILURES\n", failures);
    return failures;
}
