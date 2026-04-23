/* ============================================================================
 * 定点数复数类型 - Fixed-Point Complex Numbers (Sovereign Edition)
 *
 * 版本：v2.5-宪法锁定 (中性文明层级)
 * 状态：范畴完备，禁止浮点渗透
 *
 * 律算宪法定义：
 * - 身份：五行干涉表、手性翻转振幅、纳音驻波相位的数学载体。
 * - 基底：32-bit 有符号整数 (int32_t)，定点 Q16.16 格式。
 * - 缩放因子：FIXED_SCALE = 2^16 = 65536。
 * - 禁止：在任何运行时逻辑中使用 float/double 构造或运算。
 *
 * 数学结构：
 * z = re + i·im,  其中 re, im ∈ ℤ, 实际值 = re / FIXED_SCALE
 * 模长平方 |z|² = (re² + im²) / FIXED_SCALE
 *
 * 知识图谱映射：
 * - 根数学：能量相位 (ℤ₁₂ 环结构)
 * - 结构学：复平面几何（极向/环向缠绕的投影）
 * - 耦合域：五行相生相克的复振幅叠加 (+1, ω, ω²)
 * ============================================================================ */

#ifndef SOVEREIGN_FIXED_COMPLEX_H
#define SOVEREIGN_FIXED_COMPLEX_H

#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

/* ══════════════════════════════════════════════════════════════════════
 * 1. 宪法常量 (Constitutional Constants)
 * ══════════════════════════════════════════════════════════════════════ */

/** 
 * 缩放因子：2^16 = 65536
 * 对应 UE8M0 格式中的 E=16，实现定点数与主权 LCM 模运算的对齐。
 */
#define FIXED_SCALE (1 << 16)
#define FIXED_SCALE_HALF (1 << 15)

/* ℤ₁₂ 相位常量 (对应十二律损益相位) */
#define PHASE_MODULUS 12
#define PHASE_HUANGZHONG 0  /* 黄钟基准相位 */

/* 五行相生/相克复振幅预计算值 (Q16.16) */
#define AMP_SHENG_RE  FIXED_SCALE     /* +1 (相生) */
#define AMP_SHENG_IM  0
#define AMP_KE_RE     (-FIXED_SCALE / 2)  /* -0.5 (相克 ω 的实部) */
#define AMP_KE_IM     56632             /* +0.866 (相克 ω 的虚部，sqrt(3)/2 * 65536) */

/* ══════════════════════════════════════════════════════════════════════
 * 2. 定点数复数结构 (Fixed-Point Complex Structure)
 * ══════════════════════════════════════════════════════════════════════ */

typedef struct {
    int32_t re;  /* 定点数实部 (实际值 = re / FIXED_SCALE) */
    int32_t im;  /* 定点数虚部 (实际值 = im / FIXED_SCALE) */
} sov_fixed_complex_t;

/* ══════════════════════════════════════════════════════════════════════
 * 3. 构造函数 (Constitutional Constructors)
 * ══════════════════════════════════════════════════════════════════════ */

/** 零复数 0 + 0i */
static inline sov_fixed_complex_t fc_zero(void) {
    sov_fixed_complex_t z = {0, 0};
    return z;
}

/** 单位复数 1 + 0i */
static inline sov_fixed_complex_t fc_one(void) {
    sov_fixed_complex_t z = {FIXED_SCALE, 0};
    return z;
}

/** 纯虚数单位 i */
static inline sov_fixed_complex_t fc_unit_i(void) {
    sov_fixed_complex_t z = {0, FIXED_SCALE};
    return z;
}

/** 从整数构造 (自动缩放) */
static inline sov_fixed_complex_t fc_from_int(int32_t r, int32_t i) {
    sov_fixed_complex_t z = {r * FIXED_SCALE, i * FIXED_SCALE};
    return z;
}

/** 从定点数直接构造 */
static inline sov_fixed_complex_t fc_from_fixed(int32_t r, int32_t i) {
    sov_fixed_complex_t z = {r, i};
    return z;
}

/* ══════════════════════════════════════════════════════════════════════
 * 4. 宪法算术运算 (Constitutional Arithmetic)
 * ══════════════════════════════════════════════════════════════════════ */

/** 
 * 加法：z1 + z2
 * 对应五行干涉振幅的线性叠加。
 */
static inline sov_fixed_complex_t fc_add(sov_fixed_complex_t z1, sov_fixed_complex_t z2) {
    sov_fixed_complex_t res;
    res.re = z1.re + z2.re;
    res.im = z1.im + z2.im;
    return res;
}

/** 
 * 减法：z1 - z2
 * 对应相消干涉。
 */
static inline sov_fixed_complex_t fc_sub(sov_fixed_complex_t z1, sov_fixed_complex_t z2) {
    sov_fixed_complex_t res;
    res.re = z1.re - z2.re;
    res.im = z1.im - z2.im;
    return res;
}

/** 
 * 乘法：z1 × z2
 * (a+bi)(c+di) = (ac-bd) + i(ad+bc)
 * 注意：结果需要除以 FIXED_SCALE 以恢复 Q16.16 格式。
 * 对应复振幅的旋转与伸缩。
 */
static inline sov_fixed_complex_t fc_mul(sov_fixed_complex_t z1, sov_fixed_complex_t z2) {
    sov_fixed_complex_t res;
    int64_t re_64 = (int64_t)z1.re * z2.re - (int64_t)z1.im * z2.im;
    int64_t im_64 = (int64_t)z1.re * z2.im + (int64_t)z1.im * z2.re;
    
    /* 恢复缩放并四舍五入 */
    res.re = (int32_t)((re_64 + FIXED_SCALE_HALF) / FIXED_SCALE);
    res.im = (int32_t)((im_64 + FIXED_SCALE_HALF) / FIXED_SCALE);
    return res;
}

/** 
 * 共轭：z* = re - i·im
 * 对应手性翻转 (左旋 ↔ 右旋)。
 */
static inline sov_fixed_complex_t fc_conj(sov_fixed_complex_t z) {
    sov_fixed_complex_t res = {z.re, -z.im};
    return res;
}

/** 
 * 模长平方：|z|² = re² + im²
 * 返回值为 32-bit 整数 (已移除缩放因子的平方影响)。
 * 用于计算能隙 Δ=√3 的跃迁概率。
 */
static inline int32_t fc_norm_sq(sov_fixed_complex_t z) {
    int64_t re_sq = (int64_t)z.re * z.re;
    int64_t im_sq = (int64_t)z.im * z.im;
    int64_t norm_sq_64 = (re_sq + im_sq) / FIXED_SCALE; /* 移除一个缩放因子 */
    return (int32_t)norm_sq_64;
}

/** 
 * 模长近似：|z| ≈ max(|re|, |im|) + 0.4 * min(|re|, |im|)
 * 这是一个快速近似算法，避免耗时的开方运算。
 */
static inline int32_t fc_norm_approx(sov_fixed_complex_t z) {
    int32_t abs_re = (z.re >= 0) ? z.re : -z.re;
    int32_t abs_im = (z.im >= 0) ? z.im : -z.im;
    int32_t mx = (abs_re > abs_im) ? abs_re : abs_im;
    int32_t mn = (abs_re > abs_im) ? abs_im : abs_re;
    
    /* 0.4 近似为 13107/32768 ≈ 0.39999 */
    int32_t correction = (mn * 13107) >> 15;
    return mx + correction;
}

/* ══════════════════════════════════════════════════════════════════════
 * 5. 宪法预定义值 (Constitutional Presets)
 * ══════════════════════════════════════════════════════════════════════ */

/** 获取五行相生复振幅 (+1 + 0i) */
static inline sov_fixed_complex_t fc_amp_sheng(void) {
    sov_fixed_complex_t z = {AMP_SHENG_RE, AMP_SHENG_IM};
    return z;
}

/** 获取五行相克复振幅 (-0.5 + 0.866i = ω) */
static inline sov_fixed_complex_t fc_amp_ke(void) {
    sov_fixed_complex_t z = {AMP_KE_RE, AMP_KE_IM};
    return z;
}

/** 获取能隙 Δ=√3 对应的复振幅投影 (1.5 + 0.866i) - 仅用于校验 */
static inline sov_fixed_complex_t fc_gap_delta_ref(void) {
    /* 1.5 = 98304, 0.866 = 56632 */
    sov_fixed_complex_t z = {98304, 56632};
    return z;
}

#ifdef __cplusplus
}
#endif

#endif /* SOVEREIGN_FIXED_COMPLEX_H */
