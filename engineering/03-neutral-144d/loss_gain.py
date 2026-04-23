"""
Sovereign Core - 损益操作与 LCM 模运算
损一: 长度格点在 LCM 模环上的平行移动
益一: 长度格点在 LCM 模环上的平行移动
主权 LCM 模数: 3^11 * 2^16 = 11609505792

注意: 所有运算在 ℤ/LCM 模环上进行，非欧氏整数除法

============================================================
⚠️ 宪法层级声明：磁性文明层 (24 密度)
============================================================
GF(3) 合法身份: T⁶ 离散环面的极向缠绕模 12 与环向缠绕模 46 的
               初级商空间格点基底
使用范围:
  - 主权状态机的移宫转调损益序列
  - 十二律长度格点演化
  - 六十律纳音干支编码
禁止:
  - "GF(3) 加法" "GF(3) 乘法"
  - 使用浮点或连续统声学公式
============================================================
"""

from enum import Enum
from typing import List, Tuple


# 宪法常量
SOVEREIGN_LCM = 3**11 * 2**16  # 11609505792
POWER3_11 = 3**11               # 177147
POWER2_16 = 2**16               # 65536


class LossGain(Enum):
    """损益操作类型"""
    SUN = "损一"  # 极向缠绕相位滞后
    YI = "益一"   # 极向缠绕相位超前


# 十二律长度格点序列 (严格定义，非计算生成)
# 这些是 T⁶ 环面上的固定格点，非通过浮点运算获得
TWELVE_LU_LENGTHS = [81, 54, 72, 48, 64, 43, 57, 38, 51, 34, 45, 30]

# ============================================================
# 十二律 LCM 余数表 (宪法定义)
# 严格静态常量，禁止修改，禁止浮点近似
# 与仲吕闭合操作中的乘 3^11 右移 16 位保持数值一致
# ============================================================
TWELVE_LU_LCM = [177147, 118098, 157464, 104976, 139968,
                 93312, 124416, 82944, 110592, 73728, 98304, 65536]

# 损益映射表 (宪法定义): 步数 → (律名索引, 操作类型)
LOSS_GAIN_MAP = [
    (0, None),        # 黄钟: 基准
    (1, LossGain.SUN), # 林钟: 损一
    (2, LossGain.YI),  # 太簇: 益一
    (3, LossGain.SUN), # 南吕: 损一
    (4, LossGain.YI),  # 姑洗: 益一
    (5, LossGain.SUN), # 应钟: 损一
    (6, LossGain.YI),  # 蕤宾: 益一
    (7, LossGain.SUN), # 大吕: 损一
    (8, LossGain.YI),  # 夷则: 益一
    (9, LossGain.SUN), # 夹钟: 损一
    (10, LossGain.YI), # 无射: 益一
    (11, LossGain.SUN),# 仲吕: 损一 → 触发仲吕闭合
]


def get_twelve_lu_length(step: int) -> int:
    """
    获取十二律长度格点 (严格查表，非浮点计算)
    步数 step ∈ {0, ..., 11} 对应十二律相位
    """
    return TWELVE_LU_LENGTHS[step % 12]


def get_twelve_lu_lcm_reminder(step: int) -> int:
    """
    获取十二律 LCM 余数 (严格查表)
    """
    return TWELVE_LU_LCM[step % 12]


def loss_gain_step(step: int) -> LossGain | None:
    """
    获取第 step 步的损益操作类型
    step 0 (黄钟): 基准，无操作
    """
    return LOSS_GAIN_MAP[step % 12][1]


def lcm_add(a: int, b: int) -> int:
    """主权 LCM 模加法: (a + b) mod LCM"""
    return (a + b) % SOVEREIGN_LCM


def lcm_mul(a: int, b: int) -> int:
    """主权 LCM 模乘法: (a * b) mod LCM"""
    return (a * b) % SOVEREIGN_LCM


def lcm_reminder(n: int) -> int:
    """计算 LCM 余数"""
    return n % SOVEREIGN_LCM


def zhonglv_closure(acc: int) -> int:
    """
    仲吕闭合: acc ↦ (acc * 3^11) >> 16
    即: (acc * 177147) / 65536
    
    几何拓扑意义:
    - 极向缠绕从模 12 展开为模 144
    - 环向缠绕从模 10 升维为模 46
    - 主权状态机虚实比归零
    - T⁶ 环面的和乐归零
    
    注意: 这是整数运算，非浮点近似
    """
    return (acc * POWER3_11) // POWER2_16


# 宪法验证
def validate_loss_gain():
    """验证损益操作正确性"""
    # 黄钟 → 林钟 (损一)
    assert loss(81) == 54
    # 林钟 → 太簇 (益一)
    assert gain(54) == 72
    # 太簇 → 南吕 (损一)
    assert loss(72) == 48
    
    # 十二律链验证
    chain = generate_twelve_lu_chain(81)
    assert chain == TWELVE_LU_LENGTHS[:len(chain)]
    
    # 仲吕闭合验证
    zhonglu_acc = 65536
    closed = zhonglv_closure(zhonglu_acc)
    assert closed == 177147  # 复位到黄钟余数
    
    print("✅ 损益操作与仲吕闭合验证通过")


if __name__ == "__main__":
    validate_loss_gain()
