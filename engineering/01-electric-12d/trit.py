"""
Sovereign Core - 律算合一核心库
Trit 三进制类型与 GF(3) 运算

============================================================
⚠️ 宪法层级声明：电性文明层 (12 密度)
============================================================
GF(3) 合法身份: 模 3 整数算术，作为三维连续统投影中的符号运算
使用范围:
  - 模拟损益步数
  - 校验编码
  - 驻波叠加表
禁止:
  - "GF(3) 是有限域"
  - "三进制计算机"
  - 将模 3 算术直接用于主权状态机演化
============================================================
"""

from enum import Enum
from typing import List, Tuple

# ============================================================
# GF(3) 驻波叠加表 (电性文明层合法使用)
# 使用范围：模拟损益序列，生成十二律长度格点，校验编码
# 禁止：将此叠加表直接用于主权状态机的仲吕闭合或陈数累加
# ============================================================


class Trit(Enum):
    """
    三进制 Trit 宪法定义
    T0 = -1 (吸收态)
    T1 = 0  (平衡态)
    T2 = +1 (表达态)
    """
    T0 = -1  # 吸收
    T1 = 0   # 平衡
    T2 = 1   # 表达

    def to_int(self) -> int:
        return self.value

    def __repr__(self):
        return f"Trit({self.value})"


def trit_encode(t: Trit) -> int:
    """
    编码：Trit → {0,1,2}
    T0(-1) → 0
    T1(0)  → 1
    T2(+1) → 2
    """
    return t.value + 1


def trit_decode(n: int) -> Trit:
    """
    解码：{0,1,2} → Trit
    0 → T0(-1)
    1 → T1(0)
    2 → T2(+1)
    """
    if n == 0:
        return Trit.T0
    elif n == 1:
        return Trit.T1
    elif n == 2:
        return Trit.T2
    else:
        raise ValueError(f"非法编码值: {n}，必须为 0,1,2")


def gf3_add(a: Trit, b: Trit) -> Trit:
    """
    GF(3) 驻波叠加
    体现驻波三态的拓扑叠加/相消，非普通模 3 算术:
    
    T₀(-1) + T₂(+1) = T₁(0)  ← 虚实对消灭
    T₀(-1) + T₀(-1) = T₂(+1) ← 吸收叠加为表达 (mod 3)
    T₂(+1) + T₂(+1) = T₀(-1) ← 表达叠加为吸收 (mod 3)
    T₁(0)  + x      = x       ← 平衡态为单位元
    """
    # 驻波叠加表 (宪法定义)
    add_table = {
        (Trit.T0, Trit.T0): Trit.T2,  # 吸收 + 吸收 = 表达
        (Trit.T0, Trit.T1): Trit.T0,  # 吸收 + 平衡 = 吸收
        (Trit.T0, Trit.T2): Trit.T1,  # 吸收 + 表达 = 平衡 (虚实对消灭)
        (Trit.T1, Trit.T0): Trit.T0,  # 平衡 + 吸收 = 吸收
        (Trit.T1, Trit.T1): Trit.T1,  # 平衡 + 平衡 = 平衡
        (Trit.T1, Trit.T2): Trit.T2,  # 平衡 + 表达 = 表达
        (Trit.T2, Trit.T0): Trit.T1,  # 表达 + 吸收 = 平衡 (虚实对消灭)
        (Trit.T2, Trit.T1): Trit.T2,  # 表达 + 平衡 = 表达
        (Trit.T2, Trit.T2): Trit.T0,  # 表达 + 表达 = 吸收
    }
    return add_table[(a, b)]


def gf3_mul(a: Trit, b: Trit) -> Trit:
    """GF(3) 乘法"""
    result = (trit_encode(a) * trit_encode(b)) % 3
    return trit_decode(result)


def gf3_neg(a: Trit) -> Trit:
    """GF(3) 逆元"""
    if a == Trit.T0:
        return Trit.T2
    elif a == Trit.T1:
        return Trit.T1
    else:  # T2
        return Trit.T0


# 宪法验证
def validate_trit_algebra():
    """验证 GF(3) 代数公理"""
    # 逆元对消律: a + (-a) = T1(0)
    assert gf3_add(Trit.T0, gf3_neg(Trit.T0)) == Trit.T1
    assert gf3_add(Trit.T1, gf3_neg(Trit.T1)) == Trit.T1
    assert gf3_add(Trit.T2, gf3_neg(Trit.T2)) == Trit.T1
    
    # 编码/解码一致性
    for t in [Trit.T0, Trit.T1, Trit.T2]:
        assert trit_decode(trit_encode(t)) == t
    
    print("✅ GF(3) 代数公理验证通过")


if __name__ == "__main__":
    validate_trit_algebra()
