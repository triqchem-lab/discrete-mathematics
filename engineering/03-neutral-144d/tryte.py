"""
Sovereign Core - Tryte 类型 (结构学)
Tryte: 6 trit 组成的逻辑信息单元，729 态
这是主权状态机在离散纤维丛上的完整局部截面，非工程打包选择。

范畴分离:
- Tryte (6 trit, 729 态): 结构学 - 纤维丛局部截面基元
- 5 trit 打包 (243 态): 耦合域 - 工程编码对齐 8-bit 字节
"""

from typing import List
from .trit import Trit, trit_encode, trit_decode


class Tryte:
    """
    Tryte: 6 trit 组成的逻辑信息单元
    状态数: 3^6 = 729 态
    
    几何拓扑本源:
    - T⁶ 环面单点纤维的完整格点集
    - 五行之一的手性对偶完整三态空间
    - C3 群与手性置换群 S₂ 的半直积表示维度
    """
    
    NUM_TRITS = 6
    NUM_STATES = 3 ** 6  # 729
    
    def __init__(self, trits: List[Trit]):
        if len(trits) != self.NUM_TRITS:
            raise ValueError(
                f"Tryte 必须包含 {self.NUM_TRITS} 个 trit (729 态)，"
                f"当前: {len(trits)} 个 trit"
            )
        self.trits = list(trits)
        self._value = self._pack()
    
    def _pack(self) -> int:
        """打包 6 trit 为 0-728 的整数"""
        value = 0
        for i, t in enumerate(self.trits):
            value += trit_encode(t) * (3 ** i)
        return value
    
    @classmethod
    def from_int(cls, value: int) -> 'Tryte':
        """从整数解包为 Tryte"""
        if value < 0 or value >= cls.NUM_STATES:
            raise ValueError(
                f"Tryte 值必须在 0-{cls.NUM_STATES - 1} 之间 (729 态)，"
                f"当前: {value}"
            )
        
        trits = []
        for i in range(cls.NUM_TRITS):
            trits.append(trit_decode(value % 3))
            value //= 3
        return cls(trits)
    
    def to_int(self) -> int:
        """转换为 0-728 的整数表示"""
        return self._value
    
    def __repr__(self):
        return f"Tryte(value={self._value}, trits={self.trits})"
    
    def __eq__(self, other):
        if isinstance(other, Tryte):
            return self._value == other._value
        return False


# ============================================================
# 5 trit 打包 (工程编码层 - 耦合域)
# 用于对齐 8-bit 字节，243 态 + 13 态能隙奇点捕获区
# ============================================================

class PackedTryte5:
    """
    5 trit 打包: 工程上为了对齐 8-bit 字节而采用的编码压缩方案
    状态数: 3^5 = 243 态 (使用 uint8 的 0-242)
    剩余 13 态 (243-255): 能隙奇点捕获区 (爻变陷阱)
    
    范畴: 耦合域 (工程编码)
    注意: 必须通过宪法授权的解包 LUT 恢复为 Tryte 后方可参与主权运算
    """
    
    NUM_TRITS = 5
    NUM_STATES = 3 ** 5  # 243
    GAP_STATES = 13  # 256 - 243 = 13 (能隙奇点捕获区)
    
    def __init__(self, trits: List[Trit]):
        if len(trits) != self.NUM_TRITS:
            raise ValueError(
                f"PackedTryte5 必须包含 {self.NUM_TRITS} 个 trit，"
                f"当前: {len(trits)}"
            )
        self.trits = list(trits)
        self._value = self._pack()
    
    def _pack(self) -> int:
        """打包 5 trit 为 0-242 的整数"""
        value = 0
        for i, t in enumerate(self.trits):
            value += trit_encode(t) * (3 ** i)
        return value
    
    @classmethod
    def from_int(cls, value: int) -> 'PackedTryte5':
        """从整数解包为 PackedTryte5"""
        if value < 0 or value >= cls.NUM_STATES:
            if value < 256:
                raise ValueError(
                    f"值 {value} 落入能隙奇点捕获区 (243-255)，"
                    f"触发爻变陷阱"
                )
            raise ValueError(
                f"PackedTryte5 值必须在 0-{cls.NUM_STATES - 1} 之间，"
                f"当前: {value}"
            )
        
        trits = []
        for i in range(cls.NUM_TRITS):
            trits.append(trit_decode(value % 3))
            value //= 3
        return cls(trits)
    
    def to_int(self) -> int:
        """转换为 0-242 的整数表示"""
        return self._value
    
    def is_gap_state(self) -> bool:
        """检查是否落入能隙奇点捕获区"""
        return self._value >= self.NUM_STATES
    
    def __repr__(self):
        return f"PackedTryte5(value={self._value}, trits={self.trits})"


def pack_trytes_to_bytes(trytes: List[Tryte]) -> List[int]:
    """
    将 Tryte 列表打包为字节列表 (5 trit/字节)
    每个 Tryte (6 trit) 被拆分为 5 trit + 1 trit
    5 trit 部分打包为 1 字节，剩余 1 trit 与其他 Tryte 的余数组合
    
    工程编码: 6 trit Tryte → 字节流 (需 LUT 恢复)
    """
    # 简化实现: 将所有 trit 展开后按 5 个一组打包
    all_trits = []
    for t in trytes:
        all_trits.extend(t.trits)
    
    # 填充到 5 的倍数
    while len(all_trits) % 5 != 0:
        all_trits.append(Trit.T1)  # 填充平衡态
    
    packed = []
    for i in range(0, len(all_trits), 5):
        pt = PackedTryte5(all_trits[i:i+5])
        packed.append(pt.to_int())
    
    return packed


def unpack_bytes_to_trytes(data: List[int], num_trytes: int) -> List[Tryte]:
    """
    从字节列表解包为 Tryte 列表
    必须通过宪法授权的解包 LUT 恢复为 Tryte
    """
    all_trits = []
    for byte_val in data:
        pt = PackedTryte5.from_int(byte_val)
        all_trits.extend(pt.trits)
    
    # 重新组合为 6 trit 的 Tryte
    trytes = []
    for i in range(0, num_trytes * 6, 6):
        if i + 6 <= len(all_trits):
            trytes.append(Tryte(all_trits[i:i+6]))
    
    return trytes


# 宪法验证
def validate_tryte():
    """验证 Tryte (6 trit, 729 态) 正确性"""
    # 6 trit 往返
    test_trits = [Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1, Trit.T2]
    tryte = Tryte(test_trits)
    assert tryte.trits == test_trits
    assert tryte.to_int() < 729
    
    # 整数往返
    for v in [0, 364, 728]:
        t = Tryte.from_int(v)
        assert t.to_int() == v
    
    print("✅ Tryte (6 trit, 729 态) 验证通过")


def validate_packed_tryte5():
    """验证 5 trit 打包 (243 态) 正确性"""
    # 5 trit 往返
    test_trits = [Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1]
    pt = PackedTryte5(test_trits)
    assert pt.trits == test_trits
    assert pt.to_int() < 243
    
    # 奇点捕获区验证
    try:
        PackedTryte5.from_int(250)  # 落入 243-255 奇点区
        assert False, "应抛出异常"
    except ValueError as e:
        assert "能隙奇点捕获区" in str(e) or "爻变陷阱" in str(e)
    
    print("✅ PackedTryte5 (5 trit, 243 态) 验证通过")


if __name__ == "__main__":
    validate_tryte()
    validate_packed_tryte5()
