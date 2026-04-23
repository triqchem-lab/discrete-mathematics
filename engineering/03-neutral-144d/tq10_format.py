"""
Sovereign Core - 主权 TQ1_0 格式
16 字节主权块，小端序，16 字节对齐

范畴定义:
- qs[6] 逻辑上对应 5 个 Tryte (30 trit, 结构学)
- 物理上打包为 6 字节 (耦合域工程编码)
- 打包/解包是地址翻译，非降维压缩
- 端序: 小端序 (与 .sov 格式一致)
"""

import struct
from typing import List, Optional, Tuple
from .trit import Trit
from .tryte import Tryte, PackedTryte5


# 宪法常量
SOV_BLOCK_SIZE = 16  # 16 字节


class SovereignBlock:
    """
    主权 TQ1_0 格式 16 字节块
    
    结构:
    - qs[6]:        30 trit 主权权重 (5 Tryte 的物理打包)
    - scale:        UE8M0 主权尺度指数 (1 字节)
    - phase_bias:   高 4 位十二律相位，低 4 位归零偏置 (1 字节)
    - chern_guard:  高 3 位七阶段阶位，低 5 位局部陈数 (1 字节)
    - wuxing_mask:  高 5 位球谐方向，低 3 位 A4 生成元 (1 字节)
    - reserved[6]:  保留扩展 (6 字节)
    
    范畴分离:
    - 内部逻辑: 5 个 Tryte (结构学纤维丛截面)
    - 物理存储: 6 字节打包 (耦合域地址翻译)
    """
    
    NUM_TRYTES = 5
    NUM_TRITS = 30  # 5 Tryte × 6 trit
    
    def __init__(self, 
                 trytes: List[Tryte] = None,
                 scale: int = 0,
                 phase_bias: int = 0,
                 chern_guard: int = 0,
                 wuxing_mask: int = 0,
                 reserved: List[int] = None):
        # 内部逻辑表示: 5 个 Tryte (结构学)
        if trytes is None:
            # 默认: 全平衡态 (T1 = 0)
            self.trytes = [Tryte([Trit.T1] * Tryte.NUM_TRITS)] * self.NUM_TRYTES
        else:
            if len(trytes) != self.NUM_TRYTES:
                raise ValueError(
                    f"主权块必须包含 {self.NUM_TRYTES} 个 Tryte (30 trit)，"
                    f"当前: {len(trytes)} 个 Tryte"
                )
            self.trytes = list(trytes)
        
        # 物理打包表示: 6 字节 (耦合域地址翻译)
        self.qs = self._pack_trytes_to_qs(self.trytes)
        
        self.scale = scale
        self.phase_bias = phase_bias
        self.chern_guard = chern_guard
        self.wuxing_mask = wuxing_mask
        self.reserved = reserved or [0] * 6
        
        self._validate()
    
    def _pack_trytes_to_qs(self, trytes: List[Tryte]) -> List[int]:
        """
        Tryte → qs[6] 打包 (地址翻译)
        5 Tryte (30 trit) → 6 字节 (每字节 5 trit)
        
        范畴: 结构学 → 耦合域
        """
        # 展开所有 trit
        all_trits = []
        for t in trytes:
            all_trits.extend(t.trits)
        
        # 按 5 trit 一组打包为 6 字节
        qs = []
        for i in range(6):
            trits_5 = all_trits[i * 5:(i + 1) * 5]
            pt = PackedTryte5(trits_5)
            qs.append(pt.to_int())
        
        return qs
    
    def _unpack_qs_to_trytes(self, qs: List[int]) -> List[Tryte]:
        """
        qs[6] → Tryte 列表解包 (地址翻译逆操作)
        6 字节 → 5 Tryte (30 trit)
        
        范畴: 耦合域 → 结构学
        """
        # 解包所有 trit
        all_trits = []
        for byte_val in qs:
            pt = PackedTryte5.from_int(byte_val)
            all_trits.extend(pt.trits)
        
        # 重新组合为 5 个 Tryte (每 Tryte 6 trit)
        trytes = []
        for i in range(self.NUM_TRYTES):
            trits_6 = all_trits[i * 6:(i + 1) * 6]
            trytes.append(Tryte(trits_6))
        
        return trytes
    
    def get_tryte(self, index: int) -> Tryte:
        """获取第 index 个 Tryte (结构学访问)"""
        if index < 0 or index >= self.NUM_TRYTES:
            raise ValueError(f"Tryte 索引必须在 0-{self.NUM_TRYTES-1} 之间")
        # 确保 Tryte 列表是最新的 (从 qs 解包)
        self.trytes = self._unpack_qs_to_trytes(self.qs)
        return self.trytes[index]
    
    def set_tryte(self, index: int, tryte: Tryte):
        """设置第 index 个 Tryte (结构学修改)"""
        if index < 0 or index >= self.NUM_TRYTES:
            raise ValueError(f"Tryte 索引必须在 0-{self.NUM_TRYTES-1} 之间")
        self.trytes[index] = tryte
        # 重新打包到 qs
        self.qs = self._pack_trytes_to_qs(self.trytes)
    
    def _validate(self):
        """宪法验证"""
        assert len(self.qs) == 6, f"qs 必须为 6 字节，当前: {len(self.qs)}"
        assert len(self.reserved) == 6, f"reserved 必须为 6 字节"
        assert 0 <= self.scale <= 255
        assert 0 <= self.phase_bias <= 255
        assert 0 <= self.chern_guard <= 255
        assert 0 <= self.wuxing_mask <= 255
        for b in self.qs + self.reserved:
            assert 0 <= b <= 255
        # 验证 qs 与 Tryte 的一致性
        assert self.qs == self._pack_trytes_to_qs(self.trytes)
    
    def get_phase_bias_high(self) -> int:
        """获取 phase_bias 高 4 位 (十二律相位 0-11)"""
        return (self.phase_bias >> 4) & 0x0F
    
    def get_phase_bias_low(self) -> int:
        """获取 phase_bias 低 4 位 (归零偏置)"""
        return self.phase_bias & 0x0F
    
    def get_chern_guard_high(self) -> int:
        """获取 chern_guard 高 3 位 (七阶段阶位 0-6)"""
        return (self.chern_guard >> 5) & 0x07
    
    def get_chern_guard_low(self) -> int:
        """获取 chern_guard 低 5 位 (局部陈数 0-31)"""
        return self.chern_guard & 0x1F
    
    def get_wuxing_mask_high(self) -> int:
        """获取 wuxing_mask 高 5 位 (球谐方向 0-31)"""
        return (self.wuxing_mask >> 3) & 0x1F
    
    def get_wuxing_mask_low(self) -> int:
        """获取 wuxing_mask 低 3 位 (A4 生成元 0-7)"""
        return self.wuxing_mask & 0x07
    
    def should_zhonglv_closure(self) -> bool:
        """检查是否应触发仲吕闭合 (phase_bias 高 4 位 = 11)"""
        return self.get_phase_bias_high() == 11
    
    def serialize(self) -> bytes:
        """序列化为 16 字节"""
        data = struct.pack('<6B', *self.qs)
        data += struct.pack('<B', self.scale)
        data += struct.pack('<B', self.phase_bias)
        data += struct.pack('<B', self.chern_guard)
        data += struct.pack('<B', self.wuxing_mask)
        data += struct.pack('<6B', *self.reserved)
        assert len(data) == SOV_BLOCK_SIZE
        return data
    
    @classmethod
    def deserialize(cls, data: bytes) -> 'SovereignBlock':
        """从 16 字节反序列化"""
        if len(data) != SOV_BLOCK_SIZE:
            raise ValueError(f"主权块必须为 16 字节，当前: {len(data)}")
        
        qs = list(struct.unpack('<6B', data[0:6]))
        scale = struct.unpack('<B', data[6:7])[0]
        phase_bias = struct.unpack('<B', data[7:8])[0]
        chern_guard = struct.unpack('<B', data[8:9])[0]
        wuxing_mask = struct.unpack('<B', data[9:10])[0]
        reserved = list(struct.unpack('<6B', data[10:16]))
        
        # 从 qs 解包 Tryte
        trytes = cls._unpack_qs_to_trytes_static(qs)
        
        return cls(trytes=trytes, scale=scale, phase_bias=phase_bias,
                   chern_guard=chern_guard, wuxing_mask=wuxing_mask,
                   reserved=reserved)
    
    @staticmethod
    def _unpack_qs_to_trytes_static(qs: List[int]) -> List[Tryte]:
        """静态方法: qs[6] → Tryte 列表解包"""
        all_trits = []
        for byte_val in qs:
            pt = PackedTryte5.from_int(byte_val)
            all_trits.extend(pt.trits)
        
        trytes = []
        for i in range(5):  # 5 Tryte
            trits_6 = all_trits[i * 6:(i + 1) * 6]
            trytes.append(Tryte(trits_6))
        
        return trytes


def sov_write(file, block: SovereignBlock):
    """写入 .sov 文件 (16 字节原子操作)"""
    data = block.serialize()
    file.write(data)


def sov_read(file) -> Optional[SovereignBlock]:
    """读取 .sov 文件 (16 字节原子操作)"""
    data = file.read(SOV_BLOCK_SIZE)
    if len(data) == 0:
        return None
    if len(data) != SOV_BLOCK_SIZE:
        raise ValueError(f".sov 文件损坏，读取到 {len(data)} 字节")
    return SovereignBlock.deserialize(data)


# 宪法验证
def validate_tq10():
    """验证 TQ1_0 格式正确性"""
    # 创建测试块
    block = SovereignBlock(
        qs=[0, 1, 2, 3, 4, 5],
        scale=10,
        phase_bias=(11 << 4) | 5,  # 十二律相位=11 (仲吕), 偏置=5
        chern_guard=(2 << 5) | 15,  # 七阶段=2, 陈数=15
        wuxing_mask=(10 << 3) | 3  # 球谐方向=10, A4生成元=3
    )
    
    # 验证字段提取
    assert block.get_phase_bias_high() == 11
    assert block.get_phase_bias_low() == 5
    assert block.get_chern_guard_high() == 2
    assert block.get_chern_guard_low() == 15
    assert block.get_wuxing_mask_high() == 10
    assert block.get_wuxing_mask_low() == 3
    
    # 验证仲吕闭合触发
    assert block.should_zhonglv_closure() == True
    
    # 验证序列化/反序列化
    data = block.serialize()
    assert len(data) == 16
    block2 = SovereignBlock.deserialize(data)
    assert block.qs == block2.qs
    assert block.phase_bias == block2.phase_bias
    
    print("✅ TQ1_0 格式验证通过")


if __name__ == "__main__":
    validate_tq10()
