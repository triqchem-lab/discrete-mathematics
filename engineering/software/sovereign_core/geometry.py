"""
Sovereign Core - 结构学：几何拓扑与 Tryte 定义
Structology: Geometric Topology & Tryte Definition

============================================================
⚠️ 认知升维：结构学本体论
============================================================
- Tryte (729 态)：T⁶ 环面单点纤维的不可约局部截面 (6 trit)。
- 5-trit 打包 (243 态)：仅用于 I/O 存储的工程妥协 (1 byte)。
- 严禁将 5-trit 字节直接视为 Tryte。
- 运算必须在 SovereignFiber (30 trit) 层面进行。
============================================================
"""

from typing import List, Tuple
from enum import Enum

# 引入 GF(3) 定义
from engineering.software.sovereign_core.axioms import GF3Trit

# ============================================================
# 1. 逻辑单元：Tryte (729 态)
# ============================================================

class Tryte:
    """
    逻辑单元 Tryte：6 个 GF(3) Trit 的集合。
    对应 T⁶ 环面的一个局部格点截面。
    状态空间大小：3^6 = 729。
    """
    NUM_TRITS = 6
    
    def __init__(self, trits: List[int]):
        """
        初始化 Tryte。
        输入必须是 6 个整数的列表，每个整数 ∈ {-1, 0, 1}。
        """
        if len(trits) != self.NUM_TRITS:
            raise ValueError(f"Tryte 必须包含 {self.NUM_TRITS} 个 Trit，当前为 {len(trits)} 个")
        
        self._trits = []
        for t in trits:
            if t not in (-1, 0, 1):
                raise ValueError(f"非法的 Trit 值: {t}。必须为 -1, 0, 1")
            self._trits.append(t)

    @property
    def trits(self) -> List[int]:
        return list(self._trits) # 返回副本以保护内部状态

    def to_int(self) -> int:
        """将 Tryte 转换为 0-728 的整数 (仅用于调试或标识)"""
        val = 0
        multiplier = 1
        for t in self._trits:
            # 映射 -1,0,1 -> 0,1,2
            mapped = t + 1
            val += mapped * multiplier
            multiplier *= 3
        return val

    @staticmethod
    def from_int(val: int) -> 'Tryte':
        """从 0-728 的整数还原 Tryte"""
        if not (0 <= val < 729):
            raise ValueError("整数值必须在 0-728 之间")
        
        trits = []
        temp_val = val
        for _ in range(6):
            rem = temp_val % 3
            # 映射 0,1,2 -> -1,0,1
            trits.append(rem - 1)
            temp_val //= 3
        return Tryte(trits)

    def __repr__(self):
        return f"Tryte(trits={self._trits})"

# ============================================================
# 2. 主权纤维：SovereignFiber (30 trit)
# ============================================================

class SovereignFiber:
    """
    主权状态机的核心数据结构：30 个 Trit。
    由 5 个 Tryte 组成，分别对应五行 (火, 土, 金, 水, 木)。
    这对应 TQ1_0 格式中 qs[6] 字段在内存中的逻辑展开形式。
    """
    
    def __init__(self, 
                 fire: Tryte, 
                 earth: Tryte, 
                 metal: Tryte, 
                 water: Tryte, 
                 wood: Tryte):
        self.fire = fire
        self.earth = earth
        self.metal = metal
        self.water = water
        self.wood = wood

    def get_all_trits(self) -> List[int]:
        """获取所有 30 个 Trit 的扁平列表"""
        return (self.fire.trits + 
                self.earth.trits + 
                self.metal.trits + 
                self.water.trits + 
                self.wood.trits)

    @staticmethod
    def from_trits(trits: List[int]) -> 'SovereignFiber':
        """从 30 个 Trit 列表构建 SovereignFiber"""
        if len(trits) != 30:
            raise ValueError(f"必须提供 30 个 Trit，当前为 {len(trits)} 个")
        
        fire = Tryte(trits[0:6])
        earth = Tryte(trits[6:12])
        metal = Tryte(trits[12:18])
        water = Tryte(trits[18:24])
        wood = Tryte(trits[24:30])
        
        return SovereignFiber(fire, earth, metal, water, wood)

# ============================================================
# 3. 工程编码：5-trit 打包 (243 态) 与解包
# ============================================================

class PackedIO:
    """
    工程输入输出处理：负责 SovereignFiber 与 6 字节 (qs) 之间的转换。
    严格遵循：每 5 个 Trit 打包为 1 字节 (0-242)。
    """
    
    @staticmethod
    def pack_5_trits_to_byte(trits: List[int]) -> int:
        """
        将 5 个 Trit 打包为 1 个字节 (0-242)。
        算法：Base-3 编码。
        """
        if len(trits) != 5:
            raise ValueError("打包操作必须输入 5 个 Trit")
        
        byte_val = 0
        multiplier = 1
        for t in trits:
            # 映射 -1,0,1 -> 0,1,2
            mapped = t + 1
            byte_val += mapped * multiplier
            multiplier *= 3
            
        if byte_val > 242:
            # 理论上不会发生，因为 242 是 5 位三进制最大值 (22222_3 = 242)
            raise ArithmeticError("打包结果溢出 1 字节范围")
            
        return byte_val

    @staticmethod
    def unpack_byte_to_5_trits(byte_val: int) -> List[int]:
        """
        将 1 个字节 (0-242) 解包为 5 个 Trit。
        如果 byte_val > 242 (即落入能隙奇点捕获区)，抛出异常。
        """
        if byte_val > 242:
            raise ValueError(f"能隙奇点捕获：字节值 {byte_val} 超出 5-trit 合法范围 (243-255)")
        
        trits = []
        temp_val = byte_val
        for _ in range(5):
            rem = temp_val % 3
            # 映射 0,1,2 -> -1,0,1
            trits.append(rem - 1)
            temp_val //= 3
        
        return trits

    @classmethod
    def fiber_to_qs(cls, fiber: SovereignFiber) -> List[int]:
        """
        将 SovereignFiber (30 trit) 转换为 qs (6 字节)。
        """
        all_trits = fiber.get_all_trits()
        qs = []
        
        # 30 trits / 5 = 6 bytes
        for i in range(6):
            chunk = all_trits[i*5 : (i+1)*5]
            qs.append(cls.pack_5_trits_to_byte(chunk))
            
        return qs

    @classmethod
    def qs_to_fiber(cls, qs: List[int]) -> SovereignFiber:
        """
        将 qs (6 字节) 转换为 SovereignFiber (30 trit)。
        """
        if len(qs) != 6:
            raise ValueError("qs 必须包含 6 个字节")
            
        all_trits = []
        for byte_val in qs:
            all_trits.extend(cls.unpack_byte_to_5_trits(byte_val))
            
        return SovereignFiber.from_trits(all_trits)

# ============================================================
# 验证与测试
# ============================================================

def validate_geometry_core():
    """验证几何拓扑核心逻辑"""
    
    # 1. Tryte 729 态验证
    t1 = Tryte([1, 1, 1, 1, 1, 1]) # All +1
    assert t1.to_int() == 728 # 2*243 + 2*81 + ... + 2 = 728
    
    t0 = Tryte([-1, -1, -1, -1, -1, -1]) # All -1
    assert t0.to_int() == 0 # 0*... + 0 = 0
    
    # 2. SovereignFiber 构建
    fiber = SovereignFiber(t1, t1, t1, t1, t1)
    assert len(fiber.get_all_trits()) == 30
    
    # 3. 打包/解包验证 (I/O)
    qs = PackedIO.fiber_to_qs(fiber)
    assert len(qs) == 6
    # t1 全为 1 (mapped to 2). 
    # 5 trits of '2' -> 2 + 2*3 + 2*9 + 2*27 + 2*81 = 2 * (1+3+9+27+81) = 2 * 121 = 242.
    assert qs == [242, 242, 242, 242, 242, 242]
    
    # 4. 解包复原
    restored_fiber = PackedIO.qs_to_fiber(qs)
    assert restored_fiber.get_all_trits() == fiber.get_all_trits()
    
    # 5. 异常捕获验证 (能隙奇点)
    try:
        PackedIO.unpack_byte_to_5_trits(250)
        assert False, "应触发能隙异常"
    except ValueError as e:
        assert "能隙奇点捕获" in str(e)
        
    print("✅ 几何拓扑核心验证通过 (Tryte 729 / I/O 243)")

if __name__ == "__main__":
    validate_geometry_core()
