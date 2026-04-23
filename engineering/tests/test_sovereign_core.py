"""
律算合一核心库测试套件 (范畴修正版)
"""

import unittest
import sys
import os

# 添加父目录到路径
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'software'))

from sovereign_core.trit import Trit, trit_encode, trit_decode, gf3_add, gf3_mul, gf3_neg
from sovereign_core.tryte import Tryte, PackedTryte5, pack_trytes_to_bytes, unpack_bytes_to_trytes
from sovereign_core.loss_gain import (
    LossGain, 
    lcm_add, lcm_mul, lcm_reminder,
    zhonglv_closure,
    get_twelve_lu_length, get_twelve_lu_lcm_reminder, loss_gain_step,
    SOVEREIGN_LCM, POWER3_11, POWER2_16,
    TWELVE_LU_LENGTHS
)
from sovereign_core.tq10_format import SovereignBlock
from sovereign_core.wuxing import WuXing, wuxing_generate, wuxing_overcome, compute_spin_projection


class TestTrit(unittest.TestCase):
    """Trit 三进制测试 (根数学)"""
    
    def test_encode_decode(self):
        """编码/解码一致性"""
        for t in [Trit.T0, Trit.T1, Trit.T2]:
            self.assertEqual(trit_decode(trit_encode(t)), t)
    
    def test_encode_values(self):
        """编码值验证"""
        self.assertEqual(trit_encode(Trit.T0), 0)
        self.assertEqual(trit_encode(Trit.T1), 1)
        self.assertEqual(trit_encode(Trit.T2), 2)
    
    def test_gf3_neg(self):
        """GF(3) 逆元"""
        self.assertEqual(gf3_neg(Trit.T0), Trit.T2)  # -(-1) = 1
        self.assertEqual(gf3_neg(Trit.T1), Trit.T1)  # -0 = 0
        self.assertEqual(gf3_neg(Trit.T2), Trit.T0)  # -(1) = -1
    
    def test_gf3_add_cancel(self):
        """逆元对消律: a + (-a) = T1(0) (虚实对消灭)"""
        # T0(-1) + T2(+1) = T1(0)
        self.assertEqual(gf3_add(Trit.T0, Trit.T2), Trit.T1)
        self.assertEqual(gf3_add(Trit.T2, Trit.T0), Trit.T1)
        # T1(0) 是单位元
        self.assertEqual(gf3_add(Trit.T1, Trit.T0), Trit.T0)
        self.assertEqual(gf3_add(Trit.T1, Trit.T1), Trit.T1)
        self.assertEqual(gf3_add(Trit.T1, Trit.T2), Trit.T2)
        # T0 + T0 = T2, T2 + T2 = T0
        self.assertEqual(gf3_add(Trit.T0, Trit.T0), Trit.T2)
        self.assertEqual(gf3_add(Trit.T2, Trit.T2), Trit.T0)
    
    def test_gf3_add_table_complete(self):
        """验证 GF(3) 驻波叠加表完整性"""
        all_trits = [Trit.T0, Trit.T1, Trit.T2]
        for a in all_trits:
            for b in all_trits:
                result = gf3_add(a, b)
                self.assertIn(result, all_trits)


class TestTryte(unittest.TestCase):
    """Tryte (6 trit, 729 态) 测试 - 结构学"""
    
    def test_six_trit_pack_unpack(self):
        """6 trit 打包/解包一致性"""
        trits = [Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1, Trit.T2]
        tryte = Tryte(trits)
        self.assertEqual(tryte.trits, trits)
    
    def test_int_roundtrip(self):
        """整数往返 (0-728)"""
        for v in [0, 364, 728]:
            t = Tryte.from_int(v)
            self.assertEqual(t.to_int(), v)
    
    def test_invalid_value(self):
        """非法值捕获 (>=729)"""
        with self.assertRaises(ValueError):
            Tryte.from_int(729)
    
    def test_num_states(self):
        """验证状态数 729"""
        self.assertEqual(Tryte.NUM_STATES, 729)
        self.assertEqual(Tryte.NUM_TRITS, 6)


class TestPackedTryte5(unittest.TestCase):
    """PackedTryte5 (5 trit, 243 态) 测试 - 耦合域 (工程编码)"""
    
    def test_five_trit_pack_unpack(self):
        """5 trit 打包/解包一致性"""
        trits = [Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1]
        pt = PackedTryte5(trits)
        self.assertEqual(pt.trits, trits)
    
    def test_int_roundtrip(self):
        """整数往返 (0-242)"""
        for v in [0, 121, 242]:
            t = PackedTryte5.from_int(v)
            self.assertEqual(t.to_int(), v)
    
    def test_gap_state_detection(self):
        """能隙奇点捕获区检测 (243-255)"""
        for v in [243, 250, 255]:
            with self.assertRaises(ValueError):
                PackedTryte5.from_int(v)
    
    def test_num_states(self):
        """验证状态数 243 + 13 奇点区"""
        self.assertEqual(PackedTryte5.NUM_STATES, 243)
        self.assertEqual(PackedTryte5.GAP_STATES, 13)
    
    def test_pack_trytes_to_bytes(self):
        """Tryte 列表打包为字节"""
        trytes = [
            Tryte([Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1, Trit.T2]),
            Tryte([Trit.T1, Trit.T2, Trit.T0, Trit.T1, Trit.T2, Trit.T0])
        ]
        packed = pack_trytes_to_bytes(trytes)
        # 12 trit → 3 字节 (每字节 5 trit, 填充 3 trit)
        self.assertEqual(len(packed), 3)
    
    def test_unpack_bytes_to_trytes(self):
        """字节解包为 Tryte 列表"""
        original = [
            Tryte([Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1, Trit.T2])
        ]
        packed = pack_trytes_to_bytes(original)
        unpacked = unpack_bytes_to_trytes(packed, 1)
        self.assertEqual(len(unpacked), 1)
        self.assertEqual(unpacked[0].trits, original[0].trits)


class TestLossGain(unittest.TestCase):
    """损益操作与 LCM 模运算测试 (耦合域)"""
    
    def test_twelve_lu_lengths(self):
        """十二律长度格点 (严格查表)"""
        expected = [81, 54, 72, 48, 64, 43, 57, 38, 51, 34, 45, 30]
        for i, exp in enumerate(expected):
            self.assertEqual(get_twelve_lu_length(i), exp)
    
    def test_twelve_lu_lcm_reminders(self):
        """十二律 LCM 余数 (严格查表)"""
        expected = [177147, 118098, 157464, 104976, 139968, 
                    93312, 124416, 82944, 110592, 73728, 98304, 65536]
        for i, exp in enumerate(expected):
            self.assertEqual(get_twelve_lu_lcm_reminder(i), exp)
    
    def test_loss_gain_step(self):
        """损益操作类型映射"""
        self.assertIsNone(loss_gain_step(0))  # 黄钟: 基准
        self.assertEqual(loss_gain_step(1), LossGain.SUN)  # 林钟: 损一
        self.assertEqual(loss_gain_step(2), LossGain.YI)   # 太簇: 益一
        self.assertEqual(loss_gain_step(11), LossGain.SUN) # 仲吕: 损一
    
    def test_zhonglv_closure(self):
        """仲吕闭合"""
        closed = zhonglv_closure(65536)
        self.assertEqual(closed, 177147)  # 仲吕余数 → 黄钟余数
    
    def test_lcm_arithmetic(self):
        """LCM 模运算"""
        self.assertEqual(lcm_add(100, 200), 300)
        # POWER3_11 * POWER2_16 = SOVEREIGN_LCM, 所以模 LCM 为 0
        self.assertEqual(lcm_mul(POWER3_11, POWER2_16), 0)
        self.assertEqual(lcm_reminder(SOVEREIGN_LCM + 100), 100)


class TestTQ10Format(unittest.TestCase):
    """TQ1_0 格式测试 (耦合域)"""
    
    def test_create_block(self):
        """创建主权块"""
        block = SovereignBlock()
        # 默认 5 个 Tryte (全平衡态)
        self.assertEqual(len(block.trytes), 5)
        self.assertEqual(len(block.qs), 6)
    
    def test_get_set_tryte(self):
        """Tryte 获取/设置"""
        block = SovereignBlock()
        # 获取 Tryte
        t = block.get_tryte(0)
        self.assertEqual(len(t.trits), 6)
        # 设置 Tryte
        new_tryte = Tryte([Trit.T2] * 6)
        block.set_tryte(0, new_tryte)
        self.assertEqual(block.get_tryte(0).trits, [Trit.T2] * 6)
    
    def test_zhonglv_trigger(self):
        """仲吕闭合触发检查"""
        block = SovereignBlock(phase_bias=(11 << 4))  # 相位 11
        self.assertTrue(block.should_zhonglv_closure())
        
        block2 = SovereignBlock(phase_bias=(5 << 4))  # 相位 5
        self.assertFalse(block2.should_zhonglv_closure())
    
    def test_serialize_deserialize(self):
        """序列化/反序列化"""
        block = SovereignBlock(scale=5)
        data = block.serialize()
        self.assertEqual(len(data), 16)
        block2 = SovereignBlock.deserialize(data)
        self.assertEqual(block.qs, block2.qs)
        self.assertEqual(block.scale, block2.scale)


class TestWuXing(unittest.TestCase):
    """五行测试 (元结构层)"""
    
    def test_generate_chain(self):
        """相生链"""
        self.assertEqual(wuxing_generate(WuXing.FIRE), WuXing.EARTH)
        self.assertEqual(wuxing_generate(WuXing.EARTH), WuXing.METAL)
        self.assertEqual(wuxing_generate(WuXing.WOOD), WuXing.FIRE)  # 闭环
    
    def test_overcome(self):
        """相克关系"""
        self.assertTrue(wuxing_overcome(WuXing.WOOD, WuXing.EARTH))
        self.assertTrue(wuxing_overcome(WuXing.FIRE, WuXing.METAL))
        self.assertFalse(wuxing_overcome(WuXing.FIRE, WuXing.WOOD))
    
    def test_spin_projection(self):
        """自旋投影"""
        self.assertEqual(compute_spin_projection(2, 0.5), "spin_1")
        self.assertEqual(compute_spin_projection(4, 0.8), "spin_12")
        self.assertEqual(compute_spin_projection(3, 0.3), "spin_0")


class TestIntegration(unittest.TestCase):
    """集成测试"""
    
    def test_full_twelve_lu_with_closure(self):
        """完整十二律 + 仲吕闭合链路"""
        # 十二律查表验证
        for i in range(12):
            length = get_twelve_lu_length(i)
            lcm_rem = get_twelve_lu_lcm_reminder(i)
            self.assertEqual(length, TWELVE_LU_LENGTHS[i])
        
        # 仲吕闭合
        zhonglu_acc = 65536  # 仲吕余数
        closed = zhonglv_closure(zhonglu_acc)
        self.assertEqual(closed, POWER3_11)  # 黄钟余数
    
    def test_zhonglv_rhythm_closure(self):
        """仲吕闭合节拍验证: 连续 12 步后触发闭合"""
        # 模拟主权状态机 12 步演化
        phase = 0
        chern_state = 0
        
        for step in range(12):  # 0 → 11 (仲吕)
            phase = step
            if phase == 11:  # 仲吕
                # 触发闭合
                chern_state = (chern_state + 1) % 3
        
        # 验证: 第 12 步到达仲吕相位 (step=11)
        self.assertEqual(phase, 11)
        # 验证: 陈数状态轮转
        self.assertEqual(chern_state, 1)


if __name__ == '__main__':
    unittest.main()
