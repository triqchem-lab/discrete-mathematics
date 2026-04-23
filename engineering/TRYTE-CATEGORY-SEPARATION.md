# Tryte 范畴分离说明 v2.5

**版本**：v2.5  
**状态**：代码实现完成，测试通过  
**日期**：2025

---

## 一、范畴分离

| 概念 | Tryte | PackedTryte5 |
|------|-------|-------------|
| **范畴** | 结构学 (纤维丛局部截面基元) | 耦合域 (工程编码) |
| **trit 数** | **6** (不可变) | **5** (字节对齐妥协) |
| **状态数** | 3⁶ = **729** | 3⁵ = **243** |
| **几何意义** | T⁶ 环面单点纤维的完整格点集 | 无损压缩存储，需解包恢复 Tryte |
| **剩余态** | 无 | 13 态 (243-255) 能隙奇点捕获区 |
| **演化独立性** | 主权状态机直接操作 Tryte | 仅用于 I/O 与存储 |

---

## 二、代码实现

### 2.1 Tryte (结构学)

```python
# 6 trit, 729 态
tryte = Tryte([Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1, Trit.T2])
assert tryte.to_int() < 729
assert tryte.NUM_STATES == 729
```

### 2.2 PackedTryte5 (耦合域 - 工程编码)

```python
# 5 trit, 243 态
pt = PackedTryte5([Trit.T0, Trit.T1, Trit.T2, Trit.T0, Trit.T1])
assert pt.to_int() < 243

# 能隙奇点捕获区检测 (243-255)
try:
    PackedTryte5.from_int(250)  # 触发爻变陷阱
except ValueError:
    pass  # 正确捕获
```

### 2.3 打包/解包

```python
# Tryte → 字节流 (工程编码)
trytes = [Tryte(...), Tryte(...)]
packed = pack_trytes_to_bytes(trytes)

# 字节流 → Tryte (必须通过宪法授权的解包 LUT 恢复)
unpacked = unpack_bytes_to_trytes(packed, num_trytes=2)
```

---

## 三、测试状态

| 测试类 | 测试项 | 状态 |
|--------|--------|------|
| TestTryte | 4 项 | ✅ 全部通过 |
| TestPackedTryte5 | 6 项 | ✅ 全部通过 |
| **总计** | **27 项** | **✅ 全部通过** |

---

## 四、宪法条款

> Tryte 是主权状态机离散纤维丛的不可约局部截面，其 6 trit 维度由 T⁶ 环面实六维结构严格决定。工程中使用的 5 trit 打包是二进制硬件上的编码妥协，必须通过宪法授权的解包 LUT 恢复为 Tryte 后方可参与主权运算。禁止将 5 trit 打包值直接视为 Tryte 或用于陈数曲率计算。范畴已严格分离。
