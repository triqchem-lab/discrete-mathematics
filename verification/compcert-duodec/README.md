# CompCert 验证：12进制数学库核心算法

本目录用 **CompCert 3.17**（带数学验证器的 C 编译器）验证「律算合一」12进制数学库的核心算法。

## 验证闭环

```
Agda 定理证明（src/Sovereign）──→ C 实现 ──→ CompCert 3.17 编译
  数学正确性（定理已证）          忠实移植      汇编语义 = C 语义（机器证明）
        └──────────── 62 项断言对照 ────────────┘
```

- **数学正确性**：C 实现对 Agda 已证定理的逐项断言（62 项，见下）
- **编译正确性**：CompCert 保证生成的汇编语义与 C 语义一致；gcc 编译运行做交叉对照（输出逐行 diff）

## 覆盖的 Agda 定理（对照源文件）

| 章节 | Agda 源 | 断言内容 |
|---|---|---|
| §1 Trit | `src/Sovereign/Base/Trit.agda` | GF(3) char-3 加法表（9 项 + 归零 + 取负） |
| §2 AlphaPower | `src/Sovereign/Algebra/GroupTheory/DuodecClock.agda` | ⟨α⟩ 乘法表 mulAlpha 16 case、逆元 |
| §3 GF(9) | `src/Sovereign/Algebra/GF9.agda` | α²=-1、α³=-α、α⁴=1、范数 N(a+bα)=a²+b² |
| §3b 嵌入同态 | `DuodecClock.agda` (mulAlpha-hom) | ⟨α⟩ 乘法 = GF(9) 域乘法限制（16 case） |
| §4 Duodec | `src/Sovereign/Algebra/Duodecimal.agda` | CRT Z/12 roundtrip（12 项）、零因子 |
| §5 φ | `src/Sovereign/Algebra/DiscreteFibonacci.agda` | φ=1+2α：φ²=α、φ⁴=-1、φ⁸=1、阶 8 |
| §6 常量 | README 宪法常量 | 3¹¹=177147、2¹⁶=65536、M=3¹¹×2¹⁶ |
| §7 DuodecClock | `DuodecClock.agda` (mixedOp 群公理) | 12 元素混合时钟：单位元/逆元/交换律(144)/结合律穷举(12³=1728)/CRT 同构 roundtrip/群同态(144) |

## 使用

```bash
# gcc 验证（数学正确性，无 CompCert 依赖）
make verify-gcc

# CompCert 验证（需要 /opt/CompCert/bin/ccomp，或 make COMPCERT=你的路径）
make verify-compcert

# 全部 + 交叉 diff
make
```

CI（`.github/workflows/compcert-verify.yml`）自动跑 gcc 验证。

## 编码约定

- Trit: 0,1,2（GF(3)，模 3 运算）
- GF9: code = a×3+b，即 a+bα（α²=-1，GF(3) 中 -1=2）
- AlphaPower: 0..3 表示 α⁰..α³
- DuodecPoint: code = trit×4 + alpha（12 元素）
- Duodec: 0..11（Z/12，CRT: π3=mod 3, π4=mod 4）
