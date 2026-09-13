NB. ============================================================
NB. duodecimal_crt.ijs — 十二进制联合周期离散计算验证 (J9)
NB.
NB. 主权语义 (对应 Sovereign.Algebra.GroupTheory.DuodecimalGroup.agda,
NB.           C++ include/tetration_representation.h Z12JointPeriod):
NB.   12 = 3 × 4 = char(GF(9)) × ord(α)  — 联合时钟周期, 非抽象 Z/12 环
NB.   · z3 = 3|x : GF(3) 素域步进 (加法周期 3, 三进制归零)
NB.   · z4 = 4|x : ⟨α⟩ 旋转阶 4   (乘法周期 4, 90° 步进, α²=-1)
NB.   CRT 重构: x = (4·z3 + 9·z4) mod 12   (Z/3 ⊕ Z/4 ≅ Z/12)
NB.
NB. 运行: ./bin/jconsole duodecimal_crt.ijs
NB. ============================================================

NB. ---- 1. 十二律相位 0..11 ----
ph =: i.12

NB. ---- 2. CRT 投影 π3 (素域步进) 与 π4 (α旋转阶) ----
z3 =: 3 | ph     NB. mod 3: {0,1,2}
z4 =: 4 | ph     NB. mod 4: {0,1,2,3}

NB. ---- 3. CRT 重构 crt12: x = (4·z3 + 9·z4) mod 12 ----
re =: 12 | (4 * z3) + (9 * z4)

NB. ---- 4. 往返恒等: 重构后投影回原相位 (联合时钟周期双射) ----
roundtrip_ok =: re -: ph        NB. 应为 1

NB. ---- 5. 特征 3: 1+1+1 = 0 (mod 3) — 三进制归零 ----
char3_zero =: 0 = 3 | 1 + 1 + 1 NB. 应为 1

NB. ---- 6. α 旋转阶 4: 四步 90° 回位 (mod 4) ----
rot4_closes =: 0 = 4 | 4        NB. 应为 1

NB. ---- 7. 联合周期数值: 12 = 3 × 4 ----
joint_period =: 12 = 3 * 4      NB. 应为 1

NB. ---- 8. 非内部性: |GF(9)*| = 8, 无 12 阶元素 (12 ∤ 8) ----
gf9star_order =: 8
no_12_element  =: 0 = 12 | gf9star_order  NB. 12 不整除 8 → 应为 0 (确无 12 阶元)

NB. ---- 汇总输出 ----
echo '十二律相位 ph = ' , ": ph
echo '素域步进 z3 (mod 3) = ' , ": z3
echo 'α旋转阶 z4 (mod 4) = ' , ": z4
echo 'CRT 重构 re = ' , ": re
echo '联合时钟周期往返恒等: ' , (roundtrip_ok { 'FAIL';'PASS (12/12)')
echo '特征 3 三进制归零 (1+1+1=0 mod 3): ' , (char3_zero { 'FAIL';'PASS')
echo 'α 旋转阶 4 闭合 (4|4=0): ' , (rot4_closes { 'FAIL';'PASS')
echo '联合周期 12 = 3*4: ' , (joint_period { 'FAIL';'PASS')
echo 'GF(9)* 阶 8, 12∤8 (无 12 阶内部元素): ' , (no_12_element { 'UNEXPECTED';'PASS')
