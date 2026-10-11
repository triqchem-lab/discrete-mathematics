# 线2 DB 核心数值锚（精确整数）：lin-solve-db 及其辅助引理的全部字面断言
import json
P3, P2 = 3**11, 2**16          # 177147, 65536
C = 2 * 24371                   # 48742
ROOT3 = 2975006719
N = 177147 * 65536              # SOVEREIGN_LCM = 11609505792

assert C + 16794 == P2                                   # db-bound/db-go 的字面桥
assert 16794 * P3 + 1 == ROOT3                           # q-split zero：1 + a·3¹¹ = root₃
assert ROOT3 + 1 == 45395 * P2                           # root₃+1-anchor 一致
assert P3 * 24371 == 1 + P2 * 65876                      # inv-witness
assert P2 - C == 16794                                   # 65536 - 48742
assert (16794 + P2) * P3 + 1 > N                         # q≥1 矛盾界
assert 16794 * P3 + 2 == 45395 * P2                      # eq-ab 数值形

# 唯一性穷举：a ∈ [0, 2¹⁶) 使 a·3¹¹ + 2 ≡ 0 (mod 2¹⁶) 恰 a = 16794
sols = [a for a in range(P2) if (a * P3 + 2) % P2 == 0]
assert sols == [16794], sols

# db-go q 形：a + C = (q+1)·2¹⁶ → a = 16794 + q·2¹⁶（q=0..3 抽验 + 代数恒等）
for q in range(4):
    a = (q + 1) * P2 - C
    assert a == 16794 + q * P2
print("all anchors verified; unique solution a = 16794 in [0, 2^16)")
print("ORACLE-MANIFEST", json.dumps({
  "basis": "exact-int", "domain": P2, "points": P2,
  "claim": "lin-solve-db anchors: 16794 unique s.t. a*3^11+2==0 mod 2^16, 2*24371+16794=2^16, root3=1+16794*3^11, q>=1 contradiction"}))
