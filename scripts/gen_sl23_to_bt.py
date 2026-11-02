#!/usr/bin/env python3
"""生成 src/Sovereign/Synthesis/A4/SL23ToBT.agda —— SL23 ≅ Q₈⋊C₃ 的显式同构表。

不手抄任何表：全部从 Agda 源码就地解析
  · _⊗_   (SL23Cayley, 576 条)
  · _*q_  (BinaryTetrahedral, 64 条)
  · _*c_  (BinaryTetrahedral, 1+6 条)
  · act   (BinaryTetrahedral, 24 条)
然后
  1. 在 SL23 里验证 Q₈ ⊂ SL23、C₃ ⊂ SL23 的嵌入；
  2. 验证 act(c,·) 恰等于 SL23 中按 c 的共轭；
  3. 由此得到唯一分解 SL23 = Q₈·C₃（8×3），生成 toBT / fromBT；
  4. 对 576 对逐条验证 toBT(a⊗b) == toBT a *bt toBT b。
任一检查不过直接退出（exit 1），不产出文件。
"""

import re
import sys
from functools import reduce
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BT_SRC = ROOT / "src/Sovereign/Synthesis/A4/BinaryTetrahedral.agda"
CAY_SRC = ROOT / "src/Sovereign/Synthesis/Representation/SL23Cayley.agda"
OUT = ROOT / "src/Sovereign/Synthesis/A4/SL23ToBT.agda"

GS = [f"g{i}" for i in range(24)]
E = "g6"

fail = []


def check(name, ok, detail=""):
    print(f"  [{'OK ' if ok else 'FAIL'}] {name}{(' — ' + detail) if detail else ''}")
    if not ok:
        fail.append(name)


# ── §1. 解析 Agda 表 ─────────────────────────────────────────────────────────
cay = CAY_SRC.read_text()
TAB = {
    (m.group(1), m.group(2)): m.group(3)
    for m in re.finditer(r"^(g\d+) ⊗ (g\d+) = (g\d+)$", cay, re.M)
}
bt = BT_SRC.read_text()
QMUL = {
    (m.group(1), m.group(2)): m.group(3)
    for m in re.finditer(
        r"^(q\w+)\s+\*q\s+(q\w+)\s*=\s*(q\w+)\s*(?:--.*)?$", bt, re.M
    )
}
CMUL = {  # c0 行是 `c0 *c y = y`，只解析 6 条具体条款
    (m.group(1), m.group(2)): m.group(3)
    for m in re.finditer(
        r"^(c\d)\s+\*c\s+(c\d)\s*=\s*(c\d)\s*(?:--.*)?$", bt, re.M
    )
}
ACT = {  # c0 行是 `act c0 q = q`，只解析 16 条具体条款
    (m.group(1), m.group(2)): m.group(3)
    for m in re.finditer(
        r"^act (c\d) (q\w+)\s*=\s*(q\w+)\s*(?:--.*)?$", bt, re.M
    )
}
CC = ["c0", "c1", "c2"]
QS = ["q1", "qm1", "qi", "qmi", "qj", "qmj", "qk", "qmk"]
for _q in QS:
    ACT[("c0", _q)] = _q

print("§1 解析")
check("_⊗_ 576 条", len(TAB) == 576, f"{len(TAB)}")
check("_*q_ 64 条", len(QMUL) == 64, f"{len(QMUL)}")
check("_*c_ 6 条（c0 行由定义展开）", len(CMUL) == 6, f"{len(CMUL)}")
check("act 24 条", len(ACT) == 24, f"{len(ACT)}")
if fail:
    sys.exit(1)


def mul(a, b):
    return TAB[(a, b)]


def pw(g, k):
    return reduce(mul, [g] * k) if k else E


def cmul(a, b):
    return b if a == "c0" else CMUL[(a, b)]


def qmul(a, b):
    return QMUL[(a, b)]


# ── §2. SL23 内部结构 ────────────────────────────────────────────────────────
print("§2 SL23 内部结构")
check("每行是置换（Latin square）",
      all(sorted(mul(g, h) for h in GS) == sorted(GS) for g in GS))
check("结合律（24³ = 13824 对）",
      all(mul(mul(a, b), c) == mul(a, mul(b, c)) for a in GS for b in GS for c in GS))
check("g6 是单位元",
      all(mul(E, g) == g and mul(g, E) == g for g in GS))
check("阶 ≤ 4 的元素恰 8 个",
      len([g for g in GS if any(pw(g, k) == E for k in (1, 2, 4))]) == 8)
if fail:
    sys.exit(1)

# ── §3. Q₈ ⊂ SL23 与 C₃ ⊂ SL23 的嵌入 ────────────────────────────────────────
print("§3 Q₈ / C₃ 嵌入")
I, MINUS1 = "g0", "g15"
check("i² = −1", mul(I, I) == MINUS1)
J = next(
    g for g in GS
    if mul(g, g) == MINUS1 and g not in (I, MINUS1) and mul(g, I) != mul(I, g)
)
K = mul(I, J)
Q8S = {
    "q1": E, "qm1": MINUS1,
    "qi": I, "qmi": mul(I, MINUS1),
    "qj": J, "qmj": mul(J, MINUS1),
    "qk": K, "qmk": mul(K, MINUS1),
}
check("Q₈ 8 个不同元素", len(set(Q8S.values())) == 8, "{" + ",".join(sorted(set(Q8S.values()))) + "}")
check("Q₈ 乘法表嵌入（64 对）",
      all(mul(Q8S[a], Q8S[b]) == Q8S[qmul(a, b)] for a in QS for b in QS))

TARGET_C1 = {q: ACT[("c1", q)] for q in QS}


def conj(c, q):
    return mul(mul(c, Q8S[q]), pw(c, 2))


C1 = next(
    (g for g in GS
     if pw(g, 3) == E and g != E and all(conj(g, q) == Q8S[TARGET_C1[q]] for q in QS)),
    None,
)
check("找到 C₃ 生成元使 act(c1) == 共轭", C1 is not None, str(C1))
if fail:
    sys.exit(1)
C3S = {"c0": E, "c1": C1, "c2": mul(C1, C1)}
check("C₃ 嵌入（9 对）", all(mul(C3S[a], C3S[b]) == C3S[cmul(a, b)] for a in CC for b in CC))
check("act == SL23 共轭（24 条）",
      all(conj(C3S[c], q) == Q8S[ACT[(c, q)]] for c in CC for q in QS))
check("Q₈ ∩ C₃ = {1}", set(Q8S.values()) & set(C3S.values()) == {E})
if fail:
    sys.exit(1)

# ── §4. 唯一分解 + 同态 ──────────────────────────────────────────────────────
print("§4 分解与同态")
prod = {mul(Q8S[q], C3S[c]): (q, c) for q in QS for c in CC}
check("Q₈·C₃ = SL23（24 个互异元素）", len(prod) == 24 and set(prod) == set(GS))
if fail:
    sys.exit(1)

TOBT = dict(prod)
FROMBT = {prod[g]: g for g in GS}


def bt_mul(a, b):
    return (qmul(a[0], ACT[(a[1], b[0])]), cmul(a[1], b[1]))


bad = [(a, b) for a in GS for b in GS if TOBT[mul(a, b)] != bt_mul(TOBT[a], TOBT[b])]
check("toBT 保乘法（576 对）", not bad, f"{len(bad)} 对失败" if bad else "")
if bad:
    print("  样例:", bad[:5])
    sys.exit(1)

# ── §5. 生成 Agda ───────────────────────────────────────────────────────────
print("§5 生成", OUT.relative_to(ROOT))

rows = "\n\n".join(
    f"-- {g} 行\n"
    f"toBT-hom-{g} : ∀ (y : SL23) → toBT ({g} ⊗ y) ≡ toBT {g} *bt toBT y\n"
    + "\n".join(f"toBT-hom-{g} {h:<4s} = refl" for h in GS)
    for g in GS
)

tbl_to = "\n".join(f"toBT {g:<4s} = mkBT {TOBT[g][0]:<4s} {TOBT[g][1]}" for g in GS)
tbl_from = "\n".join(
    f"fromBT (mkBT {q:<4s} {c}) = {FROMBT[(q, c)]}" for c in CC for q in QS
)
cl_to_from = "\n".join(f"fromBT-is-section (mkBT {q:<4s} {c}) = refl" for c in CC for q in QS)
cl_from_to = "\n".join(f"fromBT-is-retraction {g:<4s} = refl" for g in GS)
dispatch = "\n".join(f"toBT-hom {g:<4s} = toBT-hom-{g}" for g in GS)

HEADER = f"""{{-# OPTIONS --rewriting --guardedness #-}}

-- | Sovereign.Synthesis.A4.SL23ToBT
--
-- **SL(2,3) ≅ 2A₄ ≅ Q₈ ⋊ C₃**——两张独立构造的 24 元素群之间的**群同构**。
--
-- 库里此前有两条互不相接的线：
--   · `BinaryTetrahedral`：2A₄ = Q₈ ⋊ C₃（`data Q8` + `data C3G` + `record BT`），
--     乘法是少数几条规则（`_*q_` 64 / `_*c_` 7 / `act` 24）；
--   · `BinaryTetrahedralDefiningRep` + `SL23Cayley`：SL(2,3) = {{det=1 的 GF(3) 2×2 矩阵}}，
--     乘法是 **576 条不透明查找表**。
--   两边都是「24 个元素」，但从未证明是同一个群。本文件补上这一环。
--
-- 【为什么值得做】同构一通，`BT` 侧的半直积结构（Q₈ 正规、C₃ 三循环作用、
--   中心 Z₂ = {{(1,c₀),(−1,c₀)}}）立刻可搬到 SL(2,3) 侧；`V2Orbit`/`V2Simple`/
--   `V2GMapWeight` 那条「V₂ 是正则表示的商」的链，所依赖的「24 槽 = Q₈×C₃ 坐标化」
--   由此获得群论底座。
--
-- 【证明策略：表对表，576 案不可约】
--   SL23 是不透明 24 构造子 data，`_⊗_` 是 576 条查找表，无生成元/字表示可归纳；
--   `toBT` 自身也是 24 条显式表。命题内容是「两张表相容」的 576 条独立事实，
--   逐条归约不可约。按「单引理 ≤27 案」纪律，按第一参数分解成 24 个行引理
--   （每个 ∀ y，24 案）再组装——与 `ToA4Hom.toA4-hom`、`BilinearSchur2A4.toME-hom`
--   同一纪律（BilinearSchur2A4.agda:252）。
--
-- 【表的来源：机器生成 + 双重验证，非手抄】
--   `scripts/gen_sl23_to_bt.py` 就地解析所依赖的四个 Agda 表并检验：
--     ① Q₈ ⊂ SL23（64 对）、C₃ ⊂ SL23（9 对）；
--     ② `act(c,·)` 恰等于 SL23 中按 c ∈ C₃ 的**共轭**（24 条）——这是半直积能与
--        SL23 相容的**充要条件**，无它则 `toBT` 不可能保乘法；
--     ③ Q₈·C₃ 覆盖全部 24 元素且互异（Q₈ ∩ C₃ = {{1}} ⇒ 分解唯一）；
--     ④ 576 对逐条验证 `toBT (a ⊗ b) ≡ toBT a *bt toBT b`。
--   任一检查不过，脚本 exit 1、不产出文件。
--   本文件内的 `toBT-hom` 576 条 refl 是 Agda 侧对同一结论的**独立复核**。
--
-- 【层级边界（重要）】本模块只做**群层**同构：对象是 24 个符号及其乘法表，
--   不涉及系数域。Z[ω] 只在把 2A₄ **线性化**成二维旋量表示时才进场
--   （`SpinNoInvariantLine` / `BilinearSchur2A4` 那一层）；把本同构读成
--   「Z[ω] 上的表示等价」是越级。群层同构是表示层的**前置**，不是替代。
--
-- ═══════════════════════════════════════════════════════════════
-- 八要素对照（形状规范: docs/maps/八要素统一形状-2026-10-14.md）
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      `toBT` / `fromBT`：SL23 ↔ BT 的 24↔24 双射表（§1、§2）
--  ② 生成元    Q₈ 的 i/j/k = {I}/{J}/{K}（阶 4、反交换），C₃ 的 ω = {C1}（阶 3）
--  ③ 关系      `toBT-hom`（576 案）+ `fromBT-is-section`/`fromBT-is-retraction`（各 24 案）
--  ④ 相位      `act c1` 的三循环 i→j→k→i —— C₃ 在 Q₈ 上的自同构相位
--  ⑤ 时钟      C₃ 的 ω³ = 1（`c2 = c1*c1`，本文件经 `_*c_` 表复用）
--  ⑥ 归零      `toBT-minus1`：中心 −1 ↦ (`qm1`, `c0`)
--  ⑦ 刚性      Q₈ ∩ C₃ = {{1}} ⇒ 分解唯一（脚本 ③ 已验，§1 表逐项体现）
--  ⑧ 核对      `iso`：`fromBT-is-section` / `fromBT-is-retraction` 共 48 条 refl + `toBT-injective`
--
-- 形状贴合: **8/8**
--
-- 0 postulate / 0 hole；零浮点。
module Sovereign.Synthesis.A4.SL23ToBT where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Synthesis.A4.BinaryTetrahedral
  using ( Q8; q1; qm1; qi; qmi; qj; qmj; qk; qmk
        ; C3G; c0; c1; c2
        ; BT; mkBT; _*bt_; bt-id; act; _*q_; _*c_ )
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using ( SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23 )
open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)

--------------------------------------------------------------------------------
-- §1. 分解表 SL23 → Q₈ × C₃
--
-- 每个 g 唯一写成 q·c（q ∈ Q₈，c ∈ C₃）。表由 `scripts/gen_sl23_to_bt.py`
-- 从 `_⊗_` 表解析得到，并已验证 576 对同态性（见文件头「表的来源」）。
--------------------------------------------------------------------------------

toBT : SL23 → BT
{tbl_to}

fromBT : BT → SL23
{tbl_from}
"""

BODY = f"""
--------------------------------------------------------------------------------
-- §2. 双射：往返恒等（24 + 24 案，全 refl——两张表互为逆）
--------------------------------------------------------------------------------

fromBT-is-section : ∀ (b : BT) → toBT (fromBT b) ≡ b
{cl_to_from}

fromBT-is-retraction : ∀ (x : SL23) → fromBT (toBT x) ≡ x
{cl_from_to}

-- 双射的直接推论：toBT 单射（不重新枚举，走往返消去）
toBT-injective : ∀ {{x y : SL23}} → toBT x ≡ toBT y → x ≡ y
toBT-injective {{x}} {{y}} p =
  begin
    x                      ≡⟨ sym (fromBT-is-retraction x) ⟩
    fromBT (toBT x)        ≡⟨ cong fromBT p ⟩
    fromBT (toBT y)        ≡⟨ fromBT-is-retraction y ⟩
    y                      ∎

--------------------------------------------------------------------------------
-- §3. 单位与中心
--------------------------------------------------------------------------------

toBT-e : toBT g6 ≡ bt-id
toBT-e = refl

-- 中心 −1（Q₈ 的中心，被 C₃ 固定）在 SL23 侧是 {MINUS1}
toBT-minus1 : toBT {MINUS1} ≡ mkBT qm1 c0
toBT-minus1 = refl

--------------------------------------------------------------------------------
-- §4. 同态性：toBT (x ⊗ y) ≡ toBT x *bt toBT y（24 行 × 24 案 = 576 对）
--
-- 【为何是穷举】见文件头「证明策略」：`_⊗_` 与 `toBT` 都是不透明 24 条表，
-- 命题是两张表相容的 576 条独立事实。按第一参数分解成 24 个行引理再组装。
--------------------------------------------------------------------------------

{rows}

toBT-hom : ∀ (x y : SL23) → toBT (x ⊗ y) ≡ toBT x *bt toBT y
{dispatch}

--------------------------------------------------------------------------------
-- §5. 打包：群同构（4 个 field 把上面的结论固定成一条可复用命题）
--------------------------------------------------------------------------------

record GroupIso : Set where
  field
    to   : SL23 → BT
    from : BT → SL23
    hom  : ∀ (x y : SL23) → to (x ⊗ y) ≡ to x *bt to y
    -- `from` 是 `to` 的 section：to ∘ from ≡ id
    from-is-section    : ∀ (b : BT) → to (from b) ≡ b
    -- `from` 是 `to` 的 retraction：from ∘ to ≡ id
    from-is-retraction : ∀ (x : SL23) → from (to x) ≡ x

-- [主定理] SL(2,3) ≅ 2A₄ = Q₈ ⋊ C₃
sl23≅bt : GroupIso
sl23≅bt = record
  {{ to                 = toBT
   ; from               = fromBT
   ; hom                = toBT-hom
   ; from-is-section    = fromBT-is-section
   ; from-is-retraction = fromBT-is-retraction
  }}
"""

DOC = HEADER + BODY

OUT.write_text(DOC)
print(f"   已写出 {len(DOC.splitlines())} 行")
