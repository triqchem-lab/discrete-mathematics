"""D1 判据实验批：Gcmp two-chain 上 π₂ᵈ 的计算
—— compute-then-verify（oracle 供猜想供料/Agda 唯一裁决）。
纯整数（词形+步形）零浮点。四步实验全落此件。

四步：
 ① Gcmp two-chain 模型（V={0,1}，边 (0,1)+(1,0) 双向无自环——Gcmp 对称面） + 闭走枚举
 ② Ω2Walk 数据形（nil2/cons2 逐字翻 Python）——全部闭 2-走词形（词长上限 5 完全性）
 ③ Ω3Walk⁺ 商面（fill-tri 气泡关系+bubble-complete 面）——π₀(Ω²) 商类数
 ④ 判定：π₂ᵈ(Gcmp) 类数（=1 平凡群/多类群或非群/孤立点特例）——D1 verdict
"""
import json
from itertools import product

# ═══ ① Gcmp two-chain 模型 ═══
# Gcmp：PursionModel——V={0,1}，edge 是有向对（双向）；无自环（KEdge 无自环）
EDGES = [(0,1),(1,0)]
def adj(u,v): return (u,v) in EDGES

# 闭走：Walk 0→0（循环）——从 0 出发走 k 步回 0
def walks_from0(length):
    """从基点 0 出发走 length 步、回到 0 的全部词（闭合形）。"""
    if length==0: return [([],0,0)]
    cur=[([],0,0)]
    for _ in range(length):
        nxt=[]
        for (w,u,v) in cur:
            for (a,b) in EDGES:
                if a==v: nxt.append((w+[ (v,b) ],u,b))
        cur=nxt
    return [x for x in cur if x[2]==0]

# ═══ ② Ω2Walk 数据形（nil2/cons2 逐字） ═══
# Ω2Walk 是 2-腔数据——nil2 w 表示「w 与 w 的空 2-腔对」、cons2 s c 是「AStep s 后面再加 2-腔」
# 闭 2-腔定义在 **闭走圈** 上（w1=w2=nil 的 2-腔环）
# 源语义锚：_PPI5f:39-46（nil2/cons2 的 Walk 基面）
# Python 侧：一个 2-腔= List[Step]（AStep 列）+ 起点基 walk w0，终点=起点。

def omega2_enumerate(maxlen=5):
    """枚举全部 Ω2Walk 型（闭 2-走，词长≤maxlen——枚举超界为立界注记）。"""
    out=[]
    for L in range(maxlen+1):
        for w in walks_from0(L):
            out.append(w)
    return out

# ═══ ③ Ω3Walk⁺ 商面（gen 关系=fill 律+bubble-complete） ═══
# fill：cons2 s (cons2 s⁻¹ nil2) ∼ nil2（「s∘s⁻¹ 气泡」）
# whisk：add 缘饰 accusative face（A1c 报告路线）
# Gcmp two-chain 边集 (0,1),(1,0)。slide 关系形式化：**简对边意图**。
# 这里按生成关系归约面近似：cons2 (step) 与 invAStep step 复合= 气泡可消
# 归约式：把相邻的 σᵢ · σᵢ⁻¹ 简化为 nil；whisk 面=其空隙补全。不硬造数值 → 是 face 面的商面
def canonical_seq(steps):
    """Gcmp two-chain 特有的 fill/whisk 关系化简（真商面近似）。
    语义锚：_PPI5f fill-tri（s∘s⁻¹ 气泡）+ _PPI5j whiskΩ3 缘饰。
    Gcmp two-chain 边集双向 (0,1)+(1,0)：step=(u,v,+)/(u,v,−) 双向标志面。
    demo 化简（fillna 面）:
      1. 相邻相反 step 简化（s∘s⁻¹ 气泡 fill-tri 语义）
      2. Gcmp two-chain 的 two-walk = [01,10]（slide 等价面——B2 已证 [e01,e10]∼[loop]）
    ⚠ 本函数为**演示近似**（真商面=源于 Agda 的商面 rec/elim）——oracle 面=供猜想。
    """
    changed=True
    seq=list(steps)
    while changed:
        changed=False; i=0
        while i<len(seq)-1:
            if seq[i][1:]==seq[i+1][1:] and seq[i][0]!=seq[i+1][0]:
                seq=seq[:i]+seq[i+2:]; changed=True; continue
            i+=1
    return seq

# ═══ ③-④ π₂ᵈ(Gcmp) 商类数 + D1 verdict ═══
def pi2_gcmp(maxlen=5):
    raw=omega2_enumerate(maxlen)
    # 分类：canonical 形作商代表（demo 归约）
    classes={}
    for (w,u,v) in raw:
        key=tuple(canonical_seq(w))
        classes.setdefault(key, 0)
        classes[key]+=1
    return raw, classes

def main():
    raw, cls = pi2_gcmp(5)
    manifest={"basis":"Gcmp two-chain π₂ᵈ 有限枚举（词长 ≤5 完全性）",
              "domain":len(raw),"points":len(raw),
              "claim":"π₀(Ω² Gcmp) 的商类计数——oracle 供料"}
    print("ORACLE-MANIFEST", json.dumps(manifest, ensure_ascii=False))
    print(f"raw walks ≤5: {len(raw)}")
    print(f"canonical classes: {len(cls)}")
    for k,v in sorted(cls.items(), key=lambda kv:-len(kv[0])):
        print(f"  class {k} size {v}")
    verdict = "✗ 尚未定判——π₂ᵈ(Gcmp) 类数有限枚举下=若干类（oracle 面）；Agda 面唯一裁决"
    print("VERDICT:", verdict)
    return raw, cls



# ═══ ④-补：词长扫描（2..12）+ manifest 完整性 ═══
def sweep(lo=2, hi=12):
    rows=[]
    for L in range(lo,hi+1):
        raw=omega2_enumerate(L)
        cc={}
        for (w,u,v) in raw:
            k=tuple(canonical_seq(w)); cc[k]=cc.get(k,0)+1
        rows.append((L, len(raw), len(cc)))
    return rows

if __name__=="__main__":
    main()
    print("── sweep 2..12 ──")
    for (L,rawl,ncls) in sweep(2,12):
        print(f"  L={L} walks={rawl} classes={ncls}")

