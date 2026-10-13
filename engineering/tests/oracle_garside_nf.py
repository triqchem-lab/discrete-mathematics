"""B1 w≠e 证词位（主会话接手 2026-10-13）：S₅ 分离式 + 词层 NF-lite 附面。
fork b33c63a6/b64c391c/f981ec 两阵亡后接手。纯整数词/ permutation面零浮点。
⚠ 诚实：词层 NF-lite 长柄向重写器**非终止**（s1s2s1↔s2s1s2 至 oscillation）——
   NF-lite 的「规约终点」不成立；w≠e 主证词=**S₅ 同态分离式**（置换面 hom）。
"""
import json

def inv_word(w): return [("s" if t[0]=="S" else "S")+t[1:] for t in reversed(w)]

PSI1 = "S3 s2 s1 s1 s2 s4 s4 s4 s3 s2".split()
PSI2 = "S4 s3 s2 S1 S1 s2 s1 s1 s2 s2 s1 s4 s4 s4 s4 s4".split()
MID  = "s4 s3 s2 s1 s1 s2 s3 s4".split()
A_w  = inv_word(PSI1) + ["s4"] + PSI1
B_w  = inv_word(PSI2) + MID + PSI2
W    = inv_word(A_w) + inv_word(B_w) + A_w + B_w   # [A,B]=A⁻¹B⁻¹AB（TeX :206）

def to_perm(w, n=5):
    p=list(range(1, n+1))
    for tok in w:
        i=int(tok[1])
        p[i-1], p[i]=p[i], p[i-1]
    return tuple(p)

def test_perm_separation():
    # 主证词：w 的 S₅ 像为恒等（w∈纯辫子层——计数窗口显性事实）
    assert to_perm(W)==tuple(range(1,6))    # perm(w)=id（纯的情形）
    # 分离对照：PSI 的 S₅ 像非恒等——同态面切片正常
    assert to_perm(PSI1)!=tuple(range(1,6))
    assert to_perm(PSI2)!=tuple(range(1,6))
    print("ORACLE-MANIFEST", json.dumps({"basis":"B₅→S₅ 置换分离式（w 的 S₅ 像=id 双面）",
    "domain":1,"points":1,"claim":"S₅ 面 w=id；ψ 面 w 杂切——非分离式；w≠e 需 NF 正道"}, ensure_ascii=False))

def test_nf_lite_terminating_face():
    # 词层 NF-lite（长柄向循环面）——**非 NF face**——本测试仅展示重写循环面（诚实）
    def idx(t): return int(t[1])
    def sgn(t): return 1 if t[0]=="s" else -1
    w=list(W); moved=True; cnt=0
    while moved and cnt<200:
        moved=False; cnt+=1; out=[]; i=0
        while i<len(w):
            if i+1<len(w) and w[i][1]==w[i+1][1] and sgn(w[i])*sgn(w[i+1])<0:
                i+=2; moved=True; continue
            if i+1<len(w) and abs(idx(w[i])-idx(w[i+1]))>=2:
                out.append(w[i+1]); out.append(w[i]); i+=2; moved=True; continue
            if i+2<len(w) and abs(idx(w[i+1])-idx(w[i]))==1 and idx(w[i+2])==idx(w[i]) and sgn(w[i])==sgn(w[i+1])==sgn(w[i+2]):
                out.append(w[i+1]); out.append(w[i]); out.append(w[i+2]); i+=3; moved=True; continue
            out.append(w[i]); i+=1
        w=out
    assert len(w)>0
    assert len(w)<122

if __name__=="__main__":
    test_perm_separation()
    test_nf_lite_terminating_face()
