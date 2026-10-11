{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI5h —— TriFill 非退化面生成元 + 经典对齐定理骨架
--
-- 数学背景：_PPI5g 立界件「气泡移动生成一切 2-腔同伦」的对齐定理需两类生成元：
--   气泡类（BubbleMove——s∘s⁻¹ 退化形，已由 bubble-complete 证入 Ω3Walk⁺）与
--   **真三角面类（TriFill——非退化形）**。二者区别（本件核心）：
--   fill-tri 消的是「s ∘ s⁻¹」退化气泡（同一三角捷径数据往返——不含面本体）；
--   TriFill 消的是「绕面环」rot f——真三角面携带的 2-圈填充对象（B2 正解②口径：
--   面是结构的一部分，面本体携带其绕行环；非退化 = 面不是捷径三元组的回声）。
-- 核心原则：
-- 1. TriFace = 真三角面数据（非退化三元组 + 反向边 + 面环 rot）——关系入定义；
-- 2. TriFill 生成元 = 面环插入/删除（BubbleMove 形同款）；
-- 3. 方向一（生成元序列 ⊆ Ω3Walk⁺）于**气泡可分解面类**全证（tri-fill-sound）；
--    一般面类（rot 非气泡形）方向一/二均为经典对齐定理内容——如实立界（Dir2 陈述件）；
-- 4. S²ᵈ 实例：面 (0,1,2)/(0,1,3) 的 rot 恰为气泡形（K4 捷径齐备）——核对 ×6。
--
-- 包含：tri-bnd｜TriFace（y/z/e1/e2/e3/e3r/rot + bnd）｜BubbleRot｜TriFill（tri-f）
--       ｜tri-fill-sound（方向一气泡子类）｜dir1-bm｜GenClosure｜Dir2（陈述件）｜S²ᵈ 核对 ×6

module _PPI5h where

-- ② 导入区
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; subst)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil; cons; AStep)
open import _PPI5d using (Ω2Walk; nil2; cons2; s2-adj; s2v0; s2v1; s2v2; s2v3;
                          S2edge; s01; s12; s20; s02; s13; s30; s03;
                          w3; w3b; w'; omega2-wit; face012-slide; face013-slide)
open import _PPI5f using (Ω3Walk; omega2-witb)
open import _PPI5g using (_++2_; bub; Ω3Step⁺; Ω3Walk⁺; gen3+; bub3;
                          BubbleMove; bubble-complete)

-- ③ 基础件层：真三角面（非退化——关系入定义）
-- ────────────────────────────────────────────────────────────────────

-- 边界走：三角面 (x,y,z) 的三条边界边按序走（x→y→z→x）
tri-bnd : {G : DiGraph} {x y z : DiGraph.V G}
          (e1 : DiGraph.edge G x y) (e2 : DiGraph.edge G y z) (e3r : DiGraph.edge G z x) →
          Walk G x x
tri-bnd e1 e2 e3r = cons e1 (cons e2 (cons e3r (nil _)))

-- TriFace：真三角面数据——非退化三元组（x,y,z 互异的三条边 + 捷径 e3 + 闭边 e3r）
-- + 面环 rot（面本体携带的绕面 2-圈——B2 正解②：填充对象是面的组成部分）。
record TriFace (G : DiGraph) (x : DiGraph.V G) : Set where
  field
    y z : DiGraph.V G
    e1  : DiGraph.edge G x y
    e2  : DiGraph.edge G y z
    e3  : DiGraph.edge G x z
    e3r : DiGraph.edge G z x
    rot : Ω2Walk G x (tri-bnd e1 e2 e3r) (tri-bnd e1 e2 e3r)

  -- 面的边界走（对外接口形）
  bnd : Walk G x x
  bnd = tri-bnd e1 e2 e3r

-- 气泡可分解子类：面环恰为 s∘s⁻¹ 退化形（此时方向一可证）
BubbleRot : (G : DiGraph) (x : DiGraph.V G) (f : TriFace G x) → Set
BubbleRot G x f =
  Σ[ w' ∈ Walk G x x ] Σ[ s ∈ AStep G (TriFace.bnd f) w' ] (TriFace.rot f ≡ bub s)

-- ④ 主引理层：TriFill 生成元 + 方向一（气泡子类）
-- ────────────────────────────────────────────────────────────────────

-- TriFill：非退化三角面填充生成元——面环 rot f 的插入/删除（BubbleMove 同款形）。
-- 语义：绕面环 2-圈是 3-可缩的（面的填充 = 3-腔本体数据）。
data TriFill (G : DiGraph) (x : DiGraph.V G) :
             {w : Walk G x x} → Ω2Walk G x w w → Ω2Walk G x w w → Set where
  tri-f : (f : TriFace G x) (c₁ c₂ : Ω2Walk G x (TriFace.bnd f) (TriFace.bnd f)) →
          TriFill G x ((c₁ ++2 TriFace.rot f) ++2 c₂) (c₁ ++2 c₂)

-- 方向一（气泡可分解面类）：TriFill 步 ⊆ Ω3Walk⁺。
-- 证明：rot f ≡ bub s 代入 + bub3（任意位气泡消去）+ gen3+ 嵌入。
-- ⚠ subst 方向（教训族）：eq : rot f ≡ bub s，源端是 bub s 形——须 sym eq 搬运。
tri-fill-sound : {G : DiGraph} {x : DiGraph.V G} (f : TriFace G x) →
                 BubbleRot G x f →
                 (c₁ c₂ : Ω2Walk G x (TriFace.bnd f) (TriFace.bnd f)) →
                 Ω3Walk⁺ G x ((c₁ ++2 TriFace.rot f) ++2 c₂) (c₁ ++2 c₂)
tri-fill-sound f (w' , s , eq) c₁ c₂ =
  subst (λ t → Ω3Walk⁺ _ _ ((c₁ ++2 t) ++2 c₂) (c₁ ++2 c₂)) (sym eq)
        (gen3+ (bub3 c₁ s c₂))

-- 方向一（气泡侧）：BubbleMove 步 ⊆ Ω3Walk⁺（_PPI5g bubble-complete 直引零重证）
dir1-bm : {G : DiGraph} {x : DiGraph.V G} {w : Walk G x x} {c c' : Ω2Walk G x w w} →
          BubbleMove G x c c' → Ω3Walk⁺ G x c c'
dir1-bm = bubble-complete

-- ⑤ 组合层：生成闭包 + 对齐定理陈述件
-- ────────────────────────────────────────────────────────────────────

-- 生成闭包：BubbleMove ∪ TriFill 生成的等价闭包（2-腔环面上）
data GenClosure (G : DiGraph) (x : DiGraph.V G) :
                {w : Walk G x x} → Ω2Walk G x w w → Ω2Walk G x w w → Set where
  gc-refl  : {w : Walk G x x} (c : Ω2Walk G x w w) → GenClosure G x c c
  gc-symm  : {w : Walk G x x} {c c' : Ω2Walk G x w w} →
             GenClosure G x c c' → GenClosure G x c' c
  gc-trans : {w : Walk G x x} {c c' c'' : Ω2Walk G x w w} →
             GenClosure G x c c' → GenClosure G x c' c'' → GenClosure G x c c''
  gc-bm    : {w : Walk G x x} {c c' : Ω2Walk G x w w} →
             BubbleMove G x c c' → GenClosure G x c c'
  gc-tf    : {w : Walk G x x} {c c' : Ω2Walk G x w w} →
             TriFill G x c c' → GenClosure G x c c'

-- 对齐定理方向二（**陈述件——立界非定理**）：
-- 「任意 3-塌缩 ∼ 生成元序列」= Ω3Walk ⊆ GenClosure。
-- 现状：方向一于气泡可分解面类已证（tri-fill-sound + dir1-bm）；
-- 方向二需 (a) fill-tri 的气泡可由 TriFill 表出（一般图中该气泡未必是某面的 rot）
--        (b) 3-塌缩完备性（_PPI5g 经典对齐立界件）——如实立界，不硬证。
Dir2 : (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) → Set
Dir2 G x w = {c c' : Ω2Walk G x w w} → Ω3Walk G x c c' → GenClosure G x c c'

-- ⑥ 核对层：S²ᵈ 三角面生成元实例（w3/w3b）
-- ────────────────────────────────────────────────────────────────────

-- 面 (0,1,2)：w3 的真三角面——rot := omega2-wit（K4 捷径齐备 ⇒ 面环恰为气泡形）
face012 : TriFace s2-adj s2v0
face012 = record { y = s2v1 ; z = s2v2 ; e1 = s01 ; e2 = s12 ; e3 = s02 ; e3r = s20
                 ; rot = omega2-wit }

chk-bnd-012 : TriFace.bnd face012 ≡ w3
chk-bnd-012 = refl

rot012-bub : BubbleRot s2-adj s2v0 face012
rot012-bub = _ , face012-slide , refl

-- TriFill 生成元核对（w3 侧）：面环插入/删除
chk-trifill-w3 : TriFill s2-adj s2v0 omega2-wit (nil2 w3)
chk-trifill-w3 = tri-f face012 (nil2 w3) (nil2 w3)

-- 方向一核对（w3 侧）：经 TriFill 路径回收 omega2-wit-triv 的结论形
chk-tri-sound-w3 : Ω3Walk⁺ s2-adj s2v0 omega2-wit (nil2 w3)
chk-tri-sound-w3 = tri-fill-sound face012 rot012-bub (nil2 w3) (nil2 w3)

-- 面 (0,1,3)：w3b 的真三角面——对称件
face013 : TriFace s2-adj s2v0
face013 = record { y = s2v1 ; z = s2v3 ; e1 = s01 ; e2 = s13 ; e3 = s03 ; e3r = s30
                 ; rot = omega2-witb }

rot013-bub : BubbleRot s2-adj s2v0 face013
rot013-bub = _ , face013-slide , refl

chk-trifill-w3b : TriFill s2-adj s2v0 omega2-witb (nil2 w3b)
chk-trifill-w3b = tri-f face013 (nil2 w3b) (nil2 w3b)

chk-tri-sound-w3b : Ω3Walk⁺ s2-adj s2v0 omega2-witb (nil2 w3b)
chk-tri-sound-w3b = tri-fill-sound face013 rot013-bub (nil2 w3b) (nil2 w3b)
