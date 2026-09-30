{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.GF4
-- GF(4) = GF(2)[α]/(α²+α+1): 四元域, 完整域公理 (0 postulate)
--
-- 元素 {0, 1, α, α+1}, 特征 2 (x+x=0), α²=α+1, α(α+1)=1, (α+1)²=α。
-- 用于 GF(4) → 正交拉丁方 → 幻方的域论生成链; 与 GF(3)/GF(9)/GF(27) 并列。
-- 判型符号化（≤64-case 表 → rep/Bit 代数链）

module Sovereign.Structology.GF4 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

--------------------------------------------------------------------------------
-- §1. GF(4) 元素
--------------------------------------------------------------------------------

data GF4 : Set where
  g0 : GF4   -- 0
  g1 : GF4   -- 1
  ga : GF4   -- α
  gb : GF4   -- α+1

-- 到 Fin 4 的索引
toFin : GF4 → Fin 4
toFin g0 = zero
toFin g1 = suc zero
toFin ga = suc (suc zero)
toFin gb = suc (suc (suc zero))

fromFin : Fin 4 → GF4
fromFin zero = g0
fromFin (suc zero) = g1
fromFin (suc (suc zero)) = ga
fromFin (suc (suc (suc zero))) = gb

toFin-fromFin : (x : GF4) → fromFin (toFin x) ≡ x
toFin-fromFin g0 = refl
toFin-fromFin g1 = refl
toFin-fromFin ga = refl
toFin-fromFin gb = refl

--------------------------------------------------------------------------------
-- §2. 加法 (特征 2)
--------------------------------------------------------------------------------

add4 : GF4 → GF4 → GF4
add4 g0 g0 = g0
add4 g0 g1 = g1
add4 g0 ga = ga
add4 g0 gb = gb
add4 g1 g0 = g1
add4 g1 g1 = g0
add4 g1 ga = gb
add4 g1 gb = ga
add4 ga g0 = ga
add4 ga g1 = gb
add4 ga ga = g0
add4 ga gb = g1
add4 gb g0 = gb
add4 gb g1 = ga
add4 gb ga = g1
add4 gb gb = g0

neg4 : GF4 → GF4   -- 特征 2: -x = x
neg4 g0 = g0
neg4 g1 = g1
neg4 ga = ga
neg4 gb = gb

--------------------------------------------------------------------------------
-- §3. 乘法 (α² = α+1)
--------------------------------------------------------------------------------

mul4 : GF4 → GF4 → GF4
mul4 g0 g0 = g0
mul4 g0 g1 = g0
mul4 g0 ga = g0
mul4 g0 gb = g0
mul4 g1 g0 = g0
mul4 g1 g1 = g1
mul4 g1 ga = ga
mul4 g1 gb = gb
mul4 ga g0 = g0
mul4 ga g1 = ga
mul4 ga ga = gb
mul4 ga gb = g1
mul4 gb g0 = g0
mul4 gb g1 = gb
mul4 gb ga = g1
mul4 gb gb = ga

--------------------------------------------------------------------------------
-- §4. 域公理 (全 refl 穷举)
--------------------------------------------------------------------------------

add4-comm : (x y : GF4) → add4 x y ≡ add4 y x
add4-comm g0 g0 = refl
add4-comm g0 g1 = refl
add4-comm g0 ga = refl
add4-comm g0 gb = refl
add4-comm g1 g0 = refl
add4-comm g1 g1 = refl
add4-comm g1 ga = refl
add4-comm g1 gb = refl
add4-comm ga g0 = refl
add4-comm ga g1 = refl
add4-comm ga ga = refl
add4-comm ga gb = refl
add4-comm gb g0 = refl
add4-comm gb g1 = refl
add4-comm gb ga = refl
add4-comm gb gb = refl

data Bit : Set where b0 b1 : Bit

bxor : Bit → Bit → Bit
bxor b0 b0 = b0
bxor b0 b1 = b1
bxor b1 b0 = b1
bxor b1 b1 = b0

band : Bit → Bit → Bit
band b1 b1 = b1
band b1 b0 = b0
band b0 b1 = b0
band b0 b0 = b0

bxor-comm : ∀ a b → bxor a b ≡ bxor b a
bxor-comm b0 b0 = refl
bxor-comm b0 b1 = refl
bxor-comm b1 b0 = refl
bxor-comm b1 b1 = refl

bxor-0r : ∀ a → bxor a b0 ≡ a
bxor-0r b0 = refl
bxor-0r b1 = refl

bxor-self : ∀ a → bxor a a ≡ b0
bxor-self b0 = refl
bxor-self b1 = refl

bxor-assoc : ∀ a b c → bxor (bxor a b) c ≡ bxor a (bxor b c)
bxor-assoc b0 b0 b0 = refl
bxor-assoc b0 b0 b1 = refl
bxor-assoc b0 b1 b0 = refl
bxor-assoc b0 b1 b1 = refl
bxor-assoc b1 b0 b0 = refl
bxor-assoc b1 b0 b1 = refl
bxor-assoc b1 b1 b0 = refl
bxor-assoc b1 b1 b1 = refl

bxor-swap4 : ∀ w x y z → bxor (bxor w x) (bxor y z) ≡ bxor (bxor w y) (bxor x z)
bxor-swap4 w x y z =
  trans (bxor-assoc w x (bxor y z))
  (trans (cong (bxor w) (sym (bxor-assoc x y z)))
  (trans (cong (λ v → bxor w (bxor v z)) (bxor-comm x y))
  (trans (cong (bxor w) (bxor-assoc y x z))
         (sym (bxor-assoc w y (bxor x z))))))

band-comm : ∀ a b → band a b ≡ band b a
band-comm b0 b0 = refl
band-comm b0 b1 = refl
band-comm b1 b0 = refl
band-comm b1 b1 = refl

band-bxor : ∀ a b c → band a (bxor b c) ≡ bxor (band a b) (band a c)
band-bxor b0 b0 b0 = refl
band-bxor b0 b0 b1 = refl
band-bxor b0 b1 b0 = refl
band-bxor b0 b1 b1 = refl
band-bxor b1 b0 b0 = refl
band-bxor b1 b0 b1 = refl
band-bxor b1 b1 b0 = refl
band-bxor b1 b1 b1 = refl

rep : GF4 → Bit × Bit
rep g0 = b0 , b0
rep g1 = b1 , b0
rep ga = b0 , b1
rep gb = b1 , b1

rep-inj : ∀ x y → rep x ≡ rep y → x ≡ y
rep-inj g0 g0 _ = refl
rep-inj g1 g1 _ = refl
rep-inj ga ga _ = refl
rep-inj gb gb _ = refl
rep-inj g0 g1 ()
rep-inj g0 ga ()
rep-inj g0 gb ()
rep-inj g1 g0 ()
rep-inj g1 ga ()
rep-inj g1 gb ()
rep-inj ga g0 ()
rep-inj ga g1 ()
rep-inj ga gb ()
rep-inj gb g0 ()
rep-inj gb g1 ()
rep-inj gb ga ()

padd : Bit × Bit → Bit × Bit → Bit × Bit
padd (a , b) (c , d) = bxor a c , bxor b d

pmul : Bit × Bit → Bit × Bit → Bit × Bit
pmul (a , b) (c , d) = bxor (band a c) (band b d)
                     , bxor (bxor (band a d) (band b c)) (band b d)

rep-add : ∀ x y → rep (add4 x y) ≡ padd (rep x) (rep y)
rep-add g0 g0 = refl
rep-add g0 g1 = refl
rep-add g0 ga = refl
rep-add g0 gb = refl
rep-add g1 g0 = refl
rep-add g1 g1 = refl
rep-add g1 ga = refl
rep-add g1 gb = refl
rep-add ga g0 = refl
rep-add ga g1 = refl
rep-add ga ga = refl
rep-add ga gb = refl
rep-add gb g0 = refl
rep-add gb g1 = refl
rep-add gb ga = refl
rep-add gb gb = refl

rep-mul : ∀ x y → rep (mul4 x y) ≡ pmul (rep x) (rep y)
rep-mul g0 g0 = refl
rep-mul g0 g1 = refl
rep-mul g0 ga = refl
rep-mul g0 gb = refl
rep-mul g1 g0 = refl
rep-mul g1 g1 = refl
rep-mul g1 ga = refl
rep-mul g1 gb = refl
rep-mul ga g0 = refl
rep-mul ga g1 = refl
rep-mul ga ga = refl
rep-mul ga gb = refl
rep-mul gb g0 = refl
rep-mul gb g1 = refl
rep-mul gb ga = refl
rep-mul gb gb = refl

padd-assoc : ∀ x y z → padd (padd x y) z ≡ padd x (padd y z)
padd-assoc (a , b) (c , d) (e , f) = cong₂ _,_ (bxor-assoc a c e) (bxor-assoc b d f)

-- structuralized add4-assoc
add4-assoc : ∀ x y z → add4 (add4 x y) z ≡ add4 x (add4 y z)
add4-assoc x y z = rep-inj (add4 (add4 x y) z) (add4 x (add4 y z))
  (trans (rep-add (add4 x y) z)
  (trans (cong (λ w → padd w (rep z)) (rep-add x y))
  (trans (padd-assoc (rep x) (rep y) (rep z))
  (trans (cong (padd (rep x)) (sym (rep-add y z)))
         (sym (rep-add x (add4 y z)))))))
add4-unit : (x : GF4) → add4 x g0 ≡ x
add4-unit g0 = refl
add4-unit g1 = refl
add4-unit ga = refl
add4-unit gb = refl

add4-inv : (x : GF4) → add4 x (neg4 x) ≡ g0
add4-inv g0 = refl
add4-inv g1 = refl
add4-inv ga = refl
add4-inv gb = refl

mul4-comm : (x y : GF4) → mul4 x y ≡ mul4 y x
mul4-comm g0 g0 = refl
mul4-comm g0 g1 = refl
mul4-comm g0 ga = refl
mul4-comm g0 gb = refl
mul4-comm g1 g0 = refl
mul4-comm g1 g1 = refl
mul4-comm g1 ga = refl
mul4-comm g1 gb = refl
mul4-comm ga g0 = refl
mul4-comm ga g1 = refl
mul4-comm ga ga = refl
mul4-comm ga gb = refl
mul4-comm gb g0 = refl
mul4-comm gb g1 = refl
mul4-comm gb ga = refl
mul4-comm gb gb = refl

-- mul4-assoc 结构化定义见 §4.5（rep-inj 回拉 + pmul-assoc）

mul4-unit : (x : GF4) → mul4 x g1 ≡ x
mul4-unit g0 = refl
mul4-unit g1 = refl
mul4-unit ga = refl
mul4-unit gb = refl

mul4-zero : (x : GF4) → mul4 x g0 ≡ g0
mul4-zero g0 = refl
mul4-zero g1 = refl
mul4-zero ga = refl
mul4-zero gb = refl

-- structuralized distrib laws
bxor6-perm : ∀ A B C D E F → bxor (bxor (bxor A B) (bxor C D)) (bxor E F) ≡ bxor (bxor (bxor A C) E) (bxor (bxor B D) F)
bxor6-perm A B C D E F =
  trans (bxor-assoc (bxor A B) (bxor C D) (bxor E F))
  (trans (cong (bxor (bxor A B)) (bxor-swap4 C D E F))
  (trans (sym (bxor-assoc (bxor A B) (bxor C E) (bxor D F)))
  (trans (cong (λ w → bxor w (bxor D F)) (bxor-swap4 A B C E))
  (trans (bxor-assoc (bxor A C) (bxor B E) (bxor D F))
  (trans (cong (bxor (bxor A C)) (bxor-swap4 B E D F))
  (trans (sym (bxor-assoc (bxor A C) (bxor B D) (bxor E F)))
         (bxor-swap4 (bxor A C) (bxor B D) E F)))))))

band-bxorˡ : ∀ a b c → band (bxor a b) c ≡ bxor (band a c) (band b c)
band-bxorˡ a b c = trans (band-comm (bxor a b) c)
  (trans (band-bxor c a b) (cong₂ bxor (band-comm c a) (band-comm c b)))

--------------------------------------------------------------------------------
-- §4.5 判型符号化（≤64-case 表 → rep/Bit 代数链）
-- mul4 三律（结合 / 左右分配）原为各 64-case refl 表，超出判型阈 27。
-- 现经 rep-inj 回拉到 Bit×Bit 层：pmul 的结合与分配由 bxor/band 代数律
-- （band-bxor / band-bxorˡ / band-assoc / bxor-assoc / bxor-comm /
--   bxor-swap4 / bxor6-perm）逐分量展开 + monomial 重排闭合。
--------------------------------------------------------------------------------

-- AND 结合律（三重积 monomial 归一化用）
band-assoc : ∀ a b c → band (band a b) c ≡ band a (band b c)
band-assoc b0 b0 b0 = refl
band-assoc b0 b0 b1 = refl
band-assoc b0 b1 b0 = refl
band-assoc b0 b1 b1 = refl
band-assoc b1 b0 b0 = refl
band-assoc b1 b0 b1 = refl
band-assoc b1 b1 b0 = refl
band-assoc b1 b1 b1 = refl

-- 左嵌套三项的末两项交换: (A⊕B)⊕C ≡ (A⊕C)⊕B
bxor3-swap : ∀ A B C → bxor (bxor A B) C ≡ bxor (bxor A C) B
bxor3-swap A B C =
  trans (bxor-assoc A B C)
  (trans (cong (bxor A) (bxor-comm B C))
         (sym (bxor-assoc A C B)))

-- 5 项 xor 重排: (A⊕B)⊕((C⊕D)⊕E) ≡ (A⊕C)⊕((D⊕B)⊕E)
bxor5-perm : ∀ A B C D E →
  bxor (bxor A B) (bxor (bxor C D) E) ≡ bxor (bxor A C) (bxor (bxor D B) E)
bxor5-perm A B C D E =
  trans (sym (bxor-assoc (bxor A B) (bxor C D) E))
  (trans (cong (λ w → bxor w E) (bxor-swap4 A B C D))
  (trans (bxor-assoc (bxor A C) (bxor B D) E)
         (cong (bxor (bxor A C)) (cong (λ w → bxor w E) (bxor-comm B D)))))

-- 8 项 xor 展平为左嵌套链
bxor8-flatten : ∀ A B C D E F G H →
  bxor (bxor (bxor A B) (bxor (bxor C D) E)) (bxor (bxor F G) H)
  ≡ bxor (bxor (bxor (bxor (bxor (bxor (bxor A B) C) D) E) F) G) H
bxor8-flatten A B C D E F G H =
  trans (cong (λ w → bxor w (bxor (bxor F G) H))
              (sym (bxor-assoc (bxor A B) (bxor C D) E)))
  (trans (cong (λ w → bxor (bxor w E) (bxor (bxor F G) H))
               (sym (bxor-assoc (bxor A B) C D)))
  (trans (sym (bxor-assoc (bxor (bxor (bxor (bxor A B) C) D) E) (bxor F G) H))
         (cong (λ w → bxor w H)
               (sym (bxor-assoc (bxor (bxor (bxor (bxor A B) C) D) E) F G)))))

-- 8 项 xor 链上对换（第一段：3 次相邻对换）
--   [A,B,C,D,E,F,G,H] → [A,C,B,F,D,E,G,H]
bxor8-swap-a : ∀ A B C D E F G H →
  bxor (bxor (bxor (bxor (bxor (bxor (bxor A B) C) D) E) F) G) H
  ≡ bxor (bxor (bxor (bxor (bxor (bxor (bxor A C) B) F) D) E) G) H
bxor8-swap-a A B C D E F G H =
  trans (cong (λ w → bxor (bxor (bxor (bxor (bxor w D) E) F) G) H) (bxor3-swap A B C))
  (trans (cong (λ w → bxor (bxor w G) H) (bxor3-swap (bxor (bxor (bxor A C) B) D) E F))
         (cong (λ w → bxor (bxor (bxor w E) G) H) (bxor3-swap (bxor (bxor A C) B) D F)))

-- 8 项 xor 链上对换（第二段：3 次相邻对换）
--   [A,C,B,F,D,E,G,H] → [A,C,F,D,B,G,E,H]
bxor8-swap-b : ∀ A B C D E F G H →
  bxor (bxor (bxor (bxor (bxor (bxor (bxor A C) B) F) D) E) G) H
  ≡ bxor (bxor (bxor (bxor (bxor (bxor (bxor A C) F) D) B) G) E) H
bxor8-swap-b A B C D E F G H =
  trans (cong (λ w → bxor (bxor (bxor (bxor w D) E) G) H) (bxor3-swap (bxor A C) B F))
  (trans (cong (λ w → bxor (bxor (bxor w E) G) H) (bxor3-swap (bxor (bxor A C) F) B D))
         (cong (λ w → bxor w H) (bxor3-swap (bxor (bxor (bxor (bxor A C) F) D) B) E G)))

-- 8 项 xor 链重塑为目标括号形状
--   [A,C,F,D,B,G,E,H] ≡ ((A⊕C)⊕F)⊕(D⊕B) ⊕ ((G⊕E)⊕H)
bxor8-shape : ∀ A B C D E F G H →
  bxor (bxor (bxor (bxor (bxor (bxor (bxor A C) F) D) B) G) E) H
  ≡ bxor (bxor (bxor (bxor A C) F) (bxor D B)) (bxor (bxor G E) H)
bxor8-shape A B C D E F G H =
  trans (cong (λ w → bxor (bxor (bxor w G) E) H) (bxor-assoc (bxor (bxor A C) F) D B))
  (trans (cong (λ w → bxor w H) (bxor-assoc (bxor (bxor (bxor A C) F) (bxor D B)) G E))
         (bxor-assoc (bxor (bxor (bxor A C) F) (bxor D B)) (bxor G E) H))

-- 8 项 xor 重排（链上 6 次相邻对换 + 3 步重塑括号）:
--   [A,B,C,D,E,F,G,H] → [A,C,F,D,B,G,E,H]
bxor8-sort : ∀ A B C D E F G H →
  bxor (bxor (bxor (bxor (bxor (bxor (bxor A B) C) D) E) F) G) H
  ≡ bxor (bxor (bxor (bxor A C) F) (bxor D B)) (bxor (bxor G E) H)
bxor8-sort A B C D E F G H =
  trans (bxor8-swap-a A B C D E F G H)
  (trans (bxor8-swap-b A B C D E F G H) (bxor8-shape A B C D E F G H))

-- 8 项 xor 重排（分组树入口）: 展平 + 链上重排
--   ((A⊕B)⊕((C⊕D)⊕E))⊕((F⊕G)⊕H) ≡ (((A⊕C)⊕F)⊕(D⊕B))⊕((G⊕E)⊕H)
bxor8-perm : ∀ A B C D E F G H →
  bxor (bxor (bxor A B) (bxor (bxor C D) E)) (bxor (bxor F G) H)
  ≡ bxor (bxor (bxor (bxor A C) F) (bxor D B)) (bxor (bxor G E) H)
bxor8-perm A B C D E F G H =
  trans (bxor8-flatten A B C D E F G H) (bxor8-sort A B C D E F G H)

-- pmul 结合律第 1 分量: 两侧展开为 5 个 monomial 后 5 项重排
--   (ac⊕bd)·e ⊕ ((ad⊕bc)⊕bd)·f ≡ a·(ce⊕df) ⊕ b·((cf⊕de)⊕df)
pmul-assoc-fst : ∀ a b c d e f →
  proj₁ (pmul (pmul (a , b) (c , d)) (e , f)) ≡ proj₁ (pmul (a , b) (pmul (c , d) (e , f)))
pmul-assoc-fst a b c d e f =
  trans (cong₂ bxor (band-bxorˡ (band a c) (band b d) e)
           (trans (band-bxorˡ (bxor (band a d) (band b c)) (band b d) f)
                  (cong (λ w → bxor w (band (band b d) f))
                        (band-bxorˡ (band a d) (band b c) f))))
  (trans (bxor5-perm (band (band a c) e) (band (band b d) e)
                     (band (band a d) f) (band (band b c) f) (band (band b d) f))
  (sym (cong₂ bxor
          (trans (band-bxor a (band c e) (band d f))
                 (cong₂ bxor (sym (band-assoc a c e)) (sym (band-assoc a d f))))
          (trans (band-bxor b (bxor (band c f) (band d e)) (band d f))
                 (cong₂ bxor
                   (trans (band-bxor b (band c f) (band d e))
                          (cong₂ bxor (sym (band-assoc b c f)) (sym (band-assoc b d e))))
                   (sym (band-assoc b d f)))))))

-- pmul 结合律第 2 分量: 两侧展开为 8 个 monomial 后 8 项重排
pmul-assoc-snd : ∀ a b c d e f →
  proj₂ (pmul (pmul (a , b) (c , d)) (e , f)) ≡ proj₂ (pmul (a , b) (pmul (c , d) (e , f)))
pmul-assoc-snd a b c d e f =
  trans (cong₂ bxor
           (cong₂ bxor
             (band-bxorˡ (band a c) (band b d) f)
             (trans (band-bxorˡ (bxor (band a d) (band b c)) (band b d) e)
                    (cong (λ w → bxor w (band (band b d) e))
                          (band-bxorˡ (band a d) (band b c) e))))
           (trans (band-bxorˡ (bxor (band a d) (band b c)) (band b d) f)
                  (cong (λ w → bxor w (band (band b d) f))
                        (band-bxorˡ (band a d) (band b c) f))))
  (trans (bxor8-perm (band (band a c) f) (band (band b d) f)
                     (band (band a d) e) (band (band b c) e)
                     (band (band b d) e) (band (band a d) f)
                     (band (band b c) f) (band (band b d) f))
  (sym (cong₂ bxor
          (cong₂ bxor
            (trans (band-bxor a (bxor (band c f) (band d e)) (band d f))
                   (cong₂ bxor
                     (trans (band-bxor a (band c f) (band d e))
                            (cong₂ bxor (sym (band-assoc a c f)) (sym (band-assoc a d e))))
                     (sym (band-assoc a d f))))
            (trans (band-bxor b (band c e) (band d f))
                   (cong₂ bxor (sym (band-assoc b c e)) (sym (band-assoc b d f)))))
          (trans (band-bxor b (bxor (band c f) (band d e)) (band d f))
                 (cong₂ bxor
                   (trans (band-bxor b (band c f) (band d e))
                          (cong₂ bxor (sym (band-assoc b c f)) (sym (band-assoc b d e))))
                   (sym (band-assoc b d f)))))))

-- Bit×Bit 上的乘法结合律（monomial 重排闭合）
pmul-assoc : ∀ x y z → pmul (pmul x y) z ≡ pmul x (pmul y z)
pmul-assoc (a , b) (c , d) (e , f) =
  cong₂ _,_ (pmul-assoc-fst a b c d e f) (pmul-assoc-snd a b c d e f)

-- mul4 结合律: rep-inj 回拉 + rep-mul + pmul-assoc（样例同 add4-assoc）
mul4-assoc : (x y z : GF4) → mul4 (mul4 x y) z ≡ mul4 x (mul4 y z)
mul4-assoc x y z = rep-inj (mul4 (mul4 x y) z) (mul4 x (mul4 y z))
  (trans (rep-mul (mul4 x y) z)
  (trans (cong (λ w → pmul w (rep z)) (rep-mul x y))
  (trans (pmul-assoc (rep x) (rep y) (rep z))
  (trans (cong (pmul (rep x)) (sym (rep-mul y z)))
         (sym (rep-mul x (mul4 y z)))))))

-- Bit×Bit 上的左分配: monomial 展开 + bxor-swap4 / bxor6-perm
pmul-distrib-l : ∀ x y z → pmul x (padd y z) ≡ padd (pmul x y) (pmul x z)
pmul-distrib-l (a , b) (c , d) (e , f) =
  cong₂ _,_
    (trans (cong₂ bxor (band-bxor a c e) (band-bxor b d f))
           (bxor-swap4 (band a c) (band a e) (band b d) (band b f)))
    (trans (cong₂ bxor (cong₂ bxor (band-bxor a d f) (band-bxor b c e)) (band-bxor b d f))
           (bxor6-perm (band a d) (band a f) (band b c) (band b e) (band b d) (band b f)))

-- Bit×Bit 上的右分配: monomial 展开 + bxor-swap4 / bxor6-perm
pmul-distrib-r : ∀ x y z → pmul (padd x y) z ≡ padd (pmul x z) (pmul y z)
pmul-distrib-r (a , b) (c , d) (e , f) =
  cong₂ _,_
    (trans (cong₂ bxor (band-bxorˡ a c e) (band-bxorˡ b d f))
           (bxor-swap4 (band a e) (band c e) (band b f) (band d f)))
    (trans (cong₂ bxor (cong₂ bxor (band-bxorˡ a c f) (band-bxorˡ b d e)) (band-bxorˡ b d f))
           (bxor6-perm (band a f) (band c f) (band b e) (band d e) (band b f) (band d f)))

distrib-left : ∀ x y z → mul4 x (add4 y z) ≡ add4 (mul4 x y) (mul4 x z)
distrib-left x y z = rep-inj (mul4 x (add4 y z)) (add4 (mul4 x y) (mul4 x z))
  (trans (rep-mul x (add4 y z))
  (trans (cong (pmul (rep x)) (rep-add y z))
  (trans (pmul-distrib-l (rep x) (rep y) (rep z))
  (trans (cong₂ padd (sym (rep-mul x y)) (sym (rep-mul x z)))
         (sym (rep-add (mul4 x y) (mul4 x z)))))))

distrib-right : ∀ x y z → mul4 (add4 x y) z ≡ add4 (mul4 x z) (mul4 y z)
distrib-right x y z = rep-inj (mul4 (add4 x y) z) (add4 (mul4 x z) (mul4 y z))
  (trans (rep-mul (add4 x y) z)
  (trans (cong (λ w → pmul w (rep z)) (rep-add x y))
  (trans (pmul-distrib-r (rep x) (rep y) (rep z))
  (trans (cong₂ padd (sym (rep-mul x z)) (sym (rep-mul y z)))
         (sym (rep-add (mul4 x z) (mul4 y z)))))))

mul4-inv : (x : GF4) → ¬ (x ≡ g0) → Σ GF4 (λ y → mul4 x y ≡ g1)
mul4-inv g0 ne = ⊥-elim (ne refl)
mul4-inv g1 ne = g1 , refl
mul4-inv ga ne = gb , refl   -- α·(α+1) = 1
mul4-inv gb ne = ga , refl   -- (α+1)·α = 1

--------------------------------------------------------------------------------
-- §5. 补充 L2 定理 (全称量化)
--------------------------------------------------------------------------------

-- 加法左单位元: 0 + x = x
add4-identityˡ : (x : GF4) → add4 g0 x ≡ x
add4-identityˡ g0 = refl
add4-identityˡ g1 = refl
add4-identityˡ ga = refl
add4-identityˡ gb = refl

-- 乘法左单位元: 1 * x = x
mul4-identityˡ : (x : GF4) → mul4 g1 x ≡ x
mul4-identityˡ g0 = refl
mul4-identityˡ g1 = refl
mul4-identityˡ ga = refl
mul4-identityˡ gb = refl

-- 特征 2: x + x = 0 (自逆)
add4-self : (x : GF4) → add4 x x ≡ g0
add4-self g0 = refl
add4-self g1 = refl
add4-self ga = refl
add4-self gb = refl

-- 否定恒等: -x = x (特征 2)
neg4-identity : (x : GF4) → neg4 x ≡ x
neg4-identity g0 = refl
neg4-identity g1 = refl
neg4-identity ga = refl
neg4-identity gb = refl

-- 零因子不存在: x*y=0 → x=0 ∨ y=0
gf4-no-zero-divisors : (x y : GF4) → mul4 x y ≡ g0 → (x ≡ g0) ⊎ (y ≡ g0)
gf4-no-zero-divisors g0 _ _ = Data.Sum.inj₁ refl
gf4-no-zero-divisors _ g0 _ = Data.Sum.inj₂ refl
gf4-no-zero-divisors g1 g1 ()
gf4-no-zero-divisors g1 ga ()
gf4-no-zero-divisors g1 gb ()
gf4-no-zero-divisors ga g1 ()
gf4-no-zero-divisors ga ga ()
gf4-no-zero-divisors ga gb ()
gf4-no-zero-divisors gb g1 ()
gf4-no-zero-divisors gb ga ()
gf4-no-zero-divisors gb gb ()

-- 平方映射: x² 的值 (α²=α+1, (α+1)²=α)
gf4-square-map : GF4 → GF4
gf4-square-map g0 = g0
gf4-square-map g1 = g1
gf4-square-map ga = gb  -- α² = α+1
gf4-square-map gb = ga  -- (α+1)² = α

gf4-squared : (x : GF4) → mul4 x x ≡ gf4-square-map x
gf4-squared g0 = refl
gf4-squared g1 = refl
gf4-squared ga = refl
gf4-squared gb = refl

-- 0 postulate.
