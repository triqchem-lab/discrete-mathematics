{-# OPTIONS --rewriting --guardedness #-}
-- | 探针 _PNormU：Laurent.norm-unique 攻坚件（唯一写域 = 本文件）
-- 数学背景：norm = insertCᵌ 并项折线（insert-last fold，LaurentSums.normC 同形）。
--   合并消 tie ⇒ `∀ xs ys → xs ↭ ys → norm xs ≡ norm ys` 免 Canon/NoZero 前提
--   （是 sort-unique 的严格加强：sort 需 Canon 前提排除 tie，norm 以合并消 tie）。
-- 攻坚路线（未来态锚定）：
--   norm-cong（↭ 归纳：refl/prep/swap/trans）
--     ├─ prep 案：normW-spec + insW-mono（IH 传导）
--     ├─ trans 案：≡ 传递（平凡）
--     └─ swap 案 = 核心：insW-swap（插入交换，合并/消去交互）★攻坚
-- 架构要点（v4 重构）：insF 返回 Σ（表值+Canon 证明）⇒ swap 双侧 Canon 证明分量
--   不等（gxy≠lyx），refl 卡证明项。正解 = insW 只取表值 + insW-irrel 证明无关引理
--   （Canon 证明不入表值计算——对 Canon 归纳证）+ 表级 swap 矩阵。
-- 机件地形（实测绘）：insertCᵌ 合并同指数项、零和丢弃（BTail）、孤零项保留
--   （insert (0,n) [] = [(0,n)]）。
-- ⚠【Stage 2 定谳：原「Statement 仍真」论断**错**】孤零反例击穿无条件版：
--   xs = (1,0)∷(0,0)∷(-1,0)∷[] 与 ys = (0,0)∷(1,0)∷(-1,0)∷[] 置换等价，
--   但 norm xs = []（(0,0) 先并入 (-1,0) → (1,0) 归零丢弃）而
--   norm ys = [(0,0)]（(1,0)+(-1,0) 先归零丢弃 → (0,0) 成孤零保留）⇒ 不等。
--   **修正版二选一**（与 norm-plus 的修正案同根）：(A) NoZero 前提版
--   （proj₁ x ≢ 0 ∧ proj₁ y ≢ 0 —— 孤零叶变 ⊥-elim，矩阵其余叶不受影响）；
--   (B) dropZ 规范化版（norm∘dropZ 无条件成立——原设计 dropZ∘merge∘sort 的补件）。
--   反证件见 §5；swap 矩阵按 (A) 重挂前提后路线不变。
-- 并发协调注记：LaurentSums 正被姊妹 fork 施工——本探针自含 normC 镜像（同定义形）。
-- 0 postulate / 0 hole（分阶段：未完件不落盘）。
module _PNormU where

open import Data.Integer using (ℤ; _<_; +_; _+_; -_)
open import Data.Integer.Properties
  using (_≟_; _<?_; +-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseʳ; <-irrefl; <-trans)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; _≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; prep; swap)
  renaming (refl to ↭-refl; trans to ↭-t)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; canon-nil; canon-one; canon-cons)
open import Sovereign.Algebra.LaurentNorm
  using (Cmp3; lt3; eq3; gt3; cmp3; SpecT; insertCᵌ)

-- ────────────────────────────────────────────────────────────────────
-- ① 基础件：insW（表值级插入）+ 证明无关 + norm 镜像
-- ────────────────────────────────────────────────────────────────────

-- 表值级插入：只取结果表（Canon 证明不入计算）
insW : (t : LaurentTerm) (ts : Laurent) → Canon ts → Laurent
insW t ts c = proj₁ (insertCᵌ t ts c)

-- 结果 Canon（供外层插入使用）
insC : (t : LaurentTerm) (ts : Laurent) (c : Canon ts) → Canon (insW t ts c)
insC t ts c = proj₁ (proj₂ (insertCᵌ t ts c))

-- norm 镜像（insert-last fold；与 LaurentSums.normC 同定义形）
normC : (ts : Laurent) → Σ[ w ∈ Laurent ] Canon w
normC [] = ([] , canon-nil)
normC (t ∷ ts) with normC ts
... | (w , cw) with insertCᵌ t w cw
...   | (w' , cw' , _) = (w' , cw')

norm : Laurent → Laurent
norm ts = proj₁ (normC ts)

normW-spec : ∀ t ts → norm (t ∷ ts) ≡ insW t (norm ts) (proj₂ (normC ts))
normW-spec t ts = refl

-- lt3 递归分支的形状：结果 = x ∷ （内层结果表）
lt3-cons-shape : ∀ t x x₂ xs p l s (spec : SpecT t (x₂ ∷ xs)) →
  proj₁ (Sovereign.Algebra.LaurentNorm.lt3-cons t x x₂ xs p l s spec)
  ≡ x ∷ proj₁ spec
lt3-cons-shape t x x₂ xs p l s (w , (cw , inj₁ b)) = refl
lt3-cons-shape t x x₂ xs p l s (w , (cw , inj₂ (h , (r , (eq , src))))) =
  cong (x ∷_) (sym eq)

-- 证明无关：Canon 证明不入表值计算（对 Canon 归纳）
insW-irrel : ∀ t ts (c1 c2 : Canon ts) → insW t ts c1 ≡ insW t ts c2
insW-irrel t [] canon-nil canon-nil = refl
insW-irrel t (x ∷ []) (canon-one .x) (canon-one .x) = refl
insW-irrel t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s) (canon-cons .x .x₂ .xs p' s')
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g = refl
... | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes z = refl
...   | no  n = refl
insW-irrel t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s) (canon-cons .x .x₂ .xs p' s')
  | lt3 _ _ l =
  trans (lt3-cons-shape t x x₂ xs p l s (insertCᵌ t (x₂ ∷ xs) s))
  (trans (cong (x ∷_) (insW-irrel t (x₂ ∷ xs) s s'))
  (sym (lt3-cons-shape t x x₂ xs p' l s' (insertCᵌ t (x₂ ∷ xs) s'))))

-- 同步表值：列表相等 ⇒ 插入结果相等（跨 Canon 证明）
insW-mono : ∀ t {w1 w2} (c1 : Canon w1) (c2 : Canon w2) →
  w1 ≡ w2 → insW t w1 c1 ≡ insW t w2 c2
insW-mono t {w1} {w2} c1 c2 refl = insW-irrel t w1 c1 c2

-- ────────────────────────────────────────────────────────────────────
-- ② swap 核心：插入交换（合并/消去交互）——攻坚件
-- ────────────────────────────────────────────────────────────────────

contra-< : ∀ {a b : ℤ} → a ≡ b → b < a → ⊥
contra-< refl p = <-irrefl refl p

-- 空基：insW x (y∷[]) ≡ insW y (x∷[])
-- 地形：spec-one 三分支（gt 前插 / eq 合并·零丢 / lt 后插）；
--   双向 cmp3 矩阵 + eq 案 ≟ 四向（交叉矛盾由 +-comm 消解）。
insW-swap0 : ∀ (x y : LaurentTerm) →
  insW x (y ∷ []) (canon-one y) ≡ insW y (x ∷ []) (canon-one x)
insW-swap0 x y with cmp3 (proj₂ x) (proj₂ y) | cmp3 (proj₂ y) (proj₂ x)
-- 一致对：两侧均 x ∷ y ∷ []
insW-swap0 x y | gt3 _ _ gxy | lt3 _ _ lyx = refl
insW-swap0 x y | lt3 _ _ lxy | gt3 _ _ gyx = refl
-- eq/eq 案：合并项（系数交换）或双丢弃
insW-swap0 x y | eq3 _ _ exy | eq3 _ _ eyx
  with (proj₁ x + proj₁ y) ≟ + 0 | (proj₁ y + proj₁ x) ≟ + 0
... | yes zxy | yes zyx = refl
... | no  nxy | no  nyx =
  trans (cong (λ c → (c , proj₂ x) ∷ []) (+-comm (proj₁ x) (proj₁ y)))
        (cong (λ e → (proj₁ y + proj₁ x , e) ∷ []) (sym eyx))
... | yes zxy | no  nyx =
  ⊥-elim (nyx (subst (λ c → c ≡ + 0) (+-comm (proj₁ x) (proj₁ y)) zxy))
... | no  nxy | yes zyx =
  ⊥-elim (nxy (subst (λ c → c ≡ + 0) (+-comm (proj₁ y) (proj₁ x)) zyx))
-- 矛盾矩阵
insW-swap0 x y | gt3 _ _ gxy | gt3 _ _ gyx =
  ⊥-elim (<-irrefl refl (<-trans gyx gxy))
insW-swap0 x y | gt3 _ _ gxy | eq3 _ _ eyx =
  ⊥-elim (contra-< (sym eyx) gxy)
insW-swap0 x y | lt3 _ _ lxy | lt3 _ _ lyx =
  ⊥-elim (<-irrefl refl (<-trans lxy lyx))
insW-swap0 x y | lt3 _ _ lxy | eq3 _ _ eyx =
  ⊥-elim (contra-< eyx lxy)
insW-swap0 x y | eq3 _ _ exy | gt3 _ _ gyx =
  ⊥-elim (contra-< (sym exy) gyx)
insW-swap0 x y | eq3 _ _ exy | lt3 _ _ lyx =
  ⊥-elim (contra-< exy lyx)

-- ────────────────────────────────────────────────────────────────────
-- ③ tie 核对（对抗验证）
-- ────────────────────────────────────────────────────────────────────

check-tie : norm ((+ 1 , + 2) ∷ (+ 1 , + 3) ∷ [])
          ≡ norm ((+ 1 , + 3) ∷ (+ 1 , + 2) ∷ [])
check-tie = refl

check-cancel : norm ((+ 2 , + 5) ∷ (- (+ 2) , + 5) ∷ []) ≡ []
check-cancel = refl

check-orphan-zero : norm ((+ 0 , + 7) ∷ []) ≡ (+ 0 , + 7) ∷ []
check-orphan-zero = refl

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 孤零反例：norm-unique 无条件版为假（statement_wrong 定谳，原签名留档）
--   数学面：合并归零丢弃 vs 孤零保留——同一多重集的两插入序给出不同 norm。
--   排除条件恰为 NoZero（无零系数项输入）或 dropZ 规范化（零项视同缺席）。
-- ────────────────────────────────────────────────────────────────────

xs-ex ys-ex : Laurent
xs-ex = (+ 1 , + 0) ∷ (+ 0 , + 0) ∷ (- (+ 1) , + 0) ∷ []
ys-ex = (+ 0 , + 0) ∷ (+ 1 , + 0) ∷ (- (+ 1) , + 0) ∷ []

xs-ex-↭-ys-ex : xs-ex ↭ ys-ex
xs-ex-↭-ys-ex = swap (+ 1 , + 0) (+ 0 , + 0) ↭-refl

norm-xs-ex : norm xs-ex ≡ []
norm-xs-ex = refl

norm-ys-ex : norm ys-ex ≡ (+ 0 , + 0) ∷ []
norm-ys-ex = refl

-- 反证件：无条件版为假（构造性——两序 norm 计算值不同）
norm-unique-false : ¬ (∀ xs ys → xs ↭ ys → norm xs ≡ norm ys)
norm-unique-false f = absurd
  (trans (sym norm-xs-ex) (trans (f xs-ex ys-ex xs-ex-↭-ys-ex) norm-ys-ex))
  where
  absurd : [] ≡ (+ 0 , + 0) ∷ [] → ⊥
  absurd ()

-- ────────────────────────────────────────────────────────────────────
-- ⑥ Stage 3 批1：dropZ 规范化件（B 主线的地基）
--   数学面：零系数项视同缺席 ⇒ 孤零叶退化，norm∘dropZ 置换不变。
--   形状纪律（with-swamp 终解）：dropZ 经显式判定参数 aux（零 with），
--   引理对 aux t ts d 形立式（d 实例化对齐）。
-- ────────────────────────────────────────────────────────────────────

-- 零自由谓词（表中无零系数项）
ZeroFree : Laurent → Set
ZeroFree [] = ⊤
ZeroFree (t ∷ ts) = (proj₁ t ≢ + 0) × ZeroFree ts

mutual
  dropZ : Laurent → Laurent
  dropZ [] = []
  dropZ (t ∷ ts) = dropZ-aux t ts (proj₁ t ≟ + 0)

  -- 显式判定参数的过滤步（普通子句，无 with——实例化可转换）
  dropZ-aux : ∀ (t : LaurentTerm) ts → Dec (proj₁ t ≡ + 0) → Laurent
  dropZ-aux t ts (yes _) = dropZ ts
  dropZ-aux t ts (no  _) = t ∷ dropZ ts

-- 两桥（对 aux 的判定参数直接匹配——零 with，实例化对齐）
dropZ-yes : ∀ t ts (d : Dec (proj₁ t ≡ + 0)) → proj₁ t ≡ + 0 → dropZ-aux t ts d ≡ dropZ ts
dropZ-yes t ts (yes _) e = refl
dropZ-yes t ts (no  n) e = ⊥-elim (n e)

dropZ-no : ∀ t ts (d : Dec (proj₁ t ≡ + 0)) → proj₁ t ≢ + 0 → dropZ-aux t ts d ≡ t ∷ dropZ ts
dropZ-no t ts (yes e) n = ⊥-elim (n e)
dropZ-no t ts (no  _) n = refl

-- 过滤保置换（对 ↭ 归纳；端=分支实参、中=中性检验子、引理种随证明实参）
dropZ-resp-↭ : ∀ xs ys → xs ↭ ys → dropZ xs ↭ dropZ ys
dropZ-resp-↭ ._ ._ ↭-refl = ↭-refl
dropZ-resp-↭ ._ ._ (prep {xs} {ys} x p) with proj₁ x ≟ + 0
... | yes zx = dropZ-resp-↭ xs ys p
... | no  nx = subst₂ _↭_ (sym (dropZ-no x xs (no nx) nx)) (sym (dropZ-no x ys (no nx) nx))
                          (prep x (dropZ-resp-↭ xs ys p))
dropZ-resp-↭ ._ ._ (swap {xs} {ys} x y p) with proj₁ x ≟ + 0 | proj₁ y ≟ + 0
... | yes zx | yes zy =
  subst₂ _↭_
    (sym (trans (dropZ-yes x (y ∷ xs) (yes zx) zx) (dropZ-yes y xs (proj₁ y ≟ + 0) zy)))
    (sym (trans (dropZ-yes y (x ∷ ys) (yes zy) zy) (dropZ-yes x ys (proj₁ x ≟ + 0) zx)))
    (dropZ-resp-↭ xs ys p)
... | yes zx | no  ny =
  subst₂ _↭_
    (sym (trans (dropZ-yes x (y ∷ xs) (yes zx) zx) (dropZ-no y xs (proj₁ y ≟ + 0) ny)))
    (sym (trans (dropZ-no y (x ∷ ys) (no ny) ny) (cong (y ∷_) (dropZ-yes x ys (proj₁ x ≟ + 0) zx))))
    (prep y (dropZ-resp-↭ xs ys p))
... | no  nx | yes zy =
  subst₂ _↭_
    (sym (trans (dropZ-no x (y ∷ xs) (no nx) nx) (cong (x ∷_) (dropZ-yes y xs (proj₁ y ≟ + 0) zy))))
    (sym (trans (dropZ-yes y (x ∷ ys) (yes zy) zy) (dropZ-no x ys (proj₁ x ≟ + 0) nx)))
    (prep x (dropZ-resp-↭ xs ys p))
... | no  nx | no  ny =
  subst₂ _↭_
    (sym (trans (dropZ-no x (y ∷ xs) (no nx) nx) (cong (x ∷_) (dropZ-no y xs (proj₁ y ≟ + 0) ny))))
    (sym (trans (dropZ-no y (x ∷ ys) (no ny) ny) (cong (y ∷_) (dropZ-no x ys (proj₁ x ≟ + 0) nx))))
    (swap x y (dropZ-resp-↭ xs ys p))
dropZ-resp-↭ ._ ._ (↭-t {xs} {ys} {zs} p q) = ↭-t (dropZ-resp-↭ xs ys p) (dropZ-resp-↭ ys zs q)

-- dropZ 输出零自由
dropZ-free : ∀ ts → ZeroFree (dropZ ts)
dropZ-free [] = tt
dropZ-free (t ∷ ts) = dropZ-free-aux t ts (proj₁ t ≟ + 0)
  where
  dropZ-free-aux : ∀ t ts (d : Dec (proj₁ t ≡ + 0)) → ZeroFree (dropZ-aux t ts d)
  dropZ-free-aux t ts (yes _) = dropZ-free ts
  dropZ-free-aux t ts (no  n) = (n , dropZ-free ts)

-- 单点插入零自由保持（insertCᵌ 三分支；eq3 垫底防嵌套 with 吞子句）
insW-free : ∀ t ts (c : Canon ts) → proj₁ t ≢ + 0 → ZeroFree ts → ZeroFree (insW t ts c)
insW-free t [] canon-nil n tt = (n , tt)
insW-free t (x ∷ []) (canon-one .x) n (nx , tt) with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ _ = (n , (nx , tt))
... | lt3 _ _ _ = (nx , (n , tt))
insW-free t (x ∷ []) (canon-one .x) n (nx , tt) | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
... | yes z = tt
... | no  nz = (nz , tt)
insW-free t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s) n (nx , z) with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ _ = (n , (nx , z))
... | lt3 _ _ l = subst ZeroFree
     (sym (lt3-cons-shape t x x₂ xs p l s (insertCᵌ t (x₂ ∷ xs) s)))
     (nx , insW-free t (x₂ ∷ xs) s n z)
insW-free t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s) n (nx , z) | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
... | yes z0 = z
... | no  nz = (nz , z)

-- norm 镜像零自由面
normC-free : ∀ ts → ZeroFree ts → ZeroFree (norm ts)
normC-free [] z = tt
normC-free (t ∷ ts) (nt , z) = insW-free t (norm ts) (proj₂ (normC ts)) nt (normC-free ts z)

-- normD = B 主线核心形（norm ∘ dropZ）
normD : Laurent → Laurent
normD ts = norm (dropZ ts)

normD-free : ∀ ts → ZeroFree (normD ts)
normD-free ts = normC-free (dropZ ts) (dropZ-free ts)

-- Stage 2 反例在 B 面退化复核（验证点②）：dropZ 后孤零消失 ⇒ 两序 normD 相等
check-dropZ-ex : normD xs-ex ≡ normD ys-ex
check-dropZ-ex = refl

check-dropZ-orphan : normD ((+ 0 , + 7) ∷ []) ≡ []
check-dropZ-orphan = refl


-- ────────────────────────────────────────────────────────────────────
-- ⑦ 批2：形状桥（链接层）→ 矩阵（零 with）→ 双收口
-- 形状纪律：矩阵/收口 aux 显式判定参数范式（零 with）；
--   形状桥 = 链接层（insertCᵌ 内部 with 于 cmp3 调用，非 aux 形）——
--   同源 scrutinee 单级 case split，非目标分支全为证据矛盾消解（无嵌套无沼泽）。
-- ────────────────────────────────────────────────────────────────────

-- nil 形（definitional）
insW0 : ∀ (t : LaurentTerm) → insW t [] canon-nil ≡ t ∷ []
insW0 t = refl

-- one 形三桥（同源 cmp3；非目标分支 contra 消解）
insW1-gt : ∀ (t x : LaurentTerm) (g : proj₂ x < proj₂ t) →
  insW t (x ∷ []) (canon-one x) ≡ t ∷ x ∷ []
insW1-gt t x g with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ _ = refl
... | eq3 _ _ e = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (<-irrefl refl (<-trans l g))

insW1-lt : ∀ (t x : LaurentTerm) (l : proj₂ t < proj₂ x) →
  insW t (x ∷ []) (canon-one x) ≡ x ∷ t ∷ []
insW1-lt t x l with cmp3 (proj₂ t) (proj₂ x)
... | lt3 _ _ _ = refl
... | eq3 _ _ e = ⊥-elim (contra-< (sym e) l)
... | gt3 _ _ g = ⊥-elim (<-irrefl refl (<-trans l g))

-- eq 形的合并体（aux 显式判定参数）
eq1-body : ∀ (t x : LaurentTerm) → Dec ((proj₁ t + proj₁ x) ≡ + 0) → Laurent
eq1-body t x (yes _) = []
eq1-body t x (no  _) = (proj₁ t + proj₁ x , proj₂ t) ∷ []

eq1-yes : ∀ (t x : LaurentTerm) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) →
  proj₁ t + proj₁ x ≡ + 0 → eq1-body t x d ≡ []
eq1-yes t x (yes _) z = refl
eq1-yes t x (no  n) z = ⊥-elim (n z)

eq1-no : ∀ (t x : LaurentTerm) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) →
  proj₁ t + proj₁ x ≢ + 0 → eq1-body t x d ≡ (proj₁ t + proj₁ x , proj₂ t) ∷ []
eq1-no t x (yes z) n = ⊥-elim (n z)
eq1-no t x (no  _) n = refl

insW1-eq : ∀ (t x : LaurentTerm) (e : proj₂ t ≡ proj₂ x) →
  insW t (x ∷ []) (canon-one x) ≡ eq1-body t x ((proj₁ t + proj₁ x) ≟ + 0)
insW1-eq (ct , et) (cx , ex) e with cmp3 et ex
... | gt3 _ _ g = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (contra-< (sym e) l)
... | eq3 _ _ _ with (ct + cx) ≟ + 0
...   | yes _ = refl
...   | no  _ = refl

-- cons 形三桥（同源 cmp3 + lt3-cons-shape 复用）
insW-cons-gt : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) (p : proj₂ x₂ < proj₂ x) (s : Canon (x₂ ∷ xs)) (g : proj₂ x < proj₂ t) →
  insW t (x ∷ x₂ ∷ xs) (canon-cons x x₂ xs p s) ≡ t ∷ x ∷ x₂ ∷ xs
insW-cons-gt t x x₂ xs p s g with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ _ = refl
... | eq3 _ _ e = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (<-irrefl refl (<-trans l g))

insW-cons-lt : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) (p : proj₂ x₂ < proj₂ x) (s : Canon (x₂ ∷ xs)) (l : proj₂ t < proj₂ x) →
  insW t (x ∷ x₂ ∷ xs) (canon-cons x x₂ xs p s) ≡ x ∷ insW t (x₂ ∷ xs) s
insW-cons-lt t x x₂ xs p s l with cmp3 (proj₂ t) (proj₂ x)
... | lt3 _ _ l' = lt3-cons-shape t x x₂ xs p l' s (insertCᵌ t (x₂ ∷ xs) s)
... | eq3 _ _ e = ⊥-elim (contra-< (sym e) l)
... | gt3 _ _ g = ⊥-elim (<-irrefl refl (<-trans l g))

eqc-body : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) → Dec ((proj₁ t + proj₁ x) ≡ + 0) → Laurent
eqc-body t x x₂ xs (yes _) = x₂ ∷ xs
eqc-body t x x₂ xs (no  _) = (proj₁ t + proj₁ x , proj₂ t) ∷ x₂ ∷ xs

eqc-yes : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) →
  proj₁ t + proj₁ x ≡ + 0 → eqc-body t x x₂ xs d ≡ x₂ ∷ xs
eqc-yes t x x₂ xs (yes _) z = refl
eqc-yes t x x₂ xs (no  n) z = ⊥-elim (n z)

eqc-no : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) →
  proj₁ t + proj₁ x ≢ + 0 → eqc-body t x x₂ xs d ≡ (proj₁ t + proj₁ x , proj₂ t) ∷ x₂ ∷ xs
eqc-no t x x₂ xs (yes z) n = ⊥-elim (n z)
eqc-no t x x₂ xs (no  _) n = refl

insW-cons-eq : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) (p : proj₂ x₂ < proj₂ x) (s : Canon (x₂ ∷ xs)) (e : proj₂ t ≡ proj₂ x) →
  insW t (x ∷ x₂ ∷ xs) (canon-cons x x₂ xs p s) ≡ eqc-body t x x₂ xs ((proj₁ t + proj₁ x) ≟ + 0)
insW-cons-eq (ct , et) (cx , ex) x₂ xs p s e with cmp3 et ex
... | gt3 _ _ g = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (contra-< (sym e) l)
... | eq3 _ _ _ with (ct + cx) ≟ + 0
...   | yes _ = refl
...   | no  _ = refl


-- ── 批2 ②a：矩阵代数助件（零 with）────────────────────────────────

-- 合并系数交换（双合并叶核心）
ms-swap : ∀ (a b c : ℤ) → (a + b) + c ≡ (b + a) + c
ms-swap a b c = cong (_+ c) (+-comm a b)

-- 合并消去：y + z = 0 ⇒ y + (x + z) = x
merge-cancel : ∀ (x y z : ℤ) → y + z ≡ + 0 → y + (x + z) ≡ x
merge-cancel x y z p =
  trans (sym (+-assoc y x z))
  (trans (cong (_+ z) (+-comm y x))
  (trans (+-assoc x y z)
  (trans (cong (λ w → x + w) p) (+-identityʳ x))))

-- 等式搬运 <
lt-resp-≡ : ∀ {a b c : ℤ} → a ≡ b → b < c → a < c
lt-resp-≡ refl q = q

lt-resp-≡' : ∀ {a b c : ℤ} → a ≡ b → c < a → c < b
lt-resp-≡' refl q = q

-- eqc-body 交换（双合并体同形；e : 指数相等）
eqc-body-swap : ∀ (t x : LaurentTerm) x₂ xs
  (d1 : Dec ((proj₁ t + proj₁ x) ≡ + 0)) (d2 : Dec ((proj₁ x + proj₁ t) ≡ + 0)) →
  proj₂ t ≡ proj₂ x → eqc-body t x x₂ xs d1 ≡ eqc-body x t x₂ xs d2
eqc-body-swap t x x₂ xs (yes z1) (yes z2) e = refl
eqc-body-swap t x x₂ xs (yes z1) (no  n2) e = ⊥-elim (n2 (subst (λ c → c ≡ + 0) (+-comm (proj₁ t) (proj₁ x)) z1))
eqc-body-swap t x x₂ xs (no  n1) (yes z2) e = ⊥-elim (n1 (subst (λ c → c ≡ + 0) (+-comm (proj₁ x) (proj₁ t)) z2))
eqc-body-swap t x x₂ xs (no  n1) (no  n2) e = cong₂ (λ s q → (s , q) ∷ x₂ ∷ xs) (+-comm (proj₁ t) (proj₁ x)) e

-- eq1-body 交换（one 表双合并体）
eq1-body-swap : ∀ (t x : LaurentTerm)
  (d1 : Dec ((proj₁ t + proj₁ x) ≡ + 0)) (d2 : Dec ((proj₁ x + proj₁ t) ≡ + 0)) →
  proj₂ t ≡ proj₂ x → eq1-body t x d1 ≡ eq1-body x t d2
eq1-body-swap t x (yes z1) (yes z2) e = refl
eq1-body-swap t x (yes z1) (no  n2) e = ⊥-elim (n2 (subst (λ c → c ≡ + 0) (+-comm (proj₁ t) (proj₁ x)) z1))
eq1-body-swap t x (no  n1) (yes z2) e = ⊥-elim (n1 (subst (λ c → c ≡ + 0) (+-comm (proj₁ x) (proj₁ t)) z2))
eq1-body-swap t x (no  n1) (no  n2) e = cong₂ (λ s q → (s , q) ∷ []) (+-comm (proj₁ t) (proj₁ x)) e

-- 单合并与孤零互斥（zero-free 面的消去叶）
eq1-drop-l : ∀ (t x : LaurentTerm) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) →
  proj₁ t + proj₁ x ≡ + 0 → eq1-body t x d ≡ []
eq1-drop-l = eq1-yes

-- ── 批2 ②b：前插×前插核（d3 驱动，零 with）────────────────────────

-- 两侧都前插 z（x>z ∧ y>z）时由 d3 = cmp3 (proj₂ x)(proj₂ y) 定序
ff-core : ∀ (x y z : LaurentTerm) (g_xz : proj₂ z < proj₂ x) (g_yz : proj₂ z < proj₂ y)
  (d3 : Cmp3 (proj₂ x) (proj₂ y)) →
  insW x (y ∷ z ∷ []) (canon-cons y z [] g_yz (canon-one z))
  ≡ insW y (x ∷ z ∷ []) (canon-cons x z [] g_xz (canon-one z))
ff-core x y z g_xz g_yz (gt3 _ _ gxy) =
  trans (insW-cons-gt x y z [] g_yz (canon-one z) gxy)
  (trans (sym (cong (λ w → x ∷ w) (insW1-gt y z g_yz)))
        (sym (insW-cons-lt y x z [] g_xz (canon-one z) gxy)))
ff-core x y z g_xz g_yz (lt3 _ _ lxy) =
  trans (insW-cons-lt x y z [] g_yz (canon-one z) lxy)
  (trans (cong (λ w → y ∷ w) (insW1-gt x z g_xz))
        (sym (insW-cons-gt y x z [] g_xz (canon-one z) lxy)))
ff-core x y z g_xz g_yz (eq3 _ _ exy) =
  trans (insW-cons-eq x y z [] g_yz (canon-one z) exy)
  (trans (eqc-body-swap x y z [] ((proj₁ x + proj₁ y) ≟ + 0) ((proj₁ y + proj₁ x) ≟ + 0) exy)
        (sym (insW-cons-eq y x z [] g_xz (canon-one z) (sym exy))))


-- ── 批2 ②c：one-表矩阵（9 格 + eq 子格 aux）──────────────────────

-- eq1-body 的 Canon（aux 范式：Dec 参数普通子句）
eq1-canon : ∀ (t x : LaurentTerm) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) → Canon (eq1-body t x d)
eq1-canon t x (yes _) = canon-nil
eq1-canon t x (no  _) = canon-one _

-- 等零和的唯一性（cell-ee 叶用）
zero-sum-unique : ∀ (a b c : ℤ) → a + c ≡ + 0 → b + c ≡ + 0 → a ≡ b
zero-sum-unique a b c p q = trans (to-neg a p) (sym (to-neg b q))
  where
  to-neg : ∀ x → x + c ≡ + 0 → x ≡ - c
  to-neg x r =
    trans (sym (+-identityʳ x))
    (trans (cong (λ w → x + w) (sym (+-inverseʳ c)))
    (trans (sym (+-assoc x c (- c)))
    (trans (cong (λ w → w + (- c)) r) (+-identityˡ (- c)))))

-- 三和不零（cell-ee 的 no-drop 叶用）
sum3-no-zero : ∀ (cx cy cz : ℤ) → cx + cz ≡ + 0 → cy ≢ + 0 → cx + (cy + cz) ≢ + 0
sum3-no-zero cx cy cz p ny s =
  ny (trans (sym (+-identityʳ cy)) (trans (cong (λ w → cy + w) (sym p)) (trans (sym (+-assoc cy cx cz)) (trans (cong (_+ cz) (+-comm cy cx)) (trans (+-assoc cx cy cz) s)))))

-- (gt,eq) 格：dyz 驱动（aux 范式）
cell-ge : ∀ (x y z : LaurentTerm) (gxz : proj₂ z < proj₂ x) (eyz : proj₂ y ≡ proj₂ z)
  (dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)) (c : Canon (eq1-body y z dyz)) →
  insW x (eq1-body y z dyz) c ≡ x ∷ eq1-body y z dyz
cell-ge x y z gxz eyz (yes zyz) canon-nil = insW0 x
cell-ge x y z gxz eyz (no  nyz) (canon-one _) = insW1-gt x (proj₁ y + proj₁ z , proj₂ y) (lt-resp-≡ eyz gxz)

-- 尾接（后插结果形）
snoc : Laurent → LaurentTerm → Laurent
snoc w x = w ++ (x ∷ [])

-- (lt,eq) 格
cell-le : ∀ (x y z : LaurentTerm) (lxz : proj₂ x < proj₂ z) (eyz : proj₂ y ≡ proj₂ z)
  (dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)) (c : Canon (eq1-body y z dyz)) →
  insW x (eq1-body y z dyz) c ≡ snoc (eq1-body y z dyz) x
cell-le x y z lxz eyz (yes zyz) canon-nil = insW0 x
cell-le x y z lxz eyz (no  nyz) (canon-one _) =
  insW1-lt x (proj₁ y + proj₁ z , proj₂ y) (lt-resp-≡' (sym eyz) lxz)

-- (eq,gt) 格
cell-eg : ∀ (x y z : LaurentTerm) (exz : proj₂ x ≡ proj₂ z) (gyz : proj₂ z < proj₂ y)
  (dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)) (c : Canon (eq1-body x z dxz)) →
  insW y (eq1-body x z dxz) c ≡ y ∷ eq1-body x z dxz
cell-eg x y z exz gyz (yes zxz) canon-nil = insW0 y
cell-eg x y z exz gyz (no  nxz) (canon-one _) = insW1-gt y (proj₁ x + proj₁ z , proj₂ x) (lt-resp-≡ exz gyz)

-- (eq,lt) 格
cell-el : ∀ (x y z : LaurentTerm) (exz : proj₂ x ≡ proj₂ z) (lyz : proj₂ y < proj₂ z)
  (dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)) (c : Canon (eq1-body x z dxz)) →
  insW y (eq1-body x z dxz) c ≡ snoc (eq1-body x z dxz) y
cell-el x y z exz lyz (yes zxz) canon-nil = insW0 y
cell-el x y z exz lyz (no  nxz) (canon-one _) = insW1-lt y (proj₁ x + proj₁ z , proj₂ x) (lt-resp-≡' (sym exz) lyz)


-- eqc-body 与 snoc 的同形桥
eqc-snoc : ∀ (t x x₂ : LaurentTerm) (d : Dec ((proj₁ t + proj₁ x) ≡ + 0)) →
  eqc-body t x x₂ [] d ≡ snoc (eq1-body t x d) x₂
eqc-snoc t x x₂ (yes _) = refl
eqc-snoc t x x₂ (no  _) = refl

-- 三和重组（ee 格算术）
sum3-eq : ∀ (cx cy cz : ℤ) → cx + (cy + cz) ≡ cy + (cx + cz)
sum3-eq cx cy cz =
  trans (sym (+-assoc cx cy cz))
  (trans (cong (λ w → w + cz) (+-comm cx cy)) (+-assoc cy cx cz))

-- ee-core：双合并体交换（m1/m2 驱动，零 with）
ee-core : ∀ (cx cy cz ex ey : ℤ) (exy : ex ≡ ey)
  (m1 : Dec ((cx + (cy + cz)) ≡ + 0)) (m2 : Dec ((cy + (cx + cz)) ≡ + 0)) →
  eq1-body (cx , ex) (cy + cz , ey) m1 ≡ eq1-body (cy , ey) (cx + cz , ex) m2
ee-core cx cy cz ex ey exy (yes s1) (yes s2) = refl
ee-core cx cy cz ex ey exy (yes s1) (no  n2) = ⊥-elim (n2 (subst (λ w → w ≡ + 0) (sum3-eq cx cy cz) s1))
ee-core cx cy cz ex ey exy (no  n1) (yes s2) = ⊥-elim (n1 (subst (λ w → w ≡ + 0) (sym (sum3-eq cx cy cz)) s2))
ee-core cx cy cz ex ey exy (no  n1) (no  n2) = cong₂ (λ s e → (s , e) ∷ []) (sum3-eq cx cy cz) exy


-- (eq,eq) 格四≟叶（dyz/dxz 驱动；ee-core 收双合并；nx/ny = 非零前提）
cell-ee : ∀ (x y z : LaurentTerm) (nx : proj₁ x ≢ + 0) (ny : proj₁ y ≢ + 0)
  (exz : proj₂ x ≡ proj₂ z) (eyz : proj₂ y ≡ proj₂ z)
  (dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)) (dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0))
  (c : Canon (eq1-body y z dyz)) (c' : Canon (eq1-body x z dxz)) →
  insW x (eq1-body y z dyz) c ≡ insW y (eq1-body x z dxz) c'
cell-ee (cx , ex) (cy , ey) (cz , ez) nx ny exz eyz (yes zyz) (yes zxz) canon-nil canon-nil =
  trans (insW0 (cx , ex)) (trans (cong (λ w → w ∷ []) x≡y) (sym (insW0 (cy , ey))))
  where
  x≡y : (cx , ex) ≡ (cy , ey)
  x≡y = cong₂ _,_ (sym (zero-sum-unique cy cx cz zyz zxz)) (trans exz (sym eyz))
cell-ee (cx , ex) (cy , ey) (cz , ez) nx ny exz eyz (yes zyz) (no  nxz) canon-nil (canon-one _) =
  trans (insW0 (cx , ex)) (trans (cong (λ w → w ∷ []) x≡rhs) (sym rhs-eq))
  where
  exy : ey ≡ ex
  exy = trans eyz (sym exz)
  total≡cx : cy + (cx + cz) ≡ cx
  total≡cx = trans (sym (sum3-eq cx cy cz)) (trans (cong (λ w → cx + w) zyz) (+-identityʳ cx))
  nz : (cy + (cx + cz)) ≢ + 0
  nz s = nx (trans (sym total≡cx) s)
  x≡rhs : (cx , ex) ≡ (cy + (cx + cz) , ey)
  x≡rhs = cong₂ _,_ (sym total≡cx) (sym exy)
  rhs-eq : insW (cy , ey) ((cx + cz , ex) ∷ []) (canon-one (cx + cz , ex)) ≡ ((cy + (cx + cz) , ey) ∷ [])
  rhs-eq = trans (insW1-eq (cy , ey) (cx + cz , ex) exy)
                 (eq1-no (cy , ey) (cx + cz , ex) ((cy + (cx + cz)) ≟ + 0) nz)
cell-ee (cx , ex) (cy , ey) (cz , ez) nx ny exz eyz (no  nyz) (yes zxz) (canon-one _) canon-nil =
  trans (lhs-eq) (trans (cong (λ w → w ∷ []) (cong₂ _,_ total≡cy (trans exz (sym eyz)))) (sym (insW0 (cy , ey))))
  where
  total≡cy : cx + (cy + cz) ≡ cy
  total≡cy = trans (sum3-eq cx cy cz) (trans (cong (λ w → cy + w) zxz) (+-identityʳ cy))
  nz : (cx + (cy + cz)) ≢ + 0
  nz s = ny (trans (sym total≡cy) s)
  lhs-eq : insW (cx , ex) ((cy + cz , ey) ∷ []) (canon-one (cy + cz , ey)) ≡ ((cx + (cy + cz) , ex) ∷ [])
  lhs-eq = trans (insW1-eq (cx , ex) (cy + cz , ey) (trans exz (sym eyz)))
                 (eq1-no (cx , ex) (cy + cz , ey) ((cx + (cy + cz)) ≟ + 0) nz)
cell-ee (cx , ex) (cy , ey) (cz , ez) nx ny exz eyz (no  nyz) (no  nxz) (canon-one _) (canon-one _) =
  trans (insW1-eq (cx , ex) (cy + cz , ey) (trans exz (sym eyz)))
  (trans (ee-core cx cy cz ex ey (trans exz (sym eyz)) ((cx + (cy + cz)) ≟ + 0) ((cy + (cx + cz)) ≟ + 0))
        (sym (insW1-eq (cy , ey) (cx + cz , ex) (trans eyz (sym exz)))))


-- one-表矩阵九格总装（d1 × d2 驱动，零 with）
insW2-swap-one : ∀ (x y z : LaurentTerm) (nx : proj₁ x ≢ + 0) (ny : proj₁ y ≢ + 0) (nz : proj₁ z ≢ + 0)
  (d1 : Cmp3 (proj₂ x) (proj₂ z)) (d2 : Cmp3 (proj₂ y) (proj₂ z)) →
  insW x (insW y (z ∷ []) (canon-one z)) (insC y (z ∷ []) (canon-one z))
  ≡ insW y (insW x (z ∷ []) (canon-one z)) (insC x (z ∷ []) (canon-one z))
insW2-swap-one x y z nx ny nz (gt3 _ _ gxz) (gt3 _ _ gyz) =
  trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (canon-cons y z [] gyz (canon-one z)) (insW1-gt y z gyz))
  (trans (ff-core x y z gxz gyz (cmp3 (proj₂ x) (proj₂ y)))
        (sym (insW-mono y (insC x (z ∷ []) (canon-one z)) (canon-cons x z [] gxz (canon-one z)) (insW1-gt x z gxz))))
insW2-swap-one x y z nx ny nz (gt3 _ _ gxz) (lt3 _ _ lyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (canon-cons z y [] lyz (canon-one y)) (insW1-lt y z lyz))
               (insW-cons-gt x z y [] lyz (canon-one y) gxz))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (canon-cons x z [] gxz (canon-one z)) (insW1-gt x z gxz))
        (trans (insW-cons-lt y x z [] gxz (canon-one z) (<-trans lyz gxz))
               (cong (λ w → x ∷ w) (insW1-lt y z lyz)))))
insW2-swap-one x y z nx ny nz (gt3 _ _ gxz) (eq3 _ _ eyz) =
  trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (eq1-canon y z ((proj₁ y + proj₁ z) ≟ + 0)) (insW1-eq y z eyz))
  (trans (cell-ge x y z gxz eyz ((proj₁ y + proj₁ z) ≟ + 0) (eq1-canon y z ((proj₁ y + proj₁ z) ≟ + 0)))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (canon-cons x z [] gxz (canon-one z)) (insW1-gt x z gxz))
        (trans (insW-cons-lt y x z [] gxz (canon-one z) (lt-resp-≡ eyz gxz))
               (cong (λ w → x ∷ w) (insW1-eq y z eyz))))))
insW2-swap-one x y z nx ny nz (lt3 _ _ lxz) (gt3 _ _ gyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (canon-cons y z [] gyz (canon-one z)) (insW1-gt y z gyz))
               (trans (insW-cons-lt x y z [] gyz (canon-one z) (<-trans lxz gyz)) (cong (λ w → y ∷ w) (insW1-lt x z lxz))))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (canon-cons z x [] lxz (canon-one x)) (insW1-lt x z lxz))
               (insW-cons-gt y z x [] lxz (canon-one x) gyz)))
insW2-swap-one x y z nx ny nz (lt3 _ _ lxz) (lt3 _ _ lyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (canon-cons z y [] lyz (canon-one y)) (insW1-lt y z lyz))
               (trans (insW-cons-lt x z y [] lyz (canon-one y) lxz) (cong (λ w → z ∷ w) (insW-swap0 x y))))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (canon-cons z x [] lxz (canon-one x)) (insW1-lt x z lxz))
               (insW-cons-lt y z x [] lxz (canon-one x) lyz)))
insW2-swap-one x y z nx ny nz (lt3 _ _ lxz) (eq3 _ _ eyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (eq1-canon y z ((proj₁ y + proj₁ z) ≟ + 0)) (insW1-eq y z eyz))
               (cell-le x y z lxz eyz ((proj₁ y + proj₁ z) ≟ + 0) (eq1-canon y z ((proj₁ y + proj₁ z) ≟ + 0))))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (canon-cons z x [] lxz (canon-one x)) (insW1-lt x z lxz))
        (trans (insW-cons-eq y z x [] lxz (canon-one x) eyz) (eqc-snoc y z x ((proj₁ y + proj₁ z) ≟ + 0)))))
insW2-swap-one x y z nx ny nz (eq3 _ _ exz) (gt3 _ _ gyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (canon-cons y z [] gyz (canon-one z)) (insW1-gt y z gyz))
               (trans (insW-cons-lt x y z [] gyz (canon-one z) (lt-resp-≡ exz gyz)) (cong (λ w → y ∷ w) (insW1-eq x z exz))))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (eq1-canon x z ((proj₁ x + proj₁ z) ≟ + 0)) (insW1-eq x z exz))
               (cell-eg x y z exz gyz ((proj₁ x + proj₁ z) ≟ + 0) (eq1-canon x z ((proj₁ x + proj₁ z) ≟ + 0)))))
insW2-swap-one x y z nx ny nz (eq3 _ _ exz) (lt3 _ _ lyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (canon-cons z y [] lyz (canon-one y)) (insW1-lt y z lyz))
               (trans (insW-cons-eq x z y [] lyz (canon-one y) exz) (eqc-snoc x z y ((proj₁ x + proj₁ z) ≟ + 0))))
  (sym (trans (insW-mono y (insC x (z ∷ []) (canon-one z)) (eq1-canon x z ((proj₁ x + proj₁ z) ≟ + 0)) (insW1-eq x z exz))
               (cell-el x y z exz lyz ((proj₁ x + proj₁ z) ≟ + 0) (eq1-canon x z ((proj₁ x + proj₁ z) ≟ + 0)))))
insW2-swap-one x y z nx ny nz (eq3 _ _ exz) (eq3 _ _ eyz) =
  trans (trans (insW-mono x (insC y (z ∷ []) (canon-one z)) (eq1-canon y z ((proj₁ y + proj₁ z) ≟ + 0)) (insW1-eq y z eyz))
               (cell-ee x y z nx ny exz eyz ((proj₁ y + proj₁ z) ≟ + 0) ((proj₁ x + proj₁ z) ≟ + 0)
                        (eq1-canon y z ((proj₁ y + proj₁ z) ≟ + 0)) (eq1-canon x z ((proj₁ x + proj₁ z) ≟ + 0))))
  (sym (insW-mono y (insC x (z ∷ []) (canon-one z)) (eq1-canon x z ((proj₁ x + proj₁ z) ≟ + 0)) (insW1-eq x z exz)))


-- ── 批2 ②d：头通用桥（任意尾 w——消形状分岔）─────────────────────
hwc-body : ∀ (t h : LaurentTerm) (w : Laurent) → Dec ((proj₁ t + proj₁ h) ≡ + 0) → Laurent
hwc-body t h w (yes _) = w
hwc-body t h w (no  _) = (proj₁ t + proj₁ h , proj₂ t) ∷ w

hwc-yes : ∀ (t h : LaurentTerm) w (d : Dec ((proj₁ t + proj₁ h) ≡ + 0)) →
  proj₁ t + proj₁ h ≡ + 0 → hwc-body t h w d ≡ w
hwc-yes t h w (yes _) z = refl
hwc-yes t h w (no  n) z = ⊥-elim (n z)

hwc-no : ∀ (t h : LaurentTerm) w (d : Dec ((proj₁ t + proj₁ h) ≡ + 0)) →
  proj₁ t + proj₁ h ≢ + 0 → hwc-body t h w d ≡ (proj₁ t + proj₁ h , proj₂ t) ∷ w
hwc-no t h w (yes z) n = ⊥-elim (n z)
hwc-no t h w (no  _) n = refl

hw-eq : ∀ (t h : LaurentTerm) w (c : Canon (h ∷ w)) (e : proj₂ t ≡ proj₂ h) →
  insW t (h ∷ w) c ≡ hwc-body t h w ((proj₁ t + proj₁ h) ≟ + 0)
hw-eq t h [] (canon-one .h) e with cmp3 (proj₂ t) (proj₂ h)
... | gt3 _ _ g = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (contra-< (sym e) l)
... | eq3 _ _ _ with (proj₁ t + proj₁ h) ≟ + 0
...   | yes _ = refl
...   | no  _ = refl
hw-eq t h (w₁ ∷ ws) (canon-cons .h w₁ ws p s) e with cmp3 (proj₂ t) (proj₂ h)
... | gt3 _ _ g = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (contra-< (sym e) l)
... | eq3 _ _ _ with (proj₁ t + proj₁ h) ≟ + 0
...   | yes _ = refl
...   | no  _ = refl


-- 尾 Canon 抽取（hw-lt 用）
tc : ∀ (h : LaurentTerm) w → Canon (h ∷ w) → Canon w
tc h [] (canon-one .h) = canon-nil
tc h (w₁ ∷ ws) (canon-cons .h w₁ ws p s) = s

-- 头通用 gt/lt 桥（任意尾）
hw-gt : ∀ (t h : LaurentTerm) w (c : Canon (h ∷ w)) (g : proj₂ h < proj₂ t) →
  insW t (h ∷ w) c ≡ t ∷ h ∷ w
hw-gt t h [] (canon-one .h) g with cmp3 (proj₂ t) (proj₂ h)
... | gt3 _ _ _ = refl
... | eq3 _ _ e = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (<-irrefl refl (<-trans l g))
hw-gt t h (w₁ ∷ ws) (canon-cons .h w₁ ws p s) g with cmp3 (proj₂ t) (proj₂ h)
... | gt3 _ _ _ = refl
... | eq3 _ _ e = ⊥-elim (contra-< e g)
... | lt3 _ _ l = ⊥-elim (<-irrefl refl (<-trans l g))

hw-lt : ∀ (t h : LaurentTerm) w (c : Canon (h ∷ w)) (l : proj₂ t < proj₂ h) →
  insW t (h ∷ w) c ≡ h ∷ insW t w (tc h w c)
hw-lt t h [] (canon-one .h) l with cmp3 (proj₂ t) (proj₂ h)
... | lt3 _ _ _ = refl
... | eq3 _ _ e = ⊥-elim (contra-< (sym e) l)
... | gt3 _ _ g = ⊥-elim (<-irrefl refl (<-trans l g))
hw-lt t h (w₁ ∷ ws) (canon-cons .h w₁ ws p s) l with cmp3 (proj₂ t) (proj₂ h)
... | lt3 _ _ l' = lt3-cons-shape t h w₁ ws p l' s (insertCᵌ t (w₁ ∷ ws) s)
... | eq3 _ _ e = ⊥-elim (contra-< (sym e) l)
... | gt3 _ _ g = ⊥-elim (<-irrefl refl (<-trans l g))

-- ff-gen：双前插核（cons 尾——d3 驱动）
ff-gen : ∀ (x y z z₂ : LaurentTerm) zs (g_xz : proj₂ z < proj₂ x) (g_yz : proj₂ z < proj₂ y)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs)) (d3 : Cmp3 (proj₂ x) (proj₂ y)) →
  insW x (y ∷ z ∷ z₂ ∷ zs) (canon-cons y z (z₂ ∷ zs) g_yz (canon-cons z z₂ zs p s'))
  ≡ insW y (x ∷ z ∷ z₂ ∷ zs) (canon-cons x z (z₂ ∷ zs) g_xz (canon-cons z z₂ zs p s'))
ff-gen x y z z₂ zs g_xz g_yz p s' (gt3 _ _ gxy) =
  trans (insW-cons-gt x y z (z₂ ∷ zs) g_yz (canon-cons z z₂ zs p s') gxy)
        (sym (trans (insW-cons-lt y x z (z₂ ∷ zs) g_xz (canon-cons z z₂ zs p s') gxy)
                   (cong (λ w → x ∷ w) (insW-cons-gt y z z₂ zs p s' g_yz))))
ff-gen x y z z₂ zs g_xz g_yz p s' (lt3 _ _ lxy) =
  trans (insW-cons-lt x y z (z₂ ∷ zs) g_yz (canon-cons z z₂ zs p s') lxy)
  (trans (cong (λ w → y ∷ w) (insW-cons-gt x z z₂ zs p s' g_xz))
        (sym (insW-cons-gt y x z (z₂ ∷ zs) g_xz (canon-cons z z₂ zs p s') lxy)))
ff-gen x y z z₂ zs g_xz g_yz p s' (eq3 _ _ exy) =
  trans (insW-cons-eq x y z (z₂ ∷ zs) g_yz (canon-cons z z₂ zs p s') exy)
  (trans (eqc-body-swap x y z (z₂ ∷ zs) ((proj₁ x + proj₁ y) ≟ + 0) ((proj₁ y + proj₁ x) ≟ + 0) exy)
        (sym (insW-cons-eq y x z (z₂ ∷ zs) g_xz (canon-cons z z₂ zs p s') (sym exy))))


-- 沿表等式搬 insW（Canon 经 refl 桥接 irrel——零 with 利器）
insW-move : ∀ (t : LaurentTerm) {w1 w2 : Laurent} (e : w1 ≡ w2) (c1 : Canon w1) (c2 : Canon w2) →
  insW t w1 c1 ≡ insW t w2 c2
insW-move t refl c1 c2 = insW-irrel t _ c1 c2

-- ee-core 尾版（双合并体交换，任意尾 w）
ee-core-w : ∀ (cx cy cz ex ey : ℤ) w (exy : ex ≡ ey)
  (m1 : Dec ((cx + (cy + cz)) ≡ + 0)) (m2 : Dec ((cy + (cx + cz)) ≡ + 0)) →
  hwc-body (cx , ex) (cy + cz , ey) w m1 ≡ hwc-body (cy , ey) (cx + cz , ex) w m2
ee-core-w cx cy cz ex ey w exy (yes s1) (yes s2) = refl
ee-core-w cx cy cz ex ey w exy (yes s1) (no  n2) = ⊥-elim (n2 (subst (λ v → v ≡ + 0) (sum3-eq cx cy cz) s1))
ee-core-w cx cy cz ex ey w exy (no  n1) (yes s2) = ⊥-elim (n1 (subst (λ v → v ≡ + 0) (sym (sum3-eq cx cy cz)) s2))
ee-core-w cx cy cz ex ey w exy (no  n1) (no  n2) = cong₂ (λ v e → (v , e) ∷ w) (sum3-eq cx cy cz) exy

-- cell-ee 尾版（cons 表四≟叶；hw-eq 形状无关直收）
cell-ee-w : ∀ (x y z z₂ : LaurentTerm) zs (nx : proj₁ x ≢ + 0) (ny : proj₁ y ≢ + 0)
  (exz : proj₂ x ≡ proj₂ z) (eyz : proj₂ y ≡ proj₂ z)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs))
  (dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)) (dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0))
  (c : Canon (eqc-body y z z₂ zs dyz)) (c' : Canon (eqc-body x z z₂ zs dxz)) →
  insW x (eqc-body y z z₂ zs dyz) c ≡ insW y (eqc-body x z z₂ zs dxz) c'
cell-ee-w (cx , ex) (cy , ey) (cz , ez) z₂ zs nx ny exz eyz p s' (yes zyz) (yes zxz) c c' =
  trans (hw-gt (cx , ex) z₂ zs c (lt-resp-≡' (sym exz) p))
  (trans (cong (λ v → v ∷ z₂ ∷ zs) x≡y) (sym (hw-gt (cy , ey) z₂ zs c' (lt-resp-≡' (sym eyz) p))))
  where
  x≡y : (cx , ex) ≡ (cy , ey)
  x≡y = cong₂ _,_ (sym (zero-sum-unique cy cx cz zyz zxz)) (trans exz (sym eyz))
cell-ee-w (cx , ex) (cy , ey) (cz , ez) z₂ zs nx ny exz eyz p s' (yes zyz) (no  nxz) c c' =
  trans (hw-gt (cx , ex) z₂ zs c (lt-resp-≡' (sym exz) p))
        (sym (trans rhs-eq (cong₂ (λ v e → (v , e) ∷ z₂ ∷ zs) total≡cx exy)))
  where
  exy : ey ≡ ex
  exy = trans eyz (sym exz)
  total≡cx : cy + (cx + cz) ≡ cx
  total≡cx = trans (sym (sum3-eq cx cy cz)) (trans (cong (λ v → cx + v) zyz) (+-identityʳ cx))
  nz : (cy + (cx + cz)) ≢ + 0
  nz s = nx (trans (sym total≡cx) s)
  rhs-eq : insW (cy , ey) ((cx + cz , ex) ∷ z₂ ∷ zs) c' ≡ ((cy + (cx + cz) , ey) ∷ z₂ ∷ zs)
  rhs-eq = trans (hw-eq (cy , ey) (cx + cz , ex) (z₂ ∷ zs) c' exy)
                 (hwc-no (cy , ey) (cx + cz , ex) (z₂ ∷ zs) ((cy + (cx + cz)) ≟ + 0) nz)
cell-ee-w (cx , ex) (cy , ey) (cz , ez) z₂ zs nx ny exz eyz p s' (no  nyz) (yes zxz) c c' =
  trans (trans lhs-eq (cong₂ (λ v e → (v , e) ∷ z₂ ∷ zs) total≡cy (trans exz (sym eyz))))
        (sym (hw-gt (cy , ey) z₂ zs c' (lt-resp-≡' (sym eyz) p)))
  where
  total≡cy : cx + (cy + cz) ≡ cy
  total≡cy = trans (sum3-eq cx cy cz) (trans (cong (λ v → cy + v) zxz) (+-identityʳ cy))
  nz : (cx + (cy + cz)) ≢ + 0
  nz s = ny (trans (sym total≡cy) s)
  lhs-eq : insW (cx , ex) ((cy + cz , ey) ∷ z₂ ∷ zs) c ≡ ((cx + (cy + cz) , ex) ∷ z₂ ∷ zs)
  lhs-eq = trans (hw-eq (cx , ex) (cy + cz , ey) (z₂ ∷ zs) c (trans exz (sym eyz)))
                 (hwc-no (cx , ex) (cy + cz , ey) (z₂ ∷ zs) ((cx + (cy + cz)) ≟ + 0) nz)
cell-ee-w (cx , ex) (cy , ey) (cz , ez) z₂ zs nx ny exz eyz p s' (no  nyz) (no  nxz) c c' =
  trans (hw-eq (cx , ex) (cy + cz , ey) (z₂ ∷ zs) c (trans exz (sym eyz)))
  (trans (ee-core-w cx cy cz ex ey (z₂ ∷ zs) (trans exz (sym eyz)) ((cx + (cy + cz)) ≟ + 0) ((cy + (cx + cz)) ≟ + 0))
        (sym (hw-eq (cy , ey) (cx + cz , ex) (z₂ ∷ zs) c' (trans eyz (sym exz)))))


-- ── 批2 ②f：cons-表四角子格 ────────────────────────────────────
c-ge : ∀ (x y z z₂ : LaurentTerm) zs (gxz : proj₂ z < proj₂ x) (eyz : proj₂ y ≡ proj₂ z)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs))
  (dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)) (c : Canon (eqc-body y z z₂ zs dyz)) →
  insW x (eqc-body y z z₂ zs dyz) c ≡ x ∷ eqc-body y z z₂ zs dyz
c-ge x y z z₂ zs gxz eyz p s' (yes zyz) c = hw-gt x z₂ zs c (<-trans p gxz)
c-ge x y z z₂ zs gxz eyz p s' (no  nyz) c = hw-gt x (proj₁ y + proj₁ z , proj₂ y) (z₂ ∷ zs) c (lt-resp-≡ eyz gxz)

c-le : ∀ (x y z z₂ : LaurentTerm) zs (lxz : proj₂ x < proj₂ z) (eyz : proj₂ y ≡ proj₂ z)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs))
  (dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)) (c : Canon (eqc-body y z z₂ zs dyz)) →
  insW x (eqc-body y z z₂ zs dyz) c ≡ hwc-body y z (insW x (z₂ ∷ zs) s') dyz
c-le x y z z₂ zs lxz eyz p s' (yes zyz) c = insW-irrel x (z₂ ∷ zs) c s'
c-le x y z z₂ zs lxz eyz p s' (no  nyz) c =
  trans (hw-lt x (proj₁ y + proj₁ z , proj₂ y) (z₂ ∷ zs) c (lt-resp-≡' (sym eyz) lxz))
        (cong (λ v → (proj₁ y + proj₁ z , proj₂ y) ∷ v)
              (insW-irrel x (z₂ ∷ zs) (tc (proj₁ y + proj₁ z , proj₂ y) (z₂ ∷ zs) c) s'))

c-eg : ∀ (x y z z₂ : LaurentTerm) zs (gyz : proj₂ z < proj₂ y) (exz : proj₂ x ≡ proj₂ z)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs))
  (dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)) (c : Canon (eqc-body x z z₂ zs dxz)) →
  insW y (eqc-body x z z₂ zs dxz) c ≡ y ∷ eqc-body x z z₂ zs dxz
c-eg x y z z₂ zs gyz exz p s' (yes zxz) c = hw-gt y z₂ zs c (<-trans p gyz)
c-eg x y z z₂ zs gyz exz p s' (no  nxz) c = hw-gt y (proj₁ x + proj₁ z , proj₂ x) (z₂ ∷ zs) c (lt-resp-≡ exz gyz)

c-el : ∀ (x y z z₂ : LaurentTerm) zs (lyz : proj₂ y < proj₂ z) (exz : proj₂ x ≡ proj₂ z)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs))
  (dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)) (c : Canon (eqc-body x z z₂ zs dxz)) →
  insW y (eqc-body x z z₂ zs dxz) c ≡ hwc-body x z (insW y (z₂ ∷ zs) s') dxz
c-el x y z z₂ zs lyz exz p s' (yes zxz) c = insW-irrel y (z₂ ∷ zs) c s'
c-el x y z z₂ zs lyz exz p s' (no  nxz) c =
  trans (hw-lt y (proj₁ x + proj₁ z , proj₂ x) (z₂ ∷ zs) c (lt-resp-≡' (sym exz) lyz))
        (cong (λ v → (proj₁ x + proj₁ z , proj₂ x) ∷ v)
              (insW-irrel y (z₂ ∷ zs) (tc (proj₁ x + proj₁ z , proj₂ x) (z₂ ∷ zs) c) s'))

-- ── 批2 ②g：cons 矩阵九格（IH 承重于 (lt,lt) 格）──────────────────
insW2-swap-cons : ∀ (x y z z₂ : LaurentTerm) zs (nx : proj₁ x ≢ + 0) (ny : proj₁ y ≢ + 0)
  (p : proj₂ z₂ < proj₂ z) (s' : Canon (z₂ ∷ zs)) (zfw : ZeroFree (z₂ ∷ zs))
  (ih : insW x (insW y (z₂ ∷ zs) s') (insC y (z₂ ∷ zs) s') ≡ insW y (insW x (z₂ ∷ zs) s') (insC x (z₂ ∷ zs) s'))
  (d1 : Cmp3 (proj₂ x) (proj₂ z)) (d2 : Cmp3 (proj₂ y) (proj₂ z)) →
  insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  ≡ insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (gt3 _ _ gxz) (gt3 _ _ gyz) =
  trans (insW-move x (insW-cons-gt y z z₂ zs p s' gyz) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
                   (canon-cons y z (z₂ ∷ zs) g_yz (canon-cons z z₂ zs p s')))
  (trans (ff-gen x y z z₂ zs g_xz g_yz p s' (cmp3 (proj₂ x) (proj₂ y)))
        (sym (insW-move y (insW-cons-gt x z z₂ zs p s' gxz) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
                        (canon-cons x z (z₂ ∷ zs) g_xz (canon-cons z z₂ zs p s')))))
  where
  g_xz : proj₂ z < proj₂ x
  g_xz = gxz
  g_yz : proj₂ z < proj₂ y
  g_yz = gyz
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (gt3 _ _ gxz) (lt3 _ _ lyz) = trans lhs-chain (sym rhs-chain)
  where
  W : Laurent
  W = insW y (z₂ ∷ zs) s'
  ey-inner : insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ z ∷ W
  ey-inner = insW-cons-lt y z z₂ zs p s' lyz
  c1 : Canon (z ∷ W)
  c1 = subst Canon ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ x ∷ z ∷ W
  lhs-chain = trans (insW-move x ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1) (hw-gt x z W c1 gxz)
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ x ∷ z ∷ W
  rhs-chain = trans (insW-move y (insW-cons-gt x z z₂ zs p s' gxz) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
                           (canon-cons x z (z₂ ∷ zs) gxz (canon-cons z z₂ zs p s')))
             (trans (hw-lt y x (z ∷ z₂ ∷ zs) (canon-cons x z (z₂ ∷ zs) gxz (canon-cons z z₂ zs p s')) (<-trans lyz gxz))
                    (cong (λ v → x ∷ v) (insW-cons-lt y z z₂ zs p s' lyz)))
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (gt3 _ _ gxz) (eq3 _ _ eyz) = trans lhs-chain (sym rhs-chain)
  where
  dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)
  dyz = (proj₁ y + proj₁ z) ≟ + 0
  ey-inner : insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ eqc-body y z z₂ zs dyz
  ey-inner = insW-cons-eq y z z₂ zs p s' eyz
  c1 : Canon (eqc-body y z z₂ zs dyz)
  c1 = subst Canon ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ x ∷ eqc-body y z z₂ zs dyz
  lhs-chain = trans (insW-move x ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1) (c-ge x y z z₂ zs gxz eyz p s' dyz c1)
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ x ∷ eqc-body y z z₂ zs dyz
  rhs-chain = trans (insW-move y (insW-cons-gt x z z₂ zs p s' gxz) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
                           (canon-cons x z (z₂ ∷ zs) gxz (canon-cons z z₂ zs p s')))
             (trans (hw-lt y x (z ∷ z₂ ∷ zs) (canon-cons x z (z₂ ∷ zs) gxz (canon-cons z z₂ zs p s')) (lt-resp-≡ eyz gxz))
                    (cong (λ v → x ∷ v) (insW-cons-eq y z z₂ zs p s' eyz)))
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (lt3 _ _ lxz) (gt3 _ _ gyz) = trans lhs-chain (sym rhs-chain)
  where
  W : Laurent
  W = insW x (z₂ ∷ zs) s'
  ex-inner : insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ z ∷ W
  ex-inner = insW-cons-lt x z z₂ zs p s' lxz
  c1 : Canon (z ∷ W)
  c1 = subst Canon ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ y ∷ z ∷ W
  lhs-chain = trans (insW-move x (insW-cons-gt y z z₂ zs p s' gyz) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
                           (canon-cons y z (z₂ ∷ zs) gyz (canon-cons z z₂ zs p s')))
             (trans (hw-lt x y (z ∷ z₂ ∷ zs) (canon-cons y z (z₂ ∷ zs) gyz (canon-cons z z₂ zs p s')) (<-trans lxz gyz))
                    (cong (λ v → y ∷ v) (insW-cons-lt x z z₂ zs p s' lxz)))
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ y ∷ z ∷ W
  rhs-chain = trans (insW-move y ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1) (hw-gt y z W c1 gyz)
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (lt3 _ _ lxz) (lt3 _ _ lyz) =
  trans lhs-chain (trans (cong (λ v → z ∷ v) ih) (sym rhs-chain))
  where
  W₁ W₂ : Laurent
  W₁ = insW y (z₂ ∷ zs) s'
  W₂ = insW x (z₂ ∷ zs) s'
  ey-inner : insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ z ∷ W₁
  ey-inner = insW-cons-lt y z z₂ zs p s' lyz
  c1 : Canon (z ∷ W₁)
  c1 = subst Canon ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  ex-inner : insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ z ∷ W₂
  ex-inner = insW-cons-lt x z z₂ zs p s' lxz
  c2 : Canon (z ∷ W₂)
  c2 = subst Canon ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ z ∷ insW x W₁ (insC y (z₂ ∷ zs) s')
  lhs-chain = trans (insW-move x ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1)
             (trans (hw-lt x z W₁ c1 lxz) (cong (λ v → z ∷ v) (insW-irrel x W₁ (tc z W₁ c1) (insC y (z₂ ∷ zs) s'))))
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ z ∷ insW y W₂ (insC x (z₂ ∷ zs) s')
  rhs-chain = trans (insW-move y ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c2)
             (trans (hw-lt y z W₂ c2 lyz) (cong (λ v → z ∷ v) (insW-irrel y W₂ (tc z W₂ c2) (insC x (z₂ ∷ zs) s'))))
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (lt3 _ _ lxz) (eq3 _ _ eyz) = trans lhs-chain (sym rhs-chain)
  where
  dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)
  dyz = (proj₁ y + proj₁ z) ≟ + 0
  W₂ : Laurent
  W₂ = insW x (z₂ ∷ zs) s'
  ey-inner : insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ eqc-body y z z₂ zs dyz
  ey-inner = insW-cons-eq y z z₂ zs p s' eyz
  c1 : Canon (eqc-body y z z₂ zs dyz)
  c1 = subst Canon ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  ex-inner : insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ z ∷ W₂
  ex-inner = insW-cons-lt x z z₂ zs p s' lxz
  c2 : Canon (z ∷ W₂)
  c2 = subst Canon ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ hwc-body y z W₂ dyz
  lhs-chain = trans (insW-move x ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1)
                    (c-le x y z z₂ zs lxz eyz p s' dyz c1)
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ hwc-body y z W₂ dyz
  rhs-chain = trans (insW-move y ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c2)
                    (hw-eq y z W₂ c2 eyz)
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (eq3 _ _ exz) (gt3 _ _ gyz) = trans lhs-chain (sym rhs-chain)
  where
  dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)
  dxz = (proj₁ x + proj₁ z) ≟ + 0
  ex-inner : insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ eqc-body x z z₂ zs dxz
  ex-inner = insW-cons-eq x z z₂ zs p s' exz
  c1 : Canon (eqc-body x z z₂ zs dxz)
  c1 = subst Canon ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ y ∷ eqc-body x z z₂ zs dxz
  lhs-chain = trans (insW-move x (insW-cons-gt y z z₂ zs p s' gyz) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
                           (canon-cons y z (z₂ ∷ zs) gyz (canon-cons z z₂ zs p s')))
             (trans (hw-lt x y (z ∷ z₂ ∷ zs) (canon-cons y z (z₂ ∷ zs) gyz (canon-cons z z₂ zs p s')) (lt-resp-≡ exz gyz))
                    (cong (λ v → y ∷ v) (insW-cons-eq x z z₂ zs p s' exz)))
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ y ∷ eqc-body x z z₂ zs dxz
  rhs-chain = trans (insW-move y ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1)
                    (c-eg x y z z₂ zs gyz exz p s' dxz c1)
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (eq3 _ _ exz) (lt3 _ _ lyz) = trans lhs-chain (sym rhs-chain)
  where
  dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)
  dxz = (proj₁ x + proj₁ z) ≟ + 0
  W₁ : Laurent
  W₁ = insW y (z₂ ∷ zs) s'
  ex-inner : insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ eqc-body x z z₂ zs dxz
  ex-inner = insW-cons-eq x z z₂ zs p s' exz
  c1 : Canon (eqc-body x z z₂ zs dxz)
  c1 = subst Canon ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  ey-inner : insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ z ∷ W₁
  ey-inner = insW-cons-lt y z z₂ zs p s' lyz
  c2 : Canon (z ∷ W₁)
  c2 = subst Canon ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ hwc-body x z W₁ dxz
  lhs-chain = trans (insW-move x ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c2)
                    (hw-eq x z W₁ c2 exz)
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ hwc-body x z W₁ dxz
  rhs-chain = trans (insW-move y ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1)
                    (c-el x y z z₂ zs lyz exz p s' dxz c1)
insW2-swap-cons x y z z₂ zs nx ny p s' zfw ih (eq3 _ _ exz) (eq3 _ _ eyz) = trans lhs-chain (sym rhs-chain)
  where
  dyz : Dec ((proj₁ y + proj₁ z) ≡ + 0)
  dyz = (proj₁ y + proj₁ z) ≟ + 0
  dxz : Dec ((proj₁ x + proj₁ z) ≡ + 0)
  dxz = (proj₁ x + proj₁ z) ≟ + 0
  ey-inner : insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ eqc-body y z z₂ zs dyz
  ey-inner = insW-cons-eq y z z₂ zs p s' eyz
  ex-inner : insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s') ≡ eqc-body x z z₂ zs dxz
  ex-inner = insW-cons-eq x z z₂ zs p s' exz
  c1 : Canon (eqc-body y z z₂ zs dyz)
  c1 = subst Canon ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  c2 : Canon (eqc-body x z z₂ zs dxz)
  c2 = subst Canon ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s'))
  lhs-chain : insW x (insW y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ insW y (eqc-body x z z₂ zs dxz) c2
  lhs-chain = trans (insW-move x ey-inner (insC y (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c1)
                    (cell-ee-w x y z z₂ zs nx ny exz eyz p s' dyz dxz c1 c2)
  rhs-chain : insW y (insW x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) ≡ insW y (eqc-body x z z₂ zs dxz) c2
  rhs-chain = insW-move y ex-inner (insC x (z ∷ z₂ ∷ zs) (canon-cons z z₂ zs p s')) c2

-- ── 批2 ②h：insW2-swap 总装（表归纳：nil/one/cons）─────────────────
insW2-swap : ∀ (x y : LaurentTerm) ts (c : Canon ts) →
  proj₁ x ≢ + 0 → proj₁ y ≢ + 0 → ZeroFree ts →
  insW x (insW y ts c) (insC y ts c) ≡ insW y (insW x ts c) (insC x ts c)
insW2-swap x y [] canon-nil nx ny tt = insW-swap0 x y
insW2-swap x y (z ∷ []) (canon-one .z) nx ny (nz , tt) =
  insW2-swap-one x y z nx ny nz (cmp3 (proj₂ x) (proj₂ z)) (cmp3 (proj₂ y) (proj₂ z))
insW2-swap x y (z ∷ z₂ ∷ zs) (canon-cons .z .z₂ .zs p s') nx ny (nz , zfw) =
  insW2-swap-cons x y z z₂ zs nx ny p s' zfw (insW2-swap x y (z₂ ∷ zs) s' nx ny zfw)
                 (cmp3 (proj₂ x) (proj₂ z)) (cmp3 (proj₂ y) (proj₂ z))


-- ── 批2 ③：normD-swap 零案 + normD-resp + 双收口 ────────────────

-- 双插过滤 aux（零 with）
dropZ2 : ∀ (x y : LaurentTerm) zs → Dec (proj₁ x ≡ + 0) → Dec (proj₁ y ≡ + 0) → Laurent
dropZ2 x y zs (yes _) dy = dropZ-aux y zs dy
dropZ2 x y zs (no  _) dy = x ∷ dropZ-aux y zs dy

dropZ2-link : ∀ (x y : LaurentTerm) zs (dx : Dec (proj₁ x ≡ + 0)) (dy : Dec (proj₁ y ≡ + 0)) →
  dropZ2 x y zs dx dy ≡ dropZ (x ∷ y ∷ zs)
dropZ2-link x y zs (yes zx) (yes zy) =
  sym (trans (dropZ-yes x (y ∷ zs) (proj₁ x ≟ + 0) zx) (dropZ-yes y zs (proj₁ y ≟ + 0) zy))
dropZ2-link x y zs (yes zx) (no  ny) =
  sym (trans (dropZ-yes x (y ∷ zs) (proj₁ x ≟ + 0) zx) (dropZ-no y zs (proj₁ y ≟ + 0) ny))
dropZ2-link x y zs (no  nx) (yes zy) =
  sym (trans (dropZ-no x (y ∷ zs) (proj₁ x ≟ + 0) nx) (cong (λ w → x ∷ w) (dropZ-yes y zs (proj₁ y ≟ + 0) zy)))
dropZ2-link x y zs (no  nx) (no  ny) =
  sym (trans (dropZ-no x (y ∷ zs) (proj₁ x ≟ + 0) nx) (cong (λ w → x ∷ w) (dropZ-no y zs (proj₁ y ≟ + 0) ny)))

-- swap 零案四分支（aux 范式：双 Dec 参数普通子句；(no,no) 叶引矩阵）
normD2-swap-aux : ∀ (x y : LaurentTerm) zs (dx : Dec (proj₁ x ≡ + 0)) (dy : Dec (proj₁ y ≡ + 0)) →
  norm (dropZ2 x y zs dx dy) ≡ norm (dropZ2 y x zs dy dx)
normD2-swap-aux x y zs (yes zx) (yes zy) = refl
normD2-swap-aux x y zs (yes zx) (no  ny) = refl
normD2-swap-aux x y zs (no  nx) (yes zy) = refl
normD2-swap-aux x y zs (no  nx) (no  ny) =
  insW2-swap x y (norm (dropZ zs)) (proj₂ (normC (dropZ zs))) nx ny (normC-free (dropZ zs) (dropZ-free zs))

normD-swap : ∀ (x y : LaurentTerm) zs → normD (x ∷ y ∷ zs) ≡ normD (y ∷ x ∷ zs)
normD-swap x y zs =
  trans (sym (cong norm (dropZ2-link x y zs (proj₁ x ≟ + 0) (proj₁ y ≟ + 0))))
  (trans (normD2-swap-aux x y zs (proj₁ x ≟ + 0) (proj₁ y ≟ + 0))
        (cong norm (dropZ2-link y x zs (proj₁ y ≟ + 0) (proj₁ x ≟ + 0))))

-- prep 案 aux（单 Dec 驱动）
dropZ1 : ∀ (x : LaurentTerm) ts → Dec (proj₁ x ≡ + 0) → Laurent
dropZ1 x ts (yes _) = dropZ ts
dropZ1 x ts (no  _) = x ∷ dropZ ts

dropZ1-link : ∀ (x : LaurentTerm) ts (dx : Dec (proj₁ x ≡ + 0)) → dropZ1 x ts dx ≡ dropZ (x ∷ ts)
dropZ1-link x ts (yes zx) = sym (dropZ-yes x ts (proj₁ x ≟ + 0) zx)
dropZ1-link x ts (no  nx) = sym (dropZ-no x ts (proj₁ x ≟ + 0) nx)

normD-resp-prep : ∀ (x : LaurentTerm) xs ys (dx : Dec (proj₁ x ≡ + 0)) →
  normD xs ≡ normD ys → norm (dropZ1 x xs dx) ≡ norm (dropZ1 x ys dx)
normD-resp-prep x xs ys (yes zx) ih = ih
normD-resp-prep x xs ys (no  nx) ih =
  insW-mono x (proj₂ (normC (dropZ xs))) (proj₂ (normC (dropZ ys))) ih

normD-resp : ∀ xs ys → xs ↭ ys → normD xs ≡ normD ys
normD-resp ._ ._ ↭-refl = refl
normD-resp ._ ._ (prep {xs} {ys} x p) =
  trans (sym (cong norm (dropZ1-link x xs (proj₁ x ≟ + 0))))
  (trans (normD-resp-prep x xs ys (proj₁ x ≟ + 0) (normD-resp xs ys p))
        (cong norm (dropZ1-link x ys (proj₁ x ≟ + 0))))
normD-resp ._ ._ (swap {xs} {ys} x y p) =
  trans (normD-swap x y xs)
        (trans (sym (cong norm (dropZ1-link y (x ∷ xs) (proj₁ y ≟ + 0))))
               (trans (normD-resp-prep y (x ∷ xs) (x ∷ ys) (proj₁ y ≟ + 0) (normD-resp _ _ (prep x p)))
                      (cong norm (dropZ1-link y (x ∷ ys) (proj₁ y ≟ + 0)))))
normD-resp ._ ._ (↭-t {xs} {ys} {zs} p q) = trans (normD-resp xs ys p) (normD-resp ys zs q)

-- ── 批2 ④：双收口（B 主 = normD-resp 直出；A 辅 = dropZ-id 导出）──
dropZ-id : ∀ ts → ZeroFree ts → dropZ ts ≡ ts
dropZ-id [] tt = refl
dropZ-id (t ∷ ts) (nt , zfw) =
  trans (dropZ-no t ts (proj₁ t ≟ + 0) nt) (cong (λ w → t ∷ w) (dropZ-id ts zfw))

norm-unique-dropZ : ∀ (xs ys : Laurent) → xs ↭ ys → norm (dropZ xs) ≡ norm (dropZ ys)
norm-unique-dropZ xs ys p = normD-resp xs ys p

norm-unique-nz : ∀ (xs ys : Laurent) → ZeroFree xs → ZeroFree ys → xs ↭ ys → norm xs ≡ norm ys
norm-unique-nz xs ys zxs zys p =
  trans (cong norm (sym (dropZ-id xs zxs)))
  (trans (normD-resp xs ys p) (cong norm (dropZ-id ys zys)))

-- 验证点②：反例在 B 面经真定理收口（除既有 refl 核对外加定理调用）
check-unique-ex : norm (dropZ xs-ex) ≡ norm (dropZ ys-ex)
check-unique-ex = norm-unique-dropZ xs-ex ys-ex xs-ex-↭-ys-ex

