# 待重贴：`NSESupportBound` 的零场刻画（2026-10-21）

> **状态**：内容已两次写入并编译通过（回执 `9cbf67cc` / `1a3e14d3` / `2b6575e3`），
> 但均被**并行协作者的整文件重写**抹掉（文件回到 89 行版本）。
> **判据**：回执变化先查 md5/行数——同一文件回执连变两次 = 有人在写它。
> **触发条件**：该文件 mtime 稳定 ≥ 数分钟后再贴；贴完立即 `proof_compile` + 登记。

## 要贴的内容（追加到 `NSESupportBound.agda` 末尾）

先补两处 import：
```agda
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; +-mono-≤; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
```

然后追加（已在会话中两次编译通过）：

```agda
-- §5 标量场：countOver f ≡ 0 ⇔ f 处处为零
isNonZero-zero : ∀ t → isNonZero t ≡ 0 → t ≡ T₀
isNonZero-zero T₀ e = refl
isNonZero-zero T₁ ()
isNonZero-zero T₂ ()

fold1N-zero : ∀ (g : C3 → ℕ) → fold1N g ≡ 0 → ∀ y → g y ≡ 0
fold1N-zero g e fzero = m+n≡0⇒m≡0 (g fzero) e
fold1N-zero g e (fsuc fzero) = m+n≡0⇒m≡0 (g (fsuc fzero)) (m+n≡0⇒n≡0 (g fzero) e)
fold1N-zero g e (fsuc (fsuc fzero)) =
  m+n≡0⇒n≡0 (g (fsuc fzero)) (m+n≡0⇒n≡0 (g fzero) e)

-- G6..G1：镜像 countOver 的六层定义（必须由内向外声明）
G6 : ScalarField → C3 → C3 → C3 → C3 → C3 → C3 → ℕ
G6 f y1 y2 y3 y4 y5 y6 = isNonZero (f (y1 , y2 , y3 , y4 , y5 , y6))
-- … G5..G1 同构（详见会话；每个都是 fold1N ∘ G_{k+1}）

countOver-zero : ∀ (f : ScalarField) → countOver f ≡ 0
               → ∀ x1 x2 x3 x4 x5 x6 → f (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀
countOver-zero f e x1 x2 x3 x4 x5 x6 =
  isNonZero-zero _
    (fold1N-zero (G6 f x1 x2 x3 x4 x5)
      (fold1N-zero (G5 f x1 x2 x3 x4)
        (fold1N-zero (G4 f x1 x2 x3)
          (fold1N-zero (G3 f x1 x2)
            (fold1N-zero (G2 f x1)
              (fold1N-zero (G1 f) e x1) x2) x3) x4) x5) x6)

fold1N-cong : ∀ {g g' : C3 → ℕ} → (∀ y → g y ≡ g' y) → fold1N g ≡ fold1N g'
fold1N-cong p = cong₂ _+_ (p fzero) (cong₂ _+_ (p (fsuc fzero)) (p (fsuc (fsuc fzero))))

countOver-zero← : ∀ (f : ScalarField)
                → (∀ x1 x2 x3 x4 x5 x6 → f (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
                → countOver f ≡ 0
countOver-zero← f h =
  trans (fold1N-cong (λ y1 → fold1N-cong (λ y2 → fold1N-cong (λ y3 →
          fold1N-cong (λ y4 → fold1N-cong (λ y5 → fold1N-cong (λ y6 →
            cong isNonZero (h y1 y2 y3 y4 y5 y6)))))))) refl
```

§6/§7（Field 六分量）用 `_SixZero` 打包六个分量，正向拆外层和（`m+n≡0⇒m/n≡0` 五次）
后逐分量套 `countOver-zero`；反向用 `countOver-zero←` 六次 + `cong₂ _+_` 嵌套。

## 为什么值得重贴
它把该模块 §4 的 ②（「supportCount 的零场刻画——未证」）从**整条未证**推进到
**双向 + 两层面（标量场 / Field）全闭合**（反向 Field 版亦然）。
