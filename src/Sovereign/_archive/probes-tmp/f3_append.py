# -*- coding: utf-8 -*-
# Fin3 body 拼接脚本：在 Fin3.agda 末尾追加 sum3 定义与引理（Unicode 直书）
p = '/data/work/discrete-mathematics/src/Sovereign/Cubical/Fin3.agda'
body = '''
-- ────────────────────────────────────────────────────────────────────
-- sum3：3 项和（直接展开，右结合）
-- ────────────────────────────────────────────────────────────────────

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

-- 逐项改写（f ≡ g 逐 3 点）
sum3-cong : ∀ (f g : Fin 3 → ℤ) →
  f fzero ≡ g fzero → f (fsuc fzero) ≡ g (fsuc fzero) → f (fsuc (fsuc fzero)) ≡ g (fsuc (fsuc fzero)) →
  sum3 f ≡ sum3 g
sum3-cong f g p₀ p₁ p₂ = cong₂ _+_ p₀ (cong₂ _+_ p₁ p₂)

-- ────────────────────────────────────────────────────────────────────
-- 纯 9 变量转置：列分组 → 行分组
-- LHS：(A1+(A2+A3)) + ((B1+(B2+B3)) + (C1+(C2+C3)))
-- RHS：(A1+(B1+C1)) + ((A2+(B2+C2)) + (A3+(B3+C3)))
-- 证明：flatten 4 步（组间 sym assoc）→ comm 9 步 → unflatten 4 步
-- ────────────────────────────────────────────────────────────────────

sum9-swap : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      (A1 + (A2 + A3)) + ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))
  ≡   (A1 + (B1 + C1)) + ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))
sum9-swap A1 A2 A3 B1 B2 B3 C1 C2 C3 =
      sym (+Assoc A1 (A2 + A3) ((B1 + (B2 + B3)) + (C1 + (C2 + C3))))
  ∙ cong (A1 +_) (sym (+Assoc A2 A3 ((B1 + (B2 + B3)) + (C1 + (C2 + C3))))))
  ∙ cong (A1 +_) (cong (A2 +_) (sym (+Assoc A3 ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (A3 +_) (sym (+Assoc B1 (B2 + B3) (C1 + (C2 + C3)))))))
  -- 全右结合 9 叶，comm 9 步冒泡：
  ∙ cong (A1 +_) (cong (A2 +_) (+Comm A3 B1))
  ∙ cong (A1 +_) (+Comm A2 B1)
  ∙ cong (A1 +_) (cong (A2 +_) (cong (A3 +_) (cong (B1 +_) (cong (B2 +_) (+Comm B3 C1))))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (cong (A3 +_) (+Comm B2 C1)))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (+Comm A3 C1))))
  ∙ cong (A1 +_) (cong (B1 +_) (+Comm A2 C1)))
  ∙ cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (A3 +_) (+Comm B2 A3))))))
  ∙ cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (B2 +_) (cong (A3 +_) (+Comm B3 C2))))))))
  ∙ cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (B2 +_) (+Comm A3 C2)))))) 
  -- unflatten（正 assoc 收拢到目标括号形）：
  ∙ +Assoc A1 (B1 + C1) ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))
  ∙ cong (A1 +_) (+Assoc B1 C1 ((A2 + (B2 + C2)) + (A3 + (B3 + C3))))
  ∙ +Assoc A1 ((B1 + C1) + (A2 + (B2 + C2))) (A3 + (B3 + C3))
  ∙ cong (A1 +_) (+Assoc (B1 + C1) (A2 + (B2 + C2)) (A3 + (B3 + C3)))

-- ────────────────────────────────────────────────────────────────────
-- sum3 交换：组装
-- ────────────────────────────────────────────────────────────────────

sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f =
  sum9-swap
    (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero)))
    (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero)))
    (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))

-- ────────────────────────────────────────────────────────────────────
-- sum3 分配律
-- ────────────────────────────────────────────────────────────────────

sum3-distribˡ : ∀ (a : ℤ) (f : Fin 3 → ℤ) →
  a · sum3 f ≡ sum3 (λ k → a · f k)
sum3-distribˡ a f =
      cong₂ _+_ (·DistR+ a (f fzero) (f (fsuc fzero) + f (fsuc (fsuc fzero)))) refl
  ∙ cong (λ w → (a · f fzero) + w) (cong₂ _+_ (·DistR+ a (f (fsuc fzero)) (f (fsuc (fsuc fzero)))) refl)
'''
s = open(p).read()
s = s.replace('\n\n-- BODY-PENDING\n', body)
open(p, 'w').write(s)
print('body appended, total lines:', len(s.split('\n')))
