# -*- coding: utf-8 -*-
content = open('/data/work/discrete-mathematics/src/Sovereign/Cubical/Fin3.agda').read() if False else ''
# 直接从 burau 头部生成 + 完整 body
bc = open('/data/work/discrete-mathematics/src/Sovereign/Algebra/BurauCubical.agda').read()
lines = bc.split('\n')
head_end = 0
for i, l in enumerate(lines):
    if l.startswith('open import Cubical.Data.Int.Properties'):
        head_end = i + 1
        break
head = '\n'.join(lines[:head_end])
head = head.replace('module Sovereign.Algebra.BurauCubical where', 'module Sovereign.Cubical.Fin3 where')

body = '''
-- +Assoc 分派包装：z 卡头时应用 stuck 但类型完整
assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

sum3-cong : ∀ (f g : Fin 3 → ℤ) →
  f fzero ≡ g fzero → f (fsuc fzero) ≡ g (fsuc fzero) → f (fsuc (fsuc fzero)) ≡ g (fsuc (fsuc fzero)) →
  sum3 f ≡ sum3 g
sum3-cong f g p₀ p₁ p₂ = cong₂ _+_ p₀ (cong₂ _+_ p₁ p₂)

sum9-swap : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      (A1 + (A2 + A3)) + ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))
  ≡   (A1 + (B1 + C1)) + ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))
sum9-swap A1 A2 A3 B1 B2 B3 C1 C2 C3 =
      sym (assocP A1 (A2 + A3) ((B1 + (B2 + B3)) + (C1 + (C2 + C3))))
  ∙ cong (A1 +_) (sym (assocP A2 A3 ((B1 + (B2 + B3)) + (C1 + (C2 + C3))))))
  ∙ cong (A1 +_) (cong (A2 +_) (sym (assocP A3 (B1 + (B2 + B3)) (C1 + (C2 + C3))))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (A3 +_) (sym (assocP B1 (B2 + B3) (C1 + (C2 + C3)))))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (A3 +_) (cong (B1 +_) (sym (assocP B2 B3 (C1 + (C2 + C3))))))))
  -- comm 9 步冒泡：
  ∙ cong (A1 +_) (cong (A2 +_) (+Comm A3 B1))
  ∙ cong (A1 +_) (+Comm A2 B1)
  ∙ cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (cong (A3 +_) (cong (B2 +_) (+Comm B3 C1))))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (cong (A3 +_) (+Comm B2 C1)))))
  ∙ cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (+Comm A3 C1))))
  ∙ cong (A1 +_) (cong (B1 +_) (+Comm A2 C1)))
  ∙ cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (+Comm A3 B2)))))
  ∙ cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (B2 +_) (cong (A3 +_) (+Comm B3 C2))))))))
  ∙ cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (B2 +_) (+Comm A3 C2)))))))
  -- unflatten（正 assoc 收拢到目标括号形）：
  ∙ +Assoc A1 B1 (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ∙ +Assoc (A1 + B1) C1 (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))
  ∙ cong (λ w → ((A1 + B1) + C1) + w) (+Assoc B2 C2 (A3 + (B3 + C3)))
  ∙ cong (λ w → ((A1 + B1) + C1) + w) (+Assoc A2 (B2 + C2) (A3 + (B3 + C3)))
  ∙ cong (λ w → ((A1 + B1) + C1) + ((A2 + (B2 + C2)) + w)) (+Assoc A3 B3 C3)

sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f =
  sum9-swap
    (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero)))
    (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero)))
    (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))

sum3-distribˡ : ∀ (a : ℤ) (f : Fin 3 → ℤ) →
  a · sum3 f ≡ sum3 (λ k → a · f k)
sum3-distribˡ a f =
      cong₂ _+_ (·DistR+ a (f fzero) (f (fsuc fzero) + f (fsuc (fsuc fzero)))) refl
  ∙ cong (λ w → (a · f fzero) + w) (cong₂ _+_ (·DistR+ a (f (fsuc fzero)) (f (fsuc (fsuc fzero)))) refl)
'''
head = head.replace('open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+)',
                    'open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)\n' +
                    'open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)\n' +
                    'open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+)')
head = '\n'.join(l for l in head.split('\n') if 'Burau' not in l and 'λ ' not in l or l.startswith('open') or l.startswith('module'))
open('/data/work/discrete-mathematics/src/Sovereign/Cubical/Fin3.agda', 'w').write(head + '\n' + body + '\n')
print('Fin3 full written, lines:', len((head + body).split('\n')))
