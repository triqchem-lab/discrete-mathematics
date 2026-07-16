{-# OPTIONS --rewriting --guardedness #-}
module Sovereign.Coupling.LCM where
open import Data.Fin using (Fin; toℕ; fromℕ; zero; suc)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; toℕ-injective)
open import Data.Vec using (Vec; map; _∷_; []; replicate)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _^_; zero; s≤s; z≤n; _<?_; NonZero) renaming (suc to ℕsuc)
open import Data.Nat.DivMod using (_div_; _mod_; _/_; _%_; m≡m%n+[m/n]*n; m%n<n; m<n⇒m/n≡0; m/n<m; m/n*n≤m; m<n⇒m%n≡m; [m+kn]%n≡m%n; m/n/o≡m/[n*o])
open import Data.Nat.Properties using (+-mono-≤; *-mono-≤; ≤-trans; n<1+n; ≤-<-trans; ≤-reflexive; <-trans; *-assoc; *-comm; *-distribˡ-+; +-identityʳ; *-zeroʳ; n<1⇒n≡0; *-identityʳ; m≤n+m; *-cancelˡ-<; *-cancelʳ-≡; +-cancelˡ-≡; <⇒≤pred; *-distribʳ-+; +-assoc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst)
open import Relation.Nullary.Decidable.Core using (toWitness; True)
import Sovereign.Coding.Trit as T; open T using (Trit)
import Sovereign.Base.Invariants as Inv

SOVEREIGN_LCM : ℕ ; SOVEREIGN_LCM = 11609505792
GAP_THRESHOLD : ℕ ; GAP_THRESHOLD = 243
SovereignSection : Set ; SovereignSection = Vec T.Trit 30

-- 本地点积（替代 Data.Vec.Properties.eval，避免 stdlib --safe 冲突）
eval-vec : ∀ {n} → Vec ℕ n → Vec ℕ n → ℕ
eval-vec [] [] = 0
eval-vec (v ∷ vs) (p ∷ ps) = (v * p) + eval-vec vs ps
eval-vec _ _ = 0  -- NOFIX: Agda→Haskell 跨编译防御
-- GHC 验证 (2026-07-12): 无此分支 → GHC -Wincomplete-patterns
--   不等长列表 → PatternMatchFail 崩溃
--   测试: [1,2]/[3,4,5] → Safe=11, Unsafe=💥
-- Agda Vec 依赖类型保证长度相等, Haskell [Int] 无此保证

powersOf3 : Vec ℕ 30
powersOf3 = 1 ∷ 3 ∷ 9 ∷ 27 ∷ 81 ∷ 243 ∷ 729 ∷ 2187 ∷ 6561 ∷ 19683 ∷ 59049 ∷ 177147 ∷ 531441 ∷ 1594323 ∷ 4782969 ∷ 14348907 ∷ 43046721 ∷ 129140163 ∷ 387420489 ∷ 1162261467 ∷ 3486784401 ∷ 10460353203 ∷ 31381059609 ∷ 94143178827 ∷ 282429536481 ∷ 847288609443 ∷ 2541865828329 ∷ 7625597484987 ∷ 22876792454961 ∷ 68630377364883 ∷ []

sectionToCoordinate : SovereignSection → ℕ ; sectionToCoordinate sec = eval-vec (map T.toℕ sec) powersOf3
coordinateToSection : (n : ℕ) → SovereignSection ; coordinateToSection n = enc 30 n where
  enc : (k : ℕ) → ℕ → Vec T.Trit k
  enc zero _ = [] ; enc (ℕsuc k) num = (num mod 3) ∷ enc k (num div 3)
modLCM : SovereignSection → SovereignSection
modLCM sec = coordinateToSection (toℕ (sectionToCoordinate sec mod SOVEREIGN_LCM))
pack5 : Vec T.Trit 5 → ℕ
pack5 (a ∷ b ∷ c ∷ d ∷ e ∷ []) = toℕ a + toℕ b * 3 + toℕ c * 9 + toℕ d * 27 + toℕ e * 81
unpack5 : ℕ → Vec T.Trit 5
unpack5 n = (n mod 3) ∷ (n div 3 mod 3) ∷ (n div 9 mod 3) ∷ (n div 27 mod 3) ∷ (n div 81 mod 3) ∷ []
packSectionToQs : SovereignSection → Vec ℕ 6 ; packSectionToQs _ = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
unpackQsToSection : Vec ℕ 6 → SovereignSection ; unpackQsToSection _ = replicate 30 T.T₀
computeDiscreteCurvature : SovereignSection → ℤ ; computeDiscreteCurvature _ = + 0
computeLocalChernHeuristic : SovereignSection → ℕ ; computeLocalChernHeuristic _ = 0

mod%3 : ∀ n → toℕ (n mod 3) ≡ n % 3 ; mod%3 n = toℕ-fromℕ< (m%n<n n 3)

go : ℕ → ℕ → ℕ → ℕ
go 0 n pow = 0 ; go (ℕsuc k) n pow = toℕ (n mod 3) * pow + go k (n div 3) (pow * 3)

go-distrib : ∀ k n m pow → go k n (m * pow) ≡ m * go k n pow
go-distrib 0 n m pow = sym (*-zeroʳ m)
go-distrib (ℕsuc k) n m pow =
  let a = toℕ (n mod 3) ; q = n div 3 ; g = go k q (pow * 3)
      inner = trans (cong (λ x → go k q x) (*-assoc m pow 3)) (go-distrib k q m (pow * 3))
      body : a * (m * pow) + m * g ≡ m * (a * pow + g)
      body = trans (cong (λ x → x + m * g) (sym (*-assoc a m pow)))
                   (trans (cong (λ x → x * pow + m * g) (*-comm a m))
                     (trans (cong (λ x → x + m * g) (*-assoc m a pow))
                       (sym (*-distribˡ-+ m (a * pow) g))))
  in trans (cong (λ x → a * (m * pow) + x) inner) body

div-lt : ∀ n k → n < 3 * (3 ^ k) → n / 3 < 3 ^ k
div-lt n k n<3p3k = *-cancelˡ-< 3 (n / 3) (3 ^ k)
  (subst (λ x → x < 3 * (3 ^ k)) (*-comm (n / 3) 3) (≤-<-trans (m/n*n≤m n 3) n<3p3k))

lemma : ∀ k n → n < 3 ^ k → go k n 1 ≡ n
lemma 0 n n<1 = trans refl (sym (n<1⇒n≡0 n<1))
lemma (ℕsuc k) n n<3k+1 =
  let q = n / 3 ; r = n % 3
      eq : n ≡ r + q * 3 ; eq = m≡m%n+[m/n]*n n 3
      q<3k : q < 3 ^ k ; q<3k = div-lt n k n<3k+1
      ih : go k q 1 ≡ q ; ih = lemma k q q<3k
  in trans (cong (λ x → x * 1 + go k q 3) (mod%3 n))
           (trans (cong (λ x → x + go k q 3) (*-identityʳ r))
            (trans (cong (λ x → r + x) (trans (go-distrib k q 3 1) (cong (3 *_) ih)))
             (trans (cong (λ x → r + x) (*-comm 3 q)) (sym eq))))

go≡stc : ∀ n → go 30 n 1 ≡ sectionToCoordinate (coordinateToSection n)
go≡stc n = refl

LCM<3^30 : SOVEREIGN_LCM < 3 ^ 30
LCM<3^30 = toWitness {a? = SOVEREIGN_LCM <? 3 ^ 30} tt

modLCM_Legal : ∀ sec → sectionToCoordinate (modLCM sec) < SOVEREIGN_LCM
modLCM_Legal sec =
  let n = toℕ (sectionToCoordinate sec mod SOVEREIGN_LCM)
      nL = toℕ<n (sectionToCoordinate sec mod SOVEREIGN_LCM)
      n3 = <-trans nL LCM<3^30
  in subst (λ x → x < SOVEREIGN_LCM) (sym (trans (go≡stc n) (lemma 30 n n3))) nL

private
  -- distributivity lemmas
  factor4*3 : ∀ a b c d → (a + b * 3 + c * 9 + d * 27) * 3 ≡ a * 3 + b * 9 + c * 27 + d * 81
  factor4*3 a b c d =
    let s1 = b * 3 ; s2 = c * 9 ; s3 = d * 27
        step1 = *-distribʳ-+ 3 (a + s1 + s2) s3
        step2 = *-distribʳ-+ 3 (a + s1) s2
        step3 = *-distribʳ-+ 3 a s1
        as1 = *-assoc b 3 3 ; as2 = *-assoc c 9 3 ; as3 = *-assoc d 27 3
        inner1 = trans step2 (cong (λ x → x + s2 * 3) step3)
        inner2 = trans step1 (cong (λ x → x + s3 * 3) inner1)
    in trans inner2
         (trans (cong (λ x → ((a * 3 + x) + s2 * 3) + s3 * 3) as1)
           (trans (cong (λ x → ((a * 3 + b * 9) + x) + s3 * 3) as2)
             (cong (λ x → ((a * 3 + b * 9) + c * 27) + x) as3)))

  factor3*3 : ∀ a b c → (a + b * 3 + c * 9) * 3 ≡ a * 3 + b * 9 + c * 27
  factor3*3 a b c =
    let s1 = b * 3 ; s2 = c * 9
        step1 = *-distribʳ-+ 3 (a + s1) s2
        step2 = *-distribʳ-+ 3 a s1
        as1 = *-assoc b 3 3 ; as2 = *-assoc c 9 3
        inner1 = trans step2 (cong (λ x → a * 3 + x) as1)
        inner2 = trans step1 (cong (λ x → x + s2 * 3) inner1)
    in trans inner2 (cong (λ x → (a * 3 + b * 9) + x) as2)

  factor2*3 : ∀ a b → (a + b * 3) * 3 ≡ a * 3 + b * 9
  factor2*3 a b =
    trans (*-distribʳ-+ 3 a (b * 3)) (cong (λ x → a * 3 + x) (*-assoc b 3 3))

  -- associativity: flatten left-assoc to a + (sum of rest)
  assoc5 : ∀ a b c d e → a + b + c + d + e ≡ a + (b + c + d + e)
  assoc5 a b c d e =
    let s1 = +-assoc ((a + b) + c) d e
        s2 = +-assoc (a + b) c (d + e)
        s3 = +-assoc a b (c + (d + e))
        s4 = +-assoc c d e
        s5 = +-assoc b c d
        inner : b + (c + (d + e)) ≡ b + c + d + e
        inner = trans (cong (λ x → b + x) (sym s4))
                 (trans (sym (+-assoc b (c + d) e))
                   (cong (λ x → x + e) (sym s5)))
    in trans s1 (trans s2 (trans s3 (cong (λ x → a + x) inner)))

  assoc4 : ∀ a b c d → a + b + c + d ≡ a + (b + c + d)
  assoc4 a b c d = trans (+-assoc (a + b) c d) (trans (+-assoc a b (c + d)) (cong (λ x → a + x) (sym (+-assoc b c d))))

  assoc3 : ∀ a b c → a + b + c ≡ a + (b + c)
  assoc3 = +-assoc

  -- (v + q*3) % 3 = v  when v < 3
  modExtract : ∀ v q → v < 3 → (v + q * 3) % 3 ≡ v
  modExtract v q v<3 = trans ([m+kn]%n≡m%n v q 3) (m<n⇒m%n≡m v<3)

  -- (v + q*3) / 3 = q  when v < 3
  divExtract : ∀ v q → v < 3 → (v + q * 3) / 3 ≡ q
  divExtract v q v<3 =
    let n = v + q * 3
        n%3≡v : n % 3 ≡ v ; n%3≡v = modExtract v q v<3
        eq : n ≡ n % 3 + (n / 3) * 3 ; eq = m≡m%n+[m/n]*n n 3
        eq2 : v + q * 3 ≡ v + (n / 3) * 3
        eq2 = trans eq (cong (λ x → x + (n / 3) * 3) n%3≡v)
        eq3 : q * 3 ≡ (n / 3) * 3
        eq3 = +-cancelˡ-≡ v _ _ eq2
    in sym (*-cancelʳ-≡ q (n / 3) 3 eq3)

unpack5-pack5-lemma : ∀ ts → unpack5 (pack5 ts) ≡ ts
unpack5-pack5-lemma (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  let v0 = toℕ a; v1 = toℕ b; v2 = toℕ c; v3 = toℕ d; v4 = toℕ e
      S0 = v0 + v1 * 3 + v2 * 9 + v3 * 27 + v4 * 81
      S1 = v1 + v2 * 3 + v3 * 9 + v4 * 27
      S2 = v2 + v3 * 3 + v4 * 9
      S3 = v3 + v4 * 3
      S4 = v4
      v0<3 = toℕ<n a; v1<3 = toℕ<n b; v2<3 = toℕ<n c
      v3<3 = toℕ<n d; v4<3 = toℕ<n e

      -- S0 ≡ v0 + S1 * 3  (via associativity and distributivity)
      S0fact : S0 ≡ v0 + (S1 * 3)
      S0fact = trans (assoc5 v0 (v1 * 3) (v2 * 9) (v3 * 27) (v4 * 81))
                (cong (λ x → v0 + x) (sym (factor4*3 v1 v2 v3 v4)))

      -- Position 0: S0 mod 3 = a
      p0 : S0 mod 3 ≡ a
      p0 = toℕ-injective
        (trans (mod%3 S0)
          (subst (λ x → x % 3 ≡ v0) (sym S0fact)
            (modExtract v0 S1 v0<3)))

      -- S1 ≡ v1 + S2 * 3
      S1fact : S1 ≡ v1 + (S2 * 3)
      S1fact = trans (assoc4 v1 (v2 * 3) (v3 * 9) (v4 * 27))
                (cong (λ x → v1 + x) (sym (factor3*3 v2 v3 v4)))

      -- S2 ≡ v2 + S3 * 3
      S2fact : S2 ≡ v2 + (S3 * 3)
      S2fact = trans (assoc3 v2 (v3 * 3) (v4 * 9))
                (cong (λ x → v2 + x) (sym (factor2*3 v3 v4)))

      -- S3 ≡ v3 + S4 * 3  (definitional: S3 = v3 + v4*3, S4 = v4)
      S3fact : S3 ≡ v3 + (S4 * 3)
      S3fact = refl

      -- Division lemmas via divExtract
      S0div3 : (v0 + (S1 * 3)) / 3 ≡ S1
      S0div3 = divExtract v0 S1 v0<3
      S1div3 : (v1 + (S2 * 3)) / 3 ≡ S2
      S1div3 = divExtract v1 S2 v1<3
      S2div3 : (v2 + (S3 * 3)) / 3 ≡ S3
      S2div3 = divExtract v2 S3 v2<3
      S3div3 : (v3 + (S4 * 3)) / 3 ≡ S4
      S3div3 = divExtract v3 S4 v3<3

      -- Position 0 already done as p0

      -- Position 1: S0/3 mod 3 = b
      p1 : S0 div 3 mod 3 ≡ b
      p1 = toℕ-injective
        (trans (mod%3 (S0 / 3))
          (trans (cong (_% 3)
            (subst (λ x → x / 3 ≡ S1) (sym S0fact) S0div3))
            (subst (λ x → x % 3 ≡ v1) (sym S1fact)
              (modExtract v1 S2 v1<3))))

      -- Position 2: S0/9 mod 3 = c
      p2 : S0 div 9 mod 3 ≡ c
      p2 = toℕ-injective
        (trans (mod%3 (S0 / 9))
          (trans (cong (_% 3)
            (trans (sym (m/n/o≡m/[n*o] S0 3 3))
              (trans (cong (_/ 3)
                (subst (λ x → x / 3 ≡ S1) (sym S0fact) S0div3))
                (subst (λ x → x / 3 ≡ S2) (sym S1fact) S1div3))))
            (subst (λ x → x % 3 ≡ v2) (sym S2fact)
              (modExtract v2 S3 v2<3))))

      -- Position 3: S0/27 mod 3 = d
      p3 : S0 div 27 mod 3 ≡ d
      p3 = toℕ-injective
        (trans (mod%3 (S0 / 27))
          (trans (cong (_% 3)
            (trans (sym (m/n/o≡m/[n*o] S0 9 3))
              (trans (cong (_/ 3)
                (trans (sym (m/n/o≡m/[n*o] S0 3 3))
                  (trans (cong (_/ 3)
                    (subst (λ x → x / 3 ≡ S1) (sym S0fact) S0div3))
                    (subst (λ x → x / 3 ≡ S2) (sym S1fact) S1div3))))
                (subst (λ x → x / 3 ≡ S3) (sym S2fact) S2div3))))
            (subst (λ x → x % 3 ≡ v3) (sym S3fact)
              (modExtract v3 S4 v3<3))))

      -- Position 4: S0/81 mod 3 = e
      p4 : S0 div 81 mod 3 ≡ e
      p4 = toℕ-injective
        (trans (mod%3 (S0 / 81))
          (trans (cong (_% 3)
            (trans (sym (m/n/o≡m/[n*o] S0 27 3))
              (trans (cong (_/ 3)
                (trans (sym (m/n/o≡m/[n*o] S0 9 3))
                  (trans (cong (_/ 3)
                    (trans (sym (m/n/o≡m/[n*o] S0 3 3))
                      (trans (cong (_/ 3)
                        (subst (λ x → x / 3 ≡ S1) (sym S0fact) S0div3))
                        (subst (λ x → x / 3 ≡ S2) (sym S1fact) S1div3))))
                    (subst (λ x → x / 3 ≡ S3) (sym S2fact) S2div3))))
                (subst (λ x → x / 3 ≡ S4) (sym S3fact) S3div3))))
            (m<n⇒m%n≡m v4<3)))

  in cong₅ p0 p1 p2 p3 p4
  where
    cong₅ : ∀ {A : Set} {x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : A}
           → x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ → x₅ ≡ y₅
           → (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) ≡ (y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ [])
    cong₅ refl refl refl refl refl = refl

pack5RangeValid : ∀ ts → pack5 ts < GAP_THRESHOLD
pack5RangeValid (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  let v0 = toℕ a; v1 = toℕ b; v2 = toℕ c; v3 = toℕ d; v4 = toℕ e
      v0≤2 = <⇒≤pred (toℕ<n a); v1≤2 = <⇒≤pred (toℕ<n b)
      v2≤2 = <⇒≤pred (toℕ<n c); v3≤2 = <⇒≤pred (toℕ<n d); v4≤2 = <⇒≤pred (toℕ<n e)
      v1*3≤6 = *-mono-≤ v1≤2 (≤-reflexive refl)
      v2*9≤18 = *-mono-≤ v2≤2 (≤-reflexive refl)
      v3*27≤54 = *-mono-≤ v3≤2 (≤-reflexive refl)
      v4*81≤162 = *-mono-≤ v4≤2 (≤-reflexive refl)
      sum≤242 : v0 + v1 * 3 + v2 * 9 + v3 * 27 + v4 * 81 ≤ 242
      sum≤242 =
        let s1 = +-mono-≤ v0≤2 v1*3≤6
            s2 = +-mono-≤ s1 v2*9≤18
            s3 = +-mono-≤ s2 v3*27≤54
            s4 = +-mono-≤ s3 v4*81≤162
        in s4
  in ≤-<-trans sum≤242 (n<1+n 242)
