open import Agda.Primitive

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

isPropIsSet : isProp (isSet A)
isPropIsSet = {!!}

postulate A : Set
postulate isSetA : isSet A

test : (x : A) → isSet (x ≡ x)
test x = isPropIsSet (isSetA x x)
