module Category.Base where

open import Agda.Primitive

import Setoid as S
import Type as T

record t ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ)) where
  open S.Π
  open T.∐
  field
    obj : Set ℓᵒ
    homˢ : obj T.∐.× obj T.Π.⇒₀ S.t ℓˢᵒ ℓˢʰ
    idnᵐ : ∀ {a} → S.𝟙.s S.Π.⇒₀ᵗ homˢ (a , a)
    cmpᵐ : ∀ {a b c} → homˢ (b , c) S.∐.× homˢ (a , b) S.Π.⇒₀ᵗ homˢ (a , c)

  field
    .idn-lhs
      : ∀ {a b}
      → (f : S.t.obj (homˢ (a , b)))
      → S.hom (homˢ (a , b))
          ( cmpᵐ $₀ (idnᵐ $₀ T.𝟙.* , f)
          , f
          )

    .idn-rhs
      : ∀ {a b}
      → (f : S.t.obj (homˢ (a , b)))
      → S.hom (homˢ (a , b))
          ( f
          , cmpᵐ $₀ (f , idnᵐ $₀ T.𝟙.*)
          )

    .cmp-ass
      : ∀ {a b c d}
      → (f : S.t.obj (homˢ (a , b)))
      → (g : S.t.obj (homˢ (b , c)))
      → (h : S.t.obj (homˢ (c , d)))
      → S.hom (homˢ (a , d))
          ( cmpᵐ $₀ (cmpᵐ $₀ (h , g) , f)
          , cmpᵐ $₀ (h , cmpᵐ $₀ (g , f))
          )
open t public

-- FIXME: notation
