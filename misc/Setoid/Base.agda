module Setoid.Base where

open import Agda.Primitive

import Type as T

record t ..(ℓᵒ ℓʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓʰ)) where
  field
    obj : Set ℓᵒ
    hom : obj T.∐.× obj → Set ℓʰ
    idn : ∀ {a} → T.#1.t T.Π.⇒₀ hom ( a T.∐., a )
    cmp : ∀ {a b c} → hom (b T.∐., c) T.∐.× hom (a T.∐., b) T.Π.⇒₀ hom (a T.∐., c)
    inv : ∀ {a b} → hom (a T.∐., b) T.Π.⇒₀ hom (b T.∐., a)

  _≈_ : (a b : obj) → Set ℓʰ
  a ≈ b = hom (a T.∐., b)

  _∘_ : ∀ {a b c} (g : hom (b T.∐., c)) (f : hom (a T.∐., b)) → hom (a T.∐., c)
  g ∘ f = cmp (g T.∐., f)
open t public
