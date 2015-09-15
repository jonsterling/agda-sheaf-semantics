module Setoid.Product.Boot where

open import Agda.Primitive
import Setoid.Base as S
import Type as T

infixr 1 _⇒₀ᵗ_

record _⇒₀ᵗ_ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  (B : S.t ℓ₁ᵒ ℓ₁ʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  infixr 1 _$₀_
  infixr 1 _$₁_
  field
    _$₀_ : S.t.obj A T.Π.⇒₀ S.t.obj B
    _$₁_ : ∀ {a b} → S.t.hom A (a T.∐., b) T.Π.⇒₀ S.t.hom B (_$₀_ a T.∐., _$₀_ b)
open _⇒₀ᵗ_ public
