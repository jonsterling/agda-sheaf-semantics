module Setoid.Extensionality where

open import Agda.Primitive
import Setoid.Base as S
import Setoid.Product.Boot as Π
import Type as T

record _⇒₁_ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  (F G : A Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ʰ) where
  field
    com : ∀ {a} → S.t.hom B (F Π.$₀ a T.∐., G Π.$₀ a)
open _⇒₁_

