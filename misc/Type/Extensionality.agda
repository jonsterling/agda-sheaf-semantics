module Type.Extensionality where

open import Agda.Primitive
import Type.Base as T
import Type.Identity as Id
  renaming (t to _≡_)
import Type.Product as Π

record _⇒₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (f g : A Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  field
    com : ∀ {x} → f x Id.≡ g x
open _⇒₁_
