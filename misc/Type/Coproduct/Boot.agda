module Type.Coproduct.Boot where

open import Agda.Primitive

infixr 0 _,_

record t ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀
open t public

syntax t A (λ x → B) = t[ x ∈ A ] B

_×_ : ∀ ..{ℓ₀ ℓ₁} → (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A × B = t A λ _ → B

data _+_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  ι₀ : A → A + B
  ι₁ : B → A + B
