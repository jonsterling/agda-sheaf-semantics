module Type.Coproduct where

open import Agda.Primitive

infixr 0 _,_

record t ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀
open t public

syntax t A (λ x → B) = t[ x ∈ A ] B

ᵛ : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : A → Set ℓ₁} {Φ : t A B → Set ℓ₂}
  → (ϕ : (x : A) (y : B x) → Φ (x , y))
  → (∀ x → Φ x)
ᵛ ϕ (x , y) = ϕ x y

_×_ : ∀ ..{ℓ₀ ℓ₁} → (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A × B = t A λ _ → B

⟨_,_⟩ : ∀ ..{ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {A : X → Set ℓ₁} {B : ∀ {x} → A x → Set ℓ₂}
  → (f : (x : X) → A x)
  → (g : (x : X) → B (f x))
  → ((x : X) → t (A x) B)
⟨ f , g ⟩ x = f x , g x

⟨_×_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : X₀ → Set ℓ₁}
  → {A : Set ℓ₂} {B : A → Set ℓ₃}
  → (f : X₀ → A)
  → (g : ∀ {x₀} → X₁ x₀ → B (f x₀))
  → (t X₀ X₁ → t A B)
⟨ f × g ⟩ (x , y) = f x , g y

data _+_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  ι₀ : A → A + B
  ι₁ : B → A + B

[_,_] : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₀} {X : Set ℓ₁}
  → (f : A → X)
  → (g : B → X)
  → (A + B → X)
[ f , g ] (ι₀ a) = f a
[ f , g ] (ι₁ b) = g b
