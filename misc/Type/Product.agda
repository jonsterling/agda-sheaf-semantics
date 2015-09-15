module Type.Product where

open import Agda.Primitive

infixr 0 _⇒₀_
infixr 1 _∘_

t : ∀ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
t A B = (x : A) → B x

syntax t A (λ x → B) = t[ x ∈ A ] B

_⇒₀_ : ∀ ..{ℓ₀ ℓ₁} → (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A ⇒₀ B = A → B

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

_∘_
  : ∀ {ℓ₀ ℓ₁ ℓ₂} {A : Set ℓ₀} {B : A → Set ℓ₁} {C : ∀ {a} → B a → Set ℓ₂}
  → (g : ∀ {a} → (b : B a) → C b)
  → (f : (a : A) → B a)
  → ((a : A) → C (f a))
_∘_ g f = λ x → g (f x)
