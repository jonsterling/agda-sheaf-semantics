module Type.Coproduct where

open import Agda.Primitive
open import Type.Coproduct.Boot public

ᵛ : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : A → Set ℓ₁} {Φ : t A B → Set ℓ₂}
  → (ϕ : (x : A) (y : B x) → Φ (x , y))
  → (∀ x → Φ x)
ᵛ ϕ (x , y) = ϕ x y

⟨_,_⟩ : ∀ ..{ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {A : X → Set ℓ₁} {B : ∀ {x} → A x → Set ℓ₂}
  → (F : (x : X) → A x)
  → (G : (x : X) → B (F x))
  → ((x : X) → t (A x) B)
⟨ F , G ⟩ x = F x , G x

⟨_×_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : X₀ → Set ℓ₁}
  → {A : Set ℓ₂} {B : A → Set ℓ₃}
  → (F : X₀ → A)
  → (G : ∀ {x₀} → X₁ x₀ → B (F x₀))
  → (t X₀ X₁ → t A B)
⟨ F × G ⟩ (x , y) = F x , G y

[_,_] : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₀} {X : Set ℓ₁}
  → (F : A → X)
  → (G : B → X)
  → (A + B → X)
[ F , G ] (ι₀ a) = F a
[ F , G ] (ι₁ b) = G b
