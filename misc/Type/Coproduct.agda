module Type.Coproduct where

open import Agda.Primitive
open import Type.Coproduct.Boot public
import Type.Product as Π

ᵛ : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : A → Set ℓ₁} {Φ : t A B → Set ℓ₂}
  → (ϕ : Π.t A (λ x → Π.t (B x) (λ y → Φ (x , y))))
  → (Π.t (t A B) Φ)
ᵛ ϕ (x , y) = ϕ x y

⟨_,_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {X : Set ℓ₀} {A : X → Set ℓ₁} {B : ∀ {x} → A x → Set ℓ₂}
  → (F : Π.t X A)
  → (G : Π.t X (λ x → B (F x)))
  → (Π.t X (λ x → t (A x) B))
⟨ F , G ⟩ x = F x , G x

⟨_×_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : X₀ → Set ℓ₁} {A : Set ℓ₂} {B : A → Set ℓ₃}
  → (F : X₀ Π.⇒₀ A)
  → (G : ∀ {x₀} → X₁ x₀ Π.⇒₀ B (F x₀))
  → (t X₀ X₁ Π.⇒₀ t A B)
⟨ F × G ⟩ (x , y) = F x , G y

[_,_]
  : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀} {B : Set ℓ₀} {X : Set ℓ₁}
  → (F : A Π.⇒₀ X)
  → (G : B Π.⇒₀ X)
  → (A + B Π.⇒₀ X)
[ F , G ] (ι₀ a) = F a
[ F , G ] (ι₁ b) = G b
