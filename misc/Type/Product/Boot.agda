module Type.Product.Boot where

open import Agda.Primitive
import Type.Coproduct.Boot as ∐

infixr 0 _⇒₀_

t : ∀ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
t A B = (x : A) → B x

syntax t A (λ x → B) = t[ x ∈ A ] B

_⇒₀_
  : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A ⇒₀ B = A → B

idn
  : ∀ {ℓ} {A : Set ℓ}
  → A ⇒₀ A
idn x = x

cmp
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : A → Set ℓ₁} {C : ∀ {a} → B a → Set ℓ₂}
  → (GF : (∀ {a} → t (B a) C) ∐.× (t A B))
  → (t A (λ a → C (∐.π₁ GF a)))
cmp (G ∐., F) = λ x → G (F x)
