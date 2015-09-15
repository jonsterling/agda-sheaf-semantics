module Type.Extensionality where

open import Agda.Primitive
import Type.Base as T
import Type.Identity as Paths
  renaming (t to _≡_)
import Type.Product as Π

record _⇒₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (F G : A Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  field
    com : ∀ {x} → F x Paths.≡ G x
open _⇒₁_ public

id
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → (F : A Π.⇒₀ B)
  → F ⇒₁ F
id F = record
  { com = Paths.idn }

_∘v_
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G H : A Π.⇒₀ B}
  → (β : G ⇒₁ H)
  → (α : F ⇒₁ G)
  → F ⇒₁ H
β ∘v α = record
  { com = Paths.cmp (com β) (com α) }

_∘w₀_
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → (H : B Π.⇒₀ C)
  → (α : F ⇒₁ G)
  → (H Π.∘ F) ⇒₁ (H Π.∘ G)
H ∘w₀ α = record
  { com = H Paths.$₁ com α }

_∘w₁_
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {G H : B Π.⇒₀ C}
  → (α : G ⇒₁ H)
  → (F : A Π.⇒₀ B)
  → (G Π.∘ F) ⇒₁ (H Π.∘ F)
α ∘w₁ F = record
  { com = com α }

_∘h₀_
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (β : H ⇒₁ K)
  → (α : F ⇒₁ G)
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
_∘h₀_ {K = K} β α = record
  { com = Paths.cmp (K Paths.$₁ com α) (com β) }

_∘h₁_
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (β : H ⇒₁ K)
  → (α : F ⇒₁ G)
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
_∘h₁_ {H = H} β α = record
  { com = Paths.cmp (com β) (H Paths.$₁ com α) }
