module Type.Homotopy where

open import Agda.Primitive
import Type.Base as T
import Type.Coproduct as ∐
import Type.Path as Path
  renaming (t to _≡_)
import Type.Product as Π
import Type.Terminal as 𝟙

record _⇒₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (F G : A Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  constructor nat
  field
    com : ∀ {x} → F x Path.≡ G x
open _⇒₁_ public

idn
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → (F : A Π.⇒₀ B)
  → 𝟙.t Π.⇒₀ (F ⇒₁ F)
idn F = λ x → nat (Path.idn x)

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G H : A Π.⇒₀ B}
  → (G ⇒₁ H) ∐.× (F ⇒₁ G)
  → F ⇒₁ H
cmp (β ∐., α) = record
  { com = Path.cmp (com β ∐., com α) }

inv
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G : A Π.⇒₀ B}
  → (F ⇒₁ G) Π.⇒₀ (G ⇒₁ F)
inv α = record
  { com = Path.inv (com α) }

_∘w₀_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → (H : B Π.⇒₀ C)
  → (α : F ⇒₁ G)
  → (H Π.∘ F) ⇒₁ (H Π.∘ G)
H ∘w₀ α = record
  { com = H Path.$₁ com α }

_∘w₁_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {G H : B Π.⇒₀ C}
  → (β : G ⇒₁ H)
  → (F : A Π.⇒₀ B)
  → (G Π.∘ F) ⇒₁ (H Π.∘ F)
β ∘w₁ F = record
  { com = com β }

_∘h₀_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (β : H ⇒₁ K)
  → (α : F ⇒₁ G)
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
_∘h₀_ {K = K} β α = record
  { com = Path.cmp (K Path.$₁ com α ∐., com β) }

_∘h₁_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ} {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (β : H ⇒₁ K)
  → (α : F ⇒₁ G)
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
_∘h₁_ {H = H} β α = record
  { com = Path.cmp (com β ∐., H Path.$₁ com α) }
