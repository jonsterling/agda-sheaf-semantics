module Setoid.Homotopy where

open import Agda.Primitive
import Setoid.Base as S
import Setoid.Path as Path
import Setoid.Product.Boot as Π
import Setoid.Terminal as 𝟙
import Type as T

record _⇒₁_ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ʰ) where
  constructor nat
  field
    com : ∀ {a} → S.t.hom B (F Π.$₀ a T.∐., G Π.$₀ a)
open _⇒₁_ public

idn
  : ∀ {ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ} {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (F : A Π.⇒₀ᵗ B)
  → T.𝟙.t T.Π.⇒₀ (F ⇒₁ F)
idn {A = A} F = λ x → nat (F Π.$₁ S.t.idn A x)

cmp
  : ∀ {ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ} {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → (G ⇒₁ H) T.∐.× (F ⇒₁ G)
  → F ⇒₁ H
cmp {B = B} (β T.∐., α) = record
  { com = S.cmp B (com β T.∐., com α) }

inv
  : ∀ {ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ} {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ G) T.Π.⇒₀ (G ⇒₁ F)
inv {B = B} α = record
  { com = S.inv B (com α) }
