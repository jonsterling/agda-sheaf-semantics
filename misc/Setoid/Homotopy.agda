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
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (F : A Π.⇒₀ᵗ B)
  → T.𝟙.t T.Π.⇒₀ (F ⇒₁ F)
idn {A = A} F = λ x → nat (F Π.$₁ S.t.idn A x)

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → (G ⇒₁ H) T.∐.× (F ⇒₁ G)
  → F ⇒₁ H
cmp {B = B} (β T.∐., α) = record
  { com = S.cmp B (com β T.∐., com α) }

inv
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ G) T.Π.⇒₀ (G ⇒₁ F)
inv {B = B} α = record
  { com = S.inv B (com α) }

cmp-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ }
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.× (F ⇒₁ G))
  → (T.∐.π₀ Hα Π.∘ᵗ F) ⇒₁ (T.∐.π₀ Hα Π.∘ᵗ G)
cmp-w₀ (H T.∐., α) = record
  { com = H Π.$₁ com α }

cmp-w₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
   → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ H) T.∐.× (A Π.⇒₀ᵗ B))
  → (G Π.∘ᵗ T.∐.π₁ βF) ⇒₁ (H Π.∘ᵗ T.∐.π₁ βF)
cmp-w₁ (β T.∐., F) = record
  { com = com β }

cmp-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.× (F ⇒₁ G))
  → (H Π.∘ᵗ F) ⇒₁ (K Π.∘ᵗ G)
cmp-h₀ {C = C} {K = K} (β T.∐., α) = record
  { com = S.cmp C (K Π.$₁ com α T.∐., com β) }

cmp-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.× (F ⇒₁ G))
  → (H Π.∘ᵗ F) ⇒₁ (K Π.∘ᵗ G)
cmp-h₁ {C = C} {H = H} (β T.∐., α) = record
  { com = S.cmp C (com β T.∐., H Π.$₁ com α) }
