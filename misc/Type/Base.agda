module Type.Base where

open import Agda.Primitive

t : ∀ ..ℓ → Set (lsuc ℓ)
t ℓ = Set ℓ

! : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} → A → B → A
! x _ = x
