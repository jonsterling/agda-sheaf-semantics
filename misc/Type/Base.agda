module Type.Base where

open import Agda.Primitive

t : ∀ ..ℓ → Set (lsuc ℓ)
t ℓ = Set ℓ
