module Type.Path where

import Type.Coproduct as ∐

data t ..{ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  idn : t x x
{-# BUILTIN EQUALITY t #-}
{-# BUILTIN REFL idn #-}

primitive
  primTrustMe : ∀ {ℓ} {A : Set ℓ} {x y : A} → t x y

cmp
  : ∀ ..{ℓ} {A : Set ℓ} {x y z : A}
  → t y z ∐.× t x y
  → t x z
cmp (idn ∐., idn) = idn

inv
  : ∀ ..{ℓ} {A : Set ℓ} {x y : A}
  → t x y
  → t y x
inv idn = idn

_$₁_
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {x y}
  → (f : A → B)
  → (t x y → t (f x) (f y))
_$₁_ f idn = idn

subst
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {x y}
  → (Φ : A → Set ℓ₁)
  → (p : t x y)
  → ((ϕ : Φ x) → Φ y)
subst Φ idn x = x
