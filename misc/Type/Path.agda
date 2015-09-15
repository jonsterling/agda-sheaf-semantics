module Type.Path where

import Type.Coproduct as ∐
import Type.Product as Π
import Type.Terminal as 𝟙

data t ..{ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : t x x
{-# BUILTIN EQUALITY t #-}
{-# BUILTIN REFL refl #-}

primitive
  primTrustMe : ∀ {ℓ} {A : Set ℓ} {x y : A} → t x y

idn
  : ∀ ..{ℓ} {A : Set ℓ} {x : A}
  → 𝟙.t Π.⇒₀ t x x
idn = Π.! refl

cmp
  : ∀ ..{ℓ} {A : Set ℓ} {x y z : A}
  → t y z ∐.× t x y Π.⇒₀ t x z
cmp (refl ∐., refl) = refl

inv
  : ∀ ..{ℓ} {A : Set ℓ} {x y : A}
  → t x y Π.⇒₀ t y x
inv refl = refl

_$₁_
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {x y}
  → (f : A Π.⇒₀ B)
  → (t x y Π.⇒₀ t (f x) (f y))
_$₁_ f refl = refl

subst
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {x y}
  → (Φ : A → Set ℓ₁)
  → (p : t x y)
  → ((ϕ : Φ x) → Φ y)
subst Φ refl x = x
