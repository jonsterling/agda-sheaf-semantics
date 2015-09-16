module Type.Path where

import Type.Coproduct as ∐
import Type.Product as Π
import Type.Terminal as 𝟙

data t ..{ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : t a a
{-# BUILTIN EQUALITY t #-}
{-# BUILTIN REFL refl #-}

primitive
  primTrustMe : ∀ {ℓ} {A : Set ℓ} {a b : A} → t a b

idn
  : ∀ ..{ℓ} {A : Set ℓ} {a : A}
  → 𝟙.t Π.⇒₀ t a a
idn = Π.! refl

cmp
  : ∀ ..{ℓ} {A : Set ℓ} {a b c : A}
  → t b c ∐.× t a b Π.⇒₀ t a c
cmp (refl ∐., refl) = refl

inv
  : ∀ ..{ℓ} {A : Set ℓ} {a b : A}
  → t a b Π.⇒₀ t b a
inv refl = refl

_$₁_
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {a b}
  → (F : A Π.⇒₀ B)
  → (t a b Π.⇒₀ t (F a) (F b))
_$₁_ f refl = refl

subst
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {a b}
  → (Ψ : A → Set ℓ₁)
  → (f : t a b)
  → ((ψ : Ψ a) → Ψ b)
subst Ψ refl ψ = ψ
