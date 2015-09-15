module Type.Identity where

data t ..{ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : t x x
{-# BUILTIN EQUALITY t #-}
{-# BUILTIN REFL refl #-}

primitive
  primTrustMe : ∀ {ℓ} {A : Set ℓ} {x y : A} → t x y

trans
  : ∀ ..{ℓ} {A : Set ℓ} {x y z : A}
  → (p₁ : t y z)
  → (p₀ : t x y)
  → t x z
trans refl refl = refl

sym
  : ∀ ..{ℓ} {A : Set ℓ} {x y : A}
  → t x y
  → t y x
sym refl = refl

cong
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {x y}
  → (f : A → B)
  → (t x y → t (f x) (f y))
cong f refl = refl

subst
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {x y}
  → (Φ : A → Set ℓ₁)
  → (p : t x y)
  → ((ϕ : Φ x) → Φ y)
subst Φ refl x = x
