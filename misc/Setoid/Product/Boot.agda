module Setoid.Product.Boot where

open import Agda.Primitive
import Setoid.Base as S
import Type as T

infixr 1 _⇒₀ᵗ_
infixr 2 _∘ᵗ_

record _⇒₀ᵗ_ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  (B : S.t ℓ₁ᵒ ℓ₁ʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  infixr 1 _$₀_
  infixr 1 _$₁_
  field
    _$₀_ : S.t.obj A T.Π.⇒₀ S.t.obj B
    _$₁_ : ∀ {a b} → S.t.hom A (a T.∐., b) T.Π.⇒₀ S.t.hom B (_$₀_ a T.∐., _$₀_ b)
open _⇒₀ᵗ_ public

idnᵗ
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → T.𝟙.t T.Π.⇒₀ (A ⇒₀ᵗ A)
idnᵗ T.𝟙.* = record
  { _$₀_ = T.Π.idn
  ; _$₁_ = T.Π.idn
  }

cmpᵗ
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.∐.× (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
cmpᵗ (G T.∐., F) = record
  { _$₀_ = (G $₀_) T.Π.∘ (F $₀_)
  ; _$₁_ = (G $₁_) T.Π.∘ (F $₁_)
  }

_∘ᵗ_
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.Π.⇒₀ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_∘ᵗ_ G F = cmpᵗ (G T.∐., F)
