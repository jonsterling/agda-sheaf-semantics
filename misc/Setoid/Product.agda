module Setoid.Product where

open import Agda.Primitive
import Setoid.Base as S
import Type as T

infixr 0 _⇒₀_
infixr 1 _∘_

record _⇒₀_ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  (B : S.t ℓ₁ᵒ ℓ₁ʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  infixl 1 _$₀_
  infixl 1 _$₁_
  field
    _$₀_ : S.t.obj A T.Π.⇒₀ S.t.obj B
    _$₁_ : ∀ {a b} → S.t.hom A (a T.∐., b) T.Π.⇒₀ S.t.hom B (_$₀_ a T.∐., _$₀_ b)
open _⇒₀_ public

id
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → A ⇒₀ A
id = record
  { _$₀_ = T.Π.id
  ; _$₁_ = T.Π.id
  }

_∘_
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → B ⇒₀ C
  → A ⇒₀ B
  → A ⇒₀ C
G ∘ F = record
  { _$₀_ = (G $₀_) T.Π.∘ (F $₀_)
  ; _$₁_ = (G $₁_) T.Π.∘ (F $₁_)
  }
