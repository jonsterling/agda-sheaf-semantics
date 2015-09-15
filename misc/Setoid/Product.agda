module Setoid.Product where

open import Agda.Primitive
import Setoid.Base as S
open import Setoid.Product.Boot public
import Setoid.Homotopy as Homo
import Type as T

s : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t ℓ₁ᵒ ℓ₁ʰ)
  → S.t _ _
s A B = record
  { obj = A ⇒₀ B
  ; hom = λ {(F T.∐., G) → F Homo.⇒₁ G}
  ; idn = Homo.idn _
  ; cmp = Homo.cmp
  ; inv = Homo.inv
  }

idn
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → T.𝟙.t T.Π.⇒₀ (A ⇒₀ A)
idn T.𝟙.* = record
  { _$₀_ = T.Π.id
  ; _$₁_ = T.Π.id
  }

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ C) T.∐.× (A ⇒₀ B) T.Π.⇒₀ (A ⇒₀ C)
cmp (G T.∐., F) = record
  { _$₀_ = (G $₀_) T.Π.∘ (F $₀_)
  ; _$₁_ = (G $₁_) T.Π.∘ (F $₁_)
  }
