module Setoid.Product where

open import Agda.Primitive
import Setoid.Base as S
open import Setoid.Coproduct.Boot as ∐
open import Setoid.Product.Boot public
import Setoid.Homotopy as Homo
import Setoid.Terminal as 𝟙
import Type as T

infixr 2 _⇒₀ˢ_

_⇒₀ˢ_ : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t ℓ₁ᵒ ℓ₁ʰ)
  → S.t _ _
_⇒₀ˢ_ A B = record
  { obj = A ⇒₀ᵗ B
  ; hom = λ {(F T.∐., G) → F Homo.⇒₁ G}
  ; idn = Homo.idn _
  ; cmp = Homo.cmp
  ; inv = Homo.inv
  }

idn
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → 𝟙.s ⇒₀ᵗ (A ⇒₀ˢ A)
idn = record
  { _$₀_ = idnᵗ
  ; _$₁_ = Homo.idn _
  }

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ˢ C) ∐.× (A ⇒₀ˢ B) ⇒₀ᵗ (A ⇒₀ˢ C)
cmp {C = C} = record
  { _$₀_ = cmpᵗ
  ; _$₁_ = Homo.cmp-h₁
  }
