module Setoid.Product where

open import Agda.Primitive
import Setoid.Base as S
open import Setoid.Product.Boot public
import Setoid.Extensionality as Ext
import Type as T

infixr 1 _∘_

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
