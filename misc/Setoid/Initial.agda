module Setoid.Initial where

open import Agda.Primitive
import Setoid.Base as S
import Setoid.Product as Π
import Type as T

s : S.t lzero lzero
s = record
  { obj = T.𝟘.t
  ; hom = λ {(() T.∐., π₁)}
  ; idn = λ {}
  ; cmp = λ {}
  ; inv = λ {}
  }

¡ : ∀ ..{ℓᵒ ℓʰ} {A : S.t ℓᵒ ℓʰ} → s Π.⇒₀ᵗ A
¡ = record
  { _$₀_ = λ ()
  ; _$₁_ = λ {}
  }

¬_ : ∀ ..{ℓᵒ ℓʰ} (A : S.t ℓᵒ ℓʰ) → Set (ℓᵒ ⊔ ℓʰ)
¬ A = A Π.⇒₀ᵗ s
