module Setoid.Coproduct where

import Setoid.Base as S
import Type as T

_×_
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t ℓ₁ᵒ ℓ₁ʰ)
  → S.t _ _
A × B = record
  { obj = S.t.obj A T.∐.× S.t.obj B
  ; hom = λ {((a₀ T.∐., b₀) T.∐., (a₁ T.∐., b₁)) →
      S.t.hom A (a₀ T.∐., a₁) T.∐.× S.t.hom B (b₀ T.∐., b₁)
    }
  ; idn = T.∐.⟨ S.t.idn A , S.t.idn B ⟩
  ; cmp = T.∐.⟨ S.t.cmp A T.Π.∘ T.∐.⟨ T.∐.π₀ × T.∐.π₀ ⟩
              , S.t.cmp B T.Π.∘ T.∐.⟨ T.∐.π₁ × T.∐.π₁ ⟩ ⟩
  ; inv = T.∐.⟨ S.t.inv A × S.t.inv B ⟩
  }
