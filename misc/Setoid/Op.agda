module Setoid.Op where

import Setoid.Base as S
import Type as T

s : ∀ ..{ℓᵒ ℓʰ} → S.t ℓᵒ ℓʰ → S.t ℓᵒ ℓʰ
s A = record
  { obj = T.Op.t (S.t.obj A)
  ; hom = S.hom A T.Π.∘ T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
  ; idn = S.idn A
  ; cmp = S.cmp A T.Π.∘ T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
  ; inv = S.inv A
  }
