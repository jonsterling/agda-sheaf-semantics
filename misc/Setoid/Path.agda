module Setoid.Path where

import Setoid.Base as S
import Type as T

s : ∀ ..{ℓᵒ} (A : T.t ℓᵒ) → S.t ℓᵒ ℓᵒ
s A = record
  { obj = A
  ; hom = λ {(a T.∐., b) → T.Path.t a b}
  ; idn = T.Path.idn
  ; cmp = T.Path.cmp
  ; inv = T.Path.inv
  }
