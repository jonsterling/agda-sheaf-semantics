module Setoid.Terminal where

open import Agda.Primitive
import Setoid.Base as S
import Type as T

s : S.t lzero lzero
s = record
  { obj = T.𝟙.t
  ; hom = T.Π.! T.𝟙.t
  }
