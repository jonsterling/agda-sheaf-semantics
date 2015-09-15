module Type where

open import Type.Base public
import Type.Coproduct
import Type.Initial
import Type.Product
import Type.Terminal

module ∐ = Type.Coproduct
module 𝟘 = Type.Initial
module Π = Type.Product
module 𝟙 = Type.Terminal
