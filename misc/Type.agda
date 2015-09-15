module Type where

open import Type.Base public
import Type.Coproduct
import Type.Homotopy
import Type.Initial
import Type.Path
import Type.Product
import Type.Terminal

module ∐ = Type.Coproduct
module Homo = Type.Homotopy
module 𝟘 = Type.Initial
module Path = Type.Path
module Π = Type.Product
module 𝟙 = Type.Terminal
