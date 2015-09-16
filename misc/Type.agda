module Type where

open import Type.Base public
import Type.Coproduct
import Type.Homotopy
import Type.Initial
import Type.Op
import Type.Path
import Type.Product
import Type.Terminal

module ∐ = Type.Coproduct
module Homo = Type.Homotopy
module 𝟘 = Type.Initial
module Op = Type.Op
module Path = Type.Path
module Π = Type.Product
module 𝟙 = Type.Terminal
