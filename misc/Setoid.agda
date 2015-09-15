module Setoid where

import Setoid.Coproduct
import Setoid.Initial
import Setoid.Product
import Setoid.Terminal

module ∐ = Setoid.Coproduct
module 𝟘 = Setoid.Initial
module Π = Setoid.Product
module 𝟙 = Setoid.Terminal
