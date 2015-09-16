module Setoid where

import Setoid.Coproduct
import Setoid.Homotopy
import Setoid.Initial
import Setoid.Op
import Setoid.Path
import Setoid.Product
import Setoid.Terminal

module ∐ = Setoid.Coproduct
module Homo = Setoid.Homotopy
module 𝟘 = Setoid.Initial
module Op = Setoid.Op
module Path = Setoid.Path
module Π = Setoid.Product
module 𝟙 = Setoid.Terminal
