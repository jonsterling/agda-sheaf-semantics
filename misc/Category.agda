module Category where

import Category.Coproduct
import Category.Initial
import Category.Product
import Category.Terminal

module ∐ = Category.Coproduct
module 𝟙 = Category.Initial
module Π = Category.Product
module 𝟘 = Category.Terminal

