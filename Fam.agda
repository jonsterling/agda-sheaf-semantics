module Fam where

open import Agda.Primitive

record t ..{i j} (cod : Set j) : Set (lsuc i ⊔ j) where
  constructor ⟨_,_⟩
  field
    dom : Set i
    π : dom → cod

open t public
