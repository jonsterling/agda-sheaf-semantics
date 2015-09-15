module EquivalenceRelation where

open import Agda.Primitive

record t ..{i j} {A : Set i} (R : A → A → Set j) : Set (i ⊔ j) where
  field
    reflexivity : ∀ x → R x x
    symmetry : ∀ x y → R x y → R y x
    transitivity : ∀ x y z → R x y → R y z → R x z

