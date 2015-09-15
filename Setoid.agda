module Setoid where

open import Agda.Primitive
import EquivalenceRelation as EqR

record t ..i ..j : Set (lsuc (i ⊔ j)) where
  field
    ob : Set i
    hom : ob → ob → Set j
    hom-equiv : EqR.t hom

open t public

module Notation where
  ∣_∣ : ∀ ..{i j} → t i j → Set i
  ∣ S ∣ = ob S

  infix 3 _∋_~_
  _∋_~_ : ∀ ..{i j} (S : t i j) → ∣ S ∣ → ∣ S ∣ → Set j
  S ∋ m ~ n = hom S m n
