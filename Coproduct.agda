module Coproduct where

open import Agda.Primitive
import Setoid as S
open S.Notation

record t ..{i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B π₁

record t! ..{i i~ j} (A : S.t i i~) (B : ∣ A ∣ → Set j) : Set (i ⊔ i~ ⊔ j) where
  constructor _unique_
  field
    pair : t ∣ A ∣ B
    unique : (a : ∣ A ∣) (p : B a) → A ∋ a ~ t.π₁ pair

open t public

module Notation where
  _×_ : ∀ ..{i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A × B = t A (λ _ → B)
