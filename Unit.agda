module Unit where

record t ..{i} : Set i where
  constructor ⟨⟩

module Notation where
  !_ : ∀ ..{i j} {A : Set i} → A → (t {j} → A)
  ! a = λ _ → a
