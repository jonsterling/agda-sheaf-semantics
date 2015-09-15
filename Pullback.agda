module Pullback where

open import Agda.Primitive

import Category as C
import Setoid as S
import Coproduct as ∐
open S.Notation
open ∐.Notation

module Sig ..{o h h~} (𝒞 : C.t o h h~) where
  open C.sig (C.struct 𝒞)
  open C.Notation (C.struct 𝒞)

  module _ {𝔵 𝔶 𝔷} (f : ∣ hom 𝔵 𝔷 ∣) (g : ∣ hom 𝔶 𝔷 ∣) where
    record law 𝔭 : Set (o ⊔ h ⊔ h~) where
      field
        π₁ : ∣ hom 𝔭 𝔵 ∣
        π₂ : ∣ hom 𝔭 𝔶 ∣
        comm : hom 𝔭 𝔷 ∋ g ∘ π₂ ~ f ∘ π₁
        pull : ∀ {𝔮} (h₁ : ∣ hom 𝔮 𝔵 ∣) (h₂ : ∣ hom 𝔮 𝔶 ∣) (p : hom 𝔮 𝔷 ∋ g ∘ h₂ ~ f ∘ h₁) → ∐.t! (hom 𝔮 𝔭) (λ u → (hom 𝔮 𝔶 ∋ π₂ ∘ u ~ h₂) × (hom 𝔮 𝔵 ∋ π₁ ∘ u ~ h₁))

    record t : Set (o ⊔ h ⊔ h~) where
      field
        pullback : _
        is-pullback : law pullback
      open law is-pullback public

  has : Set (o ⊔ h ⊔ h~)
  has = ∀ {𝔵 𝔶 𝔷} (f : ∣ hom 𝔵 𝔷 ∣) (g : ∣ hom 𝔶 𝔷 ∣) → t f g

  open law public

open Sig public
