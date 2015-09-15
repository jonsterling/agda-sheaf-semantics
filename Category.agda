module Category where

open import Agda.Primitive
import Setoid
open Setoid.Notation

record sig ..o ..h ..h~ : Set (lsuc (o ⊔ h ⊔ h~)) where
  field
    ob : Set o
    hom : ob → ob → Setoid.t h h~
    idn : ∀ {𝔞} → ∣ hom 𝔞 𝔞 ∣
    cmp : ∀ {𝔞 𝔟 𝔠} (g : ∣ hom 𝔟 𝔠 ∣) (f : ∣ hom 𝔞 𝔟 ∣) → ∣ hom 𝔞 𝔠 ∣

module Notation ..{o h h~} (𝒞 : sig o h h~) where
  open sig 𝒞

  infixr 10 _∘_
  _∘_ : ∀ {𝔞 𝔟 𝔠} (g : ∣ hom 𝔟 𝔠 ∣) (f : ∣ hom 𝔞 𝔟 ∣) → ∣ hom 𝔞 𝔠 ∣
  _∘_ = cmp

  _⋙_ : ∀ {𝔞 𝔟 𝔠} (f : ∣ hom 𝔞 𝔟 ∣) (g : ∣ hom 𝔟 𝔠 ∣)  → ∣ hom 𝔞 𝔠 ∣
  f ⋙ g = cmp g f

record law ..{o h h~} (𝒞 : sig o h h~) : Set (lsuc (o ⊔ h ⊔ h~)) where
  open sig 𝒞; open Notation 𝒞
  field
    idn-l : ∀ {𝔞 𝔟} (f : ∣ hom 𝔞 𝔟 ∣) → hom 𝔞 𝔟 ∋ idn ∘ f ~ f
    idn-r : ∀ {𝔞 𝔟} (f : ∣ hom 𝔞 𝔟 ∣) → hom 𝔞 𝔟 ∋ f ~ idn ∘ f
    assoc : ∀ {𝔞 𝔟 𝔠 𝔡} (f : ∣ hom 𝔠 𝔡 ∣) (g : ∣ hom 𝔟 𝔠 ∣) (h : ∣ hom 𝔞 𝔟 ∣) → hom 𝔞 𝔡 ∋ (f ∘ g) ∘ h ~ f ∘ g ∘ h

record t ..o ..h ..h~ : Set (lsuc (o ⊔ h ⊔ h~)) where
  field
    struct : sig o h h~
    is-category : law struct

open sig public
open law public
open t public
