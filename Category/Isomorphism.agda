open import Agda.Primitive
import Category as C

module Category.Isomorphism ..{o h h~} (𝒞 : C.t o h h~) where
  import Setoid as S
  import Coproduct as ∐

  open S.Notation
  open C.sig (C.cat 𝒞)
  open C.Notation (C.cat 𝒞)

  record law {𝔠 𝔡} (to : ∣ hom 𝔠 𝔡 ∣): Set (o ⊔ h ⊔ h~) where
    field
      from : ∣ hom 𝔡 𝔠 ∣
      id₁ : hom 𝔠 𝔠 ∋ from ∘ to ~ idn
      id₂ : hom 𝔡 𝔡 ∋ to ∘ from ~ idn

  t : ob → ob → Set (h~ ⊔ (h ⊔ o))
  t 𝔠 𝔡 = ∐.t ∣ hom 𝔠 𝔡 ∣ law

  open law public
