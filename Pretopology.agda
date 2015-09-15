module Pretopology where

open import Agda.Primitive
import Setoid as S
import Category as C
import Pullback
import Fam as 𝔉
import Coproduct as ∐
import Unit as 𝟙

open S.Notation

module _ ..{o h h~} (𝒞 : C.t o h h~) (pullback : Pullback.has 𝒞) where
  open C.sig (C.cat 𝒞)
  import Category.Isomorphism 𝒞 as Iso

  module PB = Pullback.Sig 𝒞

  hom⟨—,_⟩ : ob → Set (o ⊔ h)
  hom⟨—, 𝔡 ⟩ = ∐.t ob λ 𝔠 → ∣ hom 𝔠 𝔡 ∣

  module CoveringFam ..{ℓ} where
    t : ob → Set (lsuc ℓ ⊔ h ⊔ o)
    t 𝔡 = 𝔉.t {ℓ} hom⟨—, 𝔡 ⟩

    module Notation where
      mk-covering-fam : ∀ (I : Set ℓ) (𝔡 : ob) (𝔠 : I → ob) (f : (i : I) → ∣ hom (𝔠 i) 𝔡 ∣) → t 𝔡
      mk-covering-fam I 𝔡 𝔠 f = 𝔉.⟨ I , (λ i → ∐.⟨ 𝔠 i , f i ⟩) ⟩

      syntax mk-covering-fam I 𝔡 𝔠 f = ⟨ f ∶ 𝔠 ⇒ 𝔡 ∣ I ⟩

  record sig ..i ..j : Set (lsuc (i ⊔ j) ⊔ o ⊔ h) where
    field
      covers : (𝔡 : ob) (F : CoveringFam.t {i} 𝔡) → Set j

    Δ_ : ob → Set (lsuc i ⊔ h ⊔ o)
    Δ 𝔡 = CoveringFam.t {i} 𝔡
    syntax covers 𝔠 F = F ▹ 𝔠

  record law ..{i j} (𝔅 : sig i j) : Set (lsuc (i ⊔ j) ⊔ o ⊔ h ⊔ h~) where
    open sig 𝔅; open 𝟙.Notation; open ∐.Notation; open C.Notation (C.cat 𝒞); open CoveringFam.Notation

    field
      isomorphisms-cover :
        {𝔠 𝔡 : _}
        (f : ∣ hom 𝔠 𝔡 ∣)
          → Iso.law f
          → ⟨ ! f ∶ ! 𝔠 ⇒ 𝔡 ∣ 𝟙.t ⟩ ▹ 𝔡

      stability :
        {𝔠 𝔡 : _}
        (F : Δ 𝔡) (let module F = 𝔉.t F; f = λ i → ∐.π₂ (F.π i))
        (g : ∣ hom 𝔠 𝔡 ∣)
        (let module F×g i = PB.t _ _ (pullback (f i) g))
          → F ▹ 𝔡
          → ⟨ F×g.π₂ ∶ F×g.pullback ⇒ 𝔠 ∣ F.dom ⟩ ▹ 𝔠

      transitivity :
        {𝔡 : _}
        (F : Δ 𝔡) (let module F = 𝔉.t F; 𝔠 = λ i → ∐.π₁ (F.π i); f = λ i → ∐.π₂ (F.π i))
        (G : ∀ i → Δ 𝔠 i) (let module G i = 𝔉.t (G i); g = λ i j → ∐.π₂ (G.π i j))
          → F ▹ 𝔡
          → (∀ i → G i ▹ 𝔠 i)
          → ⟨ (λ { ∐.⟨ i , j ⟩ → f i ∘ g i j }) ∶ _ ⇒ 𝔡 ∣ ∐.t F.dom G.dom ⟩ ▹ 𝔡
