module Setoid.Coproduct where

import Setoid.Base as S
open import Setoid.Coproduct.Boot public
open import Setoid.Product as Π
import Setoid.Homotopy as Homo
import Type as T

π₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (A × B) Π.⇒₀ᵗ A
π₀ = record
  { _$₀_ = T.∐.π₀
  ; _$₁_ = T.∐.π₀
  }

π₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (A × B) Π.⇒₀ᵗ B
π₁ = record
  { _$₀_ = T.∐.π₁
  ; _$₁_ = T.∐.π₁
  }

⟨-,-⟩
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {X : S.t ℓ₀ᵒ ℓ₀ʰ} {A : S.t ℓ₁ᵒ ℓ₁ʰ} {B : S.t ℓ₂ᵒ ℓ₂ʰ}
  → ((X Π.⇒₀ˢ A) × (X Π.⇒₀ˢ B)) Π.⇒₀ᵗ (X Π.⇒₀ˢ A × B)
⟨-,-⟩ = record
  { _$₀_ = λ FG → record
    { _$₀_ = T.∐.⟨ T.∐.π₀ FG $₀_ , T.∐.π₁ FG $₀_ ⟩
    ; _$₁_ = T.∐.⟨ T.∐.π₀ FG $₁_ , T.∐.π₁ FG $₁_ ⟩
    }
  ; _$₁_ = Homo.nat T.Π.∘ (λ x → T.∐.⟨ Homo.com′ × Homo.com′ ⟩ x)
  }

⟨-×-⟩
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ ℓ₃ᵒ ℓ₃ʰ}
  → {X₀ : S.t ℓ₀ᵒ ℓ₀ʰ} {X₁ : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₂ᵒ ℓ₂ʰ} {B : S.t ℓ₃ᵒ ℓ₃ʰ}
  → ((X₀ Π.⇒₀ˢ A) × (X₁ Π.⇒₀ˢ B)) Π.⇒₀ᵗ ((X₀ × X₁) Π.⇒₀ˢ (A × B))
⟨-×-⟩ = record
  { _$₀_ = λ FG → record
    { _$₀_ = T.∐.⟨ T.∐.π₀ FG $₀_ × T.∐.π₁ FG $₀_ ⟩
    ; _$₁_ = T.∐.⟨ T.∐.π₀ FG $₁_ × T.∐.π₁ FG $₁_ ⟩
    }
  ; _$₁_ = Homo.nat T.Π.∘ (λ x → T.∐.⟨ Homo.com′ × Homo.com′ ⟩ x)
  }
