module Type.Op where

import Type.Base as T

t : ∀ ..{ℓᵒ} → T.t ℓᵒ → T.t ℓᵒ
t A = A
