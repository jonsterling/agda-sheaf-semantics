module Site where

open import Agda.Primitive

import Category as C
import Pullback
import Pretopology

record t ..{o h h~ i j} : Set (lsuc (i ⊔ j ⊔ o ⊔ h ⊔ h~)) where
  field
    cat : C.t o h h~
    pullbacks : Pullback.has cat
    pretopology : Pretopology.t cat pullbacks i j
