module Preorder where

  open import Relation.Binary
  open import Level            using (0ℓ)

  postulate
    Label   : Set
    _⊑_     : Label → Label → Set
    ⊑-refl  : Reflexive _⊑_
    ⊑-trans : Transitive _⊑_
