module Preorder where

  open import Relation.Binary
  open import Level            using (0ℓ) public
  open import Relation.Nullary

  postulate
    Label   : Set
    _⊑_     : Label → Label → Set
    ⊑-refl  : Reflexive _⊑_
    ⊑-trans : Transitive _⊑_
    ⊑-dec   : Decidable (_⊑_)
