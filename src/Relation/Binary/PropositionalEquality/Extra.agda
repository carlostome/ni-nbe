module Relation.Binary.PropositionalEquality.Extra where

  open import Relation.Binary.PropositionalEquality

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v p q} → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
  cong₃ f refl refl refl = refl
