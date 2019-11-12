module Neutrality where

  open import Preorder

  open import Type
  open import NormalForm
  open import Variable

  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Binary hiding (_⇒_)

  -- there are no neutrals typed in the
  -- empty context
  emptyNe : ∀ {a} → ¬ (Ne a Ø)
  emptyNe (var ())
  emptyNe (x ∙ _) = emptyNe x

  -- type a occurs as a subformula of type b
  data _⊲_ (a : Type) : (b : Type) → Set where
    ⊴-refl  : a ⊲ a
    -- sbl⇒  : ∀ {a b c} → a ⊲ b → a ⊲ (b ⇒ c)
    sbr⇒  : ∀ {b c} → a ⊲ c → a ⊲ (b ⇒ c)
    -- sbl+  : ∀ {a b c} → a ⊲ b → a ⊲ (b + c)
    -- sbr+  : ∀ {a b c} → a ⊲ c → a ⊲ (b + c)

  ⊲-trans : Transitive _⊲_
  ⊲-trans ⊴-refl y            = y
  ⊲-trans (sbr⇒ x) ⊴-refl     = sbr⇒ x
  ⊲-trans (sbr⇒ x) (sbr⇒ y) = sbr⇒ (⊲-trans (sbr⇒ x) y)

  -- type a occurs as a subformula of some type
  -- in context Γ
  data _⊲ᶜ_  (a : Type) : (Γ : Ctx) → Set where
    here  :  ∀ {b} {Γ} → a ⊲ b  → a ⊲ᶜ (Γ `, b)
    there :  ∀ {b} {Γ} → a ⊲ᶜ Γ → a ⊲ᶜ (Γ `, b)

  -- if type a is in context Γ then it occurs
  -- as a subformula
  neutrVar : ∀ {a} {Γ} → a ∈ Γ → a ⊲ᶜ Γ
  neutrVar ze     = here ⊴-refl
  neutrVar (su v) = there (neutrVar v)

  neutr⇒ : ∀ {a b c} → (b ⇒ c) ⊲ a → c ⊲ a
  neutr⇒ ⊴-refl     = sbr⇒ ⊴-refl
  -- neutr⇒ (sbl⇒ p) = sbl⇒ (neutr⇒ p)
  neutr⇒ (sbr⇒ p) = sbr⇒ (neutr⇒ p)
  -- neutr⇒ (sbr+ p) = sbr+ (neutr⇒ p)
  -- neutr⇒ (sbl+ p) = sbl+ (neutr⇒ p)

  ⊲-lift : ∀ {a b} {Γ} → a ⊲ b → b ⊲ᶜ Γ → a ⊲ᶜ Γ
  ⊲-lift p (here q)  = here  (⊲-trans p q)
  ⊲-lift p (there q) = there (⊲-lift p q)

  neutrality : ∀ {a} {Γ} → Ne a Γ → a ⊲ᶜ Γ
  neutrality (var x) = neutrVar x
  neutrality (x ∙ n) = ⊲-lift (sbr⇒ ⊴-refl) (neutrality x)
