module Neutrality where

  open import Preorder

  open import Type
  open import NormalForm
  open import Variable

  open import Data.Empty
  open import Relation.Nullary
  import Relation.Binary   as B

  emptyNe : ∀ {a} → ¬ (Ne a Ø)
  emptyNe (var ())
  emptyNe (x ∙ _) = emptyNe x

  BinOp = Type → Type → Type

  data _⊲_ : Type → Type → Set where
    refl  : ∀{a} → a ⊲ a
    -- sbl⇒  : ∀ {a b c} → a ⊲ b → a ⊲ (b ⇒ c)
    sbr⇒  : ∀ {a b c} → a ⊲ c → a ⊲ (b ⇒ c)
    -- sbl+  : ∀ {a b c} → a ⊲ b → a ⊲ (b + c)
    -- sbr+  : ∀ {a b c} → a ⊲ c → a ⊲ (b + c)

  postulate
    ⊲-trans : B.Transitive _⊲_

  data _⊲ᶜ_ : Type → Ctx → Set where
    here  :  ∀ {a b} {Γ} → a ⊲ b  → a ⊲ᶜ (Γ `, b)
    there :  ∀ {a b} {Γ} → a ⊲ᶜ Γ → a ⊲ᶜ (Γ `, b)

  neutrVar : ∀ {a} {Γ} → a ∈ Γ → a ⊲ᶜ Γ
  neutrVar ze = here refl
  neutrVar (su v) = there (neutrVar v)

  neutr⇒ : ∀ {a b c} → (b ⇒ c) ⊲ a → c ⊲ a
  neutr⇒ refl     = sbr⇒ refl
  -- neutr⇒ (sbl⇒ p) = sbl⇒ (neutr⇒ p)
  neutr⇒ (sbr⇒ p) = sbr⇒ (neutr⇒ p)
  -- neutr⇒ (sbr+ p) = sbr+ (neutr⇒ p)
  -- neutr⇒ (sbl+ p) = sbl+ (neutr⇒ p)

  ⊲-lift : ∀ {b a} {Γ} → b ⊲ a → a ⊲ᶜ Γ → b ⊲ᶜ Γ
  ⊲-lift p (here q)  = here (⊲-trans p q)
  ⊲-lift p (there q) = there (⊲-lift p q)

  neutrality : ∀ {a} {Γ} → Ne a Γ → a ⊲ᶜ Γ
  neutrality (var x) = neutrVar x
  neutrality (x ∙ n) = ⊲-lift (sbr⇒ refl) (neutrality x)
