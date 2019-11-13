module Security.Reduction where

open import Type
open import Variable
open import Term
open import Preorder
open import Substitution

variable
  a b c : Type
  ℓ ℓ'  : Label
  Γ Δ   : Ctx

open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)

isValue : Term a Γ → Set
isValue unit     = ⊤
isValue (`λ t)   = ⊤
isValue (η t)    = isValue t
isValue (inl t)  = isValue t
isValue (inr t)  = isValue t
isValue (var x)  = ⊥
isValue (t ∙ t₁) = ⊥
isValue (x ↑ t)  = ⊥
isValue (t ≫= t₁) = ⊥
isValue (case t t₁ t₂) = ⊥

open import Data.Product

Value : Type → Ctx → Set
Value a Γ = Σ (Term a Γ) isValue

infix 2 _⟶_

open import Substitution using (subst ; idₛ)

subst1 : Term a (Γ `, b) → Value b Γ → Term a Γ
subst1 t (u , _) = subst (idₛ `, u) t

data _⟶_ : Term a Γ → Term a Γ → Set where

  ξ-∙₁ : {t t' : Term (a ⇒ b) Γ} {u : Term a Γ}
    → t ⟶ t'
      ---------------
    → t ∙ u ⟶ t' ∙ u

  ξ-∙₂ : {t : Term (a ⇒ b) Γ} {u u' : Term a Γ}
    → isValue t
    → u ⟶ u'
      ---------------
    → t ∙ u ⟶ t ∙ u'

  red-λ  : {t : Term b (Γ `, a)} {u : Term a Γ}
    → (v : isValue u)
    ---------------------------
    → (`λ t) ∙ u ⟶ subst1 t (u , v)

  ξ-≫= : {u u' : Term (⟨ ℓ ⟩ a) Γ} {t : Term (⟨ ℓ ⟩ b) (Γ `, a) }
    → u ⟶ u'
    ------------------------
    → (u ≫= t) ⟶ (u' ≫= t)

  red-≫=  : {u : Term a Γ} {t : Term (⟨ ℓ ⟩ b) (Γ `, a)}
    → (v : isValue u)
    → (η u ≫= t) ⟶ subst1 t (u , v)

  ξ-case : {t t' : Term (a + b) Γ} {t₁ : Term c (Γ `, a)} {t₂ : Term c (Γ `, b)}
    → t ⟶ t'
    -------------------------------
    → case t t₁ t₂ ⟶ case t' t₁ t₂

  red-case₁ : {t : Term a Γ} {t₁ : Term c (Γ `, a)} {t₂ : Term c (Γ `, b)}
    → (v : isValue t)
    → case (inl t) t₁ t₂ ⟶ subst1 t₁ (t , v)

  red-case₂ : {t : Term b Γ} {t₁ : Term c (Γ `, a)} {t₂ : Term c (Γ `, b)}
    → (v : isValue t)
    → case (inr t) t₁ t₂ ⟶ subst1 t₂ (t , v)

  ξ-↑  : {t t' : Term (⟨ ℓ ⟩ a) Γ} {p : ℓ ⊑ ℓ'}
    → t ⟶ t'
    -------------------------
    → (p ↑ t) ⟶ (p ↑ t')

  red-↑ : {t : Term a Γ} {p : ℓ ⊑ ℓ'}
    → (p ↑ η t) ⟶ η t

  ξ-η : {t t' : Term a Γ}
    → t ⟶ t'
    → η {ℓ} t ⟶ η t'

  ξ-inl : {t t' : Term a Γ}
    → t ⟶ t'
    → inl {_} {a} {b} t ⟶ inl t'

  ξ-inr : {t t' : Term a Γ}
    → t ⟶ t'
    → inr {_} {b} {a} t ⟶ inr t'

data _⟶*_ : (Term a Γ) → (Term a Γ) → Set where

  refl : (t : Term a Γ)
       ------
     → t ⟶* t

  trans : (t t' u : Term a Γ)
     → t  ⟶* t'
     → t' ⟶* u
     -----------
     → t  ⟶* u

module _ where

  open import Relation.Nullary using (¬_)

  -- values don't reduce
  val¬⟶ : (t : Term a Γ) → isValue t → {t' : Term a Γ} → ¬ (t ⟶ t')
  val¬⟶ unit    _ = λ ()
  val¬⟶ (`λ _)  _ = λ ()
  val¬⟶ (η t)   x = λ { (ξ-η p) → val¬⟶ t x p }
  val¬⟶ (inl t) x = λ { (ξ-inl p) → val¬⟶ t x p }
  val¬⟶ (inr t) x = λ { (ξ-inr p) → val¬⟶ t x p }

  open import Data.Sum using (_⊎_)
    renaming (inj₁ to done ; inj₂ to step)

  Progress : Term a Γ → Set
  Progress t = (isValue t) ⊎ (∃ λ t' → t ⟶ t')

  -- a closed term makes progress
  progress : (t : Term a Ø) → Progress t
  progress unit     = done tt
  progress (`λ t)   = done tt
  progress (var ())
  progress (t ∙ u) with progress t
  progress (`λ t ∙ u) | done v with progress u
  ... | done x = step (subst (Ø `, u) t , red-λ x)
  ... | step (u' , s) = step (`λ t ∙ u' , ξ-∙₂ v s)
  progress (t    ∙ u) | step (t' , s) = step (t' ∙ u , ξ-∙₁ s)
  progress (p ↑ t)  with progress t
  progress (p ↑ η t) | done v = step (η t , red-↑)
  progress (p ↑ t)   | step (t' , s) = step (p ↑ t' , ξ-↑ s)
  progress (η t) with progress t
  progress (η t) | done x = done x
  progress (η t) | step (t' , s)  = step (η t' , ξ-η s)
  progress (t ≫= u) with progress t
  progress (η t ≫= u) | done v = step (subst (Ø `, t) u , red-≫= v)
  progress (t ≫= u) | step (t' , s) = step (t' ≫= u , ξ-≫= s)
  progress (inl t) with progress t
  progress (inl t) | done x        = done x
  progress (inl t) | step (t' , p) = step (inl t' , ξ-inl p)
  progress (inr t) with progress t
  progress (inr t) | done x        = done x
  progress (inr t) | step (t' , p) = step (inr t' , ξ-inr p)
  progress (case t t₁ t₂) with progress t
  progress (case (inl t) t₁ t₂) | done x = step (subst (Ø `, t) t₁ , red-case₁ x)
  progress (case (inr t) t₁ t₂) | done x = step (subst (Ø `, t) t₂ , red-case₂ x)
  progress (case t t₁ t₂)       | step (t' , s) = step (case t' t₁ t₂ , ξ-case s)
