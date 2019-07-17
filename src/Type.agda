module Type where

  open import Preorder

  data Type  : Set where
    𝟙     : Type
    𝕓     : Type
    _⇒_   : (a b : Type)  → Type
    _+_   : (a b : Type)  → Type
    ⟨_⟩_   : (ℓ : Label) (a : Type) → Type

  infixr 10 _⇒_

  -- Ctx as a snoc list of types
  data Ctx : Set where
    Ø    : Ctx
    _`,_ : Ctx → Type → Ctx
