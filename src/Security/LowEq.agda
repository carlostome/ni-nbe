module Security.LowEq where

  open import Preorder

  open import Type
  open import Embedding
  open import Variable
  open import Term
  open import Substitution
  open import Relation.Nullary
  open import Data.Bool
  open import Data.Empty

  open import Function using (_∋_)

  data _≡〈_〉_ {Γ} : ∀ {a} → Term a Γ → Label → Term a Γ → Set where

    unit : ∀ {ℓ}     → unit ≡〈 ℓ 〉 unit

    var  : ∀ {ℓ} {a} → (x : a ∈ Γ) → var x ≡〈 ℓ 〉 var x

    _∙_ : ∀ {ℓ} {a b} {f f′ : Term (a ⇒ b) Γ} {u u′ : Term a Γ}
        → f ≡〈 ℓ 〉 f′
        → u ≡〈 ℓ 〉 u′
        → (f ∙ u) ≡〈 ℓ 〉 (f′ ∙ u′)

    `λ : ∀ {ℓ} {a b} {t u : Term a (Γ `, b)}
       → t ≡〈 ℓ 〉 u
       → `λ t ≡〈 ℓ 〉 `λ u

    -- ⟨⟩/ congruence
    ηᴸ    : ∀ {ℓ} {a} {ℓ′} → {t₁ t₂ : Term a Γ}
          → ℓ′ ⊑ ℓ
          → t₁ ≡〈 ℓ 〉 t₂
          → η {ℓ = ℓ′} t₁ ≡〈 ℓ 〉 η t₂

    ηᴴ〈_〉    : ∀ {ℓ} {a} {ℓ′} → {t : Term a Γ} {u : Term (⟨ ℓ′ ⟩ a) Γ}
          → ¬ (ℓ′ ⊑ ℓ)
          → η {ℓ = ℓ′} t ≡〈 ℓ 〉 u

    _≫=ᴸ〈_〉_   : ∀ {ℓ} {a b } {ℓ′} → {t₁ t₂ : Term (⟨ ℓ′ ⟩ a) Γ} {t₃ t₄ : Term (⟨ ℓ′ ⟩ b) (Γ `, a) }
                 → t₁ ≡〈 ℓ 〉 t₂
                 → ℓ′ ⊑ ℓ
                 → t₃ ≡〈 ℓ 〉 t₄
                 → (t₁ ≫= t₃) ≡〈 ℓ 〉 (t₂ ≫= t₄)

    ≫=ᴴ〈_〉  : ∀ {ℓ} {a b } {ℓ′} → {t₁ : Term (⟨ ℓ′ ⟩ a) Γ} {t₂ : Term (⟨ ℓ′ ⟩ b) (Γ `, a) } {u : Term (⟨ ℓ′ ⟩ b) Γ}
            → ¬ (ℓ′ ⊑ ℓ)
            → (t₁ ≫= t₂) ≡〈 ℓ 〉 u

    _↑〈_〉_   : ∀ {ℓ} {a} {ℓᴸ ℓᴴ} (c : ℓᴸ ⊑ ℓᴴ) {t₁ t₂ : Term (⟨ ℓᴸ ⟩ a) Γ}
            → ℓᴴ ⊑ ℓ
            → t₁ ≡〈 ℓ 〉 t₂
            → (c ↑ t₁) ≡〈 ℓ 〉 (c ↑ t₂)

    _↑〈_〉    : ∀ {ℓ} {a} {ℓᴸ ℓᴴ} (c : ℓᴸ ⊑ ℓᴴ) {t : Term (⟨ ℓᴸ ⟩ a) Γ} {u : Term (⟨ ℓᴴ ⟩ a) Γ}
            → ¬ (ℓᴴ ⊑ ℓ)
            → (c ↑ t) ≡〈 ℓ 〉 u

    -- +/ congruence
    inl     : ∀ {ℓ} {a b} → {t₁ t₂ : Term a Γ}
            → t₁ ≡〈 ℓ 〉 t₂
            → (Term (a + b) Γ ∋ inl t₁) ≡〈 ℓ 〉 (inl t₂)

    inr     : ∀ {ℓ} {a b} → {t₁ t₂ : Term b Γ}
            → t₁ ≡〈 ℓ 〉 t₂
            → (Term (a + b) Γ ∋ inr t₁) ≡〈 ℓ 〉  (inr t₂)

    case    : ∀ {ℓ} {a b c} {t₁ t₂ : Term (a + b) Γ}
                        {c₁ c₂ : Term c (Γ `, a)}
                        {c₃ c₄ : Term c (Γ `, b)}
            → t₁ ≡〈 ℓ 〉 t₂
            → c₁ ≡〈 ℓ 〉 c₂
            → c₃ ≡〈 ℓ 〉 c₄
            → case t₁ c₁ c₃ ≡〈 ℓ 〉 case t₂ c₂ c₄


    ≡〈〉-sym   : ∀ {ℓ} {a} {t u : Term a Γ} → t ≡〈 ℓ 〉 u → u ≡〈 ℓ 〉 t
    ≡〈〉-trans : ∀ {ℓ} {a} {t u v : Term a Γ} → t ≡〈 ℓ 〉 u → u ≡〈 ℓ 〉 v → t ≡〈 ℓ 〉 v

  ≡〈〉-refl  : ∀ {ℓ} {Γ} {a} {t : Term a Γ} → t ≡〈 ℓ 〉 t
  ≡〈〉-refl {ℓ} {t = unit}  = unit
  ≡〈〉-refl {ℓ} {t = `λ t}  = `λ ≡〈〉-refl
  ≡〈〉-refl {ℓ} {t = var x} = var x
  ≡〈〉-refl {ℓ} {t = t ∙ u} = ≡〈〉-refl ∙ ≡〈〉-refl
  ≡〈〉-refl {ℓ} {t = _↑_ {ℓᴴ = ℓᴴ} x t} with ⊑-dec ℓᴴ ℓ
  ≡〈〉-refl {ℓ} {_} {_} {_↑_ {ℓᴴ = ℓᴴ} x t} | yes p = x ↑〈 p 〉 ≡〈〉-refl
  ≡〈〉-refl {ℓ} {_} {_} {_↑_ {ℓᴴ = ℓᴴ} x t} | no ¬p = x ↑〈 ¬p 〉 
  ≡〈〉-refl {ℓ} {t = η {ℓ′} t} with ⊑-dec ℓ′ ℓ
  ≡〈〉-refl {ℓ} {_} {_} {η {ℓ′} t} | no ¬p = ηᴴ〈 ¬p 〉
  ≡〈〉-refl {ℓ} {_} {_} {η {ℓ′} t} | yes p = ηᴸ p ≡〈〉-refl
  ≡〈〉-refl {ℓ} {t = _≫=_ {ℓ′} t u} with ⊑-dec ℓ′ ℓ
  ≡〈〉-refl {ℓ} {_} {_} {_≫=_ {ℓ′} t u} | yes p = ≡〈〉-refl ≫=ᴸ〈 p 〉 ≡〈〉-refl
  ≡〈〉-refl {ℓ} {_} {_} {_≫=_ {ℓ′} t u} | no ¬p = ≫=ᴴ〈 ¬p 〉
  ≡〈〉-refl {ℓ} {t = inl t} = inl ≡〈〉-refl
  ≡〈〉-refl {ℓ} {t = inr t} = inr ≡〈〉-refl
  ≡〈〉-refl {ℓ} {t = case t t₁ t₂} = case ≡〈〉-refl ≡〈〉-refl ≡〈〉-refl


  -- ≡〈〉-trans : ∀ {ℓ} {Γ} {a} {t u v : Term a Γ} → t ≡〈 ℓ 〉 u → u ≡〈 ℓ 〉 v → t ≡〈 ℓ 〉 v
  -- ≡〈〉-trans unit unit = unit
  -- ≡〈〉-trans unit (≡〈〉-sym y)  = ≡〈〉-sym y
  -- ≡〈〉-trans (var x) (var .x) = var x
  -- ≡〈〉-trans (var x) (≡〈〉-sym y) = ≡〈〉-sym y
  -- ≡〈〉-trans (x ∙ x₁) (y ∙ y₁)  = ≡〈〉-trans x y ∙ ≡〈〉-trans x₁ y₁
  -- ≡〈〉-trans (x ∙ x₁) (≡〈〉-sym (y ∙ y₁))  = ≡〈〉-trans x (≡〈〉-sym y) ∙ ≡〈〉-trans x₁ (≡〈〉-sym y₁)
  -- ≡〈〉-trans (x ∙ x₁) (≡〈〉-sym ηᴴ〈 x₂ 〉)   = ≡〈〉-sym ηᴴ〈 x₂ 〉
  -- ≡〈〉-trans (x ∙ x₁) (≡〈〉-sym ≫=ᴴ〈 x₂ 〉) = ≡〈〉-sym ≫=ᴴ〈 x₂ 〉
  -- ≡〈〉-trans (x ∙ x₁) (≡〈〉-sym (c ↑〈 x₂ 〉)) = ≡〈〉-sym (c ↑〈 x₂ 〉)
  -- ≡〈〉-trans (x ∙ x₁) (≡〈〉-sym (≡〈〉-sym y)) = ≡〈〉-trans (x ∙ x₁) y
  -- ≡〈〉-trans (`λ x) (`λ y) = `λ (≡〈〉-trans x y)
  -- ≡〈〉-trans (`λ x) (≡〈〉-sym (`λ y))     = `λ (≡〈〉-trans x (≡〈〉-sym y))
  -- ≡〈〉-trans (`λ x) (≡〈〉-sym (≡〈〉-sym y)) = ≡〈〉-trans (`λ x) y
  -- ≡〈〉-trans (ηᴸ p x) (ηᴸ p′ y) = ηᴸ p′ (≡〈〉-trans x y)
  -- ≡〈〉-trans (ηᴸ p _) ηᴴ〈 ¬p 〉   = ⊥-elim (¬p p)
  -- ≡〈〉-trans (ηᴸ p x) (≡〈〉-sym (ηᴸ p′ y)) = ηᴸ p′ (≡〈〉-trans x (≡〈〉-sym y))
  -- ≡〈〉-trans (ηᴸ p _) (≡〈〉-sym ηᴴ〈 ¬p 〉)   = ⊥-elim (¬p p)
  -- ≡〈〉-trans (ηᴸ p _) (≡〈〉-sym ≫=ᴴ〈 ¬p 〉)  = ⊥-elim (¬p p) 
  -- ≡〈〉-trans (ηᴸ p _) (≡〈〉-sym (c ↑〈 ¬p 〉)) = ⊥-elim (¬p p)
  -- ≡〈〉-trans (ηᴸ x x₁) (≡〈〉-sym (≡〈〉-sym y)) = ≡〈〉-trans (ηᴸ x x₁) y
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (var _) = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (_ ∙ _) = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (ηᴸ p y) = ⊥-elim (¬p p)
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 ηᴴ〈 _ 〉 = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (_ ≫=ᴸ〈 p 〉 _) = ⊥-elim (¬p p)
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 ≫=ᴴ〈 _ 〉 = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (c ↑〈 p 〉 y) = ⊥-elim (¬p p)
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (c ↑〈 _ 〉)   = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (case _ _ _) = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans ηᴴ〈 ¬p 〉 (≡〈〉-sym y)   = ηᴴ〈 ¬p 〉
  -- ≡〈〉-trans (t ≫=ᴸ〈 p 〉 u) (x ≫=ᴸ〈 _ 〉 y) = ≡〈〉-trans t x ≫=ᴸ〈 p 〉 ≡〈〉-trans u y
  -- ≡〈〉-trans (_ ≫=ᴸ〈 p 〉 _) ≫=ᴴ〈 ¬p 〉  = ⊥-elim (¬p p)
  -- ≡〈〉-trans (t ≫=ᴸ〈 p 〉 u) (≡〈〉-sym ηᴴ〈 ¬p 〉) = {!!}
  -- ≡〈〉-trans (t ≫=ᴸ〈 p 〉 u) (≡〈〉-sym (y ≫=ᴸ〈 x 〉 y₁)) = {!!}
  -- ≡〈〉-trans (t ≫=ᴸ〈 p 〉 u) (≡〈〉-sym ≫=ᴴ〈 x 〉) = {!!}
  -- ≡〈〉-trans (t ≫=ᴸ〈 p 〉 u) (≡〈〉-sym (c ↑〈 x 〉)) = {!!}
  -- ≡〈〉-trans (t ≫=ᴸ〈 p 〉 u) (≡〈〉-sym (≡〈〉-sym y)) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (var x₁) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (y ∙ y₁) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (ηᴸ x₁ y) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 ηᴴ〈 x₁ 〉 = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (y ≫=ᴸ〈 x₁ 〉 y₁) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 ≫=ᴴ〈 x₁ 〉 = ≫=ᴴ〈 x₁ 〉
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (c ↑〈 x₁ 〉 y) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (c ↑〈 x₁ 〉) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (case y y₁ y₂) = {!!}
  -- ≡〈〉-trans ≫=ᴴ〈 x 〉 (≡〈〉-sym y) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉 x₁) (.c ↑〈 x₂ 〉 y) = c ↑〈 x₂ 〉 ≡〈〉-trans x₁ y
  -- ≡〈〉-trans (c ↑〈 x 〉 x₁) (.c ↑〈 x₂ 〉)   = c ↑〈 x₂ 〉
  -- ≡〈〉-trans (c ↑〈 x 〉 x₁) (≡〈〉-sym y) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (var x₁) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (y ∙ y₁) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (ηᴸ x₁ y) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) ηᴴ〈 x₁ 〉 = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (y ≫=ᴸ〈 x₁ 〉 y₁) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) ≫=ᴴ〈 x₁ 〉 = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (c₁ ↑〈 x₁ 〉 y) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (c₁ ↑〈 x₁ 〉) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (case y y₁ y₂) = {!!}
  -- ≡〈〉-trans (c ↑〈 x 〉) (≡〈〉-sym y) = {!!}
  -- ≡〈〉-trans (inl x) (inl y) = inl (≡〈〉-trans x y)
  -- ≡〈〉-trans (inl x) (≡〈〉-sym y) = {!!}
  -- ≡〈〉-trans (inr x) (inr y) = inr (≡〈〉-trans x y)
  -- ≡〈〉-trans (inr x) (≡〈〉-sym y) = {!!}
  -- ≡〈〉-trans (case x x₁ x₂) (case y y₁ y₂) = case (≡〈〉-trans x y) (≡〈〉-trans x₁ y₁) (≡〈〉-trans x₂ y₂)
  -- ≡〈〉-trans (case x x₁ x₂) (≡〈〉-sym y) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) unit = ≡〈〉-sym x
  -- ≡〈〉-trans (≡〈〉-sym x) (var x₁) = ≡〈〉-sym x
  -- ≡〈〉-trans (≡〈〉-sym x) (y ∙ y₁) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) (`λ y) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) (ηᴸ x₁ y) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) ηᴴ〈 x₁ 〉 = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) (y ≫=ᴸ〈 x₁ 〉 y₁) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) ≫=ᴴ〈 x₁ 〉 = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) (c ↑〈 x₁ 〉 y) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) (c ↑〈 x₁ 〉) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym (inl x)) (inl y)    = inl (≡〈〉-trans (≡〈〉-sym x) y)
  -- ≡〈〉-trans (≡〈〉-sym (≡〈〉-sym x)) (inl y) = ≡〈〉-trans x (inl y)
  -- ≡〈〉-trans (≡〈〉-sym (inr x)) (inr y)    = inr (≡〈〉-trans (≡〈〉-sym x) y)
  -- ≡〈〉-trans (≡〈〉-sym (≡〈〉-sym x)) (inr y) = ≡〈〉-trans x (inr y)
  -- ≡〈〉-trans (≡〈〉-sym x) (case y y₁ y₂) = {!!}
  -- ≡〈〉-trans (≡〈〉-sym x) (≡〈〉-sym y) = ≡〈〉-sym (≡〈〉-trans y x)

  -- low equivalent substitutions
  data _≡ₛ〈_〉_ {Γ}  : ∀ {Δ} → Sub Γ Δ → Label → Sub Γ Δ → Set where
    Ø    : ∀ {ℓ} → Ø ≡ₛ〈 ℓ 〉 Ø
    _`,_ : ∀ {ℓ} {a} {t u : Term a Γ} {Δ} {σ₁ σ₂ : Sub Γ Δ}
         → σ₁ ≡ₛ〈 ℓ 〉 σ₂ → t ≡〈 ℓ 〉 u → (σ₁ `, t) ≡ₛ〈 ℓ 〉 (σ₂ `, u)
