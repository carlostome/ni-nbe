module Term where

  open import Preorder

  open import Type
  open import Variable
  open import Embedding

  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.PropositionalEquality.Extra

  data Term : Type → Ctx → Set where
    unit  : ∀ {Γ} → Term 𝟙 Γ
    `λ    : ∀ {Γ} {a b} → Term b (Γ `, a) → Term (a ⇒ b) Γ
    var   : ∀ {Γ} {a}   → a ∈ Γ → Term a Γ
    _∙_   : ∀ {Γ} {a b} → Term (a ⇒ b) Γ → Term a Γ → Term b Γ
    _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Term (⟨ ℓᴸ ⟩ a) Γ → Term (⟨ ℓᴴ ⟩ a) Γ
    η     : ∀ {ℓ} {Γ} {a}    → Term a Γ → Term (⟨ ℓ ⟩ a) Γ
    _≫=_ : ∀ {ℓ} {Γ} {a b} → Term (⟨ ℓ ⟩ a) Γ → Term (⟨ ℓ ⟩ b) (Γ `, a) → Term (⟨ ℓ ⟩ b) Γ
    inl   : ∀ {Γ} {a b} → Term a Γ → Term (a + b) Γ
    inr   : ∀ {Γ} {a b} → Term b Γ → Term (a + b) Γ
    case  : ∀ {Γ} {a b c} → Term (a + b) Γ → Term c (Γ `, a) → Term c (Γ `, b) → Term c Γ

  wkenTm : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Term a Δ → Term a Γ
  wkenTm e unit = unit
  wkenTm e (`λ t)    = `λ (wkenTm (keep e) t)
  wkenTm e (var x)   = var (wkenV e x)
  wkenTm e (t ∙ t₁)  = wkenTm e t ∙ wkenTm e t₁
  wkenTm e (η t)     = η (wkenTm e t)
  wkenTm e (t ≫= k) = wkenTm e t ≫= wkenTm (keep e) k
  wkenTm e (x ↑ t)   = x ↑ wkenTm e t
  wkenTm e (inl t) = inl (wkenTm e t)
  wkenTm e (inr t) = inr (wkenTm e t)
  wkenTm e (case t t₁ t₂) = case (wkenTm e t) (wkenTm (keep e) t₁) (wkenTm (keep e) t₂)

  wkenTm-∘ₑ : ∀ {a} {Γ Δ Σ} → (t : Term a Γ) → (e₁ : Δ ⊆ Γ) (e₂ : Σ ⊆ Δ)
            → wkenTm e₂ (wkenTm e₁ t) ≡ wkenTm (e₁ ∘ₑ e₂) t
  wkenTm-∘ₑ unit e₁ e₂ = refl
  wkenTm-∘ₑ (`λ t) e₁ e₂     = cong (`λ) (wkenTm-∘ₑ t (keep e₁) (keep e₂))
  wkenTm-∘ₑ (var x) e₁ e₂    = cong var (wkenV-∘ₑ x e₂ e₁)
  wkenTm-∘ₑ (t ∙ t₁) e₁ e₂   = cong₂ _∙_ (wkenTm-∘ₑ t e₁ e₂) (wkenTm-∘ₑ t₁ e₁ e₂)
  wkenTm-∘ₑ (x ↑ t) e₁ e₂    = cong (x ↑_) (wkenTm-∘ₑ t e₁ e₂)
  wkenTm-∘ₑ (η t) e₁ e₂      = cong η (wkenTm-∘ₑ t e₁ e₂)
  wkenTm-∘ₑ (t ≫= t₁) e₁ e₂  = cong₂ _≫=_ (wkenTm-∘ₑ t e₁ e₂) (wkenTm-∘ₑ t₁ (keep e₁) (keep e₂))
  wkenTm-∘ₑ (inl t) e₁ e₂    = cong inl (wkenTm-∘ₑ t e₁ e₂)
  wkenTm-∘ₑ (inr t) e₁ e₂    = cong inr (wkenTm-∘ₑ t e₁ e₂)
  wkenTm-∘ₑ (case t t₁ t₂) e₁ e₂ = cong₃ case (wkenTm-∘ₑ t e₁ e₂) (wkenTm-∘ₑ t₁ (keep e₁) (keep e₂))
                                                                  (wkenTm-∘ₑ t₂ (keep e₁) (keep e₂))

  wkenTm-idₑ : ∀ {a} {Γ} → (t : Term a Γ) → wkenTm idₑ t ≡ t
  wkenTm-idₑ {.𝟙} {Γ} unit         = refl
  wkenTm-idₑ {.(_ ⇒ _)} {Γ} (`λ t) = cong `λ (wkenTm-idₑ t)
  wkenTm-idₑ {a} {Γ} (var x)       = cong var (wkenV-idₑ x)
  wkenTm-idₑ {a} {Γ} (t ∙ u)       = cong₂ _∙_ (wkenTm-idₑ t) (wkenTm-idₑ u)
  wkenTm-idₑ {.(⟨ _ ⟩ _)} {Γ} (x ↑ t) = cong (x ↑_) (wkenTm-idₑ t)
  wkenTm-idₑ {.(⟨ _ ⟩ _)} {Γ} (η t)   = cong η (wkenTm-idₑ t)
  wkenTm-idₑ {.(⟨ _ ⟩ _)} {Γ} (t ≫= f) = cong₂ _≫=_ (wkenTm-idₑ t) (wkenTm-idₑ f)
  wkenTm-idₑ {.(_ + _)} {Γ} (inl t) = cong inl (wkenTm-idₑ t)
  wkenTm-idₑ {.(_ + _)} {Γ} (inr t) = cong inr (wkenTm-idₑ t)
  wkenTm-idₑ {a} {Γ} (case t t₁ t₂) = cong₃ case (wkenTm-idₑ t) (wkenTm-idₑ t₁) (wkenTm-idₑ t₂)
