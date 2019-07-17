module Variable where

    open import Type
    open import Embedding
    open import Relation.Binary.PropositionalEquality

    -- De Bruijn index into a context
    data _∈_ : Type → Ctx → Set where
      ze : ∀ {Γ a}   → a ∈ (Γ `, a)
      su : ∀ {Γ a S} → a ∈ Γ → a ∈ (Γ `, S)

    wkenV : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
    wkenV (keep e) ze     = ze
    wkenV (keep e) (su v) = su (wkenV e v)
    wkenV (drop e) v      = su (wkenV e v)

    -- properties
    wkenV-∘ₑ : ∀ {τ} {Γ Δ Σ} → (x : τ ∈ Γ) → (e₁ : Σ ⊆ Δ) (e₂ : Δ ⊆ Γ)
                → wkenV e₁ (wkenV e₂ x) ≡ wkenV (e₂ ∘ₑ e₁) x
    wkenV-∘ₑ ()     base base
    wkenV-∘ₑ ze     (keep e₁) (drop e₂) = cong su (wkenV-∘ₑ ze e₁ e₂)
    wkenV-∘ₑ (su x) (keep e₁) (drop e₂) = cong su (wkenV-∘ₑ (su x) e₁ e₂)
    wkenV-∘ₑ ze     (drop e₁) (keep e₂) = cong su (wkenV-∘ₑ ze e₁ (keep e₂))
    wkenV-∘ₑ ze     (drop e₁) (drop e₂) = cong su (wkenV-∘ₑ ze e₁ (drop e₂))
    wkenV-∘ₑ (su x) (drop e₁) (keep e₂) = cong su (wkenV-∘ₑ (su x) e₁ (keep e₂))
    wkenV-∘ₑ (su x) (drop e₁) (drop e₂) = cong su (wkenV-∘ₑ (su x) e₁ (drop e₂))
    wkenV-∘ₑ ze     (keep e₁) (keep e₂) = refl
    wkenV-∘ₑ (su x) (keep e₁) (keep e₂) = cong su (wkenV-∘ₑ x e₁ e₂)

    wkenV-idₑ : ∀ {a} {Γ} → (x : a ∈ Γ) → wkenV idₑ x ≡ x
    wkenV-idₑ {a} {.(_ `, a)} ze     = refl
    wkenV-idₑ {a} {.(_ `, _)} (su x) = cong su (wkenV-idₑ x)

