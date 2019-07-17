module Embedding where

    open import Type
    open import Relation.Binary.PropositionalEquality

    -- Weakening over contexts Γ ⊆ Δ to be read as:
    -- Γ is weaker (contains possibly more types) than Δ
    -- Δ is thinner (contains possibly less types) than Γ
    data _⊆_ : Ctx → Ctx → Set where
      base : Ø ⊆ Ø
      keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
      drop : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ Δ

    -- Weakenings are a preorder relation
    idₑ : ∀ {Γ} → Γ ⊆ Γ
    idₑ {Ø}      = base
    idₑ {Γ `, T} = keep idₑ

    _∘ₑ_ : ∀ {Γ Δ Σ} → Δ ⊆ Γ → Σ ⊆ Δ → Σ ⊆ Γ
    e₁ ∘ₑ base    = e₁
    keep e₁ ∘ₑ keep e₂ = keep (e₁ ∘ₑ e₂)
    drop e₁ ∘ₑ keep e₂ = drop (e₁ ∘ₑ e₂)
    e₁ ∘ₑ drop e₂      = drop (e₁ ∘ₑ e₂)

    -- Properties of weakenings
    idlₑ : ∀ {Γ Δ} → (e : Γ ⊆ Δ) → idₑ ∘ₑ e ≡ e
    idlₑ base     = refl
    idlₑ (drop e) = cong drop (idlₑ e)
    idlₑ (keep e) = cong keep (idlₑ e)

    idrₑ : ∀ {Γ Δ} → (e : Γ ⊆ Δ) → e ∘ₑ idₑ ≡ e
    idrₑ base     = refl
    idrₑ (drop e) = cong drop (idrₑ e)
    idrₑ (keep e) = cong keep (idrₑ e)

    assₑ : ∀ {Γ Δ Σ Ξ} → (e₁ : Δ ⊆ Γ) (e₂ : Σ ⊆ Δ) (e₃ : Ξ ⊆ Σ)
         → (e₁ ∘ₑ e₂) ∘ₑ e₃ ≡ e₁ ∘ₑ (e₂ ∘ₑ e₃)
    assₑ e₁        e₂        base      = refl
    assₑ e₁        e₂        (drop e₃) = cong drop (assₑ e₁ e₂ e₃)
    assₑ e₁        (drop e₂) (keep e₃) = cong drop (assₑ e₁ e₂ e₃)
    assₑ (drop e₁) (keep e₂) (keep e₃) = cong drop (assₑ e₁ e₂ e₃)
    assₑ (keep e₁) (keep e₂) (keep e₃) = cong keep (assₑ e₁ e₂ e₃)
