{-# OPTIONS --allow-unsolved-metas #-}
module Substitution where

  open import Type
  open import Term
  open import Embedding
  open import Variable

  open import Relation.Binary.PropositionalEquality hiding (subst)
  open import Relation.Binary.PropositionalEquality.Extra

  infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

  data Sub (Γ : Ctx) : Ctx → Set where
    Ø    : Sub Γ Ø
    _`,_ : ∀ {a Δ} → Sub Γ Δ → Term a Γ → Sub Γ (Δ `, a)

  _ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Γ ⊆ Δ → Sub Γ Σ
  Ø        ₛ∘ₑ δ = Ø
  (s `, t) ₛ∘ₑ δ = (s ₛ∘ₑ δ) `, wkenTm δ t

  _ₑ∘ₛ_ : ∀ {Γ Δ Σ} → Δ ⊆ Σ → Sub Γ Δ → Sub Γ Σ
  base   ₑ∘ₛ s        = s
  keep e ₑ∘ₛ (s `, t) = (e ₑ∘ₛ s) `, t
  drop e ₑ∘ₛ (s `, t) = e ₑ∘ₛ s

  dropˢ : ∀ {a Γ Δ} → Sub Γ Δ → Sub (Γ `, a) Δ
  dropˢ σ = σ ₛ∘ₑ drop idₑ

  keepˢ : ∀ {Γ Δ} {a} → Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
  keepˢ σ = dropˢ σ `, var ze

  ⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → Γ ⊆ Δ → Sub Γ Δ
  ⌜ base   ⌝ᵒᵖᵉ = Ø
  ⌜ drop σ ⌝ᵒᵖᵉ = dropˢ ⌜ σ ⌝ᵒᵖᵉ
  ⌜ keep σ ⌝ᵒᵖᵉ = keepˢ ⌜ σ ⌝ᵒᵖᵉ

  -- Action on ∈ and Tm
  ∈ₛ : ∀ {Γ Δ} {a} → Sub Γ Δ → a ∈ Δ → Term a Γ
  ∈ₛ (s `, t) ze     = t
  ∈ₛ (s `, x) (su e) = ∈ₛ s e

  subst : ∀ {Γ Δ} {a} → Sub Γ Δ → Term a Δ → Term a Γ
  subst s unit = unit
  subst s (`λ t) = `λ (subst (keepˢ s) t)
  subst s (var x)  = ∈ₛ s x
  subst s (t ∙ u)  = subst s t ∙ subst s u
  subst s (c ↑ t)  = c ↑ subst s t
  subst s (η t)    = η (subst s t)
  subst s (m ≫= f) = (subst s m) ≫= subst (keepˢ s) f
  subst s (inl t) = inl (subst s t)
  subst s (inr t) = inr (subst s t)
  subst s (case t t₁ t₂) = case (subst s t) (subst (keepˢ s) t₁) (subst (keepˢ s) t₂)

  -- Identity and composition
  idₛ : ∀ {Γ} → Sub Γ Γ
  idₛ {Ø}      = Ø
  idₛ {Γ `, a} = keepˢ idₛ

  _∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  Ø       ∘ₛ δ  = Ø
  (s `, t) ∘ₛ δ = (s ∘ₛ δ) `, subst δ t

  idlₛ : ∀ {Γ Δ} → (σ : Sub Γ Δ) → idₛ ∘ₛ σ ≡ σ
  idlₛ Ø        = refl
  idlₛ (σ `, x) = {!!}

  idrₛ : ∀ {Γ Δ} → (σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
  idrₛ = {!!}

  assₛ : ∀ {Γ Δ Σ Ξ} → (σ₁ : Sub Δ Γ) (σ₂ : Sub Σ Δ) (σ₃ : Sub Ξ Σ)
      → (σ₁ ∘ₛ σ₂) ∘ₛ σ₃ ≡ σ₁ ∘ₛ (σ₂ ∘ₛ σ₃)
  assₛ = {!!}

  subst-idₛ : ∀ {a} {Γ} → (t : Term a Γ)→ subst idₛ t ≡ t
  subst-idₛ t = {!!}

  assₛₑₑ : ∀ {Γ Δ Σ Ξ} (σ : Sub Δ Γ) (e₁ : Σ ⊆ Δ) (e₂ : Ξ ⊆ Σ)
        → (σ ₛ∘ₑ e₁) ₛ∘ₑ e₂ ≡ σ ₛ∘ₑ (e₁ ∘ₑ e₂)
  assₛₑₑ Ø e₁ e₂        = refl
  assₛₑₑ (σ `, x) e₁ e₂ = cong₂ _`,_ (assₛₑₑ σ e₁ e₂) (wkenTm-∘ₑ x e₁ e₂)

  assₑₛₑ : ∀ {Γ Δ Σ Ξ} (σ : Sub Δ Γ) (e₁ : Γ ⊆ Σ) (e₂ : Ξ ⊆ Δ)
        → (e₁ ₑ∘ₛ σ) ₛ∘ₑ e₂ ≡ e₁ ₑ∘ₛ (σ ₛ∘ₑ e₂)
  assₑₛₑ Ø base e₂             = refl
  assₑₛₑ (σ `, x) (keep e₁) e₂ = cong (_`, wkenTm e₂ x) (assₑₛₑ σ e₁ e₂)
  assₑₛₑ (σ `, x) (drop e₁) e₂ = assₑₛₑ σ e₁ e₂

  assₛₑₛ  : ∀ {Γ Δ Σ Ξ} (σ₁ : Sub Δ Γ) (σ₂ : Sub Ξ Σ) (e : Σ ⊆ Δ)
         → (σ₁ ₛ∘ₑ e) ∘ₛ σ₂ ≡ σ₁ ∘ₛ (e ₑ∘ₛ σ₂)

  assₛₑₛ  = ?
  ∈ₛ-ₛ∘ₑ : ∀ {τ} {Γ Δ Σ} → (x : τ ∈ Γ) → (σ : Sub Δ Γ) → (e : Σ ⊆ Δ)
        → ∈ₛ (σ ₛ∘ₑ e) x ≡ wkenTm e (∈ₛ σ x)
  ∈ₛ-ₛ∘ₑ ze (σ `, t) e     = refl
  ∈ₛ-ₛ∘ₑ (su x) (σ `, t) e = ∈ₛ-ₛ∘ₑ x σ e

  ∈ₛ-ₑ∘ₛ : ∀ {τ} {Γ Δ Σ} → (x : τ ∈ Γ) → (σ : Sub Σ Δ) → (e : Δ ⊆ Γ)
        → ∈ₛ (e ₑ∘ₛ σ) x ≡ ∈ₛ σ (wkenV e x)
  ∈ₛ-ₑ∘ₛ x      (σ `, t) (drop e) = {!!} -- ∈ₛ-ₑ∘ₛ x σ e
  ∈ₛ-ₑ∘ₛ ze     (σ `, t) (keep e) = refl
  ∈ₛ-ₑ∘ₛ (su x) (σ `, t) (keep e) = ∈ₛ-ₑ∘ₛ x σ e

  private
    lemma : ∀ {τ} {Γ Δ Σ} → (σ : Sub Δ Γ) (e : Σ ⊆ Δ)
          → dropˢ {τ} (σ ₛ∘ₑ e) ≡ (dropˢ σ ₛ∘ₑ keep e)
    lemma σ e = trans (assₛₑₑ σ e (drop idₑ)) (trans (cong (σ ₛ∘ₑ_)
                      (cong drop (trans (idrₑ e) (sym (idlₑ e)))))
                      (sym (assₛₑₑ σ (drop idₑ) (keep e))))

  Term-ₛ∘ₑ : ∀ {τ} {Γ Δ Σ} → (t : Term τ Γ) (σ : Sub Δ Γ) (e : Σ ⊆ Δ)
          → subst (σ ₛ∘ₑ e) t ≡ wkenTm e (subst σ t)
  Term-ₛ∘ₑ unit σ e = refl
  Term-ₛ∘ₑ {τ} {Γ} {Δ} {Σ} (`λ t) σ e =
    cong `λ (trans (cong (λ s → subst (s `, var ze) t) (lemma σ e))
            (Term-ₛ∘ₑ t (keepˢ σ) (keep e)))
  Term-ₛ∘ₑ (var x) σ e  = (∈ₛ-ₛ∘ₑ x σ e)
  Term-ₛ∘ₑ (t ∙ t₁) σ e = cong₂ _∙_ (Term-ₛ∘ₑ t σ e) (Term-ₛ∘ₑ t₁ σ e)
  Term-ₛ∘ₑ (x ↑ t) σ e  = cong (x ↑_) (Term-ₛ∘ₑ t σ e)
  Term-ₛ∘ₑ (η t) σ e    = cong η (Term-ₛ∘ₑ t σ e)
  Term-ₛ∘ₑ (t ≫= t₁) σ e =
    cong₂ _≫=_ (Term-ₛ∘ₑ t σ e)
                (trans (cong (λ s → subst (s `, var ze) t₁) (lemma σ e))
                        (Term-ₛ∘ₑ t₁ (keepˢ σ) (keep e)))
  Term-ₛ∘ₑ (inl t) σ e = cong inl (Term-ₛ∘ₑ t σ e)
  Term-ₛ∘ₑ (inr t) σ e = cong inr (Term-ₛ∘ₑ t σ e)
  Term-ₛ∘ₑ (case t t₁ t₂) σ e =
    cong₃ case (Term-ₛ∘ₑ t σ e)
                ((trans (cong (λ s → subst (s `, var ze) t₁) (lemma σ e))
                        (Term-ₛ∘ₑ t₁ (keepˢ σ) (keep e))))
                ((trans (cong (λ s → subst (s `, var ze) t₂) (lemma σ e))
                        (Term-ₛ∘ₑ t₂ (keepˢ σ) (keep e))))

  Term-ₑ∘ₛ : ∀ {τ} {Γ Δ Σ} → (t : Term τ Γ) (σ : Sub Σ Δ) (e : Δ ⊆ Γ)
          → subst (e ₑ∘ₛ σ) t ≡ subst σ (wkenTm e t)
  Term-ₑ∘ₛ unit σ e    = refl
  Term-ₑ∘ₛ (`λ t) σ e  = cong `λ
    (trans (cong (λ s → subst (s `, var ze) t) (assₑₛₑ σ e (drop idₑ)))
              (Term-ₑ∘ₛ t (keepˢ σ) (keep e)))
  Term-ₑ∘ₛ (var x) σ e  = ∈ₛ-ₑ∘ₛ x σ e
  Term-ₑ∘ₛ (t ∙ t₁) σ e = cong₂ _∙_ (Term-ₑ∘ₛ t σ e) (Term-ₑ∘ₛ t₁ σ e)
  Term-ₑ∘ₛ (x ↑ t) σ e  = cong (x ↑_) (Term-ₑ∘ₛ t σ e)
  Term-ₑ∘ₛ (η t) σ e    = cong η (Term-ₑ∘ₛ t σ e)
  Term-ₑ∘ₛ (t ≫= t₁) σ e = cong₂ _≫=_
    (Term-ₑ∘ₛ t σ e) (trans (cong (λ s → subst (s `, var ze) t₁) (assₑₛₑ σ e (drop idₑ)))
                    (Term-ₑ∘ₛ t₁ (keepˢ σ) (keep e)))
  Term-ₑ∘ₛ (inl t) σ e = cong inl (Term-ₑ∘ₛ t σ e)
  Term-ₑ∘ₛ (inr t) σ e = cong inr (Term-ₑ∘ₛ t σ e)
  Term-ₑ∘ₛ (case t t₁ t₂) σ e = cong₃ case (Term-ₑ∘ₛ t σ e)
    (trans (cong (λ s → subst (s `, var ze) t₁) (assₑₛₑ σ e (drop idₑ)))
            (Term-ₑ∘ₛ t₁ (keepˢ σ) (keep e)))
    (trans (cong (λ s → subst (s `, var ze) t₂) (assₑₛₑ σ e (drop idₑ)))
            (Term-ₑ∘ₛ t₂ (keepˢ σ) (keep e)))

  idlₑₛ : ∀ {Γ Δ} → (σ : Sub Δ Γ) → idₑ ₑ∘ₛ σ ≡ σ
  idlₑₛ Ø        = refl
  idlₑₛ (σ `, x) = cong (_`, x) (idlₑₛ σ)

  idlₛₑ : ∀ {Γ Δ} → (e : Δ ⊆ Γ) → (idₛ ₛ∘ₑ e) ≡ ⌜ e ⌝ᵒᵖᵉ
  idlₛₑ base     = refl
  idlₛₑ (keep e) =
    cong (_`, var ze)
          (trans (assₛₑₑ idₛ (drop idₑ) (keep e))
                  (trans (cong (λ e → (idₛ ₛ∘ₑ drop e)) (trans (idlₑ e)
                                                                (sym (idrₑ e))))
                            (trans (sym (assₛₑₑ idₛ e (drop idₑ)))
                                    (cong (_ₛ∘ₑ drop idₑ) (idlₛₑ e)) )))
  idlₛₑ (drop e) =
    trans (cong (λ e → idₛ ₛ∘ₑ drop e)
                (sym (idrₑ e)))
          (trans (sym (assₛₑₑ idₛ e (drop idₑ)))
                    (cong dropˢ (idlₛₑ e)))

  idrₛₑ : ∀ {Γ Δ} → (e : Δ ⊆ Γ) → (e ₑ∘ₛ idₛ) ≡ ⌜ e ⌝ᵒᵖᵉ
  idrₛₑ base     = refl
  idrₛₑ (keep e) = {!!}
  idrₛₑ (drop e) = {!!}

  Term-∘ₛ : ∀ {a} {Γ Δ Σ} → (t : Term a Γ) → (σ₁ : Sub Δ Γ) → (σ₂ : Sub Σ Δ)
          → subst (σ₁ ∘ₛ σ₂) t ≡ subst σ₂ (subst σ₁ t)
  Term-∘ₛ = {!!}
