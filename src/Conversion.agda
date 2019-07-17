module Conversion where

  open import Preorder

  open import Type
  open import Term
  open import Variable
  open import Substitution
  open import Embedding

  open import Function using (_∋_)
  open import Relation.Binary.PropositionalEquality hiding (subst)
  open import Relation.Binary.PropositionalEquality.Extra
  data _≈_ {Γ} : ∀ {τ} → Term τ Γ → Term τ Γ → Set where

    -- λ/ reduction
    ⇒β-≈      : ∀ {a b} → {t : Term b (Γ `, a)} {u : Term a Γ}
              → ((`λ t) ∙ u) ≈ subst (idₛ `, u) t

    ⇒η-≈      : ∀ {a b} → {t : Term (a ⇒ b) Γ}
              → t  ≈ `λ (wkenTm (drop idₑ) t ∙ (var ze))

    -- λ/ congruence
    ∙-≈ : ∀ {a b} {f f′ : Term (a ⇒ b) Γ} {u u′ : Term a Γ}
        → f ≈ f′
        → u ≈ u′
        → (f ∙ u) ≈ (f′ ∙ u′)

    λ-≈ : ∀ {a b} {t t′ : Term a (Γ `, b)}
        → t ≈ t′
        → (`λ t) ≈ (`λ t′)

    -- Monad laws
    ⟨⟩β-≈     : ∀ {a b} {ℓ} → {x : Term a Γ} {f : Term (⟨ ℓ ⟩ b) (Γ `, a)}
              → (η x ≫= f) ≈ subst (idₛ `, x) f

    ⟨⟩η-≈     : ∀ {a} {ℓ} → {t : Term (⟨ ℓ ⟩ a) Γ}
              → t ≈ (t ≫= η (var ze))

    ⟨⟩γ-≈     : ∀ {a b c} {ℓ} → {t₁ : Term (⟨ ℓ ⟩ a) Γ}
                                {t₂ : Term (⟨ ℓ ⟩ b) (Γ `, a)}
                                {t₃ : Term (⟨ ℓ ⟩ c) (Γ `, b)}
              → ((t₁ ≫= t₂) ≫= t₃) ≈ (t₁ ≫= (t₂ ≫= wkenTm (keep (drop idₑ)) t₃))

    -- Up laws

    ↑γ₁-≈ : ∀ {a} {ℓᴸ ℓᴴ} → {t : Term a Γ} {p : ℓᴸ ⊑ ℓᴴ}
              → (p ↑ η t) ≈ η t
    ↑γ₂-≈ : ∀ {a b} {ℓᴸ ℓᴴ} → {t₁ : Term (⟨ ℓᴸ ⟩ a) Γ} {t₂ : Term (⟨ ℓᴸ ⟩ (⟨ ℓᴸ ⟩ b)) (Γ `, a)}
                              {p : ℓᴸ ⊑ ℓᴴ} 
              → (p ↑ (t₁ ≫= t₂)) ≈ ((p ↑ t₁) ≫= (p ↑ t₂))


    -- ⟨⟩/ congruence
    η-≈     : ∀ {a} {ℓ} → {t₁ t₂ : Term a Γ}
            → t₁ ≈ t₂
            → η {ℓ = ℓ} t₁ ≈ η t₂

    ≫=-≈   : ∀ {a b } {ℓ} → {t₁ t₂ : Term (⟨ ℓ ⟩ a) Γ} {t₃ t₄ : Term (⟨ ℓ ⟩ b) (Γ `, a) }
            → t₁ ≈ t₂
            → t₃ ≈ t₄
            → (t₁ ≫= t₃) ≈ (t₂ ≫= t₄)

    ↑-≈     : ∀ {a} {ℓᴸ ℓᴴ} {c : ℓᴸ ⊑ ℓᴴ} → {t₁ t₂ : Term (⟨ ℓᴸ ⟩ a) Γ}
            → t₁ ≈ t₂
            → (c ↑ t₁) ≈ (c ↑ t₂)

    -- +/ congruence
    inl-≈     : ∀ {a b} → {t₁ t₂ : Term a Γ}
              → t₁ ≈ t₂
              → (Term (a + b) Γ ∋ inl t₁) ≈ (inl t₂)

    inr-≈     : ∀ {a b} → {t₁ t₂ : Term b Γ}
              → t₁ ≈ t₂
              → (Term (a + b) Γ ∋ inr t₁) ≈ (inr t₂)

    case-≈     : ∀ {a b c} {t₁ t₂ : Term (a + b) Γ}
                            {c₁ c₂ : Term c (Γ `, a)}
                            {c₃ c₄ : Term c (Γ `, b)}
                → t₁ ≈ t₂
                → c₁ ≈ c₂
                → c₃ ≈ c₄
                → case t₁ c₁ c₃ ≈ case t₂ c₂ c₄

    -- equivalence relation
    ≈-refl  : ∀ {a} {t : Term a Γ}                  → t ≈ t
    ≈-sym   : ∀ {a} {t t′ : Term a Γ}               → t ≈ t′ → t′ ≈ t
    ≈-trans : ∀ {a} {t t′ t′′ : Term a Γ}           → t ≈ t′ → t′ ≈ t′′ → t ≈ t′′

  ≡⇒≈ : ∀ {a} {Γ} {t₁ t₂ : Term a Γ} → t₁ ≡ t₂ → t₁ ≈ t₂
  ≡⇒≈ refl = ≈-refl

  postulate
    inv-subst : ∀ {Γ Δ} {a} {σ : Sub Δ Γ} → {t₁ t₂ : Term a Γ} → t₁ ≈ t₂ → subst σ t₁ ≈  subst σ t₂

  -- weakening preserves ≈
  inv-wken : ∀ {a} {Γ} {t₁ t₂ : Term a Γ}
                {Δ : Ctx} {e : Δ ⊆ Γ}
            → t₁ ≈ t₂
            → wkenTm e t₁ ≈ wkenTm e t₂
  inv-wken {e = e} (⇒β-≈ {t = t} {u = u})
    = ≈-trans ⇒β-≈ (≡⇒≈ (trans (trans (sym (Term-ₑ∘ₛ t (idₛ `, wkenTm e u) (keep e)))
                                          (cong (λ s → subst (s `, wkenTm e u) t)
                                                (trans (idrₛₑ e) (sym (idlₛₑ e)))))
                      (Term-ₛ∘ₑ t (idₛ `, u) e)))
  inv-wken {e = e} (⇒η-≈ {t = t₁})
    = ≈-trans ⇒η-≈ (≡⇒≈ (cong (λ f → `λ (f ∙ var ze))
                              (trans (wkenTm-∘ₑ t₁ e (drop idₑ))
                              (trans ((cong (λ e → wkenTm (drop e) t₁)
                                              (trans (idrₑ e) (sym (idlₑ e)))))
                                        (sym (wkenTm-∘ₑ t₁ (drop idₑ) (keep e)))))))
  inv-wken (∙-≈ x x₁) = ∙-≈ (inv-wken x) (inv-wken x₁)
  inv-wken (λ-≈ x)    = λ-≈ (inv-wken x)
  inv-wken {e = e} (⟨⟩β-≈ {x = x} {f = f})
    = ≈-trans ⟨⟩β-≈ (≡⇒≈ (trans (trans (sym (Term-ₑ∘ₛ f (idₛ `, wkenTm e x) (keep e)))
                                          (cong (λ s → subst (s `, wkenTm e x) f)
                                                (trans (idrₛₑ e) (sym (idlₛₑ e)))))
                        (Term-ₛ∘ₑ f (idₛ `, x) e)))
  inv-wken ⟨⟩η-≈       = ⟨⟩η-≈
  inv-wken {e = e} (⟨⟩γ-≈ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃})
    = ≈-trans ⟨⟩γ-≈ (≡⇒≈ (cong (λ k → wkenTm e t₁ ≫= (wkenTm (keep e) t₂ ≫= k))
                              (trans (wkenTm-∘ₑ t₃ (keep e) (keep (drop idₑ)))
                                        (trans (cong (λ e → wkenTm (keep (drop e)) t₃)
                                                (trans (idrₑ e) (sym (idlₑ e))))
                                                (sym (wkenTm-∘ₑ t₃ (keep (drop idₑ))
                                                                    (keep (keep e))))))))
  inv-wken ↑γ₁-≈      = ↑γ₁-≈
  inv-wken ↑γ₂-≈      = ↑γ₂-≈
  inv-wken (η-≈ x)    = η-≈ (inv-wken x)
  inv-wken (≫=-≈ x x₁) = ≫=-≈ (inv-wken x) (inv-wken x₁)
  inv-wken (↑-≈ x)   = ↑-≈ (inv-wken x)
  inv-wken (inl-≈ x) = inl-≈ (inv-wken x)
  inv-wken (inr-≈ x) = inr-≈ (inv-wken x)
  inv-wken (case-≈ x x₁ x₂) = case-≈ (inv-wken x) (inv-wken x₁) (inv-wken x₂)
  inv-wken ≈-refl           = ≈-refl
  inv-wken (≈-sym x)        = ≈-sym (inv-wken x)
  inv-wken (≈-trans x x₁)   = ≈-trans (inv-wken x) (inv-wken x₁)
