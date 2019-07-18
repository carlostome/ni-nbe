{-# OPTIONS --allow-unsolved-metas #-}
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
    ⇒β      : ∀ {a b} → {t : Term b (Γ `, a)} {u : Term a Γ}
              → ((`λ t) ∙ u) ≈ subst (idₛ `, u) t

    ⇒η      : ∀ {a b} → {t : Term (a ⇒ b) Γ}
              → t  ≈ `λ (wkenTm (drop idₑ) t ∙ (var ze))


    -- ⟨⟩/reduction
    ⟨⟩β     : ∀ {a b} {ℓ} → {x : Term a Γ} {f : Term (⟨ ℓ ⟩ b) (Γ `, a)}
              → (η x ≫= f) ≈ subst (idₛ `, x) f

    ⟨⟩η     : ∀ {a} {ℓ} → {t : Term (⟨ ℓ ⟩ a) Γ}
              → t ≈ (t ≫= η (var ze))

    ⟨⟩γ     : ∀ {a b c} {ℓ} → {t₁ : Term (⟨ ℓ ⟩ a) Γ}
                                {t₂ : Term (⟨ ℓ ⟩ b) (Γ `, a)}
                                {t₃ : Term (⟨ ℓ ⟩ c) (Γ `, b)}
              → ((t₁ ≫= t₂) ≫= t₃) ≈ (t₁ ≫= (t₂ ≫= wkenTm (keep (drop idₑ)) t₃))

    -- ↑
    ↑γ₁ : ∀ {a} {ℓᴸ ℓᴴ} → {t : Term a Γ} {p : ℓᴸ ⊑ ℓᴴ}
              → (p ↑ η t) ≈ η t

    ↑γ₂ : ∀ {a b} {ℓᴸ ℓᴴ} → {t₁ : Term (⟨ ℓᴸ ⟩ a) Γ} {t₂ : Term (⟨ ℓᴸ ⟩ (⟨ ℓᴸ ⟩ b)) (Γ `, a)}
                              {p : ℓᴸ ⊑ ℓᴴ} 
              → (p ↑ (t₁ ≫= t₂)) ≈ ((p ↑ t₁) ≫= (p ↑ t₂))

    ↑γ₃ : ∀ {a} {ℓ} → {t : Term (⟨ ℓ ⟩ a) Γ}
        → (⊑-refl ↑ t) ≈ t

    -- +/ reduction
    +η : ∀ {a b} {t : Term (a + b) Γ}
       → t ≈ case t (inl (var ze)) (inr (var ze))

    -- 𝟙/reduction
    𝟙η : ∀ {t : Term 𝟙 Γ } → t ≈ unit

    -- λ/ congruence
    _∙_ : ∀ {a b} {f f′ : Term (a ⇒ b) Γ} {u u′ : Term a Γ}
        → f ≈ f′
        → u ≈ u′
        → (f ∙ u) ≈ (f′ ∙ u′)

    `λ : ∀ {a b} {t t′ : Term a (Γ `, b)}
       → t ≈ t′
       → (`λ t) ≈ (`λ t′)

    -- ⟨⟩/ congruence
    η     : ∀ {a} {ℓ} → {t₁ t₂ : Term a Γ}
          → t₁ ≈ t₂
          → η {ℓ = ℓ} t₁ ≈ η t₂

    _≫=_   : ∀ {a b } {ℓ} → {t₁ t₂ : Term (⟨ ℓ ⟩ a) Γ} {t₃ t₄ : Term (⟨ ℓ ⟩ b) (Γ `, a) }
            → t₁ ≈ t₂
            → t₃ ≈ t₄
            → (t₁ ≫= t₃) ≈ (t₂ ≫= t₄)

    _↑_     : ∀ {a} {ℓᴸ ℓᴴ} (c : ℓᴸ ⊑ ℓᴴ) {t₁ t₂ : Term (⟨ ℓᴸ ⟩ a) Γ}
            → t₁ ≈ t₂
            → (c ↑ t₁) ≈ (c ↑ t₂)

    -- +/ congruence
    inl     : ∀ {a b} → {t₁ t₂ : Term a Γ}
            → t₁ ≈ t₂
            → (Term (a + b) Γ ∋ inl t₁) ≈ (inl t₂)

    inr     : ∀ {a b} → {t₁ t₂ : Term b Γ}
            → t₁ ≈ t₂
            → (Term (a + b) Γ ∋ inr t₁) ≈ (inr t₂)

    case    : ∀ {a b c} {t₁ t₂ : Term (a + b) Γ}
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

  inv-subst : ∀ {Γ Δ} {a} {t₁ t₂ : Term a Γ} → {σ : Sub Δ Γ} → t₁ ≈ t₂ → subst σ t₁ ≈  subst σ t₂
  inv-subst {σ = σ} (⇒β {t = t} {u})
    = ≈-trans ⇒β (≡⇒≈ (trans (sym (Term-∘ₛ t (keepˢ σ) (idₛ `, subst σ u)))
                      (trans (cong (λ s → subst (s `, subst σ u) t) {!!}) (Term-∘ₛ t (idₛ `, u) σ))))
  inv-subst ⇒η = ≈-trans ⇒η (`λ (≡⇒≈ {!!} ∙ ≈-refl))
  inv-subst ⟨⟩β = ≈-trans ⟨⟩β {!!}
  inv-subst ⟨⟩η = ⟨⟩η
  inv-subst ⟨⟩γ = ≈-trans ⟨⟩γ (≡⇒≈ (cong ? ?))
  inv-subst ↑γ₁ = ↑γ₁
  inv-subst ↑γ₂ = ↑γ₂
  inv-subst ↑γ₃ = ↑γ₃
  inv-subst +η  = +η
  inv-subst 𝟙η  = 𝟙η
  inv-subst (x ∙ x₁) = inv-subst x ∙ inv-subst x₁
  inv-subst (`λ x)   = `λ (inv-subst x)
  inv-subst (η x)    = η (inv-subst x)
  inv-subst (x ≫= x₁) = inv-subst x ≫= inv-subst x₁
  inv-subst (c ↑ x) = c ↑ inv-subst x
  inv-subst (inl x) = inl (inv-subst x)
  inv-subst (inr x) = inr (inv-subst x)
  inv-subst (case x x₁ x₂) = case (inv-subst x) (inv-subst x₁) (inv-subst x₂)
  inv-subst ≈-refl         = ≈-refl
  inv-subst (≈-sym x)      = ≈-sym (inv-subst x)
  inv-subst (≈-trans x x₁) = ≈-trans (inv-subst x) (inv-subst x₁)

  -- weakening preserves ≈
  inv-wken : ∀ {a} {Γ} {t₁ t₂ : Term a Γ}
                {Δ : Ctx} {e : Δ ⊆ Γ}
            → t₁ ≈ t₂
            → wkenTm e t₁ ≈ wkenTm e t₂
  inv-wken {e = e} (⇒β {t = t} {u = u})
    = ≈-trans ⇒β (≡⇒≈ (trans (trans (sym (Term-ₑ∘ₛ t (idₛ `, wkenTm e u) (keep e)))
                                          (cong (λ s → subst (s `, wkenTm e u) t)
                                                (trans (idrₑₛ e) (sym (idlₛₑ e)))))
                      (Term-ₛ∘ₑ t (idₛ `, u) e)))
  inv-wken {e = e} (⇒η {t = t₁})
    = ≈-trans ⇒η (≡⇒≈ (cong (λ f → `λ (f ∙ var ze))
                              (trans (wkenTm-∘ₑ t₁ e (drop idₑ))
                              (trans ((cong (λ e → wkenTm (drop e) t₁)
                                              (trans (idrₑ e) (sym (idlₑ e)))))
                                        (sym (wkenTm-∘ₑ t₁ (drop idₑ) (keep e)))))))
  inv-wken (x ∙ x₁) = (inv-wken x) ∙ (inv-wken x₁)
  inv-wken (`λ x)    = `λ (inv-wken x)
  inv-wken {e = e} (⟨⟩β {x = x} {f = f})
    = ≈-trans ⟨⟩β (≡⇒≈ (trans (trans (sym (Term-ₑ∘ₛ f (idₛ `, wkenTm e x) (keep e)))
                                          (cong (λ s → subst (s `, wkenTm e x) f)
                                                (trans (idrₑₛ e) (sym (idlₛₑ e)))))
                        (Term-ₛ∘ₑ f (idₛ `, x) e)))
  inv-wken ⟨⟩η       = ⟨⟩η
  inv-wken {e = e} (⟨⟩γ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃})
    = ≈-trans ⟨⟩γ (≡⇒≈ (cong (λ k → wkenTm e t₁ ≫= (wkenTm (keep e) t₂ ≫= k))
                              (trans (wkenTm-∘ₑ t₃ (keep e) (keep (drop idₑ)))
                                        (trans (cong (λ e → wkenTm (keep (drop e)) t₃)
                                                (trans (idrₑ e) (sym (idlₑ e))))
                                                (sym (wkenTm-∘ₑ t₃ (keep (drop idₑ))
                                                                    (keep (keep e))))))))
  inv-wken ↑γ₁      = ↑γ₁
  inv-wken ↑γ₂      = ↑γ₂
  inv-wken ↑γ₃      = ↑γ₃
  inv-wken (η x)    = η (inv-wken x)
  inv-wken (x ≫= x₁) = (inv-wken x) ≫= (inv-wken x₁)
  inv-wken (c ↑ x)    = c ↑ (inv-wken x)
  inv-wken (inl x) = inl (inv-wken x)
  inv-wken (inr x) = inr (inv-wken x)
  inv-wken (case x x₁ x₂) = case (inv-wken x) (inv-wken x₁) (inv-wken x₂)
  inv-wken +η      = +η
  inv-wken 𝟙η      = 𝟙η
  inv-wken ≈-refl           = ≈-refl
  inv-wken (≈-sym x)        = ≈-sym (inv-wken x)
  inv-wken (≈-trans x x₁)   = ≈-trans (inv-wken x) (inv-wken x₁)
