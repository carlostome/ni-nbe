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

  private
    -- sugar
    _︔_ = trans

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

    ↑γ₂ : ∀ {a b} {ℓᴸ ℓᴴ} → {t₁ : Term (⟨ ℓᴸ ⟩ a) Γ} {t₂ : Term (⟨ ℓᴸ ⟩ b) (Γ `, a)}
                              {p : ℓᴸ ⊑ ℓᴴ}
              → (p ↑ (t₁ ≫= t₂)) ≈ ((p ↑ t₁) ≫= (p ↑ t₂))

    ↑γ₃ : ∀ {a} {ℓ} → {t : Term (⟨ ℓ ⟩ a) Γ}
        → (⊑-refl ↑ t) ≈ t

    ↑γ₄ : ∀ {a} {ℓᴸ ℓᴹ ℓᴴ} {t : Term (⟨ ℓᴸ ⟩ a) Γ} {p : ℓᴸ ⊑ ℓᴹ} {q : ℓᴹ ⊑ ℓᴴ }
        → (q ↑ (p ↑ t)) ≈ (⊑-trans p q ↑ t)

    -- +/ reduction
    +η : ∀ {a b} {t : Term (a + b) Γ}
       → t ≈ case t (inl (var ze)) (inr (var ze))

    +β₁ : ∀ {a b c} {t : Term a Γ} {t₁ : Term c (Γ `, a)} {t₂ : Term c (Γ `, b)}
       → case (inl t) t₁ t₂ ≈ subst (idₛ `, t) t₁

    +β₂ : ∀ {a b c} {t : Term b Γ} {t₁ : Term c (Γ `, a)} {t₂ : Term c (Γ `, b)}
       → case (inr t) t₁ t₂ ≈ subst (idₛ `, t) t₂

    -- 𝟙/reduction
    𝟙η : ∀ {t : Term 𝟙 Γ } → t ≈ unit

    -- case permutations

    +π↑  : ∀ {a b c} {ℓᴸ ℓᴴ} {p : ℓᴸ ⊑ ℓᴴ}
                    {t  : Term (a + b) Γ}
                    {t₁ : Term (⟨ ℓᴸ ⟩ c) (Γ `, a)}
                    {t₂ : Term (⟨ ℓᴸ ⟩ c) (Γ `, b)}
      → (p ↑ case t t₁ t₂) ≈ case t (p ↑ t₁) (p ↑ t₂)

    +π≫= : ∀ {a b c d} {ℓ}
                    {t  : Term (a + b) Γ}
                    {t₁ : Term (⟨ ℓ ⟩ c) (Γ `, a)}
                    {t₂ : Term (⟨ ℓ ⟩ c) (Γ `, b)}
                    {u  : Term (⟨ ℓ ⟩ d) (Γ `, c)}
      → (case t t₁ t₂ ≫= u) ≈
         case t
           (t₁ ≫= wkenTm (keep (drop idₑ)) u)
           (t₂ ≫= wkenTm (keep (drop idₑ)) u)

    +π+   : ∀ {a b c d e}
              {t : Term (a + b) Γ}
              {t₁ : Term (c + d) (Γ `, a)}
              {t₂ : Term (c + d) (Γ `, b)}
              {u₁ : Term e (Γ `, c)}
              {u₂ : Term e (Γ `, d)}
          → case (case t t₁ t₂) u₁ u₂ ≈
            case t
              (case t₁ (wkenTm (keep (drop idₑ)) u₁) (wkenTm ((keep (drop idₑ))) u₂))
              (case t₂ (wkenTm (keep (drop idₑ)) u₁) (wkenTm ((keep (drop idₑ))) u₂))

    +π⇒   : ∀ {a b c d}
              {t : Term (a + b) Γ}
              {t₁ : Term (c ⇒ d) (Γ `, a)}
              {t₂ : Term (c ⇒ d) (Γ `, b)}
              {u :  Term c Γ}
          → (case t t₁ t₂ ∙ u) ≈ case t (t₁ ∙ wkenTm (drop idₑ) u) (t₂ ∙ wkenTm (drop idₑ) u)

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

  module SetoidUtil where

    open import Agda.Primitive

    open import Relation.Binary
        using (Setoid ; IsEquivalence)

    open Setoid
        renaming (_≈_ to _≈ₑ_)
        using (Carrier ; isEquivalence)

    S : ∀ {a : Type} {Γ : Ctx} → Setoid lzero lzero
    S {a} {Γ} = record
                  { Carrier       = Term a Γ
                  ; _≈_           = _≈_
                  ; isEquivalence = record
                                      { refl  = ≈-refl
                                      ; sym   = ≈-sym
                                      ; trans = ≈-trans
                                      }
                  }

    import Relation.Binary.SetoidReasoning as SetoidR
    open SetoidR public

    infix 1 begin_

    begin_ : ∀ {a : Type} {Γ : Ctx} → {t u : Term a Γ} → IsRelatedTo S t u → t ≈ u
    begin_ p = begin⟨ S ⟩ p

  open SetoidUtil

  ≡⇒≈ : ∀ {a} {Γ} {t₁ t₂ : Term a Γ} → t₁ ≡ t₂ → t₁ ≈ t₂
  ≡⇒≈ refl = ≈-refl

  inv-subst : ∀ {Γ Δ} {a} {t₁ t₂ : Term a Γ} → {σ : Sub Δ Γ} → t₁ ≈ t₂ → subst σ t₁ ≈  subst σ t₂
  inv-subst {σ = σ} (⇒β {t = t} {u})
    = ≈-trans ⇒β (≡⇒≈ (trans (sym (Term-∘ₛ t (keepˢ σ) (idₛ `, subst σ u)))
                      (trans (cong (λ s → subst (s `, subst σ u) t) auxEqR) (Term-∘ₛ t (idₛ `, u) σ))))
    where
    auxEqR : (σ ₛ∘ₑ drop idₑ) ∘ₛ (idₛ `, subst σ u) ≡ idₛ ∘ₛ σ
    auxEqR = sym
      (idlₛ _ ︔
      sym
        (assₛₑₛ _ _ _ ︔
        (sym (assₛₑₛ σ idₛ idₑ) ︔
        (idrₛ _ ︔
        idrₛₑ _))))

  inv-subst {a = a} {t₁ = t₁} {σ = σ} ⇒η = ≈-trans ⇒η (`λ (≡⇒≈ auxEqR ∙ ≈-refl))
    where
    auxEqR : ∀ {b} → wkenTm (drop {b} idₑ) (subst σ t₁)
      ≡ subst ((σ ₛ∘ₑ drop idₑ) `, var ze) (wkenTm (drop idₑ) t₁)
    auxEqR =
      sym (Term-ₛ∘ₑ t₁ _ _) ︔
      sym
        (sym ((Term-ₑ∘ₛ t₁ _ _)) ︔
        cong (λ σₓ → subst σₓ t₁)
          (sym (assₑₛₑ _ idₑ _) ︔
          cong (λ σₓ → σₓ ₛ∘ₑ drop idₑ)
            (idlₑₛ _)))
  inv-subst {σ = σ} (⟨⟩β {x = x} {f = f})
    = ≈-trans ⟨⟩β (≡⇒≈
      (sym (Term-∘ₛ f _ _) ︔
      sym
        (sym (Term-∘ₛ f _ _) ︔
        cong (λ σₓ → subst (σₓ `, subst σ x) f)
          (idlₛ _ ︔
          sym
            (assₛₑₛ _ _ _ ︔
            (sym (assₛₑₛ σ idₛ idₑ) ︔
            (idrₛ _ ︔
            idrₛₑ _)))))))
  inv-subst ⟨⟩η = ⟨⟩η
  inv-subst (⟨⟩γ {t₃ = t₃}) = ≈-trans ⟨⟩γ (≈-refl ≫= (≈-refl ≫= ≡⇒≈
    (sym (Term-ₛ∘ₑ t₃ _ _) ︔
    sym
      (sym (Term-ₑ∘ₛ t₃ _ _) ︔
      cong (λ σₓ → subst (σₓ `, var ze) t₃)
        (sym (assₑₛₑ _ idₑ _) ︔
         (cong (λ σₓ → σₓ ₛ∘ₑ drop (keep idₑ)) (idlₑₛ _) ︔
         (assₛₑₑ _ _ _ ︔
         sym (assₛₑₑ _ _ _))))))))
  inv-subst ↑γ₁ = ↑γ₁
  inv-subst ↑γ₂ = ↑γ₂
  inv-subst ↑γ₃ = ↑γ₃
  inv-subst ↑γ₄ = ↑γ₄
  inv-subst +η  = +η
  inv-subst 𝟙η  = 𝟙η
  inv-subst +π↑ = +π↑
  inv-subst {σ = σ} (+π≫= {u = u})
    = ≈-trans +π≫= (case ≈-refl
      (≈-refl ≫= ≡⇒≈
        (sym (Term-ₛ∘ₑ u _ _) ︔
        (sym
          (sym (Term-ₑ∘ₛ u _ _) ︔
          (cong (λ σₓ → subst (σₓ `, var ze) u)
            (idlₑₛ _ ︔
            (assₛₑₑ σ _ _ ︔
            (sym (assₛₑₑ σ _ _ ︔ refl)))))))) )
      (≈-refl ≫= ≡⇒≈
        (sym (Term-ₛ∘ₑ u _ _) ︔
        (sym
          (sym (Term-ₑ∘ₛ u _ _) ︔
          (cong (λ σₓ → subst (σₓ `, var ze) u)
            (idlₑₛ _ ︔
            (assₛₑₑ σ _ _ ︔
            (sym (assₛₑₑ σ _ _ ︔ refl))))))))))
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
  inv-subst {σ = σ} (+β₁ {t = t} {t₁ = t₁})
    = ≈-trans +β₁ (≡⇒≈ (trans (trans (sym (Term-∘ₛ t₁ (keepˢ σ) (idₛ
    `, subst σ t))) (cong (λ s → subst (s `, subst σ t) t₁) (trans
    (assₛₑₛ σ _ _) (trans (trans (cong (σ ∘ₛ_) (idlₑₛ idₛ)) (idrₛ σ))
    (sym (idlₛ σ)))) )) (Term-∘ₛ t₁ (idₛ `, t) σ )))
  inv-subst {σ = σ} (+β₂ {t = t} {t₂ = t₂})
    = ≈-trans +β₂ (≡⇒≈ ((trans (trans (sym (Term-∘ₛ t₂ (keepˢ σ) (idₛ
    `, subst σ t))) (cong (λ s → subst (s `, subst σ t) t₂) (trans
    (assₛₑₛ σ _ _) (trans (trans (cong (σ ∘ₛ_) (idlₑₛ idₛ)) (idrₛ σ))
    (sym (idlₛ σ)))) )) (Term-∘ₛ t₂ (idₛ `, t) σ ))))
  inv-subst {Γ = Γ} {Δ = Δ} {a = a} {σ = σ} (+π+ {u₁ = u₁} {u₂ = u₂})
    = ≈-trans +π+ (case ≈-refl
                        (case ≈-refl (aux {u = u₁}) (aux {u = u₂}))
                        (case ≈-refl (aux {u = u₁}) (aux {u = u₂})))
    where
      aux : ∀ {b} {c} {u : Term a (Γ `, c)} →
        wkenTm (keep (drop {b} idₑ)) (subst (keepˢ σ) u) ≈
        subst (keepˢ (keepˢ σ)) (wkenTm (keep (drop idₑ)) u)
      aux {u = u} = ≡⇒≈ (trans (sym (Term-ₛ∘ₑ u (keepˢ σ) (keep (drop idₑ))))
                    (trans (cong (λ s → subst (s `, var ze) u)
                    (trans (assₛₑₑ σ (drop idₑ) (keep (drop idₑ)))
                    (trans (trans refl (sym (assₛₑₑ σ (drop idₑ)
                    (drop (keep idₑ))))) (sym (idlₑₛ _)))))
                    (Term-ₑ∘ₛ u (keepˢ (keepˢ σ)) (keep (drop idₑ)))))

  inv-subst {Γ} {σ = σ} (+π⇒ {u = u})
    = ≈-trans +π⇒ (case ≈-refl (≈-refl ∙ aux) (≈-refl ∙ aux))
    where
      aux : ∀ {b} →
        wkenTm (drop {b} idₑ) (subst σ u) ≈
        subst (keepˢ σ) (wkenTm (drop idₑ) u)
      aux = ≡⇒≈ (trans (sym (Term-ₛ∘ₑ u σ (drop idₑ)))
                (trans (cong (λ s → subst s u) (sym (idlₑₛ _)))
                (Term-ₑ∘ₛ u (keepˢ σ) (drop idₑ)))) 



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
  inv-wken ↑γ₁            = ↑γ₁
  inv-wken ↑γ₂            = ↑γ₂
  inv-wken ↑γ₃            = ↑γ₃
  inv-wken ↑γ₄            = ↑γ₄
  inv-wken (η x)          = η (inv-wken x)
  inv-wken (x ≫= x₁)     = (inv-wken x) ≫= (inv-wken x₁)
  inv-wken (c ↑ x)        = c ↑ (inv-wken x)
  inv-wken (inl x)        = inl (inv-wken x)
  inv-wken (inr x)        = inr (inv-wken x)
  inv-wken (case x x₁ x₂) = case (inv-wken x) (inv-wken x₁) (inv-wken x₂)
  inv-wken +η             = +η
  inv-wken 𝟙η             = 𝟙η
  inv-wken +π↑            = +π↑
  inv-wken (+π≫= {u = u})
    = ≈-trans +π≫= (case ≈-refl
      (≈-refl ≫= ≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong (λ eₓ → wkenTm eₓ u)
            (cong (λ eₓ → keep (drop eₓ)) (idlₑ _) ︔
             sym (cong (λ eₓ → keep (drop eₓ)) (idrₑ _))))))
      ((≈-refl ≫= ≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong (λ eₓ → wkenTm eₓ u)
            (cong (λ eₓ → keep (drop eₓ)) (idlₑ _) ︔
             sym (cong (λ eₓ → keep (drop eₓ)) (idrₑ _))))))))
  inv-wken ≈-refl         = ≈-refl
  inv-wken (≈-sym x)      = ≈-sym (inv-wken x)
  inv-wken (≈-trans x x₁) = ≈-trans (inv-wken x) (inv-wken x₁)
  inv-wken {e = e} (+β₁ {t = t} {t₁ = t₁}) = ≈-trans +β₁ (≡⇒≈
    (sym
      (Term-ₑ∘ₛ t₁ _ (keep e)) ︔
      (cong
        (λ s → subst ((s `, wkenTm e t)) t₁)
          (trans (idrₑₛ e) (sym (idlₛₑ _))) ︔
      Term-ₛ∘ₑ t₁ (idₛ `, t) e)))
  inv-wken {e = e} (+β₂  {t = t} {t₂ = t₂}) =  ≈-trans +β₂ (≡⇒≈
    (sym
      (Term-ₑ∘ₛ t₂ _ (keep e)) ︔
      (cong
        (λ s → subst ((s `, wkenTm e t)) t₂)
          (trans (idrₑₛ e) (sym (idlₛₑ _))) ︔
      Term-ₛ∘ₑ t₂ (idₛ `, t) e)))
  inv-wken (+π+ {u₁ = u₁} {u₂ = u₂}) = ≈-trans +π+ (case ≈-refl
    (case ≈-refl
      (≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong (λ eₓ → wkenTm eₓ u₁)
             (cong (λ eₓ → keep (drop eₓ)) (idlₑ _) ︔
              sym (cong (λ eₓ → keep (drop eₓ)) (idrₑ _))))))
      (≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong (λ eₓ → wkenTm eₓ u₂)
               (cong (λ eₓ → keep (drop eₓ)) (idlₑ _) ︔
               sym (cong (λ eₓ → keep (drop eₓ)) (idrₑ _)))))))
    (case ≈-refl
      (≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong (λ eₓ → wkenTm eₓ u₁)
             (cong (λ eₓ → keep (drop eₓ)) (idlₑ _) ︔
              sym (cong (λ eₓ → keep (drop eₓ)) (idrₑ _))))))
      (≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong (λ eₓ → wkenTm eₓ u₂)
               (cong (λ eₓ → keep (drop eₓ)) (idlₑ _) ︔
               sym (cong (λ eₓ → keep (drop eₓ)) (idrₑ _))))))))
  inv-wken (+π⇒ {u = u}) = ≈-trans +π⇒ (case ≈-refl
    (≈-refl ∙ (≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong₂ wkenTm (cong drop (trans (idlₑ _) (sym (idrₑ _)))) refl))))
     (≈-refl ∙ (≡⇒≈
        (wkenTm-∘ₑ _ _ _ ︔
        sym
          (wkenTm-∘ₑ _ _ _ ︔
          cong₂ wkenTm (cong drop (trans (idlₑ _) (sym (idrₑ _)))) refl)))))
