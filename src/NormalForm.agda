module NormalForm where

  open import Preorder

  open import Type
  open import Variable
  open import Embedding
  open import Term

  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.PropositionalEquality.Extra

  mutual
    data Ne : Type → Ctx → Set where
      var   : ∀ {Γ} {a}   → a ∈ Γ → Ne a Γ
      _∙_   : ∀ {Γ} {a b} → Ne (a ⇒ b) Γ → Nf a Γ → Ne b Γ

    data Nf : Type → Ctx → Set where
      unit    : ∀ {Γ} → Nf 𝟙 Γ 
      `λ      : ∀ {Γ} {a b}      → Nf b (Γ `, a) → Nf (a ⇒ b) Γ
      𝕓       : ∀ {Γ}            → Ne 𝕓 Γ   → Nf 𝕓 Γ
      η       : ∀ {ℓ} {Γ}  {a}   → Nf a Γ → Nf (⟨ ℓ ⟩ a) Γ
      _↑_≫=_ : ∀ {ℓᴸ ℓᴴ} {Γ} {a b}  → ℓᴸ ⊑ ℓᴴ → Ne (⟨ ℓᴸ ⟩ a) Γ → Nf (⟨ ℓᴴ ⟩ b) (Γ `, a) → Nf (⟨ ℓᴴ ⟩ b) Γ
      inl     : ∀ {Γ} {a b} → Nf a Γ → Nf (a + b) Γ
      inr     : ∀ {Γ} {a b} → Nf b Γ → Nf (a + b) Γ
      case    : ∀ {Γ} {a b c} → Ne (a + b) Γ → Nf c (Γ `, a) → Nf c (Γ `, b) → Nf c Γ

    wkenNe : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Ne a Δ → Ne a Γ
    wkenNe e (var x) = var (wkenV e x)
    wkenNe e (n ∙ x) = (wkenNe e n) ∙ (wkenNf e x)

    wkenNf : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Nf a Δ → Nf a Γ
    wkenNf e unit           = unit
    wkenNf e (`λ n)         = `λ (wkenNf (keep e) n)
    wkenNf e (η m)          = η (wkenNf e m)
    wkenNf e (𝕓 n)          = 𝕓 (wkenNe e n)
    wkenNf e (p ↑ x ≫= m)  = p ↑ (wkenNe e x) ≫= wkenNf (keep e) m
    wkenNf e (inl n)        = inl (wkenNf e n)
    wkenNf e (inr n)        = inr (wkenNf e n)
    wkenNf e (case x n₁ n₂) = case (wkenNe e x) (wkenNf (keep e) n₁) (wkenNf (keep e) n₂)

    qNf : ∀ {a} {Γ} → Nf a Γ → Term a Γ
    qNf unit           = unit
    qNf (`λ n)         = `λ (qNf n)
    qNf (𝕓 x)          = qNe x
    qNf (η n)          = η (qNf n)
    qNf (p ↑ x ≫= n)  = (p ↑ (qNe x)) ≫= (qNf n)
    qNf (inl n)        = inl (qNf n)
    qNf (inr n)        = inr (qNf n)
    qNf (case n c₁ c₂) = case (qNe n) (qNf c₁) (qNf c₂)

    qNe : ∀ {a} {Γ} → Ne a Γ → Term a Γ
    qNe (var x) = var x
    qNe (t ∙ u) = (qNe t) ∙ (qNf u)

  mutual
    nat-qNe : ∀ {Γ Δ a} {e : Δ ⊆ Γ} → (n : Ne a Γ) → wkenTm e (qNe n) ≡ qNe (wkenNe e n)
    nat-qNe (var x) = cong var refl
    nat-qNe (n ∙ x) = cong₂ _∙_ (nat-qNe n) (nat-qNf x)

    nat-qNf : ∀ {Γ Δ a} {e : Δ ⊆ Γ} → (n : Nf a Γ) → wkenTm e (qNf n) ≡ qNf (wkenNf e n)
    nat-qNf unit = refl
    nat-qNf (`λ n) = cong `λ (nat-qNf n)
    nat-qNf (𝕓 x) = nat-qNe x
    nat-qNf (η n) = cong η (nat-qNf n)
    nat-qNf (c ↑ t ≫= n) = cong₂ _≫=_ (cong (c ↑_) (nat-qNe t)) (nat-qNf n)
    nat-qNf (inl n) = cong inl (nat-qNf n)
    nat-qNf (inr n) = cong inr (nat-qNf n)
    nat-qNf {e = e} (case n c₁ c₂) = cong₃ case (nat-qNe n) (nat-qNf c₁) (nat-qNf c₂)
