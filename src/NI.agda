module NI where

  open import Preorder

  open import Type
  open import Embedding
  open import Variable
  open import Term
  open import NormalForm

  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding (subst)
  open import Relation.Nullary 

  ⊆-term : ∀ {Γ} → Γ ⊆ Ø
  ⊆-term {Ø} = base
  ⊆-term {Γ `, x} = drop ⊆-term

  IsConstTm : ∀ {Γ a} → Term a Γ → Set
  IsConstTm {Γ} {a} t = Σ (Term a Ø) λ t' → wkenTm ⊆-term t' ≡ t

  IsConstNf : ∀ {Γ a} → Nf a Γ → Set
  IsConstNf {Γ} {a} n = Σ (Nf a Ø) λ n' → wkenNf ⊆-term n' ≡ n

  -- Example: True is a constant
  private

    Bool : Type
    Bool = 𝟙 + 𝟙

    True : ∀ {Γ} → Nf Bool Γ
    True = inl unit

    TrueIsConst : ∀ {Γ} → IsConstNf {Γ} True
    TrueIsConst = (inl unit) , refl

    -- LamConst : ∀ {Γ} {a b} → (b : Nf b (Γ `, a)) → IsConstNf b
    --          → IsConstNf (`λ b)
    -- LamConst b (fst , refl) = `λ (wkenNf (drop base) fst) , {!!}


  -- Transparency

  -- `Tr a ℓ` to be read as: `a` is transparent at level ℓ
  -- i.e., an observer at level ℓ can observe a value of type `a`

  data Tr : Type → Label → Set where
    𝟙   : ∀ {ℓ}        → Tr 𝟙 ℓ
    𝕓   : ∀ {ℓ}        → Tr 𝕓 ℓ
    _+_ : ∀ {a b} {ℓ}  → Tr a ℓ → Tr b ℓ → Tr (a + b) ℓ
    ⇒_  : ∀ {a b} {ℓ}  → Tr b ℓ → Tr (a ⇒ b) ℓ
    ⟨_⟩_ : ∀ {a} {ℓ ℓ'} → Tr a ℓ → ℓ' ⊑ ℓ → Tr (⟨ ℓ' ⟩ a) ℓ

  -- Sensitivity

  -- `⟨ ℓ ⟩ˢ a` to be read as: `a` is atleast ℓ-sensitive
  -- i.e., type `a` is atleast as sensitive as ℓ
  data ⟨_⟩ˢ : Label → Type → Set where
    ⇒_ : ∀ {ℓ} {a b}    → ⟨ ℓ ⟩ˢ b  → ⟨ ℓ ⟩ˢ (a ⇒ b)
    ⟨⟩_ : ∀ {ℓ} {ℓ'} {a} → (ℓ ⊑ ℓ') → ⟨ ℓ ⟩ˢ (⟨ ℓ' ⟩ a)
    -- products will appear here too!

  -- `⟨ ℓ ⟩ˢᶜ Γ` to be read as: Γ is atleast ℓ-sensitive
  -- i.e., all types in context Γ are atleast as sensitive as ℓ

  data ⟨_⟩ˢᶜ : Label → Ctx → Set where
    Ø    : ∀ {ℓ} → ⟨ ℓ ⟩ˢᶜ Ø
    _`,_ : ∀ {ℓ} {Γ} {a} → ⟨ ℓ ⟩ˢᶜ Γ → ⟨ ℓ ⟩ˢ a → ⟨ ℓ ⟩ˢᶜ (Γ `, a)

  -- A `Ground` type is a first order type

  data Ground : Type → Set where
    𝟙   : Ground 𝟙
    𝕓   : Ground 𝕓
    ⟨_⟩_ : ∀ {a} → Ground a → (ℓ : Label) → Ground (⟨ ℓ ⟩ a)
    _+_ : ∀ {a b} → Ground a → Ground b → Ground (a + b)

  -- Variables preserve sensitivity

  Var-Sen : ∀ {Γ} {a} {ℓ} → ⟨ ℓ ⟩ˢᶜ Γ → a ∈ Γ → ⟨ ℓ ⟩ˢ a
  Var-Sen (e `, a) ze = a
  Var-Sen (e `, a) (su v) = Var-Sen e v

  -- Neutrals preserve sensitivity

  Ne-Sen : ∀ {Γ} {a} {ℓ} → ⟨ ℓ ⟩ˢᶜ Γ → Ne a Γ → ⟨ ℓ ⟩ˢ a
  Ne-Sen e (var x) = Var-Sen e x
  Ne-Sen e (x ∙ n) with (Ne-Sen e x)
  ... | ⇒ p = p

  -- Variables are secure
  -- (observer must have clearance ℓⁱ ⊑ ℓᵒ to observe variable-outputs)

  Var-Sec : ∀ {Γ} {a} {ℓⁱ ℓᵒ}
    → ⟨ ℓⁱ ⟩ˢᶜ Γ      -- input is atleast ℓⁱ-sensitive
    → Tr a ℓᵒ        -- output is transparent at ℓᵒ
    → a ∈ Γ → (ℓⁱ ⊑ ℓᵒ)
  Var-Sec (p `, x) t (su v) = Var-Sec p t v
  Var-Sec (p `, ()) 𝟙 ze
  Var-Sec (p `, ()) 𝕓 ze
  Var-Sec (p `, ()) (_ + _) ze
  Var-Sec (p `, (⇒ x)) (⇒ y) ze    = Var-Sec (p `, x) y ze
  Var-Sec (p `, (⟨⟩ q)) (⟨ t ⟩ x) ze = ⊑-trans q x

  -- Neutrals are secure
  -- (observer must have clearance ℓⁱ ⊑ ℓᵒ to observe neutral-outputs)
  Ne-Sec : ∀ {Γ} {a} {ℓⁱ ℓᵒ}
    → ⟨ ℓⁱ ⟩ˢᶜ Γ      -- input is atleast ℓⁱ-sensitive
    → Tr a ℓᵒ        -- output is transparent at ℓᵒ
    → Ne a Γ → (ℓⁱ ⊑ ℓᵒ)
  Ne-Sec e t (var x) = Var-Sec e t x
  Ne-Sec e t (x ∙ _) = Ne-Sec e (⇒ t) x

  -----------------------------------------------------------------------------
  -- (First-order) Normal forms are either constants (IsConstNf n) or
  -- the observer must have the security clearance (ℓⁱ ⊑ ℓᵒ)
  -- (i.e., observer level must be atleast the least security level in the input)
  -----------------------------------------------------------------------------

  -- `Nf-NI` 

  Nf-NI : ∀ {Γ} {a} {ℓⁱ ℓᵒ}
    → ⟨ ℓⁱ ⟩ˢᶜ Γ           -- input is atleast ℓⁱ-sensitive
    → Ground a → Tr a ℓᵒ  -- output is ground, and transparent at ℓᵒ
    → (n : Nf a Γ) → (IsConstNf n) ⊎ (ℓⁱ ⊑ ℓᵒ)

  -- units are constants
  Nf-NI p g t unit = inj₁ (unit , refl)

  -- return type is not allowed to be a function
  Nf-NI p () t (`λ n)

  -- base types are safe, by Ne-Sec
  Nf-NI p g t (𝕓 x) = inj₂ (Ne-Sec p t x)

  -- argument of η is either constant or at a higher level
  Nf-NI p (⟨ g ⟩ ℓ) (⟨ t ⟩ q) (η n) with Nf-NI p g t n
  ... | inj₁ (n' , r) = inj₁ (η n' , cong η r)
  ... | inj₂ r = inj₂ r

  --
  Nf-NI p g (⟨ t ⟩ q) (r ↑ x ≫= n) with Ne-Sen p x
  ... | ⟨⟩ s = inj₂ (⊑-trans s (⊑-trans r q))

  --
  Nf-NI p (g + _) (t + _) (inl n) with Nf-NI p g t n
  ... | inj₁ (n' , r) = inj₁ (inl n' , cong inl r)
  ... | inj₂ r = inj₂ r

  -- 
  Nf-NI p (_ + g) (_ + t) (inr n) with Nf-NI p g t n
  ... | inj₁ (n' , r) = inj₁ (inr n' , cong inr r)
  ... | inj₂ r = inj₂ r

  -- raw unprotected sums are not allowed in the context
  Nf-NI p g t (case x n₁ n₂) with Ne-Sen p x
  ... | ()

  -------------------------------------
  -- Noninterference theorem for terms
  -------------------------------------

  open import Conversion
  open import Substitution
  open import NBE
  open import Correctness

  open import Data.Empty

  IsConstTm' : ∀ {Γ a} → Term a Γ → Set
  IsConstTm' {Γ} {a} t = Σ (Term a Ø) λ t' → wkenTm ⊆-term t' ≈ t

  -- Ultimate noninterference theorem
  Tm-NI : ∀ {Γ} {a} {ℓⁱ ℓᵒ}
      → ⟨ ℓⁱ ⟩ˢᶜ Γ           -- input is atleast ℓⁱ-sensitive
      → Ground a → Tr a ℓᵒ  -- output is ground, and transparent at ℓᵒ
      → (t : Term a Γ) → (IsConstTm' t) ⊎ (ℓⁱ ⊑ ℓᵒ)
  Tm-NI p g q t with Nf-NI p g q (norm t)
  Tm-NI p g q t | inj₁ (n , r) = inj₁ ((qNf n) ,
    (≈-trans
      (≡⇒≈ (trans (nat-qNf n)
                  (cong qNf r)))
        (≈-sym (consistent t))))
  Tm-NI p g q t | inj₂ y = inj₂ y

  private
    lemma : ∀ {Γ} {Δ} (σ σ′ : Sub Δ Γ) → ⊆-term ₑ∘ₛ σ ≡ ⊆-term ₑ∘ₛ σ′
    lemma {Ø} {Δ} Ø Ø                     = refl
    lemma {Γ `, x} {Δ} (σ `, _) (σ′ `, _) = lemma σ σ′

  NI-Prot : ∀ {Δ Γ} {a} {ℓᴸ ℓᴴ}
         → ¬ (ℓᴴ ⊑ ℓᴸ)
         → (t    : Term a Γ)
         → (σ σ′ : Sub Δ Γ)
         → ⟨ ℓᴴ ⟩ˢᶜ Γ
         → Ground a → Tr a ℓᴸ
         → subst σ t ≈ subst σ′ t
  NI-Prot ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr
    with Tm-NI pr gr tr t
  NI-Prot ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr | inj₁ (t′ , p)
   with inv-subst {σ = σ} p | inv-subst {σ = σ′} p
  ... | eq₁ | eq₂ = ≈-trans (≈-sym eq₁)
    (≈-trans (≡⇒≈ (trans (trans (sym (Term-ₑ∘ₛ t′ σ ⊆-term)) (cong (λ s → subst s t′) (lemma σ σ′)))
                  (Term-ₑ∘ₛ t′ σ′ ⊆-term))) eq₂)
  NI-Prot ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr | inj₂ y = ⊥-elim (¬ℓᴴ⊑ℓᴸ y)

  -- Low equivalence of substitutions
  data _≈⟨_⟩ₛ_ {Γ Σ} (σ₁ : Sub Σ Γ) (ℓᴴ : Label) (σ₂ : Sub Σ Γ) : Set where
    loweq : ∀ {Δ} → ⟨ ℓᴴ ⟩ˢᶜ Δ → (σₗ : Sub Δ Γ) → (σₕ₁ σₕ₂ : Sub Σ Δ)
          → σ₁ ≡ (σₗ ∘ₛ σₕ₁) → σ₂ ≡ (σₗ ∘ₛ σₕ₂)
          → σ₁ ≈⟨ ℓᴴ ⟩ₛ σ₂

  -- Noninterference for the calculus
  NI : ∀ {Δ Γ} {a} {ℓᴸ ℓᴴ}
      → ¬ (ℓᴴ ⊑ ℓᴸ)
      → (t     : Term a Γ)
      → (σ₁ σ₂ : Sub Δ Γ)
      → σ₁ ≈⟨ ℓᴴ ⟩ₛ σ₂
      → Ground a → Tr a ℓᴸ
      → subst σ₁ t ≈ subst σ₂ t
  NI ¬ℓᴴ⊑ℓᴸ t .(σₗ ∘ₛ σₕ₁) .(σₗ ∘ₛ σₕ₂) (loweq pr σₗ σₕ₁ σₕ₂ refl refl) gr tr
    with NI-Prot ¬ℓᴴ⊑ℓᴸ (subst σₗ t) σₕ₁ σₕ₂ pr gr tr
  ... | p = ≈-trans (≡⇒≈ (Term-∘ₛ t σₗ σₕ₁))
                    (≈-trans p (≡⇒≈ (sym (Term-∘ₛ t σₗ σₕ₂))))
