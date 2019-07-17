module NI where

  open import Preorder

  open import Type
  open import Embedding
  open import Variable
  open import Term
  open import NormalForm

  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality

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

  open import Relation.Nullary 
  open import Relation.Binary.PropositionalEquality

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
    ⟨⟩_ : ∀ {ℓ} {ℓ'} {a} → ¬ (ℓ' ⊑ ℓ) → ⟨ ℓ ⟩ˢ (⟨ ℓ' ⟩ a)
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
  Var-Sec (p `, ()) 𝟙 ze
  Var-Sec (p `, ()) 𝕓 ze
  Var-Sec (p `, ()) (_ + _) ze
  Var-Sec (p `, (⇒ x)) (⇒ y) ze = Var-Sec (p `, x) y ze
  Var-Sec (p `, (⟨⟩ q)) (⟨ t ⟩ x) ze = {!!} -- ⊑-trans q x
  Var-Sec (p `, x) t (su v) = Var-Sec p t v

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
  ... | ⟨⟩ s = inj₂ (⊑-trans {!!} (⊑-trans r q))

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

  -- -- -------------------------------------
  -- -- -- Noninterference theorem for terms
  -- -- -------------------------------------

  -- -- open import Relation.Binary.PropositionalEquality hiding (subst)

  -- -- ≡→≈ :  ∀ {Γ a} → {m n : Nf Γ a} → m ≡ n → qNf m ≈ qNf n
  -- -- ≡→≈ refl = ≈-refl

  -- -- ≡→≈' :  ∀ {Γ a} → {m n : Term Γ a} → m ≡ n → m ≈ n
  -- -- ≡→≈' refl = ≈-refl
  -- -- -- a weaker version of `IsConstTm`

  -- -- IsConstTm' : ∀ {Γ a} → Term a Γ → Set
  -- -- IsConstTm' {Γ} {a} t = Σ (Term a Ø) λ t' → wkenTm ⊆-term t' ≈ t



  -- -- -- IsConstSub : ∀ {Γ} {a} → (t : Term a Γ) → Set
  -- -- -- IsConstSub {Γ} {a} t = Σ (Term a Ø) λ t' → subst Ø t' ≈ t

  -- -- -- --_∘_ : ∀ {Γ Δ Σ} → Sub Γ Δ →  Sub Δ Σ → Sub Γ Σ
  -- -- -- -- Ø       ∘ δ  = Ø
  -- -- -- -- (s `, t) ∘ δ = (s ∘ δ) `, subst δ t
  -- -- -- substppp : ∀ {Σ Δ Γ} {a} {t : Term a Σ} {σ : Sub Δ Σ} {σ′ : Sub Γ Δ} → subst σ′ (subst σ t) ≈ subst (σ ∘ σ′) t
  -- -- -- substppp = {!!}

  -- -- -- final : ∀ {Γ} → (σ : Sub Γ Ø) → σ ≡ Ø
  -- -- -- final Ø = refl


  -- -- -- PPPP : ∀ {Δ Γ} {a} (t : Term a Γ) → (p : IsConstSub t) → (σ : Sub Δ Γ) → subst σ t ≈ subst Ø (proj₁ p)
  -- -- -- PPPP t (t' , pr) σ with cong-≈ {σ = σ} pr
  -- -- -- ... | a with substppp {t = t'} {σ = Ø} {σ′ = σ}
  -- -- -- ... | b =  ≈-trans (≈-sym a) b

  -- -- -- -- Ultimate noninterference theorem
  -- -- -- Tm-NI : ∀ {Γ} {a} {ℓⁱ ℓᵒ}
  -- -- --     → ⟨ ℓⁱ ⟩ˢᶜ Γ           -- input is atleast ℓⁱ-sensitive
  -- -- --     → Ground a → Tr a ℓᵒ  -- output is ground, and transparent at ℓᵒ
  -- -- --     → (t : Term a Γ) → (IsConstTm' t) ⊎ (ℓⁱ ⊑ ℓᵒ)
  -- -- -- Tm-NI p g q t with Nf-NI p g q (norm t)
  -- -- -- Tm-NI p g q t | inj₁ (n , r) = inj₁ ((qNf n) ,
  -- -- --   ≈-sym
  -- -- --     (≈-trans (consistent _)
  -- -- --     ((≈-sym
  -- -- --           (≈-trans
  -- -- --             ({!!})
  -- -- --             (≡→≈ r))))))
  -- -- -- Tm-NI p g q t | inj₂ y = inj₂ y


  -- -- -- Tm-NI' : ∀ {Δ Γ} {a} {ℓⁱ ℓᵒ}
  -- -- --     → (t : Term a Γ)
  -- -- --     → (σ : Sub Δ Γ)       -- substitution for part of input which is not sensitive
  -- -- --     → ⟨ ℓⁱ ⟩ˢᶜ Δ           -- remaining input is atleast ℓⁱ-sensitive
  -- -- --     → Ground a → Tr a ℓᵒ  -- output is ground, and transparent at ℓᵒ
  -- -- --     → (IsConstTm' (subst σ t)) ⊎ (ℓⁱ ⊑ ℓᵒ)
  -- -- -- Tm-NI' t σ s gr tr = Tm-NI s gr tr _

  -- -- -- open import Relation.Nullary
  
       
  -- -- -- -- PPPP : ∀ {Δ Γ} {a} (t : Term a Γ) → (p : IsConstSub t) → (σ : Sub Δ Γ) → subst σ t ≈ subst Ø (proj₁ p)
  -- -- -- -- PPPP t (t' , pr) σ with cong-≈ {σ = σ} pr
  -- -- -- -- ... | a with substppp {t = t'} {σ = Ø} {σ′ = σ}
  -- -- -- -- ... | b =  ≈-trans (≈-sym a) b

  -- -- -- postulate assume : ∀ {Γ} {a} → (t : Term a Γ) → IsConstTm' t -> IsConstSub t

  -- -- -- NI : ∀ {Δ Γ} {a} {ℓᴸ ℓᴴ}
  -- -- --        → ¬ (ℓᴴ ⊑ ℓᴸ)
  -- -- --        → (t    : Term a Γ)
  -- -- --        → (σ σ′ : Sub Δ Γ)
  -- -- --        → ⟨ ℓᴴ ⟩ˢᶜ Γ
  -- -- --        → Ground a → Tr a ℓᴸ
  -- -- --        → subst σ t ≈ subst σ′ t
  -- -- -- NI ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr
  -- -- --   with Tm-NI pr gr tr t
  -- -- -- NI ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr | inj₁ pp
  -- -- --   with assume t pp
  -- -- -- ... | ppp with PPPP t ppp σ | PPPP t ppp σ′
  -- -- -- ... | a | b = ≈-trans a (≈-sym b )
  -- -- -- NI ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr | inj₂ y = {!!}
