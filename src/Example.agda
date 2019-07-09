import Relation.Binary as RB
open import Level

module Example (Pre : RB.Preorder 0ℓ 0ℓ 0ℓ) where

  open import NBELMon (Pre)
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  open import Data.Sum

  Bool : Type
  Bool = 𝟙 + 𝟙

  True : ∀ {Γ} → Nf Bool Γ
  True = inl unit

  False : ∀ {Γ} → Nf Bool Γ
  False = inr unit

  -- general lemma about normal forms of programs from secret
  -- inputs to public booleans that does not assume anything
  -- but the preorder on the monad labels
  nf-lemma₁ : ∀ {a} {ℓᴸ ℓᴴ}
            → ¬ (ℓᴴ ⊑ ℓᴸ)
            → (n : Nf (⟨ ℓᴴ ⟩ a ⇒ ⟨ ℓᴸ ⟩ Bool) Ø)
            → (n ≡ `λ (η True)) ⊎ (n ≡ `λ (η False))
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inl unit))) = inj₁ refl
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inl (case x n n₁))))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inr unit))) = inj₂ refl
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inr (case x n n₁))))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (case x k₁ k₂)))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (c ↑ m ≫= k))
    with neutrality m
  ... | here refl = ⊥-elim (ℓᴴ⋢ℓᴸ c)
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (case x k₁ k₂))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (case x _ _)
    with neutrality x
  ... | ()
  
  -- An equivalent of nf-lemma₁.
  -- I chose a different (but equivalent) type for the normal form
  -- since it readily yields the result on using `Nf-Sec`.
  
  nf-lemma₁' : ∀ {a} {ℓᴸ ℓᴴ}
            → ¬ (ℓᴴ ⊑ ℓᴸ)
            → (n : Nf (⟨ ℓᴸ ⟩ Bool) (Ø `, (⟨ ℓᴴ ⟩ a)))
            → IsConstNf n
  nf-lemma₁' ℓᴴ⋢ℓᴸ n
    with Nf-NI
           (Ø `, (⟨⟩ ⊑-refl))  -- (Ø `, ⟨ ℓᴴ ⟩ a) is atleast H-sensitive
           (⟨ 𝟙 + 𝟙 ⟩ _)       -- `⟨ ℓᴸ ⟩ Bool` is ground
           (⟨ 𝟙 + 𝟙 ⟩ ⊑-refl)  -- `⟨ ℓᴸ ⟩ Bool` is transparent at ℓᴸ
           n
  ... | inj₁ nIsConst = nIsConst
  ... | inj₂ ℓᴴ⊑ℓᴸ    = ⊥-elim (ℓᴴ⋢ℓᴸ ℓᴴ⊑ℓᴸ)

  -- A more general version of nf-lemma₁'
  -- (insantiating `b` with `Bool` gives nf-lemma₁')
  
  nf-lemma₂ :  ∀ {a} {b} {ℓᴸ ℓᴴ}
            → ¬ (ℓᴴ ⊑ ℓᴸ)
            → Ground b
            → Tr b ℓᴸ
            → (n : Nf (⟨ ℓᴸ ⟩ b) (Ø `, (⟨ ℓᴴ ⟩ a)))
            → IsConstNf n
  nf-lemma₂ ℓᴴ⋢ℓᴸ g t n with Nf-NI
           (Ø `, (⟨⟩ ⊑-refl))  -- (Ø `, ⟨ ℓᴴ ⟩ a) is atleast H-sensitive
           (⟨ g ⟩ _)           -- `⟨ ℓᴸ ⟩ b` is ground (since b is)
           (⟨ t ⟩ ⊑-refl)      -- `⟨ ℓᴸ ⟩ b` is transparent at ℓᴸ (since b is)
           n
  ... | inj₁ nIsConst = nIsConst
  ... | inj₂ ℓᴴ⊑ℓᴸ = ⊥-elim (ℓᴴ⋢ℓᴸ ℓᴴ⊑ℓᴸ)

  -- NOTE: Using nf-lemma₂, we should be able to prove NI for
  -- `Nf (⟨ ℓᴸ ⟩ b × ⟨ ℓᴴ ⟩ b)  (Ø `, ⟨ ℓᴸ ⟩ a `, ⟨ ℓᴴ ⟩ a)`
  -- TBD after we add products
