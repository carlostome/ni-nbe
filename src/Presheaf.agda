module Presheaf where

  open import Preorder
  open import Type
  open import Embedding
  open import NormalForm

  open import Data.Product
  open import Data.Unit hiding (_≤_)
  open import Data.Sum
    using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
  open import Function using (_∘′_)

  record 𝒫 : Set₁ where
    field
      In   : Ctx → Set
      Wken : ∀ {Δ Γ} (Γ⊆Δ : Γ ⊆ Δ) → (In Δ → In Γ)

  open 𝒫 public

  -- natural transformation
  _→∙_ : 𝒫 → 𝒫 → Set
  (P →∙ Q) = ∀ {Γ} → P .In Γ → Q .In Γ

  _×ᴾ_ : 𝒫 → 𝒫 → 𝒫
  In (P ×ᴾ Q) Γ                 = (In P Γ) × (In Q Γ)
  Wken (P ×ᴾ Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

  _⇒ᴾ_ :  𝒫 → 𝒫 → 𝒫
  In (P ⇒ᴾ Q) Γ             = ∀ {Δ} → Δ ⊆ Γ → P .In Δ → Q .In Δ
  (P ⇒ᴾ Q) .Wken Γ⊆Δ₁ f Δ⊆Γ = f (Γ⊆Δ₁ ∘ₑ Δ⊆Γ)

  _+ᴾ_ :  𝒫 → 𝒫 → 𝒫
  In (P +ᴾ Q) Γ    = (In P Γ) ⊎ (In Q Γ)
  (P +ᴾ Q) .Wken Γ⊆Δ = [ inj₁ ∘′ Wken P Γ⊆Δ , inj₂ ∘′ Wken Q Γ⊆Δ  ]′ 

  𝟙ᴾ : 𝒫
  𝟙ᴾ = record { In = λ _ → ⊤ ; Wken = λ {Δ} {Γ} Γ⊆Δ _ → tt }

  open 𝒫


  data 𝒞 (A : 𝒫) (ℓ : Label) : Ctx → Set where
    return : ∀ {Γ}       → A .In Γ → 𝒞 A ℓ Γ
    bind   : ∀ {Γ} {a} {ℓᴸ}  → ℓᴸ ⊑ ℓ → Ne (⟨ ℓᴸ ⟩ a) Γ → 𝒞 A ℓ (Γ `, a) → 𝒞 A ℓ Γ
    branch : ∀ {Γ} {a b} → Ne (a + b) Γ →  𝒞 A ℓ (Γ `, a) →  𝒞 A ℓ (Γ `, b) → 𝒞 A ℓ Γ

  wken𝒞 : ∀ {ℓ} {A} {Γ Δ} → Γ ⊆ Δ → 𝒞 A ℓ Δ → 𝒞 A ℓ Γ
  wken𝒞 {A = A} e (return x) = return (Wken A e x)
  wken𝒞 e (bind p x m)        = bind p  (wkenNe e x) (wken𝒞 (keep e) m)
  wken𝒞 e (branch x m₁ m₂)    = branch (wkenNe e x) (wken𝒞 (keep e) m₁) (wken𝒞 (keep e) m₂)

  {- The cover monad is a presheaf -}
  𝒞ᴾ : Label → 𝒫 → 𝒫
  𝒞ᴾ ℓ A = record { In = 𝒞 A ℓ ; Wken = wken𝒞 }

  {- We can implement functorial map -}
  map𝒞  : ∀ {ℓ} {A B} → (A →∙ B) → (𝒞ᴾ ℓ A →∙ 𝒞ᴾ ℓ B)
  map𝒞 f (return x) = return (f x)
  map𝒞 f (bind p x m) = bind p x (map𝒞 f m)
  map𝒞 f (branch x c₁ c₂) = branch x (map𝒞 f c₁) (map𝒞 f c₂)

  {- And derive μ -}
  join𝒞 : ∀ {ℓ} {A} → 𝒞ᴾ ℓ (𝒞ᴾ ℓ A) →∙ 𝒞ᴾ ℓ A
  join𝒞 (return x) = x
  join𝒞 (bind p f m) = bind p f (join𝒞 m)
  join𝒞 (branch x c₁ c₂) = branch x (join𝒞 c₁) (join𝒞 c₂)

  mapExp𝒞  : ∀ {ℓ} {A B} → (A ⇒ᴾ B) →∙ (𝒞ᴾ ℓ A ⇒ᴾ 𝒞ᴾ ℓ B)
  mapExp𝒞 f e (return x) = return (f e x)
  mapExp𝒞 f e (bind p x m) = bind p x (mapExp𝒞 f (drop e) m)
  mapExp𝒞 f e (branch x c₁ c₂) = branch x (mapExp𝒞 f (drop e) c₁) (mapExp𝒞 f (drop e) c₂)

  bindExp𝒞 : ∀ {ℓ} {A B} → (A ⇒ᴾ 𝒞ᴾ ℓ B) →∙ (𝒞ᴾ ℓ A ⇒ᴾ 𝒞ᴾ ℓ B)
  bindExp𝒞 f e m = join𝒞 (mapExp𝒞 f e m)

  -- an inlined, special case of bindExp𝒞
  -- to ease the correctness proof of evaluation
  bindExp𝒞' : ∀ {ℓ} {A B Γ} → (A ⇒ᴾ 𝒞ᴾ ℓ B) .In Γ → (𝒞 A ℓ Γ → 𝒞 B ℓ Γ) 
  bindExp𝒞' f (return x) = f idₑ x -- f ⊆-refl x
  bindExp𝒞' f (bind p x m) = bind p x (bindExp𝒞' (λ e a → f (drop idₑ ∘ₑ e) a) m)
  bindExp𝒞' f (branch x m₁ m₂) =
    branch x
      (bindExp𝒞' (λ e a → f (drop idₑ ∘ₑ e) a) m₁)
      (bindExp𝒞' (λ e a → f (drop idₑ ∘ₑ e) a) m₂)

  up𝒞 : ∀ {ℓᴸ ℓᴴ} {A} → ℓᴸ ⊑ ℓᴴ → (𝒞ᴾ ℓᴸ A →∙ 𝒞ᴾ ℓᴴ A)
  up𝒞 L⊑H (return x)  = return x
  up𝒞 L⊑H (bind p n k)  = bind (⊑-trans p L⊑H) n (up𝒞 L⊑H k)
  up𝒞 L⊑H (branch x c₁ c₂) = branch x (up𝒞 L⊑H c₁) (up𝒞 L⊑H c₂)

  data 𝒟 (A : 𝒫) : Ctx → Set where
    return : ∀ {Γ} → A .In Γ → 𝒟 A Γ
    branch : ∀ {Γ} {a b}
      → Ne (a + b) Γ
      → (c₁ : 𝒟 A (Γ `, a)) → (c₂ :  𝒟 A (Γ `, b))
      ---------------------------------------------
      → 𝒟 A Γ

  wken𝒟 : ∀ {A} {Γ Δ} → Γ ⊆ Δ → 𝒟 A Δ → 𝒟 A Γ
  wken𝒟 {A} e (return x) = return (Wken A e x)
  wken𝒟 e (branch x c₁ c₂) = branch (wkenNe e x) (wken𝒟 (keep e) c₁) (wken𝒟 (keep e) c₂)

  𝒟ᴾ : 𝒫 → 𝒫
  𝒟ᴾ A = record { In = 𝒟 A ; Wken = wken𝒟 }

  map𝒟  : ∀ {A B} → (A →∙ B) → (𝒟ᴾ A →∙ 𝒟ᴾ B)
  map𝒟 f (return x) = return (f x)
  map𝒟 f (branch x c₁ c₂) = branch x (map𝒟 f c₁) (map𝒟 f c₂)

  join𝒟 : ∀ {A} → 𝒟ᴾ (𝒟ᴾ A) →∙ 𝒟ᴾ A
  join𝒟 (return x) = x
  join𝒟 (branch x m m₁) = branch x (join𝒟 m) (join𝒟 m₁)

  mapExp𝒟  : ∀ {A B} → (A ⇒ᴾ B) →∙ (𝒟ᴾ A ⇒ᴾ 𝒟ᴾ B)
  mapExp𝒟 f e (return x) =
    return (f e x)
  mapExp𝒟 f e (branch x c₁ c₂) =
    branch x (mapExp𝒟 f (drop e) c₁) (mapExp𝒟 f (drop e) c₂)

  bindExp𝒟 : ∀ {A B} → (A ⇒ᴾ 𝒟ᴾ B) →∙ (𝒟ᴾ A ⇒ᴾ 𝒟ᴾ B)
  bindExp𝒟 f e m = join𝒟 (mapExp𝒟 f e m)
