module NBE where

  open import Preorder

  open import Type
  open import Embedding
  open import Variable
  open import Term
  open import NormalForm
  open import Presheaf

  open import Relation.Binary.PropositionalEquality hiding (subst) renaming (trans to ≡-trans; sym to ≡-sym; refl to ≡-refl)
  open import Relation.Binary.PropositionalEquality.Extra
  open import Data.Product
  open import Data.Unit hiding (_≤_)
  open import Data.Sum
    using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
  open import Function using (_∘′_)


  Termᴾ : Type → 𝒫
  Termᴾ τ = record { In = Term τ ; Wken = wkenTm }

  Nfᴾ : Type → 𝒫
  Nfᴾ τ = record { In = Nf τ ; Wken = wkenNf }

  Neᴾ : Type → 𝒫
  Neᴾ τ = record { In = Ne τ ; Wken = wkenNe }

  𝕓ᴾ : 𝒫
  𝕓ᴾ = record { In   = Nf 𝕓 ; Wken = wkenNf }

  ⟦_⟧ : Type → 𝒫
  ⟦ 𝟙  ⟧        = 𝟙ᴾ
  ⟦ 𝕓 ⟧         = 𝕓ᴾ
  ⟦ a ⇒ b ⟧     = ⟦ a ⟧ ⇒ᴾ  ⟦ b ⟧
  ⟦ ⟨ ℓ ⟩ a ⟧  = 𝒞ᴾ ℓ ⟦ a ⟧
  ⟦ a + b ⟧     = 𝒟ᴾ (⟦ a ⟧ +ᴾ ⟦ b ⟧)

  ⟦_⟧ₑ : Ctx → 𝒫
  ⟦ Ø ⟧ₑ      = 𝟙ᴾ
  ⟦ Γ `, a ⟧ₑ = ⟦ Γ ⟧ₑ ×ᴾ ⟦ a ⟧

  run𝒟Nf : ∀ {a : Type} → 𝒟ᴾ (Nfᴾ a) →∙ (Nfᴾ a)
  run𝒟Nf (return x) = x
  run𝒟Nf (branch x m m₁) = case x (run𝒟Nf m) (run𝒟Nf m₁)

  run𝒟𝒞 : ∀ {A} {ℓ} → 𝒟ᴾ (𝒞ᴾ ℓ A) →∙ (𝒞ᴾ ℓ A)
  run𝒟𝒞 (return x) = x
  run𝒟𝒞 (branch x c₁ c₂) = branch x (run𝒟𝒞 c₁) (run𝒟𝒞 c₂)

  mutual

    run𝒟⇒ : ∀ {a b} {Γ} → 𝒟 ⟦ a ⇒ b ⟧ Γ → (𝒟 ⟦ a ⟧ Γ → 𝒟 ⟦ b ⟧ Γ)
    run𝒟⇒ {a} {b} (return f) x = return (f idₑ (run𝒟 {a} x))
    run𝒟⇒ {a} {b} (branch n m₁ m₂) x =
      branch n
        (run𝒟⇒ {a} {b} m₁ (wken𝒟 (drop idₑ) x))
        (run𝒟⇒ {a} {b} m₂ (wken𝒟 (drop idₑ) x))

    run𝒟 : ∀ {a : Type} → 𝒟ᴾ ⟦ a ⟧ →∙ ⟦ a ⟧
    run𝒟 {𝟙}      _ = tt
    run𝒟 {𝕓}      m = run𝒟Nf m
    run𝒟 {a + b}  m = join𝒟 m
    run𝒟 {a ⇒ b}  m {Δ} = λ e x →
      run𝒟 {b} (run𝒟⇒ {a} {b} {Δ} (wken𝒟 e m) (return x))
    run𝒟 {⟨ ℓ ⟩ a} m = run𝒟𝒞 m

  lookup : ∀ {a Γ} → a ∈ Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
  lookup ze     (_ , v) = v
  lookup (su v) (γ , _) = lookup v γ

  match' : ∀ {b c a} {Δ}
    → (⟦ b ⟧ ⇒ᴾ ⟦ a ⟧) .In Δ
    → (⟦ c ⟧ ⇒ᴾ ⟦ a ⟧) .In Δ
    → ((⟦ b ⟧ +ᴾ ⟦ c ⟧) ⇒ᴾ ⟦ a ⟧) .In Δ
  match' f g e (inj₁ x) = f e x
  match' f g e (inj₂ y) = g e y

  case𝒟 : ∀ {a b c Δ}
    → 𝒟 (⟦ b ⟧ +ᴾ ⟦ c ⟧) Δ
    → (⟦ b ⟧ ⇒ᴾ ⟦ a ⟧) .In Δ
    → (⟦ c ⟧ ⇒ᴾ ⟦ a ⟧) .In Δ
    → 𝒟 ⟦ a ⟧ Δ
  case𝒟 (return (inj₁ x)) f g = return (f idₑ x)
  case𝒟 (return (inj₂ y)) f g = return (g idₑ y)
  case𝒟 {a} {b} {c} {Δ} (branch {_} {b'} {c'} x m₁ m₂)   f g =
    branch x
      (case𝒟 {a} {b} {c} m₁ (λ e' → f (drop idₑ ∘ₑ e')) (λ e' → g (drop idₑ ∘ₑ e')))
      (case𝒟 {a} {b} {c} m₂ (λ e' → f (drop idₑ ∘ₑ e')) (λ e' → g (drop idₑ ∘ₑ e')))

  eval : ∀ {a Γ} → Term a Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
  eval unit _ = tt
  eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
  eval (var x) γ            = lookup x γ
  eval (t ∙ u) γ            = (eval t γ) idₑ (eval u γ)
  eval (η t) γ              = return (eval t γ)
  eval {Γ = Γ} (t ≫= m) γ  = bindExp𝒞' (λ e a → eval m (Wken ⟦ Γ ⟧ₑ e γ , a)) (eval t γ)
  eval (c ↑ t) γ            = up𝒞 c (eval t γ)
  eval (inl t) γ            = return (inj₁ (eval t γ))
  eval (inr t) γ            = return (inj₂ (eval t γ))
  eval {a} {Γ} (case {_} {b} {c} t t₁ t₂) {Δ} γ =
    run𝒟 {a} {Δ}
      (case𝒟 {a} {b} {c} {Δ}
        (eval t γ)
        (λ e x → eval t₁ (Wken ⟦ Γ ⟧ₑ e γ , x))
        (λ e x → eval t₂ (Wken ⟦ Γ ⟧ₑ e γ , x)))

  mutual

    reifyVal : ∀ {a} → ⟦ a ⟧ →∙ Nfᴾ a
    reifyVal {𝟙} x      = unit
    reifyVal {𝕓} x      = x
    reifyVal {a ⇒ b} f  = `λ (reifyVal (f (drop idₑ) (reflect {a} (var ze))))
    reifyVal {⟨ a ⟩ ℓ} m = reifyVal𝒞 m
    reifyVal {a + b}  m = reifyVal𝒟 m

    reifyVal𝒟 : ∀ {a b} → 𝒟ᴾ (⟦ a ⟧ +ᴾ ⟦ b ⟧) →∙ Nfᴾ (a + b)
    reifyVal𝒟 m = run𝒟Nf (map𝒟 reifySum m)

    reifySum : ∀ {a b} → (⟦ a ⟧ +ᴾ ⟦ b ⟧) →∙ Nfᴾ (a + b)
    reifySum {a} {b} = [ inl ∘′ reifyVal {a} , inr ∘′ reifyVal {b} ]′

    reifyVal𝒞 : ∀ {a} {ℓ} → 𝒞ᴾ ℓ ⟦ a ⟧ →∙ Nfᴾ (⟨ ℓ ⟩ a)
    reifyVal𝒞 (return x) = η (reifyVal x)
    reifyVal𝒞 (bind p x m) = p ↑ x ≫= reifyVal𝒞 m
    reifyVal𝒞 (branch x c₁ c₂) = case x (reifyVal𝒞 c₁) (reifyVal𝒞 c₂)

    reflect : ∀ {a} → Neᴾ a →∙ ⟦ a ⟧
    reflect {𝟙}      n = tt
    reflect {𝕓}      n = 𝕓 n
    reflect {a ⇒ b}  n = λ e v → reflect ((wkenNe e n) ∙ (reifyVal v))
    reflect {⟨ ℓ ⟩ a} n =  bind ⊑-refl n (return (reflect {a} (var ze)))
    reflect {a + b}  n =
      branch n
        (return (inj₁ (reflect {a} (var ze))))
        (return (inj₂ (reflect {b} (var ze))))

    idSubst :  ∀ Γ → ⟦ Γ ⟧ₑ .In Γ
    idSubst Ø        = tt
    idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop idₑ) (idSubst Γ) , reflect {T} (var ze)

    reify : ∀{a Γ} → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧) → Nf a Γ
    reify {a} {Γ} f = reifyVal (f (idSubst Γ))

    norm : ∀ {a} → Termᴾ a →∙ Nfᴾ a
    norm t = reify (eval t)
