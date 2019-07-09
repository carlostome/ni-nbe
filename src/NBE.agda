{-# OPTIONS --allow-unsolved-metas #-}
import Relation.Binary as RB
open import Level using (0ℓ)

module NBE (Pre : RB.Preorder 0ℓ 0ℓ 0ℓ)where

  Label   = RB.Preorder.Carrier Pre

  _⊑_     = RB.Preorder._∼_ Pre
  ⊑-refl  = RB.Preorder.refl Pre
  ⊑-trans = RB.Preorder.trans Pre

  module TypeModule where

    data Type  : Set where
      𝟙     :                 Type
      𝕓     :                 Type
      _⇒_   : (a b : Type)  → Type
      _+_   : (a b : Type)  → Type
      ⟨_⟩_   : (ℓ : Label) (a : Type) → Type

    infixr 10 _⇒_

    -- Ctx as a snoc list of types
    data Ctx : Set where
      Ø    : Ctx
      _`,_ : Ctx → Type → Ctx

  open TypeModule public

  module Weakening where

    -- Weakening over contexts Γ ⊆ Δ to be read as:
    -- Γ is weaker (contains possibly more types) than Δ
    -- Δ is thinner (contains possibly less types) than Γ
    data _⊆_ : Ctx → Ctx → Set where
      base : Ø ⊆ Ø
      keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
      drop : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ Δ

    -- Weakenings are a preorder relation
    ⊆-refl : RB.Reflexive _⊆_
    ⊆-refl {Ø}      = base
    ⊆-refl {Γ `, T} = keep ⊆-refl

    ⊆-trans : RB.Transitive _⊆_
    ⊆-trans base q = q
    ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
    ⊆-trans (keep p) (drop q) = drop (⊆-trans p q)
    ⊆-trans (drop p) q        = drop (⊆-trans p q)

  open Weakening public

  module Variable where

    -- De Bruijn index into a context
    data _∈_ : Type → Ctx → Set where
      ze : ∀ {Γ a}   → a ∈ (Γ `, a)
      su : ∀ {Γ a S} → a ∈ Γ → a ∈ (Γ `, S)

    wkenV : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
    wkenV (keep e) ze     = ze
    wkenV (keep e) (su v) = su (wkenV e v)
    wkenV (drop e) v      = su (wkenV e v)

  open Variable public

  module TermM where

    data Term : Type → Ctx → Set where
      unit  : ∀ {Γ} → Term 𝟙 Γ
      `λ    : ∀ {Γ} {a b} → Term b (Γ `, a) → Term (a ⇒ b) Γ
      var   : ∀ {Γ} {a}   → a ∈ Γ → Term a Γ
      _∙_   : ∀ {Γ} {a b} → Term (a ⇒ b) Γ → Term a Γ → Term b Γ
      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Term (⟨ ℓᴸ ⟩ a) Γ → Term (⟨ ℓᴴ ⟩ a) Γ
      η     : ∀ {ℓ} {Γ} {a}    → Term a Γ → Term (⟨ ℓ ⟩ a) Γ
      _≫=_ : ∀ {ℓ} {Γ} {a b} → Term (⟨ ℓ ⟩ a) Γ → Term (⟨ ℓ ⟩ b) (Γ `, a) → Term (⟨ ℓ ⟩ b) Γ
      inl   : ∀ {Γ} {a b} → Term a Γ → Term (a + b) Γ
      inr   : ∀ {Γ} {a b} → Term b Γ → Term (a + b) Γ
      case  : ∀ {Γ} {a b c} → Term (a + b) Γ → Term c (Γ `, a) → Term c (Γ `, b) → Term c Γ
    
    wkenTm : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Term a Δ → Term a Γ
    wkenTm e unit = unit
    wkenTm e (`λ t)    = `λ (wkenTm (keep e) t)
    wkenTm e (var x)   = var (wkenV e x)
    wkenTm e (t ∙ t₁)  = wkenTm e t ∙ wkenTm e t₁
    wkenTm e (η t)     = η (wkenTm e t)
    wkenTm e (t ≫= k) = wkenTm e t ≫= wkenTm (keep e) k
    wkenTm e (x ↑ t)   = x ↑ wkenTm e t
    wkenTm e (inl t) = inl (wkenTm e t)
    wkenTm e (inr t) = inr (wkenTm e t)
    wkenTm e (case t t₁ t₂) = case (wkenTm e t) (wkenTm (keep e) t₁) (wkenTm (keep e) t₂)

  open TermM public

  module NormalForm where

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

  open NormalForm public

  open import Data.Product
  open import Data.Unit hiding (_≤_)
  open import Data.Sum
    using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
  open import Function using (_∘′_)

  module Presheaf where
  {- Machinery for interpretations -}

    record 𝒫 : Set₁ where
      field
        In   : Ctx → Set
        Wken : ∀ {Δ Γ} (Γ⊆Δ : Γ ⊆ Δ) → (In Δ → In Γ)

    open 𝒫

    -- natural transformation
    _→∙_ : 𝒫 → 𝒫 → Set
    (P →∙ Q) = ∀ {Γ} → P .In Γ → Q .In Γ

    _×ᴾ_ : 𝒫 → 𝒫 → 𝒫
    In (P ×ᴾ Q) Γ                 = (In P Γ) × (In Q Γ)
    Wken (P ×ᴾ Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

    _⇒ᴾ_ :  𝒫 → 𝒫 → 𝒫
    In (P ⇒ᴾ Q) Γ             = ∀ {Δ} → Δ ⊆ Γ → P .In Δ → Q .In Δ
    (P ⇒ᴾ Q) .Wken Γ⊆Δ₁ f Δ⊆Γ = f (⊆-trans Δ⊆Γ  Γ⊆Δ₁)

    _+ᴾ_ :  𝒫 → 𝒫 → 𝒫
    In (P +ᴾ Q) Γ    = (In P Γ) ⊎ (In Q Γ)
    (P +ᴾ Q) .Wken Γ⊆Δ = [ inj₁ ∘′ Wken P Γ⊆Δ , inj₂ ∘′ Wken Q Γ⊆Δ  ]′ 

    𝟙ᴾ : 𝒫
    𝟙ᴾ = record { In = λ _ → ⊤ ; Wken = λ {Δ} {Γ} Γ⊆Δ _ → tt }

  open Presheaf
  open 𝒫

  module CoverMonad where

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

    up𝒞 : ∀ {ℓᴸ ℓᴴ} {A} → ℓᴸ ⊑ ℓᴴ → (𝒞ᴾ ℓᴸ A →∙ 𝒞ᴾ ℓᴴ A)
    up𝒞 L⊑H (return x)  = return x
    up𝒞 L⊑H (bind p n k)  = bind (⊑-trans p L⊑H) n (up𝒞 L⊑H k)
    up𝒞 L⊑H (branch x c₁ c₂) = branch x (up𝒞 L⊑H c₁) (up𝒞 L⊑H c₂)

  open CoverMonad public

  -- decision monad for coproducts
  module DecMonad where

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

  
  open DecMonad

  module Interpretation where

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

  open Interpretation public

  module DecMonadOps where

  run𝒟Nf : ∀ {a : Type} → 𝒟ᴾ (Nfᴾ a) →∙ (Nfᴾ a)
  run𝒟Nf (return x) = x
  run𝒟Nf (branch x m m₁) = case x (run𝒟Nf m) (run𝒟Nf m₁)

  run𝒟 : ∀ {a : Type} → 𝒟ᴾ ⟦ a ⟧ →∙ ⟦ a ⟧
  run𝒟 {𝟙}      _ = tt
  run𝒟 {𝕓}      m = run𝒟Nf m
  run𝒟 {a + b}  m = join𝒟 m
  run𝒟 {a ⇒ b}  m = λ e x → run𝒟 {b} (run𝒟⇒ m e (return x))
    where
    run𝒟⇒ : 𝒟ᴾ ⟦ a ⇒ b ⟧ →∙ (𝒟ᴾ ⟦ a ⟧ ⇒ᴾ 𝒟ᴾ ⟦ b ⟧)
    run𝒟⇒ (return f) e x = mapExp𝒟 f e x
    run𝒟⇒ (branch n c₁ c₂) e x =
      branch (wkenNe e n)
        (run𝒟⇒ c₁ (keep e) (wken𝒟 (drop ⊆-refl) x))
        (run𝒟⇒ c₂ (keep e) (wken𝒟 (drop ⊆-refl) x))
  run𝒟 {⟨ ℓ ⟩ a} m = run𝒟𝒞 m
    where
    run𝒟𝒞 : 𝒟ᴾ (𝒞ᴾ ℓ ⟦ a ⟧) →∙ (𝒞ᴾ ℓ ⟦ a ⟧)
    run𝒟𝒞 (return x) = x
    run𝒟𝒞 (branch x c₁ c₂) = branch x (run𝒟𝒞 c₁) (run𝒟𝒞 c₂)

  open DecMonadOps
  module NbE where

    open 𝒫

    lookup : ∀ {a Γ} → a ∈ Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    lookup ze     (_ , v) = v
    lookup (su v) (γ , _) = lookup v γ

    eval : ∀ {a Γ} → Term a Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    eval unit _ = tt
    eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
    eval (var x) γ            = lookup x γ
    eval (t ∙ u) γ            = (eval t γ) ⊆-refl (eval u γ)
    eval (η t) γ              = return (eval t γ)
    eval {Γ = Γ} (t ≫= m) γ  = bindExp𝒞 (λ e a → eval m (Wken ⟦ Γ ⟧ₑ e γ , a)) ⊆-refl (eval t γ)
    eval (c ↑ t) γ            = up𝒞 c (eval t γ)
    eval (inl t) γ            = return (inj₁ (eval t γ))
    eval (inr t) γ            = return (inj₂ (eval t γ))
    eval {a} {Γ} (case {_} {b} {c} t t₁ t₂) {Δ} γ =
      run𝒟 {a} (mapExp𝒟 match ⊆-refl (eval t γ))
      where
      match : ((⟦ b ⟧ +ᴾ ⟦ c ⟧) ⇒ᴾ ⟦ a ⟧) .In Δ
      match e (inj₁ x) = eval t₁ ((Wken ⟦ Γ ⟧ₑ e γ) , x)
      match e (inj₂ y) = eval t₂ ((Wken ⟦ Γ ⟧ₑ e γ) , y)

    mutual

      reifyVal : ∀ {a} → ⟦ a ⟧ →∙ Nfᴾ a
      reifyVal {𝟙} x      = unit
      reifyVal {𝕓} x      = x
      reifyVal {a ⇒ b} f  = `λ (reifyVal (f (drop ⊆-refl) (reflect {a} (var ze))))
      reifyVal {⟨ a ⟩ ℓ} m = reifyVal𝒞 m
      reifyVal {a + b}  m = run𝒟Nf (map𝒟 reifySum m)

      reifyVal𝒟 : ∀ {a} → 𝒟ᴾ ⟦ a ⟧ →∙ Nfᴾ a
      reifyVal𝒟 {a} m = run𝒟Nf {a} (map𝒟 reifyVal m)

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
      idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop ⊆-refl) (idSubst Γ) , reflect {T} (var ze)

      reify : ∀{a Γ} → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧) → Nf a Γ
      reify {a} {Γ} f = reifyVal (f (idSubst Γ))

      norm : ∀ {a} → Termᴾ a →∙ Nfᴾ a
      norm t = reify (eval t)

  open NbE public

  module Const where

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

  open Const public

  module NI where

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
    Var-Sec (p `, (⟨⟩ q)) (⟨ t ⟩ x) ze = ? -- ⊑-trans q x
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
    ... | ⟨⟩ s = inj₂ (⊑-trans ? (⊑-trans r q))

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

    open import Data.Empty
    open import Relation.Nullary

  open NI public

  module Neutrality where

    open import Data.Empty
    open import Relation.Nullary

    emptyNe : ∀ {a} → ¬ (Ne a Ø)
    emptyNe (var ())
    emptyNe (x ∙ _) = emptyNe x

    BinOp = Type → Type → Type

    data _⊲_ : Type → Type → Set where
      refl  : ∀{a} → a ⊲ a
      -- sbl⇒  : ∀ {a b c} → a ⊲ b → a ⊲ (b ⇒ c)
      sbr⇒  : ∀ {a b c} → a ⊲ c → a ⊲ (b ⇒ c)
      -- sbl+  : ∀ {a b c} → a ⊲ b → a ⊲ (b + c)
      -- sbr+  : ∀ {a b c} → a ⊲ c → a ⊲ (b + c)

    postulate
      ⊲-trans : RB.Transitive _⊲_

    data _⊲ᶜ_ : Type → Ctx → Set where
      here  :  ∀ {a b} {Γ} → a ⊲ b  → a ⊲ᶜ (Γ `, b)
      there :  ∀ {a b} {Γ} → a ⊲ᶜ Γ → a ⊲ᶜ (Γ `, b)

    neutrVar : ∀ {a} {Γ} → a ∈ Γ → a ⊲ᶜ Γ
    neutrVar ze = here refl
    neutrVar (su v) = there (neutrVar v)

    neutr⇒ : ∀ {a b c} → (b ⇒ c) ⊲ a → c ⊲ a
    neutr⇒ refl     = sbr⇒ refl
    -- neutr⇒ (sbl⇒ p) = sbl⇒ (neutr⇒ p)
    neutr⇒ (sbr⇒ p) = sbr⇒ (neutr⇒ p)
    -- neutr⇒ (sbr+ p) = sbr+ (neutr⇒ p)
    -- neutr⇒ (sbl+ p) = sbl+ (neutr⇒ p)

    ⊲-lift : ∀ {b a} {Γ} → b ⊲ a → a ⊲ᶜ Γ → b ⊲ᶜ Γ
    ⊲-lift p (here q)  = here (⊲-trans p q)
    ⊲-lift p (there q) = there (⊲-lift p q)

    neutrality : ∀ {a} {Γ} → Ne a Γ → a ⊲ᶜ Γ
    neutrality (var x) = neutrVar x
    neutrality (x ∙ n) = ⊲-lift (sbr⇒ refl) (neutrality x)

  open Neutrality public

  module Substitution where

    infixr 6 _ₑ∘_ _∘ₑ_ _∘_

    data Sub (Γ : Ctx) : Ctx → Set where
      Ø    : Sub Γ Ø
      _`,_ : ∀ {a Δ} → Sub Γ Δ → Term a Γ → Sub Γ (Δ `, a)

    _∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Γ ⊆ Δ → Sub Γ Σ
    Ø        ∘ₑ δ = Ø
    (s `, t) ∘ₑ δ = (s ∘ₑ δ) `, wkenTm δ t

    _ₑ∘_ : ∀ {Γ Δ Σ} → Δ ⊆ Σ → Sub Γ Δ → Sub Γ Σ
    base   ₑ∘ s        = s
    keep e ₑ∘ (s `, t) = (e ₑ∘ s) `, t
    drop e ₑ∘ (s `, t) = e ₑ∘ s

    dropˢ : ∀ {a Γ Δ} → Sub Γ Δ → Sub (Γ `, a) Δ
    dropˢ σ = σ ∘ₑ drop ⊆-refl

    keepˢ : ∀ {Γ Δ} {a} → Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
    keepˢ σ = dropˢ σ `, var ze

    ⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → Γ ⊆ Δ → Sub Γ Δ
    ⌜ base   ⌝ᵒᵖᵉ = Ø
    ⌜ drop σ ⌝ᵒᵖᵉ = dropˢ ⌜ σ ⌝ᵒᵖᵉ
    ⌜ keep σ ⌝ᵒᵖᵉ = keepˢ ⌜ σ ⌝ᵒᵖᵉ

    -- Action on ∈ and Tm
    ∈ : ∀ {Γ Δ} {a} → Sub Γ Δ → a ∈ Δ → Term a Γ
    ∈ (s `, t) ze     = t
    ∈ (s `, x) (su e) = ∈ s e

    subst : ∀ {Γ Δ} {a} → Sub Γ Δ → Term a Δ → Term a Γ
    subst s unit = unit
    subst s (`λ t) = `λ (subst (keepˢ s) t)
    subst s (var x)  = ∈ s x
    subst s (t ∙ u)  = subst s t ∙ subst s u
    subst s (c ↑ t)  = c ↑ subst s t
    subst s (η t)    = η (subst s t)
    subst s (m ≫= f) = (subst s m) ≫= subst (keepˢ s) f
    subst s (inl t) = inl (subst s t)
    subst s (inr t) = inr (subst s t)
    subst s (case t t₁ t₂) = case (subst s t) (subst (keepˢ s) t₁) (subst (keepˢ s) t₂)

    -- Identity and composition
    id : ∀ {Γ} → Sub Γ Γ
    id {Ø}     = Ø
    id {Γ `, a} = keepˢ id

    _∘_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
    Ø       ∘ δ  = Ø
    (s `, t) ∘ δ = (s ∘ δ) `, subst δ t

  open Substitution
  
  module Conversion where

    open import Function using (_∋_)

    data _≈_ {Γ} : ∀ {τ} → Term τ Γ → Term τ Γ → Set where

      -- λ/ reduction
      ⇒β-≈      : ∀ {a b} → {t : Term b (Γ `, a)} {u : Term a Γ}
                → ((`λ t) ∙ u) ≈ subst (id `, u) t

      ⇒η-≈      : ∀ {a b} → {t : Term (a ⇒ b) Γ}
                → t  ≈ `λ (wkenTm (drop ⊆-refl) t ∙ (var ze))

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
                → (η x ≫= f) ≈ subst (id `, x) f

      ⟨⟩η-≈     : ∀ {a} {ℓ} → {t : Term (⟨ ℓ ⟩ a) Γ}
                → t ≈ (t ≫= η (var ze))

      ⟨⟩γ-≈     : ∀ {a b c} {ℓ} → {t₁ : Term (⟨ ℓ ⟩ a) Γ}
                                  {t₂ : Term (⟨ ℓ ⟩ b) (Γ `, a)}
                                  {t₃ : Term (⟨ ℓ ⟩ c) (Γ `, b)}
                → (t₁ ≫= (t₂ ≫= wkenTm (keep (drop ⊆-refl)) t₃)) ≈ ((t₁ ≫= t₂) ≫= t₃)

      -- Up laws

      ↑γ₁-≈ : ∀ {a} {ℓᴸ ℓᴴ} → {t : Term a Γ} {p : ℓᴸ ⊑ ℓᴴ}
                → (p ↑ η t) ≈ η t
      ↑γ₂-≈ : ∀ {a b} {ℓᴸ ℓᴴ} → {t₁ : Term (⟨ ℓᴸ ⟩ a) Γ} {t₂ : Term (⟨ ℓᴸ ⟩ (⟨ ℓᴸ ⟩ b)) (Γ `, a)} {p : ℓᴸ ⊑ ℓᴴ} 
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

  open Conversion public


  module Consistency where

    open import Data.Product

    inv-wken : ∀ {a} {Γ} {t₁ t₂ : Term a Γ}
                 {Δ : Ctx} {e : Δ ⊆ Γ}
             → t₁ ≈ t₂
             → wkenTm e t₁ ≈ wkenTm e t₂
    inv-wken ⇒β-≈ = {!!}
    inv-wken ⇒η-≈ = {!!}
    inv-wken (∙-≈ x x₁) = ∙-≈ (inv-wken x) (inv-wken x₁)
    inv-wken (λ-≈ x) = λ-≈ (inv-wken x)
    inv-wken ⟨⟩β-≈ = {!!}
    inv-wken ⟨⟩η-≈ = ⟨⟩η-≈
    inv-wken ⟨⟩γ-≈ = {!!}
    inv-wken (η-≈ x) = η-≈ (inv-wken x)
    inv-wken (≫=-≈ x x₁) = ≫=-≈ (inv-wken x) (inv-wken x₁)
    inv-wken (↑-≈ x) = ↑-≈ (inv-wken x)
    inv-wken (inl-≈ x) = inl-≈ (inv-wken x)
    inv-wken (inr-≈ x) = inr-≈ (inv-wken x)
    inv-wken (case-≈ x x₁ x₂) = case-≈ (inv-wken x) (inv-wken x₁) (inv-wken x₂)
    inv-wken ≈-refl = ≈-refl
    inv-wken (≈-sym x) = ≈-sym (inv-wken x)
    inv-wken (≈-trans x x₁) = ≈-trans (inv-wken x) (inv-wken x₁)

    ----------------------
    -- Logical relations
    ----------------------

    R𝒟 : ∀ {Γ a} {A}
         → (Rl : ∀ {Δ} → Term a Δ → In A Δ → Set)
         → Term a Γ → 𝒟 A Γ → Set
    R𝒟 Rl t (return v)       =
      Rl t v
    R𝒟 Rl t (branch x d₁ d₂) =
      ∃₂ λ t₁ t₂
      → R𝒟 Rl t₁ d₁
      × R𝒟 Rl t₂ d₂
      × t ≈ case (qNe x) t₁ t₂

    R𝒞 : ∀ {Γ a} {A} {ℓ}
         → (Rl : ∀ {Δ} → Term (⟨ ℓ ⟩ a) Δ → In A Δ → Set)
         → Term (⟨ ℓ ⟩ a) Γ → 𝒞 A ℓ Γ → Set
    R𝒞 Rl t (return v)      =
      Rl t v
    R𝒞 Rl t (bind p n m)   =
      ∃ λ t'
      → R𝒞 Rl t' m
      × t ≈ ((p ↑ qNe n) ≫= t')
    R𝒞 Rl t (branch x m₁ m₂) =
      ∃₂ λ t₁ t₂
      → R𝒞 Rl t₁ m₁
      × R𝒞 Rl t₂ m₂
      × t ≈ case (qNe x) t₁ t₂

    mutual

      Rl₊ : ∀ {Γ a b} → Term (a + b) Γ  → In (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ → Set
      Rl₊ t (inj₁ x) = ∃ λ t' → R t' x × (t ≈ inl t')
      Rl₊ t (inj₂ x) = ∃ λ t' → R t' x × (t ≈ inr t')

      R₊ : ∀ {Γ a b} → Term (a + b) Γ  → 𝒟 (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ → Set
      R₊ t v = R𝒟 Rl₊ t v

      Rl⟨⟩  : ∀ {Γ a} {ℓ} → Term (⟨ ℓ ⟩ a) Γ → In ⟦ a ⟧ Γ → Set
      Rl⟨⟩ t v = ∃ λ t' → R t' v × t ≈ η t'

      R⟨⟩ : ∀ {Γ} {a} {ℓ} → Term (⟨ ℓ ⟩ a) Γ  → 𝒞 ⟦ a ⟧ ℓ Γ → Set
      R⟨⟩ t v = R𝒞 Rl⟨⟩ t v

      R : ∀ {a} {Γ} → Term a Γ → In ⟦ a ⟧ Γ → Set
      R {𝟙}      _ _  =
        ⊤
      R {𝕓}      t n  =
        t ≈ qNf n
      R {a ⇒ b} {Γ} f f' =
         ∀ {Δ t t'} → (e : Δ ⊆ Γ) → R t t' → R (wkenTm e f ∙ t) (f' e t')
      R {a + b}  t v  =
        R₊ t v
      R {⟨ ℓ ⟩ a} t v  =
        R⟨⟩ t v

    Rs : ∀ {Γ Δ} → Sub Δ Γ → In ⟦ Γ ⟧ₑ Δ → Set
    Rs Ø        tt        = ⊤
    Rs (σ `, v) (σ' , v') = Rs σ σ' × R v v'

    ---------------------
    -- Invariance lemma
    ---------------------

    -- R𝒟 Rl₊ is invariant under conversion by ≈

    inv₊ : ∀ {a b} {Γ} {t₁ t₂ : Term (a + b) Γ}
         {v : 𝒟 (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ}
       → t₁ ≈ t₂
       → R𝒟 Rl₊ t₁ v
       → R𝒟 Rl₊ t₂ v
    inv₊ {v = return (inj₁ x)} p (t , q , r) =
      t , q , ≈-trans (≈-sym p) r
    inv₊ {v = return (inj₂ y)} p (t , q , r) =
      t , q , ≈-trans (≈-sym p) r
    inv₊ {v = branch x v v₁} p (t₁ , t₂ , q₁ , q₂ , r) =
      t₁ , t₂ , q₁ , q₂ , ≈-trans (≈-sym p) r

     -- R𝒞 Rl⟨⟩ is invariant under conversion by ≈

    inv⟨⟩ : ∀ {a} {Γ} {ℓ} {t₁ t₂ : Term (⟨ ℓ ⟩ a) Γ}
         {v : 𝒞 ⟦ a ⟧ ℓ Γ}
       → t₁ ≈ t₂
       → R𝒞 Rl⟨⟩ t₁ v
       → R𝒞 Rl⟨⟩ t₂ v
    inv⟨⟩ {v = return x} p (t , q , r) =
      t , q , ≈-trans (≈-sym p) r
    inv⟨⟩ {v = branch x m₁ m₂} p (t₁ , t₂ , q₁ , q₂ , r) =
      t₁ , t₂ , q₁ , q₂ , ≈-trans (≈-sym p) r
    inv⟨⟩ {v = bind c n m} p (t₁ , q , r) =
      t₁ , q , ≈-trans (≈-sym p) r

    -- R is invariant under conversion by ≈

    inv : ∀ {a} {Γ} {t₁ t₂ :  Term a Γ} {v : In ⟦ a ⟧ Γ}
        → t₁ ≈ t₂
        → R t₁ v
        → R t₂ v
    inv {𝟙} p q =
      tt
    inv {𝕓} p q =
      ≈-trans (≈-sym p) q
    inv {a ⇒ b}  p q =
      λ  e r → inv {b} (∙-≈ {!!} ≈-refl) (q e r)
    inv {a + b} {v = v} p q =
      inv₊ {v = v} p q
    inv {⟨ ℓ ⟩ a} {v = v} p q =
      inv⟨⟩ {v = v} p q

    ---------------------------------------------
    -- Weakening preserves relations
    ---------------------------------------------

    wkPresR₊ : ∀ {a b} {Γ Δ} {t :  Term (a + b) Γ}
             {v : 𝒟 (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ}  {e : Δ ⊆ Γ}
        -- need one more argument
        → R t v
        → R (wkenTm e t) (wken𝒟 e v)
    wkPresR₊ {a} {b} {v = return x}       r =
       {!!}
    wkPresR₊ {a} {b} {v = branch x v₁ v₂} {e} (t₁ , t₂ , r₁ , r₂ , p) =
      wkenTm (keep e) t₁
      , (wkenTm (keep e) t₂)
      , wkPresR₊ {a} {b} {v = v₁} r₁
      , wkPresR₊ {a} {b} {v = v₂} r₂
      , {!!}

    wkPresR⟨⟩ : ∀ {a} {ℓ} {Γ Δ} {t :  Term (⟨ ℓ ⟩ a) Γ}
             {v : 𝒞 ⟦ a ⟧ ℓ Γ}  {e : Δ ⊆ Γ}
        → R t v
        → R (wkenTm e t) (wken𝒞 e v)
    wkPresR⟨⟩ r = {!!}
    
    wkPresR : ∀ {a} {Γ Δ} {t :  Term a Γ} {v : In ⟦ a ⟧ Γ} {e : Δ ⊆ Γ}
        → R t v
        → R (wkenTm e t) (Wken ⟦ a ⟧ e v)
    wkPresR {𝟙}              r = tt
    wkPresR {𝕓}              r = {!!}
    wkPresR {a ⇒ b} {e = e}  r = λ e' vₐ →
      inv {b}
        {!!}
        (r (⊆-trans e' e) vₐ)
    wkPresR {a + b}  {v = v} r = wkPresR₊ {a} {b} {v = v} r
    wkPresR {⟨ ℓ ⟩ a} {v = v} r = wkPresR⟨⟩ {a} {ℓ} {v = v} r
    
    ---------------------------------------------
    -- Fundamental theorem of logical relations
    ---------------------------------------------

    Fund : ∀ {Γ} {a} (t : Term a Γ) → Set
    Fund {Γ} {a} t =
      ∀ {Δ} {σ : Sub Δ Γ} {σ' : ⟦ Γ ⟧ₑ .In Δ}
     → Rs σ σ'
     → R (subst σ t) (eval t σ')

    corrEval : ∀ {Γ} {a}
      → (t : Term a Γ)
      → Fund t
    corrEval {Γ} {𝟙} t {Δ} {σ} {σ'} x = {!t!}
    corrEval {Γ} {𝕓} t {Δ} {σ} {σ'} x = {!!}
    corrEval {Γ} {a ⇒ a₁} t {Δ} {σ} {σ'} x = {!!}
    corrEval {Γ} {a + a₁} t {Δ} {σ} {σ'} x = {!!}
    corrEval {Γ} {⟨ ℓ ⟩ a} t {Δ} {σ} {σ'} x = {!!}

    ---------------------------------
    -- Correctness of normalization
    ---------------------------------

    corrReify : ∀ {Γ} {a}
      → {t : Term a Γ}
      → Fund t
      → t ≈ qNf (reify (eval t))
    corrReify {Γ} {.𝟙} {unit} f = {!!}
    corrReify {Γ} {.(_ ⇒ _)} {`λ t} f = {!!}
    corrReify {Γ} {a} {var x} f = {!!}
    corrReify {Γ} {a} {t ∙ t₁} f = {!!}
    corrReify {Γ} {.(⟨ _ ⟩ _)} {x ↑ t} f = {!!}
    corrReify {Γ} {.(⟨ _ ⟩ _)} {η t} f = {!!}
    corrReify {Γ} {.(⟨ _ ⟩ _)} {t ≫= t₁} f = {!!}
    corrReify {Γ} {.(_ + _)} {inl t} f = {!!}
    corrReify {Γ} {.(_ + _)} {inr t} f = {!!}
    corrReify {Γ} {a} {case t t₁ t₂} f = {!!}

    consistent : ∀ {Γ} {a}
      → (t : Term a Γ)
      → t ≈ qNf (norm t)
    consistent t = corrReify (corrEval t)

  open Consistency public

  -------------------------------------
  -- Noninterference theorem for terms
  -------------------------------------

  open import Relation.Binary.PropositionalEquality hiding (subst)

  ≡→≈ :  ∀ {Γ a} → {m n : Nf Γ a} → m ≡ n → qNf m ≈ qNf n
  ≡→≈ refl = ≈-refl

  ≡→≈' :  ∀ {Γ a} → {m n : Term Γ a} → m ≡ n → m ≈ n
  ≡→≈' refl = ≈-refl
  -- a weaker version of `IsConstTm`

  IsConstTm' : ∀ {Γ a} → Term a Γ → Set
  IsConstTm' {Γ} {a} t = Σ (Term a Ø) λ t' → wkenTm ⊆-term t' ≈ t

  -- Naturality condition of the `qNf` natural transformation
  -- (should be provable, also required for `consistent` I think)
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
    nat-qNf {e = e} (case n c₁ c₂) with (nat-qNe {e = e} n) | nat-qNf {e = keep e} c₁ | nat-qNf {e = keep e} c₂
    ... | nn | nc₁ | nc₂ = {!cong !}


  IsConstSub : ∀ {Γ} {a} → (t : Term a Γ) → Set
  IsConstSub {Γ} {a} t = Σ (Term a Ø) λ t' → subst Ø t' ≈ t

  --_∘_ : ∀ {Γ Δ Σ} → Sub Γ Δ →  Sub Δ Σ → Sub Γ Σ
  -- Ø       ∘ δ  = Ø
  -- (s `, t) ∘ δ = (s ∘ δ) `, subst δ t
  substppp : ∀ {Σ Δ Γ} {a} {t : Term a Σ} {σ : Sub Δ Σ} {σ′ : Sub Γ Δ} → subst σ′ (subst σ t) ≈ subst (σ ∘ σ′) t
  substppp = {!!}

  final : ∀ {Γ} → (σ : Sub Γ Ø) → σ ≡ Ø
  final Ø = refl

  cong-≈ : ∀ {Γ Δ} {a} {σ : Sub Δ Γ} → {t₁ t₂ : Term a Γ} → t₁ ≈ t₂ → subst σ t₁ ≈  subst σ t₂
  cong-≈ ⇒β-≈ = {!!}
  cong-≈ ⇒η-≈ = {!!}
  cong-≈ (∙-≈ x x₁) = ∙-≈ (cong-≈ x) (cong-≈ x₁)
  cong-≈ (λ-≈ x) = λ-≈ (cong-≈ x)
  cong-≈ ⟨⟩β-≈ = {!!}
  cong-≈ ⟨⟩η-≈ = ⟨⟩η-≈
  cong-≈ ⟨⟩γ-≈ = {!!}
  cong-≈ ↑γ₁-≈ = ↑γ₁-≈
  cong-≈ ↑γ₂-≈ = ↑γ₂-≈
  cong-≈ (η-≈ x) = η-≈ (cong-≈ x)
  cong-≈ (≫=-≈ x x₁) = ≫=-≈ (cong-≈ x) (cong-≈ x₁)
  cong-≈ (↑-≈ x) = ↑-≈ (cong-≈ x)
  cong-≈ (inl-≈ x) = inl-≈ (cong-≈ x)
  cong-≈ (inr-≈ x) = inr-≈ (cong-≈ x)
  cong-≈ (case-≈ x x₁ x₂) = case-≈ (cong-≈ x) (cong-≈ x₁) (cong-≈ x₂)
  cong-≈ ≈-refl = ≈-refl
  cong-≈ (≈-sym x) = ≈-sym (cong-≈ x)
  cong-≈ (≈-trans x x₁) = ≈-trans (cong-≈ x) (cong-≈ x₁)

  PPPP : ∀ {Δ Γ} {a} (t : Term a Γ) → (p : IsConstSub t) → (σ : Sub Δ Γ) → subst σ t ≈ subst Ø (proj₁ p)
  PPPP t (t' , pr) σ with cong-≈ {σ = σ} pr
  ... | a with substppp {t = t'} {σ = Ø} {σ′ = σ}
  ... | b =  ≈-trans (≈-sym a) b

  -- Ultimate noninterference theorem
  Tm-NI : ∀ {Γ} {a} {ℓⁱ ℓᵒ}
      → ⟨ ℓⁱ ⟩ˢᶜ Γ           -- input is atleast ℓⁱ-sensitive
      → Ground a → Tr a ℓᵒ  -- output is ground, and transparent at ℓᵒ
      → (t : Term a Γ) → (IsConstTm' t) ⊎ (ℓⁱ ⊑ ℓᵒ)
  Tm-NI p g q t with Nf-NI p g q (norm t)
  Tm-NI p g q t | inj₁ (n , r) = inj₁ ((qNf n) ,
    ≈-sym
      (≈-trans (consistent _)
      ((≈-sym
            (≈-trans
              ({!!})
              (≡→≈ r))))))
  Tm-NI p g q t | inj₂ y = inj₂ y


  Tm-NI' : ∀ {Δ Γ} {a} {ℓⁱ ℓᵒ}
      → (t : Term a Γ)
      → (σ : Sub Δ Γ)       -- substitution for part of input which is not sensitive
      → ⟨ ℓⁱ ⟩ˢᶜ Δ           -- remaining input is atleast ℓⁱ-sensitive
      → Ground a → Tr a ℓᵒ  -- output is ground, and transparent at ℓᵒ
      → (IsConstTm' (subst σ t)) ⊎ (ℓⁱ ⊑ ℓᵒ)
  Tm-NI' t σ s gr tr = Tm-NI s gr tr _

  open import Relation.Nullary
  
       
  -- PPPP : ∀ {Δ Γ} {a} (t : Term a Γ) → (p : IsConstSub t) → (σ : Sub Δ Γ) → subst σ t ≈ subst Ø (proj₁ p)
  -- PPPP t (t' , pr) σ with cong-≈ {σ = σ} pr
  -- ... | a with substppp {t = t'} {σ = Ø} {σ′ = σ}
  -- ... | b =  ≈-trans (≈-sym a) b

  postulate assume : ∀ {Γ} {a} → (t : Term a Γ) → IsConstTm' t -> IsConstSub t

  NI : ∀ {Δ Γ} {a} {ℓᴸ ℓᴴ}
         → ¬ (ℓᴴ ⊑ ℓᴸ)
         → (t    : Term a Γ)
         → (σ σ′ : Sub Δ Γ)
         → ⟨ ℓᴴ ⟩ˢᶜ Γ
         → Ground a → Tr a ℓᴸ
         → subst σ t ≈ subst σ′ t
  NI ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr
    with Tm-NI pr gr tr t
  NI ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr | inj₁ pp
    with assume t pp
  ... | ppp with PPPP t ppp σ | PPPP t ppp σ′
  ... | a | b = ≈-trans a (≈-sym b )
  NI ¬ℓᴴ⊑ℓᴸ t σ σ′ pr gr tr | inj₂ y = {!!}
