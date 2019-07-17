module Correctness where

  open import Preorder

  open import Type
  open import Variable
  open import Embedding
  open import Term
  open import NormalForm
  open import Presheaf
  open import Substitution
  open import Conversion
  open import NBE

  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality hiding (subst)

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
    λ  e r → inv {b} (∙-≈ (inv-wken p) ≈-refl) (q e r)
  inv {a + b} {v = v} p q =
    inv₊ {v = v} p q
  inv {⟨ ℓ ⟩ a} {v = v} p q =
    inv⟨⟩ {v = v} p q

  ---------------------------------------------
  -- Weakening preserves relations
  ---------------------------------------------

  mutual
    wkPresR₊ : ∀ {a b} {Γ Δ} {t :  Term (a + b) Γ}
            {v : 𝒟 (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ}  {e : Δ ⊆ Γ}
        → R t v
        → R (wkenTm e t) (wken𝒟 e v)
    wkPresR₊ {a} {b} {v = return (inj₁ x)} {e} (t′ , R₊′ , p)
      = wkenTm e t′ , wkPresR {t = t′} R₊′ ,
        ≈-trans (inv-wken p) (inl-≈ ≈-refl)
    wkPresR₊ {a} {b} {v = return (inj₂ y)} {e} (t′ , R₊′ , p)
      = wkenTm e t′ , wkPresR {t = t′} R₊′ ,
        ≈-trans (inv-wken p) (inr-≈ ≈-refl)
    wkPresR₊ {a} {b} {v = branch n v₁ v₂} {e} (t₁ , t₂ , R₊₁ , R₊₂ , p) =
      wkenTm (keep e) t₁
      , (wkenTm (keep e) t₂)
      , wkPresR₊ {a} {b} {v = v₁} R₊₁
      , wkPresR₊ {a} {b} {v = v₂} R₊₂
      , ≈-trans (inv-wken p) (≡⇒≈ (cong (λ n′ → case n′ (wkenTm (keep e) t₁) (wkenTm (keep e) t₂))
                                  (nat-qNe n)))

    wkPresR⟨⟩ : ∀ {a} {ℓ} {Γ Δ} {t :  Term (⟨ ℓ ⟩ a) Γ}
            {v : 𝒞 ⟦ a ⟧ ℓ Γ}  {e : Δ ⊆ Γ}
        → R t v
        → R (wkenTm e t) (wken𝒞 e v)
    wkPresR⟨⟩ {t = t} {return x} {e} (t′ , Rt′ , p)
      = wkenTm e t′ , wkPresR {t = t′} Rt′ , (inv-wken p)
    wkPresR⟨⟩ {t = t} {bind c n v} {e} (t′ , R𝒞′ , p)
          = wkenTm (keep e) t′  , wkPresR⟨⟩ {t = t′} {v = v} {e = keep e} R𝒞′ ,
            ≈-trans (inv-wken p ) (≡⇒≈ (cong (λ n′ → (c ↑ n′) ≫= wkenTm (keep e) t′)
                                        (nat-qNe n)))
    wkPresR⟨⟩ {t = t} {branch n v₁ v₂} {e} (t₁ , t₂ , R𝒞₁ , R𝒞₂ , p)
      = (wkenTm (keep e) t₁) , (wkenTm (keep e) t₂)
      , wkPresR⟨⟩ {t = t₁} {v = v₁} {e = keep e} R𝒞₁
      , wkPresR⟨⟩ {t = t₂} {v = v₂} {e = keep e} R𝒞₂
      , ≈-trans (inv-wken p) (≡⇒≈ (cong (λ n′ → case n′ (wkenTm (keep e) t₁) (wkenTm (keep e) t₂))
                                  (nat-qNe n)))

    wkPresR : ∀ {a} {Γ Δ} {t :  Term a Γ} {v : In ⟦ a ⟧ Γ}
            {e : Δ ⊆ Γ}
        → R t v
        → R (wkenTm e t) (Wken ⟦ a ⟧ e v)
    wkPresR {𝟙}              r = tt
    wkPresR {𝕓}     {v = v} {e = e}  r = ≈-trans (inv-wken {e = e} r)
                                                  (≡⇒≈ (nat-qNf v))
    wkPresR {a ⇒ b} {e = e} r {t = t} =  λ e' vₐ →
      inv {b}
        (≡⇒≈ (cong (λ t' → t' ∙ t) (sym (wkenTm-∘ₑ _ e e'))))
        (r (e ∘ₑ e') vₐ)
    wkPresR {a + b}  {v = v} r = wkPresR₊ {a} {b} {v = v} r
    wkPresR {⟨ ℓ ⟩ a} {v = v} r = wkPresR⟨⟩ {a} {ℓ} {v = v} r

  ---------------------------------------------
  -- Fundamental theorem of logical relations
  ---------------------------------------------

  Fund : ∀ {Γ} {a} (t : Term a Γ) → Set
  Fund {Γ} {a} t =
    ∀ {Δ} {σ : Sub Δ Γ} {γ : ⟦ Γ ⟧ₑ .In Δ}
    → Rs σ γ
    → R (subst σ t) (eval t γ)


  corrLookup : ∀ {Γ Δ} {a} {x : a ∈ Γ}
      {σ : Sub Δ Γ} {γ : ⟦ Γ ⟧ₑ .In Δ}
      → Rs σ γ
      → R (∈ₛ σ x) (lookup x γ)
  corrLookup = {!!}

  -- Dibs by Nachi
  corrUp𝒞 : ∀ {ℓᴸ ℓᴴ} {Γ} {a : Type}
          {c : ℓᴸ ⊑ ℓᴴ} {t : Term (⟨ ℓᴸ ⟩ a) Γ}
          {v : 𝒞 ⟦ a ⟧ ℓᴸ Γ} 
        → R𝒞 Rl⟨⟩ t v
        → R𝒞 Rl⟨⟩ (c ↑ t) (up𝒞 c v)
  corrUp𝒞 = {!!}


  corrEval : ∀ {Γ} {a}
    → (t : Term a Γ)
    → Fund t
  corrEval {Γ} {.𝟙} unit {Δ} {σ} {γ}         p = tt
  corrEval {Γ} {.(_ ⇒ _)} (`λ t) {Δ} {σ} {γ} p = {!!}
  corrEval {Γ} {a} (var x) {Δ} {σ} {γ}       p =
    corrLookup {x = x} p
  corrEval {Γ} {a} (t ∙ u) {Δ} {σ} {γ}       p =
    -- needs id law of Tm' presheaf
    inv {a} {!!} (corrEval t p idₑ (corrEval u p))
  corrEval {Γ} {.(⟨ _ ⟩ _)} (_↑_ c t) {Δ} {σ} {γ} p =
    corrUp𝒞 {t = subst σ t} {eval t γ} (corrEval t p)
  corrEval {Γ} {.(⟨ _ ⟩ _)} (η t) {Δ} {σ} {γ} p =
    _ , (corrEval t p , ≈-refl) 
  corrEval {Γ} {.(⟨ _ ⟩ _)} (t ≫= t₁) {Δ} {σ} {γ} p =
    {!!}
  corrEval {Γ} {.(_ + _)} (inl t) {Δ} {σ} {γ} p =
    {!!}
  corrEval {Γ} {.(_ + _)} (inr t) {Δ} {σ} {γ} p =
    {!!}
  corrEval {Γ} {a} (case t t₁ t₂) {Δ} {σ} {γ} p =
    {!!}

  ---------------------------------
  -- Correctness of normalization
  ---------------------------------

  mutual

    corrReflect : ∀ {Γ} {a}
      {n : Ne a Γ}
      → R (qNe n) (reflect n)
    corrReflect {Γ} {𝟙} {n}       = tt
    corrReflect {Γ} {𝕓} {n}       = ≈-refl
    corrReflect {Γ} {a ⇒ b} {n}
      = λ e p → inv {b}
        (∙-≈
          (≡⇒≈ (sym (nat-qNe _)))
          (≈-sym (corrReifyVal p)))
        (corrReflect {a = b})
    corrReflect {Γ} {a + b} {n}
      = _ , _
      , (var ze
        , corrReflect {Γ `, a} {n = var ze}
        , ≈-refl)
      , (var ze
        , corrReflect {Γ `, b} {n = var ze}
        , ≈-refl)
      , {!!} --needs +η-≈
    corrReflect {Γ} {⟨ ℓ ⟩ a} {n}
      = η (var ze)
      , (var ze
        , (corrReflect {Γ `, a} {n = var ze}
        , ≈-refl))
      , ≈-trans ⟨⟩η-≈ (≫=-≈ {!!} ≈-refl) -- needs some rule

    corrReifyVal : ∀ {Γ} {a}
      {t : Term a Γ} {v : ⟦ a ⟧ .In Γ}
      → R t v
      → t ≈ qNf (reifyVal v)
    corrReifyVal {Γ} {𝟙}         p = {!!} --need 𝟙η-≈
    corrReifyVal {Γ} {𝕓}         p = p
    corrReifyVal {Γ} {a ⇒ b} {t} p =
      ≈-trans
        ⇒η-≈
        (λ-≈ (corrReifyVal {a = b}
              (p (drop idₑ) (corrReflect {a = a} {n = var ze})))) 
    corrReifyVal {Γ} {a + a₁}  p = {!!}
    corrReifyVal {Γ} {⟨ ℓ ⟩ a} p = {!t!}

  corrReify : ∀ {Γ} {a}
    → {t : Term a Γ}
    → Fund t
    → t ≈ qNf (reify (eval t))
  corrReify {Γ} {a} {t} f =
    corrReifyVal
      (inv {a} {t₁ = subst idₛ t} {!!} (f {!!}))

  consistent : ∀ {Γ} {a}
    → (t : Term a Γ)
    → t ≈ qNf (norm t)
  consistent t = corrReify (corrEval t)