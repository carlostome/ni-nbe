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

  private
    -- sugar
    _︔_ = trans

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


  R𝒟-⟦⟧ : ∀ {Γ} {a} → Term a Γ → 𝒟 ⟦ a ⟧ Γ → Set
  R𝒟-⟦⟧ = R𝒟 R

  R𝒟-Nfᴾ : ∀ {Γ} {a} → Term a Γ → 𝒟 (Nfᴾ a) Γ → Set
  R𝒟-Nfᴾ = R𝒟 (λ t v → t ≈ qNf v)

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
    λ  e r → inv {b} ((inv-wken p) ∙ ≈-refl) (q e r)
  inv {a + b} {v = v} p q =
    inv₊ {v = v} p q
  inv {⟨ ℓ ⟩ a} {v = v} p q =
    inv⟨⟩ {v = v} p q

  ---------------------------------------------
  -- Weakening preserves relations
  ---------------------------------------------

  mutual
    wkPresR𝒟 : ∀ {a} {A} {Γ Δ}
            {Rl : {Δ₁ : Ctx} → Term a Δ₁ → In A Δ₁ → Set}
            (wkPresRl : ∀ {Σ Γ} {t' : Term a Σ} {x : In A Σ}
              {e : Γ ⊆ Σ} → Rl t' x → Rl (wkenTm e t') (Wken A e x))
            {t :  Term a Γ} {v : 𝒟 A Γ}
        → {e : Δ ⊆ Γ}
        → R𝒟 Rl t v
        → R𝒟 Rl (wkenTm e t) (wken𝒟 e v)
    wkPresR𝒟 {a} {b} wkprl {v = return x} {e} p = wkprl {e = e} p
    wkPresR𝒟 {a} {b} {Rl = Rl} wkprl {t} {v = branch n v₁ v₂} {e} (t₁ , t₂ , p , q , r)
      = wkenTm (keep e) t₁
      , (wkenTm (keep e) t₂)
      , wkPresR𝒟 {Rl = Rl} wkprl {v = v₁} {keep e} p
      , wkPresR𝒟 {Rl = Rl} wkprl {v = v₂} {keep e} q
      , ≈-trans (inv-wken r) (≡⇒≈
        (cong (λ n′ → case n′ (wkenTm (keep e) t₁) (wkenTm (keep e) t₂)) (nat-qNe n)))

    wkPresR₊ : ∀ {a b} {Γ Δ} {t :  Term (a + b) Γ}
            {v : 𝒟 (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ}  {e : Δ ⊆ Γ}
        → R t v
        → R (wkenTm e t) (wken𝒟 e v)
    wkPresR₊ {a} {b} {v = return (inj₁ x)} {e} (t′ , R₊′ , p)
      = wkenTm e t′ , wkPresR {t = t′} R₊′ ,
        ≈-trans (inv-wken p) (inl ≈-refl)
    wkPresR₊ {a} {b} {v = return (inj₂ y)} {e} (t′ , R₊′ , p)
      = wkenTm e t′ , wkPresR {t = t′} R₊′ ,
        ≈-trans (inv-wken p) (inr ≈-refl)
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
      , ≈-trans (inv-wken p)
          (≡⇒≈ (cong (λ n′ → case n′ (wkenTm (keep e) t₁) (wkenTm (keep e) t₂))
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

  Rs-ₛ∘ₑ : ∀ {Γ Δ Σ} {σ : Sub Δ Γ} {γ : ⟦ Γ ⟧ₑ .In Δ} {e : Σ ⊆ Δ}
        → Rs σ γ → Rs (σ ₛ∘ₑ e) (Wken ⟦ Γ ⟧ₑ e γ)
  Rs-ₛ∘ₑ {Ø} {Δ} {Σ₁} {Ø} {γ} {e} x       = x
  Rs-ₛ∘ₑ {Γ `, a} {Δ} {Σ₁} {σ `, t′} {γ , t} {e} (r₁ , r₂)
        = Rs-ₛ∘ₑ r₁ , wkPresR {t = t′} r₂

  corrLookup : ∀ {Γ Δ} {a} {x : a ∈ Γ}
      {σ : Sub Δ Γ} {γ : ⟦ Γ ⟧ₑ .In Δ}
      → Rs σ γ
      → R (∈ₛ σ x) (lookup x γ)
  corrLookup {.(_ `, a)} {Δ} {a} {ze} {_ `, t} {_ , v} (_ , p)
    = p
  corrLookup {.(_ `, _)} {Δ} {a} {su x} {σ `, _} {γ , _} (p , _)
    = corrLookup {x = x} p

  corrUp𝒞 : ∀ {ℓᴸ ℓᴴ} {Γ} {a : Type}
          {c : ℓᴸ ⊑ ℓᴴ} {t : Term (⟨ ℓᴸ ⟩ a) Γ}
          {v : 𝒞 ⟦ a ⟧ ℓᴸ Γ}
        → R𝒞 Rl⟨⟩ t v
        → R𝒞 Rl⟨⟩ (c ↑ t) (up𝒞 c v)
  corrUp𝒞 {c = c} {v = return x} (t , p , q)
    -- key rule: ↑γ₁
    = t , p , ≈-trans (c ↑ q) ↑γ₁
  corrUp𝒞 {c = c} {v = bind x n v'} (t , p , q)
    -- key rule: ↑γ₄
    = (c ↑ t)
    , corrUp𝒞 {t = t} {v = v'} p
    , ≈-trans (c ↑ q) (≈-trans ↑γ₂ (↑γ₄ ≫= ≈-refl))
  corrUp𝒞 {c = c} {v = branch x₁ v₁ v₂}  (t₁ , t₂ , p , q , r)
    -- key rule: +π↑
    = (c ↑ t₁)
    , (c ↑ t₂)
    , corrUp𝒞 {t = t₁} {v = v₁} p
    , corrUp𝒞 {t = t₂} {v = v₂} q
    , ≈-trans (_ ↑ r) +π↑

  open Conversion.SetoidUtil

  corrBindExp𝒞 : ∀ {Γ} {a b} {ℓ}
        (t : Term (⟨ ℓ ⟩ a) Γ)        (v : 𝒞 ⟦ a ⟧ ℓ Γ)
        (u : Term (⟨ ℓ ⟩ b) (Γ `, a)) (f : (⟦ a ⟧ ⇒ᴾ 𝒞ᴾ ℓ ⟦ b ⟧) .In Γ)
        → R t v
        → R (`λ u) f
        → R (t ≫= u) (bindExp𝒞' f v)
  corrBindExp𝒞 {b = b} t (return x) u f (t' , p , q) g
    -- given (p : R t' x) (q : η t' ≈ t)
    -- show: R (t ≫= u) (bindExp𝒞' f (return x))
    -- (which we do using invariance under conversion)
    -- key rule: ⟨⟩β
    = inv⟨⟩ {b} {v = f idₑ x}
        (begin
          (`λ (wkenTm idₑ u) ∙ t')
                  ≈⟨ ⇒β ⟩
          subst (idₛ `, t') (wkenTm idₑ u)
                ≈⟨ ≡⇒≈ (sym (Term-ₑ∘ₛ u _ _)) ⟩
          subst (idₑ ₑ∘ₛ idₛ `, t') u
                ≈⟨ ≡⇒≈ (cong (λ σ → subst (σ `, t') u) (idlₑₛ _)) ⟩
          subst (idₛ `, t') u
                ≈⟨ ≈-sym ⟨⟩β ⟩
          (η t' ≫= u)
                ≈⟨ ≈-sym q ≫= ≈-refl ⟩
          (t ≫= u) ∎)
      (g idₑ p)
  corrBindExp𝒞 {a = a} {b} t (bind c n v') u f (t' , p , q) g
    -- key rule: ⟨⟩γ
    = (t' ≫= wkenTm (keep (drop idₑ)) u)
      -- since bindExp𝒞' over bind is pushed inside,
      -- the induction step is on the continuation (i.e., t'/v')
    , (corrBindExp𝒞 t' v' _ _ p
         λ e x →
           inv⟨⟩ {b} {v = f (drop idₑ ∘ₑ e) _}
             (begin
               (`λ (wkenTm _ u) ∙ _)
                    ≈⟨ `λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl ⟩
               (`λ (wkenTm _ (wkenTm _ u)) ∙ _) ∎ )
         (g (drop idₑ ∘ₑ  e) x))
    , ≈-trans (q ≫= ≈-refl) ⟨⟩γ
  corrBindExp𝒞 {a = a} {b} t (branch x v₁ v₂) u f (t₁ , t₂ , p , q , r) g
    -- key rule: +π≫=
    = (t₁ ≫= wkenTm (keep (drop idₑ)) u)
    , (t₂ ≫= wkenTm (keep (drop idₑ)) u)
      -- identical to the induction step for `bind`
    , corrBindExp𝒞 t₁ v₁ _ _ p
        (λ {_} {_} {vₐ} e x →
          inv⟨⟩ {b} {v = f (drop idₑ ∘ₑ e) vₐ}
            (`λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl) (g (drop idₑ ∘ₑ  e) x))
      -- identical to the induction step for `bind`
    , corrBindExp𝒞 t₂ v₂ _ _ q
        (λ {_} {_} {vₐ} e x →
          inv⟨⟩ {b} {v = f (drop idₑ ∘ₑ e) vₐ}
            (`λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl) (g (drop idₑ ∘ₑ  e) x))
    , ≈-trans (r ≫= ≈-refl) +π≫=

  corrRun𝒟Nf : ∀ {Γ} {a}
    → (t : Term a Γ) (m : 𝒟 (Nfᴾ a) Γ)
    → R𝒟-Nfᴾ t m
    → t ≈ qNf (run𝒟Nf m)
  corrRun𝒟Nf t (return x)       p = p
  corrRun𝒟Nf t (branch x m₁ m₂) (t₁ , t₂ , p , q , r)
    = ≈-trans r (case ≈-refl (corrRun𝒟Nf _ m₁ p) (corrRun𝒟Nf _ m₂ q))

  corrJoin𝒟 : ∀ {Γ} {a} {A}
    → (t : Term a Γ) (m : 𝒟 (𝒟ᴾ A) Γ)
    → {Rᵢ : {Δ : Ctx} → Term a Δ → In A Δ → Set}
    → R𝒟 (R𝒟 Rᵢ) t m
    → R𝒟 Rᵢ t (join𝒟 m)
  corrJoin𝒟 t (return x)       p = p
  corrJoin𝒟 t (branch x m₁ m₂) (t₁ , t₂ , p , q , r)
    = t₁ , t₂ , (corrJoin𝒟 _ m₁ p) , (corrJoin𝒟 _ m₂ q) , r

  corrRun𝒟𝒞 : ∀ {Γ} {a} {A} {ℓ}
    → (t : Term (⟨ ℓ ⟩ a) Γ) (m : 𝒟 (𝒞ᴾ ℓ A) Γ)
    → {Rᵢ : {Δ : Ctx} →  Term (⟨ ℓ ⟩ a) Δ → In A Δ → Set}
    → R𝒟 (R𝒞 Rᵢ) t m
    → R𝒞 Rᵢ t (run𝒟𝒞 m)
  corrRun𝒟𝒞 t (return x)       p = p
  corrRun𝒟𝒞 t (branch x m₁ m₂) (t₁ , t₂ , p , q , r)
    = t₁ , t₂ , (corrRun𝒟𝒞 t₁ m₁ p) , (corrRun𝒟𝒞 t₂ m₂ q) , r


  mutual
    corrRun𝒟⇒ : ∀ {Γ} {a b}
      → (t : Term  (a ⇒ b) Γ) (f : 𝒟 ⟦ a ⇒ b ⟧ Γ )
      → (u : Term a Γ)       (v : 𝒟 ⟦ a ⟧ Γ)
      → R𝒟-⟦⟧ t f
      → R𝒟-⟦⟧ u v
      → R𝒟-⟦⟧ (t ∙ u) (run𝒟⇒ {a} {b} f v)
    corrRun𝒟⇒ {Γ} {a} {b} t (return x) u v p q = inv {b}
      (≡⇒≈ (wkenTm-idₑ _) ∙ ≈-refl)
      (p idₑ (corrRun𝒟 u v q))
    corrRun𝒟⇒ {Γ} {a} {b} t (branch x f₁ f₂) u v (t₁ , t₂ , p , q , r) s
      = (t₁ ∙ wkenTm (drop idₑ) u)
      , (t₂ ∙ wkenTm (drop idₑ) u)
      , corrRun𝒟⇒ t₁ f₁ _ _ p (wkPresR𝒟 {a} (wkPresR {a}) {v = v} s)
      , corrRun𝒟⇒ t₂ f₂ _ _ q (wkPresR𝒟 {a} (wkPresR {a}) {v = v} s)
      , ≈-trans (r ∙ ≈-refl) +π⇒

    corrRun𝒟 : ∀ {Γ} {a}
      → (t : Term a Γ) (v : 𝒟 ⟦ a ⟧ Γ)
      → R𝒟-⟦⟧ t v
      → R t (run𝒟 {a} v)
    corrRun𝒟 {_} {𝟙}       t m p = tt
    corrRun𝒟 {_} {𝕓}       t m p = corrRun𝒟Nf t m p
    corrRun𝒟 {_} {a ⇒ b}   t m p {Γ} {t'} {x} =
      λ e y → corrRun𝒟 {_} {b} (wkenTm e t ∙ t') _
        (corrRun𝒟⇒
          (wkenTm e t)
          (wken𝒟 e m) t'
          (return x)
          (wkPresR𝒟 (wkPresR {a ⇒ b}) {v = m} {e = e} p) y)
    corrRun𝒟 {_} {a + b}   t m p = corrJoin𝒟 t m p
    corrRun𝒟 {_} {⟨ ℓ ⟩ a} t m p = corrRun𝒟𝒞 t m p

  corrCase𝒟 : ∀ {a b c Δ}
    (t : Term (b + c) Δ) (v : 𝒟 (⟦ b ⟧ +ᴾ ⟦ c ⟧) Δ)
    (t₁ : Term a (Δ `, b)) (f : (⟦ b ⟧ ⇒ᴾ ⟦ a ⟧) .In Δ)
    (t₂ : Term a (Δ `, c)) (g : (⟦ c ⟧ ⇒ᴾ ⟦ a ⟧) .In Δ)
    → R t v
    → R (`λ t₁) f
    → R (`λ t₂) g
    → R𝒟 {Δ} {a} {⟦ a ⟧} R
         (case t t₁ t₂)
         (case𝒟 {a} {b} {c} v f g)
  corrCase𝒟 {a = a} t (return (inj₁ x)) t₁ f t₂ g (u , p , q) rt1f rt2g =
    inv {a}
      (≈-trans
        ⇒β
        (≈-sym (≈-trans
          (case q ≈-refl ≈-refl)
          (≈-trans +β₁ (≡⇒≈ ((cong (subst _) (sym (wkenTm-idₑ t₁)))))))))
      (rt1f idₑ p)
  corrCase𝒟 {a = a} t (return (inj₂ y)) t₁ f t₂ g (u , p , q) rt1f rt2g =
    inv {a}
      (≈-trans ⇒β
        (≈-sym (≈-trans
          (case q ≈-refl ≈-refl)
          (≈-trans +β₂ (≡⇒≈ ((cong (subst _) (sym (wkenTm-idₑ t₂)))))))))
      (rt2g idₑ p)
  corrCase𝒟 {a} {b} {c} {Δ} t (branch x v₁ v₂) t₁ f t₂ g (u₁ , u₂ , p , q , r ) rt1f rt2g
    = case u₁
           (wkenTm (keep (drop idₑ)) t₁)
           (wkenTm (keep (drop idₑ)) t₂)
    , case u₂
           (wkenTm (keep (drop idₑ)) t₁)
           (wkenTm (keep (drop idₑ)) t₂)
    , corrCase𝒟 u₁ v₁
           _ (λ e → f (drop idₑ ∘ₑ e))
           _ (λ e → g (drop idₑ ∘ₑ e))
           p
           (λ e r → inv {a} (`λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl) (rt1f (drop idₑ ∘ₑ e) r))
           (λ e r → inv {a} (`λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl) (rt2g (drop idₑ ∘ₑ e) r))
    , corrCase𝒟 u₂ v₂
           _ (λ e → f (drop idₑ ∘ₑ e))
           _ (λ e → g (drop idₑ ∘ₑ e))
           q
           (λ e r → inv {a} (`λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl) (rt1f (drop idₑ ∘ₑ e) r))
           (λ e r → inv {a} (`λ (≡⇒≈ (sym (wkenTm-∘ₑ _ _ _))) ∙ ≈-refl) (rt2g (drop idₑ ∘ₑ e) r))
    , ≈-trans (case r ≈-refl ≈-refl) +π+

  ---------------------------------------------
  -- Fundamental theorem of logical relations
  ---------------------------------------------

  Fund : ∀ {Γ} {a} (t : Term a Γ) → Set
  Fund {Γ} {a} t =
    ∀ {Δ} {σ : Sub Δ Γ} {γ : ⟦ Γ ⟧ₑ .In Δ}
    → Rs σ γ
    → R (subst σ t) (eval t γ)

  corrEval : ∀ {Γ} {a}
    → (t : Term a Γ)
    → Fund t
  corrEval {Γ} {.𝟙} unit {Δ} {σ} {γ}         p = tt
  corrEval {Γ} {.(a ⇒ b)} (`λ {a = a} {b} t) {Δ} {σ} {γ} p {t = t′} {e′}
    = λ e q →
        inv {a = b}
          (≈-trans
            (≡⇒≈
              (trans
                (trans (cong (λ s → subst (s `, t′) t)
                       (trans (trans (trans (sym (idrₛ _))
                              (trans (assₛₑₛ σ idₛ e) (cong (σ ∘ₛ_)
                                     (sym (idlₑₛ _)))))
                              (sym (assₛₑₛ σ (_ `, t′) (drop idₑ))))  (sym (assₛₑₛ (dropˢ σ) (idₛ `, t′) (keep e)))))
                  (Term-∘ₛ t (((dropˢ σ) ₛ∘ₑ keep e) `, (var ze)) (idₛ `, t′)))
                (cong (subst (idₛ `, t′)) (Term-ₛ∘ₑ t (keepˢ σ) (keep e)))))
            (≈-sym ⇒β))
            (corrEval t {σ = (σ ₛ∘ₑ e) `, t′} {γ = Wken ⟦ Γ ⟧ₑ e γ , e′} (Rs-ₛ∘ₑ p , q) )
  corrEval {Γ} {a} (var x) {Δ} {σ} {γ}       p =
    corrLookup {x = x} p
  corrEval {Γ} {a} (t ∙ u) {Δ} {σ} {γ}       p =
    inv {a} ((≡⇒≈ (wkenTm-idₑ _)) ∙ ≈-refl)
      (corrEval t p idₑ (corrEval u p))
  corrEval {Γ} {.(⟨ _ ⟩ _)} (_↑_ c t) {Δ} {σ} {γ} p =
    corrUp𝒞 {t = subst σ t} {eval t γ} (corrEval t p)
  corrEval {Γ} {.(⟨ _ ⟩ _)} (η t) {Δ} {σ} {γ} p =
    _ , (corrEval t p , ≈-refl)
  corrEval {Γ} {(⟨ ℓ ⟩ a)} (t ≫= t₁) {Δ} {σ} {γ} p =
    corrBindExp𝒞
      (subst σ t) (eval t γ) _ _ (corrEval t p)
      λ {_} {t'} {u'} e x →
        inv⟨⟩ {a} {v = eval t₁ (Wken ⟦ Γ ⟧ₑ e γ , u')}
          -- prove: subst ... t₁ ≈ (`λ (wkenTm ... (subst ... t₁)) ∙ ...)
          (≈-sym
            (≈-trans
              -- reduce application, making both sides subst applications
              ⇒β
              (≈-trans
                -- rewrite (wkenTm e ∘ subst σ) to subst (σ ₛ∘ₑ e)
                (inv-subst (≡⇒≈ (sym (Term-ₛ∘ₑ t₁ _ _))))
                -- equate the substitutions on both sides
                (≡⇒≈
                  (sym (Term-∘ₛ t₁ _ _) ︔
                  (cong (λ σₓ → subst (σₓ `, t') t₁)
                    (assₛₑₛ _ _ _ ︔
                    (assₛₑₛ _ _ _ ︔
                    (cong (σ ∘ₛ_) (idlₑₛ _) ︔
                    (sym (assₛₑₛ σ _ e) ︔
                    (idrₛ _)))))))))))
          (corrEval t₁ {σ = (σ ₛ∘ₑ e) `, t'} (Rs-ₛ∘ₑ p , x))

  corrEval {Γ} {.(_ + _)} (inl t) {Δ} {σ} {γ} p =
    (subst σ t) , corrEval t p , ≈-refl
  corrEval {Γ} {.(_ + _)} (inr t) {Δ} {σ} {γ} p =
    (subst σ t) , corrEval t p , ≈-refl
  corrEval {Γ} {a} (case {_} {b} {c} t t₁ t₂) {Δ = Δ} {σ} {γ} p =
    corrRun𝒟 {Δ} {a} _ _
      (corrCase𝒟 (subst σ t) (eval t γ)
        (subst (keepˢ σ) t₁) _
        (subst (keepˢ σ) t₂) _
        (corrEval t p)
          (λ e q → inv {a} (≈-sym (≈-trans ⇒β
            (≡⇒≈
            (trans
              (sym (Term-ₑ∘ₛ (subst (keepˢ σ) t₁) (idₛ `, _) (keep e)))
              (trans
                (sym (Term-∘ₛ t₁ (keepˢ σ) ((e ₑ∘ₛ idₛ) `, _)))
                (cong (λ s → subst (s `, _) t₁)
                (trans
                  (assₛₑₛ _ _ _)
                  (trans
                    (cong (σ ∘ₛ_) (idlₑₛ _))
                    (trans
                      (sym (assₛₑₛ σ idₛ e))
                      (idrₛ _))))))))))
            (corrEval t₁ {σ = (σ ₛ∘ₑ e) `, _}
            (Rs-ₛ∘ₑ p , q)))
          (λ e q → inv {a} (≈-sym (≈-trans ⇒β
             (≡⇒≈
             (trans
               (sym (Term-ₑ∘ₛ (subst (keepˢ σ) t₂) (idₛ `, _) (keep e)))
               (trans
                 (sym (Term-∘ₛ t₂ (keepˢ σ) ((e ₑ∘ₛ idₛ) `, _)))
                 (cong (λ s → subst (s `, _) t₂)
                 (trans
                   (assₛₑₛ _ _ _)
                   (trans
                     (cong (σ ∘ₛ_) (idlₑₛ _))
                     (trans
                       (sym (assₛₑₛ σ idₛ e))
                       (idrₛ _))))))))))
            (corrEval t₂ {σ = (σ ₛ∘ₑ e) `, _}
            (Rs-ₛ∘ₑ p , q))))

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
        ( (≡⇒≈ (sym (nat-qNe _))) ∙ (≈-sym (corrReifyVal p)))
        (corrReflect {a = b})
    corrReflect {Γ} {a + b} {n}
      = _ , _
      , (var ze
        , corrReflect {Γ `, a} {n = var ze}
        , ≈-refl)
      , (var ze
        , corrReflect {Γ `, b} {n = var ze}
        , ≈-refl)
      , +η
    corrReflect {Γ} {⟨ ℓ ⟩ a} {n}
      = η (var ze)
      , (var ze
        , (corrReflect {Γ `, a} {n = var ze}
        , ≈-refl))
        , ≈-trans ⟨⟩η ((≈-sym ↑γ₃ ≫= ≈-refl))

    corrReifyVal𝒞 : ∀ {Γ} {ℓ} {a} {t : Term (⟨ ℓ ⟩ a) Γ} {v : 𝒞 ⟦ a ⟧ ℓ Γ}
                  → R⟨⟩ t v
                  → t ≈ qNf (reifyVal𝒞 v)
    corrReifyVal𝒞 {v = return x} (t′ , Rt′ , p)
      = ≈-trans p (η (corrReifyVal Rt′))
    corrReifyVal𝒞 {v = bind c n v} (t′ , Rt′ , p)
      = ≈-trans p (≈-refl ≫= (corrReifyVal𝒞 {t = t′} {v = v} Rt′))
    corrReifyVal𝒞 {v = branch n v₁ v₂} (t₁ , t₂ , Rt₁ , Rt₂ , p)
      = ≈-trans p (case ≈-refl (corrReifyVal𝒞 {t = t₁} {v = v₁} Rt₁)
                               (corrReifyVal𝒞 {t = t₂} {v = v₂} Rt₂))

    corrReifySum : ∀ {Γ} {a b} {t : Term (a + b) Γ} {v : (⟦ a ⟧ +ᴾ ⟦ b ⟧) .In Γ}
                 → Rl₊ t v
                 → t ≈ (qNf (reifySum v))
    corrReifySum {Γ} {a} {b} {t} {inj₁ x} (t′ , Rt′ , p)
      = ≈-trans p (inl (corrReifyVal Rt′))
    corrReifySum {Γ} {a} {b} {t} {inj₂ y} (t′ , Rt′ , p)
      = ≈-trans p (inr (corrReifyVal Rt′))

    corrReifyVal𝒟 : ∀ {Γ} {a} {b} {t : Term (a + b) Γ}
                                   {v : 𝒟 (⟦ a ⟧ +ᴾ ⟦ b ⟧) Γ}
                  → R₊ t v
                  → t ≈ qNf (run𝒟Nf (map𝒟 reifySum v))
    corrReifyVal𝒟 {Γ} {a} {b} {t} {return x} p
      = corrReifySum p
    corrReifyVal𝒟 {Γ} {a} {b} {t} {branch x v₁ v₂} (t₁ , t₂ , R₁ , R₂ , p)
      = ≈-trans p (case ≈-refl (corrReifyVal𝒟 {t = t₁} {v = v₁} R₁)
                               (corrReifyVal𝒟 {t = t₂} {v = v₂} R₂))

    corrReifyVal : ∀ {Γ} {a}
      {t : Term a Γ} {v : ⟦ a ⟧ .In Γ}
      → R t v
      → t ≈ qNf (reifyVal v)
    corrReifyVal {Γ} {𝟙}           p = 𝟙η
    corrReifyVal {Γ} {𝕓}           p = p
    corrReifyVal {Γ} {a ⇒ b}   {t} p
      = ≈-trans ⇒η
                (`λ (corrReifyVal {a = b}
                      (p (drop idₑ) (corrReflect {a = a} {n = var ze}))))
    corrReifyVal {Γ} {a + b}  {t} {v} p
      = corrReifyVal𝒟 {t = t} {v = v} p
    corrReifyVal {Γ} {⟨ ℓ ⟩ a} {t} {v} p
      = corrReifyVal𝒞 {t = t} {v = v} p

  Rs-id : ∀ {Γ} → Rs {Γ = Γ} {Δ = Γ} idₛ (idSubst Γ)
  Rs-id {Ø}      = tt
  Rs-id {Γ `, a} with Rs-id {Γ}
  ... | p = Rs-ₛ∘ₑ p , (corrReflect {Γ = Γ `, a} {n = var ze})

  corrReify : ∀ {Γ} {a}
    → {t : Term a Γ}
    → Fund t
    → t ≈ qNf (reify (eval t))
  corrReify {Γ} {a} {t} f =
    corrReifyVal
      (inv {a} {t₁ = subst idₛ t} (≡⇒≈ (Term-idₛ _) ) (f Rs-id))

  consistent : ∀ {Γ} {a}
    → (t : Term a Γ)
    → t ≈ qNf (norm t)
  consistent t = corrReify (corrEval t)
