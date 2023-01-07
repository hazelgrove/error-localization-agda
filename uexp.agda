open import prelude
open import typ

-- unmarked expressions
module uexp where
  infix  4 _⊢_⇒_
  infix  4 _⊢_⇐_
  infix  4 _∋_∶_
  infixl 5 _,_∶_

  -- variables
  Var : Set
  Var = ℕ

  -- contexts
  data Ctx : Set where
    ∅     : Ctx
    _,_∶_ : Ctx → Var → Typ → Ctx

  -- context membership
  data _∋_∶_ : (Γ : Ctx) (x : Var) (τ : Typ) → Set where
    Z : ∀ {Γ x τ}                            → Γ , x  ∶ τ  ∋ x ∶ τ
    S : ∀ {Γ x x′ τ τ′} → x ≢ x′ → Γ ∋ x ∶ τ → Γ , x′ ∶ τ′ ∋ x ∶ τ

  _∌_ : (Γ : Ctx) → (x : Var) → Set
  Γ ∌ x = ∀ {τ} → ¬ (Γ ∋ x ∶ τ)

  -- decidable context membership
  data _∋?_ : (Γ : Ctx) (x : Var) → Set where
    yes : ∀ {Γ x τ} → Γ ∋ x ∶ τ → Γ ∋? x
    no  : ∀ {Γ x}   → Γ ∌ x     → Γ ∋? x

  _∋??_ : (Γ : Ctx) → (x : Var) → Γ ∋? x
  ∅ ∋?? x                                      = no (λ ())
  (Γ , x′ ∶ τ) ∋?? x with x ≡ℕ? x′
  ...                   | yes refl             = yes Z
  ...                   | no  x≢x′ with Γ ∋?? x
  ...                                 | yes ∋x = yes (S x≢x′ ∋x)
  ...                                 | no ∌x  = no λ { Z → x≢x′ refl ; (S _ ∋x′) → ∌x ∋x′ }

  data UExp : Set where
    ‵⦇-⦈^_  : ℕ → UExp
    ‵_      : ℕ → UExp
    ‵λ_∶_∙_ : ℕ → Typ → UExp → UExp
    ‵_∙_    : UExp → UExp → UExp
    ‵ℕ_     : ℕ → UExp
    ‵_+_    : UExp → UExp → UExp
    ‵tt     : UExp
    ‵ff     : UExp
    ‵_∙_∙_  : UExp → UExp → UExp → UExp

  data Subsumable : UExp → Set where
    SuHole : ∀ {u}
      → Subsumable (‵⦇-⦈^ u)

    SuVar : ∀ {x}
      → Subsumable (‵ x)

    SuAp : ∀ {e₁ e₂}
      → Subsumable (‵ e₁ ∙ e₂)

    SuNum : ∀ {n}
      → Subsumable (‵ℕ n)

    SuPlus : ∀ {e₁ e₂}
      → Subsumable (‵ e₁ + e₂)

    SuTrue :
        Subsumable ‵tt

    SuFalse :
        Subsumable ‵ff

  mutual
    -- synthesis
    data _⊢_⇒_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      USHole : ∀ {Γ u}
        → Γ ⊢ ‵⦇-⦈^ u  ⇒ unknown

      USVar : ∀ {Γ x τ}
        → Γ ∋ x ∶ τ
        → Γ ⊢ ‵ x ⇒ τ

      USLam : ∀ {Γ x τ e τ′}
        → Γ , x ∶ τ ⊢ e ⇒ τ′
        → Γ ⊢ ‵λ x ∶ τ ∙ e ⇒ τ′

      USAp : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → Γ ⊢ e₁ ⇒ τ
        → τ ▸ τ₁ -→ τ₂
        → Γ ⊢ e₂ ⇐ τ₁
        → Γ ⊢ ‵ e₁ ∙ e₂ ⇒ τ₂

      USNum : ∀ {Γ n}
        → Γ ⊢ ‵ℕ n ⇒ num

      USPlus : ∀ {Γ e₁ e₂}
        → Γ ⊢ e₁ ⇐ num
        → Γ ⊢ e₂ ⇐ num
        → Γ ⊢ ‵ e₁ + e₂ ⇒ num

      USTrue : ∀ {Γ}
        → Γ ⊢ ‵tt ⇒ bool

      USFalse : ∀ {Γ}
        → Γ ⊢ ‵ff ⇒ bool

      USIf : ∀ {Γ e₁ e₂ e₃ τ τ₁ τ₂}
        → Γ ⊢ e₁ ⇐ bool
        → Γ ⊢ e₂ ⇒ τ₁
        → Γ ⊢ e₃ ⇒ τ₂
        → τ₁ ⊔ τ₂ ⇒ τ
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ⇒ τ

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → τ₃ ▸ τ₁ -→ τ₂
        → Γ , x ∶ τ ⊢ e ⇐ τ₁
        → Γ ⊢ ‵λ x ∶ τ ∙ e ⇐ τ₃

      UAIf : ∀ {Γ e₁ e₂ e₃ τ}
        → Γ ⊢ e₁ ⇐ bool
        → Γ ⊢ e₂ ⇐ τ
        → Γ ⊢ e₃ ⇐ τ
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ⇐ τ

      UASubsume : ∀ {Γ e τ τ′}
        → Γ ⊢ e ⇒ τ′
        → τ ~ τ′
        → Subsumable e
        → Γ ⊢ e ⇐ τ
