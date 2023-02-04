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

  -- hole identifiers
  Hole : Set
  Hole = ℕ

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
    ‵⦇-⦈^_  : (u : Hole) → UExp
    ‵_      : (x : Var) → UExp
    ‵λ_∶_∙_ : (x : Var) → (τ : Typ) → (e : UExp) → UExp
    ‵_∙_    : (e₁ : UExp) → (e₂ : UExp) → UExp
    ‵ℕ_     : (n : ℕ) → UExp
    ‵_+_    : (e₁ : UExp) → (e₂ : UExp) → UExp
    ‵tt     : UExp
    ‵ff     : UExp
    ‵_∙_∙_  : (e₁ : UExp) → (e₂ : UExp) → (e₃ : UExp) → UExp

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
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ ‵ x ⇒ τ

      USLam : ∀ {Γ x τ e τ′}
        → (e⇒τ′ :  Γ , x ∶ τ ⊢ e ⇒ τ′)
        → Γ ⊢ ‵λ x ∶ τ ∙ e ⇒ τ -→ τ′

      USAp : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → (e₁⇒τ : Γ ⊢ e₁ ⇒ τ)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₁⇐τ₁ : Γ ⊢ e₂ ⇐ τ₁)
        → Γ ⊢ ‵ e₁ ∙ e₂ ⇒ τ₂

      USNum : ∀ {Γ n}
        → Γ ⊢ ‵ℕ n ⇒ num

      USPlus : ∀ {Γ e₁ e₂}
        → (e₁⇐num : Γ ⊢ e₁ ⇐ num)
        → (e₂⇐num : Γ ⊢ e₂ ⇐ num)
        → Γ ⊢ ‵ e₁ + e₂ ⇒ num

      USTrue : ∀ {Γ}
        → Γ ⊢ ‵tt ⇒ bool

      USFalse : ∀ {Γ}
        → Γ ⊢ ‵ff ⇒ bool

      USIf : ∀ {Γ e₁ e₂ e₃ τ τ₁ τ₂}
        → (e₁⇐bool : Γ ⊢ e₁ ⇐ bool)
        → (e₂⇒τ₁ : Γ ⊢ e₂ ⇒ τ₁)
        → (e₃⇒τ₂ : Γ ⊢ e₃ ⇒ τ₂)
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ⇒ τ

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ τ ⊢ e ⇐ τ₂)
        → Γ ⊢ ‵λ x ∶ τ ∙ e ⇐ τ₃

      UAIf : ∀ {Γ e₁ e₂ e₃ τ}
        → (e₁⇐bool : Γ ⊢ e₁ ⇐ bool)
        → (e₂⇐τ : Γ ⊢ e₂ ⇐ τ)
        → (e₃⇐τ : Γ ⊢ e₃ ⇐ τ)
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ⇐ τ

      UASubsume : ∀ {Γ e τ τ′}
        → (e⇒τ′ : Γ ⊢ e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : Subsumable e)
        → Γ ⊢ e ⇐ τ
