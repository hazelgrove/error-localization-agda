open import prelude

open import core.typ
open import core.var

module core.ctx where
  infix  4 _∋_∶_
  infixl 5 _,_∶_

  -- contexts
  data Ctx : Set where
    ∅     : Ctx
    _,_∶_ : Ctx → Var → Typ → Ctx

  -- context membership
  data _∋_∶_ : (Γ : Ctx) (x : Var) (τ : Typ) → Set where
    Z : ∀ {Γ x τ}                            → Γ , x  ∶ τ  ∋ x ∶ τ
    S : ∀ {Γ x x′ τ τ′} → x ≢ x′ → Γ ∋ x ∶ τ → Γ , x′ ∶ τ′ ∋ x ∶ τ

  _∌_ : (Γ : Ctx) → (x : Var) → Set
  Γ ∌ x = ¬ (∃[ τ ] Γ ∋ x ∶ τ)

  -- decidable context membership
  data _∋?_ : (Γ : Ctx) (x : Var) → Set where
    yes : ∀ {Γ x τ} → Γ ∋ x ∶ τ → Γ ∋? x
    no  : ∀ {Γ x}   → Γ ∌ x     → Γ ∋? x

  _∋??_ : (Γ : Ctx) → (x : Var) → Γ ∋? x
  ∅            ∋?? x          = no (λ ())
  (Γ , x′ ∶ τ) ∋?? x
    with x ≡ℕ? x′
  ...  | yes refl             = yes Z
  ...  | no  x≢x′ with Γ ∋?? x
  ...                | yes ∋x = yes (S x≢x′ ∋x)
  ...                | no ∌x  = no λ { ⟨ _ , Z ⟩ → x≢x′ refl
                                     ; ⟨ τ′ , S _ ∋x₁ ⟩ → ∌x ⟨ τ′ , ∋x₁ ⟩ }
