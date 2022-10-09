open import prelude

module core where

  -- types
  module typ where
    data Typ  : Set where
      int     : Typ
      bool    : Typ
      unknown : Typ
      _-→_    : Typ → Typ → Typ

    infixr 25  _-→_

    -- consistency
    data _~_ : (τ₁ τ₂ : Typ) → Set where
      TCRefl     : {τ : Typ} → τ ~ τ
      TCUnknown1 : {τ : Typ} → τ ~ unknown
      TCUnknown2 : {τ : Typ} → unknown ~ τ
      TCArr      : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                  → τ₁ ~ τ₁′
                  → τ₂ ~ τ₂′
                  → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′

  -- unmarked expressions
  module uexp where
    open typ using (Typ)

    data UExp : Set where
      ∙⦇-⦈[_] : ℕ → UExp
      X       : ℕ → UExp
      ∙λ_∶_∙_ : ℕ → Typ → UExp → UExp
      _∘_     : UExp → UExp → UExp
      N       : UExp
      _∙+_    : UExp → UExp → UExp
      tt      : UExp
      ff      : UExp
      _∙_∙_   : UExp → UExp → UExp → UExp
