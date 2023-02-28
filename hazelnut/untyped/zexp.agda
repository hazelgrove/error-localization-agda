open import prelude
open import core

-- cursor expressions
module hazelnut.untyped.zexp where
  -- zippered types
  data ZTyp : Set where
    ▹_◃   : (τ : Typ) → ZTyp
    _-→₁_ : (τ^ : ZTyp) → (τ : Typ) → ZTyp
    _-→₂_ : (τ : Typ) → (τ^ : ZTyp) → ZTyp
    _-×₁_ : (τ^ : ZTyp) → (τ : Typ) → ZTyp
    _-×₂_ : (τ : Typ) → (τ^ : ZTyp) → ZTyp

  infixr 25  _-→₁_
  infixr 25  _-→₂_
  infixr 24  _-×₁_
  infixr 24  _-×₂_

  -- zippered expressions
  data ZExp : Set where
    ‵▹_◃     : (e  : UExp) → ZExp
    ‵λ₁_∶_∙_ : (x  : Var)  → (τ^ : ZTyp) → (e : UExp)  → ZExp
    ‵λ₂_∶_∙_ : (x  : Var)  → (τ  : Typ)  → (ê : ZExp)  → ZExp
    ‵_∙₁_    : (ê  : ZExp) → (e  : UExp) → ZExp
    ‵_∙₂_    : (e  : UExp) → (ê  : ZExp) → ZExp
    ‵_←₁_∙_  : (x  : Var)  → (ê  : ZExp) → (e : UExp)  → ZExp
    ‵_←₂_∙_  : (x  : Var)  → (e  : UExp) → (ê : ZExp)  → ZExp
    ‵_+₁_    : (ê  : ZExp) → (e  : UExp) → ZExp
    ‵_+₂_    : (e  : UExp) → (ê  : ZExp) → ZExp
    ‵_∙₁_∙_  : (ê  : ZExp) → (e₂ : UExp) → (e₃ : UExp) → ZExp
    ‵_∙₂_∙_  : (e₁ : UExp) → (ê  : ZExp) → (e₃ : UExp) → ZExp
    ‵_∙₃_∙_  : (e₁ : UExp) → (e₂ : UExp) → (ê  : ZExp) → ZExp
    ‵⟨_,₁_⟩  : (e₁ : ZExp) → (e₂ : UExp) → ZExp
    ‵⟨_,₂_⟩  : (e₁ : UExp) → (e₂ : ZExp) → ZExp
    ‵π₁_     : (e  : ZExp) → ZExp
    ‵π₂_     : (e  : ZExp) → ZExp
