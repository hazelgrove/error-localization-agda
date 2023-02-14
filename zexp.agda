open import prelude
open import typ
open import uexp

-- cursor expressions
module zexp where
  data ZTyp : Set where
    ▹_◃   : (τ : Typ) → ZTyp
    _-→₁_ : (τ^ : ZTyp) → (τ : Typ) → ZTyp
    _-→₂_ : (τ : Typ) → (τ^ : ZTyp) → ZTyp

  infixr 25  _-→₁_
  infixr 25  _-→₂_

  data ZExp : Set where
    ‵▹_◃     : (e : UExp)  → ZExp
    ‵λ₁_∶_∙_ : (x : Var)   → (τ^ : ZTyp) → (e : UExp)  → ZExp
    ‵λ₂_∶_∙_ : (x : Var)   → (τ  : Typ)  → (ê : ZExp)  → ZExp
    ‵_∙₁_    : (ê : ZExp)  → (e  : UExp) → ZExp
    ‵_∙₂_    : (e : UExp)  → (ê  : ZExp) → ZExp
    ‵_←₁_∙_  : (x : Var)   → (ê  : ZExp) → (e : UExp)  → ZExp
    ‵_←₂_∙_  : (x : Var)   → (e  : UExp) → (ê : ZExp)  → ZExp
    ‵_+₁_    : (ê : ZExp)  → (e  : UExp) → ZExp
    ‵_+₂_    : (e : UExp)  → (ê  : ZExp) → ZExp
    ‵_∙₁_∙_  : (ê : ZExp)  → (e₂ : UExp) → (e₃ : UExp) → ZExp
    ‵_∙₂_∙_  : (e₁ : UExp) → (ê  : ZExp) → (e₃ : UExp) → ZExp
    ‵_∙₃_∙_  : (e₁ : UExp) → (e₂ : UExp) → (ê  : ZExp) → ZExp

  data erase-t : (τ^ : ZTyp) → (τ : Typ) → Set where
    ETTop  : ∀ {τ} → erase-t (▹ τ ◃) τ
    ETArr1 : ∀ {τ₁^ τ₂ τ₁} → erase-t (τ₁^ -→₁ τ₂) (τ₁ -→ τ₂)
    ETArr2 : ∀ {τ₁ τ₂^ τ₂} → erase-t (τ₁ -→₂ τ₂^) (τ₁ -→ τ₂)

  data erase-e : (ê : ZExp) → (e : UExp) → Set where
    EETop   : ∀ {e}
            → erase-e (‵▹ e ◃) e
    EELam1  : ∀ {x τ^ e τ}
            → erase-e (‵λ₁ x ∶ τ^ ∙ e) (‵λ x ∶ τ ∙ e)
    EELam2  : ∀ {x τ ê e}
            → erase-e (‵λ₂ x ∶ τ ∙ ê) (‵λ x ∶ τ ∙ e)
    EEAp1   : ∀ {ê₁ e₂ e₁}
            → erase-e (‵ ê₁ ∙₁ e₂) (‵ e₁ ∙ e₂)
    EEAp2   : ∀ {e₁ ê₂ e₂}
            → erase-e (‵ e₁ ∙₂ ê₂) (‵ e₁ ∙ e₂)
    EELet1  : ∀ {x ê₁ e₂ e₁}
            → erase-e (‵ x ←₁ ê₁ ∙ e₂) (‵ x ← e₁ ∙ e₂)
    EELet2  : ∀ {x e₁ ê₂ e₂}
            → erase-e (‵ x ←₂ e₁ ∙ ê₂) (‵ x ← e₁ ∙ e₂)
    EEPlus1 : ∀ {ê₁ e₂ e₁}
            → erase-e (‵ ê₁ +₁ e₂) (‵ e₁ + e₂)
    EEPlus2 : ∀ {e₁ ê₂ e₂}
            → erase-e (‵ e₁ +₂ ê₂) (‵ e₁ + e₂)
    EEIf1   : ∀ {ê₁ e₂ e₃ e₁}
            → erase-e (‵ ê₁ ∙₁ e₂ ∙ e₃) (‵ e₁ ∙ e₂ ∙ e₃)
    EEIf2   : ∀ {e₁ ê₂ e₃ e₂}
            → erase-e (‵ e₁ ∙₂ ê₂ ∙ e₃) (‵ e₁ ∙ e₂ ∙ e₃)
    EEIf3   : ∀ {e₁ e₂ ê₃ e₃}
            → erase-e (‵ e₁ ∙₃ e₂ ∙ ê₃) (‵ e₁ ∙ e₂ ∙ e₃)

  _◇τ : (τ^ : ZTyp) → Typ
  ▹ τ ◃      ◇τ = τ
  (τ^ -→₁ τ) ◇τ = (τ^ ◇τ) -→ τ
  (τ -→₂ τ^) ◇τ = τ -→ (τ^ ◇τ)

  _◇ : (ê : ZExp) → UExp
  ‵▹ e ◃ ◇ = e
  (‵λ₁ x ∶ τ^ ∙ e) ◇ = ‵λ x ∶ (τ^ ◇τ) ∙ e
  (‵λ₂ x ∶ τ ∙ ê)  ◇ = ‵λ x ∶ τ ∙ (ê ◇)
  (‵ ê ∙₁ e)       ◇ = ‵ (ê ◇) ∙ e
  (‵ e ∙₂ ê)       ◇ = ‵ e ∙ (ê ◇)
  (‵ x ←₁ ê ∙ e)   ◇ = ‵ x ← (ê ◇) ∙ e
  (‵ x ←₂ e ∙ ê)   ◇ = ‵ x ← e ∙ (ê ◇)
  (‵ ê +₁ e)       ◇ = ‵ (ê ◇) + e
  (‵ e +₂ ê)       ◇ = ‵ e + (ê ◇)
  (‵ ê ∙₁ e₂ ∙ e₃) ◇ = ‵ (ê ◇) ∙ e₂ ∙ e₃
  (‵ e₁ ∙₂ ê ∙ e₃) ◇ = ‵ e₁ ∙ (ê ◇) ∙ e₃
  (‵ e₁ ∙₃ e₂ ∙ ê) ◇ = ‵ e₁ ∙ e₂ ∙ (ê ◇)
