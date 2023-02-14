open import prelude
open import typ
open import uexp

-- cursor expressions
module zexp where
  data ZTyp : Set where
    ▹_◃ : (τ : Typ) → ZTyp
    _-→₁_ : (τ^ : ZTyp) → (τ : Typ) → ZTyp
    _-→₂_ : (τ : Typ) → (τ^ : ZTyp) → ZTyp

  infixr 25  _-→₁_
  infixr 25  _-→₂_

  data ZExp : Set where
    ‵▹_◃ : (e : UExp) → ZExp
    ‵λ₁_∶_∙_ : (x : Var) → (τ^ : ZTyp) → (e : UExp) → ZExp
    ‵λ₂_∶_∙_ : (x : Var) → (τ : Typ) → (ê : ZExp) → ZExp
    ‵_∙₁_ : (ê : ZExp) → (e : UExp) → ZExp
    ‵_∙₂_ : (e : UExp) → (ê : ZExp) → ZExp
    ‵_←₁_∙_ : (x : Var) → (ê : ZExp) → (e : UExp) → ZExp
    ‵_←₂_∙_ : (x : Var) → (e : UExp) → (ê : ZExp) → ZExp
    ‵_+₁_ : (ê : ZExp) → (e : UExp) → ZExp
    ‵_+₂_ : (e : UExp) → (ê : ZExp) → ZExp
    ‵_∙₁_∙_ : (ê : ZExp) → (e₂ : UExp) → (e₃ : UExp) → ZExp
    ‵_∙₂_∙_ : (e₁ : UExp) → (ê : ZExp) → (e₃ : UExp) → ZExp
    ‵_∙₃_∙_ : (e₁ : UExp) → (e₂ : UExp) → (ê : ZExp) → ZExp

  _◇τ : (τ^ : ZTyp) → Typ
  ▹ τ ◃      ◇τ = τ
  (τ^ -→₁ τ) ◇τ = (τ^ ◇τ) -→ τ
  (τ -→₂ τ^) ◇τ = τ -→ (τ^ ◇τ)

  _◇ : (ê : ZExp) → UExp
  ‵▹ e ◃ ◇ = e
  (‵λ₁ x ∶ τ^ ∙ e) ◇ = ‵λ x ∶ (τ^ ◇τ) ∙ e
  (‵λ₂ x ∶ τ ∙ ê) ◇ = ‵λ x ∶ τ ∙ (ê ◇)
  (‵ ê ∙₁ e) ◇ = ‵ (ê ◇) ∙ e
  (‵ e ∙₂ ê) ◇ = ‵ e ∙ (ê ◇)
  (‵ x ←₁ ê ∙ e) ◇ = ‵ x ← (ê ◇) ∙ e
  (‵ x ←₂ e ∙ ê) ◇ = ‵ x ← e ∙ (ê ◇)
  (‵ ê +₁ e) ◇ = ‵ (ê ◇) + e
  (‵ e +₂ ê) ◇ = ‵ e + (ê ◇)
  (‵ ê ∙₁ e₂ ∙ e₃) ◇ = ‵ (ê ◇) ∙ e₂ ∙ e₃
  (‵ e₁ ∙₂ ê ∙ e₃) ◇ = ‵ e₁ ∙ (ê ◇) ∙ e₃
  (‵ e₁ ∙₃ e₂ ∙ ê) ◇ = ‵ e₁ ∙ e₂ ∙ (ê ◇)
